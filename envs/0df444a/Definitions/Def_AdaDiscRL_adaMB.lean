-- Prove2me | Definitions.Def_AdaDiscRL_adaMB
-- name    : AdaDiscRL_adaMB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:20.264893+00:00
-- url     : https://prove2.me/theorems/19d515a6-6ba9-465d-9d8e-cf5e5f63e39a
-- title:
--   AdaMB: the model-based adaptive discretization algorithm
-- statement:
--   **AdaMB** selects balls as AdaQL does. After observing $(R^k_h,X^k_{h+1})$ it increments $n_h(B)$ for the selected ball $B$, updates the running means $\bar r_h(B)$ and $\overline{\mathbf T}_h(A\mid B)$ (the fraction of transitions into each state cell $A$ of level $\ell(B)$), and splits $B$ if $\mathrm{Conf}\le\mathrm{diam}(B)$. At the end of the episode, for $h=H,\dots,1$ and every active ball with $n\ge1$,
--   $$
--   \overline{\mathbf Q}^k_h(B)=\bar r^k_h(B)+\mathrm{Rucb}^k_h(B)+\mathbb E_{A\sim\overline{\mathbf T}^k_h(\cdot\mid B)}\big[\overline{\mathbf V}^k_{h+1}(\tilde x(A))\big]+\mathrm{Tucb}^k_h(B)+\mathrm{Bias}(B)
--   $$
--   (Eq. (6); without the expectation and $\mathrm{Tucb}$ when $h=H$), then $\widetilde{\mathbf V}^k_h(A)=\min\{\widetilde{\mathbf V}^{k-1}_h(A),\max_{B\in\mathcal P^k_h:\mathcal S(B)\supseteq A}\overline{\mathbf Q}^k_h(B)\}$ for $A\in\mathcal S(\mathcal P^k_h)$ (Eq. (7)) and
--   $$
--   \overline{\mathbf V}^k_h(x)=\min_{A'\in\mathcal S(\mathcal P^k_h)}\big(\widetilde{\mathbf V}^k_h(A')+L_V\mathcal D_{\mathcal S}(x,\tilde x(A'))\big)\qquad\text{(Eq. (8))}.
--   $$
--
--   **Formalization Note** The full update is done at the end of the episode, backward in $h$ (the order forced by $\overline{\mathbf V}^k_{h+1}$). Balls with $n=0$ keep their initial estimate.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, §3.3.1, p.17, Eq. (6)–(8); §3.3, p.16; Algorithm 1, p.13

import Mathlib
import Definitions.Def_AdaDiscRL_adaQL

namespace AdaDiscRL

open Classical

variable {S A ι : Type*} [MetricSpace S] [MeasurableSpace S] [MeasurableSpace A]
  {D : S × A → S × A → ℝ} {dS Lmax H : ℕ}

/-- One AdaMB sample at the selected ball `B` (§3.3 "Update Counts", p.16; §3.4, p.19):
`n(B) ← n(B) + 1`, `r̄(B) ← (n r̄(B) + R)/(n + 1)`,
`T̄(A | B) ← (n T̄(A | B) + 1{X_{h+1} ∈ A})/(n + 1)` for the state cells `A` of level `ℓ(B)`; then
split `B` if `Conf(B) ≤ diam(B)`, Eq. (12). -/
noncomputable def stepMB (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H) (st : Stats S ι)
    (B : ι) (r : ℝ) (x' : S) : Stats S ι :=
  let n0 := st.n B
  let n' := n0 + 1
  let rb := ((n0 : ℝ) * st.rbar B + r) / n'
  let Tb : Set S → ℝ := fun X => if X ∈ P.cellsAt (P.level B) then
      ((n0 : ℝ) * st.Tbar B X + if x' ∈ X then 1 else 0) / n' else 0
  let st1 : Stats S ι :=
    { st with
      n := Function.update st.n B n'
      rbar := Function.update st.rbar B rb
      Tbar := Function.update st.Tbar B Tb }
  if prm.confMB n' ≤ P.diam B then splitStats P st1 B else st1

/-- AdaMB full update of step `h` (Eq. (6)–(7), p.17): for every active ball `B` with
`n(B) ≥ 1`, `Q̄(B) = r̄(B) + Rucb(B) + Bias(B)` if `h = H` (`last`) and
`Q̄(B) = r̄(B) + Rucb(B) + 𝔼_{A∼T̄(·|B)}[V̄_{h+1}(x̃(A))] + Tucb(B) + Bias(B)` otherwise; balls with
`n(B) = 0` keep their initial estimate. Then, for `A ∈ S(P_h)`,
`Ṽ(A) = min{Ṽ(A), max_{B ∈ P_h : S(B) ⊇ A} Q̄(B)}`. `vnext` is `V̄_{h+1}` of this episode. -/
noncomputable def recomputeMB (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H)
    (st : Stats S ι) (last : Prop) (vnext : S → ℝ) : Stats S ι :=
  let Q' : ι → ℝ := fun B => if isActive P st B ∧ 1 ≤ st.n B then
      st.rbar B + prm.rucbMB (st.n B) +
        (if last then 0 else (∑ᶠ X : Set S, st.Tbar B X * vnext (P.sCenter X)) + prm.tucbMB (st.n B)) +
        prm.biasMB (P.diam B)
    else st.Q B
  { st with
    Q := Q'
    Vt := fun X => if X ∈ minCells P st then
      min (st.Vt X) (sSup (Q' '' {B | isActive P st B ∧ X ⊆ P.sCell B})) else st.Vt X }

/-- AdaMB value estimate, Eq. (8), p.17: `V̄_h(x) = min_{A′ ∈ S(P_h)} (Ṽ_h(A′) + L_V D_S(x, x̃(A′)))`. -/
noncomputable def VbarMB (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H) (st : Stats S ι)
    (x : S) : ℝ :=
  sInf ((fun X => st.Vt X + prm.LV * dist x (P.sCenter X)) '' minCells P st)

/-- The end-of-episode backward pass `h = H, H−1, …, 1` of AdaMB (Algorithm 1 line 16): returns the
state after recomputing the last `m` steps, and `V̄` of the earliest recomputed step
(`V̄_{H+1} ≡ 0` for `m = 0`). -/
noncomputable def mbBackward (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H)
    (σ : AlgState S ι H) : ℕ → AlgState S ι H × (S → ℝ)
  | 0 => (σ, fun _ => 0)
  | m + 1 =>
      let p := mbBackward P prm σ m
      if hm : m < H then
        let h : Fin H := ⟨H - 1 - m, by omega⟩
        let st' := recomputeMB P prm (p.1 h) (m = 0) p.2
        (Function.update p.1 h st', VbarMB P prm st')
      else p

/-- One AdaMB episode (Algorithm 1 lines 4–10, 15–16): select `B_h^k` with `Q̄_h^{k−1}` at each
step, update its statistics (and split), then recompute `Q̄`, `Ṽ` for all steps backward. -/
noncomputable def updateMB (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H)
    (choose : Finset ι → (ι → ℝ) → ι) (σ : AlgState S ι H) (d : EpData S A H) :
    AlgState S ι H :=
  (mbBackward P prm (fun h => stepMB P prm (σ h) (selBall P choose σ h (d.1 h.castSucc))
    (d.2.2 h) (d.1 h.succ)) H).1

/-- **AdaMB** run on a data sequence: the state at the end of episode `k` (`k = 0`: initial). -/
noncomputable def statesMB (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H)
    (choose : Finset ι → (ι → ℝ) → ι) (data : ℕ → EpData S A H) : ℕ → AlgState S ι H
  | 0 => initState P prm
  | k + 1 => updateMB P prm choose (statesMB P prm choose data k) (data (k + 1))

end AdaDiscRL


