-- Prove2me | Definitions.Def_AdaDiscRL_adaQL
-- name    : AdaDiscRL_adaQL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:48.044879+00:00
-- url     : https://prove2.me/theorems/53c35660-6d8d-42c9-aec6-1b9042137d7f
-- title:
--   AdaQL: the model-free adaptive discretization algorithm
-- statement:
--   **AdaQL** runs as follows in episode $k$, for each step $h$: observe $X^k_h$, select $B^k_h=\arg\max_{B\in\mathrm{RELEVANT}_h(X^k_h)}\overline{\mathbf Q}^{k-1}_h(B)$, play an action in $B^k_h$, observe $R^k_h$ and $X^k_{h+1}$; set $t=n_h(B^k_h)\leftarrow n_h(B^k_h)+1$ and, with $\alpha_t=\frac{H+1}{H+t}$, update only the selected ball by Eq. (9),
--   $$
--   \overline{\mathbf Q}^k_h(B)=(1-\alpha_t)\overline{\mathbf Q}^{k-1}_h(B)+\alpha_t\big(R^k_h+\mathrm{Rucb}^k_h(B)+\overline{\mathbf V}^{k-1}_{h+1}(X^k_{h+1})+\mathrm{Tucb}^k_h(B)+\mathrm{Bias}(B)\big),
--   $$
--   where $\overline{\mathbf V}^{k-1}_{h+1}(x)=\min\big(H,\max_{B\in\mathrm{RELEVANT}^{k-1}_{h+1}(x)}\overline{\mathbf Q}^{k-1}_{h+1}(B)\big)$ (Eq. (10)) and $\overline{\mathbf V}_{H+1}\equiv0$; finally split $B^k_h$ if $\mathrm{Conf}\le\mathrm{diam}(B^k_h)$.
--
--   `statesQL` is the sequence of algorithm states produced by a data sequence, `statesQL data k` being the state at the end of episode $k$.
--
--   **Formalization Note** In Eq. (10) the maximum is over the active balls of $\mathcal P^{k-1}_{h+1}$ containing $x$. The learning rate is the platform's `VLearning.CCE.lr`.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, §3.3.2, pp.17–18, Eq. (9)–(10); Algorithm 1, p.13

import Mathlib
import Definitions.Def_AdaDiscRL_AlgState
import Definitions.Def_AdaDiscRL_AdaParams
import Definitions.Def_VLearning_CCE_WeightedBandit

namespace AdaDiscRL

open Classical

variable {S A ι : Type*} [MeasurableSpace S] [MeasurableSpace A]
  {D : S × A → S × A → ℝ} {dS Lmax H : ℕ}

/-- Initial state (Algorithm 1 line 2, p.13): `P_h^0 = {S × A}` (the tree is the root), all counts
`0`, and the estimates `Q̄_h^0 = V̄_h^0 = Ṽ_h^0 = v₀(h)`. -/
def initState (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H) : AlgState S ι H :=
  fun h => { tree := {P.root}, n := fun _ => 0, Q := fun _ => prm.v0 h, rbar := fun _ => 0,
             Tbar := fun _ _ => 0, Vt := fun _ => prm.v0 h }

/-- AdaQL value estimate, Eq. (10), p.18: `V̄_h(x) = min(H, max_{B ∈ RELEVANT_h(x)} Q̄_h(B))`
(the maximum over the active balls of `P_h` containing `x`, reading R6). -/
noncomputable def VbarQL (P : HierPartition S A ι D dS Lmax) (σ : AlgState S ι H) (h : Fin H)
    (x : S) : ℝ :=
  min (H : ℝ) (sSup ((σ h).Q '' ↑(relevant P (σ h) x)))

/-- `V̄_{h+1}` seen from step `h : Fin H`, with `V̄_{H+1} ≡ 0` (Eq. (3)). -/
noncomputable def VnextQL (P : HierPartition S A ι D dS Lmax) (σ : AlgState S ι H) (h : Fin H)
    (x : S) : ℝ :=
  if hh : h.val + 1 < H then VbarQL P σ ⟨h.val + 1, hh⟩ x else 0

/-- One AdaQL step at the selected ball `B` (§3.3, pp.16–18; §3.4, p.19): `n(B) ← n(B) + 1`;
with `t = n(B)` and `α_t = (H+1)/(H+t)`, Eq. (9):
`Q̄(B) ← (1 − α_t) Q̄(B) + α_t (R + Rucb(B) + V̄_{h+1}^{k−1}(X_{h+1}) + Tucb(B) + Bias(B))`
(other balls unchanged); then split `B` if `Conf(B) ≤ diam(B)`, Eq. (12). `vnext` is
`V̄_{h+1}^{k−1}(X_{h+1})`. -/
noncomputable def stepQL (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H) (st : Stats S ι)
    (B : ι) (r vnext : ℝ) : Stats S ι :=
  let n' := st.n B + 1
  let α := VLearning.CCE.lr H n'
  let q' := (1 - α) * st.Q B +
    α * (r + prm.rucbQL n' + vnext + prm.tucbQL n' + prm.biasQL (P.diam B))
  let st1 : Stats S ι := { st with n := Function.update st.n B n', Q := Function.update st.Q B q' }
  if prm.confQL n' ≤ P.diam B then splitStats P st1 B else st1

/-- One AdaQL episode (Algorithm 1 lines 4–10, 17–18): at each step `h`, select
`B_h^k = argmax_{RELEVANT} Q̄_h^{k−1}` for the observed `X_h^k` and update with the observed
`R_h^k`, `X_{h+1}^k` and `V̄_{h+1}^{k−1}`. -/
noncomputable def updateQL (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H)
    (choose : Finset ι → (ι → ℝ) → ι) (σ : AlgState S ι H) (d : EpData S A H) :
    AlgState S ι H :=
  fun h => stepQL P prm (σ h) (selBall P choose σ h (d.1 h.castSucc)) (d.2.2 h)
    (VnextQL P σ h (d.1 h.succ))

/-- **AdaQL** run on a data sequence: `statesQL … data k` is the state at the end of episode `k`
(`k = 0`: initial), after processing the episodes `data 1, …, data k`. -/
noncomputable def statesQL (P : HierPartition S A ι D dS Lmax) (prm : AdaParams H)
    (choose : Finset ι → (ι → ℝ) → ι) (data : ℕ → EpData S A H) : ℕ → AlgState S ι H
  | 0 => initState P prm
  | k + 1 => updateQL P prm choose (statesQL P prm choose data k) (data (k + 1))

end AdaDiscRL


