-- Prove2me | Definitions.Def_ContJRP_Align_Policy
-- name    : ContJRP_Align_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:42.209791+00:00
-- url     : https://prove2.me/theorems/99d330dc-aa35-400e-85d4-d2a46fde210a
-- title:
--   §2.1, §2.6, §3.1 — T*_min, the easy policy, ⌈·⌉^{(R_1)}, T^max, the final policy, and the terms (I), (II), (III)
-- statement:
--   1. **Minimal interval.** $T^*_{\min}=\min_{i\in[n]}T^*_i$.
--
--   2. **Easy policy** (§2.1). $\hat T_i=\sqrt{(K_0+K_i)/H_i}$, the EOQ interval of commodity $i$ when the joint cost $K_0$ is charged to each of its orders.
--
--   3. **Final policy** (§2.6). Given approximate representatives $(R_\ell)_{\ell\in\mathcal A^*}$, let $\lceil x\rceil^{(r)}=\lceil x/r\rceil\cdot r$ be $x$ rounded up to an integer multiple of $r$, and $T^{\max}_i=\max\{\tilde T_{\min}/\epsilon,\sqrt{K_i/H_i}\}$. The options of commodity $i$ are the representatives $R_\ell$, $\ell\in\mathcal A^*$, and the single large interval $\lceil T^{\max}_i\rceil^{(R_1)}$. A policy $\hat T$ is a **final policy** when each $\hat T_i$ is one of these options and
--   $$C_i(\hat T_i)\le C_i(o)\quad\text{for every option } o \text{ of commodity } i .$$
--
--   4. **The terms of (4)** (§3.1). For $\Delta\ge0$,
--   $$\text{(I)}=\sum_{\mathcal A\text{ uncrossing}}(-1)^{|\mathcal A|+1}\Big|\bigcap_{\ell\in\mathcal A}\mathcal M_{R_\ell,\Delta}\Big|,\qquad \text{(II)}=\sum_{\mathcal A\text{ crossing}}(-1)^{|\mathcal A|+1}\Big|\bigcap_{\ell\in\mathcal A}\mathcal M_{R_\ell,\Delta}\Big|,$$
--   both over nonempty $\mathcal A\subseteq\mathcal A^*$, and $\text{(III)}=\sum_{C\in\mathrm{CC}(G^*_\Psi)}\big|\bigcup_{\ell\in C}\mathcal M_{R^*_\ell,\Delta}\big|$.
--
--   These are the policies whose costs Theorem 1.3 bounds, and the terms in which §3 analyses the joint orders.
--
--   **Formalization Note** The final policy is a predicate, not a chosen minimizer: every statement quantifies over all policies satisfying it, and the option set always contains the large interval, so such a policy exists. The paper's $R_1$ is Lean's `R 0`. (I) and (II) are integers. The sums run over nonempty sets only, matching inclusion–exclusion.
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 6 (§2.1, T*_min, easy policy), p. 11 (§2.6, final policy), pp. 13 and 15 (§3.1, (4), (I), (II), (III))

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment

namespace ContJRP.Align

open Classical

/-- The minimal ordering interval `T*_min = min_i T*_i` of a policy (§2.1, p. 6). -/
noncomputable def tmin {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty Tstar

/-- The easy-regime policy `T̂_i = √((K₀ + K_i)/H_i)`: each commodity at its EOQ interval with the
joint cost overloaded into its own ordering cost (§2.1, p. 6). -/
noncomputable def easyPolicy {n : ℕ} (K0 : ℝ) (K H : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt ((K0 + K i) / H i)

/-- `⌈x⌉^{(r)} = ⌈x / r⌉ · r`, the least integer multiple of `r > 0` that is at least `x ≥ 0`
(§2.6, p. 11). -/
noncomputable def roundUpMult (x r : ℝ) : ℝ := (⌈x / r⌉₊ : ℝ) * r

/-- `T^max_i = max{T̃_min/ε, √(K_i/H_i)}` (§2.6, p. 11). -/
noncomputable def tMax {n : ℕ} (K H : Fin n → ℝ) (ε Tt : ℝ) (i : Fin n) : ℝ :=
  max (Tt / ε) (Real.sqrt (K i / H i))

/-- The options for commodity `i` in §2.6, step 2: every approximate representative `R_ℓ`,
`ℓ ∈ A*`, and the single large interval `⌈T^max_i⌉^{(R_1)}` (Lean index `0` is the paper's `R̂_1`). -/
noncomputable def options {n : ℕ} (K H : Fin n → ℝ) (ε Tt : ℝ) (Tstar : Fin n → ℝ) (R : ℕ → ℝ)
    (i : Fin n) : Finset ℝ :=
  (active ε Tt Tstar).image R ∪ {roundUpMult (tMax K H ε Tt i) (R 0)}

/-- `That` is a final policy built from the approximate representatives `R` (§2.6, step 2): each
`That i` is one of the options of commodity `i` and minimizes `C_i` over those options. -/
def IsFinalPolicy {n : ℕ} (K H : Fin n → ℝ) (ε Tt : ℝ) (Tstar : Fin n → ℝ) (R : ℕ → ℝ)
    (That : Fin n → ℝ) : Prop :=
  ∀ i, That i ∈ options K H ε Tt Tstar R i ∧
    ∀ o ∈ options K H ε Tt Tstar R i, eoqCost (K i) (H i) (That i) ≤ eoqCost (K i) (H i) o

/-- `⋂_{ℓ ∈ s} M_{R_ℓ,Δ}` for a nonempty index set `s`. -/
noncomputable def interMultiples (s : Finset ℕ) (R : ℕ → ℝ) (Δ : ℝ) : Finset ℝ :=
  (s.biUnion fun ℓ => multiplesUpTo (R ℓ) Δ).filter (fun x => ∀ ℓ ∈ s, x ∈ multiplesUpTo (R ℓ) Δ)

/-- The uncrossing term (I) of (4): `Σ_{A uncrossing} (-1)^{|A|+1} |⋂_{ℓ ∈ A} M_{R_ℓ,Δ}|` (p. 13). -/
noncomputable def termI {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar R : ℕ → ℝ) (Δ : ℝ) : ℤ :=
  ∑ A ∈ (active ε Tt Tstar).powerset.filter (fun A => IsUncrossing ε Tt Tstar Rstar A),
    (-1 : ℤ) ^ (A.card + 1) * ((interMultiples A R Δ).card : ℤ)

/-- The crossing term (II) of (4): the same sum over the nonempty `A ⊆ A*` that are not
uncrossing (p. 13). -/
noncomputable def termII {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar R : ℕ → ℝ) (Δ : ℝ) : ℤ :=
  ∑ A ∈ (active ε Tt Tstar).powerset.filter
      (fun A => A.Nonempty ∧ ¬ IsUncrossing ε Tt Tstar Rstar A),
    (-1 : ℤ) ^ (A.card + 1) * ((interMultiples A R Δ).card : ℤ)

/-- The term (III) = `Σ_{C ∈ CC(G*_Ψ)} |⋃_{ℓ ∈ C} M_{R*_ℓ,Δ}|` (p. 15). -/
noncomputable def termIII {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ) (Δ : ℝ) : ℕ :=
  ∑ C ∈ components ε Tt Tstar Rstar, numOrders C Rstar Δ

end ContJRP.Align


