-- Prove2me | Definitions.Def_NestedLogitFPTAS_Neighbourhood
-- name    : NestedLogitFPTAS_Neighbourhood
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:26.167302+00:00
-- url     : https://prove2.me/theorems/df2c803d-ecdd-4e73-b6de-a97912eee71e
-- title:
--   §2.2, p.7, and (3), p.11 — the dual problem, the $(\delta_\omega,\delta_\rho)$-neighbourhood and $\mathcal P_\approx$
-- statement:
--   The dual problem of a $\mathcal C$-feasible $S^*$ minimizes the total cost over the assortments $S$ with $\omega_{[1,M]}(S)=\omega_{[1,M]}(S^*)$ and $\rho_{[1,M]}(S)=\rho_{[1,M]}(S^*)$.
--
--   Given accuracy levels $\delta_\omega,\delta_\rho$, the neighbourhood $\mathcal N_{(\delta_\omega,\delta_\rho)}(k,\omega_k,\rho_k)$ is the family of sets $T\subseteq N_k$ with
--   $$
--   w_+(T)\in(1\pm\delta_\omega)\cdot\omega_k^{1/\gamma_k},\qquad \mathcal R_k(T)\cdot w_+(T)^{\gamma_k}\in(1\pm\delta_\rho)\cdot\rho_k .
--   $$
--   The number $\mathcal P_{\approx(\delta_\omega,\delta_\rho)}(k,\omega_k,\rho_k)$ is the minimal cost of a set in the neighbourhood, and $\infty$ when it is empty. The module also defines $\lambda(T)=\sum_{i\in T}r_iw_i$ of §4.1.
--
--   These objects specify the single-nest step: they appear in the statements about the algorithm, and the program never enumerates them.
--
--   **Formalization Note** The paper writes the second condition as $\mathcal R_k(T)\in(1\pm\delta_\rho)\rho_k/w_+(T)^{\gamma_k}$, which is undefined at $T=\emptyset$. It is multiplied out here, and $\emptyset$ is a member exactly when $\omega_k=\rho_k=0$. With Lean's $x/0=0$, the set $\emptyset$ would wrongly belong to $\mathcal N(k,0,\rho_k)$ for $\rho_k>0$.
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §2.2, p.7; (3), p.11; §4.1, p.18

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model

namespace NestedLogitFPTAS

namespace Instance

variable {n M : ℕ} (I : Instance n M)

/-- `S` has the same `ω`- and `ρ`-quantities as `Sstar`: constraints (D₂), (D₃) of the dual problem
`F(1, ω[1,M](S*), ρ[1,M](S*))`, §2.2, p.7. Constraint (D₁) is the type of `S`. -/
def DualFeasible (Sstar S : Finset (Fin n)) : Prop :=
  I.omegaRange 1 M S = I.omegaRange 1 M Sstar ∧ I.rhoRange 1 M S = I.rhoRange 1 M Sstar

/-- `S` is an optimal solution of the dual problem of §2.2, p.7: of minimum total cost among the
dual-feasible assortments. -/
def IsDualOptimal (Sstar S : Finset (Fin n)) : Prop :=
  I.DualFeasible Sstar S ∧ ∀ S', I.DualFeasible Sstar S' → I.cost S ≤ I.cost S'

/-- `T ∈ N_(δω,δρ)(k, ωk, ρk)`: the `(δω,δρ)`-neighbourhood (3), §3.2, p.11.

**Formalization Note.** Eq. (3) reads `w₊(T) ∈ (1 ± δω)·ωk^{1/γk}` and
`Rk(T) ∈ (1 ± δρ)·ρk / w₊(T)^{γk}`. The quotient is undefined at `T = ∅`, and §4.1 calls the zero
cases trivial. The second condition is therefore multiplied out, and `∅` belongs to the
neighbourhood exactly when `ωk = ρk = 0`, which agrees with (P₂), (P₃). Lean's `x / 0 = 0` must not be
used here: it would put `∅` in `N(k, 0, ρk)` for `ρk > 0` at cost `0`. -/
def InNbhd (δω δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) (T : Finset (Fin n)) : Prop :=
  T ⊆ I.nestSet k ∧
    ((T = ∅ ∧ ωk = 0 ∧ ρk = 0) ∨
      (T.Nonempty ∧
        (1 - δω) * ωk ^ (1 / I.γ k) ≤ I.wplus k T ∧
        I.wplus k T ≤ (1 + δω) * ωk ^ (1 / I.γ k) ∧
        (1 - δρ) * ρk ≤ I.Rnest k T * I.wplus k T ^ I.γ k ∧
        I.Rnest k T * I.wplus k T ^ I.γ k ≤ (1 + δρ) * ρk))

open Classical in
/-- The neighbourhood `N_(δω,δρ)(k, ωk, ρk)` as a finite set. Specification only: the program never
enumerates subsets. -/
noncomputable def Nbhd (δω δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) : Finset (Finset (Fin n)) :=
  (I.nestSet k).powerset.filter (I.InNbhd δω δρ k ωk ρk)

/-- `P≈_(δω,δρ)(k, ωk, ρk)`, the minimal cost over the neighbourhood, `⊤` (`∞`) when it is empty,
§3.2, p.11. Specification only. -/
noncomputable def Papprox (δω δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) : WithTop ℝ :=
  (I.Nbhd δω δρ k ωk ρk).inf (fun T => ((I.cost T : ℝ) : WithTop ℝ))

/-- `λ(T) = Σ_{i∈T} λᵢ` with `λᵢ = rᵢ·wᵢ`, §4.1, p.18. -/
noncomputable def lam (T : Finset (Fin n)) : ℝ := ∑ i ∈ T, I.r i * I.w i

end Instance

end NestedLogitFPTAS


