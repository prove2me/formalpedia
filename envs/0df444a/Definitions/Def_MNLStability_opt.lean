-- Prove2me | Definitions.Def_MNLStability_opt
-- name    : MNLStability_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:05.728589+00:00
-- url     : https://prove2.me/theorems/79653b72-b861-4173-b962-781d52456b4b
-- title:
--   Feasible inventory vectors and the optimal expected revenue
-- statement:
--   An inventory vector $U\in\mathbb Z_+^n$ is **feasible** when $\|U\|_1=\sum_i U_i\le C$. The optimal expected revenue of an instance is
--
--   $$\mathrm{OPT}=\max\Bigl\{\mathbb E[R(U)]: U\in\mathbb Z_+^n,\ \sum_{i=1}^n U_i\le C\Bigr\}.$$
--
--   The goal theorem compares the expected revenue of the returned vector with $\mathrm{OPT}$.
--
--   **Formalization Note** The feasible set is finite and contains $0$, so the maximum is a maximum over a nonempty `Finset` and is attained (proved in the sanity file).
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §1.1, pp.3–4

import Mathlib
import Definitions.Def_MNLStability_Inst
import Definitions.Def_MNLStability_expX

namespace MNLStability

variable {n : ℕ}

/-- `‖U‖₁ = Σ_i U_i`, the total number of units stocked by `U`. -/
def norm1 (U : Fin n → ℕ) : ℕ := ∑ i, U i

/-- The feasible inventory vectors `{U ∈ ℤ₊ⁿ : Σ_i u_i ≤ C}` (SSRN:3498325, §1.1, p.3), as a finite
set. -/
def feasSet (n C : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (C + 1)).filter fun U => norm1 U ≤ C

lemma zero_mem_feasSet (n C : ℕ) : (0 : Fin n → ℕ) ∈ feasSet n C := by
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ => by simp, by simp [norm1]⟩

/-- The optimal expected revenue of an instance, `max { E[R(U)] : U ∈ ℤ₊ⁿ, Σ_i u_i ≤ C }`
(SSRN:3498325, §1.1, p.4).

**Formalization Note.** A maximum over the finite, nonempty set `feasSet` (it contains `0`), so it
is attained. -/
noncomputable def opt (I : Inst n) : ℝ :=
  (feasSet n I.C).sup' ⟨0, zero_mem_feasSet n I.C⟩ (expR I.wts I.r I.pM)

end MNLStability


