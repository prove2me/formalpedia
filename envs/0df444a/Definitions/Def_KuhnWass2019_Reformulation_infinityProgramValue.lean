-- Prove2me | Definitions.Def_KuhnWass2019_Reformulation_infinityProgramValue
-- name    : KuhnWass2019_Reformulation_infinityProgramValue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T03:14:47.425461+00:00
-- url     : https://prove2.me/theorems/25f2a296-9a79-4a66-9477-99fc5767b0e6
-- title:
--   Convex program at the type-infinity endpoint
-- statement:
--   The endpoint program minimizes $N^{-1}\sum_i s_i$ in the sense of an infimum over real $s_i$ and dual vectors $u_{ij},v_{ij}$, subject to $[-\ell_j]^*(u_{ij}-v_{ij})+\sigma_\Xi(v_{ij})-u_{ij}(\widehat\xi_i)+\varepsilon\|u_{ij}\|_*\le s_i$. There is no multiplier term in the objective. Infeasibility gives $+\infty$; no attainment is asserted.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), p. 11, Remark 1

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- Remark 1, p=infinity: epsilon times the dual norm, with no multiplier
in the objective. The value is an infimum and does not assert attainment. -/
noncomputable def infinityProgramValue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (Ξ : Set E) {N J : ℕ} (ξhat : Fin N → E) (ℓ : Fin J → E → EReal) : EReal :=
  ⨅ (s : Fin N → ℝ) (u : Fin N → Fin J → StrongDual ℝ E) (v : Fin N → Fin J → StrongDual ℝ E)
    (_ : ∀ i j, WassDDRO.Reduction.conjOn Set.univ (fun x => -ℓ j x) (u i j - v i j)
      + WassDDRO.Reduction.supportFun Ξ (v i j) - ((u i j (ξhat i) : ℝ) : EReal)
      + ((ε * ‖u i j‖ : ℝ) : EReal) ≤ (s i : EReal)),
    (((1 / (N : ℝ)) * ∑ i, s i : ℝ) : EReal)

end KuhnWass2019.Reformulation


