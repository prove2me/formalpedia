-- Prove2me | Definitions.Def_KuhnWass2019_Reformulation_finiteProgramValue
-- name    : KuhnWass2019_Reformulation_finiteProgramValue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T03:15:21.056811+00:00
-- url     : https://prove2.me/theorems/60275991-a159-4f33-8ed9-095572a971d1
-- title:
--   Finite convex program for every finite Wasserstein order
-- statement:
--   The program value is the infimum of $\gamma\varepsilon^p+N^{-1}\sum_i s_i$ over $\gamma\ge0$, real $s_i$, and dual vectors $u_{ij},v_{ij}$ satisfying $[-\ell_j]^*(u_{ij}-v_{ij})+\sigma_\Xi(v_{ij})-u_{ij}(\widehat\xi_i)+\mathrm{penalty}_p(\gamma,u_{ij})\le s_i$ for every $i,j$. For $p=1$ the penalty is the dual-norm-ball indicator; for $p>1$ it is the closed conjugate-power perspective. The infimum is taken in the extended reals, so infeasibility gives $+\infty$ and unboundedness below gives $-\infty$. No minimizer is asserted.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), p. 11, Theorem 8, equation (11), and Remark 1

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting
import Definitions.Def_KuhnWass2019_Reformulation_powerPerspective

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- The infimum in (11), including the p=1 constraints in Remark 1.
The real epigraph variables ensure that an infeasible program has value +∞. -/
noncomputable def finiteProgramValue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε p : ℝ) (Ξ : Set E) {N J : ℕ} (ξhat : Fin N → E) (ℓ : Fin J → E → EReal) : EReal :=
  ⨅ (γ : ℝ) (s : Fin N → ℝ)
    (u : Fin N → Fin J → StrongDual ℝ E) (v : Fin N → Fin J → StrongDual ℝ E)
    (_ : 0 ≤ γ)
    (_ : ∀ i j, WassDDRO.Reduction.conjOn Set.univ (fun x => -ℓ j x) (u i j - v i j)
      + WassDDRO.Reduction.supportFun Ξ (v i j) - ((u i j (ξhat i) : ℝ) : EReal)
      + powerPerspective p γ (u i j) ≤ (s i : EReal)),
    ((γ * ε ^ p + (1 / (N : ℝ)) * ∑ i, s i : ℝ) : EReal)

end KuhnWass2019.Reformulation


