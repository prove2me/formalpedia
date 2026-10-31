-- Prove2me | Definitions.Def_DynStochMatching_Reward_LinearPrograms
-- name    : DynStochMatching_Reward_LinearPrograms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:37:14.938042+00:00
-- url     : https://prove2.me/theorems/f0fd5228-a81e-4120-848c-5a227a5008d7
-- title:
--   Equational linear programs and an exact solver interface
-- statement:
--   Finite real linear programs maximize a linear objective under equality constraints and nonnegative variables. Feasibility, optimality and boundedness use the published MatousekLP definitions. The general LP oracle returns an optimal solution whenever feasibility and boundedness hold; it has no matching-specific guarantee. Its use is charged as one polynomial-size LP call in the computational model.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, §3 and §5.1, printed 10, 21–22 / PDF 11, 22–23

import Definitions.Def_MatousekLP_BFS_EquationalForm

namespace DynStochMatching.Reward

/-- Equational-form linear programs with the published feasibility/optimality convention. -/
structure LinearProgram where
  rows : ℕ
  cols : ℕ
  matrix : Matrix (Fin rows) (Fin cols) ℝ
  rhs : Fin rows → ℝ
  objective : Fin cols → ℝ

noncomputable def LinearProgram.feasible (P : LinearProgram) (v : Fin P.cols → ℝ) : Prop :=
  MatousekLP.BFS.IsFeasible P.matrix P.rhs v

noncomputable def LinearProgram.optimal (P : LinearProgram) (v : Fin P.cols → ℝ) : Prop :=
  MatousekLP.BFS.IsOptimal P.matrix P.rhs P.objective v

/-- General LP primitive interface. This carries LP correctness only, never a matching bound. -/
structure LinearOracle where
  solve : (P : LinearProgram) → (Fin P.cols → ℝ)
  correct : ∀ P : LinearProgram, (∃ v, P.feasible v) →
    MatousekLP.BFS.IsBoundedAbove P.matrix P.rhs P.objective → P.optimal (solve P)

end DynStochMatching.Reward


