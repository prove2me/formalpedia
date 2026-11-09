-- Prove2me | Definitions.Def_OddPermSum_Evaluation_achievedExponent
-- name    : OddPermSum_Evaluation_achievedExponent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:19:00.841366+00:00
-- url     : https://prove2.me/theorems/f6275e49-79a8-4ff5-a51e-83fe5d6a678d
-- title:
--   Achieved matrix multiplication exponent and uniform cost contract
-- statement:
--   A supplied program $M$ multiplies within $(\omega,C_M,n_M)$ if $C_M>0$, it terminates on every pair of square matrices of every size, returns their full product, and its successful-run cost obeys
--
--   $$\operatorname{cost}_M(n,A,B)\le C_Mn^\omega\quad\text{when }n\ge\max(1,n_M).$$
--
--   An achieved exponent has $2<\omega\le3$ and admits such one finite program and uniform constants. Correctness and termination also hold below the threshold. The constant and threshold precede the size and entries; no $\varepsilon$, infimum exponent, field-value oracle, or unrelated family of programs is used. This is a specification of programs whose execution and cost were independently defined.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 5, Linear algebra paragraph; p. 2, Theorem 1.1

import Definitions.Def_OddPermSum_Evaluation_machineExecution
import Definitions.Def_OddPermSum_Evaluation_matrixEncoding

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Specification, separate from program syntax and execution. One finite program
handles all sizes and all pairs; C and n₀ precede every input quantifier. -/
def MultipliesWithin {F : Type*} [Field F] (p : AlgebraicProgram F)
    (ω C : ℝ) (n₀ : ℕ) : Prop :=
  0 < C ∧ ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) F),
    ∃ (fuel : ℕ) (s : MachineState F),
      run p n (matrixEncoding A ++ matrixEncoding B) fuel = some s ∧
      s.outputs = matrixEncoding (A * B) ∧
      (max 1 n₀ ≤ n → (s.cost : ℝ) ≤ C * (n : ℝ)^ω)

/-- Achieved O(n^ω), with no ε, infimum, or per-size program family. -/
def AchievedExponent (F : Type*) [Field F] (ω : ℝ) : Prop :=
  2 < ω ∧ ω ≤ 3 ∧ ∃ (p : AlgebraicProgram F) (C : ℝ) (n₀ : ℕ),
    MultipliesWithin p ω C n₀

end OddPermSum.Evaluation


