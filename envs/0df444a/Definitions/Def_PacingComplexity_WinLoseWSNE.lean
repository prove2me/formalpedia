-- Prove2me | Definitions.Def_PacingComplexity_WinLoseWSNE
-- name    : PacingComplexity_WinLoseWSNE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:20.530264+00:00
-- url     : https://prove2.me/theorems/3cb4a6a2-1fcb-49df-9a0e-c58e10984fb1
-- title:
--   The search problem WIN-LOSE-WSNE
-- statement:
--   **WIN-LOSE-WSNE** is the following search problem on bit strings.
--
--   1. **Instances:** an integer $n\ge1$ and two $n\times n$ cost matrices $A,B$ with all entries in $\{0,1\}$, encoded in binary.
--   2. **Answers:** rational vectors $x,y$, encoded in binary, that form a $\tfrac1n$-well-supported Nash equilibrium of $(A,B)$.
--
--   Chen, Teng and Valiant (2007), cited in the paper, show that this problem is PPAD-hard; the mission's hardness theorems are reductions from it.
--
--   **Formalization Note** Encodings use the platform's public rational vector and matrix codes. Rational answers lose nothing, since a bimatrix game with rational costs has a rational Nash equilibrium.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Appendix A, p.30 ('{0, 1}-cost n × n bimatrix game (A, B) and let ε = 1/n') and p.34

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_PacingComplexity_IsWSNE

namespace PacingComplexity

open CardinalMatching

/-- **WIN-LOSE-WSNE**, the search problem the hardness proof reduces from (Chen, Kroer, Kumar, *The
Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2, Appendix A, p.30: "Consider a
{0, 1}-cost n × n bimatrix game (A, B) and let ε = 1/n"; p.34: "the PPAD-hardness of finding an
ε-well-supported Nash equilibrium in a {0, 1}-cost bimatrix game Chen et al. [2007]").
* An instance is the code `encRatMatrix n A ++ encRatMatrix n B` of `n ≥ 1` and two `n × n` cost
  matrices with all entries in `{0, 1}`.
* An answer is the code `encRatVec n x ++ encRatVec n y` of rational vectors `x`, `y` that, as
  real vectors, form a `1/n`-well-supported Nash equilibrium of `(A, B)` (`IsWSNE`).

**Formalization Note** Binary encodings on the platform's public `encRatMatrix`/`encRatVec`
(self-delimiting, so a string encodes at most one instance). Rational answers lose nothing: every
bimatrix game with rational costs has a rational Nash equilibrium. -/
noncomputable def WinLoseWSNE : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (n : ℕ) (A B : Fin n → Fin n → ℚ),
    1 ≤ n ∧ (∀ i j, A i j = 0 ∨ A i j = 1) ∧ (∀ i j, B i j = 0 ∨ B i j = 1) ∧
    s = encRatMatrix n A ++ encRatMatrix n B
  answer s t := ∃ (n : ℕ) (A B : Fin n → Fin n → ℚ) (x y : Fin n → ℚ),
    1 ≤ n ∧ (∀ i j, A i j = 0 ∨ A i j = 1) ∧ (∀ i j, B i j = 0 ∨ B i j = 1) ∧
    s = encRatMatrix n A ++ encRatMatrix n B ∧ t = encRatVec n x ++ encRatVec n y ∧
    IsWSNE (1 / (n : ℝ)) (fun i j => (A i j : ℝ)) (fun i j => (B i j : ℝ))
      (fun i => (x i : ℝ)) (fun j => (y j : ℝ))

end PacingComplexity


