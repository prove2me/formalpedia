-- Prove2me | Definitions.Def_LpBallVI_Affine_LinVI
-- name    : LpBallVI_Affine_LinVI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:10:31.136127+00:00
-- url     : https://prove2.me/theorems/4e3750a0-80fc-4e90-a1eb-3ee6baa13d9a
-- title:
--   LinVI over [0,1]^d at a fixed accuracy ε
-- statement:
--   A valid LinVI pair is a rational $D \in [-1,1]^{d\times d}$ with $\|D\|_1 \le 1$ (absolute column sums at most 1) and $\|D\|_\infty \le 1$ (absolute row sums at most 1) and a rational $b \in [-1,1]^d$. **LinVI at accuracy $\varepsilon$** asks for a point $z \in [0,1]^d$ with
--   $$(Dz + b)_i (z'_i - z_i) \ge -\varepsilon \qquad \forall i \in [d],\ \forall z'_i \in [0, 1].$$
--
--   **Formalization Note** In the paper $\varepsilon \in (0,1]$ is part of the input; Lemma 4.11 concerns instances whose $\varepsilon$ is one absolute constant, so the problem is indexed by that constant. Inputs are coded by `encRatMatrix`/`encRatVec`, answers are rational points coded by `encRatVec`.
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 36, §4.3.1, case p = ∞

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix

set_option autoImplicit false

namespace LpBallVI.Affine

open scoped BigOperators

/-- A valid `LinVI` matrix–vector pair over the hypercube (Anagnostides–Panageas–Yan,
arXiv:2611.04151, §4.3.1, p. 36): a rational `D ∈ [−1, 1]^{d×d}` with `‖D‖₁ ≤ 1` (every column
has absolute sum at most `1`) and `‖D‖_∞ ≤ 1` (every row has absolute sum at most `1`), and a
rational `b ∈ [−1, 1]^d`. -/
def LinVIValid (d : ℕ) (D : Fin d → Fin d → ℚ) (b : Fin d → ℚ) : Prop :=
  (∀ i j, |D i j| ≤ 1) ∧ (∀ j, ∑ i, |D i j| ≤ 1) ∧ (∀ i, ∑ j, |D i j| ≤ 1) ∧ (∀ i, |b i| ≤ 1)

/-- **The search problem `LinVI` at a fixed accuracy `ε`** (p. 36). A valid string is the code
`encRatMatrix d D ++ encRatVec d b` of a valid pair (`LinVIValid`); an answer is the code
`encRatVec d z` of a rational `z ∈ [0, 1]^d` with `(D z + b)ᵢ (z'ᵢ − zᵢ) ≥ −ε` for every `i` and
every `z'ᵢ ∈ [0, 1]`.

**Formalization Note** In the paper the accuracy `ε ∈ (0, 1]` is part of the input; Lemma 4.11 is
about instances whose `ε` is one absolute constant, so the problem is indexed by that constant
and `ε` is not encoded. Answers are rational points with no length bound. -/
def LinVI (ε : ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (d : ℕ) (D : Fin d → Fin d → ℚ) (b : Fin d → ℚ),
    LinVIValid d D b ∧ s = CardinalMatching.encRatMatrix d D ++ CardinalMatching.encRatVec d b
  answer s t := ∃ (d : ℕ) (D : Fin d → Fin d → ℚ) (b : Fin d → ℚ),
    LinVIValid d D b ∧ s = CardinalMatching.encRatMatrix d D ++ CardinalMatching.encRatVec d b ∧
    ∃ z : Fin d → ℚ, t = CardinalMatching.encRatVec d z ∧ (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧
      ∀ i, ∀ z' : ℝ, 0 ≤ z' → z' ≤ 1 →
        -ε ≤ ((∑ j, (D i j : ℝ) * (z j : ℝ)) + (b i : ℝ)) * (z' - (z i : ℝ))

end LpBallVI.Affine


