-- Prove2me | Definitions.Def_LpBallVI_Affine_CircBallVI
-- name    : LpBallVI_Affine_CircBallVI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:10.85642+00:00
-- url     : https://prove2.me/theorems/1f2eba81-cb3c-4a5e-a728-482b8c5cd3d3
-- title:
--   Ballp-VI for operators given by well-behaved arithmetic circuits over {+, −, ×, min, max}, with a rational accuracy ε ∈ (0,1) in binary
-- statement:
--   An input is $(d, C, \varepsilon)$: a well-behaved arithmetic circuit $C$ with $d$ inputs and $d$ outputs over rational constants and $\{+, -, \times, \min, \max\}$ (no comparison gate), whose operator $F = C$ is 1-Lipschitz on $B^d_p$ in the Euclidean norm, and a rational $\varepsilon \in (0,1)$. An answer is a rational $x \in B^d_p$ with
--   $$\operatorname{Gap}_{B^d_p}(x; F) = \max_{x' \in B^d_p} \langle x' - x, F(x)\rangle \le \varepsilon.$$
--
--   **Formalization Note** Circuits, well-behavedness, exact real evaluation and code are the public `NadlerCLS.Circ`, `Circ.Valid`, `Circ.eval`, `encCirc`; `NoTestGate` excludes that gate set's comparison gate. Input code: $d$ in binary, the circuit, then $\varepsilon$; answers coded by `encRatVec`, no length bound.
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 4, Ballp-VI; p. 50, Theorem B.1

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_NadlerCLS_Circ
import Definitions.Def_LpBallVI_Affine_Geometry

set_option autoImplicit false

namespace LpBallVI.Affine

/-- The circuit uses only the operations `{+, −, ×, min, max}` (and inputs and rational constants):
no gate is the comparison gate `ArithmeticGate.test` of the public `NadlerCLS.Circ` gate set
(Anagnostides–Panageas–Yan, arXiv:2611.04151, p. 4). -/
def NoTestGate (C : NadlerCLS.Circ) : Prop :=
  ∀ g ∈ C.gates, ∀ a b : ℕ, g ≠ NetworkEquilibriumCLS.LinearNash.ArithmeticGate.test a b

/-- A valid circuit instance `(d, C, ε)` of `Ballp-VI` (p. 4; Theorem B.1, p. 50): `C` is a valid
well-behaved arithmetic circuit with `d` inputs and `d` outputs over rational constants and
`{+, −, ×, min, max}`, the operator `F = C.eval : ℝ^d → ℝ^d` is 1-Lipschitz on the unit ball `B^d_p`
in the Euclidean norm, and `ε ∈ (0, 1)` is rational. -/
def CircValid (p : Exponent) (d : ℕ) (C : NadlerCLS.Circ) (ε : ℚ) : Prop :=
  C.Valid d d ∧ NoTestGate C ∧ 0 < ε ∧ ε < 1 ∧
    ∀ x ∈ (p.unitBall : Set (Fin d → ℝ)), ∀ y ∈ (p.unitBall : Set (Fin d → ℝ)),
      eucNorm (fun j : Fin d => C.eval x j - C.eval y j) ≤ eucNorm (x - y)

/-- **The search problem `Ballp-VI`** (p. 4) for operators given by well-behaved arithmetic
circuits. A valid string is the code `encBin d ++ encCirc C ++ encRat ε` of a valid triple
`(d, C, ε)` (`CircValid`); an answer is the code `encRatVec d x` of a rational point `x ∈ B^d_p` with
`Gap_{B^d_p}(x; F) = max_{x' ∈ B^d_p} ⟨x' − x, F(x)⟩ ≤ ε`, where `F = C.eval`.

**Formalization Note** Circuits, their validity (well-behavedness), exact real evaluation and code
are the public `NadlerCLS.Circ`, `Circ.Valid`, `Circ.eval`, `encCirc`; `NoTestGate` removes that
gate set's comparison gate, which the paper's `{+, −, ×, min, max}` lacks. Answers are rational
points with no length bound. -/
def CircBallVI (p : Exponent) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (d : ℕ) (C : NadlerCLS.Circ) (ε : ℚ), CircValid p d C ε ∧
    s = QAlgorithms.LocalHamiltonian.encBin d ++ NadlerCLS.encCirc C ++
      QAlgorithms.LocalHamiltonian.encRat ε
  answer s t := ∃ (d : ℕ) (C : NadlerCLS.Circ) (ε : ℚ), CircValid p d C ε ∧
    s = QAlgorithms.LocalHamiltonian.encBin d ++ NadlerCLS.encCirc C ++
      QAlgorithms.LocalHamiltonian.encRat ε ∧
    ∃ x : Fin d → ℚ, t = CardinalMatching.encRatVec d x ∧
      (fun i => (x i : ℝ)) ∈ p.unitBall ∧
      GapLE p.unitBall (fun (y : Fin d → ℝ) (j : Fin d) => C.eval y j) (fun i => (x i : ℝ))
        (ε : ℝ)

end LpBallVI.Affine


