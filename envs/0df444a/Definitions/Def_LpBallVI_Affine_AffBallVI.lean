-- Prove2me | Definitions.Def_LpBallVI_Affine_AffBallVI
-- name    : LpBallVI_Affine_AffBallVI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:07.949012+00:00
-- url     : https://prove2.me/theorems/5babc095-92bc-4902-917e-7f8de4883b69
-- title:
--   The affine ℓp-ball VI search problem AffBallVI(p, ε): instances (d, A, b), answers rational points with VI gap at most ε(d)
-- statement:
--   Fix an exponent $p$ (a rational, or $\infty$) and an accuracy function $\varepsilon : \mathbb N \to \mathbb R$. A **valid affine instance** is $(d, A, b)$ with $d \ge 1$, $A \in \mathbb Q^{d\times d}$, $b \in \mathbb Q^d$, every coefficient in $[-1, 1]$, such that $F(z) = Az + b$ is 1-Lipschitz on $B^d_p$ in the Euclidean norm: $\|F(x) - F(y)\| \le \|x - y\|$ for $x, y \in B^d_p$.
--
--   **AffBallVI$(p, \varepsilon)$** is the search problem whose valid inputs are the binary codes $\mathrm{encRatMatrix}(d, A) \,\|\, \mathrm{encRatVec}(d, b)$ of valid instances, and whose answers to such an input are the codes $\mathrm{encRatVec}(d, x)$ of rational points $x$ with
--   $$\|x\|_p \le 1, \qquad \max_{x' \in B^d_p} \langle x' - x, Ax + b\rangle \le \varepsilon(d).$$
--
--   This is the problem Ballp-VI of p. 4 restricted to affine operators specified by their rational coefficients (Theorem 4.1).
--
--   **Formalization Note** The accuracy is not an input: it is $\varepsilon(d)$ for the instance's own dimension. Answers are rational points with no length bound. Codes are the public self-delimiting `CardinalMatching.encRatMatrix`/`encRatVec`.
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 4, Ballp-VI; p. 19, Theorem 4.1

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_LpBallVI_Affine_Geometry

set_option autoImplicit false

namespace LpBallVI.Affine

open scoped BigOperators

/-- The affine operator `F(z) = A z + b` on `ℝ^d` with rational `A`, `b` (Theorem 4.1, p. 19). -/
def affineOp {d : ℕ} (A : Fin d → Fin d → ℚ) (b : Fin d → ℚ) (z : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (∑ j, (A i j : ℝ) * z j) + (b i : ℝ)

/-- A valid affine instance `(d, A, b)` of `Ballp-VI` (p. 4 and Theorem 4.1, p. 19): `d ≥ 1`,
every coefficient of `A ∈ ℚ^{d×d}` and `b ∈ ℚ^d` lies in `[−1, 1]`, and `F(z) = A z + b` is
1-Lipschitz on the unit ball `B^d_p` with respect to the Euclidean norm. -/
def AffValid (p : Exponent) (d : ℕ) (A : Fin d → Fin d → ℚ) (b : Fin d → ℚ) : Prop :=
  1 ≤ d ∧ (∀ i j, |A i j| ≤ 1) ∧ (∀ i, |b i| ≤ 1) ∧
    ∀ x ∈ p.unitBall, ∀ y ∈ p.unitBall,
      eucNorm (affineOp A b x - affineOp A b y) ≤ eucNorm (x - y)

/-- **The search problem `AffBallVI(p, ε)`**: `Ballp-VI` (p. 4) for affine operators specified by
their rational coefficients (Theorem 4.1, p. 19), at the accuracy `ε(d)`, a fixed function of the
dimension.

A string `s` is a valid instance iff it is the code `encRatMatrix d A ++ encRatVec d b` of a valid
affine instance `(d, A, b)` (`AffValid`). An answer `t` to `s` is the code `encRatVec d x` of a
rational point `x` of the unit ball `B^d_p` whose VI gap is at most `ε(d)`:
`max_{x' ∈ B^d_p} ⟨x' − x, A x + b⟩ ≤ ε(d)`.

**Formalization Note** The accuracy is not part of the input: it is `ε d` for the instance's own
dimension `d`. Answers are rational points (codes of bit strings) with no length bound. Codes are
the public `CardinalMatching.encRatMatrix` / `encRatVec` (self-delimiting binary). -/
def AffBallVI (p : Exponent) (ε : ℕ → ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (d : ℕ) (A : Fin d → Fin d → ℚ) (b : Fin d → ℚ),
    AffValid p d A b ∧ s = CardinalMatching.encRatMatrix d A ++ CardinalMatching.encRatVec d b
  answer s t := ∃ (d : ℕ) (A : Fin d → Fin d → ℚ) (b : Fin d → ℚ),
    AffValid p d A b ∧ s = CardinalMatching.encRatMatrix d A ++ CardinalMatching.encRatVec d b ∧
    ∃ x : Fin d → ℚ, t = CardinalMatching.encRatVec d x ∧
      (fun i => (x i : ℝ)) ∈ p.unitBall ∧
      GapLE p.unitBall (affineOp A b) (fun i => (x i : ℝ)) (ε d)

end LpBallVI.Affine


