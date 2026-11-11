-- Prove2me | Definitions.Def_LpBallVI_Affine_SymNash
-- name    : LpBallVI_Affine_SymNash
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:10:26.996693+00:00
-- url     : https://prove2.me/theorems/e24dce6b-3921-45a2-bb14-205f3a986bce
-- title:
--   Approximate symmetric Nash equilibria of symmetric bimatrix games (A, Aᵀ) as a search problem
-- statement:
--   For a rational $A \in [0,1]^{d\times d}$, $d \ge 1$, a point $x \in \Delta_d$ (nonnegative, summing to 1) is an **$\varepsilon$-approximate symmetric Nash equilibrium** of $(A, A^\top)$ if
--   $$\max_i (Ax)_i - x^\top A x \le \varepsilon.$$
--   The search problem at accuracy $\varepsilon(d)$ has as inputs the codes of such $A$ and as answers the codes of rational $\varepsilon(d)$-approximate symmetric equilibria.
--
--   **Formalization Note** The accuracy is a function of the number $d$ of strategies, not an input. Codes are `encRatMatrix`/`encRatVec`; answers have no length bound.
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 36, §4.3.1, case p = 1

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix

set_option autoImplicit false

namespace LpBallVI.Affine

open scoped BigOperators

/-- `x ∈ ∆_d` is an **`ε`-approximate symmetric Nash equilibrium** of the symmetric game `(A, Aᵀ)`
(Anagnostides–Panageas–Yan, arXiv:2611.04151, §4.3.1, case p = 1, p. 36): `x` is a probability
vector and `max_i (A x)_i − xᵀ A x ≤ ε`, i.e. `(A x)_i − xᵀ A x ≤ ε` for every pure strategy `i`. -/
def IsSymApproxNash {d : ℕ} (A : Fin d → Fin d → ℝ) (x : Fin d → ℝ) (ε : ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧
    ∀ i, (∑ j, A i j * x j) - (∑ k, ∑ j, x k * A k j * x j) ≤ ε

/-- **The search problem: approximate symmetric Nash equilibria of symmetric bimatrix games**, at
the accuracy `ε(d)` (p. 36): a valid string is the code `encRatMatrix d A` of a rational
`A ∈ [0, 1]^{d×d}` with `d ≥ 1`; an answer is the code `encRatVec d x` of a rational `x ∈ ∆_d` that
is an `ε(d)`-approximate symmetric Nash equilibrium of `(A, Aᵀ)`.

**Formalization Note** The accuracy is a fixed function of the number `d` of pure strategies, not
an input; "inverse-polynomial" accuracy is `ε(d) = d^{−c}`. Answers have no length bound. -/
def SymNash (ε : ℕ → ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (d : ℕ) (A : Fin d → Fin d → ℚ),
    1 ≤ d ∧ (∀ i j, 0 ≤ A i j ∧ A i j ≤ 1) ∧ s = CardinalMatching.encRatMatrix d A
  answer s t := ∃ (d : ℕ) (A : Fin d → Fin d → ℚ),
    1 ≤ d ∧ (∀ i j, 0 ≤ A i j ∧ A i j ≤ 1) ∧ s = CardinalMatching.encRatMatrix d A ∧
    ∃ x : Fin d → ℚ, t = CardinalMatching.encRatVec d x ∧
      IsSymApproxNash (fun i j => (A i j : ℝ)) (fun i => (x i : ℝ)) (ε d)

end LpBallVI.Affine


