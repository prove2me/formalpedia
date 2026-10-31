-- Prove2me | Definitions.Def_AubinLipschitz_blockProcess
-- name    : AubinLipschitz_blockProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:33.319751+00:00
-- url     : https://prove2.me/theorems/8c92d38e-1d40-4f8c-9043-8046a24b41db
-- title:
--   The block matrix of processes $\begin{pmatrix}P&A^*\\-A&R\end{pmatrix}$
-- statement:
--   For set-valued maps $P$ from $X$ to $X^*$ and $R$ from $Y^*$ to $Y$ and a linear operator $A:X\to Y$, the matrix
--
--   $$
--   \begin{pmatrix}P & A^*\\ -A & R\end{pmatrix}
--   $$
--
--   denotes the set-valued map from $X\times Y^*$ to $X^*\times Y$ whose value at $(\delta x,\delta q)$ is
--
--   $$
--   \{(a+A^*\delta q,\ -A\delta x+b)\mid a\in P(\delta x),\ b\in R(\delta q)\}.
--   $$
--
--   This notation is used in the hypothesis and the conclusion of the goal, and in Corollary 1 of §5.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Theorem 1, p.32, and Corollary 1, p.35

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, p.32 and Corollary 1, p.35: the process given by the matrix
`[[P, A*], [−A, R]]` for `P : X ⇉ X*`, `R : Y* ⇉ Y` and `A : X → Y`, from `X × Y*` to `X* × Y`:
its value at `(δx, δq)` is the set of `(a + A*δq, −A δx + b)` with `a ∈ P(δx)`, `b ∈ R(δq)`.

**Formalization Note** The paper's "from `X × Y` to itself" (p.32) identifies `X` with `X*`
and `Y` with `Y*`; the matrix entries show the domain `X × Y*` and range `X* × Y`. -/
def blockProcess {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (P : X → Set (StrongDual ℝ X)) (A : X →L[ℝ] Y) (R : StrongDual ℝ Y → Set Y) :
    X × StrongDual ℝ Y → Set (StrongDual ℝ X × Y) :=
  fun z => {w | ∃ a ∈ P z.1, ∃ b ∈ R z.2, w = (a + z.2.comp A, -(A z.1) + b)}

end AubinLipschitz


