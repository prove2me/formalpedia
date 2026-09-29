-- Prove2me | Definitions.Def_SmaleNinth_Khachiyan
-- name    : SmaleNinth_Khachiyan
-- status  : Definition
-- author  : @ORdos
-- created : 2026-09-06T15:07:57.367943+00:00
-- url     : https://prove2.me/theorems/75d2dd69-08d6-4664-9a24-9c7ef553cdf0
-- title:
--   Khachiyan's perturbed-and-boxed system and iteration budget
-- statement:
--   Deciding a linear system by the ellipsoid method requires converting it into one that is bounded and, when feasible, of guaranteed positive volume — the ellipsoid iteration can only detect a feasible set that is not vanishingly thin, and cannot terminate on a set that is unbounded. For **integer** data this conversion is possible with explicit constants, and this module fixes one admissible choice of them.
--
--   Throughout, $A \in \mathbb{Z}^{m\times n}$ and $b \in \mathbb{Z}^m$ have all entries bounded in absolute value by an integer $U \ge 1$.
--
--   **The perturbation and the box.** The two basic constants are
--
--   $$\varepsilon \;=\; \frac{1}{2\,(n+1)\,(n+1)!\;U^{\,n+1}}, \qquad\qquad M \;=\; n!\;U^{\,n} + 1 .$$
--
--   Here $\varepsilon$ is a relaxation small enough not to create feasibility where there was none, and $M$ is a box radius large enough that a feasible system has a solution inside the box; both magnitudes come from Cramer-type determinant bounds on integer matrices, whose determinants are either $0$ or at least $1$ in absolute value while being at most $n!\,U^n$ in size.
--
--   **The perturbed-and-boxed system.** These are combined into the single system in $n$ variables with $m + 2n$ rows
--
--   $$\begin{pmatrix} A \\ I_n \\ -I_n\end{pmatrix} x \;\ge\; \begin{pmatrix} b - \varepsilon\mathbf{1} \\ -M\mathbf{1} \\ -M\mathbf{1}\end{pmatrix}, \qquad\text{that is}\qquad Ax \ge b - \varepsilon\mathbf{1}, \quad -M \le x_j \le M \ \ (j = 0,\dots,n-1),$$
--
--   whose solution set is the object the ellipsoid method is actually run on.
--
--   **The geometric budget.** Three further quantities describe that run: the **enclosing radius** $r = (n+1)M$, bounding the perturbed-and-boxed solution set inside the ball of radius $r$ about the origin; the **volume floor** $v = \bigl(\varepsilon/(nU)\bigr)^{n}$, a lower bound for that solution set's volume when it is nonempty; and the **iteration budget**
--
--   $$t^{*} \;=\; \Bigl\lceil\, 2\,(n+1)\,\log\frac{(2r)^{n}}{v/2} \,\Bigr\rceil ,$$
--
--   obtained by feeding the enclosing cube's volume $(2r)^n$ and the strict volume floor $v/2$ into the ellipsoid method's volume-halving iteration count.
--
--   **Conventions.** Only the polynomial order of these constants matters — $t^*$ is polynomial in $n$ and $\log U$ — and every step below tolerates replacing them by any other valid choice; they are pinned down here so that the statements built on them are fully explicit rather than asymptotic. The definitions are total functions of $n$ and $U$ and degenerate outside the intended range: for $U = 0$ the perturbation and the volume floor collapse to $0$ and the budget to a junk value, which is why every statement using them assumes $U \ge 1$. Nothing here asserts a property of these quantities; the assertions are the accompanying theorems.
-- source:
--   L.G. Khachiyan, A polynomial algorithm in linear programming, Soviet Math. Doklady 20 (1979) 191-194; quantification per B. Korte, J. Vygen, Combinatorial Optimization, 6th ed., Springer, Sections 4.4-4.5, and Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Section 8.4.

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_Ellipsoid

/-!
The perturbed-and-boxed system through which the ellipsoid method decides
the feasibility of a linear system with integer data — the quantitative
scaffolding of Khachiyan's theorem.

Source: L.G. Khachiyan, *A polynomial algorithm in linear programming*,
Soviet Math. Doklady 20 (1979) 191–194, in the standard textbook
quantification of B. Korte, J. Vygen, *Combinatorial Optimization*, 6th ed.,
Springer, §4.4–4.5, and Bertsimas–Tsitsiklis, *Introduction to Linear
Optimization*, §8.4. The constants below follow the classical
Cramer–Hadamard estimates; they are chosen generously (any valid choice
of the same polynomial order works) and are fixed here once so that every
statement built on them is fully explicit:

- `khachiyanEps n U = 1 / (2 (n+1) (n+1)! U^(n+1))` — a perturbation so
  small that `{x | Ax ≥ b}` and `{x | Ax ≥ b − ε𝟙}` are simultaneously
  empty or nonempty (via Farkas and a Cramer bound on a basic dual
  certificate).
- `khachiyanBox n U = n!·U^n + 1` — a box radius `M` such that a nonempty
  `{x | Ax ≥ b}` contains a point with `|x_j| ≤ M − 1` (Cramer–Hadamard
  bound on a point of a minimal face).
- `khachiyanSystemA / khachiyanSystemb` — the stacked system
  `Ax ≥ b − ε𝟙, x ≥ −M𝟙, −x ≥ −M𝟙` (rows: `A`, then `I`, then `−I`),
  a bounded polyhedron that is nonempty iff the original system is, and in
  that case is full-dimensional with an explicit volume lower bound.
- `khachiyanVolLB n U = (ε/(nU))^n` — the volume lower bound (a cube of
  side `ε/(nU)` around a bounded feasible point fits inside the system).
- `khachiyanRadius n U = (n+1)·M` — the perturbed system lies in the ball
  `E(0, r²I)` of this radius `r`.
- `khachiyanIterations n U = ⌈2(n+1)·log((2r)^n / (v/2))⌉` — the
  iteration budget fed to the ellipsoid method of the platform's
  `LinearOptimization` development (Bertsimas–Tsitsiklis Chapter 8), with
  `V = (2r)^n` the enclosing-cube volume bound and `v/2` a strict lower
  bound for the nonempty case. It is polynomially bounded in `n` and
  `log U`.
-/

open Matrix LinearOptimization

namespace SmaleNinth

/-- The Khachiyan perturbation `ε = 1 / (2 (n+1) (n+1)! U^(n+1))` for a
system in `n` variables with integer entries bounded by `U`. -/
noncomputable def khachiyanEps (n U : ℕ) : ℝ :=
  1 / (2 * ((n : ℝ) + 1) * ((n + 1).factorial : ℝ) * (U : ℝ) ^ (n + 1))

/-- The Khachiyan box radius `M = n!·U^n + 1`: a nonempty system with data
bounded by `U` has a solution of sup-norm at most `M − 1`. -/
noncomputable def khachiyanBox (n U : ℕ) : ℝ :=
  (n.factorial : ℝ) * (U : ℝ) ^ n + 1

/-- The constraint matrix of the perturbed-and-boxed system: the rows of
`A` (cast to `ℝ`), then `I` (the constraints `x_j ≥ −M`), then `−I` (the
constraints `−x_j ≥ −M`). -/
noncomputable def khachiyanSystemA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m + n + n)) (Fin n) ℝ :=
  fun i j =>
    if h : (i : ℕ) < m then (A ⟨(i : ℕ), h⟩ j : ℝ)
    else if (i : ℕ) < m + n then (if (j : ℕ) = (i : ℕ) - m then 1 else 0)
    else (if (j : ℕ) = (i : ℕ) - m - n then -1 else 0)

/-- The right-hand side of the perturbed-and-boxed system: `b_i − ε` on the
original rows, `−M` on all `2n` box rows. -/
noncomputable def khachiyanSystemb {m : ℕ} (n U : ℕ) (b : Fin m → ℤ) :
    Fin (m + n + n) → ℝ :=
  fun i =>
    if h : (i : ℕ) < m then (b ⟨(i : ℕ), h⟩ : ℝ) - khachiyanEps n U
    else -(khachiyanBox n U)

/-- The volume lower bound `v = (ε/(nU))^n` for the nonempty case. -/
noncomputable def khachiyanVolLB (n U : ℕ) : ℝ :=
  (khachiyanEps n U / ((n : ℝ) * (U : ℝ))) ^ n

/-- The enclosing-ball radius `r = (n+1)·M` for the perturbed-and-boxed
system. -/
noncomputable def khachiyanRadius (n U : ℕ) : ℝ :=
  ((n : ℝ) + 1) * khachiyanBox n U

/-- The ellipsoid-method iteration budget
`t* = ⌈2(n+1)·log(V/v')⌉` with `V = (2r)^n` (the enclosing cube's volume)
and `v' = v/2` (a strict volume lower bound in the nonempty case). -/
noncomputable def khachiyanIterations (n U : ℕ) : ℕ :=
  ⌈2 * ((n : ℝ) + 1) *
    Real.log ((2 * khachiyanRadius n U) ^ n / (khachiyanVolLB n U / 2))⌉₊

end SmaleNinth


