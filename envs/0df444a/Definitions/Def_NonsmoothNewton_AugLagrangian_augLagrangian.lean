-- Prove2me | Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian
-- name    : NonsmoothNewton_AugLagrangian_augLagrangian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:49:15.310381+00:00
-- url     : https://prove2.me/theorems/633a38d3-9391-4042-aa9c-8fe51dd6223e
-- title:
--   Augmented Lagrangian $L_r(x,y)$ of the nonlinear program (4.1), and the term $\eta(x,s)=\phi(r,f_i(x),s)$
-- statement:
--   Consider the nonlinear program
--   $$
--   \text{(NLP)}\quad \min f_0(x) \ \text{ s.t. } f_i(x) = 0,\ i = 1,\dots,p, \quad f_i(x) \le 0,\ i = p+1,\dots,m, \tag{4.1}
--   $$
--   with $x \in \mathbb{R}^n$. For $r > 0$ define, for real numbers $a$ (a constraint value) and $y$ (a multiplier),
--   $$
--   \phi(r, a, y) = \begin{cases} y a + \tfrac12 r a^2, & y + r a \ge 0,\\[2pt] -\tfrac{1}{2r} y^2, & y + r a \le 0. \end{cases}
--   $$
--   The two cases agree on $y + r a = 0$, where both equal $-y^2/(2r)$. The **augmented Lagrangian** of NLP is the function of $(x, y) \in \mathbb{R}^n \times \mathbb{R}^m$
--   $$
--   L_r(x, y) = f_0(x) + \sum_{i=1}^{p} \Big( y_i f_i(x) + \tfrac12 r f_i(x)^2 \Big) + \sum_{i=p+1}^{m} \phi\big(r, f_i(x), y_i\big).
--   $$
--   For a single constraint function $g$ (playing the role of an inequality constraint $f_i$) the file also defines
--   $$
--   \eta(x, s) = \phi\big(r, g(x), s\big), \qquad (x, s) \in \mathbb{R}^n \times \mathbb{R},
--   $$
--   the one-constraint term on which the proof of Theorem 4.1 works.
--
--   The augmented Lagrangian is the merit function minimized in each step of the method of multipliers; the paper shows that its gradient is semismooth, so the nonsmooth Newton method applies to it.
--
--   **Formalization Note** $\mathbb{R}^n$, $\mathbb{R}^m$ are `EuclideanSpace ℝ (Fin n)`, `EuclideanSpace ℝ (Fin m)`, and $L_r$ is a function on their product. The paper's constraint index $i \in \{1,\dots,m\}$ is `i : Fin m` with paper index `i.val + 1`: equality constraints are those with `i.val < p`, inequality constraints those with `p ≤ i.val`. The paper's first sum prints $h(r_i, f_i(x), y_i)$ with a typo $r_i$; the single $r$ is used, as in the paper's definition of $h$. The case split of $\phi$ uses `0 ≤ y + r * a` for the first branch, which is faithful because the branches agree on the boundary. The definitions do not require $r > 0$ or $p \le m$; every theorem that uses them assumes $r > 0$ (for $r = 0$ Lean's $1/(2\cdot 0) = 0$ would make $\phi$ meaningless), and $p > m$ simply means there are no inequality constraints.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 363, Section 4, Eq. (4.1), definitions of L_r, h, φ, and η (proof of Theorem 4.1)

import Mathlib

namespace NonsmoothNewton.AugLagrangian

/-- The inequality-constraint term of Rockafellar's augmented Lagrangian, Qi–Sun (1993),
p. 363: `φ(r, a, y) = y a + ½ r a²` if `y + r a ≥ 0`, and `-(1/2r) y²` if `y + r a ≤ 0`.
The two branches agree on `y + r a = 0` (both equal `-y²/(2r)`), so the `if` is faithful. -/
noncomputable def phi (r a y : ℝ) : ℝ :=
  if 0 ≤ y + r * a then y * a + r / 2 * a ^ 2 else -(1 / (2 * r)) * y ^ 2

/-- The augmented Lagrangian of the nonlinear program (4.1), Qi–Sun (1993), p. 363:
`L_r(x, y) = f₀(x) + Σ_{i ≤ p} (y_i f_i(x) + ½ r f_i(x)²) + Σ_{i > p} φ(r, f_i(x), y_i)`.
The paper's constraint `i ∈ {1, …, m}` is `i : Fin m` (paper index `i.val + 1`); it is an
equality constraint iff `i.val < p` and an inequality constraint iff `p ≤ i.val`. -/
noncomputable def augLagrangian {n m : ℕ} (p : ℕ) (r : ℝ) (f0 : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) : ℝ :=
  f0 z.1
    + ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < p),
        (z.2 i * f i z.1 + r / 2 * f i z.1 ^ 2)
    + ∑ i ∈ Finset.univ.filter (fun i : Fin m => p ≤ i.val), phi r (f i z.1) (z.2 i)

/-- The single inequality term of the proof of Theorem 4.1, Qi–Sun (1993), p. 363:
`η(x, s) = φ(r, g(x), s)` for one constraint function `g = f_i`. -/
noncomputable def eta {n : ℕ} (r : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  phi r (g z.1) z.2

end NonsmoothNewton.AugLagrangian


