-- Prove2me | Definitions.Def_BellmanDP_Allocation_GeneralEquation
-- name    : BellmanDP_Allocation_GeneralEquation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T04:44:30.02563+00:00
-- url     : https://prove2.me/theorems/c34dd111-d120-4bbd-9171-fa589fef8bba
-- title:
--   The general allocation equation $f(x)=\max_{0\le y\le x}[u(x,y)+f(ay+b(x-y))]$
-- statement:
--   For a one-stage return $u(x,y)$ depending on both the total quantity $x$ and the allocation $y$, Bellman's § 18 considers the equation
--   $$f(x) = \max_{0 \le y \le x} \big[ u(x,y) + f\big(ay + b(x-y)\big) \big], \qquad x \ge 0.$$
--   A function $f$ is a solution when for every $x \ge 0$ the maximum is attained and equals $f(x)$.
--
--   The file also defines, for a function $\varphi(x,y)$ and $z \ge 0$, the maximum over the triangle $0 \le y \le x \le z$:
--   $$\max_{0 \le x \le z} \, \max_{0 \le y \le x} \varphi(x,y),$$
--   used in Theorem 9 for the majorant $m(z)$ and the discrepancy $D(z)$.
--
--   **Formalization Note** The triangle maximum is a real supremum (`sSup`) of the image of the triangle; for continuous $\varphi$ the triangle is compact and nonempty, so it is the book's maximum.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 18, Eq. (18.1) and Theorem 9 (2), p. 29

import Mathlib

namespace BellmanDP.Allocation

/-- Ch. I, § 18, Eq. (18.1), p. 29: `f` solves `f(x) = Max_{0 ≤ y ≤ x} [u(x, y) + f(ay + b(x − y))]`
for every `x ≥ 0`, the maximum being attained. -/
def IsGeneralSolution (u : ℝ → ℝ → ℝ) (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → IsGreatest ((fun y => u x y + f (a * y + b * (x - y))) '' Set.Icc 0 x) (f x)

/-- Ch. I, Theorem 9, p. 29: the maximum of `φ(x, y)` over the triangle
`0 ≤ y ≤ x ≤ z`, i.e. `Max_{0 ≤ x ≤ z} Max_{0 ≤ y ≤ x} φ(x, y)`. For `φ` continuous and `z ≥ 0` the
triangle is compact and nonempty, so the supremum is attained. -/
noncomputable def triangleMax (φ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => φ p.1 p.2) '' {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ z})

end BellmanDP.Allocation


