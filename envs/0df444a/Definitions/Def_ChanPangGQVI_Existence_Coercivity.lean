-- Prove2me | Definitions.Def_ChanPangGQVI_Existence_Coercivity
-- name    : ChanPangGQVI_Existence_Coercivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:36:52.846223+00:00
-- url     : https://prove2.me/theorems/a5a94ef1-2baa-4196-9260-f8b79950ac81
-- title:
--   Coercivity function bound $C_{\mu,K}(r,x^0)\ge c$, coercivity (4), and strong copositivity
-- statement:
--   Let $\mu$ and $K$ be point-to-set mappings of $\mathbb R^n$ and let $\|\cdot\|$ be the Euclidean norm. Write $B_r$ for the closed ball of radius $r$ about the origin and $C_r$ for its boundary sphere. The paper's **coercivity function** is
--
--   $$
--   C_{\mu,K}(r,x^0)=\inf_{x\in K(x)\cap C_r}\Big[\inf_{y\in\mu(x)}(x-x^0)^T y\Big]\Big/\big(r+\|x^0\|\big),
--   $$
--
--   with the convention that an infimum over an empty set is $+\infty$. This file does not define $C_{\mu,K}$ as a function; it defines the statement $C_{\mu,K}(r,x^0)\ge c$, which for $r>0$ is equivalent to
--
--   $$
--   c\,(r+\|x^0\|)\ \le\ (x-x^0)^T y\qquad\text{for all } x \text{ with } \|x\|=r,\ x\in K(x), \text{ and all } y\in\mu(x).
--   $$
--
--   The mapping $\mu$ is **coercive with respect to $K$ at $x^0$** (condition (4) of the paper) if
--
--   $$
--   \lim_{\|x\|\to\infty,\ x\in K(x)}\ \inf_{y\in\mu(x)} \frac{(x-x^0)^T y}{\|x\|}=\infty,
--   $$
--
--   that is, for every $M$ there is $R$ such that $M\|x\|\le (x-x^0)^T y$ whenever $x\in K(x)$, $\|x\|\ge R$ and $y\in\mu(x)$.
--
--   The mapping $\mu$ is **strongly copositive with respect to $K$ at $x^0$** if $x^0\in K(x^0)$ and there are a scalar $\alpha>0$ and a vector $y^0\in\mu(x^0)$ such that for all $x$ with $x\in K(x)$,
--
--   $$
--   (y-y^0)^T(x-x^0)\ \ge\ \alpha\|x-x^0\|^2\qquad\text{for all } y\in\mu(x).
--   $$
--
--   **Formalization Note** The names are `CoercivityGE μ K r x0 c`, `IsCoerciveAt μ K x0` and `IsStronglyCopositiveAt μ K x0`. Stating the bound on $C_{\mu,K}$ in this universally quantified form keeps the paper's convention $\inf\emptyset=+\infty$ (a real-valued infimum would return $0$ on an empty set). `CoercivityGE` is only used with $r>0$, where $r+\|x^0\|>0$.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 217 (coercivity function C_{μ,K}, Corollary 4.1 condition (4)); p. 218 (coercive and strongly copositive with respect to K)

import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 217, §4: the statement `C_{μ,K}(r, x⁰) ≥ c` about the coercivity
function
`C_{μ,K}(r, x⁰) = inf_{x ∈ K(x) ∩ C_r} [inf_{y ∈ μ(x)} (x - x⁰)ᵀ y] / (r + ‖x⁰‖)`,
where `C_r` is the sphere of radius `r` about the origin and the infimum over an empty set is `+∞`.
Since the infimum is `≥ c` exactly when every element is, and `r + ‖x⁰‖ > 0` whenever `r > 0`,
this is: for every `x` with `‖x‖ = r` and `x ∈ K(x)` and every `y ∈ μ(x)`,
`c (r + ‖x⁰‖) ≤ (x - x⁰)ᵀ y`. It is only used with `r > 0`. -/
def CoercivityGE {n : ℕ}
    (μ K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (c : ℝ) : Prop :=
  ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r, x ∈ K x →
    ∀ y ∈ μ x, c * (r + ‖x0‖) ≤ ⟪x - x0, y⟫

/-- Chan and Pang 1982, pp. 217–218, condition (4) and the definition following Corollary 4.1:
`μ` is coercive with respect to `K` at `x⁰` if
`lim_{‖x‖ → ∞, x ∈ K(x)} inf_{y ∈ μ(x)} (x - x⁰)ᵀ y / ‖x‖ = ∞`,
i.e. for every `M` there is `R` such that `M ‖x‖ ≤ (x - x⁰)ᵀ y` whenever `x ∈ K(x)`,
`‖x‖ ≥ R` and `y ∈ μ(x)` (infimum over an empty set `= +∞`). -/
def IsCoerciveAt {n : ℕ}
    (μ K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x0 : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ x, x ∈ K x → R ≤ ‖x‖ → ∀ y ∈ μ x, M * ‖x‖ ≤ ⟪x - x0, y⟫

/-- Chan and Pang 1982, p. 218: `μ` is strongly copositive with respect to `K` at `x⁰` if
`x⁰ ∈ K(x⁰)` and there are `α > 0` and `y⁰ ∈ μ(x⁰)` such that for all `x` with `x ∈ K(x)`,
`(y - y⁰)ᵀ (x - x⁰) ≥ α ‖x - x⁰‖²` for all `y ∈ μ(x)`. -/
def IsStronglyCopositiveAt {n : ℕ}
    (μ K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x0 : EuclideanSpace ℝ (Fin n)) : Prop :=
  x0 ∈ K x0 ∧ ∃ α : ℝ, 0 < α ∧ ∃ y0 ∈ μ x0,
    ∀ x, x ∈ K x → ∀ y ∈ μ x, α * ‖x - x0‖ ^ 2 ≤ ⟪y - y0, x - x0⟫

end ChanPangGQVI.Existence


