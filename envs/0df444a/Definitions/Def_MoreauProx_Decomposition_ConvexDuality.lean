-- Prove2me | Definitions.Def_MoreauProx_Decomposition_ConvexDuality
-- name    : MoreauProx_Decomposition_ConvexDuality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:09:33.39434+00:00
-- url     : https://prove2.me/theorems/60dfc551-9d12-4e19-83a2-4fe6bd2eb7ac
-- title:
--   Γ₀(H), the dual function, the subdifferential and the proximal point in a real Hilbert space
-- statement:
--   Let $H$ be a real Hilbert space with inner product $(x \mid y)$. Functions take values in the extended real line $\overline{\mathbb R} = [-\infty, +\infty]$.
--
--   1. **The class $\Gamma_0(H)$** (Moreau, §2.a). A function $f : H \to \overline{\mathbb R}$ belongs to $\Gamma_0(H)$ when
--      - $f$ never takes the value $-\infty$, so $f$ has values in $]-\infty, +\infty]$;
--      - $f$ is not identically $+\infty$;
--      - $f$ is convex, in the sense that its epigraph $\{(x, r) \in H \times \mathbb R : f(x) \le r\}$ is a convex subset of $H \times \mathbb R$;
--      - $f$ is lower semicontinuous for the norm topology of $H$.
--
--   2. **The dual function** (Moreau, (2.2)). For any $f : H \to \overline{\mathbb R}$,
--   $$ f^{*}(y) = \sup_{x \in H}\,\big[(x \mid y) - f(x)\big], \qquad y \in H, $$
--   computed in $\overline{\mathbb R}$, where a term with $f(x) = +\infty$ equals $-\infty$ and so does not contribute. Moreau calls $g = f^{*}$ the *fonction duale* of $f$.
--
--   3. **The subdifferential** (Moreau, §2.c). $\partial f(x) = \{ y \in H : f(x) + f^{*}(y) = (x \mid y) \}$, the set of points $y$ *conjugate* to $x$ with respect to $f$ and its dual.
--
--   4. **The proximal objective and proximal points** (Moreau, 3.a–3.b). For $z \in H$ put
--   $$ \Phi_z(u) = \tfrac12 \|u - z\|^2 + f(u). $$
--   A point $x$ is a *proximal point of $z$ relative to $f$* when $\Phi_z(x) \le \Phi_z(u)$ for every $u \in H$.
--
--   These objects are the vocabulary of Moreau's theory: every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** The paper defines $\Gamma_0(H)$ as the suprema of families of continuous affine functions other than the constants $\pm\infty$, and then states (citing [17], §1) that these are exactly the convex, lower semicontinuous functions with values in $]-\infty,+\infty]$ other than the constant $+\infty$; the second description is the one formalized. Mathlib's `ConvexOn` does not apply to `EReal`-valued functions, so convexity is stated for the epigraph. The paper writes $x = \mathrm{prox}_f z$ for "the unique minimizer" (3.b); here `IsProx f z x` is the predicate "x minimizes $\Phi_z$", which for $f \in \Gamma_0(H)$ characterizes $\mathrm{prox}_f z$ because the minimizer exists and is unique (Proposition 3.a). No choice function with a junk value is used.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), pp. 275–278, §2.a (Notation), (2.2), §2.c (Notation), 3.a, 3.b

import Mathlib

namespace MoreauProx.Decomposition

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `Γ₀(H)` (Moreau 1965, §2.a, pp. 275–276): the functions `f : H → ]−∞, +∞]` that are convex,
lower semicontinuous and not identically `+∞`. Values live in `EReal`; `f x ≠ ⊥` excludes `−∞`.
Convexity of an extended-valued function is convexity of its epigraph `{(x, r) | f x ≤ r}` in
`H × ℝ`. -/
structure GammaZero (f : H → EReal) : Prop where
  ne_bot : ∀ x, f x ≠ ⊥
  exists_ne_top : ∃ x, f x ≠ ⊤
  convex_epigraph : Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)}
  lowerSemicontinuous : LowerSemicontinuous f

/-- The dual (conjugate) function of `f` (Moreau 1965, (2.2), p. 276):
`g(y) = sup_{x ∈ H} [(x | y) − f(x)]`, computed in `EReal` (a term with `f x = +∞` is `−∞`). -/
noncomputable def conj (f : H → EReal) (y : H) : EReal :=
  ⨆ x, ((⟪x, y⟫_ℝ : ℝ) : EReal) - f x

/-- The subdifferential `∂f(x)` (Moreau 1965, §2.c, p. 277): the points `y` conjugate to `x`
with respect to `f` and its dual, i.e. with `f(x) + g(y) = (x | y)`. -/
def subdiff (f : H → EReal) (x : H) : Set H :=
  {y | f x + conj f y = ((⟪x, y⟫_ℝ : ℝ) : EReal)}

/-- The proximal objective `Φ(u) = ½‖u − z‖² + f(u)` (Moreau 1965, 3.a, p. 278). -/
noncomputable def proxObjective (f : H → EReal) (z u : H) : EReal :=
  ((‖u - z‖ ^ 2 / 2 : ℝ) : EReal) + f u

/-- `x` is a proximal point of `z` relative to `f`: `x` minimizes `u ↦ ½‖u − z‖² + f(u)` over
`H` (Moreau 1965, 3.b, p. 278). For `f ∈ Γ₀(H)` this minimizer exists and is unique (3.a), and
`IsProx f z x` is exactly `x = prox_f z`. -/
def IsProx (f : H → EReal) (z x : H) : Prop :=
  ∀ u, proxObjective f z x ≤ proxObjective f z u

end MoreauProx.Decomposition


