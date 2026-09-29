-- Prove2me | Definitions.Def_MoreauProx_Characterization_GammaZero
-- name    : MoreauProx_Characterization_GammaZero
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:15:46.293192+00:00
-- url     : https://prove2.me/theorems/96c21383-8dc6-483d-84de-70fd298d6fcf
-- title:
--   Γ₀(H), the dual function, and subgradients on a real Hilbert space
-- statement:
--   Let $H$ be a real Hilbert space with inner product $(x \mid y)$, and consider functions $f : H \to \,]-\infty, +\infty]$.
--
--   1. **Convexity.** A function $\varphi : H \to [-\infty, +\infty]$ is called convex when its epigraph $\{(x, t) \in H \times \mathbb{R} : \varphi(x) \le t\}$ is a convex subset of $H \times \mathbb{R}$.
--   2. **The class $\Gamma_0(H)$.** A function $f$ belongs to $\Gamma_0(H)$ when it never takes the value $-\infty$, is not identically $+\infty$, is convex and is lower semicontinuous (for the norm topology).
--   3. **The dual function.** The dual (conjugate) of $f$ is
--   $$
--   g(y) = \sup_{x \in H} \big[(x \mid y) - f(x)\big], \qquad y \in H,
--   $$
--   with values in $[-\infty, +\infty]$.
--   4. **Subgradients.** A vector $y$ is a subgradient of $\varphi$ at $z$ when $\varphi(z)$ is finite and the continuous affine function $u \mapsto (u - z \mid y) + \varphi(z)$ is a minorant of $\varphi$, i.e.
--   $$
--   \varphi(z) + (u - z \mid y) \le \varphi(u) \quad \text{for all } u \in H.
--   $$
--   The set of subgradients of $\varphi$ at $z$ is written $\partial\varphi(z)$.
--
--   These are the basic objects of Moreau's paper: $\Gamma_0(H)$ is the class of functions on which the duality $f \leftrightarrow g$ is an involution, and $\partial f(z)$ is the set of points conjugate to $z$.
--
--   **Formalization Note** Values in $]-\infty,+\infty]$ are encoded in `EReal`. The paper defines $\Gamma_0(H)$ as the upper envelopes of nonempty families of continuous affine functions other than the constant $+\infty$, and states on the same page that this is the class of convex, lower semicontinuous functions with values in $]-\infty, +\infty]$ other than $+\infty$; we state the latter. The paper defines $y \in \partial f(x)$ by the equality $f(x) + g(y) = (x \mid y)$ and glosses it as the affine-minorant condition used here; the two agree whenever $\varphi(z)$ is finite, in particular on $\Gamma_0(H)$, and the minorant form is also meaningful for functions outside $\Gamma_0(H)$ (needed for Corollary 10.c).
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), pp. 275–277, §2.a, (2.2), §2.c

import Mathlib
open scoped InnerProductSpace

namespace MoreauProx.Characterization

/-- Convexity of a function `φ : H → ]−∞, +∞]` (encoded in `EReal`): its epigraph
`{(x, t) ∈ H × ℝ | φ x ≤ t}` is a convex subset of `H × ℝ`. For functions that never take the
value `⊥` this is the usual convexity inequality with the conventions of `]−∞, +∞]`. -/
def EConvex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : H → EReal) : Prop :=
  Convex ℝ {p : H × ℝ | φ p.1 ≤ ((p.2 : ℝ) : EReal)}

/-- Moreau §2.a: `Γ₀(H)`, the functions `H → ]−∞, +∞]` that are convex and lower semicontinuous
and not identically `+∞` (the paper's stated equivalent of "upper envelope of a nonempty family
of continuous affine functions, other than the constants ±∞"). -/
def GammaZero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (∃ x, f x ≠ ⊤) ∧ EConvex f ∧ LowerSemicontinuous f

/-- Moreau (2.2): the dual (conjugate) function `g(y) = sup_{x ∈ H} [(x | y) − f(x)]`,
computed in `EReal` (where `a − ⊤ = ⊥`, so points with `f x = +∞` contribute nothing). -/
noncomputable def conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (y : H) : EReal :=
  ⨆ x : H, ((⟪x, y⟫_ℝ : ℝ) : EReal) - f x

/-- Moreau §2.c: `y` is a subgradient of `φ` at `z` when `φ z` is finite and the continuous
affine function `u ↦ (u − z | y) + φ(z)` minorizes `φ` (an affine minorant exact at `z`).
`subgrad φ z` is the set `∂φ(z)`. -/
def subgrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : H → EReal) (z : H) : Set H :=
  {y | φ z ≠ ⊥ ∧ φ z ≠ ⊤ ∧ ∀ u : H, φ z + ((⟪u - z, y⟫_ℝ : ℝ) : EReal) ≤ φ u}

end MoreauProx.Characterization


