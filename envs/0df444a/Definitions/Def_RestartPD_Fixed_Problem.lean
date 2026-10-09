-- Prove2me | Definitions.Def_RestartPD_Fixed_Problem
-- name    : RestartPD_Fixed_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:53:57.252987+00:00
-- url     : https://prove2.me/theorems/192fc09c-f8b6-4a72-b619-1c418aa49cdf
-- title:
--   §1, §3, pp. 2–4, 11 — problem (1), Z⋆, the primal-dual gap (3), the normalized duality gap (4a)–(4b), dist and diam, Definition 1
-- statement:
--   Let $X \subseteq \mathbb R^n$ and $Y \subseteq \mathbb R^m$ and let $L : \mathbb R^n \times \mathbb R^m \to \mathbb R$. Problem (1) is the saddle-point problem
--   $$\min_{x \in X} \max_{y \in Y} L(x, y)$$
--   on the feasible region $Z = X \times Y$; a primal-dual point is written $z = (x, y)$. The **standing assumptions** (p. 2) are that $X$ and $Y$ are closed and convex, that $L$ is differentiable, convex in $x$ on $X$ for each $y \in Y$ and concave in $y$ on $Y$ for each $x \in X$, and that (1) has a solution. The solution set $Z^\star$ is the set of saddle points: $z^\star = (x^\star, y^\star) \in Z$ with $L(x^\star, y') \le L(x^\star, y^\star) \le L(x', y^\star)$ for all $x' \in X$, $y' \in Y$.
--
--   The file fixes, for a semi-norm $\|\cdot\|$ on $\mathbb R^n \times \mathbb R^m$:
--   1. the **primal-dual gap** (3) at $z$, $\sup_{\hat z \in Z} \{L(x, \hat y) - L(\hat x, y)\}$, an extended real number;
--   2. the feasible ball $W_r(z) = \{\hat z \in Z : \|z - \hat z\| \le r\}$;
--   3. the **normalized duality gap** (4a)–(4b),
--   $$\rho_r(z) = \sup_{\hat z \in W_r(z)} \frac{L(x, \hat y) - L(\hat x, y)}{r} \quad (r > 0), \qquad \rho_0(z) = \limsup_{r \to 0^+} \rho_r(z),$$
--   with values in $[-\infty, +\infty]$;
--   4. $\operatorname{dist}(z, Z^\star) = \inf_{z^\star \in Z^\star} \|z - z^\star\|$ and $\operatorname{diam}(S) = \sup_{s, s' \in S} \|s - s'\| \in [0, +\infty]$;
--   5. **Definition 1**: problem (1) is **$\alpha$-sharp on $S \subseteq Z$** if $\alpha \operatorname{dist}(z, Z^\star) \le \rho_r(z)$ for every $z \in S$ and every $r \in (0, \operatorname{diam}(S)]$.
--
--   These are the objects in which Theorem 1 and its lemmas are stated: $\rho_r$ is the progress measure of the restart scheme, and sharpness turns a bound on $\rho_r$ into a bound on the distance to $Z^\star$.
--
--   **Formalization Note** $\mathbb R^n$, $\mathbb R^m$ are `EuclideanSpace ℝ (Fin n)`, `EuclideanSpace ℝ (Fin m)`; the semi-norm is an arbitrary `Seminorm ℝ` on their product, never the product's own norm. The gaps, $\rho_r$ and $\operatorname{diam}$ are suprema in `EReal`, so an unbounded set gives $+\infty$ rather than Lean's junk value $0$. "(1) has a solution" ($Z^\star \neq \emptyset$) replaces the page's "the feasible region is non-empty and (1) has a bounded optimal value": every result measures $\operatorname{dist}(\cdot, Z^\star)$, which the page treats as finite, and the proof of Proposition 4 picks a point of $Z^\star$. Differentiability is required on the whole space, as the page gives no domain. The page defines $\operatorname{diam}$ only for bounded sets; here it is $+\infty$ on unbounded sets, so the sharpness range $(0, \operatorname{diam}(S)]$ is then $(0, \infty)$.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, pp. 2–4, 11, (1), (3), (4a)–(4b), (5), Notation (diam), Definition 1 (13)

import Mathlib

namespace RestartPD.Fixed

/-- Primal space `ℝⁿ`. -/
abbrev Primal (n : ℕ) := EuclideanSpace ℝ (Fin n)
/-- Dual space `ℝᵐ`. -/
abbrev Dual (m : ℕ) := EuclideanSpace ℝ (Fin m)
/-- Primal-dual space: `z = (x, y)`, with `z.1 = x` and `z.2 = y`. -/
abbrev E (n m : ℕ) := Primal n × Dual m

variable {n m : ℕ}

/-- `Z⋆`, the solutions of problem (1): the saddle points of `L` on `Z = X × Y`. -/
def Zstar (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m)) :
    Set (E n m) :=
  {z | z ∈ X ×ˢ Y ∧ ∀ x' ∈ X, ∀ y' ∈ Y, L z.1 y' ≤ L z.1 z.2 ∧ L z.1 z.2 ≤ L x' z.2}

/-- The standing assumptions on problem (1), p. 2: `X`, `Y` closed and convex, `L` convex in `x`,
concave in `y`, differentiable; and a nonempty solution set `Z⋆`. -/
structure IsPDProblem (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m)) :
    Prop where
  closed_X : IsClosed X
  convex_X : Convex ℝ X
  closed_Y : IsClosed Y
  convex_Y : Convex ℝ Y
  convex_L : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y)
  concave_L : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y)
  differentiable_L : Differentiable ℝ (fun z : E n m => L z.1 z.2)
  solution_nonempty : (Zstar L X Y).Nonempty

/-- The bracket of (3) and (4a): `L(x, ŷ) − L(x̂, y)` for `z = (x, y)`, `ẑ = (x̂, ŷ)`. -/
def gapAt (L : Primal n → Dual m → ℝ) (z zh : E n m) : ℝ :=
  L z.1 zh.2 - L zh.1 z.2

/-- The primal-dual gap (3), `max_{ẑ ∈ Z} {L(x, ŷ) − L(x̂, y)}`, as an extended-real supremum. -/
noncomputable def pdGap (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (z : E n m) : EReal :=
  ⨆ zh ∈ X ×ˢ Y, ((gapAt L z zh : ℝ) : EReal)

/-- `W_r(z) = {ẑ ∈ Z | ‖z − ẑ‖ ≤ r}` in the semi-norm `p`. -/
def Wball (X : Set (Primal n)) (Y : Set (Dual m)) (p : Seminorm ℝ (E n m)) (r : ℝ) (z : E n m) :
    Set (E n m) :=
  {zh | zh ∈ X ×ˢ Y ∧ p (z - zh) ≤ r}

/-- The normalized duality gap (4a) for a radius `r > 0`, as an extended-real supremum. -/
noncomputable def rhoPos (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (r : ℝ) (z : E n m) : EReal :=
  ⨆ zh ∈ Wball X Y p r z, ((gapAt L z zh / r : ℝ) : EReal)

/-- The normalized duality gap `ρ_r(z)`: (4a) for `r ≠ 0`, and (4b)
`ρ_0(z) = limsup_{r → 0+} ρ_r(z)` for `r = 0`. -/
noncomputable def rho (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (r : ℝ) (z : E n m) : EReal :=
  if r = 0 then Filter.limsup (fun s : ℝ => rhoPos L X Y p s z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
  else rhoPos L X Y p r z

/-- `dist(z, Z⋆) = inf_{s ∈ Z⋆} ‖z − s‖` in the semi-norm `p`. -/
noncomputable def distZ (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (z : E n m) : ℝ :=
  ⨅ s : Zstar L X Y, p (z - (s : E n m))

/-- `diam(S) = sup_{s, s' ∈ S} ‖s − s'‖` in the semi-norm `p`, extended-real (`⊤` if
unbounded, `0` if empty). -/
noncomputable def diamS (p : Seminorm ℝ (E n m)) (S : Set (E n m)) : EReal :=
  max 0 (⨆ s ∈ S, ⨆ s' ∈ S, ((p (s - s') : ℝ) : EReal))

/-- Definition 1: problem (1) is `α`-sharp on `S ⊆ Z` if `α dist(z, Z⋆) ≤ ρ_r(z)` for all `z ∈ S`
and all `r ∈ (0, diam(S)]`. -/
def IsSharpOn (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (α : ℝ) (S : Set (E n m)) : Prop :=
  S ⊆ X ×ˢ Y ∧
    ∀ r : ℝ, 0 < r → (r : EReal) ≤ diamS p S →
      ∀ z ∈ S, ((α * distZ L X Y p z : ℝ) : EReal) ≤ rho L X Y p r z

end RestartPD.Fixed


