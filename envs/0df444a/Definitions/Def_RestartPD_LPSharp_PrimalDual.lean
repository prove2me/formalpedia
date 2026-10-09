-- Prove2me | Definitions.Def_RestartPD_LPSharp_PrimalDual
-- name    : RestartPD_LPSharp_PrimalDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:43.081004+00:00
-- url     : https://prove2.me/theorems/5518e2c9-bd58-497d-8bc6-e17458e495d4
-- title:
--   (1), (4a)–(4b), (5), Notation, Definition 1, pp. 2–11 — Z⋆, W_r(z), the normalized duality gap ρ_r, dist, diam and α-sharpness, Euclidean norm
-- statement:
--   Objects of the convex–concave saddle-point problem
--   $$\min_{x\in X}\max_{y\in Y} L(x,y), \qquad (1)$$
--   with $x\in\mathbb R^n$, $y\in\mathbb R^m$, $X\subseteq\mathbb R^n$, $Y\subseteq\mathbb R^m$. A primal-dual point is $z=(x,y)$, and $Z=X\times Y$. Throughout, $\|\cdot\|$ on $\mathbb R^{n+m}$ is the **Euclidean norm** $\|(x,y)\|=\sqrt{\|x\|_2^2+\|y\|_2^2}$.
--
--   1. **Solution set.** $Z^\star$ is the set of saddle points: $z=(x,y)\in Z$ with $L(x,y')\le L(x,y)\le L(x',y)$ for all $x'\in X$, $y'\in Y$.
--   2. **Ball.** For $r\ge 0$, $W_r(z)=\{\hat z\in Z : \|z-\hat z\|\le r\}$.
--   3. **Normalized duality gap** (4a)–(4b). For $r\in(0,\infty)$,
--   $$\rho_r(z)=\sup_{\hat z\in W_r(z)}\frac{L(x,\hat y)-L(\hat x,y)}{r},$$
--   and $\rho_0(z)=\limsup_{r\to0^+}\rho_r(z)$. The value lies in the extended reals.
--   4. **Distance and diameter.** $\operatorname{dist}(z,Z^\star)=\inf_{\hat z\in Z^\star}\|z-\hat z\|$ and $\operatorname{diam}(S)=\sup_{s,s'\in S}\|s-s'\|$ (extended-real valued, $+\infty$ for unbounded $S$).
--   5. **Sharpness** (Definition 1). Problem (1) is $\alpha$-sharp on $S\subseteq Z$ if for every $r\in(0,\operatorname{diam}(S)]$ and every $z\in S$
--   $$\alpha\,\operatorname{dist}(z,Z^\star)\le\rho_r(z). \qquad (13)$$
--
--   Sharpness of the normalized duality gap is the property under which restarted primal-dual methods converge linearly; this file fixes the objects in which the LP sharpness results of the paper are stated.
--
--   **Formalization Note** $\rho_r$ and $\operatorname{diam}$ are `EReal`-valued suprema so that an unbounded supremum is $+\infty$ rather than a junk real value. $\operatorname{dist}(z,Z^\star)$ is a real infimum; every theorem that uses it assumes $Z^\star\neq\emptyset$. The norm is the $L^2$ norm of `WithLp 2 (ℝⁿ × ℝᵐ)`, never the sup norm of the bare product type. The page's standing assumptions on (1) (differentiable, convex–concave $L$, closed convex $X,Y$) are not built into these definitions; the LP instance of this mission satisfies them.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, pp. 2–4, 11, (1), (4a)–(4b), (5), Notation (diam), Definition 1 (13)

import Mathlib

namespace RestartPD.LPSharp

open Filter Topology

/-- The primal-dual space `E = ℝⁿ × ℝᵐ`; a point is `z = (x, y)` with `z.1 = x`, `z.2 = y`. -/
abbrev PDSpace (n m : ℕ) := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)

/-- The Euclidean norm on `ℝ^{n+m}`: `eucl (x, y) = √(‖x‖² + ‖y‖²)`. (The norm instance of the bare
product `PDSpace n m` is the sup norm and is not used anywhere in this development.) -/
noncomputable def eucl (n m : ℕ) : Seminorm ℝ (PDSpace n m) :=
  (normSeminorm ℝ (WithLp 2 (PDSpace n m))).comp
    (WithLp.linearEquiv 2 ℝ (PDSpace n m)).symm.toLinearMap

variable {n m : ℕ}

/-- `Z⋆`: the solutions (saddle points) of `min_{x ∈ X} max_{y ∈ Y} L(x, y)` (problem (1)), i.e. the
points `z = (x, y) ∈ X × Y` with `L(x, y') ≤ L(x, y) ≤ L(x', y)` for all `x' ∈ X`, `y' ∈ Y`. -/
def Zstar (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (Y : Set (EuclideanSpace ℝ (Fin m))) :
    Set (PDSpace n m) :=
  {z | z ∈ X ×ˢ Y ∧ ∀ x' ∈ X, ∀ y' ∈ Y, L z.1 y' ≤ L z.1 z.2 ∧ L z.1 z.2 ≤ L x' z.2}

/-- The bracket of (4a): `L(x, ŷ) − L(x̂, y)` for `z = (x, y)`, `ẑ = (x̂, ŷ)`. -/
def gapAt (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (z zh : PDSpace n m) : ℝ :=
  L z.1 zh.2 - L zh.1 z.2

/-- `W_r(z) := {ẑ ∈ Z | ‖z − ẑ‖ ≤ r}` with `Z = X × Y` and the Euclidean norm. -/
def Wball (X : Set (EuclideanSpace ℝ (Fin n))) (Y : Set (EuclideanSpace ℝ (Fin m)))
    (r : ℝ) (z : PDSpace n m) : Set (PDSpace n m) :=
  {zh | zh ∈ X ×ˢ Y ∧ eucl n m (z - zh) ≤ r}

/-- (4a), for `r ∈ (0, ∞)`: `ρ_r(z) := sup_{ẑ ∈ W_r(z)} (L(x, ŷ) − L(x̂, y)) / r`, valued in `EReal`. -/
noncomputable def rhoPos (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (Y : Set (EuclideanSpace ℝ (Fin m)))
    (r : ℝ) (z : PDSpace n m) : EReal :=
  ⨆ zh ∈ Wball X Y r z, ((gapAt L z zh / r : ℝ) : EReal)

/-- The normalized duality gap `ρ_r(z)`: (4a) for `r ≠ 0`, and (4b) `ρ_0(z) := limsup_{r → 0+} ρ_r(z)`. -/
noncomputable def rho (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (Y : Set (EuclideanSpace ℝ (Fin m)))
    (r : ℝ) (z : PDSpace n m) : EReal :=
  if r = 0 then Filter.limsup (fun s => rhoPos L X Y s z) (𝓝[>] (0 : ℝ)) else rhoPos L X Y r z

/-- `dist(z, Z⋆) := inf_{ẑ ∈ Z⋆} ‖z − ẑ‖` (display (5)), Euclidean norm. -/
noncomputable def distZ (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (Y : Set (EuclideanSpace ℝ (Fin m)))
    (z : PDSpace n m) : ℝ :=
  ⨅ s : Zstar L X Y, eucl n m (z - (s : PDSpace n m))

/-- `diam(S) := sup_{s, s' ∈ S} ‖s − s'‖` (Notation, p. 4), valued in `EReal` (`⊤` if `S` is unbounded). -/
noncomputable def diamS (S : Set (PDSpace n m)) : EReal :=
  ⨆ s ∈ S, ⨆ s' ∈ S, ((eucl n m (s - s') : ℝ) : EReal)

/-- Definition 1: problem (1) is `α`-sharp on `S ⊆ Z` if for all `r ∈ (0, diam(S)]` and all `z ∈ S`,
`α dist(z, Z⋆) ≤ ρ_r(z)` (13). -/
def IsSharpOn (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (Y : Set (EuclideanSpace ℝ (Fin m)))
    (α : ℝ) (S : Set (PDSpace n m)) : Prop :=
  S ⊆ X ×ˢ Y ∧ ∀ r : ℝ, 0 < r → (r : EReal) ≤ diamS S →
    ∀ z ∈ S, ((α * distZ L X Y z : ℝ) : EReal) ≤ rho L X Y r z

end RestartPD.LPSharp


