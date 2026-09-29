-- Prove2me | Definitions.Def_MoreauProx_Characterization_Prox
-- name    : MoreauProx_Characterization_Prox
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:16:21.100474+00:00
-- url     : https://prove2.me/theorems/672fc2e6-bf10-4262-ae2b-e2b0c8656077
-- title:
--   Proximal points, prox maps, maps contracting distances, and the primitive of prox_g
-- statement:
--   Let $H$ be a real Hilbert space and $f : H \to \,]-\infty, +\infty]$.
--
--   1. **Proximal point.** A point $x$ is a proximal point of $z$ relative to $f$ when it minimizes
--   $$
--   u \mapsto \tfrac12 \|u - z\|^2 + f(u).
--   $$
--   For $f \in \Gamma_0(H)$ this minimizer exists and is unique; it is written $\operatorname{prox}_f z$, and $z \mapsto \operatorname{prox}_f z$ is the proximal map of $f$.
--   2. **Prox map.** A map $p : H \to H$ is an *application prox* when $p = \operatorname{prox}_g$ for some $g \in \Gamma_0(H)$.
--   3. **Contracting distances.** A multivalued map $P$, associating to each $z \in H$ a (possibly empty) set $Pz \subseteq H$, contracts distances when
--   $$
--   x \in Pz,\ x' \in Pz' \ \Longrightarrow\ \|x - x'\| \le \|z - z'\|.
--   $$
--   4. **Primitive of $\operatorname{prox}_g$.** For a pair of dual functions $f, g$, with $x = \operatorname{prox}_f z$ and $y = \operatorname{prox}_g z$, the real-valued function
--   $$
--   \varphi(z) = \tfrac12 \|y\|^2 + f(x)
--   $$
--   is called the primitive of the map $\operatorname{prox}_g$.
--
--   These objects carry Sections 3, 7 and 10 of the paper: the goal characterizes prox maps as the distance-contracting maps that select a subgradient of a convex function, and the primitive is the convex function whose gradient is $\operatorname{prox}_g$.
--
--   **Formalization Note** The proximal point is encoded both as a predicate (`IsProx f z x`: $x$ minimizes the objective, computed in `EReal`) and as a function `prox f z`, which picks such a minimizer by choice when one exists and returns the junk value $0$ otherwise; every theorem using `prox f` assumes $f \in \Gamma_0(H)$, where the minimizer exists and is unique. A prox map is encoded through the predicate: there is $g \in \Gamma_0(H)$ such that for every $z$, $p(z)$ minimizes $u \mapsto \tfrac12\|u - z\|^2 + g(u)$. The primitive takes the pair $(f, g)$ as the paper does; it converts $f(\operatorname{prox}_f z)$ to a real number, which is harmless because this value is finite whenever $f \in \Gamma_0(H)$ and $g$ is the dual of $f$ (the hypotheses of every theorem that uses it).
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 278, Notation 3.b; p. 284, Définition 7.a; p. 291, §10.a

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
open scoped InnerProductSpace

namespace MoreauProx.Characterization

/-- Moreau 3.b: `x` minimizes the proximal objective `u ↦ ½‖u − z‖² + f(u)`
(values in `EReal`). For `f ∈ Γ₀(H)` this minimizer exists and is unique (Proposition 3.a),
and it is the proximal point `prox_f z`. -/
def IsProx {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (z x : H) : Prop :=
  ∀ u : H, ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal) + f x ≤ ((‖u - z‖ ^ 2 / 2 : ℝ) : EReal) + f u

open Classical in
/-- Moreau 3.b: the proximal map `prox_f`. It picks a minimizer of `u ↦ ½‖u − z‖² + f(u)` when
one exists, and returns the junk value `0` otherwise. Every theorem about `prox f` assumes
`f ∈ Γ₀(H)`, where the minimizer exists and is unique, so the junk branch is never used. -/
noncomputable def prox {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (z : H) : H :=
  if h : ∃ x, IsProx f z x then h.choose else 0

/-- A map `p : H → H` is an "application prox" when `p = prox_g` for some `g ∈ Γ₀(H)`,
i.e. `p z` minimizes `u ↦ ½‖u − z‖² + g(u)` for every `z`. -/
def IsProxMap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) : Prop :=
  ∃ g : H → EReal, GammaZero g ∧ ∀ z, IsProx g z (p z)

/-- Moreau 10.a: a multivalued map `P : H → Set H` contracts distances when
`x ∈ P z`, `x' ∈ P z'` imply `‖x − x'‖ ≤ ‖z − z'‖`. -/
def ContractsDistances {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H → Set H) : Prop :=
  ∀ z z' x x' : H, x ∈ P z → x' ∈ P z' → ‖x - x'‖ ≤ ‖z - z'‖

/-- Moreau Définition 7.a: for dual functions `f` and `g`, the primitive of `prox_g` is
`φ(z) = ½‖y‖² + f(x)` with `x = prox_f z`, `y = prox_g z`. Real-valued; `toReal` is harmless
when `f ∈ Γ₀(H)` and `g` is its dual, since then `f (prox f z)` is finite. -/
noncomputable def primitive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : H → EReal) (z : H) : ℝ :=
  ‖prox g z‖ ^ 2 / 2 + (f (prox f z)).toReal

end MoreauProx.Characterization


