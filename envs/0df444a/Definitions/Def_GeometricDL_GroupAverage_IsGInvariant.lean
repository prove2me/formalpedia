-- Prove2me | Definitions.Def_GeometricDL_GroupAverage_IsGInvariant
-- name    : GeometricDL_GroupAverage_IsGInvariant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:10:22.763725+00:00
-- url     : https://prove2.me/theorems/d013e403-8133-4034-b5a3-30d3e23f4d8e
-- title:
--   $\mathfrak G$-invariant function
-- statement:
--   Let $\mathfrak G$ be a group and let $\rho$ be a representation of $\mathfrak G$ on a real normed space $E$ of signals, assigning to each $\mathfrak g \in \mathfrak G$ a bounded linear operator $\rho(\mathfrak g) : E \to E$ with $\rho(\mathfrak g\mathfrak h) = \rho(\mathfrak g)\rho(\mathfrak h)$ and $\rho(1) = \mathrm{id}$. A function $f : E \to \mathcal Y$ is **$\mathfrak G$-invariant** if
--   $$f(\rho(\mathfrak g)x) = f(x) \quad \text{for all } \mathfrak g \in \mathfrak G \text{ and } x \in E,$$
--   i.e. its output is unaffected by the group action on the input.
--
--   This is the basic symmetry prior of Geometric Deep Learning; the paper's main example is the action $(\mathfrak g.x)(u) = x(\mathfrak g^{-1}u)$ of a symmetry group of a domain $\Omega$ on signals $x : \Omega \to \mathbb R$.
--
--   **Formalization Note** The representation is a monoid homomorphism `G →* (E →L[ℝ] E)` into bounded operators on a real normed space; each $\rho(\mathfrak g)$ is then invertible with inverse $\rho(\mathfrak g^{-1})$. The function $f$ is arbitrary (no linearity is built in).
-- source:
--   Bronstein, Bruna, Cohen, Veličković, Geometric Deep Learning: Grids, Groups, Graphs, Geodesics, and Gauges, arXiv:2104.13478v2, §3.1, unnumbered definition (Invariant and Equivariant functions), p. 15 (PDF p. 19); representation, p. 15; action (3), p. 14

import Mathlib

namespace GeometricDL.GroupAverage

/-- **G-invariant function (p. 15).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning: Grids, Groups, Graphs, Geodesics,
and Gauges*, arXiv:2104.13478v2, §3.1, unnumbered definition, printed p. 15 (PDF p. 19):
"A function f : X(Ω) → Y is G-invariant if f(ρ(g)x) = f(x) for all g ∈ G and x ∈ X(Ω), i.e., its
output is unaffected by the group action on the input."

For a group `G`, a real normed space `E` (the paper's signal space X(Ω)), a representation
`ρ : G →* (E →L[ℝ] E)` and any function `f : E → Y`, `IsGInvariant ρ f` says
`f (ρ g x) = f x` for every `g : G` and `x : E`.

**Formalization Note.** The paper's representation (p. 15) assigns to each `g` an invertible
matrix `ρ(g)` with `ρ(gh) = ρ(g)ρ(h)`, or, for infinite Ω, a linear operator on X(Ω) (side note
p. 15). It is encoded as a monoid hom into continuous linear operators on a real normed space
`E`; invertibility follows from `ρ g * ρ g⁻¹ = ρ 1 = 1`. The paper's action (3), p. 14,
`(g.x)(u) = x(g⁻¹u)`, is one such representation. `f` is an arbitrary function: no linearity or
continuity is part of the definition. -/
def IsGInvariant {G : Type*} [Group G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type*}
    (ρ : G →* (E →L[ℝ] E)) (f : E → Y) : Prop :=
  ∀ (g : G) (x : E), f (ρ g x) = f x

end GeometricDL.GroupAverage


