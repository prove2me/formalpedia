-- Prove2me | Definitions.Def_TreeCoverLB_hardMetric
-- name    : TreeCoverLB_hardMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:05.997346+00:00
-- url     : https://prove2.me/theorems/710e6973-9198-45d7-92db-cc3d042d359d
-- title:
--   The hard metric $(X_r,d_r)$
-- statement:
--   Let $\Gamma$ triangulate the scaled cone $C_r$ over $E_d\mathbb Z_p$. The point set $X_r$ is the vertex set $\Lambda_r=V(\Gamma)$ with every boundary $\mathbb Z_p$-orbit contracted to one point: two vertices are identified iff they are boundary vertices $u\in\Lambda_r\cap r|K|$ and $v=\gamma^a u$ for some $a$; $\pi:\Lambda_r\to X_r$ is the quotient map. The metric $d_r$ is the shortest-path distance of the quotient graph: for $A,B\in X_r$ with fixed representatives $\hat A,\hat B$,
--   $$
--   d_r(A,B)=\inf\{\operatorname{len}(Q):\ Q \text{ a walk in } \widetilde G_r \text{ from } \hat A \text{ to } \hat B\}.
--   $$
--
--   **Formalization Note** The paper contracts the vertices at zero distance in $\widetilde G_r$; since ordinary edges have positive weight these are exactly the boundary orbits. Shortest walks between representatives do not depend on the representatives (special edges weigh zero), so $d_r$ is the shortest-path distance of the quotient graph $G_r$.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.13 (PDF p.15): X_r := V(G_r), d_r the shortest-path metric on G_r, π the quotient map

import Mathlib
import Definitions.Def_TreeCoverLB_GWalk

open Classical

namespace TreeCoverLB

/-- Two vertices of `Γ` are **identified** when they are boundary vertices in one `ℤ_p`-orbit:
`u ∈ ∂Λ_r = Λ_r ∩ r|K|` and `v = γ^a u` for some `a ∈ ℤ_p` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.13 (PDF p.15): "each
G-orbit in ∂Λ_r is identified to a single point; no interior vertex is identified"). -/
def orbitRel {p d : ℕ} [NeZero p] (r : ℝ) (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ)))
    (u v : ↥(vertexSet Γ)) : Prop :=
  (u : Fin (d + 1) × ZMod p → ℝ) ∈ coneBase (EJoin d (ZMod p)) r ∧
    ∃ a : ZMod p, (v : Fin (d + 1) × ZMod p → ℝ) = ejoinAct a u

/-- The point set `X_r = V(G_r)` of the **hard metric** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.13 (PDF p.15)): the vertices
`Λ_r = V(Γ)` of the triangulation with every boundary `ℤ_p`-orbit contracted to one point.
`π : Λ_r → X_r` is `Quot.mk`.

**Formalization Note** The paper contracts "vertices at zero distance" in `G̃_r`. Ordinary edges have
positive weight, so two vertices are at distance zero exactly when they are joined by special edges
only, i.e. when they are boundary vertices of one orbit; this is the relation `orbitRel` (whose
equivalence closure `Quot` takes). -/
def HardSpace {p d : ℕ} [NeZero p] (r : ℝ) (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))) :
    Type :=
  Quot (orbitRel r Γ)

/-- The **shortest-walk distance** in `G̃_r` between two points: the infimum of the weighted lengths
of all walks in `G̃_r` from `u` to `v` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.13). -/
noncomputable def gdist {p d : ℕ} [NeZero p] (r : ℝ)
    (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))) (u v : Fin (d + 1) × ZMod p → ℝ) : ℝ :=
  sInf {ℓ : ℝ | ∃ w : GWalk r Γ u v, w.length = ℓ}

/-- The **hard metric** `d_r` on `X_r` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.13 (PDF p.15): "let d_r be the shortest-path
metric on G_r"): `d_r(A, B)` is the shortest-walk distance in `G̃_r` between fixed representatives
`Â ∈ π⁻¹(A)` and `B̂ ∈ π⁻¹(B)` (the paper fixes such representatives in §4.2, p.14).

**Formalization Note** A shortest path in the quotient `G_r` lifts to a walk in `G̃_r` of the same
length between any two representatives (the special edges inserted at identified vertices weigh
zero, §4.2, p.14), so this does not depend on the representatives and equals the shortest-path
distance of `G_r`. The infimum is over a set bounded below by `0`; it is nonempty when the
1-skeleton of `Γ` is connected, which holds for every triangulation of the connected set `C_r`. -/
noncomputable def hardDist {p d : ℕ} [NeZero p] (r : ℝ)
    (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))) (A B : HardSpace r Γ) : ℝ :=
  gdist r Γ (Quot.out A : ↥(vertexSet Γ)) (Quot.out B : ↥(vertexSet Γ))

end TreeCoverLB


