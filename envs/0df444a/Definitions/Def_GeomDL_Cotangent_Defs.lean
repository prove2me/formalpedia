-- Prove2me | Definitions.Def_GeomDL_Cotangent_Defs
-- name    : GeomDL_Cotangent_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:58.425348+00:00
-- url     : https://prove2.me/theorems/e3c4b3cd-ee6b-48df-8252-2a36281b0f73
-- title:
--   §4.6, pp. 61–63 — triangular meshes, edge lengths ℓ, triangle area, Heron's formula and the cotangent Laplacian (24)–(25)
-- statement:
--   This file sets up the objects of the section *Geometric graphs and Meshes* (§4.6) of Bronstein, Bruna, Cohen and Veličković.
--
--   1. **Triangular mesh.** A mesh on the nodes $V = \{1,\dots,n\}$ is a finite set $\mathcal F$ of ordered triplets $(u,v,q)$, the faces. The order of the nodes is the orientation of the face. Every face has three distinct nodes, and no triangle appears twice in $\mathcal F$ (two faces with the same three nodes are equal).
--   2. **Embedding and metric.** The nodes are embedded by points $\mathbf x_1,\dots,\mathbf x_n$ of a Euclidean space, and the metric of the mesh is the edge length $\ell_{uv} = \|\mathbf x_u - \mathbf x_v\|$.
--   3. **Triangle area.** The area of the triangle with vertices $\mathbf x_u, \mathbf x_v, \mathbf x_q$ is the geometric quantity
--   $$a_{uvq} = \tfrac12\, \ell_{uq}\, \ell_{vq}\, \sin \angle uqv,$$
--   where $\angle uqv$ is the angle at $\mathbf x_q$ between the directions to $\mathbf x_u$ and $\mathbf x_v$.
--   4. **Heron's expression.** For three lengths $\ell_{uv}, \ell_{vq}, \ell_{uq}$ with semiperimeter $s = \tfrac12(\ell_{uv} + \ell_{uq} + \ell_{vq})$,
--   $$\operatorname{heron}(\ell_{uv}, \ell_{vq}, \ell_{uq}) = \sqrt{s(s-\ell_{uv})(s-\ell_{vq})(s-\ell_{uq})}.$$
--   5. **Local area element.** $a_u = \tfrac13 \sum_{f \in \mathcal F,\ u \in f} a_f$, the sum of the areas of the faces incident to $u$, each counted once, divided by three.
--   6. **Cotangent weights (25).** For nodes $u, v$, let $c_{uv}$ be the sum, over the faces containing both $u$ and $v$, of the cotangent of the angle opposite the edge $(u,v)$ (the angle at the third vertex). For an interior edge shared by the faces $(u,q,v)$ and $(u,p,v)$, $c_{uv} = \cot\angle uqv + \cot\angle upv$. The weight of (25) is $w_{uv} = c_{uv} / (2a_u)$; the unnormalised weight is $c_{uv}/2$.
--   7. **Laplacian (24).** For a weight function $w$, $\boldsymbol\Delta = \mathbf D - \mathbf W$ with $W_{uv} = w_{uv}$ for $u \ne v$, $W_{uu} = 0$, and $\mathbf D = \operatorname{diag}(d_1,\dots,d_n)$, $d_u = \sum_v W_{uv}$. The cotangent Laplacian uses the weights (25); the unnormalised one uses $c_{uv}/2$.
--   8. **Interior edge.** $(u,v)$ is an interior edge with opposite nodes $q \ne p$ if the faces containing both $u$ and $v$ are exactly two, with node sets $\{u,v,q\}$ and $\{u,v,p\}$.
--
--   The area is defined geometrically, not by Heron's formula, so that Heron's formula and the intrinsic form of the cotangent weights are theorems about these definitions.
--
--   **Formalization Note** The nodes are `Fin n` and the embedding takes values in any Euclidean affine space (the book's $\mathbb R^3$ is one instance). The book writes $a_u = \frac13\sum_{v,q:(u,v,q)\in\mathcal F} a_{uvq}$ over ordered triplets; since a face is stored once with one orientation, this is read as the sum over the faces incident to $u$. Angles are Mathlib's `EuclideanGeometry.angle` (vertex in the middle argument) and $\cot$ is `Real.cot`. For a degenerate triangle Lean's $\cot$ takes the junk value $0$ at the angles $0$ and $\pi$; every theorem that uses a cotangent assumes non-degenerate triangles.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.6, pp. 61–63: faces F p. 61, ℓ_uv = ∥x_u − x_v∥ p. 61, (24) and (25) p. 62, a_u p. 63, Heron's formula p. 63

import Mathlib

namespace GeomDL.Cotangent

open EuclideanGeometry

/-! Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning* (arXiv:2104.13478v2), §4.6,
pp. 61–63: triangular meshes, the metric `ℓ`, triangle areas, Heron's formula and the cotangent
Laplacian (24)–(25). The nodes are embedded in an arbitrary Euclidean affine space `P`
(the book's ℝ³ is `EuclideanSpace ℝ (Fin 3)`). -/

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- A triangular mesh on the nodes `Fin n` (p. 61): a finite set of ordered triplets
`(u, v, q)` (the faces `F`; the order is the orientation). Each face has three distinct
nodes, and no triangle is listed twice (two faces with the same three nodes are equal). -/
structure TriMesh (n : ℕ) where
  faces : Finset (Fin n × Fin n × Fin n)
  distinct : ∀ t ∈ faces, t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2
  injective : ∀ t ∈ faces, ∀ t' ∈ faces,
    ({t.1, t.2.1, t.2.2} : Finset (Fin n)) = {t'.1, t'.2.1, t'.2.2} → t = t'

/-- The set of the three nodes of a face `t = (a, b, c)`. -/
def vertexSet {n : ℕ} (t : Fin n × Fin n × Fin n) : Finset (Fin n) := {t.1, t.2.1, t.2.2}

/-- The vertices joined to `u` by a face edge. -/
noncomputable def vertexNeighbors {n : ℕ} (M : TriMesh n) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ≠ u ∧ ∃ t ∈ M.faces, u ∈ vertexSet t ∧ v ∈ vertexSet t)

/-- Consecutive vertices in the link of `u` are the other two vertices of a face at `u`. -/
def linkAdjacent {n : ℕ} (M : TriMesh n) (u v w : Fin n) : Prop :=
  v ≠ w ∧ v ≠ u ∧ w ≠ u ∧
    ∃ t ∈ M.faces, u ∈ vertexSet t ∧ v ∈ vertexSet t ∧ w ∈ vertexSet t

/-- The standing manifold-mesh assumption of §4.6, pp. 61–62: every edge belongs to two
triangles, every node has a face, and the link of every node is connected. Together with
`TriMesh.injective`, the two-face condition makes each vertex link 2-regular; connectivity
then says that the incident triangles form a single loop. -/
def IsManifoldMesh {n : ℕ} (M : TriMesh n) : Prop :=
  M.faces.Nonempty ∧
  (∀ u, (vertexNeighbors M u).Nonempty) ∧
  (∀ u v, u ≠ v →
    (M.faces.filter (fun t => u ∈ vertexSet t ∧ v ∈ vertexSet t)).Nonempty →
    (M.faces.filter (fun t => u ∈ vertexSet t ∧ v ∈ vertexSet t)).card = 2) ∧
  (∀ u v w, v ∈ vertexNeighbors M u → w ∈ vertexNeighbors M u →
    Relation.ReflTransGen (linkAdjacent M u) v w)

/-- The metric induced by the embedding `x` of the nodes (p. 61): `ℓ_uv = ‖x_u − x_v‖`. -/
noncomputable def edgeLength {ι : Type*} (x : ι → P) (u v : ι) : ℝ := dist (x u) (x v)

/-- The (geometric, extrinsic) area of the triangle with vertices `a, b, c`:
`½ · |ac| · |bc| · sin ∠acb`, the angle being taken at `c`. -/
noncomputable def triArea (a b c : P) : ℝ := (1 / 2) * dist a c * dist b c * Real.sin (∠ a c b)

/-- Heron's formula (p. 63) as a function of the three side lengths
`ℓ_uv, ℓ_vq, ℓ_uq`: `√(s(s − ℓ_uv)(s − ℓ_vq)(s − ℓ_uq))` with `s = ½(ℓ_uv + ℓ_uq + ℓ_vq)`. -/
noncomputable def heron (luv lvq luq : ℝ) : ℝ :=
  Real.sqrt (((luv + luq + lvq) / 2) * ((luv + luq + lvq) / 2 - luv) *
    ((luv + luq + lvq) / 2 - lvq) * ((luv + luq + lvq) / 2 - luq))

/-- The contribution of the face `t = (a, b, c)` to the edge `{u, v}`: if `{u, v}` is an edge of
`t`, the cotangent of the angle of `t` opposite that edge (at the third vertex), else `0`. -/
noncomputable def cotOpp {n : ℕ} (x : Fin n → P) (t : Fin n × Fin n × Fin n) (u v : Fin n) : ℝ :=
  if ({u, v} : Finset (Fin n)) = {t.1, t.2.1} then Real.cot (∠ (x t.1) (x t.2.2) (x t.2.1))
  else if ({u, v} : Finset (Fin n)) = {t.2.1, t.2.2} then Real.cot (∠ (x t.2.1) (x t.1) (x t.2.2))
  else if ({u, v} : Finset (Fin n)) = {t.1, t.2.2} then Real.cot (∠ (x t.1) (x t.2.1) (x t.2.2))
  else 0

/-- The local area element at `u` (p. 63): `a_u = ⅓ Σ_{faces f ∋ u} a_f`, the faces incident to
`u` each counted once. -/
noncomputable def vertexArea {n : ℕ} (M : TriMesh n) (x : Fin n → P) (u : Fin n) : ℝ :=
  (1 / 3) * ∑ t ∈ M.faces with u ∈ vertexSet t, triArea (x t.1) (x t.2.1) (x t.2.2)

/-- The cotangent weight (25), p. 62: `w_uv = (cot ∠uqv + cot ∠upv) / (2 a_u)`, the sum of the
cotangents of the angles opposite the edge `(u, v)` in the faces containing it, over `2 a_u`. -/
noncomputable def cotWeight {n : ℕ} (M : TriMesh n) (x : Fin n → P) (u v : Fin n) : ℝ :=
  (∑ t ∈ M.faces, cotOpp x t u v) / (2 * vertexArea M x u)

/-- The unnormalised cotangent weight `(cot ∠uqv + cot ∠upv) / 2` (no division by `a_u`). -/
noncomputable def cotWeightUnnorm {n : ℕ} (M : TriMesh n) (x : Fin n → P) (u v : Fin n) : ℝ :=
  (∑ t ∈ M.faces, cotOpp x t u v) / 2

/-- The Laplacian matrix (24), `Δ = D − W`, of a weight function `w` on `Fin n`:
`W_uv = w_uv` for `u ≠ v`, `W_uu = 0`, `D = diag(d_1, …, d_n)` with `d_u = Σ_v W_uv`. -/
def laplacianOf {n : ℕ} (w : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun u => ∑ v, (if u = v then 0 else w u v)) -
    Matrix.of (fun u v => if u = v then 0 else w u v)

/-- The cotangent Laplacian: (24) with the weights (25). -/
noncomputable def cotLaplacian {n : ℕ} (M : TriMesh n) (x : Fin n → P) :
    Matrix (Fin n) (Fin n) ℝ :=
  laplacianOf (cotWeight M x)

/-- The unnormalised cotangent Laplacian: (24) with the weights `(cot ∠uqv + cot ∠upv) / 2`. -/
noncomputable def cotLaplacianUnnorm {n : ℕ} (M : TriMesh n) (x : Fin n → P) :
    Matrix (Fin n) (Fin n) ℝ :=
  laplacianOf (cotWeightUnnorm M x)

/-- `(u, v)` is an interior edge of `M` shared by exactly two faces, with vertex sets
`{u, v, q}` and `{u, v, p}`, `q ≠ p` (p. 62: "the two angles in the triangles (u, q, v) and
(u, p, v) opposite the shared edge (u, v)"). -/
def IsInteriorEdge {n : ℕ} (M : TriMesh n) (u v q p : Fin n) : Prop :=
  u ≠ v ∧ q ≠ p ∧
    (M.faces.filter (fun t => u ∈ vertexSet t ∧ v ∈ vertexSet t)).image vertexSet =
      {{u, v, q}, {u, v, p}}

end GeomDL.Cotangent


