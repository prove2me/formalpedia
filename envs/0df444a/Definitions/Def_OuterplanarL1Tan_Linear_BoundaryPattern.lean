-- Prove2me | Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern
-- name    : OuterplanarL1Tan_Linear_BoundaryPattern
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:11:26.725141+00:00
-- url     : https://prove2.me/theorems/83c43753-e663-44e2-b5e7-5ef08cc873e4
-- title:
--   The fixed boundary pattern, augmented map and stage norms
-- statement:
--   Let $H$ be a finite connected plane weighted graph, $B=\partial H$ its geometric boundary, and $b_0,\ldots,b_{m-1}$ its cyclic outer facial walk, including repeated visits. All distances in the following maps are intrinsic to $H$:
--
--   $$\Phi_H(z)_j=d_H(z,b_j)-d_H(z,b_{j+1}),\qquad d_H(z,B)=\min_{b\in B}d_H(z,b),$$
--   $$g_H(z)=\tfrac14\Phi_H(z)\oplus 2d_H(z,B).$$
--
--   Coordinates carry the sum norm. For endpoints $x,y$, the potential is $q(z)=d_H(x,z)-d_H(y,z)$ and the threshold set is $A_t=\{z:q(z)\le t\}$. Its transition count includes every consecutive pair of visits and the final-to-first pair.
--
--   For the ambient graph $G$, stage $n=0$ has prescribed norm $h_1(x)=\operatorname{diam}(G)$, and stage $n>0$ has $h_{n+1}(x)=d_G(x,V\setminus R_n)$. A component map is extended by zero outside that component in its own coordinate block. These definitions distinguish ambient and intrinsic distances.
--
--   The maps are determined by graph data and the chosen facial order; none is an arbitrary function postulated to satisfy the desired estimates.
--
--   **Formalization Note** Finite vectors use `PiLp 1`, including the direct sum's extra coordinate. Boundary distances are real infima of finite nonempty sets in all milestone applications. The diameter includes zero in its defining set, giving diameter zero for the empty graph. Equation (5) has a separate first-stage branch, so it never uses distance to the empty set there. Definitions have total values outside the theorem domain; their defaults and valid-use guards are recorded in the moderation notes.
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 2–3, 7, §§2.1–2.2, §3.3 equation (5) (PDF p. 3–4, 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Definitions.Def_OuterplanarL1Tan_Linear_PlaneGeometry

namespace OuterplanarL1Tan.Linear

/-- Real finite-dimensional ℓ₁, with the sum norm, including dimension zero. -/
abbrev L1Vector (n : ℕ) := PiLp 1 (fun _ : Fin n => ℝ)

/-- The fixed pattern map of §2.1, indexed by boundary visits, not distinct vertices. -/
noncomputable def pattern {V : Type} (W : WeightedGraph V)
    (D : PlaneDrawing W.graph) (B : OuterFacialWalk D) (z : V) :
    L1Vector B.size :=
  WithLp.toLp 1 (fun j => W.distance z (B.vertex j) -
    W.distance z (B.vertex (cyclicNext B.positive j)))

/-- Intrinsic distance to the geometric outer boundary. Used only for finite
reachable graphs with a facial walk, so the set is nonempty and bounded below. -/
noncomputable def boundaryDistance {V : Type} (W : WeightedGraph V)
    (D : PlaneDrawing W.graph) (z : V) : ℝ :=
  sInf {r : ℝ | ∃ b ∈ D.boundary Set.univ, r = W.distance z b}

/-- The fixed map `g_H = (Φ_H / 4) ⊕ (2 d_H(·,∂H))`, in an ℓ₁ sum.
Using `Sum` as coordinate type gives the sum norm also on the extra coordinate. -/
noncomputable def augmented {V : Type} (W : WeightedGraph V)
    (D : PlaneDrawing W.graph) (B : OuterFacialWalk D) (z : V) :
    PiLp 1 (fun _ : Fin B.size ⊕ Unit => ℝ) :=
  WithLp.toLp 1 (Sum.elim (fun j => (1 / 4 : ℝ) * pattern W D B z j)
    (fun _ => 2 * boundaryDistance W D z))

/-- The source's `q(z)` for fixed endpoints. -/
noncomputable def differencePotential {V : Type} (W : WeightedGraph V)
    (x y z : V) : ℝ := W.distance x z - W.distance y z

/-- The source's sublevel set uses the non-strict threshold convention. -/
noncomputable def sublevel {V : Type} (W : WeightedGraph V) (x y : V)
    (t : ℝ) : Set V := {z | differencePotential W x y z ≤ t}

/-- Number of cyclic indicator transitions, including the last-to-first step. -/
noncomputable def transitionCount {V : Type} {G : SimpleGraph V}
    (D : PlaneDrawing G) (B : OuterFacialWalk D) (A : Set V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => ¬ (B.vertex j ∈ A ↔
    B.vertex (cyclicNext B.positive j) ∈ A))).card

/-- Intrinsic finite diameter, with value zero also on the empty graph. -/
noncomputable def graphDiameter {V : Type} (W : WeightedGraph V) : ℝ :=
  sSup (insert 0 {r : ℝ | ∃ x y : V, r = W.distance x y})

/-- The prescribed norm in (5), with an explicit first-round branch.
The graph is finite and reachable whenever this is used in the construction. -/
noncomputable def stageNorm {V : Type} (W : WeightedGraph V)
    (D : PlaneDrawing W.graph) (n : ℕ) (x : V) : ℝ :=
  if n = 0 then graphDiameter W else
    sInf {r : ℝ | ∃ a ∈ D.earlierLayers n, r = W.distance x a}

/-- Extension of a component map by zero into its own coordinate block. -/
noncomputable def extendByZero {V : Type} {S : Set V} {n : ℕ}
    (f : S → L1Vector n) (x : V) : L1Vector n := by
  classical
  exact if h : x ∈ S then f ⟨x, h⟩ else 0

end OuterplanarL1Tan.Linear


