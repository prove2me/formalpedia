-- Prove2me | Definitions.Def_Q146C003
-- name    : Q146C003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:08:07.458562+00:00
-- url     : https://prove2.me/theorems/418c54e1-ea04-491a-b14b-71d518c8f4d0
-- title:
--   Definitions bundle Q146C003 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 756 declarations of OpenAI's Lean: 89 definitions, 24 inductive types or structures, 2 instances and 641 theorems. The definitions and types are `Graph.IsPathGraph`, `Graph.IsTwoConnected`, `Graph.component`, `Graph.mapDrawing`, `Graph.relabelDrawing`, `Graph.walkPointSet`, `OAI.CircleDomainRigidity.DiskRayTime`, `Schoenflies.ArcCollar`, `Schoenflies.ArcHomeo`, `Schoenflies.ArcMatch`, `Schoenflies.ArcStrip`, `Schoenflies.ArcStrip.blockL`, `Schoenflies.ArcStrip.blockR`, `Schoenflies.ArcStrip.chainL`, `Schoenflies.ArcStrip.chainR`, `Schoenflies.ArcStrip.collar`, `Schoenflies.ArcStrip.nbhd`, `Schoenflies.ArcStrip.sectorL`, `Schoenflies.ArcStrip.sectorR`, `Schoenflies.ArcStrip.sideL`, `Schoenflies.ArcStrip.sideR`, `Schoenflies.ArcStrip.tube`, `Schoenflies.CellStructure.BoundaryCycles`, `Schoenflies.CellStructure.CombInvariants`, `Schoenflies.CellStructure.FaceCycle`, `Schoenflies.CellStructure.OuterEdgeUniqueFace`, `Schoenflies.CellStructure.Realization.IsCellDecomposition`, `Schoenflies.CellStructure.Realization.IsFaceJordan`, `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible`, `Schoenflies.CellStructure.Realization.Refines`, `Schoenflies.CellStructure.Realization.cellUnion`, `Schoenflies.CellStructure.Realization.outerSet`, `Schoenflies.CellStructure.SplitData`, `Schoenflies.CellStructure.SplitData.EarCrosscut`, `Schoenflies.CellStructure.SplitData.EarHomeo`, `Schoenflies.CellStructure.SplitData.EarHomeo.symm`, `Schoenflies.CellStructure.SplitData.cells₁`, `Schoenflies.CellStructure.SplitData.cells₂`, `Schoenflies.CellStructure.SplitData.earCells`, `Schoenflies.CellStructure.SplitData.earGraph` and 73 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `ArcCollars`, `ArcComplement`, `ArcComplementPrep`, `ArcMonotone`, `BoundaryCycles`, `CellulationInvariants`, `CircleDomains_Topology_DiskRayLift`, `CombinatorialInvariance`, `CrosscutAtMostTwo`, `CrosscutEncloses`, `CrosscutExists`, `Curve`, `Direction`, `FaceCycles`, `FaceCyclesProof`, `FiniteTransfer`, `GeneratedStructure`, `Graph_Component`, `Graph_CycleJordan`, `Graph_Drawing`, `Graph_Ear`, `Graph_K33Land`, `Graph_K33Planar`, `Graph_OuterFace`, `Graph_PathGraph`, `Graph_Redrawing`, `Graph_Relabel`, `Graph_Tree`, `Graph_TwoConnected`, `Graph_VertexSquares`, `Graph_Walk`, `JordanSeparates`, `LocallyPolygonal`, `MatchedArc`, `MatchedSplit`, `ModelCurve`, `OuterChain`, `Overlay`, `OverlayGraph`, `PolyArcRealize`, `PolyLocal`, `PolyPath`, `PolygonalCarrier`, `PrePolygonArc`, `Realization`, `RealizeSplit`, `RealizeSubdiv`, `RealizeSubdivHomeo`, `RefinementStars`, `SegmentCut`, `SegmentMeet`, `SegmentOrder`, `SimpleArc`, `SkeletonLocal`, `Square`, `SquareMover`, `Subarc`, `Subdivide`, `Topology`.
--
--   **Imports.** It imports the bundles `Q146C000` and `Q146C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q146C006`, `Q146C007` and `Q146C008`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_Q146C000
import Definitions.Def_Q146C001

section
-- module Solutions.Q146_CD.Curve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Arcs and Jordan curves

A simple arc is the image of an injective continuous map from `[0, 1]`; a Jordan curve is
the image of a map on `[0, 1]` which is injective before it returns to its start. Those are
the blueprint's definitions verbatim.

The parameter domain is a *subset of `ℝ`*, not a type: an arc is carried by an ordinary
`f : ℝ → Plane` together with `ContinuousOn f unitInterval` and `InjOn f unitInterval`.
Mathlib's `Path` bundles a map out of `↥unitInterval` instead, which is the right choice
when paths are to be composed up to homotopy, and the wrong one here: subarcs are taken at
arbitrary parameter pairs, reparametrisation is composition on `ℝ` with nothing to extract,
and a Jordan curve's theorems are all about *its parameters*. Taking the circle as the
domain would need a traversal of the circle by an interval, which is exactly what a
trigonometry-free development does not have.

`IsArcBetween` is the set-level reading — an arc *between two named points* — and is the
form most of the development speaks, since gluing and cutting are stated about endpoints.

## Blueprint

* `IsArc`, `IsJordanCurve` — §1, the definitions of a simple arc and a Jordan curve.
* `IsArcBetween` — an arc between two named points.
* `IsLoop` — the parametrisation underlying a Jordan curve.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Arcs -/

/-- A simple arc: the image of a continuous injective map on `[0, 1]`. -/
def IsArc (A : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A

/-! ### The unit interval, as a subset of `ℝ` -/

/-- The image of a relatively closed piece of the parameter interval is compact. This is
what makes a parametrisation a closed map onto its arc, and hence its inverse continuous. -/
theorem isCompact_image_of_subset_I {f : ℝ → Plane} (hf : ContinuousOn f I)
    {S : Set ℝ} (hS : S ⊆ I) (hSc : IsClosed S) : IsCompact (f '' S) :=
  (isCompact_I.of_isClosed_subset hSc hS).image_of_continuousOn (hf.mono hS)

/-! ### Elementary properties -/

namespace IsArcBetween

variable {A : Set Plane} {p q : Plane}

theorem isArc (h : IsArcBetween A p q) : IsArc A := by
  obtain ⟨f, hc, hi, him, -, -⟩ := h
  exact ⟨f, hc, hi, him⟩

end IsArcBetween

namespace IsArc

variable {A : Set Plane}

theorem isCompact (h : IsArc A) : IsCompact A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hc

theorem isConnected (h : IsArc A) : IsConnected A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isConnected_I.image f hc

theorem isClosed (h : IsArc A) : IsClosed A := h.isCompact.isClosed

end IsArc

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolyPath
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_pair _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polygonal paths

A polygonal path is carried by a list of vertices; its `poly` carrier is the union of the
segments joining consecutive entries. This is the combinatorial representation the whole
of Part I works with — by the blueprint's polygonal overlay convention only finite
polygonal objects are ever overlaid, so vertex lists, not parametrizations, are the
primitive.

## Blueprint

* `poly` — the carrier of a polygonal path.
* `exists_poly_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), less the passage
  to a *simple* arc, which needs the finite-graph machinery and is proved with Lemma 1.2.
-/

open Metric Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

/-! ### Segments -/

/-! ### The carrier of a vertex list -/

theorem poly_nonempty : ∀ {vs : List Plane}, vs ≠ [] → (poly vs).Nonempty
  | [], h => absurd rfl h
  | [v], _ => ⟨v, rfl⟩
  | _ :: v :: _, _ => ⟨v, Or.inl (right_mem_segment ℝ _ _)⟩

theorem isCompact_poly : ∀ vs : List Plane, IsCompact (poly vs)
  | [] => by simp
  | [v] => by simp
  | u :: v :: rest => by
    rw [poly_cons_cons]
    exact (isCompact_segment u v).union (isCompact_poly (v :: rest))

theorem head_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.head h ∈ poly vs :=
  mem_poly_of_mem (List.head_mem h)

theorem getLast_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.getLast h ∈ poly vs :=
  mem_poly_of_mem (List.getLast_mem h)

/-- The carrier of a nonempty vertex list is connected: consecutive segments share a vertex. -/
theorem isConnected_poly : ∀ {vs : List Plane}, vs ≠ [] → IsConnected (poly vs)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isConnected_singleton (x := v)
  | u :: v :: rest, _ => by
    rw [poly_cons_cons]
    refine IsConnected.union ⟨v, right_mem_segment ℝ u v, head_mem_poly (by simp)⟩
      ((convex_segment u v).isConnected ⟨u, left_mem_segment ℝ u v⟩)
      (isConnected_poly (List.cons_ne_nil v rest))

/-- Appending one vertex extends the carrier by one segment. -/
theorem poly_concat : ∀ {vs : List Plane} (h : vs ≠ []) (z : Plane),
    poly (vs ++ [z]) = poly vs ∪ segment ℝ (vs.getLast h) z
  | [], h, _ => absurd rfl h
  | [v], _, z => by
    simp only [List.singleton_append, poly_cons_cons, poly_singleton, List.getLast_singleton]
    rw [union_singleton, insert_eq_self.2 (right_mem_segment ℝ v z), singleton_union,
      insert_eq_self.2 (left_mem_segment ℝ v z)]
  | u :: v :: rest, _, z => by
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_concat (List.cons_ne_nil v rest) z,
      List.getLast_cons (List.cons_ne_nil v rest)]
    exact (union_assoc _ _ _).symm

/-! ### Polygonal connectedness -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Direction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Directions, and the two arcs cut out by a pair of rays

This module supplies the *direction facts* that the two-sided strip lemma runs on. Everything
here is stated through the sign of the orientation form `Plane.det`: no angle is named, no
inverse trigonometric function appears, and no case distinction on the sense of a turn is
ever made.

A *direction* is a unit vector (`Plane.IsDirection`). What actually matters about a direction
is its ray — the set of its positive multiples — because every predicate below is invariant
under positive scaling (`Plane.smul_mem_arcCCW`). So the arcs are defined on all nonzero
vectors and the unit-vector normalisation `Plane.dir` is only a convenience.

## The two arcs

Two directions `u` and `w` that are neither equal nor opposite are exactly two directions with
`det u w ≠ 0` (`Plane.det_ne_zero_iff`). They cut the circle of directions into two open arcs.
The arc traversed counterclockwise from `u` to `w` is `Plane.arcCCW u w`, defined by Sedgewick's
`ccw` predicate on the triple `(u, d, w)`: at least two of the three consecutive orientation
forms are positive. This definition is manifestly invariant under rotating the triple, and — this
is the point — it is correct for *both* arcs at once, the short one and the long one, with no
sign hypothesis in the definition itself.

`Plane.mem_ray_or_mem_arcCCW` and `Plane.arcCCW_disjoint` say that the two arcs and the two
bounding rays partition the nonzero vectors.

## The transfer fact

`Plane.same_arc_of_det_neg_of_det_pos` is Appendix C's transfer fact: *a direction with negative
`det` against the first ray lies on the same arc as a direction with positive `det` against the
second*. Note that no nearness hypothesis is needed for it — see the module note below.

## Blueprint

* `Plane.IsDirection`, `Plane.dir`, `Plane.arcCCW`, `Plane.det_ne_zero_iff`,
  `Plane.mem_ray_or_mem_arcCCW`, `Plane.arcCCW_disjoint` — Appendix C, item 1, "two distinct,
  non-opposite unit vectors bound two open arcs of directions".
* `Plane.same_arc_of_det_neg_of_det_pos` — Appendix C, item 1, the transfer fact.
* `Plane.exists_isDirection_det_ne_zero`, `Plane.exists_isDirection_det_and_inner_ne_zero` —
  Appendix C, item 1, "the existence of a unit vector avoiding any prescribed finite set of
  directions".
* `Plane.germs_split`, `Plane.exists_germ_threshold` — the vertex matching inside Lemma 1.8
  (Two-sided polygonal strips): the two left half-strip germs land on one arc and the two right
  ones on the other.

## A note on "near"

Appendix C states the transfer fact for directions *near* the two bounding rays. The nearness is
not needed: `Plane.mem_arcCCW_rev_iff` shows that the arc counterclockwise from `w` to `u` is cut
out by a *disjunction* of two sign conditions, so a single sign suffices to land on it. The
mirror statement — a direction with positive `det` against `u` and one with negative `det`
against `w` both lie on `arcCCW u w` — is *not* available from one sign each, because that arc is
cut out by the *conjunction* (`Plane.mem_arcCCW_iff`). Lemma 1.8 needs the mirror statement too,
for the two right germs, and there the missing second sign is exactly what "`s/t` small" buys:
`Plane.exists_germ_threshold` supplies it, with an explicit threshold.
-/

open Set

namespace Schoenflies

namespace Plane

variable {u w d d₁ d₂ r₁ r₂ v : Plane} {r t s : ℝ}

/-! ### Directions -/

theorem IsDirection.ne_zero (hu : IsDirection u) : u ≠ 0 := by
  intro h
  rw [IsDirection, h, norm_zero] at hu
  exact zero_ne_one hu

/-! ### Nonvanishing of `det` -/

/-! ### The two arcs -/

/-! ### The transfer fact -/

/-! ### Half-strip germs

Fix a vertex with incoming unit tangent `u` and outgoing unit tangent `w`, and let `r₁ = -u`,
`r₂ = w` be the two rays leaving the vertex, so that `perp r₁ = -u^⊥` and `perp r₂ = w^⊥`.
Then the four half-strip germs of Lemma 1.8 are, in the blueprint's own notation,

* incoming left, `-t u + s u^⊥ = t • r₁ - s • perp r₁`;
* outgoing left, `t w + s w^⊥ = t • r₂ + s • perp r₂`;
* incoming right, `-t u - s u^⊥ = t • r₁ + s • perp r₁`;
* outgoing right, `t w - s w^⊥ = t • r₂ - s • perp r₂`,

each with `t, s > 0`. The four computations below place them on the two arcs. -/

/-! ### A direction avoiding finitely many others

The argument is a counting one, with no measure and no trigonometry: the one-parameter family
`a ↦ (1, a)` meets the line of any fixed nonzero vector at most once, so finitely many vectors
rule out only finitely many parameters, and `ℝ` has more than finitely many. -/

/-! ### The arcs are open

Not needed by Lemma 1.8, which uses only the partition, but it justifies the word "open" in
"two open arcs of directions". -/

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.Subarc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subarcs, open arcs, and the subarc basis

A subarc is the arc restricted to a subinterval of the parameter interval — but an arc is
carried by a map *on* `[0, 1]`, so the restriction has to be reparametrised back onto it.
That reparametrisation is `reparam a b : t ↦ a + t * (b - a)`: pure arithmetic, with no
inverse to construct and no choice to make. With it a subarc is a composition, and the two
things an arc must be — continuous and injective — are the two things a composition inherits.

Injectivity is required only on `uIcc a b`, the parameter interval actually traversed, not on
all of `[0, 1]`. That is what lets the two arcs of a Jordan curve be cut out of a loop, whose
parametrisation is injective on `[0, 1)` only.

The substance of the file is the last two sections. A parametrisation is an **open map onto
its arc**: the image of a relatively open piece of the parameter interval is relatively open
in the arc. This is where the continuity of the inverse earns its keep, and it is proved
without ever constructing that inverse — a continuous injection on a compact set is a closed
map onto its image, and a closed injective map is open onto its image, by complements.
Together with `basic_piece_inside_ball`, which puts such a piece inside any prescribed ball,
these images are a basis of the arc's subspace topology.

Relative openness is stated in the ambient form `∃ V, IsOpen V ∧ W = V ∩ A` rather than
through the subtype `↥A`, since every consumer here works with subsets of the plane.

## Blueprint

The blueprint uses subarcs throughout §1 without a numbered statement of their own; they are
the tool behind, among others, the model-curve parametrization (`lem:jordan-circle`), where
"the relatively open subarcs of `C`" are exactly the images produced by `image_isRelOpen`, and
the density arguments of `lem:accessible-dense`, which need `basic_piece_inside_ball`.

* `subarc`, `isArcBetween_subarc` — a piece of an arc is again an arc.
* `IsArc.exists_isArcBetween_subset` — the set-level reading: two points of an arc bound a
  subarc of it.
* `openArc` — the blueprint's `P°`, an arc without its two endpoints.
* `image_isRelOpen` — a parametrisation is an open map onto its arc; `openArc_isRelOpen` and
  `openArc_subarc_isRelOpen` are the "relatively open subarcs" of `lem:jordan-circle`.
* `basic_piece_inside_ball` — the subarc basis.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Reparametrising `[0, 1]` onto a subinterval -/

variable {a b : ℝ}

theorem continuous_reparam : Continuous (reparam a b) := by unfold reparam; fun_prop

/-- The reparametrisation is injective as soon as it is not constant. -/
theorem reparam_injective (hab : a ≠ b) : Function.Injective (reparam a b) := by
  intro s t hst
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have : s * (b - a) = t * (b - a) := by
    have := hst
    simp only [reparam] at this
    linarith
  exact mul_right_cancel₀ hba this

/-- `reparam a b` carries the unit interval exactly onto `uIcc a b`. This is `segment_eq_image'`
read through the identification of a real segment with an unordered closed interval. -/
theorem image_reparam_I : reparam a b '' I = uIcc a b := by
  have h : (fun θ : ℝ => a + θ • (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
    rw [← segment_eq_image' ℝ a b, segment_eq_uIcc]
  simp only [smul_eq_mul] at h
  exact h

theorem mapsTo_reparam : MapsTo (reparam a b) I (uIcc a b) :=
  mapsTo_iff_image_subset.mpr image_reparam_I.subset

/-! ### Subarcs -/

variable {f : ℝ → Plane}

/-- The image of a subarc is the arc restricted to the subinterval — which is what "sub"
means, and the form every consumer wants. -/
theorem subarc_image : subarc f a b '' I = f '' uIcc a b := by
  rw [show subarc f a b = f ∘ reparam a b from rfl, image_comp, image_reparam_I]

theorem continuousOn_subarc (hc : ContinuousOn f I) (ha : a ∈ I) (hb : b ∈ I) :
    ContinuousOn (subarc f a b) I :=
  hc.comp continuous_reparam.continuousOn
    (mapsTo_reparam.mono_right (uIcc_subset_I ha hb))

/-- Injectivity of the subarc needs injectivity of `f` only where the subarc runs. -/
theorem injOn_subarc (hi : InjOn f (uIcc a b)) (hab : a ≠ b) : InjOn (subarc f a b) I := by
  intro s hs t ht hst
  exact reparam_injective hab (hi (mapsTo_reparam hs) (mapsTo_reparam ht) hst)

/-- A subarc between two distinct parameters is an arc between the two values there. The
injectivity hypothesis is confined to the traversed interval, so this applies to a piece of a
Jordan curve as well as to a piece of an arc. -/
theorem isArcBetween_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  ⟨subarc f a b, continuousOn_subarc hc ha hb, injOn_subarc hi hab,
    subarc_image, subarc_zero, subarc_one⟩

/-- The version for an arc, whose parametrisation is injective everywhere. -/
theorem isArcBetween_subarc_of_injOn_I (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  isArcBetween_subarc hc (hi.mono (uIcc_subset_I ha hb)) ha hb hab

/-! ### The arc without its endpoints -/

/-! ### The interior of an arc, set-level

`openArc` is stated for a parametrisation. Three separate modules needed the same facts stated
for the *set* — `IsArcBetween A p q` gives `A ∖ {p, q}` connected, nonempty, and having both
endpoints in its closure — and each proved them again from scratch, one of them twice under two
names. Two of those copies were literally the same statement in modules that do not import each
other, so the build never noticed: alpha-equivalent `Prop`s are defeq under proof irrelevance,
and Lean's import checker accepts them. They live here now. -/

/-- The interior of an arc is nonempty: `Ioo 0 1` is. -/
theorem IsArcBetween.nonempty_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    (A \ {p, q}).Nonempty := by
  obtain ⟨f, -, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact ⟨f (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- The interior of an arc is connected in the nonempty sense. -/
theorem IsArcBetween.isConnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsConnected (A \ {p, q}) :=
  ⟨h.nonempty_diff, h.isPreconnected_diff⟩

/-! ### A parametrisation is an open map onto its arc -/

/-- **The parametrisation is an open map onto its arc.** The image of a relatively open piece
of the parameter interval is relatively open in the arc.

No inverse is constructed. The complement piece `I \ U` is compact, so its image is compact,
so it is closed; and by injectivity the image of `U ∩ I` is exactly the arc minus that closed
set. Stated for a relatively open *piece* `U ∩ I` rather than for a subarc, because at an
endpoint the basic neighbourhood is half-open — `openArc` of a subarc is the interior case,
and this covers both. -/
theorem image_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) {U : Set ℝ} (hU : IsOpen U) :
    ∃ V : Set Plane, IsOpen V ∧ f '' (U ∩ I) = V ∩ f '' I := by
  refine ⟨(f '' (I \ U))ᶜ, ?_, ?_⟩
  · -- The discarded piece is compact, hence closed, so its complement is open.
    exact (isCompact_image_of_subset_I hc sdiff_subset
      (isClosed_Icc.sdiff hU)).isClosed.isOpen_compl
  · -- Injectivity turns "remove the image" into "image of the removal".
    have hdiff : f '' (I \ (I \ U)) = f '' I \ f '' (I \ U) :=
      hi.image_sdiff_subset sdiff_subset
    rw [sdiff_sdiff_right_self, inter_comm I U] at hdiff
    rw [hdiff, sdiff_eq, inter_comm]

/-- The pointwise reading of the previous theorem, and the one consumers use: around every
point of the image of a relatively open piece there is a ball meeting the arc only inside that
image. This is precisely the continuity of the inverse parametrisation. -/
theorem exists_ball_inter_subset_image (hc : ContinuousOn f I) (hi : InjOn f I)
    {U : Set ℝ} (hU : IsOpen U) {x : Plane} (hx : x ∈ f '' (U ∩ I)) :
    ∃ ε > 0, Metric.ball x ε ∩ f '' I ⊆ f '' (U ∩ I) := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi hU
  have hxV : x ∈ V := (hV ▸ hx).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen x hxV
  exact ⟨ε, hε, fun y hy => hV ▸ ⟨hball hy.1, hy.2⟩⟩

/-! ### The subarc basis -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Topology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Topology of the plane: the gaps Mathlib leaves

Appendix C of the blueprint lists the topology imported without proof. Almost all of it is in
Mathlib: compactness and Heine–Borel, the compact-to-Hausdorff homeomorphism criterion,
connectedness and its stability under images, unions through a common point, adjoining closure
points (`IsPreconnected.subset_closure`), a connected set inside a disjoint union of two opens
(`IsPreconnected.subset_left_of_subset_union`), `Metric.diam_closure`, thickenings, and the
two-piece pasting lemma (`continuousOn_union_iff_of_isClosed`).

This module collects the few that are not stated in the form the development uses.

## Blueprint

* `isOpen_connectedComponentIn` — Appendix C item 4: components of open subsets of the plane
  are open. The plane is locally connected, so this is Mathlib's, restated at `Plane` so that
  the instance is found once here rather than at every call site.
* `frontier_connectedComponentIn_compl_subset` — Appendix C item 5: the boundary of a component
  of the complement of a closed set lies in that closed set. This is the form Part I uses to
  recognize that a region's frontier sits on the curve.
* `continuousOn_union_of_isClosed` — Appendix C item 6, the pasting lemma, in the two-piece
  form the development pastes with.
-/

open Metric Set

namespace Schoenflies

namespace Plane

variable {U K : Set Plane} {x : Plane}

/-- Appendix C item 6, the pasting lemma, two closed pieces. -/
theorem continuousOn_union_of_isClosed {f : Plane → Plane} {s t : Set Plane}
    (hs : IsClosed s) (ht : IsClosed t) (hfs : ContinuousOn f s) (hft : ContinuousOn f t) :
    ContinuousOn f (s ∪ t) :=
  (continuousOn_union_iff_of_isClosed hs ht).2 ⟨hfs, hft⟩

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.CrosscutAtMostTwo
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A crosscut cuts a region into at most two pieces

Lemma "At most two sides": if `D` is a region and `P` is a simple polygonal arc whose endpoints
lie *outside* `D` and whose remaining points lie in `D`, then `D ∖ P` has at most two
components. This is the missing half of the crosscut theorem — the crosscut-cells lemma
(`Schoenflies.crosscut_cells`) already exhibits two components, and this says there are no
others.

## "At most two" as a covering statement

Nothing here talks about the *set* of components. What is proved, and what the crosscut theorem
consumes, is the constructive form: two points `z_L, z_R` of `D ∖ P` such that every point of
`D ∖ P` lies in the component of one of them (`crosscut_at_most_two`). Handed two components
that are known to be distinct — which is exactly what the crosscut-cells lemma supplies — that
turns into "every point lies in one of *those* two" (`crosscut_components_exhaust`), which is
the sentence the crosscut theorem actually needs.

## The proof is a clopen argument, not the blueprint's path argument

The blueprint traces a polygonal arc `γ` from an arbitrary `x ∈ D ∖ P` to a reference point
`z₀ ∈ P`, takes the first point `z` of `γ` on `P`, and pushes `x` into a track of a strip around
the subarc of `P` from `z` to `z₀`. The first-hitting-point step is only there to *find* a point
of `D ∖ P` next to `P`; once one knows that a whole neighbourhood of every point of `P ∩ D` is
covered by the two components, the statement is a connectedness argument and no path is needed:

* `T`, the set of points of `D ∖ P` in neither of the two components, is open, because a
  component of an open subset of the plane is open and two components are equal or disjoint
  (`isOpen_notMem_two_components`);
* `U`, the union of the two components with every open piece of `D` whose complement of `P` is
  covered, is open and contains all of `P ∩ D`;
* `U` and `T` are disjoint, cover `D`, and `U` meets `D`; so `T = ∅` because `D` is connected.

That is `covered_by_two_of_local`, and it is where "at most two" really comes from. The arc, the
polygonality and the endpoint hypotheses enter only through the collar.

## The collar is a hypothesis: `Schoenflies/Strip.lean` is stated for a closed curve

The local input the argument needs is blueprint Lemma 1.8 (b) — a two-sided collar of a compact
subarc of `P ∖ ∂P`. `Schoenflies/Strip.lean`, `Schoenflies/StripLocal.lean` and
`Schoenflies/Compose.lean` build the collar of a `ClosedPolygon`, a *closed* curve, and the note
at the end of `StripLocal.lean` says in as many words that the arc case "is not formalised".
There is no way to get it from the closed case: the two tracks of a closed collar are connected
because they run all the way round the curve, and intersecting them with `D` destroys exactly
that.

So `HasArcCollars D P` is an explicit hypothesis of every theorem below. It is blueprint
Lemma 1.8 (b) with the prescribed open set taken to be `D`, together with the "local sides"
clause of that lemma in the form `StripLocal.lean` already proves in the closed case
(`StripData.carrier_subset_closure_sideL`): every point of the subarc is in the closure of both
tracks. `ArcCollar` is the bundled datum, so a discharger returns a construction rather than an
existential.

## Blueprint

* `Schoenflies.ArcCollar`, `Schoenflies.HasArcCollars` — Lemma 1.8 (b) (two-sided polygonal
  strips, the arc case) as an interface: the collar of one compact subarc as data, and the
  hypothesis that every compact subarc has one.
* `Schoenflies.isOpen_notMem_two_components`, `Schoenflies.covered_by_two_of_local` — the clopen
  step, which is the whole of the lemma once the collar is available.
* `Schoenflies.crosscut_at_most_two` — Lemma "At most two sides".
* `Schoenflies.crosscut_components_exhaust` — the same, applied to two components already known
  to be distinct; this is the form Theorem "Crosscut theorem" cites.
* `Schoenflies.Plane.mem_segment_iff_coord`, `Schoenflies.hasArcCollars_segment` — Lemma 1.8 (b)
  for a straight crosscut, which is the blueprint's edge block and nothing else. With it,
  `Schoenflies.segment_crosscut_at_most_two` is Lemma "At most two sides" for a straight
  crosscut with no hypothesis left standing, and certifies that `HasArcCollars` is satisfiable.
-/

open Metric Set unitInterval

namespace Schoenflies

variable {D P K K' : Set Plane}

/-! ### The collar of a compact subarc, as data

Blueprint Lemma 1.8 (b). `nbhd` is the neighbourhood `N`, `left` and `right` are the two tracks
`N_L, N_R`. The prescribed open set of the blueprint is `D`, which is all this development ever
prescribes.

Two clauses of the blueprint are dropped because nothing here uses them: that the tracks are
open and that they are disjoint. Two are kept and are essential: that each track is *connected*
— that is the whole point of a collar, and it is what ties the local picture at one point of the
arc to the local picture at another — and that every point of the subarc is in the closure of
both tracks, which is the blueprint's "the two sets `N_L, N_R` are the two local sides of the
curve" in the form `StripLocal.lean` proves it for a closed polygon. -/

/-- A **two-sided collar** of the compact subarc `K` of `P`, inside the region `D`: an open
neighbourhood `nbhd` of `K` contained in `D`, whose complement of `P` splits into two connected
tracks, each of which approaches every point of `K`.

Note that the splitting clause is stated for `nbhd ∖ P` and not for `nbhd ∖ K`: an open
neighbourhood of `K` necessarily contains points of `P` beyond the ends of `K`, and it is the
*whole* of `P` that has to be removed for the tracks to lie in `D ∖ P`. That is how the
blueprint states it too. -/
structure ArcCollar (D P K : Set Plane) where
  /-- the neighbourhood `N` of the subarc -/
  nbhd : Set Plane
  /-- the left track `N_L` -/
  left : Set Plane
  /-- the right track `N_R` -/
  right : Set Plane
  isOpen_nbhd : IsOpen nbhd
  subset_nbhd : K ⊆ nbhd
  nbhd_subset : nbhd ⊆ D
  nbhd_diff : nbhd \ P = left ∪ right
  isConnected_left : IsConnected left
  isConnected_right : IsConnected right
  subset_closure_left : K ⊆ closure left
  subset_closure_right : K ⊆ closure right

/-! ### The clopen step -/

/-! ### Lemma "At most two sides" -/

/-! ### The collar hypothesis is not vacuous: a straight crosscut

The collar of a *straight* crosscut is a rectangle, and the free-standing frame toolkit of
`Schoenflies/Strip.lean` — `coordAlong`, `coordAcross`, `strip`, `isOpen_strip`, `convex_strip`,
`dist_foot`, `frame_decomp` — builds it directly, with no cyclic vertex family in sight. So
`HasArcCollars` is discharged outright in the simplest crosscut configuration, and
`segment_crosscut_at_most_two` below is a hypothesis-free instance of the lemma.

This is the shape a general discharger has to reproduce along a chain of edges: it is exactly
the blueprint's edge block, and what is missing is the vertex disks between consecutive blocks
and the end cross-sections. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.ArcCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Two-sided collars along a simple polygonal arc

`Schoenflies/CrosscutAtMostTwo.lean` proves Lemma "At most two sides" assuming
`Schoenflies.HasArcCollars`: every compact piece of `D ∩ P` has a two-sided collar inside `D`.
This module discharges that hypothesis for a polygonal arc presented by its vertex list.

## The route: a linear chain, not a cyclic one

`Schoenflies/Strip.lean` builds the collar of blueprint Lemma 1.8 for a `ClosedPolygon`, whose
vertex family is indexed by `ZMod (m + 3)`. The apparatus is redone here on a *linear* index —
route (A) of the three the blueprint's arc case admits. Closing the arc into a polygon (route
(B)) was rejected: it needs a return path from one end of the arc back to the other meeting the
arc only at its ends, and producing one is the two-sided collar of the arc all over again.

Two things change from the cyclic case, and both make the arc case *easier*.

* **There are no sectors at the two extreme vertices.** An edge block already stops short of
  both of its endpoints by the trim `lam`, so the collar of the whole chain of blocks is an open
  neighbourhood of the arc minus two small end caps — which is all that is wanted, because the
  compact piece `K` sits at positive distance from the two endpoints of a crosscut (they are
  outside `D` and `K` is inside).
* **The neighbourhood is open by construction.** The collar of a closed polygon has to contain
  the curve, so `StripData.nbhd` is a union of open sets *plus the carrier*, and
  `StripData.nbhd_eq` is needed to see that it is open. Here `nbhd` is defined outright as the
  union of the vertex balls and the edge tubes; it contains the arc only away from its two ends,
  and there is nothing to prove.

What does **not** change is the germ argument at a corner: `Plane.germs_split'` is applied
exactly as in the cyclic case, with the incoming ray at vertex `i + 1` written `A.back i` and
the outgoing one `A.tang (i + 1)`.

## The one thing left open

`PolyArc` is a *presentation*: a simple polygonal arc given by its vertex list, exactly as
`ClosedPolygon` presents a simple closed polygonal curve. Everything is proved for a `PolyArc`,
and `Schoenflies.polyArc_crosscut_at_most_two` is Lemma "At most two sides" for one with no
hypothesis left standing at all. What is *not* proved is the converse presentation statement:
that a set which happens to be a simple polygonal arc is the carrier of some `PolyArc`. That is
the arc analogue of `Schoenflies.exists_closedPolygon`, which `Schoenflies/Realization.lean`
proves for a Jordan curve; it is normalisation, not geometry.
`Schoenflies.hasArcCollars` therefore carries it as the hypothesis
`Schoenflies.IsPolyArcCarrier`. See the note at the end of the file for the route.

The presentation is checked in both other directions, so neither the structure nor the
hypothesis is vacuous or accidentally false: `Schoenflies.PolyArc.isArcBetween_carrier` and
`Schoenflies.PolyArc.isPolygonal_carrier` say the carrier of a `PolyArc` *is* a simple polygonal
arc, and `Schoenflies.isPolyArcCarrier_segment` exhibits one.

## Blueprint

* `Schoenflies.PolyArc` — a simple polygonal arc presented by its vertex list; the arc analogue
  of `Schoenflies.ClosedPolygon`.
* `Schoenflies.ArcStrip` — the constants of blueprint Lemma 1.8 (b), as a structure: the cone
  radius `R`, the trim `lam`, the half-width `rho`, and the separations they satisfy. The arc
  analogue of `Schoenflies.StripData`, with the two clauses that make the collar fit inside the
  prescribed region and clear of the two endpoints.
* `Schoenflies.ArcStrip.nbhd`, `.sideL`, `.sideR` — the collar `N` and its two tracks `N_L`,
  `N_R` of Lemma 1.8 (b).
* `Schoenflies.ArcStrip.nbhd_diff_carrier`, `.isConnected_sideL`, `.isConnected_sideR`,
  `.sideL_disjoint_sideR`, `.subset_closure_sideL`, `.subset_closure_sideR` — the clauses of
  Lemma 1.8 (b).
* `Schoenflies.exists_arcStrip` — the constants exist. The arc analogue of
  `Schoenflies.exists_stripData_subset`.
* `Schoenflies.ArcStrip.collar`, `Schoenflies.PolyArc.exists_arcCollar`,
  `Schoenflies.PolyArc.hasArcCollars` — Lemma 1.8 (b) itself, as the interface
  `Schoenflies.ArcCollar` that `Schoenflies/CrosscutAtMostTwo.lean` consumes.
* `Schoenflies.PolyArc.isArcBetween_carrier`, `Schoenflies.PolyArc.isPolygonal_carrier` — the
  carrier of a `PolyArc` is a simple polygonal arc between its two extreme vertices.
* `Schoenflies.polyArc_crosscut_at_most_two`,
  `Schoenflies.polyArc_crosscut_components_exhaust` — Lemma "At most two sides" for a polygonal
  arc presented by a vertex list, with no further assumptions.
* `Schoenflies.hasArcCollars`, `Schoenflies.crosscut_at_most_two_of_polyArc`,
  `Schoenflies.crosscut_components_exhaust_of_polyArc` — the same for a *set* `P` presented by
  `Schoenflies.IsPolyArcCarrier`.
* `Schoenflies.segmentPolyArc`, `Schoenflies.isPolyArcCarrier_segment` — a straight crosscut as
  a `PolyArc`, which recovers `Schoenflies.hasArcCollars_segment` as a special case.
-/

open Metric Set

namespace Schoenflies

open Plane

/-! ## Simple polygonal arcs

A polygonal arc is presented by its vertex list `v 0, …, v (n + 1)`; its edges are the `n + 1`
segments `edge i = [v i, v (i + 1)]` for `i ≤ n`, and its *interior* vertices — the ones that
carry a corner, and hence a sector of the collar — are `v 1, …, v n`.

The vertex function is indexed by all of `ℕ` and asked to be injective outright, rather than
injective on `{0, …, n + 1}`. Nothing past `v (n + 1)` is ever looked at except through
`A.tang i` and `A.len i`, which are only well behaved when `v i ≠ v (i + 1)`; asking for global
injectivity buys that for free and removes an `i ≤ n` side condition from every lemma about the
edge frame. It costs a discharger nothing: a finite vertex list is padded to an injective
sequence by any tail of fresh points. -/

/-- A **simple polygonal arc**, presented by its vertex list. The arc runs from `vertex 0` to
`vertex (n + 1)` along the `n + 1` edges `[vertex i, vertex (i + 1)]`, `i ≤ n`. -/
structure PolyArc (n : ℕ) where
  /-- The vertices, in order along the arc. Only `vertex 0, …, vertex (n + 1)` are on it. -/
  vertex : ℕ → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}
  /-- No redundant vertex: the two edges at an *interior* vertex are not collinear. The two
  extreme vertices carry no condition, because the collar puts no sector there. -/
  corner : ∀ i < n, det (vertex i - vertex (i + 1)) (vertex (i + 2) - vertex (i + 1)) ≠ 0

/-! ### The turned vector of a reversed direction -/

namespace Plane

/-- Turning the reverse of a vector is the reverse of turning it. -/
theorem perp_neg (u : Plane) : perp (-u) = -perp u := by
  ext k; fin_cases k <;> simp [perp]

end Plane

namespace PolyArc

variable {n : ℕ} (A : PolyArc n) (i j : ℕ) (c t s : ℝ)

/-- The length of edge `i`. -/
noncomputable def len : ℝ := ‖A.vertex (i + 1) - A.vertex i‖

/-- The unit tangent of edge `i`, which is also the outgoing ray at `vertex i`. -/
noncomputable def tang : Plane := dir (A.vertex (i + 1) - A.vertex i)

/-- The incoming ray at `vertex (i + 1)`: the direction back along edge `i`. -/
noncomputable def back : Plane := dir (A.vertex i - A.vertex (i + 1))

/-- The point at progress `t` and signed offset `s` in the frame of edge `i`. -/
noncomputable def off : Plane := A.vertex i + t • A.tang i + s • perp (A.tang i)

/-- The point of edge `i` at distance `c` from its initial vertex. -/
noncomputable def pt : Plane := A.off i c 0

/-- Edge `i` of the arc. -/
def edge : Set Plane := segment ℝ (A.vertex i) (A.vertex (i + 1))

/-- The carrier of the arc: the union of its `n + 1` edges. -/
def carrier : Set Plane := ⋃ i, ⋃ (_ : i ≤ n), A.edge i

variable {A i j c t s}

theorem mem_carrier_iff {x : Plane} : x ∈ A.carrier ↔ ∃ i ≤ n, x ∈ A.edge i := by
  simp only [carrier, Set.mem_iUnion, exists_prop]

theorem edge_subset_carrier (hi : i ≤ n) : A.edge i ⊆ A.carrier :=
  fun _ hx => mem_carrier_iff.2 ⟨i, hi, hx⟩

theorem vertex_ne : A.vertex i ≠ A.vertex (i + 1) := fun h => by
  have := A.vertex_inj h; omega

theorem sub_ne_zero_of_edge : A.vertex (i + 1) - A.vertex i ≠ 0 :=
  sub_ne_zero.2 (vertex_ne (A := A) (i := i)).symm

theorem len_pos : 0 < A.len i := norm_pos_iff.2 sub_ne_zero_of_edge

theorem isDirection_tang : IsDirection (A.tang i) := isDirection_dir sub_ne_zero_of_edge

theorem len_smul_tang : (A.len i) • A.tang i = A.vertex (i + 1) - A.vertex i := by
  rw [tang, dir, smul_smul, len, mul_inv_cancel₀ (norm_ne_zero_iff.2 sub_ne_zero_of_edge),
    one_smul]

theorem vertex_succ_eq : A.vertex (i + 1) = A.vertex i + (A.len i) • A.tang i := by
  rw [len_smul_tang]; module

/-- The incoming ray at `vertex (i + 1)` is the reverse of the tangent of edge `i`. -/
theorem back_eq : A.back i = -A.tang i := by
  rw [back, tang, dir, dir, norm_sub_rev (A.vertex i) (A.vertex (i + 1))]
  module

theorem isDirection_back : IsDirection (A.back i) := by
  rw [back_eq, IsDirection, norm_neg]; exact isDirection_tang.norm

theorem perp_back : perp (A.back i) = -perp (A.tang i) := by
  rw [back_eq, perp_neg]

/-- The corner condition, read on the two unit rays at an interior vertex. -/
theorem det_rays_ne_zero (hi : i < n) : det (A.back i) (A.tang (i + 1)) ≠ 0 := by
  obtain ⟨c₁, hc₁, h₁⟩ := dir_eq_smul (sub_ne_zero.2 (vertex_ne (A := A) (i := i)))
  obtain ⟨c₂, hc₂, h₂⟩ := dir_eq_smul (sub_ne_zero_of_edge (A := A) (i := i + 1))
  rw [back, tang, h₁, h₂, det_smul_left, det_smul_right]
  exact mul_ne_zero hc₁.ne' (mul_ne_zero hc₂.ne' (A.corner i hi))

/-! ### The edge frame -/

theorem off_zero_zero : A.off i 0 0 = A.vertex i := by rw [off]; module

theorem pt_zero : A.pt i 0 = A.vertex i := off_zero_zero

theorem pt_eq : A.pt i c = A.vertex i + c • A.tang i := by rw [pt, off, zero_smul, add_zero]

theorem pt_len : A.pt i (A.len i) = A.vertex (i + 1) := by
  rw [pt_eq, ← vertex_succ_eq]

theorem off_sub_vertex : A.off i t s - A.vertex i = t • A.tang i + s • perp (A.tang i) := by
  rw [off]; module

theorem pt_sub_vertex : A.pt i c - A.vertex i = c • A.tang i := by
  rw [pt, off_sub_vertex, zero_smul, add_zero]

theorem dist_pt_vertex : dist (A.pt i c) (A.vertex i) = |c| := by
  rw [dist_eq_norm, pt_sub_vertex, norm_smul, Real.norm_eq_abs, isDirection_tang.norm, mul_one]

theorem off_sub_vertex_succ :
    A.off i t s - A.vertex (i + 1) = (t - A.len i) • A.tang i + s • perp (A.tang i) := by
  rw [off, vertex_succ_eq]; module

/-- The same difference written in the frame of the incoming ray, which is the form the germ
argument at `vertex (i + 1)` consumes. -/
theorem off_sub_vertex_succ_ray :
    A.off i t s - A.vertex (i + 1) =
      (A.len i - t) • A.back i - s • perp (A.back i) := by
  rw [off_sub_vertex_succ, perp_back, back_eq]
  module

theorem dist_off_vertex_le : dist (A.off i t s) (A.vertex i) ≤ |t| + |s| := by
  rw [dist_eq_norm, off_sub_vertex]
  calc ‖t • A.tang i + s • perp (A.tang i)‖ ≤ ‖t • A.tang i‖ + ‖s • perp (A.tang i)‖ :=
        norm_add_le _ _
    _ = |t| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

theorem dist_off_vertex_succ_le :
    dist (A.off i t s) (A.vertex (i + 1)) ≤ |t - A.len i| + |s| := by
  rw [dist_eq_norm, off_sub_vertex_succ]
  calc ‖(t - A.len i) • A.tang i + s • perp (A.tang i)‖
      ≤ ‖(t - A.len i) • A.tang i‖ + ‖s • perp (A.tang i)‖ := norm_add_le _ _
    _ = |t - A.len i| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

theorem dist_pt_vertex_succ : dist (A.pt i c) (A.vertex (i + 1)) = |c - A.len i| := by
  rw [pt, dist_eq_norm, off_sub_vertex_succ, zero_smul, add_zero, norm_smul, Real.norm_eq_abs,
    isDirection_tang.norm, mul_one]

theorem dist_off_pt : dist (A.off i t s) (A.pt i t) = |s| := by
  rw [pt, dist_eq_norm, show A.off i t s - A.off i t 0 = s • perp (A.tang i) by
    rw [off, off]; module, norm_smul, Real.norm_eq_abs, norm_perp, isDirection_tang.norm,
    mul_one]

@[simp] theorem coordAlong_off : coordAlong (A.vertex i) (A.tang i) (A.off i t s) = t :=
  coordAlong_param isDirection_tang _ _ _

@[simp] theorem coordAcross_off : coordAcross (A.vertex i) (A.tang i) (A.off i t s) = s :=
  coordAcross_param isDirection_tang _ _ _

/-- Every point is the point of some frame position, so the two coordinates identify it. -/
theorem off_coord (A : PolyArc n) (i : ℕ) (x : Plane) :
    x = A.off i (coordAlong (A.vertex i) (A.tang i) x) (coordAcross (A.vertex i) (A.tang i) x) :=
  frame_decomp isDirection_tang _ _

/-! ### Edges as sets -/

theorem mem_edge_iff {x : Plane} :
    x ∈ A.edge i ↔ ∃ c ∈ Set.Icc (0 : ℝ) (A.len i), x = A.pt i c := by
  rw [edge, segment_eq_image' ℝ]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    refine ⟨θ * A.len i, ⟨mul_nonneg hθ0 len_pos.le, ?_⟩, ?_⟩
    · nlinarith [len_pos (A := A) (i := i)]
    · rw [pt_eq, ← len_smul_tang]
      simp [smul_smul]
  · rintro ⟨c, ⟨hc0, hc1⟩, rfl⟩
    refine ⟨c / A.len i, ⟨div_nonneg hc0 len_pos.le, ?_⟩, ?_⟩
    · rw [div_le_one len_pos]; exact hc1
    · rw [pt_eq, ← len_smul_tang]
      simp [smul_smul, div_mul_cancel₀ _ (len_pos (A := A) (i := i)).ne']

theorem pt_mem_edge (hc : c ∈ Set.Icc (0 : ℝ) (A.len i)) : A.pt i c ∈ A.edge i :=
  mem_edge_iff.2 ⟨c, hc, rfl⟩

theorem vertex_mem_edge : A.vertex i ∈ A.edge i := by
  rw [← pt_zero]; exact pt_mem_edge ⟨le_refl _, len_pos.le⟩

theorem vertex_mem_carrier (hi : i ≤ n) : A.vertex i ∈ A.carrier :=
  edge_subset_carrier hi vertex_mem_edge

/-- A point of edge `i`, seen from the vertex it leaves, is a nonnegative multiple of the
outgoing ray. -/
theorem mem_edge_sub {x : Plane} (hx : x ∈ A.edge i) :
    ∃ c : ℝ, 0 ≤ c ∧ x - A.vertex i = c • A.tang i := by
  obtain ⟨c, ⟨hc0, _⟩, rfl⟩ := mem_edge_iff.1 hx
  exact ⟨c, hc0, pt_sub_vertex⟩

/-- A point of edge `i`, seen from the vertex it arrives at, is a nonnegative multiple of the
incoming ray there. -/
theorem mem_edge_sub_succ {x : Plane} (hx : x ∈ A.edge i) :
    ∃ c : ℝ, 0 ≤ c ∧ x - A.vertex (i + 1) = c • A.back i := by
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := mem_edge_iff.1 hx
  refine ⟨A.len i - c, by linarith, ?_⟩
  rw [pt, off_sub_vertex_succ, back_eq, zero_smul, add_zero]
  module

/-- Walking back along the incoming ray from `vertex (i + 1)` traverses edge `i`. -/
theorem vertex_add_smul_back : A.vertex (i + 1) + c • A.back i = A.pt i (A.len i - c) := by
  rw [pt_eq, back_eq, vertex_succ_eq]
  module

theorem mem_edge_of_smul_back (hc0 : 0 ≤ c) (hc1 : c ≤ A.len i) :
    A.vertex (i + 1) + c • A.back i ∈ A.edge i := by
  rw [vertex_add_smul_back]
  exact pt_mem_edge ⟨by linarith, by linarith⟩

theorem mem_edge_of_smul_tang (hc0 : 0 ≤ c) (hc1 : c ≤ A.len i) :
    A.vertex i + c • A.tang i ∈ A.edge i := by
  rw [← pt_eq]; exact pt_mem_edge ⟨hc0, hc1⟩

/-! ### What simplicity gives -/

/-! ### The four germs at an interior vertex

`Plane.germs_split'` applied at the interior vertex `v (i + 1)`, whose incoming ray is
`A.back i` and whose outgoing ray is `A.tang (i + 1)`. The smallness of the offset is left as a
hypothesis; the block versions supply it from the `germ` field of an `ArcStrip`. -/

theorem off_sub_mem_arcL_start (hi : i < n) (hs : 0 < s)
    (hsm : s * |inner ℝ (A.back i) (A.tang (i + 1))| <
      t * |det (A.back i) (A.tang (i + 1))|) :
    A.off (i + 1) t s - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := by
  rw [off_sub_vertex]
  exact (germs_split' (det_rays_ne_zero hi) hs hsm).1.2

theorem off_sub_mem_arcR_start (hi : i < n) (hs : s < 0)
    (hsm : (-s) * |inner ℝ (A.back i) (A.tang (i + 1))| <
      t * |det (A.back i) (A.tang (i + 1))|) :
    A.off (i + 1) t s - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := by
  have h : A.off (i + 1) t s - A.vertex (i + 1) =
      t • A.tang (i + 1) - (-s) • perp (A.tang (i + 1)) := by
    rw [off_sub_vertex]; module
  rw [h]
  exact (germs_split' (det_rays_ne_zero hi) (by linarith) hsm).2.2

theorem off_sub_mem_arcL_finish (hi : i < n) (hs : 0 < s)
    (hsm : s * |inner ℝ (A.back i) (A.tang (i + 1))| <
      (A.len i - t) * |det (A.back i) (A.tang (i + 1))|) :
    A.off i t s - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := by
  rw [off_sub_vertex_succ_ray]
  exact (germs_split' (det_rays_ne_zero hi) hs hsm).1.1

theorem off_sub_mem_arcR_finish (hi : i < n) (hs : s < 0)
    (hsm : (-s) * |inner ℝ (A.back i) (A.tang (i + 1))| <
      (A.len i - t) * |det (A.back i) (A.tang (i + 1))|) :
    A.off i t s - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := by
  have h : A.off i t s - A.vertex (i + 1) =
      (A.len i - t) • A.back i + (-s) • perp (A.back i) := by
    rw [off_sub_vertex_succ_ray]; module
  rw [h]
  exact (germs_split' (det_rays_ne_zero hi) (by linarith) hsm).2.1

end PolyArc

/-! ## The constants

`ArcStrip` is the arc analogue of `Schoenflies.StripData`: the blueprint's "choose the blocks so
that consecutive ones overlap and nonadjacent closures are disjoint", with every constant named.
Three fields have no counterpart in the closed case, and they are what makes the collar a collar
*of `K` inside `D`*: `ball_subset` and `tube_subset` put every piece inside the prescribed open
set, and `sep_ends` keeps `K` clear of the two ends of the arc, where the collar has no pieces.

`sep_ends` is not a restriction in the intended application: the two endpoints of a crosscut lie
outside `D` and `K` lies inside, so the distance from `K` to either endpoint is positive and `R`
is chosen below it. -/

/-- The constants of the collar of a compact piece `K` of the simple polygonal arc `A`, inside a
prescribed open set `D`. -/
structure ArcStrip {n : ℕ} (A : PolyArc n) (D K : Set Plane) where
  /-- The radius of the vertex sectors. -/
  R : ℝ
  /-- The distance by which an edge block stops short of each endpoint of its edge. -/
  lam : ℝ
  /-- The half-width of an edge block. -/
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_lam : rho < lam
  /-- The sectors reach past the ends of the blocks they have to overlap. -/
  two_lam_lt_R : 2 * lam < R
  /-- The blocks are nonempty, with room to spare at both ends. -/
  four_lam_lt_len : ∀ i ≤ n, 4 * lam < A.len i
  /-- A sector does not run past the far end of an incident edge. -/
  R_le_len : ∀ i ≤ n, R ≤ A.len i
  /-- Distinct vertices are `2R` apart, so distinct sectors are disjoint. -/
  sep_vertex : ∀ i ≤ n + 1, ∀ j ≤ n + 1, i ≠ j → 2 * R ≤ dist (A.vertex i) (A.vertex j)
  /-- A vertex is `2R` away from every nonincident edge. -/
  sep_vertex_edge : ∀ i ≤ n + 1, ∀ j ≤ n, i ≠ j → i ≠ j + 1 →
    ∀ y ∈ A.edge j, 2 * R ≤ dist (A.vertex i) y
  /-- The trimmed edge `i` is `2 * rho` away from every other edge. -/
  sep_trim_edge : ∀ i ≤ n, ∀ j ≤ n, j ≠ i → ∀ c ∈ Set.Icc lam (A.len i - lam),
    ∀ y ∈ A.edge j, 2 * rho ≤ dist (A.pt i c) y
  /-- **The vertex-matching threshold**, at the interior vertices only. -/
  germ : ∀ i < n, rho * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) ≤
    lam * |det (A.back i) (A.tang (i + 1))|
  /-- The sector at an interior vertex is inside the prescribed open set. -/
  ball_subset : ∀ i < n, ball (A.vertex (i + 1)) R ⊆ D
  /-- The block of an edge is inside the prescribed open set: a `rho`-ball about a point of the
  trimmed core is. -/
  tube_subset : ∀ i ≤ n, ∀ c ∈ Set.Icc lam (A.len i - lam), ball (A.pt i c) rho ⊆ D
  /-- The compact piece is inside the arc… -/
  subset_carrier : K ⊆ A.carrier
  /-- …and clear of its two endpoints, where the collar has no pieces. -/
  sep_ends : ∀ x ∈ K, R ≤ dist x (A.vertex 0) ∧ R ≤ dist x (A.vertex (n + 1))

namespace ArcStrip

variable {n : ℕ} {A : PolyArc n} {D K : Set Plane} (S : ArcStrip A D K) {i j k : ℕ} {x : Plane}

theorem lam_pos : 0 < S.lam := lt_trans S.rho_pos S.rho_lt_lam

theorem R_pos : 0 < S.R := by have := S.lam_pos; linarith [S.two_lam_lt_R]

theorem lam_lt_R : S.lam < S.R := by have := S.lam_pos; linarith [S.two_lam_lt_R]

/-! ### The four families of blocks -/

/-- The left block of edge `i`. -/
def blockL (i : ℕ) : Set Plane :=
  strip (A.vertex i) (A.tang i) S.lam (A.len i - S.lam) 0 S.rho

/-- The right block of edge `i`. -/
def blockR (i : ℕ) : Set Plane :=
  strip (A.vertex i) (A.tang i) S.lam (A.len i - S.lam) (-S.rho) 0

/-- The full tube of edge `i`: the trimmed edge thickened by `rho` on both sides. -/
def tube (i : ℕ) : Set Plane :=
  strip (A.vertex i) (A.tang i) S.lam (A.len i - S.lam) (-S.rho) S.rho

/-- The left sector at the interior vertex `vertex (i + 1)`. -/
def sectorL (i : ℕ) : Set Plane :=
  cone (A.vertex (i + 1)) (arcCCW (A.tang (i + 1)) (A.back i)) S.R

/-- The right sector at the interior vertex `vertex (i + 1)`. -/
def sectorR (i : ℕ) : Set Plane :=
  cone (A.vertex (i + 1)) (arcCCW (A.back i) (A.tang (i + 1))) S.R

/-- The `k`-th link of the left chain: the block of edge `0` to start with, and thereafter the
sector at `vertex k` glued to the block of edge `k`. Consecutive links overlap in the block of
the earlier edge, which is what makes the union connected. -/
def chainL (T : ArcStrip A D K) : ℕ → Set Plane
  | 0 => T.blockL 0
  | (k + 1) => T.sectorL k ∪ T.blockL (k + 1)

/-- The `k`-th link of the right chain. -/
def chainR (T : ArcStrip A D K) : ℕ → Set Plane
  | 0 => T.blockR 0
  | (k + 1) => T.sectorR k ∪ T.blockR (k + 1)

/-- The left track of the collar. -/
def sideL : Set Plane := ⋃ k, ⋃ (_ : k ≤ n), S.chainL k

/-- The right track of the collar. -/
def sideR : Set Plane := ⋃ k, ⋃ (_ : k ≤ n), S.chainR k

/-- The collar: the union of the edge tubes and the balls about the interior vertices. Unlike
the closed case it is *not* a neighbourhood of the whole arc — it stops short of the two
endpoints — and it is manifestly open. -/
def nbhd : Set Plane :=
  (⋃ i, ⋃ (_ : i ≤ n), S.tube i) ∪ (⋃ i, ⋃ (_ : i < n), ball (A.vertex (i + 1)) S.R)

theorem mem_blockL_iff : x ∈ S.blockL i ↔
    S.lam < coordAlong (A.vertex i) (A.tang i) x ∧
      coordAlong (A.vertex i) (A.tang i) x < A.len i - S.lam ∧
      0 < coordAcross (A.vertex i) (A.tang i) x ∧
      coordAcross (A.vertex i) (A.tang i) x < S.rho := Iff.rfl

theorem mem_blockR_iff : x ∈ S.blockR i ↔
    S.lam < coordAlong (A.vertex i) (A.tang i) x ∧
      coordAlong (A.vertex i) (A.tang i) x < A.len i - S.lam ∧
      -S.rho < coordAcross (A.vertex i) (A.tang i) x ∧
      coordAcross (A.vertex i) (A.tang i) x < 0 := Iff.rfl

theorem mem_tube_iff : x ∈ S.tube i ↔
    S.lam < coordAlong (A.vertex i) (A.tang i) x ∧
      coordAlong (A.vertex i) (A.tang i) x < A.len i - S.lam ∧
      -S.rho < coordAcross (A.vertex i) (A.tang i) x ∧
      coordAcross (A.vertex i) (A.tang i) x < S.rho := Iff.rfl

theorem mem_blockL_off {t s : ℝ} : A.off i t s ∈ S.blockL i ↔
    S.lam < t ∧ t < A.len i - S.lam ∧ 0 < s ∧ s < S.rho := by
  rw [mem_blockL_iff, PolyArc.coordAlong_off, PolyArc.coordAcross_off]

theorem mem_blockR_off {t s : ℝ} : A.off i t s ∈ S.blockR i ↔
    S.lam < t ∧ t < A.len i - S.lam ∧ -S.rho < s ∧ s < 0 := by
  rw [mem_blockR_iff, PolyArc.coordAlong_off, PolyArc.coordAcross_off]

theorem mem_tube_off {t s : ℝ} : A.off i t s ∈ S.tube i ↔
    S.lam < t ∧ t < A.len i - S.lam ∧ -S.rho < s ∧ s < S.rho := by
  rw [mem_tube_iff, PolyArc.coordAlong_off, PolyArc.coordAcross_off]

theorem isOpen_tube : IsOpen (S.tube i) := isOpen_strip _ _ _ _ _ _

theorem convex_blockL : Convex ℝ (S.blockL i) := convex_strip _ _ _ _ _ _
theorem convex_blockR : Convex ℝ (S.blockR i) := convex_strip _ _ _ _ _ _

theorem isConnected_sectorL (hi : i < n) : IsConnected (S.sectorL i) :=
  isConnected_cone_arcCCW _
    (by rw [det_comm]; exact neg_ne_zero.2 (PolyArc.det_rays_ne_zero hi)) S.R_pos

theorem isConnected_sectorR (hi : i < n) : IsConnected (S.sectorR i) :=
  isConnected_cone_arcCCW _ (PolyArc.det_rays_ne_zero hi) S.R_pos

theorem blockL_subset_tube : S.blockL i ⊆ S.tube i := fun _ hy =>
  ⟨hy.1, hy.2.1, by linarith [S.rho_pos, hy.2.2.1], hy.2.2.2⟩

theorem blockR_subset_tube : S.blockR i ⊆ S.tube i := fun _ hy =>
  ⟨hy.1, hy.2.1, hy.2.2.1, by linarith [S.rho_pos, hy.2.2.2]⟩

theorem sectorL_subset_ball : S.sectorL i ⊆ ball (A.vertex (i + 1)) S.R := cone_subset_ball
theorem sectorR_subset_ball : S.sectorR i ⊆ ball (A.vertex (i + 1)) S.R := cone_subset_ball

/-- The foot of the perpendicular from a point of a tube lies on the trimmed edge, within `rho`
of the point. -/
theorem exists_foot (h : x ∈ S.tube i) :
    ∃ c ∈ Set.Icc S.lam (A.len i - S.lam), dist x (A.pt i c) < S.rho := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_tube_iff.1 h
  refine ⟨coordAlong (A.vertex i) (A.tang i) x, ⟨h1.le, h2.le⟩, ?_⟩
  rw [PolyArc.pt_eq, dist_foot PolyArc.isDirection_tang, abs_lt]
  exact ⟨h3, h4⟩

/-! ### The germ argument at an interior vertex -/

/-- The threshold hypothesis, specialised to a point of a block. -/
theorem germ_ineq (hi : i < n) {t s : ℝ} (ht : S.lam < t) (hs0 : 0 < s) (hs : s < S.rho) :
    s * |inner ℝ (A.back i) (A.tang (i + 1))| < t * |det (A.back i) (A.tang (i + 1))| := by
  have hd : 0 < |det (A.back i) (A.tang (i + 1))| := abs_pos.2 (PolyArc.det_rays_ne_zero hi)
  have habs : (0 : ℝ) ≤ |inner ℝ (A.back i) (A.tang (i + 1))| := abs_nonneg _
  have h1 : s * |inner ℝ (A.back i) (A.tang (i + 1))| ≤
      s * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) := by nlinarith
  have h2 : s * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) <
      S.rho * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) := by nlinarith
  have h3 := S.germ i hi
  nlinarith

/-- A point of the left block of edge `i + 1`, seen from the interior vertex it leaves, is in the
left arc there. -/
theorem blockL_sub_mem_arcL_start (hi : i < n) (h : x ∈ S.blockL (i + 1)) :
    x - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_blockL_iff.1 h
  rw [PolyArc.off_coord A (i + 1) x]
  exact PolyArc.off_sub_mem_arcL_start hi h3 (S.germ_ineq hi h1 h3 h4)

/-- A point of the left block of edge `i`, seen from the interior vertex it arrives at. -/
theorem blockL_sub_mem_arcL_finish (hi : i < n) (h : x ∈ S.blockL i) :
    x - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_blockL_iff.1 h
  rw [PolyArc.off_coord A i x]
  exact PolyArc.off_sub_mem_arcL_finish hi h3
    (S.germ_ineq hi (by linarith) h3 h4)

theorem blockR_sub_mem_arcR_start (hi : i < n) (h : x ∈ S.blockR (i + 1)) :
    x - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_blockR_iff.1 h
  rw [PolyArc.off_coord A (i + 1) x]
  exact PolyArc.off_sub_mem_arcR_start hi h4
    (S.germ_ineq hi h1 (by linarith) (by linarith))

theorem blockR_sub_mem_arcR_finish (hi : i < n) (h : x ∈ S.blockR i) :
    x - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_blockR_iff.1 h
  rw [PolyArc.off_coord A i x]
  exact PolyArc.off_sub_mem_arcR_finish hi h4
    (S.germ_ineq hi (by linarith) (by linarith) (by linarith))

end ArcStrip

/-! ### Two shapes of bounded union

Both tracks and the collar are unions over an initial segment of `ℕ`. These two rewrites are the
only interface to that indexing. -/

namespace ArcStrip

variable {n : ℕ} {A : PolyArc n} {D K : Set Plane} (S : ArcStrip A D K) {i j k : ℕ} {x : Plane}

/-! ### Nonadjacent blocks are disjoint

Every step is one of the separation hypotheses of `ArcStrip` against one of the two containments
`exists_foot` and `sectorL_subset_ball`. -/

/-- A tube misses every edge but its own. -/
theorem tube_notMem_edge (hi : i ≤ n) (hj : j ≤ n) (hji : j ≠ i) (h : x ∈ S.tube i) :
    x ∉ A.edge j := by
  intro hx
  obtain ⟨c, hc, hd⟩ := S.exists_foot h
  have := S.sep_trim_edge i hi j hj hji c hc x hx
  rw [dist_comm] at hd
  linarith [S.rho_pos]

/-- A block misses its own edge, because its points have nonzero offset. -/
theorem block_notMem_own_edge (h : x ∈ S.blockL i ∪ S.blockR i) : x ∉ A.edge i := by
  intro hx
  obtain ⟨c, -, rfl⟩ := PolyArc.mem_edge_iff.1 hx
  have hzero : coordAcross (A.vertex i) (A.tang i) (A.pt i c) = 0 := by
    rw [PolyArc.pt]; exact PolyArc.coordAcross_off
  rcases h with h | h
  · have hpos := (S.mem_blockL_iff.1 h).2.2.1
    rw [hzero] at hpos; exact lt_irrefl 0 hpos
  · have hneg := (S.mem_blockR_iff.1 h).2.2.2
    rw [hzero] at hneg; exact lt_irrefl 0 hneg

theorem block_notMem_carrier (hi : i ≤ n) (h : x ∈ S.blockL i ∪ S.blockR i) : x ∉ A.carrier := by
  intro hx
  obtain ⟨j, hj, hxj⟩ := PolyArc.mem_carrier_iff.1 hx
  by_cases hij : j = i
  · exact S.block_notMem_own_edge h (hij ▸ hxj)
  · have htube : x ∈ S.tube i :=
      h.elim (fun h => S.blockL_subset_tube h) (fun h => S.blockR_subset_tube h)
    exact S.tube_notMem_edge hi hj hij htube hxj

/-- A sector misses every edge that is not incident to its vertex. -/
theorem sector_notMem_far_edge (hi : i ≤ n + 1) (hj : j ≤ n) (h1 : i ≠ j) (h2 : i ≠ j + 1)
    (h : x ∈ ball (A.vertex i) S.R) : x ∉ A.edge j := by
  intro hx
  have := S.sep_vertex_edge i hi j hj h1 h2 x hx
  rw [mem_ball, dist_comm] at h
  linarith [S.R_pos]

/-- A sector misses the two edges incident to its vertex: their points lie on the two bounding
rays, and the arcs are open. -/
theorem sectorL_notMem_carrier (hi : i < n) (h : x ∈ S.sectorL i) : x ∉ A.carrier := by
  intro hx
  obtain ⟨j, hj, hxj⟩ := PolyArc.mem_carrier_iff.1 hx
  by_cases hji : j = i
  · rw [hji] at hxj
    obtain ⟨c, hc, he⟩ := PolyArc.mem_edge_sub_succ hxj
    exact ((notMem_arcCCW_smul (A.back i) (A.tang (i + 1)) hc).2) (he ▸ h.1)
  by_cases hjs : j = i + 1
  · rw [hjs] at hxj
    obtain ⟨c, hc, he⟩ := PolyArc.mem_edge_sub hxj
    exact ((notMem_arcCCW_smul (A.tang (i + 1)) (A.back i) hc).1) (he ▸ h.1)
  · exact S.sector_notMem_far_edge (by omega) hj (fun he => hjs he.symm)
      (fun he => hji (by omega)) h.2 hxj

theorem sectorR_notMem_carrier (hi : i < n) (h : x ∈ S.sectorR i) : x ∉ A.carrier := by
  intro hx
  obtain ⟨j, hj, hxj⟩ := PolyArc.mem_carrier_iff.1 hx
  by_cases hji : j = i
  · rw [hji] at hxj
    obtain ⟨c, hc, he⟩ := PolyArc.mem_edge_sub_succ hxj
    exact ((notMem_arcCCW_smul (A.back i) (A.tang (i + 1)) hc).1) (he ▸ h.1)
  by_cases hjs : j = i + 1
  · rw [hjs] at hxj
    obtain ⟨c, hc, he⟩ := PolyArc.mem_edge_sub hxj
    exact ((notMem_arcCCW_smul (A.tang (i + 1)) (A.back i) hc).2) (he ▸ h.1)
  · exact S.sector_notMem_far_edge (by omega) hj (fun he => hjs he.symm)
      (fun he => hji (by omega)) h.2 hxj

/-! ### The two tracks, as sets -/

theorem blockL_subset_chainL (k : ℕ) : S.blockL k ⊆ S.chainL k := by
  cases k with
  | zero => exact subset_rfl
  | succ k => exact subset_union_right

theorem blockR_subset_chainR (k : ℕ) : S.blockR k ⊆ S.chainR k := by
  cases k with
  | zero => exact subset_rfl
  | succ k => exact subset_union_right

theorem mem_sideL_iff :
    x ∈ S.sideL ↔ (∃ i ≤ n, x ∈ S.blockL i) ∨ (∃ i < n, x ∈ S.sectorL i) := by
  rw [sideL, mem_iUnion_le_nat]
  constructor
  · rintro ⟨k, hk, hxk⟩
    cases k with
    | zero => exact Or.inl ⟨0, Nat.zero_le n, hxk⟩
    | succ k =>
        rcases hxk with h | h
        · exact Or.inr ⟨k, by omega, h⟩
        · exact Or.inl ⟨k + 1, hk, h⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, hi, S.blockL_subset_chainL i h⟩
    · exact ⟨i + 1, by omega, Or.inl h⟩

theorem mem_sideR_iff :
    x ∈ S.sideR ↔ (∃ i ≤ n, x ∈ S.blockR i) ∨ (∃ i < n, x ∈ S.sectorR i) := by
  rw [sideR, mem_iUnion_le_nat]
  constructor
  · rintro ⟨k, hk, hxk⟩
    cases k with
    | zero => exact Or.inl ⟨0, Nat.zero_le n, hxk⟩
    | succ k =>
        rcases hxk with h | h
        · exact Or.inr ⟨k, by omega, h⟩
        · exact Or.inl ⟨k + 1, hk, h⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, hi, S.blockR_subset_chainR i h⟩
    · exact ⟨i + 1, by omega, Or.inl h⟩

theorem blockL_subset_sideL (hi : i ≤ n) : S.blockL i ⊆ S.sideL :=
  fun _ h => S.mem_sideL_iff.2 (Or.inl ⟨i, hi, h⟩)

theorem blockR_subset_sideR (hi : i ≤ n) : S.blockR i ⊆ S.sideR :=
  fun _ h => S.mem_sideR_iff.2 (Or.inl ⟨i, hi, h⟩)

theorem sectorL_subset_sideL (hi : i < n) : S.sectorL i ⊆ S.sideL :=
  fun _ h => S.mem_sideL_iff.2 (Or.inr ⟨i, hi, h⟩)

theorem sectorR_subset_sideR (hi : i < n) : S.sectorR i ⊆ S.sideR :=
  fun _ h => S.mem_sideR_iff.2 (Or.inr ⟨i, hi, h⟩)

theorem sideL_disjoint_carrier : Disjoint S.sideL A.carrier := by
  rw [Set.disjoint_left]
  intro y hy hc
  rcases S.mem_sideL_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact S.block_notMem_carrier hi (Or.inl h) hc
  · exact S.sectorL_notMem_carrier hi h hc

theorem sideR_disjoint_carrier : Disjoint S.sideR A.carrier := by
  rw [Set.disjoint_left]
  intro y hy hc
  rcases S.mem_sideR_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact S.block_notMem_carrier hi (Or.inr h) hc
  · exact S.sectorR_notMem_carrier hi h hc

theorem sideL_subset_nbhd : S.sideL ⊆ S.nbhd := by
  intro y hy
  rcases S.mem_sideL_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact Or.inl (mem_iUnion_le_nat.2 ⟨i, hi, S.blockL_subset_tube h⟩)
  · exact Or.inr (mem_iUnion_lt_nat.2 ⟨i, hi, S.sectorL_subset_ball h⟩)

theorem sideR_subset_nbhd : S.sideR ⊆ S.nbhd := by
  intro y hy
  rcases S.mem_sideR_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact Or.inl (mem_iUnion_le_nat.2 ⟨i, hi, S.blockR_subset_tube h⟩)
  · exact Or.inr (mem_iUnion_lt_nat.2 ⟨i, hi, S.sectorR_subset_ball h⟩)

/-! ### The collar minus the arc is exactly the two tracks -/

/-- **A vertex ball minus the arc is covered by the two sectors at that vertex.** A point of the
ball off the arc points in some direction from the vertex; that direction is either one of the
two incident rays — and then the point is *on* the incident edge, because `R_le_len` says the
sector does not run past the far end — or on one of the two arcs, and then the point is in the
corresponding sector. -/
theorem ball_diff_carrier_subset (hi : i < n) :
    ball (A.vertex (i + 1)) S.R \ A.carrier ⊆ S.sectorL i ∪ S.sectorR i := by
  rintro y ⟨hy, hyc⟩
  have hne : y - A.vertex (i + 1) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hyc (h ▸ PolyArc.vertex_mem_carrier (i := i + 1) (by omega))
  rcases mem_ray_or_mem_arcCCW' (PolyArc.det_rays_ne_zero hi) hne with
    ⟨c, hc, hcy⟩ | ⟨c, hc, hcy⟩ | harc | harc
  · -- Back along the incoming edge: the point lies on edge `i`.
    refine absurd ?_ hyc
    have hd : dist y (A.vertex (i + 1)) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        (PolyArc.isDirection_back (A := A) (i := i)).norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = A.vertex (i + 1) + c • A.back i := by rw [← hcy]; module
    rw [hy']
    exact PolyArc.edge_subset_carrier (by omega)
      (PolyArc.mem_edge_of_smul_back hc.le (le_trans hy.le (S.R_le_len i (by omega))))
  · -- Out along the outgoing edge: the point lies on edge `i + 1`.
    refine absurd ?_ hyc
    have hd : dist y (A.vertex (i + 1)) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        (PolyArc.isDirection_tang (A := A) (i := i + 1)).norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = A.vertex (i + 1) + c • A.tang (i + 1) := by rw [← hcy]; module
    rw [hy']
    exact PolyArc.edge_subset_carrier (by omega)
      (PolyArc.mem_edge_of_smul_tang hc.le (le_trans hy.le (S.R_le_len (i + 1) (by omega))))
  · exact Or.inr ⟨harc, hy⟩
  · exact Or.inl ⟨harc, hy⟩

/-- **A tube minus the arc is its two blocks.** -/
theorem tube_diff_carrier_subset (hi : i ≤ n) :
    S.tube i \ A.carrier ⊆ S.blockL i ∪ S.blockR i := by
  rintro y ⟨⟨h1, h2, h3, h4⟩, hyc⟩
  rcases lt_trichotomy (coordAcross (A.vertex i) (A.tang i) y) 0 with h | h | h
  · exact Or.inr (S.mem_blockR_iff.2 ⟨h1, h2, h3, h⟩)
  · refine absurd ?_ hyc
    have hy0 : y = A.pt i (coordAlong (A.vertex i) (A.tang i) y) := by
      rw [PolyArc.pt, ← h]; exact PolyArc.off_coord A i y
    rw [hy0]
    exact PolyArc.edge_subset_carrier hi (PolyArc.pt_mem_edge
      ⟨by linarith [S.lam_pos], by linarith [S.lam_pos]⟩)
  · exact Or.inl (S.mem_blockL_iff.2 ⟨h1, h2, h, h4⟩)

/-- **Lemma 1.8 (b), the set equality.** Removing the arc from the collar leaves exactly the two
labelled tracks. -/
theorem nbhd_diff_carrier : S.nbhd \ A.carrier = S.sideL ∪ S.sideR := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hy, hyc⟩
    rcases hy with hy | hy
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion_le_nat.1 hy
      rcases S.tube_diff_carrier_subset hi ⟨hyi, hyc⟩ with h | h
      · exact Or.inl (S.blockL_subset_sideL hi h)
      · exact Or.inr (S.blockR_subset_sideR hi h)
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion_lt_nat.1 hy
      rcases S.ball_diff_carrier_subset hi ⟨hyi, hyc⟩ with h | h
      · exact Or.inl (S.sectorL_subset_sideL hi h)
      · exact Or.inr (S.sectorR_subset_sideR hi h)
  · rintro y (hy | hy)
    · exact ⟨S.sideL_subset_nbhd hy, fun hc => Set.disjoint_left.1 S.sideL_disjoint_carrier hy hc⟩
    · exact ⟨S.sideR_subset_nbhd hy, fun hc => Set.disjoint_left.1 S.sideR_disjoint_carrier hy hc⟩

theorem isOpen_nbhd : IsOpen S.nbhd :=
  (isOpen_iUnion fun _ => isOpen_iUnion fun _ => S.isOpen_tube).union
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball)

/-- **The collar is inside the prescribed open set.** -/
theorem nbhd_subset : S.nbhd ⊆ D := by
  rintro y (hy | hy)
  · obtain ⟨i, hi, hyi⟩ := mem_iUnion_le_nat.1 hy
    obtain ⟨c, hc, hd⟩ := S.exists_foot hyi
    exact S.tube_subset i hi c hc (mem_ball.2 hd)
  · obtain ⟨i, hi, hyi⟩ := mem_iUnion_lt_nat.1 hy
    exact S.ball_subset i hi hyi

end ArcStrip

/-! ## Chaining a linear family

The union of the left pieces is connected because consecutive pieces overlap. Unlike the cyclic
case there is no closing overlap to discard: the chain `0, 1, …, N` is exactly the spanning tree
of the overlap graph. -/

namespace ArcStrip

variable {n : ℕ} {A : PolyArc n} {D K : Set Plane} (S : ArcStrip A D K) {i j k : ℕ} {x : Plane}

/-! ### The overlaps

The blueprint's "consecutive edge and vertex blocks overlap in a nonempty labelled half-strip".
Both witnesses sit at across-coordinate `rho / 2`, at along-coordinate `3 lam / 2` from the
interior vertex in question. -/

theorem lam_lt_three_halves_lam : S.lam < 3 * S.lam / 2 := by have := S.lam_pos; linarith

theorem three_halves_lam_lt (hi : i ≤ n) : 3 * S.lam / 2 < A.len i - S.lam := by
  have := S.lam_pos
  have := S.four_lam_lt_len i hi
  linarith

theorem overlap_dist_lt : 3 * S.lam / 2 + S.rho / 2 < S.R := by
  have := S.rho_lt_lam
  have := S.two_lam_lt_R
  linarith

theorem mem_blockL_overlap_start (hi : i < n) :
    A.off (i + 1) (3 * S.lam / 2) (S.rho / 2) ∈ S.blockL (i + 1) :=
  S.mem_blockL_off.2 ⟨S.lam_lt_three_halves_lam, S.three_halves_lam_lt (by omega),
    by linarith [S.rho_pos], by linarith [S.rho_pos]⟩

theorem mem_blockR_overlap_start (hi : i < n) :
    A.off (i + 1) (3 * S.lam / 2) (-(S.rho / 2)) ∈ S.blockR (i + 1) :=
  S.mem_blockR_off.2 ⟨S.lam_lt_three_halves_lam, S.three_halves_lam_lt (by omega),
    by linarith [S.rho_pos], by linarith [S.rho_pos]⟩

theorem mem_blockL_overlap_finish (hi : i < n) :
    A.off i (A.len i - 3 * S.lam / 2) (S.rho / 2) ∈ S.blockL i := by
  have h1 : S.lam < A.len i - 3 * S.lam / 2 := by
    have := S.lam_pos; have := S.four_lam_lt_len i (by omega); linarith
  exact S.mem_blockL_off.2 ⟨h1, by have := S.lam_pos; linarith, by linarith [S.rho_pos],
    by linarith [S.rho_pos]⟩

theorem mem_blockR_overlap_finish (hi : i < n) :
    A.off i (A.len i - 3 * S.lam / 2) (-(S.rho / 2)) ∈ S.blockR i := by
  have h1 : S.lam < A.len i - 3 * S.lam / 2 := by
    have := S.lam_pos; have := S.four_lam_lt_len i (by omega); linarith
  exact S.mem_blockR_off.2 ⟨h1, by have := S.lam_pos; linarith, by linarith [S.rho_pos],
    by linarith [S.rho_pos]⟩

/-- **The overlap at the departure vertex.** -/
theorem mem_overlapL_start (hi : i < n) :
    A.off (i + 1) (3 * S.lam / 2) (S.rho / 2) ∈ S.blockL (i + 1) ∩ S.sectorL i := by
  refine ⟨S.mem_blockL_overlap_start hi,
    S.blockL_sub_mem_arcL_start hi (S.mem_blockL_overlap_start hi), ?_⟩
  refine lt_of_le_of_lt PolyArc.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [S.lam_pos] : (0:ℝ) < 3 * S.lam / 2),
    abs_of_pos (by linarith [S.rho_pos] : (0:ℝ) < S.rho / 2)]
  exact S.overlap_dist_lt

/-- **The overlap at the arrival vertex.** -/
theorem mem_overlapL_finish (hi : i < n) :
    A.off i (A.len i - 3 * S.lam / 2) (S.rho / 2) ∈ S.blockL i ∩ S.sectorL i := by
  refine ⟨S.mem_blockL_overlap_finish hi,
    S.blockL_sub_mem_arcL_finish hi (S.mem_blockL_overlap_finish hi), ?_⟩
  refine lt_of_le_of_lt PolyArc.dist_off_vertex_succ_le ?_
  rw [show A.len i - 3 * S.lam / 2 - A.len i = -(3 * S.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [S.lam_pos] : (0:ℝ) < 3 * S.lam / 2),
    abs_of_pos (by linarith [S.rho_pos] : (0:ℝ) < S.rho / 2)]
  exact S.overlap_dist_lt

theorem mem_overlapR_start (hi : i < n) :
    A.off (i + 1) (3 * S.lam / 2) (-(S.rho / 2)) ∈ S.blockR (i + 1) ∩ S.sectorR i := by
  refine ⟨S.mem_blockR_overlap_start hi,
    S.blockR_sub_mem_arcR_start hi (S.mem_blockR_overlap_start hi), ?_⟩
  refine lt_of_le_of_lt PolyArc.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [S.lam_pos] : (0:ℝ) < 3 * S.lam / 2),
    abs_neg, abs_of_pos (by linarith [S.rho_pos] : (0:ℝ) < S.rho / 2)]
  exact S.overlap_dist_lt

theorem mem_overlapR_finish (hi : i < n) :
    A.off i (A.len i - 3 * S.lam / 2) (-(S.rho / 2)) ∈ S.blockR i ∩ S.sectorR i := by
  refine ⟨S.mem_blockR_overlap_finish hi,
    S.blockR_sub_mem_arcR_finish hi (S.mem_blockR_overlap_finish hi), ?_⟩
  refine lt_of_le_of_lt PolyArc.dist_off_vertex_succ_le ?_
  rw [show A.len i - 3 * S.lam / 2 - A.len i = -(3 * S.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [S.lam_pos] : (0:ℝ) < 3 * S.lam / 2),
    abs_neg, abs_of_pos (by linarith [S.rho_pos] : (0:ℝ) < S.rho / 2)]
  exact S.overlap_dist_lt

theorem blockL_nonempty (hi : i ≤ n) : (S.blockL i).Nonempty :=
  ⟨A.off i (3 * S.lam / 2) (S.rho / 2), S.mem_blockL_off.2
    ⟨S.lam_lt_three_halves_lam, S.three_halves_lam_lt hi, by linarith [S.rho_pos],
      by linarith [S.rho_pos]⟩⟩

theorem blockR_nonempty (hi : i ≤ n) : (S.blockR i).Nonempty :=
  ⟨A.off i (3 * S.lam / 2) (-(S.rho / 2)), S.mem_blockR_off.2
    ⟨S.lam_lt_three_halves_lam, S.three_halves_lam_lt hi, by linarith [S.rho_pos],
      by linarith [S.rho_pos]⟩⟩

theorem isConnected_blockL (hi : i ≤ n) : IsConnected (S.blockL i) :=
  S.convex_blockL.isConnected (S.blockL_nonempty hi)

theorem isConnected_blockR (hi : i ≤ n) : IsConnected (S.blockR i) :=
  S.convex_blockR.isConnected (S.blockR_nonempty hi)

/-! ### The two tracks are connected -/

theorem isConnected_chainL (hk : k ≤ n) : IsConnected (S.chainL k) := by
  cases k with
  | zero => exact S.isConnected_blockL (Nat.zero_le n)
  | succ k =>
      exact IsConnected.union ⟨_, (S.mem_overlapL_start (by omega)).2,
        (S.mem_overlapL_start (by omega)).1⟩ (S.isConnected_sectorL (by omega))
        (S.isConnected_blockL hk)

theorem isConnected_chainR (hk : k ≤ n) : IsConnected (S.chainR k) := by
  cases k with
  | zero => exact S.isConnected_blockR (Nat.zero_le n)
  | succ k =>
      exact IsConnected.union ⟨_, (S.mem_overlapR_start (by omega)).2,
        (S.mem_overlapR_start (by omega)).1⟩ (S.isConnected_sectorR (by omega))
        (S.isConnected_blockR hk)

theorem chainL_meet (hk : k < n) : (S.chainL k ∩ S.chainL (k + 1)).Nonempty :=
  ⟨_, S.blockL_subset_chainL k (S.mem_overlapL_finish hk).1,
    Or.inl (S.mem_overlapL_finish hk).2⟩

theorem chainR_meet (hk : k < n) : (S.chainR k ∩ S.chainR (k + 1)).Nonempty :=
  ⟨_, S.blockR_subset_chainR k (S.mem_overlapR_finish hk).1,
    Or.inl (S.mem_overlapR_finish hk).2⟩

/-- **The left track of the collar is connected.** -/
theorem isConnected_sideL : IsConnected S.sideL :=
  isConnected_iUnion_chain n (fun _ hk => S.isConnected_chainL hk) fun _ hk => S.chainL_meet hk

/-- **The right track of the collar is connected.** -/
theorem isConnected_sideR : IsConnected S.sideR :=
  isConnected_iUnion_chain n (fun _ hk => S.isConnected_chainR hk) fun _ hk => S.chainR_meet hk

end ArcStrip

namespace ArcStrip

variable {n : ℕ} {A : PolyArc n} {D K : Set Plane} (S : ArcStrip A D K) {i j k : ℕ} {x : Plane}

/-! ### The two tracks are disjoint

Not a clause of `Schoenflies.ArcCollar` — the consumer does not need it — but it comes out of
the same four families times four families as in the cyclic case, and a later consumer will
want it. -/

/-! ### The compact piece is inside the collar

`sep_ends` is what makes this work: a point of `K` on the first edge is at least `R` from the
first vertex, so it is never in the gap the collar leaves at that end, and symmetrically at the
other end. -/

/-- **`K` is inside the collar.** -/
theorem subset_nbhd : K ⊆ S.nbhd := by
  intro y hy
  obtain ⟨i, hi, hyi⟩ := PolyArc.mem_carrier_iff.1 (S.subset_carrier hy)
  obtain ⟨hend0, hend1⟩ := S.sep_ends y hy
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := PolyArc.mem_edge_iff.1 hyi
  have hlow : i = 0 → S.R ≤ c := by
    intro h
    have heq : A.vertex 0 = A.vertex i := by rw [h]
    rwa [heq, PolyArc.dist_pt_vertex, abs_of_nonneg hc0] at hend0
  have hhigh : i = n → S.R ≤ A.len i - c := by
    intro h
    have heq : A.vertex (n + 1) = A.vertex (i + 1) := by rw [h]
    rw [heq, PolyArc.dist_pt_vertex_succ, abs_of_nonpos (by linarith)] at hend1
    linarith
  rcases lt_or_ge c S.R with h1 | h1
  · have hi0 : i ≠ 0 := fun h => by have h2 := hlow h; linarith
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    refine Or.inr (mem_iUnion_lt_nat.2 ⟨j, by omega, ?_⟩)
    rw [mem_ball, PolyArc.dist_pt_vertex, abs_of_nonneg hc0]
    exact h1
  rcases lt_or_ge (A.len i - S.R) c with h2 | h2
  · have hin : i ≠ n := fun h => by have h2' := hhigh h; linarith
    refine Or.inr (mem_iUnion_lt_nat.2 ⟨i, by omega, ?_⟩)
    rw [mem_ball, PolyArc.dist_pt_vertex_succ, abs_of_nonpos (by linarith)]
    linarith
  · refine Or.inl (mem_iUnion_le_nat.2 ⟨i, hi, ?_⟩)
    rw [PolyArc.pt]
    exact S.mem_tube_off.2 ⟨by linarith [S.lam_lt_R], by linarith [S.lam_lt_R],
      by linarith [S.rho_pos], S.rho_pos⟩

/-! ### Both tracks approach every point of `K` -/

/-- A sector comes arbitrarily close to its vertex: shrink a point of it towards the vertex,
which stays in the arc because an arc of directions is a cone. -/
theorem exists_near_sectorL (hi : i < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ S.sectorL i, dist y (A.vertex (i + 1)) < ε := by
  obtain ⟨z, hz⟩ := (S.isConnected_sectorL hi).nonempty
  have harc : z - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := hz.1
  have hwne : z - A.vertex (i + 1) ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - A.vertex (i + 1)‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - A.vertex (i + 1)‖ < S.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨A.vertex (i + 1) + (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)),
    ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) := lt_min one_pos (by positivity)
     have hsub : A.vertex (i + 1) +
         (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)) -
         A.vertex (i + 1) =
         (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)) := by module)
  · rw [Set.mem_setOf_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) ≤ ε / (2 * ‖z - A.vertex (i + 1)‖) :=
      min_le_right _ _
    have hkey : ε / (2 * ‖z - A.vertex (i + 1)‖) * ‖z - A.vertex (i + 1)‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

theorem exists_near_sectorR (hi : i < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ S.sectorR i, dist y (A.vertex (i + 1)) < ε := by
  obtain ⟨z, hz⟩ := (S.isConnected_sectorR hi).nonempty
  have harc : z - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := hz.1
  have hwne : z - A.vertex (i + 1) ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - A.vertex (i + 1)‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - A.vertex (i + 1)‖ < S.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨A.vertex (i + 1) + (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)),
    ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) := lt_min one_pos (by positivity)
     have hsub : A.vertex (i + 1) +
         (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)) -
         A.vertex (i + 1) =
         (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)) := by module)
  · rw [Set.mem_setOf_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) ≤ ε / (2 * ‖z - A.vertex (i + 1)‖) :=
      min_le_right _ _
    have hkey : ε / (2 * ‖z - A.vertex (i + 1)‖) * ‖z - A.vertex (i + 1)‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

/-- **Both tracks come arbitrarily close to every point of `K`.** In the middle of an edge this
is the block; at an interior vertex it is `exists_near_sectorL`; in between it is the germ with
the progress held fixed and the offset shrunk below the corner's threshold. The two cases the
cyclic argument does not have — a point near an *extreme* vertex, where there is no sector —
are excluded by `sep_ends`. -/
theorem exists_near_sides (hx : x ∈ K) {ε : ℝ} (hε : 0 < ε) :
    (∃ y ∈ S.sideL, dist x y < ε) ∧ (∃ y ∈ S.sideR, dist x y < ε) := by
  obtain ⟨i, hi, hxi⟩ := PolyArc.mem_carrier_iff.1 (S.subset_carrier hx)
  obtain ⟨hend0, hend1⟩ := S.sep_ends x hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := PolyArc.mem_edge_iff.1 hxi
  have hlow : i = 0 → S.R ≤ c := by
    intro h
    have heq : A.vertex 0 = A.vertex i := by rw [h]
    rwa [heq, PolyArc.dist_pt_vertex, abs_of_nonneg hc0] at hend0
  have hhigh : i = n → S.R ≤ A.len i - c := by
    intro h
    have heq : A.vertex (n + 1) = A.vertex (i + 1) := by rw [h]
    rw [heq, PolyArc.dist_pt_vertex_succ, abs_of_nonpos (by linarith)] at hend1
    linarith
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · -- the initial vertex of the edge, which `sep_ends` forces to be an interior vertex
    have hi0 : i ≠ 0 := fun h => by
      have h2 := hlow h; rw [← hc0'] at h2; linarith [S.R_pos]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j < n := by omega
    rw [← hc0', PolyArc.pt_zero]
    obtain ⟨y, hy, hd⟩ := S.exists_near_sectorL hj hε
    obtain ⟨y', hy', hd'⟩ := S.exists_near_sectorR hj hε
    exact ⟨⟨y, S.sectorL_subset_sideL hj hy, by rw [dist_comm]; exact hd⟩,
      ⟨y', S.sectorR_subset_sideR hj hy', by rw [dist_comm]; exact hd'⟩⟩
  rcases eq_or_lt_of_le hc1 with hc1' | hc1'
  · -- the terminal vertex of the edge
    have hin : i ≠ n := fun h => by
      have h2 := hhigh h; rw [hc1'] at h2; linarith [S.R_pos]
    have hin' : i < n := by omega
    rw [hc1', PolyArc.pt_len]
    obtain ⟨y, hy, hd⟩ := S.exists_near_sectorL hin' hε
    obtain ⟨y', hy', hd'⟩ := S.exists_near_sectorR hin' hε
    exact ⟨⟨y, S.sectorL_subset_sideL hin' hy, by rw [dist_comm]; exact hd⟩,
      ⟨y', S.sectorR_subset_sideR hin' hy', by rw [dist_comm]; exact hd'⟩⟩
  by_cases hmid : S.lam < c ∧ c < A.len i - S.lam
  · -- an interior point of the middle stretch: the block does it
    have hσpos : 0 < min (S.rho / 2) (ε / 2) := lt_min (by linarith [S.rho_pos]) (by linarith)
    have hσrho : min (S.rho / 2) (ε / 2) < S.rho :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith [S.rho_pos])
    have hσε : min (S.rho / 2) (ε / 2) < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨⟨A.off i c (min (S.rho / 2) (ε / 2)), S.blockL_subset_sideL hi
        (S.mem_blockL_off.2 ⟨hmid.1, hmid.2, hσpos, hσrho⟩), ?_⟩,
      ⟨A.off i c (-min (S.rho / 2) (ε / 2)), S.blockR_subset_sideR hi
        (S.mem_blockR_off.2 ⟨hmid.1, hmid.2, by linarith, by linarith⟩), ?_⟩⟩
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_pos hσpos]; exact hσε
    · rw [dist_comm, PolyArc.dist_off_pt,
        abs_of_neg (by linarith : -min (S.rho / 2) (ε / 2) < 0)]
      linarith
  push Not at hmid
  by_cases hnear : c ≤ S.lam
  · -- near the initial vertex, which `sep_ends` again forces to be interior
    have hi0 : i ≠ 0 := fun h => by have h2 := hlow h; linarith [S.lam_lt_R]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j < n := by omega
    have hdet : 0 < |det (A.back j) (A.tang (j + 1))| := abs_pos.2 (PolyArc.det_rays_ne_zero hj)
    have hker : (0 : ℝ) < 1 + |inner ℝ (A.back j) (A.tang (j + 1))| := by positivity
    obtain ⟨σ, hσpos, hσε, hσR, hσm⟩ := exists_offset_bound hε
      (show (0 : ℝ) < S.R - S.lam by linarith [S.lam_lt_R]) (mul_pos hc0' hdet) hker
    have hgerm : σ * |inner ℝ (A.back j) (A.tang (j + 1))| <
        c * |det (A.back j) (A.tang (j + 1))| := by
      have h1 := mul_le_mul_of_nonneg_left
        (show |inner ℝ (A.back j) (A.tang (j + 1))| ≤
          1 + |inner ℝ (A.back j) (A.tang (j + 1))| by linarith) hσpos.le
      linarith
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (A.off (j + 1) c τ) (A.vertex (j + 1)) < S.R := by
      intro τ hτ
      have h := PolyArc.dist_off_vertex_le (A := A) (i := j + 1) (t := c) (s := τ)
      rw [abs_of_pos hc0'] at h
      linarith
    refine ⟨⟨A.off (j + 1) c σ, S.sectorL_subset_sideL hj
        ⟨PolyArc.off_sub_mem_arcL_start hj hσpos hgerm, hdv σ (by rw [abs_of_pos hσpos])⟩, ?_⟩,
      ⟨A.off (j + 1) c (-σ), S.sectorR_subset_sideR hj
        ⟨PolyArc.off_sub_mem_arcR_start hj (by linarith) (by rw [neg_neg]; exact hgerm),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩, ?_⟩⟩
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_pos hσpos]; exact hσε
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_neg (by linarith : -σ < 0)]; linarith
  · -- near the terminal vertex
    push Not at hnear
    have hfar : A.len i - c ≤ S.lam := by have h := hmid hnear; linarith
    have hin : i ≠ n := fun h => by have h2 := hhigh h; linarith [S.lam_lt_R]
    have hin' : i < n := by omega
    have hdet : 0 < |det (A.back i) (A.tang (i + 1))| :=
      abs_pos.2 (PolyArc.det_rays_ne_zero hin')
    have hker : (0 : ℝ) < 1 + |inner ℝ (A.back i) (A.tang (i + 1))| := by positivity
    obtain ⟨σ, hσpos, hσε, hσR, hσm⟩ := exists_offset_bound hε
      (show (0 : ℝ) < S.R - S.lam by linarith [S.lam_lt_R])
      (mul_pos (show (0 : ℝ) < A.len i - c by linarith) hdet) hker
    have hgerm : σ * |inner ℝ (A.back i) (A.tang (i + 1))| <
        (A.len i - c) * |det (A.back i) (A.tang (i + 1))| := by
      have h1 := mul_le_mul_of_nonneg_left
        (show |inner ℝ (A.back i) (A.tang (i + 1))| ≤
          1 + |inner ℝ (A.back i) (A.tang (i + 1))| by linarith) hσpos.le
      linarith
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (A.off i c τ) (A.vertex (i + 1)) < S.R := by
      intro τ hτ
      have h := PolyArc.dist_off_vertex_succ_le (A := A) (i := i) (t := c) (s := τ)
      rw [abs_sub_comm, abs_of_pos (show (0 : ℝ) < A.len i - c by linarith)] at h
      linarith
    refine ⟨⟨A.off i c σ, S.sectorL_subset_sideL hin'
        ⟨PolyArc.off_sub_mem_arcL_finish hin' hσpos hgerm, hdv σ (by rw [abs_of_pos hσpos])⟩, ?_⟩,
      ⟨A.off i c (-σ), S.sectorR_subset_sideR hin'
        ⟨PolyArc.off_sub_mem_arcR_finish hin' (by linarith) (by rw [neg_neg]; exact hgerm),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩, ?_⟩⟩
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_pos hσpos]; exact hσε
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_neg (by linarith : -σ < 0)]; linarith

/-- Every point of `K` is in the closure of the left track. -/
theorem subset_closure_sideL : K ⊆ closure S.sideL := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨⟨z, hz, hd⟩, -⟩ := S.exists_near_sides hy hε
  exact ⟨z, hz, hd⟩

/-- Every point of `K` is in the closure of the right track. -/
theorem subset_closure_sideR : K ⊆ closure S.sideR := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨-, ⟨z, hz, hd⟩⟩ := S.exists_near_sides hy hε
  exact ⟨z, hz, hd⟩

/-! ### Lemma 1.8 (b) -/

/-- **The two-sided collar of the compact piece `K` along the arc**, as the record
`Schoenflies.ArcCollar` that `Schoenflies/CrosscutAtMostTwo.lean` consumes. The construction is
exported, not existentially packaged: `nbhd`, `sideL` and `sideR` are definitions with an API
of their own, and `Schoenflies.ArcStrip.sideL_disjoint_sideR` and
`Schoenflies.ArcStrip.isOpen_sideL` are two clauses of Lemma 1.8 (b) that the record drops. -/
def collar : ArcCollar D A.carrier K where
  nbhd := S.nbhd
  left := S.sideL
  right := S.sideR
  isOpen_nbhd := S.isOpen_nbhd
  subset_nbhd := S.subset_nbhd
  nbhd_subset := S.nbhd_subset
  nbhd_diff := S.nbhd_diff_carrier
  isConnected_left := S.isConnected_sideL
  isConnected_right := S.isConnected_sideR
  subset_closure_left := S.subset_closure_sideL
  subset_closure_right := S.subset_closure_sideR

@[simp] theorem collar_nbhd : S.collar.nbhd = S.nbhd := rfl
@[simp] theorem collar_left : S.collar.left = S.sideL := rfl
@[simp] theorem collar_right : S.collar.right = S.sideR := rfl

end ArcStrip

/-! ## Choosing the constants

The blueprint's own recipe, in the blueprint's order, with the two clauses about the prescribed
open set folded in at the step where they can be met.

1. `R` from the edge lengths, the pairwise vertex separations, the distance from each vertex to
   each nonincident edge, the openness of `D` at each interior vertex, and the distance from `K`
   to the two endpoints of the arc.
2. `lam := R / 5`, which gives `2 lam < R` and, through `R ≤ len i`, also `4 lam < len i`.
3. `rho` from the distance of each *trimmed* edge to every other edge, from the germ threshold
   at every interior vertex, and from the compact separation of each trimmed edge from the
   complement of `D`. Step 3 is where "the collar is inside `D`" is really paid for: a trimmed
   core is a compact subset of `D`, because the only points of the arc outside `D` are its two
   endpoints and the trim removes them. -/

/-! ## Lemma 1.8 (b), and `HasArcCollars` -/

/-! ## The presentation is faithful: the carrier is a simple polygonal arc

`PolyArc` is a *presentation*, so the interface owes a check in the other direction: that the
carrier of a `PolyArc` really is a simple polygonal arc between its two extreme vertices. Both
halves are an induction along the chain of edges, and the only input is simplicity: consecutive
edges meet exactly at the vertex they share, and nonconsecutive ones not at all.

With them, Lemma "At most two sides" for an arc presented by a vertex list has **no hypothesis
left standing** — `Schoenflies.polyArc_crosscut_at_most_two`. -/

/-! ## The presentation is not vacuous: a straight crosscut

A nondegenerate segment is a `PolyArc 0`: one edge, no interior vertex, so both `edges_meet` and
`corner` are vacuous. The vertex function is padded past the segment by walking on in the same
direction, which keeps it injective — this is the padding convention the structure's docstring
describes, in its simplest instance. With it, `Schoenflies.hasArcCollars_segment` of
`Schoenflies/CrosscutAtMostTwo.lean` is a special case of `Schoenflies.hasArcCollars`, which
certifies that `Schoenflies.IsPolyArcCarrier` is satisfiable and that the whole apparatus above
is not vacuous. -/

/-!
## What is still missing

Exactly one thing: `Schoenflies.IsPolyArcCarrier`. Everything above is proved for an arc
*presented by its vertex list*, and `Schoenflies.hasArcCollars` therefore carries that
presentation as a hypothesis in place of the blueprint's set-level "`P` is a simple polygonal
arc" (`IsArcBetween P a b` together with `IsPolygonal P`).

The missing theorem is

```
theorem isPolyArcCarrier_of_isPolygonal {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) (hab : a ≠ b) : IsPolyArcCarrier P a b
```

the arc analogue of `Schoenflies.exists_closedPolygon`, which `Schoenflies/Realization.lean`
proves for a Jordan curve. It is a *normalisation* statement, not geometry: it says a set that
happens to be both an arc and a finite union of segments can be cut into a chain. The route is
the one `Schoenflies/Realization.lean` takes in the closed case, and its three steps are:

1. `Schoenflies.IsArcBetween.exists_poly_eq` already gives a vertex list `vs` with
   `poly vs = P`, `vs.head = a`, `vs.getLast = b`. That list may backtrack: nothing yet says its
   vertices occur in order along `P`.
2. Order them. Each segment `[vs i, vs (i+1)]` is contained in `P` and is an arc between its
   ends, so by `Schoenflies.IsArcBetween.eq_of_subset` it *is* the subarc of `P` between the two
   parameters. The parameters of the `vs i`, sorted and deduplicated, therefore cut `[0, 1]` into
   intervals each of which is covered by one of those segments, and the subarc over each is a
   segment. That is the chain, with `vertex_inj` and `edges_meet` immediate from injectivity of
   the parametrisation.
3. Delete redundant vertices, i.e. merge two consecutive collinear edges into one. This is the
   blueprint's own first sentence ("Delete redundant vertices at which two consecutive edges are
   collinear") and is what `corner` needs; the closed-curve analogue is
   `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`.

None of the three is formalised for an arc. The remaining results require no such interface.
-/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Square
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The sup metric and axis-parallel squares

The blueprint takes the Euclidean norm as primary and uses the sup norm for the
axis-parallel objects the polygonal work is built on: grids of small squares, the vertex
squares of the redrawing argument, and the large square a bounded set is caught inside.
Appendix C item 1 asks for the comparison `‖x‖∞ ≤ ‖x‖ ≤ √2 ‖x‖∞`, which is `supNorm_le_norm`
and `norm_le_sqrt_two_mul_supNorm` here.

The one theorem of substance is `isConnected_beyondSquare`: the plane outside a closed
square is connected. It is a *square* and not a disk on purpose — the outside of a square is
exactly a union of four half-planes, each convex, with consecutive ones sharing a point,
whereas the outside of a disk would need the polar decomposition this development withholds.

## Blueprint

* `supNorm`, `supDist` — Appendix C, item 1 (the sup metric).
* `supNorm_le_norm`, `norm_le_sqrt_two_mul_supNorm` — the comparison, used without comment.
* `closedSquare`, `openSquare` — the axis-parallel square about a point.
* `isConnected_beyondSquare` — the outside of a square is connected; what makes exactly one
  face of a plane graph unbounded.
-/

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### Coordinates -/

theorem continuous_coord (i : Fin 2) : Continuous fun x : Plane => x i :=
  PiLp.continuous_apply _ _ i

/-! ### The sup norm -/

theorem supDist_nonneg (x y : Plane) : 0 ≤ supDist x y := supNorm_nonneg _

theorem supDist_comm (x y : Plane) : supDist x y = supDist y x := by
  simp only [supDist, supNorm, sub_apply]
  rw [abs_sub_comm (x 0) (y 0), abs_sub_comm (x 1) (y 1)]

theorem abs_sub_zero_le_supDist (x y : Plane) : |x 0 - y 0| ≤ supDist x y :=
  le_max_left _ _

theorem abs_sub_one_le_supDist (x y : Plane) : |x 1 - y 1| ≤ supDist x y :=
  le_max_right _ _

/-- The sup distance satisfies the triangle inequality, one coordinate at a time. -/
theorem supDist_triangle (x y z : Plane) : supDist x z ≤ supDist x y + supDist y z := by
  simp only [supDist, supNorm, sub_apply]
  refine max_le ?_ ?_
  · calc |x 0 - z 0| ≤ |x 0 - y 0| + |y 0 - z 0| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_zero_le_supDist x y) (abs_sub_zero_le_supDist y z)
  · calc |x 1 - z 1| ≤ |x 1 - y 1| + |y 1 - z 1| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_one_le_supDist x y) (abs_sub_one_le_supDist y z)

/-! ### Coordinate half-planes

One convexity proof per direction serves all four sides of a square, and the outside of a
square is four of them. -/

theorem convex_coord_le (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_ge (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r ≤ x i} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem isOpen_coord_lt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | x i < r} :=
  isOpen_lt (continuous_coord i) continuous_const

theorem isOpen_coord_gt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | r < x i} :=
  isOpen_lt continuous_const (continuous_coord i)

/-! ### Axis-parallel squares -/

/-- The open axis-parallel square of radius `r` about `c`. -/
def openSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c < r}

theorem closedSquare_eq_inter (c : Plane) (r : ℝ) :
    closedSquare c r =
      ({x : Plane | c 0 - r ≤ x 0} ∩ {x : Plane | x 0 ≤ c 0 + r}) ∩
      ({x : Plane | c 1 - r ≤ x 1} ∩ {x : Plane | x 1 ≤ c 1 + r}) := by
  ext x
  simp only [closedSquare, supDist, supNorm, sub_apply, mem_setOf_eq, mem_inter_iff,
    max_le_iff, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem openSquare_eq_inter (c : Plane) (r : ℝ) :
    openSquare c r =
      ({x : Plane | c 0 - r < x 0} ∩ {x : Plane | x 0 < c 0 + r}) ∩
      ({x : Plane | c 1 - r < x 1} ∩ {x : Plane | x 1 < c 1 + r}) := by
  ext x
  simp only [openSquare, supDist, supNorm, sub_apply, mem_setOf_eq, mem_inter_iff,
    max_lt_iff, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem convex_closedSquare (c : Plane) (r : ℝ) : Convex ℝ (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((convex_coord_ge 0 _).inter (convex_coord_le 0 _)).inter
    ((convex_coord_ge 1 _).inter (convex_coord_le 1 _))

theorem convex_openSquare (c : Plane) (r : ℝ) : Convex ℝ (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((convex_coord_gt 0 _).inter (convex_coord_lt 0 _)).inter
    ((convex_coord_gt 1 _).inter (convex_coord_lt 1 _))

theorem isOpen_openSquare (c : Plane) (r : ℝ) : IsOpen (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((isOpen_coord_gt 0 _).inter (isOpen_coord_lt 0 _)).inter
    ((isOpen_coord_gt 1 _).inter (isOpen_coord_lt 1 _))

theorem isClosed_closedSquare (c : Plane) (r : ℝ) : IsClosed (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((isClosed_le continuous_const (continuous_coord 0)).inter
      (isClosed_le (continuous_coord 0) continuous_const)).inter
    ((isClosed_le continuous_const (continuous_coord 1)).inter
      (isClosed_le (continuous_coord 1) continuous_const))

/-! ### The outside of a square -/

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.LocallyPolygonal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_pair _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The plane minus finitely many open squares is locally polygonally connected

This is brick B5 of the polygonal-redrawing argument. The redrawing cuts an open axis-parallel
square out of the plane around each vertex of the graph; what the rest of the argument needs of
the leftover set `M` is that it is *locally polygonally connected* — every point of `M` has a
relatively open neighbourhood all of whose points are joined to each other by polygonal paths
running inside `M`. That is what feeds the clopen argument one level up (brick B6), where the
basic open piece is no longer a ball.

The informal description of the three basic shapes — a disk away from every square, a half-disk
against one side, a three-quarter disk at a corner — suggests an angular case analysis. There is
none here. Both the squares and the basic neighbourhoods are axis-parallel, so each shape is an
intersection of a small square with the complement of an open square, and

* the complement of an open square is the union of the four closed coordinate half-planes that
  bound it (`Plane.compl_openSquare_subset_iUnion`);
* intersecting with a small square gives four *rectangles*, each convex;
* if the small square is small enough, each of those rectangles is either empty or contains the
  centre `p` (`Plane.exists_radius_sides`).

A union of convex sets with a common point is polygonally connected by two segments through that
point, which is `isLocallyPolyConnAt_of_star`. The three shapes are then just the three ways the
list of nonempty pieces can come out (one, two adjacent, or two adjacent again with `p` on the
corner) and none of them has to be named.

The passage from one square to finitely many is a shrinking step: since the closed squares are
pairwise disjoint, a point lies in at most one of them, and a small enough neighbourhood of any
point misses all the others outright, so `M` looks locally exactly like the one-square case.

## Blueprint

* `PolyConnIn` — "joined by a polygonal path inside `S`"; the relation Lemma 1.1 produces.
* `IsLocallyPolyConn` — the local form of polygonal connectedness, brick B5's conclusion.
* `polyConnIn_of_convex`, `polyConnIn_union_of_convex` — a rectangle, and two rectangles that
  meet, are polygonally connected.
* `Plane.sideHalfPlane`, `Plane.sideGap` — the four half-planes bounding a square and the room
  between a point and each of them.
* `isLocallyPolyConnAt_compl_openSquare` — the one-square case: the complement of any open
  square is locally polygonally connected, at every point of the plane.
* `isLocallyPolyConn_compl_biUnion` — brick B5: the plane minus finitely many open squares with
  pairwise disjoint closures is locally polygonally connected.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {S T : Set Plane} {x y z : Plane}

/-! ### Two list lemmas about `poly`

`PolyPath.lean` has `poly_concat`, which extends a vertex list by a single vertex. Transitivity
and symmetry of polygonal connectedness need the two-list versions; both are general facts about
`poly` and belong beside `poly_concat` rather than here. -/

/-! ### Polygonal connectedness inside a set -/

/-- `x` and `y` are joined by a polygonal path lying inside `S`.

This is the relation `exists_poly_of_isPreconnected` produces; naming it lets the local statement
below be phrased without repeating the vertex-list existential. -/
def PolyConnIn (S : Set Plane) (x y : Plane) : Prop :=
  ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ S ∧ vs.head h = x ∧ vs.getLast h = y

/-! ### The local statement -/

/-- `S` is polygonally connected near `p`: some open `U` containing `p` has all the points of
`U ∩ S` joined to each other by polygonal paths *inside `S`*.

`U ∩ S` is the relative neighbourhood; stating it through an ambient open set avoids carrying a
subtype topology. Note the paths are required to lie in `S`, not in the neighbourhood — that is
the form brick B6's clopen argument consumes. -/
def IsLocallyPolyConnAt (S : Set Plane) (p : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyConnIn S x y

/-- `S` is locally polygonally connected: polygonally connected near each of its points. -/
def IsLocallyPolyConn (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt S p

/-! ### The four sides of a square -/

namespace Plane

/-- A coordinate description of the open square: it is the set of points within `r` of the
centre in each coordinate separately. -/
theorem mem_openSquare_iff (c : Plane) (r : ℝ) (x : Plane) :
    x ∈ openSquare c r ↔ ∀ i, |x i - c i| < r := by
  simp only [openSquare, mem_setOf_eq, supDist, supNorm, sub_apply, max_lt_iff,
    Fin.forall_fin_two]

/-- The centre of a square of positive radius is in it. -/
theorem mem_openSquare_self {p : Plane} {s : ℝ} (hs : 0 < s) : p ∈ openSquare p s := by
  simpa [openSquare] using hs

/-- Squares about a point grow with the radius. -/
theorem openSquare_mono {p : Plane} {s t : ℝ} (h : s ≤ t) : openSquare p s ⊆ openSquare p t :=
  fun _ hx => lt_of_lt_of_le hx h

/-- The closed half-plane on the far side of the `i`-th pair of sides of the square about `c` of
radius `r`; `b = true` picks the upper one. The four of them cover the complement of the square,
and each is convex, which is all the argument uses them for. -/
def sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) : Set Plane :=
  cond b {x | c i + r ≤ x i} {x | x i ≤ c i - r}

/-- How much room there is between `p` and the half-plane `sideHalfPlane c r i b`: positive
exactly when `p` is outside it, and an upper bound on a square radius that keeps a neighbourhood
of `p` clear of it. -/
noncomputable def sideGap (c : Plane) (r : ℝ) (p : Plane) (i : Fin 2) (b : Bool) : ℝ :=
  cond b ((c i + r) - p i) (p i - (c i - r))

theorem convex_sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    Convex ℝ (sideHalfPlane c r i b) := by
  cases b
  · exact convex_coord_le i _
  · exact convex_coord_ge i _

/-- Each of the four half-planes misses the open square. -/
theorem sideHalfPlane_subset_compl (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    sideHalfPlane c r i b ⊆ (openSquare c r)ᶜ := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff c r x).1 hmem i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hx) (by linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hx) (by linarith [hlt.2])

/-- The complement of an open square is covered by the four closed half-planes bounding it. -/
theorem compl_openSquare_subset_iUnion (c : Plane) (r : ℝ) :
    (openSquare c r)ᶜ ⊆ ⋃ ib : Fin 2 × Bool, sideHalfPlane c r ib.1 ib.2 := by
  intro x hx
  rw [mem_compl_iff, mem_openSquare_iff] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  rcases le_abs.1 hi with h | h
  · exact mem_iUnion.2 ⟨(i, true), show c i + r ≤ x i by linarith⟩
  · exact mem_iUnion.2 ⟨(i, false), show x i ≤ c i - r by linarith⟩

/-- If the radius is at most the room between `p` and a half-plane, the square about `p` of that
radius misses the half-plane. No sign condition on the gap: when it is nonpositive the radius is
too, and the square is empty. -/
theorem openSquare_disjoint_sideHalfPlane {c : Plane} {r s : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (hs : s ≤ sideGap c r p i b) :
    ∀ x ∈ openSquare p s, x ∉ sideHalfPlane c r i b := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff p s x).1 hx i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hmem) (by
      simp only [sideGap, cond_false] at hs <;> linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hmem) (by
      simp only [sideGap, cond_true] at hs <;> linarith [hlt.2])

/-- If there is no room between `p` and a half-plane, `p` is in it. -/
theorem mem_sideHalfPlane_of_sideGap_nonpos {c : Plane} {r : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (h : sideGap c r p i b ≤ 0) : p ∈ sideHalfPlane c r i b := by
  cases b
  · simp only [sideGap, cond_false] at h
    exact show p i ≤ c i - r by linarith
  · simp only [sideGap, cond_true] at h
    exact show c i + r ≤ p i by linarith

end Plane

/-! ### Choosing one radius for finitely many constraints -/

/-- A positive lower bound for whichever members of a finite family happen to be positive.
This is `exists_pos_le_of_finite` with the selection built in; the members that are nonpositive
impose nothing. -/
theorem exists_pos_le_of_pos {ι : Type*} [Finite ι] (d : ι → ℝ) :
    ∃ s > 0, ∀ i, 0 < d i → s ≤ d i := by
  obtain ⟨s, hs, hle⟩ :=
    exists_pos_le_of_finite (S := {i : ι | 0 < d i}) (Set.toFinite _) (f := d) fun _ hi => hi
  exact ⟨s, hs, fun i hi => hle i hi⟩

/-- A radius small enough that the square about `p` misses every side half-plane of the square
about `c` that `p` itself is outside of. -/
theorem Plane.exists_radius_sides (c : Plane) (r : ℝ) (p : Plane) :
    ∃ s > 0, ∀ ib : Fin 2 × Bool,
      ∀ z ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2,
        p ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2 := by
  obtain ⟨s, hs, hle⟩ := exists_pos_le_of_pos fun ib : Fin 2 × Bool => sideGap c r p ib.1 ib.2
  refine ⟨s, hs, fun ib z hz => ⟨?_, ?_⟩⟩
  · -- `p` is the centre of its own square, which is nonempty because `s > 0`.
    exact mem_openSquare_self hs
  · -- If there were room, the square about `p` would already miss this half-plane, and `z`
    -- could not be in it.
    by_contra hp
    exact openSquare_disjoint_sideHalfPlane
      (hle ib (lt_of_not_ge fun hcon => hp (mem_sideHalfPlane_of_sideGap_nonpos hcon))) z hz.1 hz.2

/-! ### The one-square case -/

/-! ### Finitely many squares -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Walk
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.IsCycleThrough.cycleGraph_vertexSet _root_.Graph.pathGraphOf_isLink _root_.Graph.pathGraphOf_vertexSet _root_.Graph.vertexSet_union_pathGraphOf
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Walks and paths in a multigraph

Mathlib's `Graph α β` carries incidence (`G.IsLink e x y`) and nothing that moves along it.
This file is the bottom of the combinatorial layer: walks, paths, reachability and
connectedness, all of which the plane development consumes through one theorem —
`Graph.IsWalk.contains_path`, the blueprint's "shorten an arbitrary walk at repeated
vertices".

## A walk is a list of edges

`G.IsWalk u W v` says the edge list `W` walks from `u` to `v`, each edge taken from the vertex
the previous one arrived at. It names its **edges**, not its vertices. That is forced by
parallel edges: two edges with the same ends are distinguishable only by name, and a walk
along one of them must be able to say which it took — a two-vertex cycle, which the plane
layer builds out of a Jordan curve cut at two points, is exactly such a graph. Nothing is
lost by naming edges, because an edge determines where taking it arrives
(`Graph.IsLink.right_unique` upstream, `Graph.IsWalk.target_unique` here).

It is an **inductive family**, not a recursion over the list. Every consumer argues by
induction along the walk, and the inductive gives that directly, naming the waypoint of each
step; a recursion `fun u (e :: W) v => ∃ w, G.IsLink e u w ∧ IsWalk G w W v` would force
every proof to generalize the source vertex by hand and to destructure an existential at each
step. The relation is built at the **source** end, since that is the end a list is extended
at; concatenation (`Graph.IsWalk.append`) and reversal (`Graph.IsWalk.reverse`) are proved
here once, and after that no argument has to care.

The empty walk demands `x ∈ V(G)`. This buys the whole file: every vertex a walk visits is a
vertex of the graph with *no* side hypothesis, because Mathlib's `Graph` already forces the
ends of an edge into `V(G)`.

## A path carries its own freshness

`G.IsPath u W v` is a walk with one clause added at each step: the vertex the step departs
from is not among those the rest of the path visits. The condition travels with the
induction, instead of being imposed afterwards on a separately computed vertex list — which
would have to be computed, and would need the graph to be loopless before it was even
correct.

## Loops

Mathlib's `Graph` allows an edge with both ends equal; the blueprint's graphs have none.
**Walks tolerate loops and paths exclude them automatically** — no hypothesis on `G` anywhere
in this file. A step of a path from `u` along `e` to `w` requires `u ∉ G.walkVertices w W`,
and `w` is always in that set, so `u ≠ w`: the freshness clause already says a path's step is
not a loop (`Graph.IsPath.not_isLoopAt`). Imposing looplessness on the graph instead would
put a hypothesis on every statement in the layer to rule out something the definitions
already rule out.

## Namespace

Declarations live in the root `Graph` namespace, extending Mathlib's, rather than in
`Schoenflies`: `G.IsWalk`, `hW.append`, `hP.isWalk` are the spellings every consumer wants,
and dot notation on a Mathlib type resolves through the type's own namespace.

## Blueprint

The blueprint uses finite graphs as an imported foundation (§"Imported facts", *Finite
graphs*: "in a finite connected graph, any two vertices are joined by a simple path, obtained
by shortening an arbitrary walk at repeated vertices"). This file supplies that import.

* `Graph.IsWalk.contains_path` — shortening a walk to a path; used at
  `lem:polygonal-connected` ("take a simple path in the resulting finite graph"),
  `lem:finite-polygonal-union` ("a simple graph path has the required realization") and
  `lem:skeleton-crosscuts` ("the resulting finite graph is connected, so it contains a
  simple graph path `P` from `a` to `b`").
* `Graph.Reaches`, `Graph.Connected` — the connectedness those three lemmas invoke.
* `Graph.IsPath.nodup` — a simple path repeats no edge; underneath the finiteness arguments
  that bound a path's length.
* `Graph.IsPath.reverse`, `Graph.IsPath.split` — a path backwards, and a path cut in two at a
  vertex it visits; what `lem:subdivision-ear-preserve` and `lem:relative-ear` run on.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y z : α} {e f : β} {W W₁ W₂ P : List β}

namespace Graph

/-! ### The vertices an edge list touches -/

/-- Every vertex on an edge of the graph is a vertex of the graph. -/
theorem coveredVertices_subset_vertexSet : G.coveredVertices W ⊆ V(G) :=
  fun _ ⟨_, _, hx⟩ ↦ hx.vertex_mem

theorem walkVertices_subset_vertexSet (hu : u ∈ V(G)) : G.walkVertices u W ⊆ V(G) :=
  Set.insert_subset hu coveredVertices_subset_vertexSet

/-! ### Walks -/

theorem IsWalk.right_mem (h : G.IsWalk u W v) : v ∈ V(G) := by
  induction h with
  | nil hx => exact hx
  | cons _ _ ih => exact ih

/-- Every vertex a walk visits is a vertex of the graph — with no hypothesis, since the
empty walk already stands at one. -/
theorem IsWalk.walkVertices_subset (h : G.IsWalk u W v) : G.walkVertices u W ⊆ V(G) :=
  walkVertices_subset_vertexSet h.left_mem

/-! ### Paths -/

theorem IsPath.left_mem (h : G.IsPath u W v) : u ∈ V(G) := h.isWalk.left_mem

theorem IsPath.right_mem (h : G.IsPath u W v) : v ∈ V(G) := h.isWalk.right_mem

/-- A path takes no edge twice: an edge it took again would put the vertex it departed from
back among the ones the rest of the path visits. -/
theorem IsPath.nodup (h : G.IsPath u W v) : W.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons u w v e W hl hW hfresh ih =>
    refine List.nodup_cons.2 ⟨fun he ↦ hfresh ?_, ih⟩
    exact mem_walkVertices_of_mem_covered ⟨e, he, hl.inc_left⟩

/-- A path grows at its **target** end. The relation is built at the source end, so this is
the direction that has to be worked for; it is what reversal runs on. -/
theorem IsPath.extend_at_target (h : G.IsPath u P w) (hl : G.IsLink e w v)
    (hv : v ∉ G.walkVertices u P) : G.IsPath u (P ++ [e]) v := by
  induction h with
  | nil hx =>
    rw [walkVertices_nil] at hv
    exact List.nil_append _ ▸ IsPath.single hl (Ne.symm hv)
  | @cons u w₀ w f P₀ hl₀ hP₀ hfresh ih =>
    have hv₀ : v ∉ G.walkVertices w₀ P₀ := fun hmem ↦ hv (mem_walkVertices_cons_of_mem hl₀ hmem)
    refine List.cons_append .. ▸ .cons hl₀ (ih hl hv₀) fun hmem ↦ ?_
    -- The departure vertex is still fresh: the only new edge is `e`, whose ends are the old
    -- target `w` — already visited — and `v`, which the source is not.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | ⟨f', hf', hinc⟩
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · obtain rfl : f' = e := by simpa using hf'
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      · exact hfresh hP₀.target_mem_walkVertices
      · exact hv mem_walkVertices_self

/-- A path runs backwards over the same edges. -/
theorem IsPath.reverse (h : G.IsPath u W v) : G.IsPath v W.reverse u := by
  induction h with
  | nil hx => simpa using IsPath.nil hx
  | @cons u w v e W hl hW hfresh ih =>
    rw [List.reverse_cons]
    refine ih.extend_at_target hl.symm fun hmem ↦ hfresh ?_
    -- `u` avoids everything the rest of the path visits, and reversal changes none of that.
    rw [walkVertices_reverse] at hmem
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hW.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered hcov

/-- A path splits at any vertex it visits, and the far half never returns to the source.
`Graph.IsPath.from_visited` is the suffix alone; the prefix is the awkward half, since the
relation is built at the source end and the prefix is what the induction has to carry
forward. -/
theorem IsPath.split (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      (x = u ∨ u ∉ G.walkVertices x W₂) := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', Or.inl rfl⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh, Or.inl rfl⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem ↦ hfresh (walkVertices_mono hsub₁ hmem),
      h₂, Or.inr fun hmem ↦ hfresh ?_⟩
    -- The far half's edges are among the rest, which the source already avoided.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hx'
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)

/-! ### Reachability -/

theorem Reaches.right_mem (h : G.Reaches u v) : v ∈ V(G) := h.choose_spec.right_mem

/-! ### Connectedness -/

/-! ### Transferring walks and paths along an inclusion or a deletion

`IsWalk.anti` above pulls a walk down an inclusion. These are its companions, factored here
because both the cycle module and the two-connectivity module reached for them independently.
-/

theorem coveredVertices_mono_of_le (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, hy.mono hHG⟩

theorem walkVertices_mono_of_le (hHG : H ≤ G) : H.walkVertices u W ⊆ G.walkVertices u W :=
  Set.insert_subset_insert (coveredVertices_mono_of_le hHG)

/-- A path of a graph whose edges all survive into a subgraph is a path of that subgraph —
the companion of `Graph.IsWalk.anti`, which it is otherwise identical to. Freshness comes
down the inclusion because the subgraph's edges touch no vertices the graph's do not. -/
theorem IsPath.anti (hHG : H ≤ G) (h : G.IsPath u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsPath u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl hW hfresh ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))
      fun hmem ↦ hfresh (walkVertices_mono_of_le hHG hmem)

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Drawing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Plane graphs

There is no `PlaneGraph` type. A plane graph is an abstract `G : Graph Plane β` **together
with** a drawing `drawing : β → ℝ → Plane`, related by `IsDrawing G drawing`. The abstract
graph stays itself, so every combinatorial theorem of `Schoenflies/Graph/` applies with
nothing to project through, and "a plane graph realises an abstract finite graph" is true by
construction rather than by a theorem. Bundling would put a record projection inside every
combinatorial citation.

The vertices being plane points is what makes the definition short: that the vertices are
distinct is not a clause, it is what `V(G) : Set Plane` already means.

`IsDrawing` has three clauses. Each edge is drawn by an injective continuous parametrization on
`[0, 1]` whose endpoint values are the two ends of that edge; an edge's arc meets the vertex set
only at those two ends; and two distinct edges meet only at vertices incident with both. The
second and third are the blueprint's "distinct edges of a plane graph meet only at shared
vertices", split so that `unique_edge_at` — away from the vertices a point of the drawing lies
on exactly one edge — falls out directly. That corollary is the form the polygonal overlay
wants.

The first clause names the *parametrization*, not merely its image. The weaker reading — "the
point set of an edge is an arc between its ends" — suffices for everything about faces, and
fails for the polygonal redrawing, which must speak of the last parameter at which an edge is
inside a given square. `edge_isArcBetween` recovers the weaker reading, so consumers needing
only that are unaffected.

## Blueprint

* `IsDrawing` — a plane graph, as an abstract graph plus a drawing.
* `IsDrawing.edge_param`, `IsDrawing.edge_isArcBetween` — the parametrization, and its image.
* `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` — distinct edges meet only at
  shared vertices; away from the vertices, a point lies on exactly one edge.
* `pointSet`, `IsDrawing.isCompact_pointSet`, `exterior`, `isOpen_exterior` — what a plane
  graph occupies, and the open set its faces live in.
* `face` — the component of the exterior through a point off the drawing. Named by a point
  rather than indexed, so no face has to be produced before it is spoken about.
-/

open Metric Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {base : Plane}

namespace IsDrawing

theorem isArc_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsArc (edgeArc drawing e) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  exact (h.edge_isArcBetween hxy).isArc

theorem isCompact_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsCompact (edgeArc drawing e) := (h.isArc_edgeArc he).isCompact

/-- The blueprint's "distinct edges of a plane graph meet only at shared vertices". -/
theorem arcs_meet_at_vertex (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hef : e ≠ f) {p : Plane} (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    p ∈ V(G) :=
  (h.edge_inter he hf hef hpe hpf).1

end IsDrawing

/-! ### What a plane graph occupies -/

/-- A finite plane graph occupies a compact set: finitely many points and finitely many
compact arcs. -/
theorem IsDrawing.isCompact_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsCompact (pointSet G drawing) := by
  refine (Graph.finite_vertexSet (G := G)).isCompact.union ?_
  exact (Graph.finite_edgeSet (G := G)).isCompact_biUnion fun e he => h.isCompact_edgeArc he

theorem IsDrawing.isClosed_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (pointSet G drawing) := h.isCompact_pointSet.isClosed

theorem IsDrawing.isOpen_exterior [G.Finite] (h : IsDrawing G drawing) :
    IsOpen (exterior G drawing) := h.isClosed_pointSet.isOpen_compl

theorem face_subset_exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) :
    face G drawing base ⊆ exterior G drawing :=
  connectedComponentIn_subset _ _

theorem mem_face (h : base ∈ exterior G drawing) : base ∈ face G drawing base :=
  mem_connectedComponentIn h

theorem IsDrawing.isOpen_face [G.Finite] (h : IsDrawing G drawing) (base : Plane) :
    IsOpen (face G drawing base) :=
  Schoenflies.Plane.isOpen_connectedComponentIn h.isOpen_exterior

/-- Faces partition the exterior: two faces either coincide or are disjoint. -/
theorem face_eq_or_disjoint (b c : Plane) :
    face G drawing b = face G drawing c ∨ Disjoint (face G drawing b) (face G drawing c) := by
  by_cases h : (face G drawing b ∩ face G drawing c).Nonempty
  · obtain ⟨z, hzb, hzc⟩ := h
    left
    rw [face, face, connectedComponentIn_eq hzb, connectedComponentIn_eq hzc]
  · right
    exact Set.disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h)

end Graph
end

section
-- module Solutions.Q146_CD.Graph_CycleJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The realisation of a cycle is a Jordan curve

A cycle of a plane graph arrives as `Schoenflies/Graph/Cycle.lean` presents it: an edge, and a
path between that edge's two ends which does not use it. Its realisation is the set of points
the arcs of those edges occupy, and the claim is that this set is a Jordan curve.

## The argument is set-level; no parametrisation of a walk is built

The obvious approach — a `walkArc` definition folding `Schoenflies.concatenate` along the edge
list — is the wrong shape twice over. The empty-list base case is a *constant* map, which is
not an arc, so the fold cannot be shown injective at the last step; and threading a
parametrisation through the induction buys nothing, since every consumer wants the point set.

Instead **the existence of the arc is what the induction carries**, in
`Schoenflies.IsArcBetween`. The arcs are chosen inside the induction and the concatenation of
them is chosen by the gluing theorem; no parametrisation is ever named.

## Where the geometry enters

Exactly once, in `Graph.IsDrawing.first_edge_meets_rest`: a common point of the first edge's
arc and the rest of the path is a vertex incident with both edges
(`Graph.IsDrawing.arcs_meet_at_vertex`), hence one of the two ends of the first edge, and the
path's own freshness clause — the vertex a step departs from is not one the rest visits —
forbids it being the source. Taking the same edge again is refused by the *same* clause, so a
separate "the edges of a path are distinct" lemma is not needed.

## Loops

Nothing here hypothesises looplessness, and nothing needs to: `Graph.IsDrawing.ne_of_isLink`
derives it. An edge with equal ends would be drawn by an arc whose parametrisation takes the
same value at `0` and at `1`, which its injectivity forbids. That is what rules out the
degenerate cycle `Graph.liesOnCycle_of_isLoopAt` — a loop with an empty detour — whose
realisation is a single arc and not a Jordan curve.

## Blueprint

* `Graph.edgesCover` — what a *list* of edges occupies. `Graph.pointSet` is the vertices
  together with this, taken over all the edges of the graph.
* `Graph.IsDrawing.path_isArcBetween` — the realisation of a path is an arc between its two
  ends.
* `Graph.IsDrawing.cycle_isJordanCurve` — §"Plane graphs and the utility graph": "in a plane
  graph the realization of a cycle is a Jordan curve: its edges are simple arcs with pairwise
  disjoint interiors, and consecutive edges meet exactly at their shared vertices, so the edge
  arcs concatenate injectively into a simple closed curve".
* `Graph.IsDrawing.cycle_inter` — the meeting condition in full: the detour and the edge meet
  in exactly the edge's two ends. `Schoenflies.IsJordanCurve.of_two_arcs` consumes only one
  inclusion of it, but the equality is what the blueprint asserts.
-/

open Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z : Plane} {W D : List β}

/-! ### What a list of edges occupies -/

theorem edgesCover_mono (h : W ⊆ D) : edgesCover drawing W ⊆ edgesCover drawing D :=
  fun _ hz ↦ let ⟨_, he, hze⟩ := mem_edgesCover_iff.1 hz; mem_edgesCover (h he) hze

/-- A list of edges of the graph occupies part of what the graph occupies. -/
theorem edgesCover_subset_pointSet (hW : ∀ e ∈ W, e ∈ E(G)) :
    edgesCover drawing W ⊆ pointSet G drawing := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_edgesCover_iff.1 hz
  exact edgeArc_subset_pointSet (hW e he) hze

/-! ### A plane graph has no loops

This is not a hypothesis anywhere in this file; it is a consequence of the drawing condition,
and it is what makes the degenerate cycle — a loop, with the empty path back — impossible. -/

/-! ### The realisation of a path

The induction carries the *existence* of an arc, not a parametrisation. Its one geometric
step is `Graph.IsDrawing.first_edge_meets_rest`. -/

/-! ### The realisation of a cycle -/

end Graph
end

section
-- module Solutions.Q146_CD.SegmentMeet
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# How two segments meet

Two segments meet in nothing, or in a segment. The blueprint says "the empty set, one
point, or one closed interval" (Lemma 3.7, polygonal overlay); a point *is* a segment with
equal endpoints, so the statement folds to a dichotomy, and that is the form the overlay
wants — it subdivides at the endpoints of whatever the meet turns out to be, and a
degenerate meet contributes one subdivision point.

No case analysis on whether the segments are parallel, and no determinant. The meet is
compact and convex, so its preimage under the parametrization `lineMap a b` is a compact
convex subset of `ℝ`, hence a closed interval; pushing that interval forward is a segment.

## Blueprint

* `segment_inter_segment` — the meet dichotomy used by Lemma 3.7.
-/

open Metric Set

namespace Schoenflies

/-- Two segments meet in nothing, or in a segment. -/
theorem segment_inter_segment (a b c d : Plane)
    (hne : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ∃ p q : Plane, segment ℝ a b ∩ segment ℝ c d = segment ℝ p q := by
  set S : Set Plane := segment ℝ a b ∩ segment ℝ c d with hSdef
  have hScompact : IsCompact S := (isCompact_segment a b).inter (isCompact_segment c d)
  have hSconvex : Convex ℝ S := (convex_segment a b).inter (convex_segment c d)
  -- Pull the meet back along the parametrization of the first segment.
  set f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap a b with hfdef
  set T : Set ℝ := Icc 0 1 ∩ f ⁻¹' S with hTdef
  -- `T` carries `S` forward. Note this needs no injectivity of `f`, so the degenerate case
  -- `a = b` is not a separate case.
  have himage : f '' T = S := by
    refine subset_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨t, ht, rfl⟩ := hx
      exact ht.2
    · have : x ∈ segment ℝ a b := hx.1
      rw [segment_eq_image_lineMap] at this
      obtain ⟨t, ht, rfl⟩ := this
      exact ⟨t, ⟨ht, hx⟩, rfl⟩
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have : x ∈ f '' T := by rw [himage]; exact hx
    obtain ⟨t, ht, -⟩ := this
    exact ⟨t, ht⟩
  have hTcompact : IsCompact T :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.inter (hScompact.isClosed.preimage AffineMap.lineMap_continuous))
      inter_subset_left
  have hTconvex : Convex ℝ T := (convex_Icc 0 1).inter (hSconvex.affine_preimage f)
  -- A nonempty compact convex subset of `ℝ` is a closed interval.
  obtain ⟨t₀, t₁, hTIcc⟩ : ∃ t₀ t₁, T = Icc t₀ t₁ :=
    ⟨_, _, eq_Icc_of_connected_compact ⟨hTne, hTconvex.isPreconnected⟩ hTcompact⟩
  have hle : t₀ ≤ t₁ := by
    rw [hTIcc] at hTne
    exact nonempty_Icc.1 hTne
  exact ⟨f t₀, f t₁, by rw [← himage, hTIcc, ← segment_eq_Icc hle, image_segment]⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.SegmentCut
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cutting a segment

Mathlib has no lemma splitting a segment at an interior point, and the polygonal subdivision
of Layer 6 is built entirely out of one: cutting loses nothing (`segment_split`) and cutting
is permanent (`openSegment_left_subset`, `openSegment_right_subset` — each half's interior
stays inside the whole's, so nothing later can put a removed point back into an interior).

Everything here is an identity between convex combinations. The `⊇` half of the split is
convexity; the `⊆` half rescales the parameter, and the only case analysis is on whether the
far coefficient vanishes.

## Blueprint

* `segment_split` — cutting at a point of the segment loses nothing; underneath
  `subdivide_covers`.
* `openSegment_left_subset`, `openSegment_right_subset` — a cut is permanent; underneath
  `subdivide_inside`.
-/

open Set

namespace Schoenflies

variable {a b p : Plane}

/-- Cutting is permanent, near half: the interior of the near piece stays inside the
interior of the whole. -/
theorem openSegment_left_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ a p ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s + t * α, t * β, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]

/-- Cutting is permanent, far half. -/
theorem openSegment_right_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ p b ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s * α, s * β + t, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]

end Schoenflies
end

section
-- module Solutions.Q146_CD.SegmentOrder
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Along one segment: the distance from an end as a coordinate

Everything the polygonal overlay has to say about several collinear segments — which piece
lies inside which, where a piece may end, when two pieces have to coincide — is
one-dimensional: it happens along a single straight segment. This module supplies the
coordinate that makes it ordinary arithmetic. Along a nondegenerate `segment ℝ a b` the
distance from `a` determines the point, and it reads betweenness off as a pair of
inequalities, so a claim about four collinear points becomes a claim about four reals.

No new geometry is needed. `dist_left_lineMap` already says the distance from `a` *is* the
parameter of `AffineMap.lineMap a b`, scaled by the segment's length, and `image_segment`
already says that parametrization carries segments of `ℝ` to segments of the plane. What is
added here is the translation, stated once so that the arithmetic does not have to be redone
at every use.

The two results the module exists for come last, and they are what makes cutting at every
meet enough:

* a piece that meets an overlap and keeps the overlap's ends out of its interior lies inside
  the overlap (`segment_inside_of_ends_outside`);
* two pieces whose interiors meet, each keeping the other's ends out of its interior, are the
  same pair of points (`same_ends_of_meeting_interiors`).

Both are stated **inside one ambient segment**. Collinearity is not optional: a piece crossing
the overlap transversally would meet it and avoid both its ends without lying inside it, so
every point named is a point of one ambient `segment ℝ a b`.

Both are also stated with no orientation asked of the caller. The `_oriented` forms they wrap
are near-end-first, which is what the arithmetic wants; the unoriented forms decide the
orientation themselves, and they are what the overlay uses.

## A note on degenerate pieces

Mathlib's `openSegment ℝ u u` is `{u}`, not `∅`. A degenerate piece therefore has a nonempty
interior, and the strict translation `dist_lt_of_mem_openSegment` genuinely needs `u ≠ v`.
The two headline theorems do *not* ask for it: in each of them a degenerate piece is either
excluded by the hypotheses or settled outright, and that case split lives inside the proof.

## Blueprint

* `segment_inside_of_ends_outside`, `same_ends_of_meeting_interiors` — the separation behind
  the deduplication clause of the polygonal overlay (`lem:polygonal-overlay`, "represent every
  duplicate geometric subsegment only once") and of the subdivision in
  `lem:polygonal-connected` ("delete duplicate subsegments"): once every piece's ends are cut
  points, and so interior to nothing, two pieces that share an interior point coincide instead
  of merely overlapping.
-/

open Set

namespace Schoenflies

variable {a b : Plane}

/-! ### The parametrization of a segment

`AffineMap.lineMap a b` walks from `a` to `b`. It carries a segment of `ℝ` onto the
corresponding piece of `[a, b]`, and it turns the distance from `a` into multiplication by
the segment's length. Those two facts are the whole content of the module; the rest is
arithmetic. -/

/-- The same for interiors. -/
theorem openSegment_lineMap_image (a b : Plane) (p q : ℝ) :
    openSegment ℝ (AffineMap.lineMap a b p) (AffineMap.lineMap a b q)
      = (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Plane) '' openSegment ℝ p q := by
  simp

/-! ### The coordinate -/

/-! ### Betweenness as a pair of inequalities -/

/-- The converse: a point of the segment whose distance from `a` lies between the two ends'
distances lies between the ends. -/
theorem mem_segment_of_dist_le (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) (h₁ : dist a u ≤ dist a x)
    (h₂ : dist a x ≤ dist a v) : x ∈ segment ℝ u v := by
  obtain ⟨p, hp0, -, rfl, -⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, -⟩ := exists_param_of_mem_segment hv
  obtain ⟨t, ht0, -, rfl, -⟩ := exists_param_of_mem_segment hx
  have hpt : p ≤ t := parameter_le_of_distance hab hp0 ht0 h₁
  have htq : t ≤ q := parameter_le_of_distance hab ht0 hq0 h₂
  rw [segment_lineMap_image, segment_eq_Icc (hpt.trans htq)]
  exact ⟨t, ⟨hpt, htq⟩, rfl⟩

/-! ### The same translation for interiors

`openSegment ℝ u u = {u}` in Mathlib, so the strict form asks for a nondegenerate piece; its
converse does not, since strict inequalities force nondegeneracy on their own. -/

/-- A point interior to a nondegenerate piece of the segment is strictly between its ends in
distance from `a`. -/
theorem dist_lt_of_mem_openSegment (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (huv : u ≠ v) (hor : dist a u ≤ dist a v)
    (hx : x ∈ openSegment ℝ u v) : dist a u < dist a x ∧ dist a x < dist a v := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨p, hp0, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  have hpq : p < q :=
    lt_of_le_of_ne (parameter_le_of_distance hab hp0 hq0 hor) fun h => huv (by rw [h])
  rw [openSegment_lineMap_image, openSegment_eq_Ioo hpq] at hx
  obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := hx
  rw [hpd, hqd, dist_left_lineMap_of_nonneg a b (hp0.trans hpt.le)]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The converse: a point of the segment strictly between the ends in distance from `a` is
interior to the piece they span. -/
theorem mem_openSegment_of_dist_lt (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) (h₁ : dist a u < dist a x)
    (h₂ : dist a x < dist a v) : x ∈ openSegment ℝ u v := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨p, -, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, -, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  obtain ⟨t, -, -, rfl, htd⟩ := exists_param_of_mem_segment hx
  rw [hpd, htd] at h₁
  rw [htd, hqd] at h₂
  have hpt : p < t := lt_of_mul_lt_mul_right h₁ hd.le
  have htq : t < q := lt_of_mul_lt_mul_right h₂ hd.le
  rw [openSegment_lineMap_image, openSegment_eq_Ioo (hpt.trans htq)]
  exact ⟨t, ⟨hpt, htq⟩, rfl⟩

/-! ### Where a point that is not interior to a piece must sit

These two carry the whole one-dimensional argument. A point of the ambient segment kept out
of a piece's interior has to be outside on one side or the other, and knowing which side it
is not settles it. -/

/-- A point of the ambient segment kept out of `[u, v]`'s interior and lying before `v` lies
at or before `u`. -/
theorem dist_le_left_of_notMem_openSegment (hab : a ≠ b) {u v y : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hout : y ∉ openSegment ℝ u v) (hlt : dist a y < dist a v) : dist a y ≤ dist a u := by
  by_contra hcon
  exact hout (mem_openSegment_of_dist_lt hab hu hv hy (lt_of_not_ge hcon) hlt)

/-- The mirror: a point of the ambient segment kept out of `[u, v]`'s interior and lying
after `u` lies at or after `v`. -/
theorem le_dist_right_of_notMem_openSegment (hab : a ≠ b) {u v y : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hout : y ∉ openSegment ℝ u v) (hlt : dist a u < dist a y) : dist a v ≤ dist a y := by
  by_contra hcon
  exact hout (mem_openSegment_of_dist_lt hab hu hv hy hlt (lt_of_not_ge hcon))

/-! ### What the overlay is after -/

/-- A piece that meets an overlap and keeps the overlap's two ends out of its interior lies
inside the overlap — near-end-first form. -/
theorem segment_inside_of_ends_outside_oriented (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hpiece : dist a u ≤ dist a v)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b) (hover : dist a s ≤ dist a t)
    (hxp : x ∈ openSegment ℝ u v) (hxo : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ s t := by
  -- A degenerate overlap is impossible: its only interior point is `s`, which by hypothesis
  -- is not interior to the piece, whereas `x` is.
  rcases eq_or_ne s t with rfl | hst
  · rw [openSegment_same, mem_singleton_iff] at hxo
    rw [← hxo] at hsout
    exact absurd hxp hsout
  -- A degenerate piece is the single point `x`, which already lies in the overlap.
  rcases eq_or_ne u v with rfl | huv
  · rw [openSegment_same, mem_singleton_iff] at hxp
    rw [segment_same, singleton_subset_iff, ← hxp]
    exact openSegment_subset_segment ℝ s t hxo
  obtain ⟨hux, hxv⟩ := dist_lt_of_mem_openSegment hab hu hv huv hpiece hxp
  obtain ⟨hsx, hxt⟩ := dist_lt_of_mem_openSegment hab hs ht hst hover hxo
  -- The overlap starts at or before the piece and ends at or after it.
  have hsu : dist a s ≤ dist a u :=
    dist_le_left_of_notMem_openSegment hab hu hv hs hsout (hsx.trans hxv)
  have hvt : dist a v ≤ dist a t :=
    le_dist_right_of_notMem_openSegment hab hu hv ht htout (hux.trans hxt)
  intro y hy
  have hyab : y ∈ segment ℝ a b := (convex_segment a b).segment_subset hu hv hy
  obtain ⟨huy, hyv⟩ := dist_le_of_mem_segment hab hu hv hpiece hy
  exact mem_segment_of_dist_le hab hs ht hyab (hsu.trans huy) (hyv.trans hvt)

/-- Two pieces of one ambient segment whose interiors meet, each keeping the other's ends out
of its interior, have the same ends — near-end-first form. -/
theorem same_ends_of_meeting_interiors_oriented (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hfirst : dist a u ≤ dist a v)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b) (hsecond : dist a s ≤ dist a t)
    (hxu : x ∈ openSegment ℝ u v) (hxs : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v)
    (huout : u ∉ openSegment ℝ s t) (hvout : v ∉ openSegment ℝ s t) :
    u = s ∧ v = t := by
  -- Neither piece can be degenerate: its only interior point would then be one of its own
  -- ends, which the other piece is required to keep out of its interior.
  rcases eq_or_ne u v with rfl | huv
  · rw [openSegment_same, mem_singleton_iff] at hxu
    rw [← hxu] at huout
    exact absurd hxs huout
  rcases eq_or_ne s t with rfl | hst
  · rw [openSegment_same, mem_singleton_iff] at hxs
    rw [← hxs] at hsout
    exact absurd hxu hsout
  obtain ⟨hux, hxv⟩ := dist_lt_of_mem_openSegment hab hu hv huv hfirst hxu
  obtain ⟨hsx, hxt⟩ := dist_lt_of_mem_openSegment hab hs ht hst hsecond hxs
  -- Each piece's near end lies at or before the other's, so they agree.
  have hsu : dist a s ≤ dist a u :=
    dist_le_left_of_notMem_openSegment hab hu hv hs hsout (hsx.trans hxv)
  have hus : dist a u ≤ dist a s :=
    dist_le_left_of_notMem_openSegment hab hs ht hu huout (hux.trans hxt)
  -- And the same on the far side.
  have hvt : dist a v ≤ dist a t :=
    le_dist_right_of_notMem_openSegment hab hu hv ht htout (hux.trans hxt)
  have htv : dist a t ≤ dist a v :=
    le_dist_right_of_notMem_openSegment hab hs ht hv hvout (hsx.trans hxv)
  exact ⟨eq_of_dist_left_eq hab hu hs (le_antisymm hus hsu),
    eq_of_dist_left_eq hab hv ht (le_antisymm hvt htv)⟩

/-! ### The same two, asking the caller nothing about orientation

A piece is a pair of ends, and which of them is nearer `a` is none of the caller's business —
`segment` and `openSegment` do not care. The oriented forms above are near-end-first because
that is what the arithmetic wants; these decide the orientation themselves. Every hypothesis
is restated in both spellings first, so each of the four cases is just "which way round, then
cite". -/

/-- A piece that meets an overlap and keeps the overlap's two ends out of its interior lies
inside the overlap.

Collinearity is not optional: every point named is a point of one ambient `segment ℝ a b`. A
piece crossing the overlap transversally would meet it and avoid both its ends without lying
inside it. -/
theorem segment_inside_of_ends_outside (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b)
    (hxp : x ∈ openSegment ℝ u v) (hxo : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ s t := by
  have hxp' : x ∈ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hsout' : s ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have htout' : t ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hxo' : x ∈ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hrevPiece : segment ℝ v u = segment ℝ u v := segment_symm ℝ v u
  have hrevOverlap : segment ℝ t s = segment ℝ s t := segment_symm ℝ t s
  rcases le_total (dist a u) (dist a v) with hp | hp <;>
    rcases le_total (dist a s) (dist a t) with ho | ho
  · exact segment_inside_of_ends_outside_oriented hab hu hv hp hs ht ho hxp hxo hsout htout
  · rw [← hrevOverlap]
    exact segment_inside_of_ends_outside_oriented hab hu hv hp ht hs ho hxp hxo' htout hsout
  · rw [← hrevPiece]
    exact segment_inside_of_ends_outside_oriented hab hv hu hp hs ht ho hxp' hxo hsout' htout'
  · rw [← hrevPiece, ← hrevOverlap]
    exact segment_inside_of_ends_outside_oriented hab hv hu hp ht hs ho hxp' hxo' htout' hsout'

/-- Two pieces of one ambient segment whose interiors meet, each keeping the other's ends out
of its interior, are the same pair of points — in one order or the other.

This is the separation the deduplication clause is for: overlapping collinear pieces cannot
be pulled apart by cutting, and after enough cuts they coincide instead. -/
theorem same_ends_of_meeting_interiors (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b)
    (hxu : x ∈ openSegment ℝ u v) (hxs : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v)
    (huout : u ∉ openSegment ℝ s t) (hvout : v ∉ openSegment ℝ s t) :
    (u = s ∧ v = t) ∨ (u = t ∧ v = s) := by
  have hxu' : x ∈ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hxs' : x ∈ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hsout' : s ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have htout' : t ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have huout' : u ∉ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hvout' : v ∉ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  rcases le_total (dist a u) (dist a v) with hp | hp <;>
    rcases le_total (dist a s) (dist a t) with ho | ho
  · exact Or.inl (same_ends_of_meeting_interiors_oriented hab hu hv hp hs ht ho hxu hxs
      hsout htout huout hvout)
  · exact Or.inr (same_ends_of_meeting_interiors_oriented hab hu hv hp ht hs ho hxu hxs'
      htout hsout huout' hvout')
  · obtain ⟨h₁, h₂⟩ := same_ends_of_meeting_interiors_oriented hab hv hu hp hs ht ho hxu' hxs
      hsout' htout' hvout huout
    exact Or.inr ⟨h₂, h₁⟩
  · obtain ⟨h₁, h₂⟩ := same_ends_of_meeting_interiors_oriented hab hv hu hp ht hs ho hxu' hxs'
      htout' hsout' hvout' huout'
    exact Or.inl ⟨h₂, h₁⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.Subdivide
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subdividing a list of segments

A polygonal edge **is** its pair of endpoints: a straight segment is determined by its ends,
so naming one by anything else names a distinction that does not exist. `Piece := Plane ×
Plane`, and the blueprint's "represent every duplicate geometric subsegment only once"
becomes deduplication of a list of *names*, with no geometry in it.

**The subdivision recurses on the POINT list, not on the segment.** `subdivide pieces points`
cuts every current piece at the head point and recurses with the rest. Read literally the
blueprint wants the cut points as data, which would need a choice operator (the meets are
existential) and then a sort (to order them along each segment). Neither is required: order
does not matter, because cutting at a point that has already become an endpoint is a no-op.

Three facts about one cut, each lifted across the piece list and then across the point list:

* `subdivide_cover` — cutting loses nothing, so a subdivision occupies what it came from;
* `subdivide_ne` — no piece degenerates, so the drawing condition's invariant survives;
* `subdivide_interior_subset` — every piece's interior lies inside the interior of a piece
  it came from. This is what makes a cut **permanent**: nothing later can put a removed point
  back into an interior.

## Blueprint

* `Piece`, `cover` — the segment representation and what a list of them occupies.
* `subdivide` and its three properties — the cutting half of Lemma 3.7 (polygonal overlay).
-/

open Metric Set

namespace Schoenflies

theorem cover_flatMap (f : Piece → List Piece) (ps : List Piece) :
    cover (ps.flatMap f) = ⋃ P ∈ ps, cover (f P) := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.flatMap_cons, cover_append, ih]; simp

/-! ### One cut -/

theorem splitAt_cover (p : Plane) (P : Piece) : cover (splitAt p P) = P.seg := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    simp only [cover_cons, cover_nil, union_empty]
    exact (segment_split hp).symm
  · simp

/-- Cutting at an interior point leaves both halves nondegenerate: an interior point differs
from both ends. -/
theorem splitAt_ne (p : Plane) {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ splitAt p P, Q.Nondeg := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ
    -- `p` is strictly inside, so it is neither end.
    have h1 : P.1 ≠ p := by
      rintro rfl
      exact hP (left_mem_openSegment_iff.1 h)
    have h2 : p ≠ P.2 := by
      rintro rfl
      exact hP (right_mem_openSegment_iff.1 h)
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h1
    · rcases List.mem_singleton.1 hQ with rfl
      exact h2
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact hP

/-- Cutting is permanent: each half's interior lies inside the whole's. -/
theorem splitAt_interior_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact openSegment_left_subset h
    · rcases List.mem_singleton.1 hQ with rfl
      exact openSegment_right_subset h
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact subset_rfl

/-- After cutting at `p`, no piece has `p` in its interior.

Nondegeneracy is needed: a degenerate piece `(p, p)` has `p` in its interior and cutting it
produces two more copies of itself. -/
theorem splitAt_avoids (p : Plane) {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ splitAt p P, p ∉ Q.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have h1 : P.1 ≠ p := by
      rintro rfl
      exact hP (left_mem_openSegment_iff.1 h)
    have h2 : p ≠ P.2 := by
      rintro rfl
      exact hP (right_mem_openSegment_iff.1 h)
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact fun hmem => h1 (right_mem_openSegment_iff.1 hmem)
    · rcases List.mem_singleton.1 hQ with rfl
      exact fun hmem => h2 (left_mem_openSegment_iff.1 hmem)
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact h

/-! ### One cut, across the whole list -/

theorem splitAllAt_cover (p : Plane) (pieces : List Piece) :
    cover (splitAllAt p pieces) = cover pieces := by
  rw [splitAllAt, cover_flatMap]
  simp only [splitAt_cover]
  rfl

theorem splitAllAt_ne (p : Plane) {pieces : List Piece} (h : ∀ P ∈ pieces, P.Nondeg) :
    ∀ Q ∈ splitAllAt p pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_ne p (h P hP) Q hQP

theorem splitAllAt_interior_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_interior_subset p P Q hQP⟩

theorem splitAllAt_avoids (p : Plane) {pieces : List Piece} (h : ∀ P ∈ pieces, P.Nondeg) :
    ∀ Q ∈ splitAllAt p pieces, p ∉ Q.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_avoids p (h P hP) Q hQP

/-! ### The subdivision -/

/-- Cutting loses nothing: a subdivision occupies exactly what it came from. -/
theorem subdivide_cover (pieces : List Piece) (points : List Plane) :
    cover (subdivide pieces points) = cover pieces := by
  induction points generalizing pieces with
  | nil => rfl
  | cons p ps ih => rw [subdivide_cons, ih, splitAllAt_cover]

/-- No piece degenerates. -/
theorem subdivide_ne {pieces : List Piece} (points : List Plane)
    (h : ∀ P ∈ pieces, P.Nondeg) : ∀ Q ∈ subdivide pieces points, Q.Nondeg := by
  induction points generalizing pieces with
  | nil => exact h
  | cons p ps ih => exact ih (splitAllAt_ne p h)

/-- Every piece's interior lies inside the interior of a piece it came from. This is what
makes a cut permanent. -/
theorem subdivide_interior_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP⟩ := splitAllAt_interior_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP⟩

/-- After subdividing, no cut point is interior to any piece. Permanence is what makes this
work: a later cut only shrinks interiors, so a point removed early stays removed. -/
theorem subdivide_avoids {pieces : List Piece} (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∀ p ∈ points, ∀ Q ∈ subdivide pieces points, p ∉ Q.interior := by
  induction points generalizing pieces with
  | nil => simp
  | cons p ps ih =>
    intro q hq Q hQ
    rcases List.mem_cons.1 hq with rfl | hq
    · -- `q` was cut out at this step; permanence keeps it out of every later piece.
      obtain ⟨R, hR, hQR⟩ := subdivide_interior_subset (splitAllAt q pieces) ps Q hQ
      exact fun hmem => splitAllAt_avoids q hnd R hR (hQR hmem)
    · exact ih (pieces := splitAllAt p pieces) (splitAllAt_ne p hnd) q hq Q hQ

end Schoenflies
end

section
-- module Solutions.Q146_CD.Overlay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygonal overlay

Finitely many segments become a plane graph once they are subdivided at their meets and each
duplicated subsegment is named once (`lem:polygonal-overlay`).

## Blueprint

* `polygonal_overlay` — Lemma 3.7 (polygonal overlay).
-/

open Metric Set

namespace Schoenflies

/-! ### Two more properties of `subdivide`

Both belong in `Schoenflies/Subdivide.lean` beside the other four; they are here because that
module is on `main`.

`subdivide_subset` is `subdivide_interior_subset` with the **closed** inclusion carried
alongside the open one, in one existential: separation reads a piece's ends off its source
segment and its interior off the source's interior, and it needs both at the same source.

`subdivide_ends` is the endpoint criterion — an end of a piece that is not a cut point was an
end all along. Without it the case of two pieces from different sources does not close: two
different subpieces can both sit inside one long overlap. -/

/-- Cutting one piece keeps each half inside the whole, closed and open at once. -/
theorem splitAt_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact ⟨(convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hp,
        openSegment_left_subset h⟩
    · rcases List.mem_singleton.1 hQ with rfl
      exact ⟨(convex_segment P.1 P.2).segment_subset hp (right_mem_segment ℝ _ _),
        openSegment_right_subset h⟩
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact ⟨subset_rfl, subset_rfl⟩

theorem splitAllAt_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_subset p P Q hQP⟩

/-- Every piece of a subdivision lies inside a piece it came from, both as a segment and as an
interior — and at the **same** source. -/
theorem subdivide_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR, hQR'⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP, hRP'⟩ := splitAllAt_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP, hQR'.trans hRP'⟩

/-- Cutting one piece introduces only the cut point as a new end. -/
theorem splitAt_ends (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, ∀ z, (z = Q.1 ∨ z = Q.2) → z = p ∨ (z = P.1 ∨ z = P.2) := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ z hz
    rcases List.mem_cons.1 hQ with rfl | hQ
    · rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · rcases List.mem_singleton.1 hQ with rfl
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
  · intro Q hQ z hz
    rcases List.mem_singleton.1 hQ with rfl
    exact Or.inr hz

theorem splitAllAt_ends (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z = p ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  intro Q hQ z hz
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  rcases splitAt_ends p P Q hQP z hz with h | h
  · exact Or.inl h
  · exact Or.inr ⟨P, hP, h⟩

/-- **The endpoint criterion.** An end of a piece of the subdivision is either a cut point or
was an end of a source piece all along. -/
theorem subdivide_ends (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z ∈ points ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ z hz => Or.inr ⟨Q, hQ, hz⟩
  | cons p ps ih =>
    intro Q hQ z hz
    rcases ih (pieces := splitAllAt p pieces) Q hQ z hz with h | ⟨R, hR, hzR⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases splitAllAt_ends p pieces R hR z hzR with rfl | ⟨P, hP, hzP⟩
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr ⟨P, hP, hzP⟩

/-! ### What the cut points have to cover

Two conditions, and between them they are the blueprint's "subdivide at all old endpoints,
isolated intersections, and endpoints of overlapping intervals". The second asks for **some**
pair of ends of each meet rather than every pair, because that is what a construction can
supply: a meet is `segment ℝ u v` and `segment ℝ v u` alike, and that a nondegenerate
segment's ends are determined by its point set is a theorem this development does not have and
does not need. -/

/-- For every pair of distinct source pieces that meet, some pair of ends of the meet is
cut. -/
def MeetsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ Q ∈ pieces, P ≠ Q → (meetOf P Q).Nonempty →
    ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points

/-- With the source ends cut too, the endpoint criterion says outright that every end of every
piece of the subdivision is a cut point. -/
theorem subdivide_ends_are_cuts {pieces : List Piece} {points : List Plane}
    (h : EndsAreCut pieces points) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) → z ∈ points := by
  intro Q hQ z hz
  rcases subdivide_ends pieces points Q hQ z hz with h' | ⟨P, hP, hzP⟩
  · exact h'
  · exact h P hP z hzP

/-! ### Producing the cut points

Nothing computes them. The overlay is stated existentially, so the list is built by the
induction that proves it exists, and `segment_inter_segment` hands over the ends of a meet the
moment the meet is known to be nonempty. That is what keeps the choice operator out: the
witnesses of `segment_inter_segment` are not unique, so there is nothing to name. -/

/-- One piece against a list: a point list holding both ends of every meet. -/
theorem exists_meet_points (P : Piece) (others : List Piece) :
    ∃ points : List Plane, ∀ Q ∈ others, (meetOf P Q).Nonempty →
      ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points := by
  induction others with
  | nil => exact ⟨[], by simp⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, htail⟩ := ih
    by_cases hR : (meetOf P R).Nonempty
    · obtain ⟨u, v, huv⟩ := segment_inter_segment P.1 P.2 R.1 R.2 hR
      refine ⟨u :: v :: tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact ⟨u, v, huv, by simp, by simp⟩
      · obtain ⟨s, t, hst, hs, ht⟩ := htail Q hQ hne
        exact ⟨s, t, hst, by simp [hs], by simp [ht]⟩
    · refine ⟨tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact absurd hne hR
      · exact htail Q hQ hne

/-- The whole list: the ends of each piece, and both ends of each meet. No sort and no choice
operator — the point list is existential throughout. -/
theorem exists_cut_points (pieces : List Piece) :
    ∃ points : List Plane, EndsAreCut pieces points ∧ MeetsAreCut pieces points := by
  induction pieces with
  | nil => exact ⟨[], by simp [EndsAreCut], by simp [MeetsAreCut]⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, hEnds, hMeets⟩ := ih
    obtain ⟨meetPoints, hHead⟩ := exists_meet_points R rs
    refine ⟨R.1 :: R.2 :: (meetPoints ++ tailPoints), fun P hP z hz => ?_,
      fun P hP Q hQ hPQ hne => ?_⟩
    · -- The head's two ends open the list; the tail's ends are already in `tailPoints`.
      rcases List.mem_cons.1 hP with rfl | hPt
      · rcases hz with rfl | rfl <;> simp
      · have := hEnds P hPt z hz
        simp [this]
    · -- A pair involving the head is covered by `meetPoints`, in whichever order it is asked
      -- for; a pair inside the tail was covered already.
      rcases List.mem_cons.1 hP with hPh | hPt
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · exact absurd (hPh.trans hQh.symm) hPQ
        · subst hPh
          obtain ⟨u, v, huv, hu, hv⟩ := hHead Q hQt hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · subst hQh
          have hne' : (meetOf Q P).Nonempty := by rwa [meetOf_comm]
          obtain ⟨u, v, huv, hu, hv⟩ := hHead P hPt hne'
          exact ⟨u, v, by rw [meetOf_comm]; exact huv, by simp [hu], by simp [hv]⟩
        · obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hPt Q hQt hPQ hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩

/-! ### Separation

Cut at every end of every source piece and at both ends of every meet, and two pieces of the
subdivision that share an interior point are the **same** segment — equal, not disjoint.
Overlapping collinear pieces cannot be pulled apart by cutting; after enough cuts they
coincide, which is what the blueprint's deduplication clause is for. -/

/-- Collinearity: two pieces of the subdivision that share an interior point lie inside one
nondegenerate segment. If they came from the same source piece, that piece; if from different
ones, the sources' overlap — nondegenerate because the shared point is interior to it, the
overlap's ends being cut points and so interior to nothing. -/
theorem subdivide_common_segment {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    ∃ A : Piece, A.Nondeg ∧ P.seg ⊆ A.seg ∧ Q.seg ⊆ A.seg := by
  obtain ⟨p, hp, hPseg, hPint⟩ := subdivide_subset pieces points P hP
  obtain ⟨q, hq, hQseg, hQint⟩ := subdivide_subset pieces points Q hQ
  by_cases hpq : p = q
  · subst hpq
    exact ⟨p, hnd p hp, hPseg, hQseg⟩
  -- The sources meet at `x`, so their meet is a segment with both ends cut.
  have hxp : x ∈ p.seg := openSegment_subset_segment ℝ _ _ (hPint hxP)
  have hxq : x ∈ q.seg := openSegment_subset_segment ℝ _ _ (hQint hxQ)
  obtain ⟨u, v, huv, hu, hv⟩ := hMeets p hp q hq hpq ⟨x, hxp, hxq⟩
  have hux : u ∉ P.interior := subdivide_avoids points hnd u hu P hP
  have hvx : v ∉ P.interior := subdivide_avoids points hnd v hv P hP
  have huy : u ∉ Q.interior := subdivide_avoids points hnd u hu Q hQ
  have hvy : v ∉ Q.interior := subdivide_avoids points hnd v hv Q hQ
  -- `x` is interior to the meet: it lies on it, and it is neither of its ends.
  have hxuv : x ∈ segment ℝ u v := huv ▸ ⟨hxp, hxq⟩
  have hxu : u ≠ x := fun h => hux (h ▸ hxP)
  have hxv : v ≠ x := fun h => hvx (h ▸ hxP)
  have hxopen : x ∈ openSegment ℝ u v := mem_openSegment_of_ne_left_right hxu hxv hxuv
  have huvne : u ≠ v := by
    rintro rfl
    rw [openSegment_same, mem_singleton_iff] at hxopen
    exact hxu hxopen.symm
  -- Both ends of the meet lie on both sources, so each one-dimensional citation has its
  -- ambient segment.
  have hsubp : segment ℝ u v ⊆ p.seg := huv ▸ inter_subset_left
  have hsubq : segment ℝ u v ⊆ q.seg := huv ▸ inter_subset_right
  refine ⟨(u, v), huvne, ?_, ?_⟩
  · exact segment_inside_of_ends_outside (hnd p hp)
      (hPseg (left_mem_segment ℝ _ _)) (hPseg (right_mem_segment ℝ _ _))
      (hsubp (left_mem_segment ℝ _ _)) (hsubp (right_mem_segment ℝ _ _))
      hxP hxopen hux hvx
  · exact segment_inside_of_ends_outside (hnd q hq)
      (hQseg (left_mem_segment ℝ _ _)) (hQseg (right_mem_segment ℝ _ _))
      (hsubq (left_mem_segment ℝ _ _)) (hsubq (right_mem_segment ℝ _ _))
      hxQ hxopen huy hvy

/-- **Separation.** Two pieces of the subdivision that share an interior point are the same
segment, in one order or the other. -/
theorem subdivide_separated {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    P = Q ∨ P = (Q.2, Q.1) := by
  -- Every end of every piece is a cut point, hence interior to nothing.
  have cut : ∀ R ∈ subdivide pieces points, ∀ z, (z = R.1 ∨ z = R.2) → z ∈ points :=
    subdivide_ends_are_cuts hEnds
  have h₁ : Q.1 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inl rfl)) P hP
  have h₂ : Q.2 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inr rfl)) P hP
  have h₃ : P.1 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inl rfl)) Q hQ
  have h₄ : P.2 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inr rfl)) Q hQ
  obtain ⟨A, hA, hPA, hQA⟩ := subdivide_common_segment hnd hMeets hP hQ hxP hxQ
  rcases same_ends_of_meeting_interiors hA
      (hPA (left_mem_segment ℝ _ _)) (hPA (right_mem_segment ℝ _ _))
      (hQA (left_mem_segment ℝ _ _)) (hQA (right_mem_segment ℝ _ _))
      hxP hxQ h₁ h₂ h₃ h₄ with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · exact Or.inl (Prod.ext e₁ e₂)
  · exact Or.inr (Prod.ext e₁ e₂)

end Schoenflies
end

section
-- module Solutions.Q146_CD.OverlayGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygonal overlay, assembled into a plane graph

`Schoenflies/Overlay.lean` does the separating half of `lem:polygonal-overlay`: after cutting
at the right points, two pieces of the subdivision whose interiors meet are the **same
segment**, in one order or the other. This module turns that into a plane graph.

The only thing standing between "the same segment" and "the same edge" is that a segment has
two names, `(a, b)` and `(b, a)`. `orientPiece` removes the choice by fixing a total order on
plane points — `Precedes`, lexicographic in the coordinates — and putting the smaller end
first. Two names for one segment then orient to the *same* name, so "represent each duplicated
subsegment once" stops being deduplication up to reversal and becomes deduplication up to
equality, which `List.dedup` does without knowing any geometry. Nothing geometric rests on
which order it is: only `precedes_total` and `eq_of_precedes_of_precedes` are ever used.

The graph is `overlayGraph`, a `Graph Plane Piece`: its edges are the oriented, deduplicated
pieces, and its vertices are their ends. `IsLink P x y` says that `P` is an edge and that `x`
and `y` are its two ends in one order or the other — which is why
`eq_or_eq_of_isLink_of_isLink` is a two-line case split rather than an argument.

The three clauses of `Graph.IsDrawing` come out as follows.

* *Each edge is drawn by an arc between its ends* — `isArcBetween_segment`, given
  nondegeneracy, which `subdivide_ne` preserves and orienting does not disturb.
* *An edge's arc meets the vertex set only at its own ends* — a vertex is an end of some
  edge, hence a cut point, and `subdivide_avoids` says a cut point is interior to nothing.
* *Distinct edges meet only at shared vertices* — a common point that is an end of neither
  would be interior to both, and `subdivide_separated` would make the two pieces the same
  segment, hence (after orienting) the same name. Once it is an end of one it is a cut point,
  so it cannot be interior to the other either, and it is an end of both.

## Blueprint

* `Precedes`, `orientPiece` — the canonical orientation of a segment.
* `overlayPieces`, `overlayGraph`, `segmentDrawing` — the graph of Lemma 3.7.
* `polygonal_overlay` — Lemma 3.7 (polygonal overlay), the whole statement.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### A total order on plane points

It exists to pick one of two points canonically. Only two facts about it are used: that it
compares any two points, and that it cannot rank two distinct points both ways round. -/

/-! ### The canonical orientation of a piece -/

/-- Nor which points are its ends. -/
theorem orientPiece_ends (P : Piece) (z : Plane) :
    (z = (orientPiece P).1 ∨ z = (orientPiece P).2) ↔ (z = P.1 ∨ z = P.2) := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact or_comm

/-! ### Deduplication

`cover` only sees which pieces are in the list, so both steps of the assembly — orienting and
deduplicating — leave it alone. -/

theorem cover_eq_of_mem_iff {l₁ l₂ : List Piece} (h : ∀ P, P ∈ l₁ ↔ P ∈ l₂) :
    cover l₁ = cover l₂ := by
  ext x
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hx⟩ => ⟨P, (h P).1 hP, hx⟩, fun ⟨P, hP, hx⟩ => ⟨P, (h P).2 hP, hx⟩⟩

theorem mem_overlayPieces {pieces : List Piece} {points : List Plane} {P : Piece} :
    P ∈ overlayPieces pieces points ↔ ∃ Q ∈ subdivide pieces points, orientPiece Q = P := by
  rw [overlayPieces, List.mem_dedup, List.mem_map]

/-- Neither orienting nor deduplicating changes what the pieces occupy. -/
theorem overlayPieces_cover (pieces : List Piece) (points : List Plane) :
    cover (overlayPieces pieces points) = cover pieces := by
  rw [overlayPieces,
    cover_eq_of_mem_iff (l₂ := (subdivide pieces points).map orientPiece) fun _ => List.mem_dedup,
    cover_map_orientPiece, subdivide_cover]

theorem overlayPieces_nondeg {pieces : List Piece} (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) : ∀ P ∈ overlayPieces pieces points, P.Nondeg := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  exact orientPiece_nondeg (subdivide_ne points hnd Q hQ)

/-- Every end of every edge is a cut point: orienting does not change which points are ends,
and `subdivide_ends_are_cuts` covers the subdivision. -/
theorem overlayPieces_ends_cut {pieces : List Piece} {points : List Plane}
    (hEnds : EndsAreCut pieces points) :
    ∀ P ∈ overlayPieces pieces points, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points := by
  intro P hP z hz
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  exact subdivide_ends_are_cuts hEnds Q hQ z ((orientPiece_ends Q z).1 hz)

/-- And a cut point is interior to no edge. -/
theorem overlayPieces_avoids {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∀ p ∈ points, ∀ P ∈ overlayPieces pieces points, p ∉ P.interior := by
  intro p hp P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  rw [orientPiece_interior]
  exact subdivide_avoids points hnd p hp Q hQ

/-- **Distinct edges have disjoint interiors.** This is where separation is spent: two pieces
sharing an interior point are the same segment, so after orienting they are the same *name*,
and a deduplicated list holds a name once. -/
theorem overlayPieces_disjoint_interiors {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) {P Q : Piece}
    (hP : P ∈ overlayPieces pieces points) (hQ : Q ∈ overlayPieces pieces points)
    (hPQ : P ≠ Q) {x : Plane} (hxP : x ∈ P.interior) : x ∉ Q.interior := by
  intro hxQ
  obtain ⟨P', hP', rfl⟩ := mem_overlayPieces.1 hP
  obtain ⟨Q', hQ', rfl⟩ := mem_overlayPieces.1 hQ
  rw [orientPiece_interior] at hxP hxQ
  rcases subdivide_separated hnd hEnds hMeets hP' hQ' hxP hxQ with h | h
  · exact hPQ (by rw [h])
  · exact hPQ (by rw [h, orientPiece_swap])

/-! ### The graph -/

variable {pieces : List Piece} {points : List Plane} {P : Piece} {x y v : Plane}

/-! ### The drawing

A straight edge is drawn by the affine parametrization of its segment, so the arc clause of
`IsDrawing` is `isArcBetween_segment` and nothing else. -/

/-! ### Finiteness

Without this the whole face and outer-face machinery of `Schoenflies/Graph/Drawing.lean` and
`Schoenflies/Graph/OuterFace.lean` is inapplicable to the overlay, since every statement there
carries a `[G.Finite]` instance. Both sets come from one finite list, so it is immediate — but
it has to be said, and the instance has to be found by typeclass search at the call site. -/

theorem finite_endSet (edges : List Piece) : (endSet edges).Finite := by
  -- The end set is the image of a finite list under the two projections.
  have : endSet edges ⊆ (fun P : Piece => P.1) '' {P | P ∈ edges}
      ∪ (fun P : Piece => P.2) '' {P | P ∈ edges} := by
    rintro v ⟨P, hP, rfl | rfl⟩
    · exact Or.inl ⟨P, hP, rfl⟩
    · exact Or.inr ⟨P, hP, rfl⟩
  exact Set.Finite.subset
    ((edges.finite_toSet.image _).union (edges.finite_toSet.image _)) this

end Schoenflies
end

section
-- module Solutions.Q146_CD.SimpleArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Simple polygonal arcs

`Schoenflies/PolyPath.lean` joins two points of a region by a polygonal *path* — a vertex list
whose carrier stays inside the region. A path may cross itself, so it is not an arc. This
module supplies the missing half of Lemma 1.1 and, with it, Lemma 1.2, by running the
blueprint's recipe: *subdivide at all intersections, delete duplicate subsegments, and take a
simple path in the resulting finite graph.*

The three steps are already available.

* Subdividing and deduplicating is `Schoenflies.overlayGraph`: a finite list of nondegenerate
  segments becomes a finite plane graph whose point set is exactly their union
  (`Schoenflies.overlayGraph_pointSet`).
* A simple path in that graph is `Graph.IsPath`, produced by `Graph.Reaches.exists_isPath`.
* Its realisation is an arc between its ends, by `Graph.IsDrawing.path_isArcBetween`.

## What actually has to be proved here

Two things, and neither is in the list above.

**The graph is connected when the union is.** The overlay is built from geometry, so nothing
so far says that two points joined *in the plane* are joined *along edges*. The argument is a
clopen one: for a vertex `a`, the points carried by the edges the walk relation can reach from
`a` form a compact set, the points carried by the other edges form another, the two are
disjoint — a common point would be a vertex incident with edges from both classes, by the
drawing condition — and together they are the whole union. Preconnectedness then forces the
second class to carry nothing.

**The realisation of a path is `poly` of a vertex list.** `Graph.IsDrawing.path_isArcBetween`
delivers `Graph.edgesCover`, a union of edge arcs with no order in it, while `IsPolygonal` and
every polygonal consumer downstream want a vertex list. `Schoenflies.exists_poly_eq_edgesCover`
recovers one by induction along the walk. Its statement returns the list, not the bare
existence of *some* polygonal set, so a consumer that needs the vertices — the redrawing
argument does — still has them.

Both endpoints have to be vertices of the overlay, which is arranged by putting them on the
list of cut points: `EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in
that list, so lengthening it is free.

## Blueprint

* `Schoenflies.segsOf`, `Schoenflies.cover_segsOf` — a vertex list read as a list of
  nondegenerate segments, the input format the overlay wants.
* `Schoenflies.overlayGraph_reaches` — the overlay graph of a connected union is connected.
* `Schoenflies.exists_simple_poly_of_cover` — Lemma 1.2 (finite polygonal unions), for a union
  given as a finite list of nondegenerate segments.
* `Schoenflies.exists_simple_poly_of_poly`, `Schoenflies.exists_simple_poly_of_isPolygonal` —
  Lemma 1.2 for a set presented as a polygonal carrier.
* `Schoenflies.exists_simple_poly_of_biUnion`, `Schoenflies.exists_simple_poly_of_union` —
  Lemma 1.2 as the blueprint states it, for a finite union of polygonal sets.
* `Schoenflies.exists_simple_poly_of_isPreconnected`,
  `Schoenflies.exists_simple_arc_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), in
  full: any two points of a region are joined in it by a *simple* polygonal arc.

## Two lemmas that belong elsewhere

`Schoenflies.cover_flatMap_list` generalises `Schoenflies.cover_flatMap` to an arbitrary index
list and belongs beside it in `Schoenflies/Subdivide.lean`; `Schoenflies.subset_of_finite_diff`
is a general fact about preconnected sets. Both are here only because their homes are on
`main`.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {Ω : Set Plane} {a b x y : Plane}

/-! ### One more shape of `poly`

`poly_cons_cons` peels a segment off a list of length at least two. The overlay's induction
peels one off a list known only to be nonempty, so it needs the head as a term rather than as
a pattern. -/

/-! ### The segments of a vertex list

`poly` is a *chain*: consecutive vertices, with repetitions allowed. The overlay takes a list
of pieces and insists that each be nondegenerate, so a repetition has to be dropped rather
than passed on. Dropping one is harmless — a degenerate segment is a single point, and that
point is an end of the neighbouring segment — except when the whole chain degenerates to a
point, which is the second disjunct of `cover_segsOf`. -/

open scoped Classical in
theorem segsOf_cons_cons (u v : Plane) (rest : List Plane) :
    segsOf (u :: v :: rest) =
      if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest) := rfl

/-- Every segment produced is nondegenerate — which is the whole point of the definition. -/
theorem segsOf_nondeg (vs : List Plane) : ∀ P ∈ segsOf vs, P.Nondeg := by
  classical
  induction vs with
  | nil => simp
  | cons u tl ih =>
    match tl, ih with
    | [], _ => simp
    | v :: rest, ih =>
      rw [segsOf_cons_cons]
      split_ifs with huv
      · exact ih
      · intro P hP
        rcases List.mem_cons.1 hP with rfl | hP
        · exact huv
        · exact ih P hP

/-- The segments of a chain occupy the chain — unless the chain has collapsed to a point (or
to nothing), in which case there are no segments at all. -/
theorem cover_segsOf (vs : List Plane) :
    cover (segsOf vs) = poly vs ∨ (segsOf vs = [] ∧ (poly vs).Subsingleton) := by
  classical
  induction vs with
  | nil => exact Or.inr ⟨rfl, by simp⟩
  | cons u tl ih =>
    match tl, ih with
    | [], _ => exact Or.inr ⟨rfl, by simp [Set.Subsingleton]⟩
    | v :: rest, ih =>
      rw [segsOf_cons_cons, poly_cons_cons]
      by_cases huv : u = v
      · -- A repeated vertex contributes the point `u`, which the rest of the chain already
        -- holds.
        subst huv
        rw [if_pos rfl, segment_same]
        have hmem : u ∈ poly (u :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
        rcases ih with h | ⟨h1, h2⟩
        · exact Or.inl (by rw [h, union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)])
        · refine Or.inr ⟨h1, ?_⟩
          rw [union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)]
          exact h2
      · rw [if_neg huv, cover_cons]
        refine Or.inl ?_
        rcases ih with h | ⟨h1, h2⟩
        · rw [h]; rfl
        · -- The rest of the chain is the single point `v`, already an end of the new segment.
          rw [h1, cover_nil, union_empty,
            h2.eq_singleton_of_mem (mem_poly_of_mem (List.mem_cons_self ..)),
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))]
          rfl

/-- When a chain carries two distinct points it has not collapsed, so its segments occupy
exactly it. -/
theorem cover_segsOf_eq {vs : List Plane} (ha : a ∈ poly vs) (hb : b ∈ poly vs)
    (hab : a ≠ b) : cover (segsOf vs) = poly vs := by
  rcases cover_segsOf vs with h | ⟨-, h⟩
  · exact h
  · exact absurd (h ha hb) hab

/-! ### The realisation of a walk is a polygonal chain

`Graph.edgesCover` is a union with no order in it. The walk supplies the order, and the
induction reads the vertex list off it. -/

/-! ### The overlay graph of a connected union is connected

Nothing built so far relates the plane topology of the union to the walk relation of the
graph. This is where they meet. -/

/-! ### Lemma 1.2, and then Lemma 1.1 -/

/-! ### A finite union of polygonal arcs

The blueprint states Lemma 1.2 for a finite union, which `Schoenflies.cover` already is. The
only thing standing between the two readings is that a member of the union may have collapsed
to a single point, contributing no segment at all. A collapsed member is harmless: were its
point missing from the segments, it would be clopen in the union, which a connected set with
more than one point does not tolerate. -/

/-- Peeling the head off a union indexed by a list. -/
theorem biUnion_list_cons {α : Type*} (f : α → Set Plane) (x : α) (l : List α) :
    (⋃ y ∈ x :: l, f y) = f x ∪ ⋃ y ∈ l, f y := by
  ext z
  simp only [mem_iUnion, exists_prop, List.mem_cons, mem_union]
  constructor
  · rintro ⟨y, rfl | hy, hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨y, hy, hz⟩
  · rintro (hz | ⟨y, hy, hz⟩)
    · exact ⟨x, Or.inl rfl, hz⟩
    · exact ⟨y, Or.inr hy, hz⟩

/-- `Schoenflies.cover_flatMap`, over an arbitrary index list rather than a list of pieces.
Belongs beside it in `Schoenflies/Subdivide.lean`; it is here because that module is on
`main`. -/
theorem cover_flatMap_list {α : Type*} (f : α → List Piece) (l : List α) :
    cover (l.flatMap f) = ⋃ x ∈ l, cover (f x) := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.flatMap_cons, cover_append, ih, biUnion_list_cons]

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_OuterFace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The outer face

Exactly one face of a finite plane graph is unbounded.

The plane fact this needs is not "the exterior of a large disk is connected" but the exterior
of a *square*, and that one is elementary — `Plane.isConnected_beyondSquare`, four convex
half-planes with consecutive ones sharing a corner. The disk version is what would have
needed a traversal of the circle, which a trigonometry-free development withholds.

No face is produced as data: a face is named by a point of it, as `Graph.face` always has
been, so "the outer face" is "the face through any point far enough out".

## Blueprint

* `exists_unbounded_face` — some face is unbounded.
* `unbounded_face_unique` — any two unbounded faces coincide.
* `beyondSquare_subset_face` — an unbounded face swallows the whole outside of any square
  containing the drawing. This is the working form: it is how one proves a given point lies in
  the outer face.
-/

open Metric Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A square containing the whole drawing. -/
theorem IsDrawing.exists_closedSquare [G.Finite] (h : IsDrawing G drawing) :
    ∃ r : ℝ, 0 ≤ r ∧ pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r :=
  Schoenflies.Plane.exists_closedSquare_of_isBounded h.isCompact_pointSet.isBounded

end Graph
end

section
-- module Solutions.Q146_CD.ModelCurve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The model curve, and the parametrization of a Jordan curve by it

The blueprint's model curve is `S = ∂Q`, the boundary of the square `Q = [-1,1]²`, and *not*
the unit circle. That is a deliberate choice: this development is trigonometry-free, so a
traversal of the round circle by an interval is unavailable, whereas `S` is four segments
glued end to end and each segment is an arc by `isArcBetween_segment`. The blueprint says so
explicitly ("Nothing in this document needs the unit circle in place of `S`").

`modelCurve` is defined by the sup norm, `‖x‖∞ = 1`, which is the same square the rest of the
development already speaks about (`Plane.closedSquare 0 1`), and it is cut into its four sides
by `modelCurve_eq_sides`.

## The content of Lemma 3.1

The lemma has three clauses. Only the first is proved here; the other two are already on
`main`, transported along the homeomorphism the first clause supplies:

* *"`γ` induces a homeomorphism from `S` onto `C`"* — `isJordanCurve_modelCurve` together with
  `IsJordanCurve.homeomorph_modelCurve`. The general fact behind it is `IsLoop.exists_homeomorph`:
  a loop is a quotient map of `[0,1]` which identifies exactly `0` with `1`, so *any two* loops
  induce a homeomorphism between their images, matching parameter for parameter.
* *"two distinct points divide `C` into two simple arcs meeting exactly in those points"* — this
  is `IsJordanCurve.two_arcs` in `Schoenflies/TwoArcs.lean`, proved directly on the parameter
  interval, which is strictly stronger than transporting it from `S`.
* *"the relatively open subarcs form a basis of the subspace topology"* — `openArc_isRelOpen`,
  `openArc_subarc_isRelOpen` and `basic_piece_inside_ball` in `Schoenflies/Subarc.lean`.

The route to the homeomorphism is the blueprint's, with the sequence argument replaced by its
point-set content: `t ↦ γ t` is a continuous surjection from the compact `[0,1]` onto the
Hausdorff `C`, hence a closed map, hence a *quotient* map; so a map out of `C` is continuous as
soon as its composite with the parametrization is. That is exactly what the blueprint's
subsequence chase establishes, and it is one line here.

## Blueprint

* `modelCurve` — Lemma 3.1, the model curve `S = ∂Q` with `Q = [-1,1]²`.
* `modelCurve_eq_sides` — the decomposition of `S` into its four sides.
* `modelCurve_eq_frontier` — `S` is literally the topological boundary of `Q`.
* `isJordanCurve_modelCurve` — `S` is a Jordan curve.
* `IsLoop.param_eq_or`, `IsLoop.eq_of_eq` — a loop identifies exactly the two endpoints of the
  parameter interval.
* `IsLoop.exists_homeomorph` — two loops induce a homeomorphism of their images.
* `IsJordanCurve.homeomorph`, `IsJordanCurve.homeomorph_modelCurve`,
  `IsJordanCurve.modelCurve_homeomorph` — Lemma 3.1, first clause.
-/

open Set Topology unitInterval

namespace Schoenflies

/-! ### Segments with a constant coordinate

The four sides of the square are axis-parallel, so each is pinned by one coordinate and swept
by the other. Two lemmas serve all four. -/

/-- A horizontal segment: constant second coordinate, first coordinate sweeping a real
segment. -/
theorem mem_segment_horiz {u v c : ℝ} {x : Plane} :
    x ∈ segment ℝ (Plane.mk u c) (Plane.mk v c) ↔ x 1 = c ∧ x 0 ∈ segment ℝ u v := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨?_, p, q, hp, hq, hpq, ?_⟩
    · rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one]
      linear_combination c * hpq
    · rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero]
      simp [smul_eq_mul]
  · rintro ⟨hx1, p, q, hp, hq, hpq, hx0⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    ext i
    fin_cases i
    · change (p • Plane.mk u c + q • Plane.mk v c) 0 = x 0
      rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero, ← hx0]
      simp [smul_eq_mul]
    · change (p • Plane.mk u c + q • Plane.mk v c) 1 = x 1
      rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one, hx1]
      linear_combination c * hpq

/-- A vertical segment: constant first coordinate, second coordinate sweeping a real
segment. -/
theorem mem_segment_vert {c u v : ℝ} {x : Plane} :
    x ∈ segment ℝ (Plane.mk c u) (Plane.mk c v) ↔ x 0 = c ∧ x 1 ∈ segment ℝ u v := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨?_, p, q, hp, hq, hpq, ?_⟩
    · rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero]
      linear_combination c * hpq
    · rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one]
      simp [smul_eq_mul]
  · rintro ⟨hx0, p, q, hp, hq, hpq, hx1⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    ext i
    fin_cases i
    · change (p • Plane.mk c u + q • Plane.mk c v) 0 = x 0
      rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero, hx0]
      linear_combination c * hpq
    · change (p • Plane.mk c u + q • Plane.mk c v) 1 = x 1
      rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one, ← hx1]
      simp [smul_eq_mul]

/-! ### The model curve and its four sides -/

/-! ### The model curve is a Jordan curve -/

/-! ### The model curve is the boundary of the square

This is the blueprint's description `S = ∂Q` with `Q = [-1,1]²`, and the check that the sup-norm
definition above is the intended one. The only content is that a point of sup norm exactly `1`
is *not* interior to the square: scaling it out by a factor `1 + δ` leaves the square while
moving an arbitrarily small distance. -/

/-! ### A loop identifies exactly the ends of the parameter interval -/

/-! ### Lemma 3.1: parametrization by the model curve -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Moving an interior point of the square

The pointed form of the bounded theorem needs a self-homeomorphism of the closed square that
fixes the boundary pointwise and carries one prescribed interior point to another. The
blueprint builds it by coning: the four triangles `conv {x, vᵢ, vᵢ₊₁}` triangulate the square,
and the affine map of each onto `conv {y, vᵢ, vᵢ₊₁}` fixing the two corners pastes with its
neighbours along the radial edges.

The construction here is the same map in different coordinates, and it is written so that no
pasting of four affine pieces is needed. It is the composite of two *shears*. A shear bends
one coordinate by the piecewise-linear self-map of `[-r, r]` that fixes the two endpoints and
moves a chosen breakpoint (`bend`), with a displacement that is scaled by a tent function of
the *other* coordinate (`tent`), so that it dies away to zero on the two transverse sides of
the square. The first shear moves the first coordinate of `x` to that of `y`, the second moves
the second coordinate.

Two features make this cheap. Writing the tent as a minimum of two affine functions makes it
continuous with no case split at all. And the family of shears is closed under inversion: the
shear with displacement parameters `k, k'` is undone by the shear with parameters `k + k',
-k'`, so bijectivity and the continuity of the inverse come from one composition identity
(`bend_bend`) instead of from a compactness argument, and no map has to be inverted by hand.

## Blueprint

* `Plane.exists_squareMover` — Lemma (Moving an interior point of the square): for interior
  points `x`, `y` of the square there are mutually inverse boundary-fixing self-maps `M`, `N`
  of the closed square with `M x = y`. `Plane.IsSquareMover` bundles the properties that make
  `M` a homeomorphism of the square onto itself, `Plane.IsSquareMover.homeomorph` repackages
  it as a `Homeomorph`, and `Plane.IsSquareMover.eqOn_frontier` states the boundary condition
  against the topological frontier, which `Plane.frontier_closedSquare` identifies with the
  blueprint's boundary square `S`.
* `Plane.iInter_eq_singleton_of_mem_tail` — the point-set kernel of Proposition (Skeleton
  agreement). The proposition itself is not statable in the present development; see the
  section comment at that lemma for exactly what is and is not proved.

Supporting material, of independent use: `Plane.tent` and `Plane.bend` with their algebra,
`Plane.continuousOn_bend`, the coordinate lemmas `Plane.abs_sub_le_supDist`,
`Plane.supDist_le_of_forall`, `Plane.exists_abs_sub_eq_of_supDist_eq`,
and `Plane.interior_closedSquare`.
-/

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### The tent function -/

variable {r p q u : ℝ}

/-! ### Bending an interval -/

/-! ### Coordinates of the square -/

/-! ### Shearing the square along one coordinate -/

variable {c : Plane} {a b k k' : ℝ} {i j l : Fin 2} {z : Plane}

/-! ### Movers of the square -/

/-- `M` and `N` are mutually inverse self-homeomorphisms of the closed square about `c` of
radius `r`, each fixing its boundary pointwise. This is the "homeomorphism of `Q` fixing `S`"
of the blueprint, written without the `Homeomorph` bundle; `IsSquareMover.homeomorph`
repackages it as one. -/
structure IsSquareMover (c : Plane) (r : ℝ) (M N : Plane → Plane) : Prop where
  /-- `M` maps the square to itself -/
  mapsTo : MapsTo M (closedSquare c r) (closedSquare c r)
  /-- `N` maps the square to itself -/
  mapsTo_inv : MapsTo N (closedSquare c r) (closedSquare c r)
  /-- `M` is continuous on the square -/
  continuousOn : ContinuousOn M (closedSquare c r)
  /-- `N` is continuous on the square -/
  continuousOn_inv : ContinuousOn N (closedSquare c r)
  /-- the two are mutually inverse there -/
  invOn : InvOn N M (closedSquare c r) (closedSquare c r)
  /-- `M` fixes the boundary pointwise -/
  fixes : ∀ z ∈ closedSquare c r, supDist z c = r → M z = z
  /-- `N` fixes the boundary pointwise -/
  fixes_inv : ∀ z ∈ closedSquare c r, supDist z c = r → N z = z

/-! ### Moving an interior point -/

/-! ### The boundary of the square -/

/-! ### The mover as a homeomorphism -/

/-- A mover of the square, packaged as a self-homeomorphism of the closed square. -/
noncomputable def IsSquareMover.homeomorph {M N : Plane → Plane} (h : IsSquareMover c r M N) :
    closedSquare c r ≃ₜ closedSquare c r where
  toFun z := ⟨M z, h.mapsTo z.2⟩
  invFun z := ⟨N z, h.mapsTo_inv z.2⟩
  left_inv z := Subtype.ext (h.invOn.1 z.2)
  right_inv z := Subtype.ext (h.invOn.2 z.2)
  continuous_toFun := h.continuousOn.restrict.subtype_mk _
  continuous_invFun := h.continuousOn_inv.restrict.subtype_mk _

@[simp] theorem IsSquareMover.homeomorph_apply {M N : Plane → Plane}
    (h : IsSquareMover c r M N) (z : closedSquare c r) :
    (h.homeomorph z : Plane) = M z := rfl

@[simp] theorem IsSquareMover.homeomorph_symm_apply {M N : Plane → Plane}
    (h : IsSquareMover c r M N) (z : closedSquare c r) :
    (h.homeomorph.symm z : Plane) = N z := rfl

/-! ### The point-set kernel of skeleton agreement

The blueprint's Proposition (Skeleton agreement) says that the limit map `F`, defined at `x`
as the unique point of the nested intersection `⋂ n, T n x` of closed target stars, agrees
with every finite skeleton map: if `x ∈ G_N ∩ D` then `F x = g_N x`. Its proof is one line of
point-set topology once the combinatorics is in place — the value `g_N x` lies in `T n x` for
every `n ≥ N`, hence in the intersection, hence is *the* point of the intersection.

That one line is what follows. The proposition itself cannot be stated in this development
yet: matched cell structures, carriers, stars, the skeleton homeomorphisms `g_n` and the limit
map `F` do not exist here. What is proved is exactly the implication the proposition rests on,
with the nested stars as an abstract antitone sequence of shrinking compacta and `g_N x` as an
abstract point of all late terms. -/

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.ArcComplementPrep
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Scaffolding for the arc-complement theorem

`thm:arc-complement` — a simple arc does not separate the plane — is proved by covering the
arc with a chain of small axis-parallel squares, overlaying their boundaries into one plane
graph `G`, and showing that the two given points lie in the outer face of `G`, which is then
disjoint from the arc. This module builds everything in that proof that does **not** need the
outer-chain lemma (`lem:outer-chain`), so that the theorem itself becomes a short assembly.

## What is here

1. *The square boundary as a polygon.* `Schoenflies.squarePolygon c hr : ClosedPolygon 1` is
   the axis-parallel square of `ℓ^∞`-radius `r` about `c`, presented the way the parity and
   overlay machinery consume a polygon — as a `ClosedPolygon`, not as a set. Its carrier is
   `frontier (Plane.closedSquare c r)` (`carrier_squarePolygon`), and the polygonal Jordan
   curve theorem then hands over that this frontier is a Jordan curve, is polygonal, and is
   separating, with `inside` the open square and `outside` the complement of the closed one.

   `Schoenflies.modelCurve` is the case `c = 0`, `r = 1` as a *set*; nothing there is a
   `ClosedPolygon`, so nothing there could be fed to the overlay.

2. *Two nearby congruent squares meet twice.* The route taken is the coordinate one, not the
   blueprint's topological one, because the meeting points can be written down: a vertical
   side of one square crosses a horizontal side of the other, transversally, in a single
   point. That "single point" is exactly what `Schoenflies.MeetsAreCut` needs to turn a
   meeting point into a *vertex* of the overlay graph, which is what
   `Graph.IsTwoConnected.union` consumes. See `exists_two_common_vertices` and the discussion
   before it.

3. *The uniform-continuity partition.* `Schoenflies.sample n i = i / n` is the even partition
   of `[0,1]`; `exists_mesh` says that for `n` large enough — and `n` may be asked to be a
   multiple of any prescribed `k`, which is what makes the fine partition refine the coarse
   one — every point of `α '' [t i, t (i+1)]` is within `ε` of `α (t i)`.

4. *Nonadjacent subarcs are at positive distance.* `exists_pos_dist_nonadjacent`.

5. *The covering clause.* `image_subset_iUnion_closedSquare`: the closed squares of radius `ε`
   about the samples cover the arc.

## Blueprint

* `squarePolygon`, `carrier_squarePolygon` — the square boundary of the proof of
  `thm:arc-complement` ("around every sample draw the boundary of the axis-parallel square of
  `ℓ^∞`-radius `δ/4`"), as a polygon.
* `isJordanCurve_frontier_closedSquare`, `isPolygonal_frontier_closedSquare`,
  `isSeparating_frontier_closedSquare`, `inside_frontier_closedSquare`,
  `outside_frontier_closedSquare` — `thm:polygonal-jordan` specialised to the square.
* `exists_two_meets`, `exists_two_frontier_inter` — "their boundary cycles therefore meet in
  at least two points", `thm:arc-complement`; `exists_two_meets` is the sharp form, in which
  each meeting point is a transversal crossing of two sides.
* `exists_two_common_vertices`, `exists_two_cut_points`, `exists_overlayPiece_end_subset` —
  the bridge from "two common points" to the two common **vertices** that
  `lem:union-two-connected` (`Graph.IsTwoConnected.union`) consumes.
* `sample`, `exists_mesh` — "By uniform continuity, choose a partition …", used twice in
  `thm:arc-complement` and again in `prop:anchored-square-mesh`.
* `exists_pos_dist_nonadjacent` — "Nonadjacent compact subarcs are disjoint, hence at positive
  distance by `lem:compact-separation`(b)".
* `image_subset_iUnion_closedSquare` — "Every point of `A` lies in or on one of the small
  squares".
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## Part 1: the boundary of a square, as a polygon

Everything is done in coordinates. The four corners are named, the four sides are the four
segments between consecutive corners, and the two lemmas `Plane.mem_seg_horiz` and
`Plane.mem_seg_vert` of `Schoenflies/ModelCurve.lean` reduce membership of a side to a pair of
scalar conditions. -/

namespace Plane

variable {c z : Plane} {r : ℝ}

/-- The north-east corner of the square of radius `r` about `c`. -/
def sqNE (c : Plane) (r : ℝ) : Plane := mk (c 0 + r) (c 1 + r)

/-- The north-west corner. -/
def sqNW (c : Plane) (r : ℝ) : Plane := mk (c 0 - r) (c 1 + r)

/-- The south-west corner. -/
def sqSW (c : Plane) (r : ℝ) : Plane := mk (c 0 - r) (c 1 - r)

/-- The south-east corner. -/
def sqSE (c : Plane) (r : ℝ) : Plane := mk (c 0 + r) (c 1 - r)

@[simp] theorem sqNE_zero : sqNE c r 0 = c 0 + r := rfl
@[simp] theorem sqNE_one : sqNE c r 1 = c 1 + r := rfl
@[simp] theorem sqNW_zero : sqNW c r 0 = c 0 - r := rfl
@[simp] theorem sqNW_one : sqNW c r 1 = c 1 + r := rfl
@[simp] theorem sqSW_zero : sqSW c r 0 = c 0 - r := rfl
@[simp] theorem sqSW_one : sqSW c r 1 = c 1 - r := rfl
@[simp] theorem sqSE_zero : sqSE c r 0 = c 0 + r := rfl
@[simp] theorem sqSE_one : sqSE c r 1 = c 1 - r := rfl

/-- The top side. -/
theorem mem_seg_top (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqNE c r) (sqNW c r) ↔ z 1 = c 1 + r ∧ |z 0 - c 0| ≤ r := by
  rw [sqNE, sqNW, mem_segment_horiz, mem_segment_abs' hr]

/-- The left side. -/
theorem mem_seg_left (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqNW c r) (sqSW c r) ↔ z 0 = c 0 - r ∧ |z 1 - c 1| ≤ r := by
  rw [sqNW, sqSW, mem_segment_vert, mem_segment_abs' hr]

/-- The bottom side. -/
theorem mem_seg_bottom (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqSW c r) (sqSE c r) ↔ z 1 = c 1 - r ∧ |z 0 - c 0| ≤ r := by
  rw [sqSW, sqSE, mem_segment_horiz, mem_segment_abs hr]

/-- The right side. -/
theorem mem_seg_right (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqSE c r) (sqNE c r) ↔ z 0 = c 0 + r ∧ |z 1 - c 1| ≤ r := by
  rw [sqSE, sqNE, mem_segment_vert, mem_segment_abs hr]

end Plane

open Plane

/-! ### The square as a `ClosedPolygon`

Four corners in counterclockwise order. `edges_meet` splits into the four adjacent pairs,
where `segment_inter_shared` applies because consecutive sides are perpendicular, and the two
opposite pairs, which are disjoint because opposite sides are pinned to different values of
one coordinate. -/

variable {c : Plane} {r : ℝ}

/-- **The boundary of the axis-parallel square of `ℓ^∞`-radius `r` about `c`, as a closed
polygon.**This is the presentation the overlay and parity machinery consume;
`Schoenflies.modelCurve` is the case `c = 0`, `r = 1` but only as a set. -/
def squarePolygon (c : Plane) {r : ℝ} (hr : 0 < r) : ClosedPolygon 1 where
  vertex := ![sqNE c r, sqNW c r, sqSW c r, sqSE c r]
  vertex_inj := by
    -- Any two of the four corners differ in a coordinate; `r > 0` is what makes them differ.
    have hfst : ∀ p q : Plane, p 0 ≠ q 0 → p ≠ q := fun _ _ h e => h (by rw [e])
    have hsnd : ∀ p q : Plane, p 1 ≠ q 1 → p ≠ q := fun _ _ h e => h (by rw [e])
    have h01 : sqNE c r ≠ sqNW c r := hfst _ _ (by simp <;> linarith)
    have h02 : sqNE c r ≠ sqSW c r := hfst _ _ (by simp <;> linarith)
    have h03 : sqNE c r ≠ sqSE c r := hsnd _ _ (by simp <;> linarith)
    have h12 : sqNW c r ≠ sqSW c r := hsnd _ _ (by simp <;> linarith)
    have h13 : sqNW c r ≠ sqSE c r := hfst _ _ (by simp <;> linarith)
    have h23 : sqSW c r ≠ sqSE c r := hfst _ _ (by simp <;> linarith)
    intro i j hij
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij h03
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij h13
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
    · exact absurd hij h23
    · exact absurd hij.symm h03
    · exact absurd hij.symm h13
    · exact absurd hij.symm h23
    · rfl
  edges_meet := by
    -- Consecutive sides are perpendicular, so they meet only at the corner they share.
    have mTL : segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqNW c r) (sqSW c r)
        ⊆ {sqNW c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero,
          sqNW_one, sqSW_zero, sqSW_one] at h <;> nlinarith)
    have mLB : segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSW c r) (sqSE c r)
        ⊆ {sqSW c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqNW_zero, sqNW_one, sqSW_zero,
          sqSW_one, sqSE_zero, sqSE_one] at h <;> nlinarith)
    have mBR : segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqSE c r) (sqNE c r)
        ⊆ {sqSE c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqSW_zero, sqSW_one, sqSE_zero,
          sqSE_one, sqNE_zero, sqNE_one] at h <;> nlinarith)
    have mRT : segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNE c r) (sqNW c r)
        ⊆ {sqNE c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqSE_zero, sqSE_one, sqNE_zero,
          sqNE_one, sqNW_zero, sqNW_one] at h <;> nlinarith)
    -- Opposite sides sit at different values of one coordinate, so they never meet.
    have mTB : ∀ z, z ∈ segment ℝ (sqNE c r) (sqNW c r) →
        z ∈ segment ℝ (sqSW c r) (sqSE c r) → False := by
      intro z h1 h2
      rw [mem_seg_top hr.le] at h1
      rw [mem_seg_bottom hr.le] at h2
      have := h1.1.symm.trans h2.1
      linarith
    have mLR : ∀ z, z ∈ segment ℝ (sqNW c r) (sqSW c r) →
        z ∈ segment ℝ (sqSE c r) (sqNE c r) → False := by
      intro z h1 h2
      rw [mem_seg_left hr.le] at h1
      rw [mem_seg_right hr.le] at h2
      have := h1.1.symm.trans h2.1
      linarith
    intro i j hij
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl
    · exact absurd rfl hij
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqNE c r, sqNW c r}
      exact subset_trans mTL (by simp)
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqNE c r, sqNW c r}
      exact fun z hz => absurd hz.2 (fun h => mTB z hz.1 h)
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqNE c r, sqNW c r}
      rw [Set.inter_comm]
      exact subset_trans mRT (by simp)
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqNW c r, sqSW c r}
      rw [Set.inter_comm]
      exact subset_trans mTL (by simp)
    · exact absurd rfl hij
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqNW c r, sqSW c r}
      exact subset_trans mLB (by simp)
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqNW c r, sqSW c r}
      exact fun z hz => absurd hz.2 (fun h => mLR z hz.1 h)
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqSW c r, sqSE c r}
      exact fun z hz => absurd hz.1 (fun h => mTB z hz.2 h)
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqSW c r, sqSE c r}
      rw [Set.inter_comm]
      exact subset_trans mLB (by simp)
    · exact absurd rfl hij
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqSW c r, sqSE c r}
      exact subset_trans mBR (by simp)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqSE c r, sqNE c r}
      exact subset_trans mRT (by simp)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqSE c r, sqNE c r}
      exact fun z hz => absurd hz.1 (fun h => mLR z hz.2 h)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqSE c r, sqNE c r}
      rw [Set.inter_comm]
      exact subset_trans mBR (by simp)
    · exact absurd rfl hij
  corner := by
    intro i
    -- The two edges at a corner are perpendicular, so the orientation form is `±4r²`.
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl
    · change det (sqSE c r - sqNE c r) (sqNW c r - sqNE c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero, sqNW_one,
        sqSE_zero, sqSE_one] at h
      nlinarith
    · change det (sqNE c r - sqNW c r) (sqSW c r - sqNW c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero, sqNW_one,
        sqSW_zero, sqSW_one] at h
      nlinarith
    · change det (sqNW c r - sqSW c r) (sqSE c r - sqSW c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNW_zero, sqNW_one, sqSW_zero, sqSW_one,
        sqSE_zero, sqSE_one] at h
      nlinarith
    · change det (sqSW c r - sqSE c r) (sqNE c r - sqSE c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqSW_zero, sqSW_one, sqSE_zero, sqSE_one,
        sqNE_zero, sqNE_one] at h
      nlinarith

@[simp] theorem squarePolygon_vertex_zero (hr : 0 < r) :
    (squarePolygon c hr).vertex 0 = sqNE c r := rfl

@[simp] theorem squarePolygon_vertex_one (hr : 0 < r) :
    (squarePolygon c hr).vertex 1 = sqNW c r := rfl

@[simp] theorem squarePolygon_vertex_two (hr : 0 < r) :
    (squarePolygon c hr).vertex 2 = sqSW c r := rfl

@[simp] theorem squarePolygon_vertex_three (hr : 0 < r) :
    (squarePolygon c hr).vertex 3 = sqSE c r := rfl

/-! ### What the polygonal Jordan curve theorem says about a square

All four clauses come from `main`; only the identification of the two regions is new, and it
is `Plane.connectedComponentIn_eq_of_frontier_disjoint` twice: once for the open square and
once for its complement. -/


/-! ## Part 2: two nearby congruent squares meet twice

The blueprint (`thm:arc-complement`) argues topologically: neither congruent square contains
the other, so each boundary has nonempty relatively open parts inside the other open square and
outside the other closed square, and a single intersection point could not disconnect a
connected boundary curve.

**The route taken here is the coordinate one**, and it proves more than the blueprint asks.
Write the two centres as `c₁` and `c₂ = c₁ + (a, b)` with `|a|, |b| < r`. Then

* the vertical side of `S₁` on the side of `c₂` crosses the horizontal side of `S₂` away from
  `c₁`, in the single point `(c₁₀ ± r, c₂₁ ∓ r)`;
* the horizontal side of `S₁` away from `c₂` crosses the vertical side of `S₂` on the side of
  `c₁`, in the single point `(c₂₀ ∓ r, c₁₁ ± r)`;

and the two points differ because their first coordinates differ by `2r - |a| ≠ 0`. Each is a
*transversal* crossing — the meet of the two sides is a singleton, not a segment — which is
exactly what `MeetsAreCut` turns into a cut point and hence into a **vertex** of the overlay
graph. Two common points would not be enough for `Graph.IsTwoConnected.union`, which wants two
common vertices; see `exists_two_common_vertices`. -/

/-! ### A vertical side crosses a horizontal side in one point -/

/-! ### From a meeting point to a vertex of the overlay

`Graph.IsTwoConnected.union` needs two common **vertices**, not two common points.  The
overlay's cut-point condition `MeetsAreCut` says that both ends of the meet of two source
pieces are cut points; when the meet is a *singleton* both ends are that one point, so the
crossing point is a cut point, and `overlayGraph_mem_vertexSet_of_mem_cover` promotes a cut
point on the union to a vertex.  This is the whole bridge, and it is why `exists_two_meets` is
stated with singleton meets rather than with mere common points. -/

/-! ### Localizing a cut point to one source piece

`overlayGraph_mem_vertexSet_of_mem_cover` says a cut point on the union is a vertex, but it
says nothing about *which* edge it is an end of.  The next wave has to place the two common
points of two neighbouring squares in the vertex sets of the two graphs being unioned, and for
that the edge must be pinned inside the boundary it came from.  The three lemmas below do that;
the first two are general facts about `subdivide` whose home is `Schoenflies/Subdivide.lean`. -/

/-! ## Part 3: the uniform-continuity partition

The blueprint asks for "a partition `0 = t₀ < t₁ < ⋯ < t_k = 1`, with `k ≥ 3`, such that every
point of `α([t_{i-1}, t_i])` is at distance less than `ε` from `α(t_{i-1})`", and separately for
a refinement of it inside each piece.  Both are served by the **even** partition: nothing in
the proof uses anything about the partition beyond the mesh bound, and taking `t_i = i/n`
makes "the fine partition refines the coarse one" the arithmetic identity `sample (k*m) (i*m)
= sample k i` rather than a bookkeeping argument.  The number of pieces can be forced to be a
multiple of any prescribed `k` and hence as large as one likes, which covers the `k ≥ 3`
clause. -/

/-! ## Part 4: nonadjacent subarcs are at positive distance -/

/-! ## Part 5: the covering clause -/

/-! ## The shape of `lem:outer-chain` this module expects to be handed

This is a note to the integrator, not a declaration.  `thm:arc-complement` consumes the
outer-chain lemma exactly once, and the form that makes the assembly short is the following.
`Γ : ℕ → Graph Plane Piece` are the chain graphs, all subgraphs of **one** overlay graph `G`
built from the concatenation of the `squarePieces` of every sample — so that "after subdividing
common points into vertices" is discharged by construction rather than assumed, and so that all
the `Γ i` are `Graph.Compatible` with each other for free (they share edge names because they
share the ambient edge type `Piece`).

```
theorem outer_chain {k : ℕ} (hk : 3 ≤ k) (Γ : ℕ → Graph Plane Piece)
    (drawing : Piece → ℝ → Plane)
    (hfin : ∀ i < k, (Γ i).Finite)
    (hdraw : ∀ i < k, Graph.IsDrawing (Γ i) drawing)
    (h2c : ∀ i < k, (Γ i).IsTwoConnected)
    (hshare : ∀ i, i + 1 < k → ∃ a b : Plane, a ≠ b ∧
      a ∈ V(Γ i) ∧ a ∈ V(Γ (i+1)) ∧ b ∈ V(Γ i) ∧ b ∈ V(Γ (i+1)))
    (hfar : ∀ i j, i < k → j < k → i + 2 ≤ j →
      Disjoint (Graph.pointSet (Γ i) drawing) (Graph.pointSet (Γ j) drawing))
    {x : Plane}
    (houter : ∀ i, i + 1 < k → ¬ Bornology.IsBounded
      (Graph.face ((Γ i).union (Γ (i+1))) drawing x)) :
    ¬ Bornology.IsBounded (Graph.face (chainUnion Γ k) drawing x)
```

with `chainUnion Γ k` the fold of `Graph.union` over `i < k`, exported as a `def` with
`vertexSet` / `edgeSet` / `IsLink` lemmas.  Three things matter for the join:

* **"outer face" must be stated as `¬ IsBounded (face …)`, not as `face … = face … base` for
  some chosen base point.**  `Graph.exists_unbounded_face` and `Graph.unbounded_face_unique`
  make the two equivalent, but the arc-complement proof gets its hypothesis from
  `Graph.beyondSquare_subset_face` applied to a containing square, which is naturally an
  unboundedness statement about `x`'s own face.
* **`hshare` must be about vertices**, which is what `exists_two_common_vertices` and
  `exists_two_cut_points` + `exists_overlayPiece_end_subset` above deliver.  Two common
  *points* would not compose with `Graph.IsTwoConnected.union`.
* **`hfar` is about point sets, not vertex sets.**  The arc-complement proof gets it from
  `exists_pos_dist_nonadjacent`: nonadjacent samples are at distance `≥ δ` while the squares
  have radius `δ/4`, so the two point sets are `δ/2` apart.
-/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_TwoConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Vertex deletion and 2-connectivity

Deleting a vertex from Mathlib's multigraph `Graph α β`, and the blueprint's notion of a
2-connected graph.

## Vertex deletion is Mathlib's

Mathlib already has it: `Graph.deleteVerts G X = G.induce (V(G) \ X)`, in
`Mathlib/Combinatorics/Graph/Delete.lean`, with `V(G.deleteVerts X) = V(G) \ X` and
`E(G.deleteVerts X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X}` — an edge with an end in
`X` is gone, which is exactly what is wanted. Nothing here redefines it; `G.deleteVerts {x}`
is the deletion of one vertex, and what this file adds is the transfer of *walks* across it,
which Mathlib has no notion of.

Two of those transfers are the whole story, and both are corollaries of `Graph.IsWalk.anti`:

* `Graph.IsWalk.deleteVerts_singleton` — a walk that never visits `x` is a walk of `G - x`.
  The edges of such a walk automatically survive, because the ends of an edge of a walk are
  vertices the walk visits.
* `Graph.IsWalk.notMem_of_inc_of_deleteVerts` — a walk **in** `G - x` cannot have used an
  edge at `x`; there are none left to use. This is how an argument that routes around a
  vertex ends up avoiding a named edge, and it is what makes `Graph.IsTwoConnected.no_bridge`
  short.

Deleting a vertex the graph does not have changes nothing — `G.deleteVerts {x} = G` on the
nose (`Graph.deleteVerts_singleton_eq_self`), since `V(G) \ {x} = V(G)`. That equation is
what makes the union lemma's hard case disappear.

## At least three vertices

The counting clause of 2-connectivity is carried by `Graph.HasThreeVertices`, "three pairwise
distinct vertices", rather than by `3 ≤ V(G).ncard`. The two agree on a finite graph, but the
existential form is **monotone with no finiteness hypothesis** (`Graph.HasThreeVertices.mono`),
and monotonicity is precisely what `Graph.IsTwoConnected.union` needs: the union of two graphs
is not known to be finite at the point where its third vertex is produced. `Set.ncard` is `0`
on an infinite set, so `3 ≤ V(G).ncard` would additionally make every infinite graph fail to
be 2-connected, which is not the intent of the convention.

What consumers actually use is never the clause itself but `Graph.HasThreeVertices.exists_ne_ne`
— any two vertices leave a third over. `Graph.hasThreeVertices_iff_ncard` is the bridge back to
the count, for a consumer that has one.

## The convention, verbatim, and what it costs

`Graph.IsTwoConnected` is the blueprint's definition word for word (§"Plane graphs and the
utility graph"): at least three vertices, connected, and still connected after any one vertex
is deleted. Two consequences the blueprint calls out are recorded here as theorems rather
than as prose:

* the one-edge graph is **not** 2-connected, and
* a two-vertex cycle — two parallel edges — is a cycle without being 2-connected.

Both are instances of `Graph.not_isTwoConnected_banana`: `Graph.banana u v F` has only the two
vertices `u` and `v` whatever `F` is, so it fails the counting clause. Two-vertex cycles do
occur in the development, as face boundaries inside a larger 2-connected graph, and this is
the theorem that says they are not themselves 2-connected. (No cycle is *named* here: this
file must not depend on the cycle module.)

## Union

Mathlib's `Mathlib/Combinatorics/Graph/Lattice.lean` provides only the *infimum* of two
graphs — there is no union in this version of Mathlib — so `Graph.union` is defined here. On
an edge belonging to both graphs, `G`'s ends win:

```
(G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
```

which makes the definition total. It has to be resolved somehow: two graphs may disagree
about the ends of a shared edge name, and then no graph has both as subgraphs. When the two
graphs are `Graph.Compatible` — in particular when both are subgraphs of one graph, via
`Graph.Compatible.of_le_le`, which is the only way the plane layer forms unions — the
disjunction collapses to the naive one (`Graph.Compatible.union_isLink`) and both graphs are
subgraphs of the union.

## Blueprint

* `Graph.IsTwoConnected` — the definition in §"Plane graphs and the utility graph": "a finite
  graph is *2-connected* if it has at least three vertices, is connected, and remains
  connected after deletion of any one vertex".
* `Graph.IsTwoConnected.no_cut_vertex` — "with this convention a 2-connected graph has no cut
  vertex".
* `Graph.not_isTwoConnected_banana` — "the one-edge graph is not 2-connected", and the same
  computation for the two-vertex cycle of the next paragraph.
* `Graph.IsTwoConnected.no_bridge` — "A 2-connected graph has no bridge", the step of
  `lem:subdivision-ear-preserve` (a) that the ear decomposition runs on. Stated as "deleting
  the edge leaves its ends connected", which is the form `lem:cycle-criterion` consumes; the
  cycle itself is built elsewhere.
* `Graph.IsTwoConnected.union` — `lem:union-two-connected`, "if two finite 2-connected graphs
  have at least two vertices in common, their union is 2-connected".
-/

open Set

variable {α β : Type*} {G H K G₁ G₂ : Graph α β} {a b s t u v w x y z : α} {e f : β}
  {W : List β} {X : Set α} {F : Set β}

namespace Graph

/-! ### Deleting one vertex -/

/-! ### Walks across a vertex deletion -/

/-! ### Cut vertices -/

/-! ### At least three vertices -/

/-! ### Two-connectivity -/

/-- **The blueprint's convention, verbatim**: at least three vertices, connected, and still
connected after any one vertex is deleted. -/
structure IsTwoConnected (G : Graph α β) : Prop where
  /-- The graph has at least three vertices. -/
  hasThreeVertices : G.HasThreeVertices
  /-- The graph is connected. -/
  connected : G.Connected
  /-- Deleting any one vertex leaves it connected. -/
  deleteVerts_connected : ∀ ⦃x⦄, x ∈ V(G) → (G.deleteVerts {x}).Connected

/-- The deletion clause with its hypothesis dropped: deleting a vertex the graph does not have
changes nothing, so no consumer has to check membership first. -/
theorem IsTwoConnected.deleteVerts_connected' (h : G.IsTwoConnected) (x : α) :
    (G.deleteVerts {x}).Connected := by
  by_cases hx : x ∈ V(G)
  · exact h.deleteVerts_connected hx
  · exact h.connected.deleteVerts_singleton_of_notMem hx

/-! ### The union of two graphs -/

theorem union_isLink :
    (G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y) := Iff.rfl

/-- Two subgraphs of one graph have their union inside it. -/
theorem union_le (hGK : G ≤ K) (hHK : H ≤ K) : G.union H ≤ K where
  vertexSet_mono := Set.union_subset hGK.vertexSet_mono hHK.vertexSet_mono
  isLink_mono := by
    rintro g p q (h | ⟨-, h⟩)
    exacts [hGK.isLink_mono h, hHK.isLink_mono h]

end Graph
end

section
-- module Solutions.Q146_CD.CombinatorialInvariance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Combinatorial invariance

The first module of Part II. It introduces the abstract record of a matched cellulation, the
notion of a geometric realization of that record, and proves that everything a realization
inherits from the record is the same for two realizations of one record —
`lem:combinatorial-invariance`.

Per the blueprint's citation index this lemma has no internal prerequisites: the whole point of
the design is that the combinatorial content of the cellulation machinery is separated from all
of the geometry, so this can be built while the Jordan curve theorem is still unproved.

## What is defined here, and how faithful it is

`CellStructure` is the *abstract* record of `def:matched-cellulation`: the finite cell sets in
each dimension, the endpoint maps, the outer subcomplex, the boundary walks, and the subcell
relation. Cells of all three dimensions are names drawn from one type `γ`; the 0- and 1-cells
are the vertices and the edges of an abstract multigraph `skel : Graph γ γ`, the 2-cells are a
set `faces`, and the three collections are disjoint. What is deliberately **not** in the record:
the parent maps (they belong to a refinement — a pair of stages — not to a stage), and any
compatibility between `sub` and the realizations (that is assertion (ix) of
`lem:cellulation-invariants`, and the blueprint is explicit that `≼_abs` "enters as a raw
datum"). No reflexivity or transitivity of `sub` is assumed; the one lemma that needs
transitivity takes it as a hypothesis.

`CellStructure.Realization` is one of the two geometric realizations. The repository's plane
graphs have `V(G) : Set Plane` — vertices *are* points — so the drawn skeleton cannot literally
be the abstract graph. It is instead the pushforward `S.skel.map pos` along the positions of
the 0-cells, with `pos` injective on `V(S.skel)`. This is the representation choice of the
module, and the alternative — carrying an abstract graph isomorphism as data — was rejected
because with the pushforward "the two skeleta realize the *same* abstract graph" is a
definitional identity rather than a theorem, which is exactly what the blueprint's proof of
part (a) asserts.

The price of the choice is paid here, once: `Graph.isTwoConnected_map_iff` and
`Graph.connected_map_iff` transport connectivity along an injective relabelling of the
vertices, so that 2-connectivity of the *drawn* graph — which is what
`def:admissible-graph` requires — transfers between the realizations. Those two, and the walk
and vertex-deletion lemmas they rest on, are general facts about `Graph.map` in the root
`Graph` namespace and belong in `Schoenflies/Graph/` if a second consumer appears.

`SkeletonHomeo` is `g : |Γ| → |Γ'|` of `def:matched-pair`, as a set-level homeomorphism with
its inverse supplied as data (so that no finiteness hypothesis is needed to invert it).
Clause 3 of `def:matched-pair` is recorded in the weaker form "`g` carries each drawn edge onto
the corresponding drawn edge", which is all that is used and which the full clause implies.

## The three parts of the lemma

Only part (b) has topological content. Parts (a) and (c) are, under this representation, either
definitional identities or one-line consequences of the fact that the index sets involved are
fields of the single structure both realizations realize; that is precisely the blueprint's
argument ("all the data in (c) belong to the common abstract cell structure"), and the
statements below are shaped so that a consumer gets the geometric conclusion on *both* sides
from one combinatorial hypothesis.

## Blueprint

* `Schoenflies.CellStructure` — the abstract record of `def:matched-cellulation`.
* `Schoenflies.CellStructure.Realization` — one of its two geometric realizations.
* `Schoenflies.CellStructure.Realization.nonboundary` — the open nonboundary part
  `|Γ| \ C` of `def:admissible-graph`.
* `Schoenflies.CellStructure.Realization.star` — the closed star `St(σ) = ⋃_{σ ≼ τ} closure τ`.
* `Schoenflies.CellStructure.SkeletonHomeo` — the skeleton homeomorphism of
  `def:matched-pair`.
* `Schoenflies.CellStructure.combinatorial_invariance` — `lem:combinatorial-invariance`,
  assembled from:
  * (a) `Realization.graph_eq_map`, `Realization.edgeSet_graph_congr`,
    `Realization.isTwoConnected_congr`, `SkeletonHomeo.image_outerSet`;
  * (b) `SkeletonHomeo.image_nonboundary`, `SkeletonHomeo.isConnected_nonboundary_iff`;
  * (c) `Realization.star_mono`, `Realization.star_transfer`,
    `Realization.star_subset_of_sub`, `outerEdge_face_corresponds`.
* `Graph.isTwoConnected_map_iff`, `Graph.connected_map_iff` — connectivity is invariant under
  an injective relabelling of the vertices; the transport that the pushforward representation
  of a realization needs.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*}

namespace CellStructure

variable (S : CellStructure γ)

/-- All cells of the structure. -/
def cells : Set γ := V(S.skel) ∪ E(S.skel) ∪ S.faces

/-! ### Realizations -/

namespace Realization

variable {S}
variable (R : S.Realization)

instance finite_graph : (R.graph).Finite where
  finite_vertexSet := by rw [vertexSet_graph]; exact S.finite_vertexSet.image _
  finite_edgeSet := by rw [edgeSet_graph]; exact S.finite_edgeSet

/-- The realized outer cycle: `C` in the source realization, `S` in the target one. -/
def outerSet : Set Plane := pointSet (S.outerGraph.map R.pos) R.drawing

theorem isCompact_skeletonSet : IsCompact R.skeletonSet :=
  @IsDrawing.isCompact_pointSet _ _ _ R.finite_graph R.isDrawing

end Realization

/-! ### The skeleton homeomorphism -/

namespace SkeletonHomeo

variable {S} {R₁ R₂ : S.Realization} (g : SkeletonHomeo R₁ R₂)

/-- `g` carries the realization of any subcomplex of the skeleton onto the realization of the
same subcomplex on the other side. Used for the whole skeleton and for the outer cycle. -/
theorem image_pointSet_map {H : Graph γ γ} (hH : H ≤ S.skel) :
    g.toFun '' pointSet (H.map R₁.pos) R₁.drawing = pointSet (H.map R₂.pos) R₂.drawing := by
  rw [pointSet, pointSet, Set.image_union, Set.image_iUnion₂]
  congr 1
  · rw [vertexSet_map, vertexSet_map, ← Set.image_comp]
    exact Set.image_congr fun v hv => g.pos_apply (hH.vertexSet_mono hv)
  · rw [edgeSet_map]
    exact Set.iUnion₂_congr fun e he => g.edgeArc_image (hH.edgeSet_mono he)

theorem image_skeletonSet : g.toFun '' R₁.skeletonSet = R₂.skeletonSet :=
  g.image_pointSet_map le_rfl

theorem injOn : InjOn g.toFun R₁.skeletonSet := g.leftInvOn.injOn

end SkeletonHomeo

/-! ### Combinatorial invariance -/

variable {S}

/-- The clause "every outer edge is a subcell of exactly one 2-cell" — assertion (vi) of
lem:cellulation-invariants — as a property of the abstract structure alone. -/
def OuterEdgeUniqueFace (S : CellStructure γ) : Prop :=
  ∀ ⦃e⦄, e ∈ E(S.outerGraph) → ∃! F, F ∈ S.faces ∧ S.sub e F

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_VertexSquares
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The vertex squares, the last parameter inside a closed set, and the cores

Three of the ordinary bricks of the polygonal redrawing of a finite plane graph.

**The vertex squares.** Around each vertex of a finite plane graph sits a closed axis-parallel
square which meets no other vertex and no edge arc of an edge not incident with that vertex.
One compact separation per other vertex and per non-incident arc, then the single-`ε`-for-all
lemma of `Schoenflies/UniformBound.lean`. Squares rather than disks because the assembly needs
the boundary to be made of segments; convexity, which the radial segments of the last step
want, both shapes have.

Because the choice is made once for all vertices rather than vertex by vertex, halving the
common radius also makes *distinct squares disjoint* — which the cores of the next brick need
and which the per-vertex statement does not give. That is why `exists_vertexSquares` is the
form to consume and `exists_square_at` only its ingredient.

**The last parameter inside a closed set.** The parameters at which an arc lies in a closed
set form a compact subset of the parameter interval; if it is nonempty its supremum is
attained, and past that supremum the arc has left the set for good. The mirror statement about
the infimum is what the far end of an edge wants: the arc leaves the square at `v` for the last
time and enters the square at `w` for the first time.

**The cores.** The subarc of an edge between those two parameters. It meets the square at `v`
in its own first endpoint only, the square at `w` in its own last endpoint only, and — the
clause the assembly really uses — it contains no vertex, which makes distinct cores disjoint
without any further estimate.

## Blueprint

Bricks B2, B3 and B4 of `lem:polygonal-redrawing`.

* `Plane.closedBall_subset_closedSquare`, `Plane.closedSquare_subset_ball` — a square sits
  inside a ball and vice versa, the comparison every separation argument passes through.
* `Plane.supDist_triangle`, `Plane.closedSquare_mono_center`, `Plane.mem_closedSquare_self` —
  square arithmetic missing from `Schoenflies/Square.lean`.
* `exists_last_mem_Icc`, `exists_first_mem_Icc`, `exists_last_mem`, `exists_first_mem` — B3,
  with `isCompact_parameters_mem` behind them.
* `Graph.IsDrawing.exists_square_at` — B2 at one vertex.
* `Graph.IsDrawing.exists_vertexSquares` — B2 as consumed: one radius for every vertex, with
  distinct squares disjoint.
* `Graph.IsDrawing.exists_core` — B4, the core of one edge.
* `Graph.IsDrawing.disjoint_of_subset_edgeArc` — B4's "distinct cores are disjoint".
* `Graph.IsDrawing.closedSquare_disjoint_edgeArc_of_ne` — B4's "meets no other vertex square",
  which is a property of the whole arc.
-/

open Metric Set unitInterval

namespace Schoenflies

namespace Plane

/-! ### Square arithmetic

`Schoenflies/Square.lean` has convexity, openness and closedness of `closedSquare` but no
triangle inequality for `supDist` and no monotonicity at a general centre; both are needed
here. -/

/-- Squares about a common centre grow with the radius. `Bounded.closedSquare_mono` says this
only about the origin. -/
theorem closedSquare_mono_center (c : Plane) {r s : ℝ} (h : r ≤ s) :
    closedSquare c r ⊆ closedSquare c s := fun _ hx => le_trans hx h

/-- The centre lies in its own square. -/
theorem mem_closedSquare_self (c : Plane) {r : ℝ} (hr : 0 ≤ r) : c ∈ closedSquare c r := by
  change supDist c c ≤ r
  rw [supDist_self]; exact hr

theorem supDist_eq_dist_le (x c : Plane) : supDist x c ≤ dist x c := by
  rw [dist_eq_norm]; exact supNorm_le_norm _

/-- The inscribed ball: a ball is inside the square of the same radius, since the sup norm is
at most the Euclidean norm. -/
theorem closedBall_subset_closedSquare (c : Plane) (r : ℝ) :
    closedBall c r ⊆ closedSquare c r := fun _ hx =>
  le_trans (supDist_eq_dist_le _ _) (mem_closedBall.1 hx)

/-- The circumscribed ball, in the form the separations want: a square of *half* a given
radius sits inside the open ball of that radius, because `√2 < 2`. -/
theorem closedSquare_subset_ball {c : Plane} {ρ : ℝ} (hρ : 0 < ρ) :
    closedSquare c (ρ / 2) ⊆ ball c ρ := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x c ≤ ρ / 2 := hx
  have hnorm : ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) :=
    le_trans (norm_le_sqrt_two_mul_supNorm _)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  rw [mem_ball, dist_eq_norm]
  calc ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) := hnorm
    _ < 2 * (ρ / 2) := by
        exact mul_lt_mul_of_pos_right hsqrt (by linarith)
    _ = ρ := by ring

end Plane

/-! ### B3 — the last point of an arc inside a closed set -/

/-- The parameters at which a curve lies in a closed set form a compact subset of the
parameter interval: the parametrisation is continuous there and the interval is compact.

Stated over an arbitrary `Icc` and not only over `[0, 1]`, because the *second* use of B3 —
the first entry into the far vertex's square — has to happen after the last exit from the near
one, i.e. on the interval `[a, 1]`. -/
theorem isCompact_parameters_mem {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) : IsCompact {t | t ∈ Icc α β ∧ f t ∈ C} := by
  have hset : {t | t ∈ Icc α β ∧ f t ∈ C} = Icc α β ∩ f ⁻¹' C := rfl
  rw [hset]
  exact isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc hC) inter_subset_left

/-- The last parameter inside a closed set. Given one parameter whose point lies in `C`, there
is a largest one: the curve is in `C` there, and at every larger parameter of the interval it
has left `C` for good.

This is the supremum of a nonempty compact set of parameters, which is therefore attained. -/
theorem exists_last_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, s < t → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sSup S ∈ S := hcpt.sSup_mem hne
  refine ⟨sSup S, hsI, le_csSup hcpt.bddAbove ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  -- A parameter past the supremum that still lands in `C` would be a member above it.
  exact absurd (le_csSup hcpt.bddAbove ⟨htI, htC⟩) (not_le.2 hlt)

/-- The mirror of `exists_last_mem_Icc`: the first parameter inside a closed set. Before it the
curve has not yet reached `C`. -/
theorem exists_first_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, t < s → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sInf S ∈ S := hcpt.sInf_mem hne
  refine ⟨sInf S, hsI, csInf_le hcpt.bddBelow ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  exact absurd (csInf_le hcpt.bddBelow ⟨htI, htC⟩) (not_le.2 hlt)

/-- B3 on the unit interval: the last parameter at which an arc is inside a closed set. -/
theorem exists_last_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ I, s < t → f t ∉ C :=
  exists_last_mem_Icc hf hC ht₀ hmem

end Schoenflies

/-! ### B2 — the vertex squares -/

open Schoenflies
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A vertex lies on no arc of an edge it is not incident with: the arc meets the vertex set
only at its own two ends, and those are the vertices it is incident with. -/
theorem IsDrawing.notMem_edgeArc_of_not_inc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G))
    {v : Plane} (hv : v ∈ V(G)) (hinc : ¬ G.Inc e v) : v ∉ edgeArc drawing e := by
  intro hmem
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  rcases h.vertex_mem_edgeArc hxy hv hmem with rfl | rfl
  · exact hinc hxy.inc_left
  · exact hinc hxy.inc_right

/-- B2 at a single vertex: a closed square about `v` meeting no other vertex and no arc of an
edge not incident with `v`.

The two families are separated the same way — one compact separation each, then the common
positive bound of `exists_pos_forall_of_finite` — and the two radii are then merged by taking
the smaller, which is legitimate because shrinking a square preserves "meets nothing". -/
theorem IsDrawing.exists_square_at [G.Finite] (h : IsDrawing G drawing) {v : Plane}
    (hv : v ∈ V(G)) :
    ∃ r > 0, (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      ∀ e ∈ E(G), ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
  -- The other vertices.
  obtain ⟨r₁, hr₁, hvert⟩ :
      ∃ r > 0, ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun w r => w ≠ v → w ∉ Plane.closedSquare v r) ?_ ?_
    · exact fun w δ ε _ hδε hP hne hmem =>
        hP hne (Plane.closedSquare_mono_center v hδε hmem)
    · intro w hw
      by_cases hwv : w = v
      · exact ⟨1, one_pos, fun hne => absurd hwv hne⟩
      · -- `w` is at positive Euclidean distance from `v`, and a square of half that radius
        -- sits inside the ball of that radius.
        have hpos : 0 < dist w v := dist_pos.2 hwv
        refine ⟨dist w v / 2, by linarith, fun _ hmem => ?_⟩
        exact absurd (mem_ball.1 (Plane.closedSquare_subset_ball hpos hmem)) (by simp)
  -- The non-incident edges.
  obtain ⟨r₂, hr₂, hedge⟩ :
      ∃ r > 0, ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e r => ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e))
      ?_ ?_
    · exact fun e δ ε _ hδε hP hinc =>
        Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hP hinc)
    · intro e he
      by_cases hinc : G.Inc e v
      · exact ⟨1, one_pos, fun h' => absurd hinc h'⟩
      · have hdisj : Disjoint ({v} : Set Plane) (edgeArc drawing e) :=
          Set.disjoint_singleton_left.2 (h.notMem_edgeArc_of_not_inc he hv hinc)
        obtain ⟨ρ, hρ, hsep⟩ :=
          Plane.exists_dist_pos isCompact_singleton (h.isCompact_edgeArc he) hdisj
        refine ⟨ρ / 2, by linarith, fun _ => Set.disjoint_left.2 fun x hx hxe => ?_⟩
        have hclose : dist x v < ρ := mem_ball.1 (Plane.closedSquare_subset_ball hρ hx)
        have hfar : ρ ≤ dist v x := hsep v rfl x hxe
        rw [dist_comm] at hfar
        linarith
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun w hw hne hmem => ?_, fun e he hinc => ?_⟩
  · exact hvert w hw hne (Plane.closedSquare_mono_center v (min_le_left _ _) hmem)
  · exact Set.disjoint_of_subset_left
      (Plane.closedSquare_mono_center v (min_le_right _ _)) (hedge e he hinc)

/-- B2 as its consumers want it: **one** radius serving every vertex at once, with the squares
about distinct vertices disjoint.

Disjointness is not a consequence of the per-vertex statement — a square about `v` avoiding
`w` says nothing about a square about `w` reaching towards `v`. It comes from choosing the
radius once for all vertices and then halving it: two squares of radius `r` that met would put
their centres within `2r` in the sup metric, i.e. each centre in the other's square of radius
`2r`, which the unhalved choice forbids. -/
theorem IsDrawing.exists_vertexSquares [G.Finite] (h : IsDrawing G drawing) :
    ∃ r > 0,
      (∀ v ∈ V(G), ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      (∀ v ∈ V(G), ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ∧
      ∀ v ∈ V(G), ∀ w ∈ V(G), v ≠ w →
        Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r) := by
  -- One radius for all vertices, by the same monotone-downward bound.
  obtain ⟨r, hr, hall⟩ :
      ∃ r > 0, ∀ v ∈ V(G),
        (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun v r => (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ?_ ?_
    · rintro v δ ε _ hδε ⟨hP, hQ⟩
      exact ⟨fun w hw hne hmem => hP w hw hne (Plane.closedSquare_mono_center v hδε hmem),
        fun e he hinc =>
          Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hQ e he hinc)⟩
    · exact fun v hv => h.exists_square_at hv
  refine ⟨r / 2, by linarith, fun v hv w hw hne hmem => ?_, fun v hv e he hinc => ?_,
    fun v hv w hw hne => Set.disjoint_left.2 fun x hxv hxw => ?_⟩
  · exact (hall v hv).1 w hw hne (Plane.closedSquare_mono_center v (by linarith) hmem)
  · exact Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v (by linarith))
      ((hall v hv).2 e he hinc)
  · -- Both centres are within `r/2` of `x`, hence within `r` of each other.
    have hvx : Plane.supDist x v ≤ r / 2 := hxv
    have hwx : Plane.supDist x w ≤ r / 2 := hxw
    have : Plane.supDist w v ≤ r := by
      have := Plane.supDist_triangle w x v
      rw [Plane.supDist_comm w x] at this
      linarith
    exact (hall v hv).1 w hw (Ne.symm hne) this

/-! ### B4 — the cores -/

/-- An edge is incident only with its own two ends. -/
theorem not_inc_of_ne {e : β} {v w u : Plane} (hlink : G.IsLink e v w) (huv : u ≠ v)
    (huw : u ≠ w) : ¬ G.Inc e u := fun hinc => (hinc.eq_or_eq_of_isLink hlink).elim huv huw

/-- **Distinct cores are disjoint.** A subset of one edge's arc containing no vertex meets no
other edge's arc at all, because distinct edges meet only at vertices. Stated for arbitrary
subsets rather than for cores, since that is all the argument uses — and it is why
`exists_core` carries `Disjoint K V(G)` rather than a clause about other edges. -/
theorem IsDrawing.disjoint_of_subset_edgeArc (h : IsDrawing G drawing) {e f : β}
    (he : e ∈ E(G)) (hf : f ∈ E(G)) (hef : e ≠ f) {K L : Set Plane}
    (hK : K ⊆ edgeArc drawing e) (hKV : Disjoint K V(G)) (hL : L ⊆ edgeArc drawing f) :
    Disjoint K L :=
  Set.disjoint_left.2 fun _ hxK hxL =>
    Set.disjoint_left.1 hKV hxK (h.arcs_meet_at_vertex he hf hef (hK hxK) (hL hxL))

/-- **The core of an edge.** Between the last parameter at which the edge's arc is inside the
square about `v` and the first parameter after that at which it is inside the square about `w`
sits a subarc `K` — the core — which meets the square at `v` in its first endpoint only, meets
the square at `w` in its last endpoint only, and contains no vertex at all.

The two squares must be disjoint, which is what the uniform choice of `exists_vertexSquares`
provides; disjointness in particular forces `v ≠ w`, so **this says nothing about a loop
edge** — see the module report.

The "first entry after the last exit" is not the same as "first entry": nothing forbids the
arc from dipping into the far square and coming back, so the second application of B3 is over
`[a, 1]` and not over `[0, 1]`.

That the endpoints of the core are *not* the vertices themselves is where the positivity of
the radius is used: the arc starts at the centre of the square about `v`, so it is still
inside the square just after leaving it, and the last exit therefore happens at a positive
parameter. That fact is what makes `Disjoint K V(G)` true and hence distinct cores disjoint. -/
theorem IsDrawing.exists_core (h : IsDrawing G drawing) {e : β} {v w : Plane} {r : ℝ}
    (hr : 0 < r) (hlink : G.IsLink e v w)
    (hdisj : Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r)) :
    ∃ (K : Set Plane) (p q : Plane),
      K ⊆ edgeArc drawing e ∧ IsCompact K ∧ IsArcBetween K p q ∧
      K ∩ Plane.closedSquare v r = {p} ∧ K ∩ Plane.closedSquare w r = {q} ∧
      Disjoint K V(G) := by
  obtain ⟨f, hcont, hinj, himg, hf0, hf1⟩ := h.edge_isArcBetween hlink
  have hv0 : f 0 ∈ Plane.closedSquare v r := by
    rw [hf0]; exact Plane.mem_closedSquare_self v hr.le
  have hw1 : f 1 ∈ Plane.closedSquare w r := by
    rw [hf1]; exact Plane.mem_closedSquare_self w hr.le
  -- The last exit from the square at `v` …
  obtain ⟨a, haI, -, haD, hafter⟩ :=
    exists_last_mem hcont (Plane.isClosed_closedSquare v r) zero_mem_I hv0
  have hsub : Icc a 1 ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, ht.2⟩
  -- … and the first entry into the square at `w` after it.
  obtain ⟨b, hbmem, -, hbD, hbefore⟩ :=
    exists_first_mem_Icc (hcont.mono hsub) (Plane.isClosed_closedSquare w r)
      (right_mem_Icc.2 haI.2) hw1
  have hbI : b ∈ I := hsub hbmem
  have hne : a ≠ b := by
    intro hEq
    rw [hEq] at haD
    exact Set.disjoint_left.1 hdisj haD hbD
  have hIccI : Icc a b ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, le_trans ht.2 hbmem.2⟩
  -- The core does not reach back to `v`: just after `0` the arc is still inside the square.
  have hpv : f a ≠ v := by
    intro hEq
    have ha0 : a = 0 := hinj haI zero_mem_I (by rw [hEq, hf0])
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 0 zero_mem_I) r hr
    have ht0 : 0 < min (δ / 2) 1 := lt_min (by linarith) one_pos
    have htI : min (δ / 2) 1 ∈ I := ⟨ht0.le, min_le_right _ _⟩
    have hdist : dist (min (δ / 2) 1) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine hafter _ htI (by rw [ha0]; exact ht0) (Plane.closedBall_subset_closedSquare v r ?_)
    rw [mem_closedBall, ← hf0]
    exact (hclose htI hdist).le
  -- Symmetrically, the core does not reach forward to `w`.
  have hqw : f b ≠ w := by
    intro hEq
    have hb1 : b = 1 := hinj hbI one_mem_I (by rw [hEq, hf1])
    have halt1 : a < 1 := by rw [← hb1]; exact lt_of_le_of_ne hbmem.1 hne
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 1 one_mem_I) r hr
    have hmax1 : max (1 - δ / 2) ((a + 1) / 2) < 1 := max_lt (by linarith) (by linarith)
    have hmaxa : a ≤ max (1 - δ / 2) ((a + 1) / 2) :=
      le_trans (by linarith) (le_max_right _ _)
    have htmem : max (1 - δ / 2) ((a + 1) / 2) ∈ Icc a 1 := ⟨hmaxa, hmax1.le⟩
    have hdist : dist (max (1 - δ / 2) ((a + 1) / 2)) 1 < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]
      have := le_max_left (1 - δ / 2) ((a + 1) / 2)
      linarith
    refine hbefore _ htmem (by rw [hb1]; exact hmax1)
      (Plane.closedBall_subset_closedSquare w r ?_)
    rw [mem_closedBall, ← hf1]
    exact (hclose (hsub htmem) hdist).le
  -- The core itself.
  have harc : IsArcBetween (f '' Icc a b) (f a) (f b) := by
    have hsubarc := isArcBetween_subarc_of_injOn_I hcont hinj haI hbI hne
    rwa [uIcc_of_le hbmem.1] at hsubarc
  have hKsub : f '' Icc a b ⊆ edgeArc drawing e := by
    rw [← himg]; exact image_mono hIccI
  have hKv : f '' Icc a b ∩ Plane.closedSquare v r = {f a} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.1 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hafter t (hIccI ht) hlt)
    · rintro rfl
      exact ⟨⟨a, ⟨le_refl a, hbmem.1⟩, rfl⟩, haD⟩
  have hKw : f '' Icc a b ∩ Plane.closedSquare w r = {f b} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.2 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hbefore t ⟨ht.1, le_trans ht.2 hbmem.2⟩ hlt)
    · rintro rfl
      exact ⟨⟨b, ⟨hbmem.1, le_refl b⟩, rfl⟩, hbD⟩
  refine ⟨f '' Icc a b, f a, f b, hKsub, harc.isArc.isCompact, harc, hKv, hKw,
    Set.disjoint_left.2 fun x hxK hxV => ?_⟩
  -- A vertex on the core is an end of the edge, and each end is excluded by the two facts
  -- above together with the descriptions of `K ∩ D_v` and `K ∩ D_w`.
  rcases h.vertex_mem_edgeArc hlink hxV (hKsub hxK) with heq | heq
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare v r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self v hr.le⟩
    rw [hKv, mem_singleton_iff] at hmem
    exact hpv (hmem ▸ heq)
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare w r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self w hr.le⟩
    rw [hKw, mem_singleton_iff] at hmem
    exact hqw (hmem ▸ heq)

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Component
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Components and shortest paths

The two prerequisites of the relative ear decomposition (`lem:relative-ear`) that no earlier
module builds: the **component** of a vertex, and a **shortest** walk between two vertices.
Both are then spent on the geometric heart of that lemma — a component of `G - S` has two
distinct neighbours in `S`, and a path between two of them whose interior lies outside `S`.

## The component is a comprehension

`G.component u = {v | G.Reaches u v}`, exactly as `connectedComponentIn` collects the points
a space reaches. Nothing restricts the comprehension to `V(G)`: the empty walk already demands
a vertex of the graph (`Graph.IsWalk.nil`), so `G.Reaches u v` carries `v ∈ V(G)` with it, and
a clause `v ∈ V(G) ∧ …` would be redundant noise at every use site. When `u ∉ V(G)` the
component is empty, which is the convention that makes the covering statement
`Graph.iUnion_component` true with no side condition.

Reachability is an equivalence relation on `V(G)`, so the component is closed under `Reaches`,
two components are equal or disjoint, and the components cover `V(G)`. The one statement that
is not pure equivalence-relation bookkeeping is that the **induced** subgraph on a component
is connected: a walk between two vertices of a component never leaves it
(`Graph.IsWalk.walkVertices_subset_component`), so it is already a walk of the induced
subgraph, by `Graph.IsWalk.anti`.

## Shortest walks need no finiteness

The set of lengths of walks from `u` to `v` is a nonempty set of naturals, so it has a least
element — `Nat.find`, with no `Graph.Finite` hypothesis anywhere. That is worth noticing: the
blueprint says "in a finite graph", but finiteness is used there only to terminate the ear
*process*, never to find one shortest path.

A minimum-length walk is automatically a path (`Graph.IsWalk.isPath_of_minLength`). The proof
is the induction of `Graph.IsWalk.contains_path` run once more, with lengths attached: if the
step's source were revisited later, `Graph.IsPath.from_visited` would cut the tail down to a
strictly shorter walk with the same ends, and a path's edge list repeats nothing
(`Graph.IsPath.nodup`), so the cut piece really is no longer than what it came from
(`List.subperm_of_subset`).

## The two neighbours, without a contradiction

The blueprint argues by contradiction: "otherwise its unique neighbour would be a cut vertex".
Here the two neighbours are *constructed*, in the shape `Graph.IsTwoConnected.no_bridge`
already uses. A walk from the component out to a vertex of `S` crosses the boundary
(`Graph.IsWalk.crossing`), and the crossing edge's far end is in `S` — because a neighbour
outside `S` would still be in the component. That is the first neighbour `c`. For the second,
delete `c`: the big graph is still connected, so the same crossing argument runs inside
`G - c`, and its crossing edge's far end is a neighbour that is not `c`.

Two distinct vertices of `S` are needed, and used exactly once: the walk of the second step
must aim at a vertex of `S` other than `c`. In the application `S` is the vertex set of a
2-connected subgraph, which has three.

## Blueprint

* `Graph.component`, `Graph.induce_component_connected` — "a component `L` of `G - V(H₀)`" in
  the proof of `lem:relative-ear`.
* `Graph.exists_minLength_isPath` — "a shortest path through `L`", same proof.
* `Graph.IsTwoConnected.component_two_neighbors` — "if a component `L` of `G - V(H₀)` contains
  a vertex, it has at least two distinct neighbors in `H₀`; otherwise its unique neighbor
  would be a cut vertex of `G`".
* `Graph.IsTwoConnected.exists_path_through_component` — "a shortest path through `L` between
  two such neighbors is an ear": a path of `G` between two distinct vertices of `S`, whose
  every other vertex is outside `S`, which has at least one such vertex, and each of whose
  edges has an end outside `S`. The word *ear* is not used here and nothing about ears is
  assumed; this is the raw path that a consumer recognises as one.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y z a b c d p q : α} {e f : β}
  {W W' P Q : List β} {S : Set α}

/-! ### Components -/

/-- The component of `u` in `G`: the vertices `u` reaches. A comprehension over the vertices,
not an indexed union of connected subgraphs; the membership test is `Graph.Reaches` itself,
which is why every closure property below is one line of the reachability API.

No `v ∈ V(G)` clause: `Graph.Reaches` already carries it, since the empty walk demands a
vertex of the graph. For `u ∉ V(G)` the component is empty. -/
def component (G : Graph α β) (u : α) : Set α := {v | G.Reaches u v}

/-! ### The subgraph induced on a component -/

@[simp]
theorem mem_vertexSet_induce_component : v ∈ V(G.induce (G.component u)) ↔ G.Reaches u v :=
  Iff.rfl

/-! ### Shortest walks and shortest paths -/

/-! ### Components of a vertex deletion

From here on `S : Set α` is a set of vertices to be deleted, and the component in question is
one of `G.deleteVerts S`. Only two facts about the deletion are used, and both are about where
its walks can go. -/

/-! ### The two neighbours of a component, and the path through it -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_PathGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A path presented as a graph

`Schoenflies/Graph/Walk.lean` says what it means for an edge list to *run* through a graph.
This file says what it means for a graph to *be* a path, and — the point of the file —
constructs one.

## Why the object exists

An ear is a path that gets glued onto a graph, so it has to be a graph itself, not a walk
inside one. `Graph.IsPathGraph P u W v` says that `P`'s own edges, listed in the order `W`,
form a path from `u` to `v` and that `P`'s vertices are exactly the ones that path visits.
The list `W` is an index of the predicate rather than an existential: its **order** is part
of the claim, and it is what lets every later argument cut the path at a vertex without first
having to sort anything.

Mathlib's `Graph α β` carries a `Set β` of edges, not a list, so the correspondence between
the two is a clause of the definition (`Graph.IsPathGraph.edgeSet_eq`) rather than something
a list-based graph would give for free.

## Constructing one

`Graph.pathGraphOf G u W` is the subgraph of `G` spanned by the walk `W` from `u`: the
vertices the walk visits, and its own edges. Everything else in the file is a hypothesis of
the form `IsPathGraph`; this is where one is produced, and it is what an ear decomposition
runs on — a path found inside a big graph has to be turned into a graph before it can be
unioned back in.

## What the ear argument actually asks

Always the same thing: **whatever vertex is deleted, every remaining vertex of the path still
reaches one of the two ends** (`Graph.IsPathGraph.reaches_an_end`). The proof is uniform in
the deleted vertex `c`, with no case split on whether `c` is an end, an interior vertex or
off the path at all:

* if `c` is on the path, cut there (`Graph.IsPath.split`); each remaining vertex lies on one
  of the two halves, and a half runs to its far end without meeting the cut, because the
  split's last clause says the far half never returns to the source;
* if `c` is not on the path, cut at the vertex itself and reverse the near half.

Both branches go through the same two lemmas, `Graph.IsPath.reaches_target_of_ne_source` and
its mirror, so the interior case has no separate content.

## Blueprint

* `Graph.IsPathGraph` — the object called "a path `P`" in Lemma
  `lem:subdivision-ear-preserve` (b) ("if `P` is a path whose distinct endpoints lie in `G`
  … then `G ∪ P` is 2-connected") and "an ear" in Lemma `lem:relative-ear`.
* `Graph.IsPathGraph.reaches_an_end` — the blueprint's "every component of `P - x` is
  attached to `G - x` at one of the two endpoints of `P`; when `x` is an endpoint, the
  remainder of `P` is attached at the other endpoint", both sentences at once.
* `Graph.pathGraphOf` — the "shortest path through `L` between two such neighbors is an ear"
  of `lem:relative-ear`: a path of the ambient graph, presented as a graph.

Nothing here mentions 2-connectivity; the union of a 2-connected graph with an ear is a
later module.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`, so that `h.reaches_an_end` and
`G.pathGraphOf u W` resolve by dot notation.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H P : Graph α β} {u v w x y c : α} {e : β} {W W₁ W₂ : List β}

/-! ### Walks and vertex deletion

Mathlib's `Graph.deleteVerts` takes a set; a single deleted vertex is `{c}`. -/

/-- **A walk that never visits `c` survives the deletion of `c`.** Every deletion argument in
the ear layer reduces to this. -/
theorem IsWalk.avoiding (h : G.IsWalk u W v) (hc : c ∉ G.walkVertices u W) :
    (G.deleteVerts {c}).IsWalk u W v := by
  induction h with
  | @nil x hx =>
    refine .nil ?_
    rw [vertexSet_deleteVerts]
    exact ⟨hx, by rintro (rfl : x = c); exact hc mem_walkVertices_self⟩
  | @cons u w v e W hl _ ih =>
    have hw : w ∈ G.walkVertices u (e :: W) :=
      mem_walkVertices_cons_of_mem hl mem_walkVertices_self
    have hcw : c ∉ G.walkVertices w W := fun h ↦ hc (mem_walkVertices_cons_of_mem hl h)
    refine .cons ?_ (ih hcw)
    rw [deleteVerts_isLink]
    refine ⟨hl, ?_, ?_⟩
    · rintro (rfl : u ∈ ({c} : Set α))
      exact hc mem_walkVertices_self
    · rintro (rfl : w ∈ ({c} : Set α))
      exact hc hw

/-- Reversal does not change which vertices a walk visits — but it does change the source, so
this is not `Graph.walkVertices_reverse`, which keeps it. -/
theorem IsWalk.reverse_walkVertices (h : G.IsWalk u W v) :
    G.walkVertices v W.reverse = G.walkVertices u W := by
  have h₁ : v ∈ G.walkVertices u W := h.target_mem_walkVertices
  have h₂ : u ∈ G.walkVertices v W := by
    have := h.reverse.target_mem_walkVertices
    rwa [walkVertices_reverse] at this
  rw [walkVertices_reverse]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_) <;>
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
  exacts [h₁, mem_walkVertices_of_mem_covered hcov, h₂, mem_walkVertices_of_mem_covered hcov]

/-- Splitting the visited set along a concatenation. Purely about lists: no walk is needed,
and the middle vertex `w` is arbitrary. -/
theorem walkVertices_append_subset :
    G.walkVertices u (W₁ ++ W₂) ⊆ G.walkVertices u W₁ ∪ G.walkVertices w W₂ := by
  rintro y hy
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  · rw [coveredVertices_append] at hcov
    exact hcov.imp mem_walkVertices_of_mem_covered mem_walkVertices_of_mem_covered

/-! ### Reaching an end of a path after a deletion -/

/-- A vertex of a path other than its source still reaches the target once the source is
deleted: cut the path at the vertex, and the far half never returns to the source. -/
theorem IsPath.reaches_target_of_ne_source (h : G.IsPath u W v)
    (hx : x ∈ G.walkVertices u W) (hxu : x ≠ u) : (G.deleteVerts {u}).Reaches x v := by
  obtain ⟨-, W₂, -, -, h₂, hback⟩ := h.split hx
  exact ⟨W₂, h₂.isWalk.avoiding (hback.resolve_left hxu)⟩

/-- The mirror image, run on the reversed path. -/
theorem IsPath.reaches_source_of_ne_target (h : G.IsPath u W v)
    (hx : x ∈ G.walkVertices u W) (hxv : x ≠ v) : (G.deleteVerts {v}).Reaches x u :=
  h.reverse.reaches_target_of_ne_source (by rwa [h.isWalk.reverse_walkVertices]) hxv

/-- **Deleting any vertex leaves every other vertex of a path able to reach an end.**
Uniform in the deleted vertex `c`: if `c` is on the path the path is cut there and each
remaining vertex sits on a half that runs to that half's far end; if `c` is off the path the
path is cut at the vertex itself and its near half, reversed, runs to the source. -/
theorem IsPath.reaches_an_end (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W)
    (hxc : x ≠ c) :
    (G.deleteVerts {c}).Reaches x u ∨ (G.deleteVerts {c}).Reaches x v := by
  by_cases hc : c ∈ G.walkVertices u W
  · obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := h.split hc
    rcases walkVertices_append_subset (w := c) hx with hx₁ | hx₂
    · exact Or.inl (h₁.reaches_source_of_ne_target hx₁ hxc)
    · exact Or.inr (h₂.reaches_target_of_ne_source hx₂ hxc)
  · -- The deletion misses the path entirely, so the near half survives whole.
    obtain ⟨W₁, W₂, rfl, h₁, -, -⟩ := h.split hx
    refine Or.inl ⟨W₁.reverse, h₁.reverse.isWalk.avoiding ?_⟩
    rw [h₁.isWalk.reverse_walkVertices]
    exact fun hmem ↦ hc (walkVertices_mono (List.subset_append_left _ _) hmem)

/-! ### A graph that is a path -/

/-- `P.IsPathGraph u W v` : the graph `P` *is* the path from `u` to `v` along `W`. Its own
edges are exactly the entries of `W`, and its vertices are exactly the ones that path visits.

The edge list is an index rather than an existential because its order is used: an argument
that deletes a vertex cuts `W` in two, and a graph whose edges were only a set would have to
recover the order first. -/
structure IsPathGraph (P : Graph α β) (u : α) (W : List β) (v : α) : Prop where
  /-- The graph's own edges, in the given order, form a path from one end to the other. -/
  isPath : P.IsPath u W v
  /-- The graph has no edges beyond that path's. -/
  edgeSet_eq : E(P) = {e | e ∈ W}
  /-- The graph has no vertices beyond the ones that path visits. -/
  vertexSet_eq : V(P) = P.walkVertices u W

namespace IsPathGraph

theorem isWalk (h : P.IsPathGraph u W v) : P.IsWalk u W v := h.isPath.isWalk

/-- A vertex of a path graph is visited by its path. -/
theorem mem_walkVertices (h : P.IsPathGraph u W v) (hx : x ∈ V(P)) :
    x ∈ P.walkVertices u W := h.vertexSet_eq ▸ hx

theorem source_mem (h : P.IsPathGraph u W v) : u ∈ V(P) := h.isPath.left_mem

/-- A path graph is connected: every vertex is visited, so the path's own prefix runs to it
from the source. -/
theorem connected (h : P.IsPathGraph u W v) : P.Connected := by
  refine Connected.of_hub h.source_mem fun x hx ↦ ?_
  obtain ⟨W₁, -, -, h₁, -, -⟩ := h.isPath.split (h.mem_walkVertices hx)
  exact ⟨W₁, h₁.isWalk⟩

/-- **Whatever vertex is deleted, every remaining vertex of a path graph still reaches one of
its two ends.** This is what the ear argument turns on: the ear's two ends are the only
vertices it shares with the graph it is glued to, so a surviving vertex of the ear has to
reach one of them inside the ear itself. -/
theorem reaches_an_end (h : P.IsPathGraph u W v) (hx : x ∈ V(P)) (hxc : x ≠ c) :
    (P.deleteVerts {c}).Reaches x u ∨ (P.deleteVerts {c}).Reaches x v :=
  h.isPath.reaches_an_end (h.mem_walkVertices hx) hxc

end IsPathGraph

/-! ### Constructing a path graph -/

/-- The spanned subgraph really is a subgraph. -/
theorem pathGraphOf_le (h : G.IsWalk u W v) : G.pathGraphOf u W ≤ G :=
  le_trans (induce_le h.walkVertices_subset) restrict_le

/-- Its edges are exactly the walk's. One inclusion is the definition; the other needs the
walk, to know that an entry of `W` is an edge of `G` at all and that its ends are visited. -/
theorem pathGraphOf_edgeSet (h : G.IsWalk u W v) : E(G.pathGraphOf u W) = {e | e ∈ W} := by
  ext f
  rw [edgeSet_eq_setOf_exists_isLink]
  simp only [pathGraphOf_isLink, mem_setOf_eq]
  refine ⟨fun ⟨_, _, hf, _⟩ ↦ hf, fun hf ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hf)
  exact ⟨a, b, hf, hab, mem_walkVertices_of_mem_covered ⟨f, hf, hab.inc_left⟩,
    mem_walkVertices_of_mem_covered ⟨f, hf, hab.inc_right⟩⟩

/-! ### Finiteness

A walk visits finitely many vertices and takes finitely many edges, so the graph it spans is
finite with no hypothesis on the ambient graph. -/

/-- A step of a walk adds exactly one vertex to the visited set. -/
theorem walkVertices_cons (hl : G.IsLink e u w) :
    G.walkVertices u (e :: W) = insert u (G.walkVertices w W) := by
  ext x
  constructor
  · intro hx
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    exacts [Set.mem_insert _ _, Set.mem_insert_of_mem _ hx']
  · intro hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx'
    exacts [mem_walkVertices_self, mem_walkVertices_cons_of_mem hl hx']

theorem IsWalk.finite_walkVertices (h : G.IsWalk u W v) : (G.walkVertices u W).Finite := by
  induction h with
  | nil => rw [walkVertices_nil]; exact Set.finite_singleton _
  | @cons u w v e W hl _ ih => rw [walkVertices_cons hl]; exact Set.Finite.insert u ih

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Ear
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.chainUnion_succ _root_.Graph.mem_vertexSet_induce_component _root_.Graph.pointSet_union _root_.Graph.vertexSet_union_pathGraphOf
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Ears

The ear decomposition: `lem:subdivision-ear-preserve` in both halves, and the step of
`lem:relative-ear` that grows a 2-connected subgraph towards the graph containing it.

## Rerouting is the engine of half (a)

`Graph.Reaches.reroute` says the obvious thing in the one form every consumer wants: if every
edge but `e` survives from `G` into `H`, and whatever `e` joins in `G` is joined in `H` by
other means, then `H` reaches whatever `G` reaches. A walk that took `e` takes the
replacement route instead, and the induction is over the walk.

Its `hends` premise is stated as "**whatever** `e` joins in `G` is joined in `H`", not as "the
two named ends are joined". That is what makes the premise dischargeable in the case where
`e` is not an edge of `G` at all: it is then vacuous. `Graph.Reaches.across_edge_replacement`
is the specialisation the subdivision runs on, and it is where the vacuous case is used — its
`routed` premise carries the three-way choice the blueprint's proof makes in prose:

* reroute along the new path — the deleted vertex is not on it, so the path survives whole;
* reroute around the old graph — the deleted vertex *is* on the path, so the old graph is
  untouched and the replaced edge was not a bridge (`Graph.IsTwoConnected.no_bridge`);
* do not reroute at all — the deleted vertex is an end of the replaced edge, so no surviving
  walk could have taken that edge.

## Half (a) is stated for a path

`Graph.IsTwoConnected.replace_edge_by_path` replaces an edge by a whole path, not by a single
new vertex. Nothing in the argument cares how long the replacement is, and the general form is
what a subdivision needs: subdividing one edge by one vertex is the case where the path has
two edges.

## Half (b) does not need the blueprint's freshness hypothesis

`Graph.IsTwoConnected.ear` attaches an ear, and the blueprint's "whose internal vertices are
new" is **not** assumed — the proof does not use it. What carries the argument is
`Graph.IsPathGraph.reaches_an_end`: whatever vertex is deleted, every remaining vertex of the
path still reaches one of the two ends. The two ends live in a 2-connected graph, at least one
of them survives the deletion, and that survivor is the hub everything routes through.

Half (a) *does* use freshness, and for a real reason: without it the deleted vertex could sit
both on the replacement path and inside the old graph, and then neither of the two routes
between the replaced edge's ends need exist.

## Finding the ear

`Graph.IsTwoConnected.ear_exists` needs neither the components of `G - V(H)` nor a shortest
path, which is what the blueprint's proof reaches for. The ear is *found*: walk out of the
subgraph to a vertex outside it, take the edge where the walk **first** leaves the subgraph
(`Graph.IsWalk.crossing`), and walk back from that edge's outer end to a *different* vertex of
the subgraph inside `G` minus the edge's inner end — a graph that is connected because `G` is
2-connected, and whose walks therefore never touch the inner end. That walk with the crossing
edge in front is a path of `G` between two vertices of the subgraph, and the crossing edge is
one the subgraph did not have.

`Graph.pathGraphOf` turns it into a graph and `Graph.IsTwoConnected.grows_by_ear` glues it on.
Termination — the blueprint's "finiteness terminates the process" — is not here; this is the
single step, and a consumer that counts edges iterates it.

## Looplessness

`Graph.IsTwoConnected.ear_exists` is the one statement here that has to assume the graph has
no loop, and the hypothesis is not bureaucracy: adding a loop to a 2-connected graph leaves it
2-connected, so a 2-connected subgraph missing only a loop grows by no ear at all, and the
conclusion — a path between *distinct* vertices — is false. It is used only in the degenerate
branch where every vertex is already present and the missing object is an edge. A plane
consumer discharges it from its drawing.

## Blueprint

* `Graph.IsTwoConnected.replace_edge_by_path` — `lem:subdivision-ear-preserve` (a), "every
  subdivision of `G` is 2-connected", stated for a replacement path of any length.
* `Graph.IsTwoConnected.ear` — `lem:subdivision-ear-preserve` (b), "if `P` is a path whose
  distinct endpoints lie in `G` … then `G ∪ P` is 2-connected".
* `Graph.IsTwoConnected.ear_exists`, `Graph.IsTwoConnected.grows_by_ear` — the step of
  `lem:relative-ear`, "`G` is obtained from `H` by repeatedly adding paths whose distinct
  endpoints are already present".
* `Graph.Reaches.reroute`, `Graph.Reaches.across_edge_replacement` — the blueprint's "the
  remaining part of the subdivided edge attaches `w` to `u` or `v`" together with "a
  2-connected graph has no bridge", turned into one transfer lemma.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K P : Graph α β} {a b c s t u v x y z : α} {e f : β}
  {W D : List β}

/-! ### The union of two subgraphs

`Graph.union` and the two inclusions *into* it live in `Schoenflies/Graph/TwoConnected.lean`;
this is the inclusion *out of* it, which the ear construction needs in order to know that the
enlarged subgraph is still a subgraph. It is general and belongs beside the other two — the
integrator should hoist it. -/

/-! ### Rerouting one edge -/

/-! ### Attaching an ear -/

/-- **`lem:subdivision-ear-preserve` (b): attaching an ear preserves 2-connectivity.** `P` is
a path whose two distinct ends lie in the 2-connected graph `G`; then `G ∪ P` is 2-connected.

The blueprint's hypothesis that the ear's internal vertices are new is **not** needed. Delete
a vertex `c`. One of the ear's two ends survives, and it is the hub: `G - c` is connected and
contains it, and every surviving vertex of the ear reaches one of the two ends inside the ear
(`Graph.IsPathGraph.reaches_an_end`) — an end which, having been reached after the deletion, is
itself not `c`, so it lies in `G - c` too. -/
theorem IsTwoConnected.ear (hG : G.IsTwoConnected) (hcompat : G.Compatible P)
    (hP : P.IsPathGraph u W v) (huv : u ≠ v) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (G.union P).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G P).vertexSet_mono
  connected := hcompat.union_connected hG.connected hP.connected hu hP.source_mem
  deleteVerts_connected := by
    intro c _
    -- One of the ear's two ends survives the deletion; it is the hub.
    obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
      by_cases hcu : u = c
      · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
      · exact ⟨u, hu, hcu⟩
    have hGle : G.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono (left_le_union G P) _
    have hPle : P.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono hcompat.right_le_union _
    have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
    -- Every surviving vertex of the graph side reaches the hub inside the graph side.
    have key : ∀ x ∈ V(G), x ≠ c → ((G.union P).deleteVerts {c}).Reaches z x := fun x hx hxc ↦
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hzG hzc)
        (mem_deleteVerts_singleton_of_ne hx hxc)).mono hGle
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne
      ((left_le_union G P).vertexSet_mono hzG) hzc) fun x hx ↦ ?_
    rw [vertexSet_deleteVerts] at hx
    obtain ⟨hxS, hxc⟩ := hx
    have hxc' : x ≠ c := by simpa using hxc
    rcases (hxS : x ∈ V(G) ∪ V(P)) with hxG | hxP
    · exact key x hxG hxc'
    · -- On the ear, one of the two ends is still reachable, and it survived the deletion.
      rcases hP.reaches_an_end hxP hxc' with hr | hr
      · have hune : u ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key u hu hune).trans (hr.mono hPle).symm
      · have hvne : v ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key v hv hvne).trans (hr.mono hPle).symm

/-! ### Replacing an edge by a path -/

/-! ### Finding an ear -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Tree
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Trees

A tree is a connected graph in which no edge lies on a cycle. What the blueprint asks of a
tree is always about its leaves, and every such question starts the same way: **take a longest
path**. Neither of its ends can carry a second edge — an edge back onto the path would close a
cycle, and an edge off the path would make a longer path — so both ends are leaves.

## The three theorems this file exists for

* deleting a leaf leaves a tree (`Graph.IsTree.delete_leaf`),
* a tree on `n` vertices has `n - 1` edges (`Graph.IsTree.edge_count`), by peeling leaves,
* **a tree with exactly three leaves has one vertex of degree three**
  (`Graph.IsTree.three_leaves`), which is where the handshake lemma finally pays.

## Why a longest path rather than a maximal one

A longest path is produced by `Nat.findGreatest` over the lengths of paths, bounded because a
path repeats no edge (`Graph.IsPath.nodup`) and the graph has finitely many. That needs
`Graph.Finite` and nothing else — in particular no well-founded recursion and no choice of a
maximal element in an order. The bound is the only place finiteness enters the longest-path
argument.

## Vertex deletion

`Graph.deleteVerts` is Mathlib's. What this file adds is the transfer lemma every deletion
argument reduces to — `Graph.IsWalk.deleteVerts`, a walk that never visits a deleted vertex
survives — together with the reason the hypothesis is ever available:
`Graph.IsLeaf.path_avoids`, a path whose two ends are elsewhere never visits a vertex of
degree one. To pass through such a vertex a path would have to arrive and leave along its
single edge, and a path takes no edge twice.

## Blueprint

* `Graph.IsTree.three_leaves` — `lem:three-leaf-tree` ("a finite tree with exactly three
  leaves has exactly one vertex of degree at least three; that vertex has degree exactly
  three, and every other vertex is a leaf or has degree two"), used at the H5 step of
  `lem:two-components` to produce the three internally disjoint branches of each spanning
  tree `T_i`.
* `Graph.IsTree.edge_count` — the same lemma's "a finite tree with `n` vertices has exactly
  `n - 1` edges".
* `Graph.IsTree.has_leaf`, `Graph.IsTree.delete_leaf` — its "a tree with an edge has a leaf,
  since an endpoint of a maximal simple path has no neighbor off the path, and a second
  neighbor on the path would close a cycle; deleting a leaf and its edge leaves a tree".
* `Graph.IsTree` — the trees of `lem:two-components` ("take a minimal connected subgraph
  `T_i` spanning the three terminals. It is a tree").

## Namespace

The root `Graph` namespace, as in `Walk.lean`, `Degree.lean` and `Cycle.lean`.
-/

open Set
open scoped Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {P W : List β}

namespace Graph

/-! ### Trees -/

/-! ### A walk departs along an edge -/

/-- A path between two distinct vertices takes at least one edge. -/
theorem IsPath.ne_nil (h : G.IsPath u P v) (huv : u ≠ v) : P ≠ [] := by
  rintro rfl
  exact huv h.isWalk.eq_of_nil

/-! ### A path leaves its source once and for all

Two edges of a path incident with its source are the same edge: the departing step is the
only candidate, since a later edge at the source would put the source back among the vertices
the rest of the path visits. -/

/-! ### A longest path -/

/-! ### Both ends of a longest path are leaves -/

/-! ### A path steers clear of a leaf -/

/-! ### Vertex deletion -/

/-! ### A tree has one edge fewer than it has vertices -/

/-! ### A tree with three leaves

The blueprint's `lem:three-leaf-tree`, and the one place the handshake lemma is used. Three
leaves contribute one apiece to the degree sum, every other vertex contributes two plus
whatever it carries above two, and the totals leave exactly one degree to carry. -/

end Graph
end

section
-- module Solutions.Q146_CD.FaceCycles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
/-!
# Face cycles: the base cycle, and the faces of a plane graph that grows by ears

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as
its boundary and is one of the two complementary regions of that cycle* — is proved by growing
the graph from a cycle by ears (`Graph.IsTwoConnected.ear_decomposition`) and applying
`thm:polygonal-crosscut` at each step. This file supplies everything in that proof that is not
the crosscut application itself. **The lemma is not proved here**; see "What is missing" below,
which says exactly what is in the way.

## The base cycle

The blueprint's first paragraph, in full. *"First choose a cycle of length at least three.
Such a cycle exists: under our convention the graph has at least three vertices, and every
vertex has at least two distinct neighbors. Indeed, if a vertex `v` had only one distinct
neighbor `w`, then deleting `w` would isolate `v` from some third vertex, contrary to
2-connectivity. Now take a maximal simple path. An endpoint has a neighbor on the path other
than its predecessor, and the resulting closed subpath is a cycle of length at least three."*

`Graph.IsTwoConnected.exists_adj_ne` is the two-neighbours sentence; "take a maximal simple
path" is `Graph.exists_longest_path`, already in `Schoenflies/Graph/Tree.lean` and not rebuilt
here; and `Graph.IsTwoConnected.exists_long_cycle` is the conclusion, packaged as
`Graph.IsLongCycle`, a cycle together with a *named* third vertex. Naming the third vertex
rather than counting is what both consumers want: the counting clause of
`Graph.IsTwoConnected`, and — later — the non-degeneracy of the polygon the cycle draws.

`Graph.cycleGraph` is that cycle as a subgraph, and `Graph.IsLongCycle.isTwoConnected` is
*"the cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`"*. This
is the one place "length at least three" is used: a two-vertex cycle is a `Graph.banana`, and
`Graph.not_isTwoConnected_banana` says it is not 2-connected.

## One step of the induction

Adding an ear removes the ear's own point set from the exterior and changes nothing else:
`Graph.pointSet_union`, `Graph.exterior_union` and `Graph.face_union_eq_of_disjoint` are
*"all other faces are unchanged"*.

`Graph.IsDrawing.exists_face_of_ear` is *"its interior is connected and disjoint from the
current graph, so it lies in one current face `F`"*: the ear's realisation without its two ends
is the interior of an arc, hence connected
(`Schoenflies.IsArcBetween.isConnected_diff`), and it misses the drawing of the current
subgraph altogether (`Graph.IsDrawing.edgesCover_inter_pointSet`).
`Graph.IsDrawing.ends_mem_frontier_face` is the next sentence, *"the ear's two endpoints are
limits of its interior, which lies in `F`, so they lie on `∂F`"* — which is what makes the ear
a crosscut of that face.

`Graph.IsDrawing.mono` — a subgraph of a plane graph is a plane graph, with the same drawing —
is what lets the induction talk about the faces of the current subgraph at all.

## An interface repair

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)`, which `Graph.IsTwoConnected.relative_ear_exists` proves and which
`Graph.IsTwoConnected.relative_grows_by_ear` drops on the way. A geometric consumer needs it:
without it the ear may be drawn right on top of the current subgraph, and
`Graph.IsDrawing.edgesCover_inter_pointSet` is false. `Graph.ear_edges_notMem_or_union_eq`
recovers it in the only form available from the outside — either every edge of the ear is new,
or the ear is a single edge the subgraph already had and the enlarged graph *is* the old graph,
so the step has nothing to prove. The better fix is for the integrator to add the clause to
`relative_grows_by_ear` and to `ear_decomposition`; that would make this lemma unnecessary.

## What is missing

The crosscut application, and therefore `lem:face-cycles` itself. `thm:polygonal-crosscut` is
available as `Schoenflies.IsPolygonalCrosscut` and `Schoenflies.polygonal_crosscut`, whose
hypotheses are stated for `Schoenflies.ClosedPolygon`s: an explicit cyclic vertex list with
`vertex_inj`, `edges_meet` and `corner` (no two consecutive edges collinear). The realisation
of a graph cycle arrives here as a **set** — `Graph.edgesCover drawing (e :: D)` — which
`Graph.IsDrawing.cycle_isJordanCurve` knows to be a Jordan curve and `Graph.polygonal_redrawing`
knows to be polygonal. Turning such a set into a `ClosedPolygon` (enumerate its vertices
cyclically, delete the redundant collinear ones, and derive `vertex_inj` and `edges_meet` from
simplicity) is a construction `main` does not have, and the same construction is needed again
for the two curves `Aᵢ ∪ P` that the crosscut produces. Nothing below pretends to it, and no
statement below is weaker than its blueprint counterpart.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`. The two arc lemmas are stated in
`Schoenflies`, where the rest of the arc theory lives.

## Blueprint

* `Graph.IsTwoConnected.exists_adj_ne` — "every vertex has at least two distinct neighbors".
* `Graph.IsLongCycle`, `Graph.IsTwoConnected.exists_long_cycle` — "the resulting closed subpath
  is a cycle of length at least three".
* `Graph.cycleGraph`, `Graph.IsLongCycle.isTwoConnected` — "the cycle `C` is 2-connected, so
  Lemma `lem:relative-ear` builds the graph from `C`".
* `Graph.ear_edges_notMem_or_union_eq` — the ear's edges are new, or the ear is not an ear.
* `Graph.pointSet_union`, `Graph.exterior_union`, `Graph.face_union_subset`,
  `Graph.face_union_eq_of_disjoint` — "all other faces are unchanged".
* `Graph.IsDrawing.mono` — the current subgraph is itself a plane graph.
* `Schoenflies.IsArcBetween.isConnected_diff`,
  `Schoenflies.IsArcBetween.left_mem_closure_diff`, `…right_mem_closure_diff`,
  `Graph.IsDrawing.edgesCover_inter_pointSet`, `Graph.IsDrawing.exists_face_of_ear`,
  `Graph.IsDrawing.ends_mem_frontier_face` — "its interior is connected and disjoint from the
  current graph, so it lies in one current face `F` … the ear's two endpoints are limits of its
  interior, which lies in `F`, so they lie on `∂F`; the ear is therefore a crosscut of that
  side".
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K B : Graph α β} {u v w x y z c : α} {e f g : β} {D W : List β}

/-! ## Two distinct neighbours -/

/-! ## The base cycle

"Take a maximal simple path" is `Graph.exists_longest_path`, already in
`Schoenflies/Graph/Tree.lean` — it is what the three-leaf lemma runs on — so nothing here
rebuilds it. -/

/-- **A path from a vertex back to itself is empty.** The first step would depart from the
vertex the rest of the path arrives at, which the freshness clause forbids. -/
theorem IsPath.eq_nil_of_eq (h : G.IsPath u W u) : W = [] := by
  cases h with
  | nil => rfl
  | cons _ hT hfresh => exact absurd hT.target_mem_walkVertices hfresh

/-! ## The cycle as a subgraph, and its 2-connectivity

`Graph.IsTwoConnected.ear_decomposition` starts from a 2-connected subgraph. The subgraph the
blueprint starts from is the base cycle, and this section builds it and proves it 2-connected.
This is the one place where "length at least three" is used: a two-vertex cycle is a
`Graph.banana`, and `Graph.not_isTwoConnected_banana` says it is not 2-connected. -/

namespace IsCycleThrough

variable (hc : G.IsCycleThrough e u v D)
include hc

/-- Going round: the detour and then the edge is a closed walk at the source. -/
theorem isWalk_round : G.IsWalk u (D ++ [e]) u :=
  hc.isPath.isWalk.append (IsWalk.single hc.isLink.symm)

theorem cycleGraph_le : G.cycleGraph u e D ≤ G := pathGraphOf_le hc.isWalk_round

theorem cycleGraph_edgeSet : E(G.cycleGraph u e D) = {f | f ∈ D ++ [e]} :=
  pathGraphOf_edgeSet hc.isWalk_round

theorem left_mem_cycleGraph : u ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact mem_walkVertices_self

theorem right_mem_cycleGraph : v ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact hc.isPath.target_mem_walkVertices

/-- The edge of the cycle really is an edge of the cycle graph, joining the same two ends. -/
theorem cycleGraph_isLink : (G.cycleGraph u e D).IsLink e u v :=
  pathGraphOf_isLink.2 ⟨by simp, hc.isLink,
    hc.walkVertices_round ▸ mem_walkVertices_self,
    hc.walkVertices_round ▸ hc.isPath.target_mem_walkVertices⟩

/-- The cycle graph is connected: every vertex it has is visited by the detour, and the
detour's own prefix runs there from the source. -/
theorem cycleGraph_connected : (G.cycleGraph u e D).Connected := by
  refine Connected.of_hub hc.left_mem_cycleGraph fun x hx ↦ ?_
  rw [hc.cycleGraph_vertexSet] at hx
  obtain ⟨W₁, W₂, hcat, h₁, -, -⟩ := hc.isPath.split hx
  refine ⟨W₁, h₁.isWalk.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg ↦ ?_⟩
  rw [hc.cycleGraph_edgeSet]
  exact List.mem_append_left _ (hcat ▸ List.mem_append_left _ hg)

end IsCycleThrough

/-! ## An ear that is not new

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)` that `Graph.IsTwoConnected.relative_ear_exists` proves and that
`Graph.IsTwoConnected.relative_grows_by_ear` drops. A *geometric* consumer needs it: the ear's
drawing has to miss the drawing of the current subgraph, and an edge shared with `B` would sit
right on it.

It is recoverable, and this section recovers it. An edge of the ear that `B` already has must
join the ear's two ends; the ear is then that single edge, and the enlarged graph is the old
one, so the step has nothing to prove. The integrator may prefer to add the clause to
`relative_grows_by_ear` and to `ear_decomposition` instead — that is the better fix, and it
makes this section unnecessary. -/

/-! ## The faces of a graph that grows

Adding an ear removes the ear's own point set from the exterior and changes nothing else. That
is the whole of "all other faces are unchanged", and the half of "its interior is connected and
disjoint from the current graph, so it lies in one current face `F`" that is pure topology. -/

section Plane

open Schoenflies

variable {β : Type*} {G B P : Graph Plane β} {drawing : β → ℝ → Plane} {z a b : Plane}
  {S : Set Plane} {D : List β}

/-- Adding a graph removes exactly its own point set from the exterior. -/
theorem exterior_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    exterior (B.union P) drawing = exterior B drawing \ pointSet P drawing := by
  rw [exterior, exterior, pointSet_union, Set.compl_union]
  rfl

/-- A face of the enlarged graph lies inside a face of the old one. -/
theorem face_union_subset : face (B.union P) drawing z ⊆ face B drawing z := by
  by_cases hz : z ∈ exterior (B.union P) drawing
  · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_face hz) fun w hw ↦ ?_
    exact ((exterior_union B P drawing) ▸ face_subset_exterior _ _ _ hw).1
  · rw [face, connectedComponentIn_eq_empty hz]
    exact Set.empty_subset _

/-- **"All other faces are unchanged."** A face the ear does not touch survives the ear. -/
theorem face_union_eq_of_disjoint (hz : z ∈ exterior B drawing)
    (hdis : Disjoint (face B drawing z) (pointSet P drawing)) :
    face (B.union P) drawing z = face B drawing z := by
  refine Set.Subset.antisymm face_union_subset ?_
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_face hz) fun w hw ↦ ?_
  rw [exterior_union]
  exact ⟨face_subset_exterior _ _ _ hw, fun hwP ↦ Set.disjoint_left.1 hdis hw hwP⟩

/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face."** The topological half: a nonempty preconnected subset of the exterior lies in one
face. -/
theorem exists_face_of_isPreconnected (hS : IsPreconnected S) (hSne : S.Nonempty)
    (hsub : S ⊆ exterior B drawing) :
    ∃ z ∈ exterior B drawing, S ⊆ face B drawing z := by
  obtain ⟨z, hz⟩ := hSne
  exact ⟨z, hsub hz, hS.subset_connectedComponentIn hz hsub⟩

/-! ### The ear lies in one face

The blueprint's *"its interior is connected and disjoint from the current graph, so it lies in
one current face `F`"*, in full. -/

/- "An arc without its two endpoints is connected" is
`Schoenflies.IsArcBetween.isConnected_diff`, now in `Schoenflies/Subarc.lean`. -/

/-- **The ear's realisation meets the drawing of the current subgraph only in the ear's two
ends.** Two cases, and both come down to the ear's freshness clause: a point of the ear on a
*vertex* of `B` is an end of the edge of the ear it lies on
(`Graph.IsDrawing.vertex_mem_edgeArc`), and a point of the ear on an *edge* of `B` is a vertex
incident with both (`Graph.IsDrawing.edge_inter`) — the two edges being distinct because no
edge of the ear belongs to `B`. Either way the point is a vertex of `B` that the ear visits,
which the freshness clause makes one of the ear's two ends. -/
theorem IsDrawing.edgesCover_inter_pointSet (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    edgesCover drawing D ∩ pointSet B drawing ⊆ {a, b} := by
  -- A vertex of `B` that an edge of the ear is incident with is one of the ear's two ends.
  have key : ∀ p, (∃ f ∈ D, G.Inc f p) → p ∈ V(B) → p = a ∨ p = b := by
    rintro p ⟨f, hf, hinc⟩ hpB
    by_contra hcon
    push Not at hcon
    exact hint p (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hcon.1 hcon.2 hpB
  rintro p ⟨hpD, hpB⟩
  obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hpD
  have hfG : f ∈ E(G) := hpath.edge_mem hf
  rcases hpB with hpV | hpE
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hfG
    have hinc : G.Inc f p := by
      rcases hG.vertex_mem_edgeArc hxy (hBG.vertexSet_mono hpV) hpf with rfl | rfl
      exacts [hxy.inc_left, hxy.inc_right]
    exact key p ⟨f, hf, hinc⟩ hpV
  · simp only [Set.mem_iUnion, exists_prop] at hpE
    obtain ⟨g, hgB, hpg⟩ := hpE
    have hfg : f ≠ g := fun hh ↦ hnew f hf (hh ▸ hgB)
    obtain ⟨-, hincf, hincg⟩ := hG.edge_inter hfG (hBG.edgeSet_mono hgB) hfg hpf hpg
    exact key p ⟨f, hf, hincf⟩ (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hincg)

/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face `F`."** The ear's realisation without its two ends is an arc's interior, hence connected,
and it misses the drawing of `B` altogether, so it lies in a single face. -/
theorem IsDrawing.exists_face_of_ear (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b) (hab : a ≠ b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    ∃ z ∈ exterior B drawing, edgesCover drawing D \ {a, b} ⊆ face B drawing z := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hconn := harc.isConnected_diff
  refine exists_face_of_isPreconnected hconn.isPreconnected hconn.nonempty fun w hw hwB ↦ ?_
  exact hw.2 (hG.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hwB⟩)

/-! ### A subgraph of a plane graph is a plane graph

The induction speaks of the faces of the *current* subgraph, so every step needs the current
subgraph to be a plane graph in its own right. Nothing has to be redrawn: the same drawing
serves. General, and not in `Schoenflies/Graph/Drawing.lean`; the integrator may want to hoist
it. -/

/-- **A subgraph of a plane graph is a plane graph**, with the same drawing. -/
theorem IsDrawing.mono (hG : IsDrawing G drawing) (hBG : B ≤ G) : IsDrawing B drawing where
  edge_param := fun e he ↦ by
    obtain ⟨hc, hi, hl⟩ := hG.edge_param (hBG.edgeSet_mono he)
    exact ⟨hc, hi, (hBG.isLink_iff he).2 hl⟩
  vertex_mem_edgeArc := fun _ _ _ _ hl hv hmem ↦
    hG.vertex_mem_edgeArc (hl.mono hBG) (hBG.vertexSet_mono hv) hmem
  edge_inter := fun e f he hf hef p hpe hpf ↦ by
    obtain ⟨-, hince, hincf⟩ :=
      hG.edge_inter (hBG.edgeSet_mono he) (hBG.edgeSet_mono hf) hef hpe hpf
    obtain ⟨y, hy⟩ := hince
    obtain ⟨y', hy'⟩ := hincf
    exact ⟨mem_vertexSet_of_inc_of_mem_edgeSet hBG he ⟨y, hy⟩,
      ⟨y, (hBG.isLink_iff he).2 hy⟩, ⟨y', (hBG.isLink_iff hf).2 hy'⟩⟩

/-! ### The ear's ends lie on the boundary of the face its interior lies in -/

/- "An endpoint of an arc is a limit of the arc's interior" is
`Schoenflies.IsArcBetween.left_mem_closure_diff` / `…right_mem_closure_diff`, hoisted into
`Schoenflies/Subarc.lean` alongside `…isConnected_diff`. This module had its own copy, with the
same statement as the one in `Schoenflies/AlternatingCrosscuts.lean`; the two modules do not
import each other, so the build accepted both. -/

set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- **"The ear's two endpoints are limits of its interior, which lies in `F`, so they lie on
`∂F`."** This is the hypothesis `thm:polygonal-crosscut` needs of a crosscut: its two ends are
on the boundary curve of the region it cuts. -/
theorem IsDrawing.ends_mem_frontier_face (hG : IsDrawing G drawing)
    (hopen : IsOpen (face B drawing z)) (hpath : G.IsPath a D b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hsub : edgesCover drawing D \ {a, b} ⊆ face B drawing z) :
    a ∈ frontier (face B drawing z) ∧ b ∈ frontier (face B drawing z) := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hnot : ∀ y ∈ V(B), y ∉ face B drawing z := fun y hy hyf ↦
    face_subset_exterior _ _ _ hyf (vertexSet_subset_pointSet hy)
  refine ⟨⟨closure_mono hsub harc.left_mem_closure_diff, ?_⟩,
    ⟨closure_mono hsub harc.right_mem_closure_diff, ?_⟩⟩
  · rw [hopen.interior_eq]; exact hnot a ha
  · rw [hopen.interior_eq]; exact hnot b hb

end Plane

end Graph
end

section
-- module Solutions.Q146_CD.Realization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing a polygonal Jordan curve as a `ClosedPolygon`

The blueprint's "simple closed polygonal curve" is set-theoretic: an `IsJordanCurve` that is
also `IsPolygonal`, with no condition on vertices at all. The development works instead with
`Schoenflies.ClosedPolygon`, a cyclic vertex list carrying a `corner` field — no three
consecutive vertices collinear. That field is a *presentation* condition, strictly stronger than
the blueprint's notion, and until now nothing said that a set-level polygonal Jordan curve
admits such a presentation. This module proves it.

## How the vertex list is found

The curve is *not* read off the vertex list `IsPolygonal` hands over: that list may retrace
itself, cross itself, and repeat segments, and it carries no order along the curve. Two
structures are laid over the point set instead and then matched.

* **From the plane side**, the overlay of `Schoenflies/OverlayGraph.lean`, with the graph
  discarded: `Schoenflies.IsClean` is a finite list of nondegenerate segments occupying the
  curve, with pairwise disjoint interiors and no end interior to any of them. Around an interior
  point of a piece the curve *is* that piece (`IsClean.exists_ball_subset_seg`), so the piece
  interiors are separated by honest open sets of the plane (`Schoenflies.nearPiece`) and a
  connected subset of the curve away from the ends lies inside a single piece.
* **From the curve side**, the loop's parameters at which it reaches an end of a piece. They
  form a finite subset of `[0, 1)` containing `0` — `0` because the loop's start is put on the
  cut list, so that the last gap is the one that closes the curve — and, listed in increasing
  order, they cut `[0, 1)` into gaps.

The two match: a gap image is connected and misses the ends, so it lies in one piece interior;
and the interior is connected and covered by the *closed* gap images, so it lies in that one
gap. Gaps and pieces therefore correspond one to one, the ends of a gap are the ends of its
piece, and the ends listed in the loop's order are a cyclic vertex list whose edges are the
pieces. That list satisfies `vertex_inj` and `edges_meet` but not `corner`, which is what
`Schoenflies.PrePolygon` is for; `corner` is then arranged by deleting redundant vertices.

## Blueprint

* `Schoenflies.PrePolygon` — a `ClosedPolygon` less the `corner` field: the blueprint's simple
  closed polygonal curve *presented by a vertex list*, redundant vertices allowed.
* `Schoenflies.PrePolygon.deleteLast`, `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`
  — the blueprint's opening move in Lemma 1.8, "delete redundant vertices at which two
  consecutive edges are collinear", as an operation rather than an invariant.
* `Schoenflies.IsClean`, `Schoenflies.exists_isClean` — Lemma 3.7 (polygonal overlay) with the
  combinatorics dropped: what the overlay says about the point set alone.
* `Schoenflies.par`, `Schoenflies.parNext`, `Schoenflies.exists_mem_gap` — the parameters in
  increasing order, and that their gaps tile `[0, 1)`.
* `Schoenflies.exists_prePolygon_of_isJordanCurve`, `Schoenflies.exists_closedPolygon` — §1:
  every simple closed polygonal curve, in the blueprint's set-level sense, is the carrier of a
  `ClosedPolygon`.
* `Schoenflies.IsStraightAt`, `Schoenflies.IsCornerAt`,
  `Schoenflies.ClosedPolygon.exists_vertex_eq_of_isCornerAt`,
  `Schoenflies.ClosedPolygon.isCornerAt_vertex` — the vertex set of a realization is *exactly*
  the set of points at which the curve does not run straight. So a named point can be required
  to be a vertex precisely when it is a corner, and no realization has any choice about it.
* `Schoenflies.ClosedPolygon.rotate`, `…isArcBetween_arc`, `…arc_inter` — the two arcs of a
  splitting, as arcs between the two cut vertices meeting exactly there.
* `Schoenflies.two_arcs_unique` — two points cut a Jordan curve into two arcs in only one way.
* `Schoenflies.exists_closedPolygon_corners`, `Schoenflies.exists_closedPolygon_split`,
  `Schoenflies.exists_closedPolygon_arcs`, `Schoenflies.exists_closedPolygon_arcs_ordered` — the
  realization with named corners, with the splitting indices, and with the two arcs identified.
  The last is the shape `Graph.IsHexRealization` asks for.

## The corner hypothesis is not an artefact

`exists_closedPolygon_arcs` requires the two cut points to be corners.
`ClosedPolygon.isCornerAt_vertex` shows that this cannot be dropped: every vertex of every
realization is a corner, so a cut point at which the curve runs straight is a vertex of *no*
realization, and no `ClosedPolygon` with that carrier has an arc ending there. A consumer that
needs to cut at a straight point has to change the curve — bend it there — which is a different
theorem, and is exactly the freedom `Graph.IsK33Config.not_isDrawing` reserves for itself.
-/

open Metric Set unitInterval

namespace Schoenflies

open Plane

/-! ## Polygons before normalization

`PrePolygon` is `ClosedPolygon` with the `corner` field removed. Everything the curve bridge of
`Schoenflies/PolygonBridge.lean` proves about a `ClosedPolygon` — that its carrier is a Jordan
curve, that it is polygonal — uses only `vertex_inj` and `edges_meet`, so it is already true
here; what `corner` buys is the germ argument of the strip lemma, and nothing else. -/

/-! ## Small facts about the cyclic index

`ZMod (m + 3)` has at least three elements; `0`, `1` and `2` are distinct, which is what makes
a vertex, its successor and its predecessor three different vertices. -/

namespace PrePolygon

variable {m : ℕ}

/-! ## Rotation

Reading the same cyclic list from a different starting vertex. It is used once, to bring the
vertex that is about to be deleted to the end of the list. -/

/-! ## Deleting the last vertex

The blueprint's opening move in the strip lemma. The vertex to be deleted is brought to the end
of the list by `rotate`, so only that one case has to be treated. `emb` is the inclusion of the
shortened index set into the old one: the same numeral, one modulus smaller. -/

/-! ## Recognising a redundant vertex

The `corner` field is `det ≠ 0` at every vertex. Where it fails the vertex is *interior* to the
segment joining its two neighbours, never an endpoint of it. That is the geometric content of
`edges_meet`: two edges leaving a vertex in the *same* direction would overlap in a
nondegenerate segment, and `edges_meet` would then put a whole segment inside a two-point
set. -/

variable {m : ℕ} {P : PrePolygon m}

/-! ## Normalization

Delete redundant vertices until none is left. Each deletion shortens the list by one, and the
list can never shrink below three vertices: a triangle with a redundant vertex would have one
edge inside another, which `edges_meet` forbids. -/

/-- Assembling a cyclic vertex family into a `PrePolygon`. The index type is `ZMod n` for an
`n` known only to be at least three, which is what `PrePolygon` asks for after `n` is written
`m + 3`. -/
theorem exists_prePolygon {n : ℕ} (hn : 3 ≤ n) (w : ZMod n → Plane) (hinj : Function.Injective w)
    (hmeet : ∀ i j : ZMod n, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)}) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = ⋃ i, segment ℝ (w i) (w (i + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact ⟨m, ⟨w, hinj, hmeet⟩, rfl⟩

end PrePolygon

/-! ## Clean pieces

The overlay of `Schoenflies/OverlayGraph.lean`, stripped of the graph. All that is wanted from
it is a finite list of segments occupying the curve whose interiors are pairwise disjoint and
none of whose ends is interior to any of them — the geometric content of `lem:polygonal-overlay`
with the combinatorics left out. -/

/-- **Every polygonal set with two points in it has a clean presentation**, and any finite list
of points of it may be required to be among the ends. Lengthening the cut list is free: both
`EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in it. -/
theorem exists_isClean {C : Set Plane} (hC : IsPolygonal C) {a b : Plane} (ha : a ∈ C)
    (hb : b ∈ C) (hab : a ≠ b) (extra : List Plane) :
    ∃ Q : List Piece, IsClean Q C ∧ ∀ p ∈ extra, p ∈ C → ∃ R ∈ Q, p = R.1 ∨ p = R.2 := by
  obtain ⟨vs, rfl⟩ := hC
  have hnd : ∀ P ∈ segsOf vs, P.Nondeg := segsOf_nondeg vs
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  obtain ⟨pts, hEnds, hMeets⟩ := exists_cut_points (segsOf vs)
  refine ⟨overlayPieces (segsOf vs) (pts ++ extra), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [overlayPieces_cover, hcov]
  · exact overlayPieces_nondeg _ hnd
  · intro R hR S hS z hz
    exact overlayPieces_avoids hnd z
      (overlayPieces_ends_cut (fun P hP y hy => List.mem_append_left _ (hEnds P hP y hy)) R hR z hz)
      S hS
  · intro R hR S hS hRS x hx
    refine overlayPieces_disjoint_interiors hnd
      (fun P hP y hy => List.mem_append_left _ (hEnds P hP y hy)) (fun P hP Q hQ hPQ hne => ?_)
      hR hS hRS hx
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hP Q hQ hPQ hne
    exact ⟨u, v, huv, List.mem_append_left _ hu, List.mem_append_left _ hv⟩
  · -- A required point lies on some piece and is interior to none, hence is an end of one.
    intro p hp hpC
    have hpts : p ∈ pts ++ extra := List.mem_append_right _ hp
    have hpcov : p ∈ cover (overlayPieces (segsOf vs) (pts ++ extra)) := by
      rw [overlayPieces_cover, hcov]; exact hpC
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hpcov
    refine ⟨R, hR, ?_⟩
    by_contra hcon
    push Not at hcon
    exact overlayPieces_avoids hnd p hpts R hR
      (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpR)

/-! ## The gaps between the parameters

The loop's parameters at which it visits an end of a piece form a finite subset of `[0, 1)`
containing `0`. Listed in increasing order they cut `[0, 1)` into gaps, one per piece; the last
gap runs to `1`, where the loop closes. This section is pure order theory on `ℝ`. -/

/-- Two points of a nondegenerate pair, each known to be one of two given points, exhaust
them. -/
theorem pair_eq_of_mem_pair {a b p q : Plane} (hab : a ≠ b) (ha : a = p ∨ a = q)
    (hb : b = p ∨ b = q) : (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab

/-- The successor in `ZMod n`, read as a numeral below `n`. -/
theorem zmod_val_succ {n : ℕ} (hn : 1 < n) (j : ZMod n) :
    (j + 1).val = if j.val + 1 < n then j.val + 1 else 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have h1 : (1 : ZMod n).val = 1 := by
    rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num]
    exact ZMod.val_cast_of_lt hn
  rw [ZMod.val_add, h1]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hj : j.val + 1 = n := by have := ZMod.val_lt j; omega
    rw [hj, Nat.mod_self]

/-! ## From a clean presentation to a cyclic vertex list

The loop reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the loop reaches them, are the cyclic
vertex list of a `PrePolygon` whose edges are the pieces. -/

/-- **A polygonal Jordan curve is the carrier of a cyclic vertex list.** -/
theorem exists_prePolygon_of_isJordanCurve {C : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) : ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C := by
  classical
  obtain ⟨f, hf, hfC⟩ := hJ
  -- Two distinct points of `C`, so that the clean presentation does not collapse.
  have hmemC : ∀ s ∈ I, f s ∈ C := fun s hs => hfC ▸ ⟨s, hs, rfl⟩
  have h0C : f 0 ∈ C := hmemC 0 zero_mem_I
  have hhC : f (1 / 2) ∈ C := hmemC _ ⟨by norm_num, by norm_num⟩
  have hne : f 0 ≠ f (1 / 2) := fun he =>
    absurd (hf.injOn ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, by norm_num⟩ he) (by norm_num)
  obtain ⟨Q, hQ, hextra⟩ := exists_isClean hP h0C hhC hne [f 0]
  obtain ⟨R₀, hR₀, hR₀end⟩ := hextra (f 0) (List.mem_singleton_self _) h0C
  have hV₀ : f 0 ∈ endSet Q := ⟨R₀, hR₀, hR₀end⟩
  -- Every point of the curve is reached before the loop closes.
  have hsurj : ∀ z ∈ C, ∃ s ∈ Ico (0 : ℝ) 1, f s = z := by
    intro z hz
    rw [← hfC] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact ⟨0, ⟨le_refl 0, by norm_num⟩, hf.closes⟩
    · exact ⟨s, ⟨hs.1, hlt⟩, rfl⟩
  -- The parameters at which the loop is at an end of a piece.
  have hTfin : {t : ℝ | t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q}.Finite := by
    refine Set.Finite.of_finite_image (f := f) ((finite_endSet Q).subset ?_)
      (hf.injOn.mono fun t ht => ht.1)
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  obtain ⟨n, hcard⟩ : ∃ n, hTfin.toFinset.card = n := ⟨_, rfl⟩
  set TF : Finset ℝ := hTfin.toFinset with hTFdef
  have hmemTF : ∀ t : ℝ, t ∈ TF ↔ (t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q) := by
    intro t; rw [hTFdef, Set.Finite.mem_toFinset]; exact Iff.rfl
  have hTle : ∀ s ∈ TF, s ∈ Ico (0 : ℝ) 1 := fun s hs => ((hmemTF s).1 hs).1
  have h0TF : (0 : ℝ) ∈ TF := (hmemTF 0).2 ⟨⟨le_refl 0, by norm_num⟩, hV₀⟩
  set tp : Fin n → ℝ := par TF hcard with htp
  set nx : Fin n → ℝ := parNext TF hcard with hnx
  -- Both ends of every gap are ends of pieces.
  have htpV : ∀ i : Fin n, f (tp i) ∈ endSet Q := fun i =>
    ((hmemTF _).1 (par_mem hcard i)).2
  have hnxV : ∀ i : Fin n, f (nx i) ∈ endSet Q := by
    intro i
    rw [hnx, parNext]
    split_ifs with hi
    · exact ((hmemTF _).1 (Finset.orderEmbOfFin_mem _ _ _)).2
    · rw [← hf.closes]; exact hV₀
  have hlt : ∀ i : Fin n, tp i < nx i := fun i => par_lt_parNext hcard hTle i
  have hIcc : ∀ i : Fin n, Icc (tp i) (nx i) ⊆ I := fun i => gapClosure_subset_I hcard hTle i
  have hIoo : ∀ i : Fin n, Ioo (tp i) (nx i) ⊆ Ico (0 : ℝ) 1 := fun i =>
    gap_subset_Ico hcard hTle i
  set G : Fin n → Set Plane := fun i => f '' Ioo (tp i) (nx i) with hG
  set Z : Fin n → Set Plane := fun i => f '' Icc (tp i) (nx i) with hZ
  have hGne : ∀ i, (G i).Nonempty := fun i =>
    ((Set.nonempty_Ioo.2 (hlt i)).image f)
  have hGconn : ∀ i, IsPreconnected (G i) := fun i =>
    isPreconnected_Ioo.image f (hf.continuousOn.mono (fun s hs => hIcc i (Ioo_subset_Icc_self hs)))
  have hGdiff : ∀ i, G i ⊆ C \ endSet Q := by
    rintro i z ⟨s, hs, rfl⟩
    refine ⟨hmemC s (hIcc i (Ioo_subset_Icc_self hs)), fun hzV => ?_⟩
    exact notMem_of_mem_gap hcard hs ((hmemTF s).2 ⟨hIoo i hs, hzV⟩)
  have hZcompact : ∀ i, IsCompact (Z i) := fun i =>
    isCompact_image_of_subset_I hf.continuousOn (hIcc i) isClosed_Icc
  have hZeq : ∀ i, Z i = G i ∪ {f (tp i), f (nx i)} := by
    intro i
    simp only [hZ, hG]
    rw [Icc_eq_Ioo_union_ends (hlt i).le, Set.image_union, Set.image_pair]
  have hZdiff : ∀ i, Z i ∩ (C \ endSet Q) = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨(hZeq i) ▸ Or.inl hz, hGdiff i hz⟩)
    rintro z ⟨hzZ, hzC, hzV⟩
    rcases (hZeq i) ▸ hzZ with hz | hz
    · exact hz
    · rcases hz with rfl | rfl
      exacts [absurd (htpV i) hzV, absurd (hnxV i) hzV]
  have hGdisj : ∀ i j : Fin n, i ≠ j → G i ∩ G j = ∅ := by
    intro i j hij
    refine Set.eq_empty_of_forall_notMem ?_
    rintro z ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
    have := hf.injOn (hIoo j ht) (hIoo i hs) hts
    exact Set.disjoint_left.1 (gap_disjoint hcard hij) hs (this ▸ ht)
  -- The gaps cover the curve away from the ends of the pieces.
  have hcov : (⋃ i, G i) = C \ endSet Q := by
    refine Set.Subset.antisymm (Set.iUnion_subset hGdiff) (fun z hz => ?_)
    obtain ⟨s, hs, rfl⟩ := hsurj z hz.1
    obtain ⟨i, hi⟩ := exists_mem_gap hcard hTle h0TF hs
      (fun hsT => hz.2 ((hmemTF s).1 hsT).2)
    exact Set.mem_iUnion.2 ⟨i, ⟨s, hi, rfl⟩⟩
  -- Each gap image lies in one piece interior.
  have hchoose : ∀ i, ∃ R ∈ Q, G i ⊆ R.interior := fun i =>
    hQ.preconnected_subset_interior (hGconn i) (hGne i) (hGdiff i)
  choose pc hpcQ hpcsub using hchoose
  -- And is the whole of it: the interior is connected and covered by the closed gap images.
  have hpceq : ∀ i, (pc i).interior = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (hpcsub i)
    set W : Set Plane := ⋃ j ∈ ({i}ᶜ : Set (Fin n)), Z j with hW
    have hWclosed : IsClosed W :=
      Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ => (hZcompact j).isClosed
    have hAdiff : (pc i).interior ⊆ C \ endSet Q := by
      rw [hQ.diff_endSet_eq]
      exact fun z hz => Set.mem_iUnion₂.2 ⟨pc i, hpcQ i, hz⟩
    have hAZ : (pc i).interior ⊆ Z i ∪ W := by
      intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hAdiff hz)
      by_cases hji : j = i
      · exact Or.inl ((hZeq i) ▸ Or.inl (hji ▸ hj))
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, (hZeq j) ▸ Or.inl hj⟩)
    have hGW : ∀ z ∈ G i, z ∉ W := by
      intro z hz hzW
      obtain ⟨j, hji, hzj⟩ := Set.mem_iUnion₂.1 hzW
      have : z ∈ G j := (hZdiff j) ▸ ⟨hzj, hGdiff i hz⟩
      exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j (Ne.symm hji)) z ⟨hz, this⟩
    have hcover2 : (pc i).interior ⊆ Wᶜ ∪ (Z i)ᶜ := by
      intro z hz
      by_cases hzW : z ∈ W
      · refine Or.inr fun hzZ => ?_
        exact hGW z ((hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩) hzW
      · exact Or.inl hzW
    have hnone : ¬ ((pc i).interior ∩ (Wᶜ ∩ (Z i)ᶜ)).Nonempty := by
      rintro ⟨z, hz, hzW, hzZ⟩
      rcases hAZ hz with h | h
      exacts [hzZ h, hzW h]
    have hconv : IsPreconnected ((pc i).interior) :=
      (convex_openSegment _ _).isPreconnected
    obtain ⟨z₀, hz₀⟩ := hGne i
    have hAu : ((pc i).interior ∩ Wᶜ).Nonempty := ⟨z₀, hpcsub i hz₀, hGW z₀ hz₀⟩
    have hnotv : ¬ ((pc i).interior ∩ (Z i)ᶜ).Nonempty := fun hv =>
      hnone (hconv _ _ hWclosed.isOpen_compl (hZcompact i).isClosed.isOpen_compl hcover2 hAu hv)
    intro z hz
    have hzZ : z ∈ Z i := by
      by_contra hzZ
      exact hnotv ⟨z, hz, hzZ⟩
    exact (hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩
  -- The correspondence between gaps and pieces is a bijection.
  have hpcinj : Function.Injective pc := by
    intro i j hij
    by_contra hne'
    obtain ⟨z, hz⟩ := hGne i
    have hzj : z ∈ G j := by rw [← hpceq j, ← hij, hpceq i]; exact hz
    exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j hne') z ⟨hz, hzj⟩
  have hpcsurj : ∀ R ∈ Q, ∃ i, pc i = R := by
    intro R hR
    have hx : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ R.interior :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hxd : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ C \ endSet Q := by
      rw [hQ.diff_endSet_eq]; exact Set.mem_iUnion₂.2 ⟨R, hR, hx⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hxd)
    refine ⟨i, ?_⟩
    by_contra hne'
    exact hQ.interiors (pc i) (hpcQ i) R hR hne' _ (hpceq i ▸ hi) hx
  -- The ends of the piece are the two ends of the gap.
  have hends : ∀ i, ((pc i).1 = f (tp i) ∧ (pc i).2 = f (nx i)) ∨
      ((pc i).1 = f (nx i) ∧ (pc i).2 = f (tp i)) := by
    intro i
    have hnd : (pc i).1 ≠ (pc i).2 := hQ.nondeg _ (hpcQ i)
    have hclosure : (pc i).seg ⊆ Z i := by
      have hcl : closure ((pc i).interior) ⊆ Z i := by
        rw [hpceq i]
        exact closure_minimal (fun z hz => (hZeq i) ▸ Or.inl hz) (hZcompact i).isClosed
      rwa [Piece.interior, closure_openSegment] at hcl
    have hmem : ∀ z, z = (pc i).1 ∨ z = (pc i).2 → z = f (tp i) ∨ z = f (nx i) := by
      intro z hz
      have hzseg : z ∈ (pc i).seg := by
        rcases hz with rfl | rfl
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      rcases (hZeq i) ▸ hclosure hzseg with hzG | hzE
      · exfalso
        rw [← hpceq i] at hzG
        rcases hz with rfl | rfl
        exacts [hnd (left_mem_openSegment_iff.1 hzG), hnd (right_mem_openSegment_iff.1 hzG)]
      · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzE
    exact pair_eq_of_mem_pair hnd (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl))
  have hpcseg : ∀ i, (pc i).seg = segment ℝ (f (tp i)) (f (nx i)) := by
    intro i
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Piece.seg, h1, h2]
    · rw [Piece.seg, h1, h2, segment_symm]
  have hfne : ∀ i, f (tp i) ≠ f (nx i) := by
    intro i he
    refine hQ.nondeg _ (hpcQ i) ?_
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact he
    · rw [h1, h2]; exact he.symm
  -- There are at least three parameters.
  have hn0 : 0 < n := par_card_pos hcard h0TF
  have htp0 : tp ⟨0, hn0⟩ = 0 := par_zero hcard hTle h0TF
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt2 | hge
    · exfalso
      have hcond : ¬ ((⟨0, hn0⟩ : Fin n) : ℕ) + 1 < n :=
        fun hc => absurd (lt_of_le_of_lt (Nat.le_add_left 1 _) hc) (by omega)
      have hnx0 : nx ⟨0, hn0⟩ = 1 := by rw [hnx, parNext, dif_neg hcond]
      exact hfne ⟨0, hn0⟩ (by rw [htp0, hnx0]; exact hf.closes)
    · exact hge
  haveI : NeZero n := ⟨by omega⟩
  -- The cyclic vertex list: the ends, in the order the loop reaches them.
  set w : ZMod n → Plane := fun j => f (tp ⟨j.val, ZMod.val_lt j⟩) with hw
  have hwsucc : ∀ j : ZMod n, w (j + 1) = f (nx ⟨j.val, ZMod.val_lt j⟩) := by
    intro j
    have hjlt := ZMod.val_lt j
    by_cases hj : j.val + 1 < n
    · have hval : (j + 1).val = j.val + 1 := by rw [zmod_val_succ (by omega) j, if_pos hj]
      have hfin : (⟨(j + 1).val, ZMod.val_lt (j + 1)⟩ : Fin n) = ⟨j.val + 1, hj⟩ :=
        Fin.val_injective hval
      simp only [hw, hfin]
      rw [hnx, parNext, dif_pos (show (⟨j.val, hjlt⟩ : Fin n).val + 1 < n from hj)]
      rfl
    · have hval : (j + 1).val = 0 := by rw [zmod_val_succ (by omega) j, if_neg hj]
      have hfin : (⟨(j + 1).val, ZMod.val_lt (j + 1)⟩ : Fin n) = ⟨0, hn0⟩ :=
        Fin.val_injective hval
      simp only [hw, hfin]
      rw [htp0, hnx, parNext, dif_neg (show ¬ ((⟨j.val, hjlt⟩ : Fin n).val + 1 < n) from hj)]
      exact hf.closes
  have hedgeq : ∀ j : ZMod n,
      segment ℝ (w j) (w (j + 1)) = (pc ⟨j.val, ZMod.val_lt j⟩).seg := by
    intro j
    rw [hwsucc j, hpcseg]
  have hwinj : Function.Injective w := by
    intro j k hjk
    simp only [hw] at hjk
    have h1 := hf.injOn (hTle _ (par_mem hcard ⟨j.val, ZMod.val_lt j⟩))
      (hTle _ (par_mem hcard ⟨k.val, ZMod.val_lt k⟩)) hjk
    exact ZMod.val_injective _ (congrArg Fin.val ((TF.orderEmbOfFin hcard).injective h1))
  have hwmeet : ∀ i j : ZMod n, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)} := by
    intro i j hij
    rw [hedgeq i, hedgeq j]
    have hne' : pc ⟨i.val, ZMod.val_lt i⟩ ≠ pc ⟨j.val, ZMod.val_lt j⟩ := fun he =>
      hij (ZMod.val_injective _ (congrArg Fin.val (hpcinj he)))
    refine le_trans (hQ.seg_inter_subset (hpcQ _) (hpcQ _) hne') ?_
    have hwi : w i = f (tp ⟨i.val, ZMod.val_lt i⟩) := rfl
    rcases hends ⟨i.val, ZMod.val_lt i⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, ← hwi, ← hwsucc i]
    · rw [h1, h2, ← hwi, ← hwsucc i, Set.pair_comm]
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with hlt3 | hge
    · exfalso
      have hn2' : n = 2 := by omega
      have hone : (1 : ZMod n).val = 1 := by
        rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num]
        exact ZMod.val_cast_of_lt (by omega)
      have h01 : (0 : ZMod n) ≠ 1 := by
        intro he
        have hv : (0 : ZMod n).val = (1 : ZMod n).val := by rw [he]
        rw [ZMod.val_zero, hone] at hv
        omega
      have hsucc1 : (1 : ZMod n) + 1 = 0 := by
        refine ZMod.val_injective _ ?_
        rw [zmod_val_succ (by omega) 1, hone, if_neg (by omega), ZMod.val_zero]
      have hw01 : w 0 ≠ w 1 := fun he => h01 (hwinj he)
      obtain ⟨p, hp, hp1, hp2⟩ := PrePolygon.exists_mem_segment_ne hw01
      have hmem := hwmeet 0 1 h01
        ⟨by rw [zero_add]; exact hp, by rw [hsucc1, segment_symm]; exact hp⟩
      rw [zero_add] at hmem
      rcases hmem with h | h
      exacts [hp1 h, hp2 h]
    · exact hge
  -- Assemble.
  refine (PrePolygon.exists_prePolygon hn3 w hwinj hwmeet).imp fun m hm => hm.imp fun P hP => ?_
  rw [hP, ← hQ.cover_eq]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) ?_
  · rw [hedgeq j]
    exact fun z hz => mem_cover (hpcQ _) hz
  · rw [cover]
    refine Set.iUnion₂_subset fun R hR => ?_
    obtain ⟨i, rfl⟩ := hpcsurj R hR
    have hfin : (⟨((i.val : ℕ) : ZMod n).val, ZMod.val_lt _⟩ : Fin n) = i :=
      Fin.val_injective (ZMod.val_cast_of_lt i.isLt)
    refine le_trans (le_of_eq ?_)
      (Set.subset_iUnion (fun j : ZMod n => segment ℝ (w j) (w (j + 1))) ((i.val : ℕ) : ZMod n))
    rw [hedgeq, hfin]

/-! ## The realization theorem -/

/-- **Every simple closed polygonal curve is the carrier of a `ClosedPolygon`.** This is the
blueprint's set-level notion — `IsJordanCurve` together with `IsPolygonal`, no condition on
vertices — matched with the presentation the development works with. -/
theorem exists_closedPolygon {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C) :
    ∃ (m : ℕ) (P : ClosedPolygon m), P.carrier = C := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar'⟩ := PrePolygon.exists_closedPolygon_of_prePolygon m P
  exact ⟨m', P', by rw [hcar', hcar]⟩

/-! ## Corners

A realization cannot put a vertex wherever it likes: `corner` forbids a vertex at which the
curve runs straight through. The points that *must* be vertices are exactly the ones at which
it does not, and this is what a consumer needing a named point to be a vertex has to check. -/

/-! ## The two arcs of a splitting

`ClosedPolygon.arc a k` and `ClosedPolygon.arc (a + k) (m + 3 - k)` are what a consumer tracking
a decomposition of the curve has to be handed. This section says what they are: two arcs between
the two cut vertices, covering the curve and meeting exactly there. -/

/-! ## The two-arc decomposition is unique

Two points cut a Jordan curve into two arcs, and *only* into those two: the interior of any arc
of the curve between them is connected and misses both, so it lies on one side of any other such
splitting. Without this a realization could name two arcs and still not be known to name the two
arcs a consumer started from. -/

/-- The interior of an arc — the arc less its two endpoints — is connected and nonempty. The
paired form the uniqueness argument below destructures; both halves are in
`Schoenflies/Subarc.lean`, which is where the shared set identity `A ∖ {p, q} = f '' Ioo 0 1`
lives. -/
theorem IsArcBetween.preconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) ∧ (A \ {p, q}).Nonempty :=
  ⟨h.isPreconnected_diff, h.nonempty_diff⟩

/-- **The two arcs a pair of points cuts a curve into are determined.** -/
theorem two_arcs_unique {C A₁ A₂ D₁ D₂ : Set Plane} {p q : Plane}
    (hA : A₁ ∪ A₂ = C) (hAi : A₁ ∩ A₂ = {p, q})
    (hD : D₁ ∪ D₂ = C) (hDi : D₁ ∩ D₂ = {p, q})
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hD1 : IsArcBetween D₁ p q) (hD2 : IsArcBetween D₂ p q) :
    (A₁ = D₁ ∧ A₂ = D₂) ∨ (A₁ = D₂ ∧ A₂ = D₁) := by
  have hpA : p ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inl rfl
  have hqA : q ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inr rfl
  have hpD : p ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inl rfl
  have hqD : q ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inr rfl
  -- An arc between the two points lies on one side of the other splitting.
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ D₁ ∨ A ⊆ D₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ D₁ᶜ ∪ D₂ᶜ := by
      intro z hz
      by_cases h1 : z ∈ D₁
      · by_cases h2 : z ∈ D₂
        · exact absurd (show z ∈ ({p, q} : Set Plane) by rw [← hDi]; exact ⟨h1, h2⟩) hz.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (D₁ᶜ ∩ D₂ᶜ)).Nonempty := by
      rintro ⟨z, hz, h1, h2⟩
      have hzC : z ∈ C := hAC hz.1
      rw [← hD] at hzC
      exact hzC.elim h1 h2
    -- Whichever side the interior meets, it stays there; the two endpoints are on both.
    have hends : ∀ D : Set Plane, p ∈ D → q ∈ D → A \ {p, q} ⊆ D → A ⊆ D := by
      intro D hpD' hqD' hsub' z hz
      by_cases hzpq : z ∈ ({p, q} : Set Plane)
      · rcases hzpq with rfl | rfl
        exacts [hpD', hqD']
      · exact hsub' ⟨hz, hzpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ D₁ᶜ).Nonempty
    · refine Or.inr (hends D₂ hpD.2 hqD.2 fun z hz => ?_)
      by_contra hzD2
      exact hnone (hconn _ _ (hD1.isArc.isClosed).isOpen_compl (hD2.isArc.isClosed).isOpen_compl
        hsub hcase ⟨z, hz, hzD2⟩)
    · refine Or.inl (hends D₁ hpD.1 hqD.1 fun z hz => ?_)
      by_contra hzD1
      exact hcase ⟨z, hz, hzD1⟩
  -- Both arcs cannot land on the same side: the other side would be just the two points.
  have hthird : ∀ D : Set Plane, IsArcBetween D p q → ¬ D ⊆ ({p, q} : Set Plane) := by
    intro D hDar hsub
    obtain ⟨-, z, hz⟩ := hDar.preconnected_diff
    exact hz.2 (hsub hz.1)
  have hnotboth : ∀ D D' : Set Plane, D ∪ D' = C → D ∩ D' = {p, q} → IsArcBetween D' p q →
      A₁ ⊆ D → A₂ ⊆ D → False := by
    intro D D' hDD hDDi hD'ar h1 h2
    refine hthird D' hD'ar ?_
    rw [← hDDi]
    intro z hz
    have hzC : z ∈ C := by rw [← hDD]; exact Or.inr hz
    rw [← hA] at hzC
    exact hzC.elim (fun h => ⟨h1 h, hz⟩) fun h => ⟨h2 h, hz⟩
  -- On opposite sides, the inclusions are equalities.
  have heq : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∪ Y' = C → X' ∩ Y' = {p, q} →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y' hX'Y'i hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun z hz => ?_
    have hzC : z ∈ C := by rw [← hX'Y']; exact Or.inl hz
    rw [← hXY] at hzC
    rcases hzC with h | h
    · exact h
    · have hzpq : z ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hz, hYY h⟩
      rcases hzpq with rfl | rfl
      exacts [hpX, hqX]
  have hAC₁ : A₁ ⊆ C := by rw [← hA]; exact Set.subset_union_left
  have hAC₂ : A₂ ⊆ C := by rw [← hA]; exact Set.subset_union_right
  rcases key A₁ hA1 hAC₁ with h1 | h1 <;> rcases key A₂ hA2 hAC₂ with h2 | h2
  · exact absurd (hnotboth D₁ D₂ hD hDi hD2 h1 h2) (by simp)
  · exact Or.inl ⟨heq A₁ A₂ D₁ D₂ hA hD hDi hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₂ D₁ (by rw [Set.union_comm]; exact hA) (by rw [Set.union_comm]; exact hD)
        (by rw [Set.inter_comm]; exact hDi) hpA.2 hqA.2 h2 h1⟩
  · exact Or.inr ⟨heq A₁ A₂ D₂ D₁ hA (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₁ D₂ (by rw [Set.union_comm]; exact hA) hD hDi hpA.2 hqA.2 h2 h1⟩
  · exact absurd (hnotboth D₂ D₁ (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hD1 h1 h2) (by simp)

end Schoenflies
end

section
-- module Solutions.Q146_CD.FaceCyclesProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Face cycles: the proof

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as its
boundary and is one of the two complementary regions of that cycle*. `Schoenflies/FaceCycles.lean`
built the base cycle, its 2-connectivity, and the topology of adding an ear; this module runs
the induction of the blueprint's proof on top of them.

## READ THIS FIRST: what is assumed

`Graph.face_cycles` **carries a hypothesis, `Schoenflies.CrosscutSplitsRegion`, which nothing
proves.** It is the exhaustion clause of `thm:polygonal-crosscut` — "the crosscut replaces `F`
by exactly two regions" — stated for a crosscut whose two endpoints are *arbitrary points of
the curve*. Everything else in the blueprint's proof is discharged here without hypotheses, and
each of those pieces is a standalone theorem below.

`main`'s Theorem 2.8 does **not** discharge it, and the obstruction is not a missing bridge.
`Schoenflies.IsPolygonalCrosscut` states its two splitting hypotheses against
`ClosedPolygon.arcPieces C a k`, which cuts the polygon's edge list at two of *its vertices*;
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says every vertex of every realization of a
curve is a corner of it. In the induction below the two cut points are the ear's endpoints —
graph vertices at which the two cycle edges may leave along opposite rays, so that the boundary
curve runs *straight* through the cut point. Such a point is a vertex of no `ClosedPolygon`
with that carrier, and `Schoenflies.exists_closedPolygon_split` (whose `IsCornerAt` hypotheses
are therefore not an artefact) cannot be applied.

There is a **second, independent** reason, and it bites even when both cut points *are*
corners. `IsPolygonalCrosscut.edges₁` asks for `SameEdges J₁.pieces (C.arcPieces a k ++ K)`,
a multiset equality of unoriented segments. The list on the right has two pieces ending at the
cut point `q` — the arc's last and the crosscut's first. If those two are collinear, the curve
`J₁ = A₁ ∪ P` runs straight through `q`, so `q` is a vertex of no `ClosedPolygon` with that
carrier and *no* piece of `J₁.pieces` ends there: the multiset equality is unsatisfiable. Since
the crosscut may perfectly well leave a cut vertex along the ray opposite the arriving arc edge,
`edges₁` and `edges₂` are not dischargeable as stated. Deleting the redundant vertex —
`Schoenflies.PrePolygon.deleteLast` — repairs the *realization* and breaks `SameEdges` in the
same move.

Closing the gap therefore means restating Theorem 2.8 with the edge lists related by *parity*
rather than by `SameEdges`, for a split made at arbitrary points of the curve. The tools exist:
`Schoenflies.parity_split` is already stated for arbitrary lists, and
`Schoenflies.parity_subdivide` (Lemma 2.1) absorbs the difference between a merged piece and its
two halves. What is missing is the parity theory of presentations carrying redundant vertices —
`Schoenflies.parity_eq_one_iff` for `Schoenflies.PrePolygon` rather than only for
`ClosedPolygon`, obtained by carrying the parity along the normalization induction of
`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`. That is a separate module.

## Main results

* **The realisation of a cycle is a separating curve** (`Graph.IsDrawing.cycle_isSeparating`),
  which is what the base case needed and what `main` could not say. It composes
  `Graph.IsDrawing.cycle_isJordanCurve` with `Schoenflies.exists_closedPolygon` and
  `Schoenflies.ClosedPolygon.isSeparating_carrier`. The polygonality half needed a bridge that
  `main` did not have: `Schoenflies.IsPolygonal` is the carrier of *one* vertex list, so a union
  of edge arcs is polygonal only once each arc is known to be a polyline running from one of its
  ends to the other (`Schoenflies.IsArcBetween.exists_poly_eq`, which rests on the arc
  uniqueness `Schoenflies.IsArcBetween.eq_of_subset`).
* **The base case** (`Graph.IsDrawing.hasFaceCycles_cycleGraph`): the cycle subgraph occupies
  exactly the cycle's realisation, so its faces are the two regions of that curve.
* **Cutting a cycle at two of its vertices** (`Graph.IsCycleThrough.split_at`) and **splicing an
  ear onto an arc** (`Graph.exists_spliced_cycle`) — the combinatorics of "both bounded by
  cycles" — together with the geometric reading of the split
  (`Graph.IsDrawing.arcs_of_split`).
* **The step's topology**: the enlarged exterior is the old one minus the ear
  (`Graph.IsDrawing.pointSet_pathGraphOf`), a face the ear misses survives with its cycle
  (`Graph.IsFaceCycle.mono`), and the face the ear cuts is cut only inside itself
  (`Schoenflies.connectedComponentIn_diff`).

## For the integrator

`Graph.IsPath.append`, `Graph.IsPath.split_meet`, `Graph.IsWalk.walkVertices_eq_covered`,
`Graph.IsWalk.walkVertices_reverse_eq`, `Graph.coveredVertices_congr_of_le`,
`Graph.walkVertices_congr_of_le` and `Graph.edgesCover_append` / `…_perm` / `…_reverse` are
general and belong in `Schoenflies/Graph/Walk.lean` and `Schoenflies/Graph/CycleJordan.lean`.
`Schoenflies.IsArcBetween.eq_of_subset` belongs in `Schoenflies/Subarc.lean` and
`Schoenflies.poly_append_join` in `Schoenflies/PolyPath.lean`.

## Blueprint

* `Schoenflies.IsArcBetween.eq_of_subset`, `Schoenflies.IsArcBetween.exists_poly_eq`,
  `Graph.IsDrawing.exists_poly_eq_edgesCover`, `Graph.IsDrawing.isPolygonal_edgesCover` — §1,
  the polygonality of what a walk draws.
* `Graph.IsDrawing.cycle_isSeparating` — `thm:polygonal-jordan` for the realisation of a cycle:
  "This is true for the initial cycle by Theorem `thm:polygonal-jordan`."
* `Graph.IsFaceCycle`, `Graph.HasFaceCycles` — the conclusion of `lem:face-cycles`, at one face
  and at all of them.
* `Graph.IsDrawing.hasFaceCycles_cycleGraph` — the base case.
* `Graph.IsCycleThrough.split_at`, `Graph.IsDrawing.arcs_of_split`,
  `Graph.exists_spliced_cycle` — "Theorem `thm:polygonal-crosscut` replaces `F` by exactly two
  regions, both bounded by cycles", combinatorially.
* `Schoenflies.CrosscutSplitsRegion` — **the assumed** exhaustion clause of
  `thm:polygonal-crosscut` at arbitrary cut points.
* `Graph.IsDrawing.hasFaceCycles_union` — one ear.
* `Graph.face_cycles` — `lem:face-cycles`, modulo `Schoenflies.CrosscutSplitsRegion`.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## An arc inside an arc with the same ends is the whole of it -/

/-! ## Concatenating polylines -/

/-! ## A component survives the removal of a set

The face of the enlarged graph through a point of an old face is a component of *that old
face* with the ear removed — not merely of the whole old exterior with the ear removed. No
topology is needed: a component of the small set is preconnected inside the big one, and back
again. -/

/-- **Cutting inside one component.** The component of `z` in `S ∖ P` sees only the component
of `z` in `S`. -/
theorem connectedComponentIn_diff (S P : Set Plane) (z : Plane) :
    connectedComponentIn (S \ P) z = connectedComponentIn (connectedComponentIn S z \ P) z := by
  by_cases hz : z ∈ S \ P
  · have hcomp : connectedComponentIn (S \ P) z ⊆ connectedComponentIn S z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) ((connectedComponentIn_subset _ _).trans Set.sdiff_subset)
    have hzR : z ∈ connectedComponentIn (connectedComponentIn S z \ P) z :=
      mem_connectedComponentIn ⟨mem_connectedComponentIn hz.1, hz.2⟩
    refine Set.Subset.antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) fun w hw =>
          ⟨hcomp hw, (connectedComponentIn_subset _ _ hw).2⟩)
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn hzR fun w hw => ?_)
    have hw' : w ∈ connectedComponentIn S z \ P := connectedComponentIn_subset _ _ hw
    exact ⟨connectedComponentIn_subset _ _ hw'.1, hw'.2⟩
  · rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty]
    rintro ⟨hw, hwP⟩
    exact hz ⟨connectedComponentIn_subset _ _ hw, hwP⟩

/-! ## A polygonal arc is a polyline running from one end to the other -/

end Schoenflies

namespace Graph

/-! ## Cutting and joining paths

Two general facts about paths that `Schoenflies/Graph/Walk.lean` does not have, and that the
splitting of a cycle at two of its vertices runs on. **The integrator should hoist both into
`Schoenflies/Graph/Walk.lean`**, next to `Graph.IsPath.split`, which is the weaker form of the
second. -/

section GeneralWalk

variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e : β} {W W₁ W₂ : List β}

/-- **Two paths meeting only at the junction concatenate.** The freshness clause of the joined
path is the freshness of the first together with the meeting condition: a vertex the second
half visits and the first half departs from would be the junction, which the first half has
already arrived at. -/
theorem IsPath.append : ∀ {u w v : α} {W₁ W₂ : List β}, G.IsPath u W₁ w → G.IsPath w W₂ v →
    (∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices w W₂ → y = w) → G.IsPath u (W₁ ++ W₂) v := by
  intro u w v W₁ W₂ h₁
  induction h₁ with
  | nil hx => intro h₂ _; simpa using h₂
  | @cons u w₀ w e W hl hW hfresh ih =>
    intro h₂ hmeet
    refine List.cons_append .. ▸ IsPath.cons hl
      (ih h₂ fun y hy hy₂ => hmeet y (mem_walkVertices_cons_of_mem hl hy) hy₂) fun hmem => ?_
    -- The departure vertex is fresh: the only new vertices are those of the second half, and
    -- one of those shared with the first half would be the junction, already visited.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | hcov
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · have := hmeet u mem_walkVertices_self (mem_walkVertices_of_mem_covered hcov)
      exact hfresh (this ▸ hW.target_mem_walkVertices)

/-- **A path splits at any vertex it visits, and the two halves meet only there.** This is
`Graph.IsPath.split` with the meeting condition in place of its weaker last clause. -/
theorem IsPath.split_meet (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      ∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices x W₂ → y = x := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', fun y hy _ => by simpa using hy⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh,
        fun y hy _ => by simpa using hy⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, hmeet⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem => hfresh (walkVertices_mono hsub₁ hmem),
      h₂, fun y hy hy₂ => ?_⟩
    -- A vertex of the extended prefix is either the new source — which the far half never
    -- visits, by freshness — or one the induction hypothesis already handles.
    rcases mem_walkVertices_cons hl hy with rfl | hy'
    · exfalso
      rcases mem_walkVertices_iff.1 hy₂ with rfl | hcov
      · exact hfresh (walkVertices_mono hsub₁ h₁.target_mem_walkVertices)
      · exact hfresh (mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov))
    · exact hmeet y hy' hy₂

/-! ### Cutting a cycle at two of its vertices

The cycle is `X ++ Y ++ Z` closed up by the edge `e`, cut at the two vertices `c` (between `X`
and `Y`) and `d` (between `Y` and `Z`). One arc is `Y`; the other runs `Z`, then the closing
edge, then `X`. Both cases of "which of the two named vertices comes first along the detour"
feed this one lemma. -/

/-- **The complementary arc of a cut cycle**, together with the two facts a geometric consumer
needs: that the two arcs between them use every edge of the cycle exactly once, and that they
visit no common vertex but the two cut points. -/
theorem IsCycleThrough.split_aux {G : Graph α β} {e : β} {u v c d : α} {D X Y Z : List β}
    (hc : G.IsCycleThrough e u v D) (hD : D = X ++ (Y ++ Z)) (hX : G.IsPath u X c)
    (hY : G.IsPath c Y d) (hZ : G.IsPath d Z v) (hcd : c ≠ d)
    (hM1 : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices c (Y ++ Z) → y = c)
    (hM2 : ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d Z → y = d) :
    G.IsPath d (Z ++ e :: X) c ∧ (Y ++ (Z ++ e :: X)).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d (Z ++ e :: X) → y = c ∨ y = d := by
  have hZsub : G.walkVertices d Z ⊆ G.walkVertices c (Y ++ Z) := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
    · exact walkVertices_mono (List.subset_append_left _ _) hY.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono
        (List.subset_append_right _ _) hcov)
  -- A vertex of the first stretch that the last stretch also reaches would merge the two cuts.
  have hclash : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices d Z → False := by
    intro y hy hyZ
    obtain rfl : y = c := hM1 y hy (hZsub hyZ)
    exact hcd (hM2 y mem_walkVertices_self hyZ)
  have hvZ : v ∈ G.walkVertices d Z := hZ.target_mem_walkVertices
  have hvX : v ∉ G.walkVertices u X := fun hh => hclash v hh hvZ
  -- The closing edge, then the first stretch, is a path from the far end back to the first cut.
  have hePath : G.IsPath v (e :: X) c := IsPath.cons hc.isLink.symm hX hvX
  -- Its vertices, other than `v` itself, are those of the first stretch.
  have hcons : ∀ y ∈ G.walkVertices v (e :: X), y = v ∨ y ∈ G.walkVertices u X := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | ⟨g, hg, hinc⟩
    · exact Or.inl rfl
    rcases List.mem_cons.1 hg with rfl | hg'
    · rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
      · exact Or.inr mem_walkVertices_self
      · exact Or.inl rfl
    · exact Or.inr (mem_walkVertices_of_mem_covered ⟨g, hg', hinc⟩)
  refine ⟨hZ.append hePath fun y hy hy' => ?_, ?_, fun y hy hy' => ?_⟩
  · rcases hcons y hy' with rfl | hyX
    · rfl
    · exact absurd hyX fun hh => hclash y hh hy
  · subst hD
    rw [show Y ++ (Z ++ e :: X) = (Y ++ Z) ++ (e :: X) by rw [List.append_assoc]]
    exact List.perm_middle.trans (List.Perm.cons _ List.perm_append_comm)
  · -- A vertex on both arcs is on the last stretch — hence the second cut — or on the first,
    -- hence the first cut.
    rcases mem_walkVertices_iff.1 hy' with rfl | hcov
    · exact Or.inr rfl
    rw [coveredVertices_append] at hcov
    rcases hcov with hcovZ | hcovE
    · exact Or.inr (hM2 y hy (mem_walkVertices_of_mem_covered hcovZ))
    · rcases hcons y (mem_walkVertices_of_mem_covered hcovE) with rfl | hyX
      · exact Or.inr (hM2 y hy hvZ)
      · exact Or.inl (hM1 y hyX (walkVertices_mono (List.subset_append_left _ _) hy))

/-- **A cycle cut at two of its vertices is two paths between them.** The two arcs use every
edge of the cycle exactly once — that is what the permutation says — and they have no vertex in
common but the two cut points. This is the combinatorial half of "the ear is a crosscut of the
face": the geometric half reads the two arcs of the Jordan curve off it. -/
theorem IsCycleThrough.split_at {G : Graph α β} {e : β} {u v a b : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (ha : a ∈ G.walkVertices u D) (hb : b ∈ G.walkVertices u D)
    (hab : a ≠ b) :
    ∃ D₁ D₂ : List β, G.IsPath a D₁ b ∧ G.IsPath b D₂ a ∧ (D₁ ++ D₂).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b := by
  obtain ⟨P, Q, hPQ, hP, hQ, hM1⟩ := hc.isPath.split_meet ha
  -- The second cut point lies on one of the two stretches the first one made.
  have hcases : b ∈ G.walkVertices a Q ∨ b ∈ G.walkVertices u P := by
    rw [hPQ] at hb
    rcases mem_walkVertices_iff.1 hb with rfl | hcov
    · exact Or.inr mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with h | h
    · exact Or.inr (mem_walkVertices_of_mem_covered h)
    · exact Or.inl (mem_walkVertices_of_mem_covered h)
  rcases hcases with hbQ | hbP
  · -- `b` comes after `a`: cut the far stretch at `b`.
    obtain ⟨Q₁, Q₂, hQ12, hQ1, hQ2, hM2⟩ := hQ.split_meet hbQ
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P) (Y := Q₁) (Z := Q₂)
      (by rw [hPQ, hQ12]) hP hQ1 hQ2 hab (by rw [← hQ12]; exact hM1) hM2
    exact ⟨Q₁, Q₂ ++ e :: P, hQ1, hpath, hperm, hmeet⟩
  · -- `b` comes before `a`: cut the near stretch at `b`, and the two roles are exchanged.
    obtain ⟨P₁, P₂, hP12, hP1, hP2, hM2⟩ := hP.split_meet hbP
    have hP1sub : G.walkVertices u P₁ ⊆ G.walkVertices u P :=
      walkVertices_mono (by rw [hP12]; exact List.subset_append_left _ _)
    have hP2sub : G.walkVertices b P₂ ⊆ G.walkVertices u P := by
      intro y hy
      rcases mem_walkVertices_iff.1 hy with rfl | hcov
      · exact hbP
      · exact mem_walkVertices_of_mem_covered
          (coveredVertices_mono (by rw [hP12]; exact List.subset_append_right _ _) hcov)
    have hM1' : ∀ y ∈ G.walkVertices u P₁, y ∈ G.walkVertices b (P₂ ++ Q) → y = b := by
      intro y hy hy'
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · rfl
      rw [coveredVertices_append] at hcov
      rcases hcov with h | h
      · exact hM2 y hy (mem_walkVertices_of_mem_covered h)
      · -- A vertex both stretches of the near half and the far half reach merges the two cuts.
        exfalso
        obtain rfl : y = a := hM1 y (hP1sub hy) (mem_walkVertices_of_mem_covered h)
        exact hab (hM2 y hy hP2.target_mem_walkVertices)
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P₁) (Y := P₂) (Z := Q)
      (by rw [hPQ, hP12, List.append_assoc]) hP1 hP2 hQ (Ne.symm hab) hM1'
      fun y hy hy' => hM1 y (hP2sub hy) hy'
    refine ⟨Q ++ e :: P₁, P₂, hpath, hP2, List.perm_append_comm.trans hperm, fun y hy hy' => ?_⟩
    exact (hmeet y hy' hy).symm

/-! ### Splicing an ear onto an arc

The blueprint's "the crosscut replaces `F` by exactly two regions, both bounded by cycles": the
two new cycles are the two arcs of the old one, each closed up by the ear. This is the
combinatorial construction of one of them. -/

/-- Incidence along edges of a subgraph is the same in the subgraph as in the graph, so the
vertices a walk visits do not depend on which of the two it is read in. -/
theorem coveredVertices_congr_of_le {H G : Graph α β} (hHG : H ≤ G) (hW : ∀ f ∈ W, f ∈ E(H)) :
    G.coveredVertices W = H.coveredVertices W := by
  ext x
  constructor
  · rintro ⟨g, hg, y, hy⟩
    exact ⟨g, hg, y, (hHG.isLink_iff (hW g hg)).2 hy⟩
  · rintro ⟨g, hg, y, hy⟩
    exact ⟨g, hg, y, hy.mono hHG⟩

theorem walkVertices_congr_of_le {H G : Graph α β} (hHG : H ≤ G) (hW : ∀ f ∈ W, f ∈ E(H)) :
    G.walkVertices u W = H.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_congr_of_le hHG hW]

/-- **The cycle an ear splices onto an arc of the old cycle.** The closed walk runs along the
arc and back along the ear; presented as `Graph.IsCycleThrough`, its named edge is the ear's
first, and its detour is the arc followed by the rest of the ear reversed. -/
theorem exists_spliced_cycle {B G : Graph α β} (hBG : B ≤ G) {a b : α} {D₁ D' : List β}
    (hD1 : B.IsPath a D₁ b) (hear : G.IsPath a D' b) (hab : a ≠ b)
    (hnew : ∀ g ∈ D', g ∉ E(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B)) :
    ∃ (f : β) (x y : α) (T : List β),
      (B.union (G.pathGraphOf a D')).IsCycleThrough f x y T ∧ (f :: T).Perm (D₁ ++ D') := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, D' = f :: T := by
    cases D' with
    | nil => exact absurd hear.isWalk.eq_of_nil hab
    | cons f T => exact ⟨f, T, rfl⟩
  obtain ⟨w, hl, hT, hfresh⟩ :
      ∃ w, G.IsLink f a w ∧ G.IsPath w T b ∧ a ∉ G.walkVertices w T := by
    cases hear with
    | cons hl hT hfr => exact ⟨_, hl, hT, hfr⟩
  set P := G.pathGraphOf a (f :: T) with hP
  have hPG : P ≤ G := pathGraphOf_le hear.isWalk
  have hcompat : B.Compatible P := Compatible.of_le_le hBG hPG
  have hPB : P ≤ B.union P := hcompat.right_le_union
  have hBB : B ≤ B.union P := left_le_union _ _
  have hedges : ∀ g ∈ T, g ∈ E(P) := fun g hg => by
    rw [pathGraphOf_edgeSet hear.isWalk]; exact List.mem_cons_of_mem _ hg
  -- The ear's tail, run backwards, is a path of the enlarged graph from the far end.
  have hTrev : (B.union P).IsPath b T.reverse w := by
    refine ((hT.reverse.anti hPG ?_ ?_).mono hPB)
    · rw [pathGraphOf_vertexSet]; exact hear.isWalk.target_mem_walkVertices
    · intro g hg; exact hedges g (List.mem_reverse.1 hg)
  have hD1' : (B.union P).IsPath a D₁ b := hD1.mono hBB
  have hTedges : ∀ g ∈ T.reverse, g ∈ E(P) := fun g hg => hedges g (List.mem_reverse.1 hg)
  have hcovP : ∀ W' : List β, (∀ g ∈ W', g ∈ E(P)) →
      (B.union P).coveredVertices W' = G.coveredVertices W' := by
    intro W' hW'
    rw [coveredVertices_congr_of_le hPB hW', ← coveredVertices_congr_of_le hPG hW']
  -- The arc and the ear's tail meet only at the ear's far end: a common vertex lies in the old
  -- subgraph, so the ear's freshness clause makes it one of the ear's two ends, and the source
  -- is not one the rest of the ear visits.
  have hmeet : ∀ y ∈ (B.union P).walkVertices a D₁, y ∈ (B.union P).walkVertices b T.reverse →
      y = b := by
    intro y hy hy'
    have hyB : y ∈ V(B) := by
      rw [walkVertices_congr_of_le hBB (fun g hg => hD1.edge_mem hg)] at hy
      exact hD1.isWalk.walkVertices_subset hy
    have hy'' : y = b ∨ y ∈ G.coveredVertices T := by
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · exact Or.inl rfl
      · rw [hcovP _ hTedges, coveredVertices_reverse] at hcov
        exact Or.inr hcov
    rcases hy'' with rfl | hcov
    · rfl
    have hyD : y ∈ G.walkVertices a (f :: T) :=
      mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hcov)
    by_contra hyb
    obtain rfl : y = a := by
      by_contra hya
      exact hint y hyD hya hyb hyB
    exact hfresh (mem_walkVertices_of_mem_covered hcov)
  refine ⟨f, a, w, D₁ ++ T.reverse, ⟨?_, hD1'.append hTrev hmeet, ?_⟩, ?_⟩
  · exact (pathGraphOf_isLink.2 ⟨List.mem_cons_self, hl, mem_walkVertices_self,
      mem_walkVertices_of_mem_covered ⟨f, List.mem_cons_self, hl.inc_right⟩⟩).mono hPB
  · -- The ear's first edge is on neither the arc — it is not an edge of the old subgraph at
    -- all — nor the rest of the ear, which is a path.
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · exact hnew f List.mem_cons_self (hD1.edge_mem h)
    · exact (List.nodup_cons.1 hear.nodup).1 (List.mem_reverse.1 h)
  · exact ((List.reverse_perm T).append_left D₁).cons f |>.trans List.perm_middle.symm

end GeneralWalk

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a walk of a polygonal plane graph draws -/

/-! ## The realisation of a cycle is a separating curve

This is the composition the base case of `lem:face-cycles` needs, and the one thing that was
missing from it: `Graph.IsDrawing.cycle_isJordanCurve` says the realisation is a Jordan curve
and `Graph.IsDrawing.isPolygonal_edgesCover` says it is polygonal, and
`Schoenflies.exists_closedPolygon` — the realization theorem — turns that pair into a
`Schoenflies.ClosedPolygon`, whose carrier `Schoenflies.ClosedPolygon.isSeparating_carrier`
knows to separate the plane. Nothing here inspects the polygon; it is used and discarded. -/

/-- Going round the cycle the other way: the edge, then the detour, is a closed walk at the
edge's far end. This is the walk whose edge list is `e :: D`, the list every statement about
the realisation of a cycle is phrased with. -/
theorem IsCycleThrough.isWalk_cons {α : Type*} {G : Graph α β} {e : β} {u v : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) : G.IsWalk v (e :: D) v :=
  IsWalk.cons hc.isLink.symm hc.isPath.isWalk

/-- **The realisation of a cycle of a polygonal plane graph is a separating Jordan curve.**
`Schoenflies.IsSeparating` is Definition 2.4: the complement has exactly two regions, one
bounded and one unbounded, each with the curve as its boundary. -/
theorem IsDrawing.cycle_isSeparating (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : IsSeparating (edgesCover drawing (e :: D)) := by
  obtain ⟨m, P, hP⟩ := exists_closedPolygon (h.cycle_isJordanCurve hc)
    (h.isPolygonal_edgesCover hpoly hc.isWalk_cons (List.cons_ne_nil _ _))
  exact hP ▸ P.isSeparating_carrier

/-! ## What a subgraph spanned by a walk occupies -/

/-- An end of an edge lies on that edge's arc. -/
theorem IsDrawing.inc_mem_edgeArc (h : IsDrawing G drawing) {x : Plane} (hinc : G.Inc e x) :
    x ∈ edgeArc drawing e := by
  obtain ⟨y, hy⟩ := hinc
  exact (h.edge_isArcBetween hy).left_mem

/-- **The subgraph spanned by a nonempty walk occupies exactly what the walk draws.** Its
vertices are ends of its edges, so they add nothing to the union of the edge arcs. -/
theorem IsDrawing.pointSet_pathGraphOf (h : IsDrawing G drawing) (hW : G.IsWalk u W v)
    (hne : W ≠ []) : pointSet (G.pathGraphOf u W) drawing = edgesCover drawing W := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, W = f :: T := by
    cases W with
    | nil => exact absurd rfl hne
    | cons f T => exact ⟨f, T, rfl⟩
  refine Set.Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · -- Every vertex the walk visits is an end of one of its edges.
    intro x hx
    rw [pathGraphOf_vertexSet] at hx
    rcases mem_walkVertices_iff.1 hx with rfl | ⟨g, hg, hinc⟩
    · cases hW with
      | cons hl _ => exact mem_edgesCover List.mem_cons_self (h.inc_mem_edgeArc hl.inc_left)
    · exact mem_edgesCover hg (h.inc_mem_edgeArc hinc)
  · refine Set.iUnion₂_subset fun g hg => ?_
    rw [pathGraphOf_edgeSet hW] at hg
    exact fun z hz => mem_edgesCover hg hz
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
    refine edgeArc_subset_pointSet ?_ hzg
    rw [pathGraphOf_edgeSet hW]
    exact hg

/-- **The cycle subgraph occupies exactly what the cycle draws.** -/
theorem IsDrawing.pointSet_cycleGraph (h : IsDrawing G drawing) {e : β} {u v : Plane}
    {D : List β} (hc : G.IsCycleThrough e u v D) :
    pointSet (G.cycleGraph u e D) drawing = edgesCover drawing (e :: D) := by
  have hround := h.pointSet_pathGraphOf hc.isWalk_round (by simp)
  rw [cycleGraph, hround]
  refine Set.Subset.antisymm (edgesCover_mono fun g hg => ?_) (edgesCover_mono fun g hg => ?_)
  · rcases List.mem_append.1 hg with hg' | hg'
    · exact List.mem_cons_of_mem _ hg'
    · obtain rfl : g = e := by simpa using hg'
      exact List.mem_cons_self
  · rcases List.mem_cons.1 hg with rfl | hg'
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ hg'

/-! ## The conclusion of `lem:face-cycles`, at one face -/

namespace IsFaceCycle

variable {e : β} {u v : Plane} {D : List β}

/-- **"has a cycle as its boundary"**: the frontier of the face is the realisation. -/
theorem frontier_eq (h : IsFaceCycle G drawing z e u v D) :
    frontier (face G drawing z) = edgesCover drawing (e :: D) :=
  h.isRegionOf.frontier_eq h.isSeparating

/-- A face bounded by a cycle of a subgraph is bounded by the same cycle of the whole graph,
*provided the face itself is unchanged* — which is the shape the induction step needs when it
carries a face past an ear that does not touch it. -/
theorem mono (h : IsFaceCycle B drawing z e u v D) (hBG : B ≤ G)
    (hface : face G drawing z = face B drawing z) : IsFaceCycle G drawing z e u v D where
  isCycle := ⟨h.isCycle.isLink.mono hBG, h.isCycle.isPath.mono hBG, h.isCycle.notMem⟩
  isSeparating := h.isSeparating
  isRegionOf := hface ▸ h.isRegionOf

end IsFaceCycle

/-! ## The base case: the faces of a single cycle

"This is true for the initial cycle by Theorem `thm:polygonal-jordan`." The cycle subgraph
occupies exactly the cycle's realisation, so its faces are literally the components of the
complement of that curve, and the curve is separating. -/

/-- **The base case of `lem:face-cycles`.** Both faces of the graph consisting of one cycle
are regions of that cycle. -/
theorem IsDrawing.hasFaceCycles_cycleGraph (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : HasFaceCycles (G.cycleGraph u e D) drawing := by
  have hsep : IsSeparating (edgesCover drawing (e :: D)) := h.cycle_isSeparating hpoly hc
  -- The same cycle, read inside the subgraph it spans.
  have hcyc : (G.cycleGraph u e D).IsCycleThrough e u v D :=
    ⟨hc.cycleGraph_isLink,
      hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg => by
        rw [hc.cycleGraph_edgeSet]; exact List.mem_append_left _ hg,
      hc.notMem⟩
  intro z hz
  refine ⟨e, u, v, D, hcyc, hsep, ?_⟩
  rw [face, exterior, h.pointSet_cycleGraph hc]
  refine hsep.isRegionOf_connectedComponentIn ?_
  rw [exterior, h.pointSet_cycleGraph hc] at hz
  exact hz

/-! ## The two arcs a cycle is cut into, as sets

The combinatorial split of `Graph.IsCycleThrough.split_at` becomes the geometric one: the two
arcs of the Jordan curve between the two cut vertices. The drawing condition is used once, to
turn "the two edge lists are disjoint" into "the two arcs meet only at vertices". -/

/-- A vertex of the graph lying on the realisation of a cycle is a vertex of that cycle. -/
theorem IsDrawing.mem_walkVertices_of_mem_edgesCover (h : IsDrawing G drawing) {e : β}
    {u v z : Plane} {D : List β} (hc : G.IsCycleThrough e u v D) (hzV : z ∈ V(G))
    (hz : z ∈ edgesCover drawing (e :: D)) : z ∈ G.walkVertices u D := by
  obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
  rcases List.mem_cons.1 hg with rfl | hg'
  · rcases h.vertex_mem_edgeArc hc.isLink hzV hzg with rfl | rfl
    · exact mem_walkVertices_self
    · exact hc.isPath.target_mem_walkVertices
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet (hc.isPath.edge_mem hg')
    rcases h.vertex_mem_edgeArc hxy hzV hzg with rfl | rfl
    · exact mem_walkVertices_of_mem_covered ⟨g, hg', hxy.inc_left⟩
    · exact mem_walkVertices_of_mem_covered ⟨g, hg', hxy.inc_right⟩

/-- **The realisation of a cycle, cut at two of its vertices, is two arcs meeting exactly
there.** The hypotheses are the output of `Graph.IsCycleThrough.split_at`, read in the plane. -/
theorem IsDrawing.arcs_of_split (h : IsDrawing G drawing) {a b : Plane} {D₁ D₂ : List β}
    (h₁ : G.IsPath a D₁ b) (h₂ : G.IsPath b D₂ a) (hab : a ≠ b)
    (hdisj : ∀ g ∈ D₁, g ∉ D₂)
    (hmeet : ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b) :
    IsArcBetween (edgesCover drawing D₁) a b ∧ IsArcBetween (edgesCover drawing D₂) b a ∧
      edgesCover drawing D₁ ∩ edgesCover drawing D₂ = {a, b} := by
  have harc₁ : IsArcBetween (edgesCover drawing D₁) a b :=
    h.path_isArcBetween h₁ (h₁.ne_nil hab)
  have harc₂ : IsArcBetween (edgesCover drawing D₂) b a :=
    h.path_isArcBetween h₂ (h₂.ne_nil (Ne.symm hab))
  refine ⟨harc₁, harc₂, Set.Subset.antisymm (fun z ⟨hz₁, hz₂⟩ => ?_) ?_⟩
  · -- A common point lies on an edge of each, and the two edges are distinct.
    obtain ⟨g₁, hg₁, hzg₁⟩ := mem_edgesCover_iff.1 hz₁
    obtain ⟨g₂, hg₂, hzg₂⟩ := mem_edgesCover_iff.1 hz₂
    have hne : g₁ ≠ g₂ := fun hh => hdisj g₁ hg₁ (hh ▸ hg₂)
    obtain ⟨-, hinc₁, hinc₂⟩ :=
      h.edge_inter (h₁.edge_mem hg₁) (h₂.edge_mem hg₂) hne hzg₁ hzg₂
    exact hmeet z (mem_walkVertices_of_mem_covered ⟨g₁, hg₁, hinc₁⟩)
      (mem_walkVertices_of_mem_covered ⟨g₂, hg₂, hinc₂⟩)
  · rintro z (rfl | rfl)
    exacts [⟨harc₁.left_mem, harc₂.right_mem⟩, ⟨harc₁.right_mem, harc₂.left_mem⟩]

end Graph

namespace Schoenflies

/-! ## The obligation this module does not discharge

**Read this before using `Graph.face_cycles`.** Everything below the base case is proved
*modulo* one hypothesis, `Schoenflies.CrosscutSplitsRegion`, and the final theorem carries it
as an argument. It is the exhaustion clause of `thm:polygonal-crosscut` — Theorem 2.8, in the
shape `Schoenflies.IsPolygonalCrosscut.region_eq` and
`Schoenflies.IsPolygonalCrosscut.cell_isComponent₁` already have it — at a crosscut whose two
endpoints are **arbitrary points of the curve**.

`main`'s Theorem 2.8 cannot be applied here, and the reason is not a missing bridge. Its
hypotheses `edges₁`/`edges₂` are stated against `ClosedPolygon.arcPieces C a k`, which splits
the polygon's edge list **at two of its vertices**; and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` every vertex of every realization of a curve is a
*corner* of it. In the induction below the two cut points are the ear's endpoints, which are
graph vertices at which the two cycle edges may perfectly well leave along opposite rays — the
curve then runs straight through the cut point, which is therefore a vertex of no
`ClosedPolygon` with that carrier, and no realization theorem can supply one. Discharging this
hypothesis needs Theorem 2.8 restated for an edge-list split made at arbitrary points, which in
turn needs the parity theory for polygon presentations carrying redundant vertices
(`Schoenflies.PrePolygon`) rather than only for `ClosedPolygon`. That is a separate module. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.**
`J` is a separating polygonal curve cut by the points `p, q` into the arcs `A₁, A₂`; `P` is a
polygonal crosscut from `p` to `q` meeting `J` only there and running inside the region `Ω`.
The claim is that every component of `Ω ∖ P` is a region of `A₁ ∪ P` or of `A₂ ∪ P` — the
blueprint's "Theorem 2.8 replaces `F` by exactly two regions, both bounded by cycles".

This is **assumed**, not proved; see the section docstring for why `main`'s Theorem 2.8 does
not apply. -/
def CrosscutSplitsRegion : Prop :=
  ∀ (J A₁ A₂ P Ω : Set Plane) (p q : Plane),
    IsSeparating J → IsPolygonal J → IsPolygonal P →
    IsArcBetween A₁ p q → IsArcBetween A₂ p q → A₁ ∪ A₂ = J → A₁ ∩ A₂ = {p, q} →
    IsArcBetween P p q → P ∩ J = {p, q} → IsRegionOf J Ω → P \ {p, q} ⊆ Ω →
    ∀ z ∈ Ω \ P, IsRegionOf (A₁ ∪ P) (connectedComponentIn (Ω \ P) z) ∨
      IsRegionOf (A₂ ∪ P) (connectedComponentIn (Ω \ P) z)

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a list of edges draws depends only on which edges are on it -/

theorem edgesCover_append (drawing : β → ℝ → Plane) (W₁ W₂ : List β) :
    edgesCover drawing (W₁ ++ W₂) = edgesCover drawing W₁ ∪ edgesCover drawing W₂ := by
  refine Set.Subset.antisymm (fun z hz => ?_)
    (Set.union_subset (edgesCover_mono (List.subset_append_left _ _))
      (edgesCover_mono (List.subset_append_right _ _)))
  obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
  exact (List.mem_append.1 hg).imp (fun h => mem_edgesCover h hzg) fun h => mem_edgesCover h hzg

theorem edgesCover_perm {W₁ W₂ : List β} (hp : W₁.Perm W₂) :
    edgesCover drawing W₁ = edgesCover drawing W₂ :=
  Set.Subset.antisymm (edgesCover_mono fun _ hg => hp.mem_iff.1 hg)
    (edgesCover_mono fun _ hg => hp.mem_iff.2 hg)

theorem edgesCover_reverse (drawing : β → ℝ → Plane) (W : List β) :
    edgesCover drawing W.reverse = edgesCover drawing W := edgesCover_perm (List.reverse_perm W)

/-! ## The induction step: one ear

"Suppose it holds for the current graph and add the next geometric ear. Its interior is
connected and disjoint from the current graph, so it lies in one current face `F` … the ear is
therefore a crosscut of that side, and Theorem `thm:polygonal-crosscut` replaces `F` by exactly
two regions, both bounded by cycles; all other faces are unchanged."

Everything here is proved, except that the appeal to Theorem 2.8 is to the hypothesis
`Schoenflies.CrosscutSplitsRegion` instead. -/

/-- **One ear.** Given `lem:face-cycles` for the current subgraph, it holds for the subgraph
enlarged by an ear — modulo `Schoenflies.CrosscutSplitsRegion`. -/
theorem IsDrawing.hasFaceCycles_union [G.Finite] (h : IsDrawing G drawing)
    (hobl : CrosscutSplitsRegion) (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hBG : B ≤ G) (hmot : HasFaceCycles B drawing) {D' : List β}
    (hpath : G.IsPath a D' b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D', g ∉ E(B)) :
    HasFaceCycles (B.union (G.pathGraphOf a D')) drawing := by
  haveI : B.Finite := Finite.of_le hBG
  have hB : IsDrawing B drawing := h.mono hBG
  have hne : D' ≠ [] := hpath.ne_nil hab
  have hPG : G.pathGraphOf a D' ≤ G := pathGraphOf_le hpath.isWalk
  have hB'G : B.union (G.pathGraphOf a D') ≤ G := union_le hBG hPG
  have hBB' : B ≤ B.union (G.pathGraphOf a D') := left_le_union _ _
  have hB' : IsDrawing (B.union (G.pathGraphOf a D')) drawing := h.mono hB'G
  have hpoly' : ∀ g ∈ E(B.union (G.pathGraphOf a D')), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hB'G.edgeSet_mono hg)
  have hQarc : IsArcBetween (edgesCover drawing D') a b := h.path_isArcBetween hpath hne
  have hQpoly : IsPolygonal (edgesCover drawing D') :=
    h.isPolygonal_edgesCover hpoly hpath.isWalk hne
  have hext : exterior (B.union (G.pathGraphOf a D')) drawing =
      exterior B drawing \ edgesCover drawing D' := by
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne]
  -- The ear lies in one face of the old subgraph.
  obtain ⟨z₀, hz₀, hsub₀⟩ := h.exists_face_of_ear hBG hpath hab hint hnew
  have hQinter : ∀ w ∈ edgesCover drawing D', w ∈ exterior B drawing →
      w ∈ face B drawing z₀ := by
    intro w hw hwe
    refine hsub₀ ⟨hw, fun hcon => hwe ?_⟩
    rcases hcon with rfl | rfl
    exacts [vertexSet_subset_pointSet ha, vertexSet_subset_pointSet hb]
  intro z hz
  rw [hext] at hz
  obtain ⟨hzB, hzQ⟩ := hz
  obtain ⟨e, u, v, D, hface⟩ := hmot z hzB
  by_cases hsame : face B drawing z = face B drawing z₀
  · -- The face the ear cuts.
    have hopenF : IsOpen (face B drawing z₀) := hB.isOpen_face z₀
    obtain ⟨haF, hbF⟩ := h.ends_mem_frontier_face hopenF hpath hab ha hb hsub₀
    have hfr : frontier (face B drawing z₀) = edgesCover drawing (e :: D) := by
      rw [← hsame]; exact hface.frontier_eq
    have haW : a ∈ B.walkVertices u D :=
      hB.mem_walkVertices_of_mem_edgesCover hface.isCycle ha (hfr ▸ haF)
    have hbW : b ∈ B.walkVertices u D :=
      hB.mem_walkVertices_of_mem_edgesCover hface.isCycle hb (hfr ▸ hbF)
    obtain ⟨D₁, D₂, hD1, hD2, hperm, hmeet⟩ := hface.isCycle.split_at haW hbW hab
    -- The two arcs use disjoint edge lists, because the cycle's own list repeats nothing.
    have hnodup : (e :: D).Nodup := List.nodup_cons.2 ⟨hface.isCycle.notMem,
      hface.isCycle.isPath.nodup⟩
    have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg hg₂ =>
      (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg g hg₂ rfl
    obtain ⟨harc₁, harc₂, hinter⟩ := hB.arcs_of_split hD1 hD2 hab hdisj hmeet
    have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ = edgesCover drawing (e :: D) := by
      rw [← edgesCover_append, edgesCover_perm hperm]
    -- The ear meets the cycle exactly in its own two ends.
    have hJsub : edgesCover drawing (e :: D) ⊆ pointSet B drawing :=
      edgesCover_subset_pointSet fun g hg => by
        rcases List.mem_cons.1 hg with rfl | hg'
        exacts [hface.isCycle.isLink.edge_mem, hface.isCycle.isPath.edge_mem hg']
    have hmeetJ : edgesCover drawing D' ∩ edgesCover drawing (e :: D) = {a, b} := by
      refine Set.Subset.antisymm (fun w hw =>
        h.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hJsub hw.2⟩) ?_
      rintro w (rfl | rfl)
      exacts [⟨hQarc.left_mem, hfr ▸ haF⟩, ⟨hQarc.right_mem, hfr ▸ hbF⟩]
    -- The crosscut hypothesis.
    have hzF : z ∈ face B drawing z \ edgesCover drawing D' := ⟨mem_face hzB, hzQ⟩
    have hfaceEq : face (B.union (G.pathGraphOf a D')) drawing z =
        connectedComponentIn (face B drawing z \ edgesCover drawing D') z := by
      have hstep : face (B.union (G.pathGraphOf a D')) drawing z =
          connectedComponentIn (exterior B drawing \ edgesCover drawing D') z := by
        rw [face, hext]
      rw [hstep, connectedComponentIn_diff]
      rfl
    have hcross := hobl (edgesCover drawing (e :: D)) (edgesCover drawing D₁)
      (edgesCover drawing D₂) (edgesCover drawing D') (face B drawing z) a b
      hface.isSeparating
      (h.isPolygonal_edgesCover hpoly (hface.isCycle.isWalk_cons.mono hBG)
        (List.cons_ne_nil _ _))
      hQpoly harc₁ harc₂.reverse hunion hinter hQarc hmeetJ hface.isRegionOf
      (by rw [hsame]; exact hsub₀) z hzF
    -- Either way, the new face is a region of the arc closed up by the ear.
    rcases hcross with hreg | hreg
    · obtain ⟨f, x, y, T, hcyc, hpermT⟩ := exists_spliced_cycle hBG hD1 hpath hab hnew hint
      have hcov : edgesCover drawing (f :: T) =
          edgesCover drawing D₁ ∪ edgesCover drawing D' := by
        rw [edgesCover_perm hpermT, edgesCover_append]
      exact ⟨f, x, y, T, hcyc, hB'.cycle_isSeparating hpoly' hcyc,
        by rw [hcov, hfaceEq]; exact hreg⟩
    · obtain ⟨f, x, y, T, hcyc, hpermT⟩ :=
        exists_spliced_cycle hBG hD2.reverse hpath hab hnew hint
      have hcov : edgesCover drawing (f :: T) =
          edgesCover drawing D₂ ∪ edgesCover drawing D' := by
        rw [edgesCover_perm hpermT, edgesCover_append, edgesCover_reverse]
      exact ⟨f, x, y, T, hcyc, hB'.cycle_isSeparating hpoly' hcyc,
        by rw [hcov, hfaceEq]; exact hreg⟩
  · -- The ear misses this face, which therefore survives unchanged.
    have hdis : Disjoint (face B drawing z) (pointSet (G.pathGraphOf a D') drawing) := by
      rw [h.pointSet_pathGraphOf hpath.isWalk hne, Set.disjoint_left]
      intro w hw hwQ
      refine absurd ?_ hsame
      refine (face_eq_or_disjoint (G := B) (drawing := drawing) z z₀).resolve_right fun hd => ?_
      exact Set.disjoint_left.1 hd hw (hQinter w hwQ (face_subset_exterior _ _ _ hw))
    exact ⟨e, u, v, D, hface.mono hBB' (face_union_eq_of_disjoint hzB hdis)⟩

/-! ## `lem:face-cycles`

"The cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`. We prove
by induction that every face is exactly one of the two regions bounded by its boundary cycle." -/

end Graph
end

section
-- module Solutions.Q146_CD.PrePolygonArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The arcs of a `PrePolygon`, and inserting a vertex

`Schoenflies.PrePolygon` is `Schoenflies.ClosedPolygon` without the `corner` field, so its
vertices may sit anywhere on the curve. This module carries §1 and §2 of the blueprint for such
a presentation: the edge list of an arc, the arc as a set, the two arcs of a splitting, and the
construction that makes the whole thing worth having — a prescribed point of the curve can be
made a vertex.

Everything below is the `Schoenflies.ClosedPolygon` development of
`Schoenflies/PolygonBridge.lean`, `Schoenflies/ParitySplitting.lean`,
`Schoenflies/PolygonalCrosscut.lean` and `Schoenflies/Realization.lean` with the structure
changed; every proof uses only `vertex_inj` and `edges_meet`, and `corner` is never mentioned.

## Why this module exists

`Schoenflies/Graph/K33Land.lean` and `Schoenflies/FaceCyclesLand.lean` each needed the same
apparatus and each transcribed it, the second under an `FC` suffix. The two copies were not
alpha-equivalent — `insertLast` in particular carried an extra hypothesis in one of them — so
the import checker never complained, and there were two of everything. This module is the
single copy; both consumers import it.

The one signature that genuinely differed is `Schoenflies.PrePolygon.insertLast`. The
`FaceCyclesLand` copy took, besides `hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)`, a
hypothesis `∀ j, P.vertex j ≠ z` saying the new point is not already a vertex. That is not an
extra assumption but a consequence: `Schoenflies.PrePolygon.vertex_ne_of_mem_openSegment`
derives it from `hz`. The general form — the one with `hz` alone — is what survives here.

## Inserting a vertex, and why it is the crux

`Schoenflies.PrePolygon.deleteLast` removes a vertex at which the curve runs straight (the
blueprint's Lemma 1.8); `Schoenflies.PrePolygon.insertLast` is the inverse move, and it is the
reason `PrePolygon` is the right structure for a consumer that needs named points to be
vertices. The vertex is inserted at the end of the list, interior to the last edge, so that the
only edge that changes is the last one, which splits in two;
`Schoenflies.PrePolygon.rotate` brings any edge there. Simplicity survives because the far end
of the split edge lies on neither half.

## Blueprint

* `Schoenflies.PrePolygon.vertex_natCast_ne`, `…edge_meet_earlier` — the elementary simplicity
  facts, §1.
* `Schoenflies.PrePolygon.chain`, `…mem_chain_iff`, `…isArcBetween_chain` — the union of the
  first `k` edges, and that it is an arc.
* `Schoenflies.PrePolygon.arcPieces`, `…arcPieces_add`, `…arcPieces_full`,
  `…isChainFrom_arcPieces`, `…arcPieces_split_perm`, `…sameEdges_arcPieces_split`,
  `…parity_splitting` — the edge list of an arc, and Lemma 2.7 for it.
* `Schoenflies.PrePolygon.arc`, `…arc_union`, `…arc_inter`, `…isArcBetween_arc`,
  `…arc_not_subset_endpoints`, `…isCompact_arc` — the two arcs of a splitting, §2.
* `Schoenflies.PrePolygon.parity_ne_iff_mem_farRegion` — `thm:polygonal-jordan` read as a
  separation criterion.
* `Schoenflies.PrePolygon.arcList`, `…poly_arcList`, `…isPolygonal_arc` — an arc as a polyline,
  which is how it is glued to a crosscut.
* `Schoenflies.segment_halves_inter`, `Schoenflies.right_notMem_left_half`,
  `Schoenflies.left_notMem_right_half` — §1: cutting a segment at an interior point, in order.
  General-purpose; they belong beside `Schoenflies.segment_split` in `Schoenflies/SegmentCut.lean`.
* `Schoenflies.PrePolygon.insertLast`, `…carrier_insertLast`,
  `Schoenflies.PrePolygon.exists_prePolygon_insert`, `…exists_prePolygon_vertices` — the inverse
  of the blueprint's "delete redundant vertices" (Lemma 1.8): *insert* one, anywhere on the curve.
* `Schoenflies.exists_prePolygon_points`, `…exists_prePolygon_split` — §1, the realization
  theorem **with the cut points anywhere on the curve**. Compare
  `Schoenflies.exists_closedPolygon_split`, which requires them to be corners.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

/-! ## Cutting a segment at an interior point, in order

The two halves of a cut segment meet only at the cut, and neither reaches the far end of the
other. Both are read off `Schoenflies/SegmentOrder.lean`: along a nondegenerate segment the
distance from one end is a coordinate. -/

/-! ## The realization theorem, with the cut points anywhere on the curve

`Schoenflies.exists_closedPolygon_split` requires the two cut points to be *corners*, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that requirement cannot be dropped while the
realization is a `ClosedPolygon`. For a `PrePolygon` there is no such obstruction: a point of the
curve is either already a vertex or interior to an edge, and an edge may be cut. -/

/-- **The realization theorem for `PrePolygon`, with named points.** Any finite list of points of
the curve — corners or not — can be required to be among the vertices. -/
theorem exists_prePolygon_points {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    (S : List Plane) (hS : ∀ p ∈ S, p ∈ C) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C ∧ ∀ p ∈ S, ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar', hnew, -⟩ :=
    PrePolygon.exists_prePolygon_vertices S P (fun z hz => by rw [hcar]; exact hS z hz)
  exact ⟨m', P', by rw [hcar', hcar], hnew⟩

/-- **The realization theorem tracking two named points**, for a presentation that may carry
redundant vertices. Unlike `Schoenflies.exists_closedPolygon_split` this asks nothing of the two
points but that they lie on the curve: a `PrePolygon` has no `corner` field to obstruct a vertex
where the curve runs straight. -/
theorem exists_prePolygon_split {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧ 1 ≤ k ∧ k ≤ m + 2 := by
  obtain ⟨m, P, hcar, hvert⟩ := exists_prePolygon_points hJ hP [p, q]
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      exacts [hp, hq])
  obtain ⟨a, ha⟩ := hvert p (by simp)
  obtain ⟨b, hb⟩ := hvert q (by simp)
  have hab : b - a ≠ 0 := fun he => hpq (by rw [← ha, ← hb, show b = a by linear_combination he])
  refine ⟨m, P, a, (b - a).val, hcar, ha, ?_, ?_, ?_⟩
  · rw [ZMod.natCast_rightInverse (b - a), add_sub_cancel]; exact hb
  · rcases Nat.eq_zero_or_pos (b - a).val with h0 | h0
    · exact absurd (by rw [← ZMod.natCast_rightInverse (b - a), h0, Nat.cast_zero]) hab
    · exact h0
  · have := ZMod.val_lt (b - a)
    omega

end Schoenflies
end

section
-- module Solutions.Q146_CD.OuterChain
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The outer face of a chain of plane graphs

`lem:outer-chain`. Let `Γ 0, …, Γ n` (`n ≥ 2`, so at least three graphs) be finite 2-connected
polygonal plane graphs, consecutive ones sharing at least two vertices and nonconsecutive ones
disjoint. If a point `x` is in the outer face of every consecutive pair `Γ p ∪ Γ (p+1)`, then it
is in the outer face of `Γ 0 ∪ ⋯ ∪ Γ n`.

## How the chain is formalised

The blueprint says "after subdividing common points into vertices". Here that is true by
construction rather than by a theorem: the family shares **one** ambient edge type `β` and
**one** drawing `drawing : β → ℝ → Plane`, and every member is a subgraph of a single plane
graph `G` — see `Graph.IsPlaneChain`. Two members therefore agree about the ends of a shared
edge, meet only where `G` lets them meet, and `Γ p ∪ Γ q` is `Graph.union` with nothing to
check. The ambient `G` is allowed to be larger than the chain's own union; a consumer that has
built all its pieces inside one polygonal overlay hands that overlay over as `G`.

`Graph.chainUnion Γ i m` is the block `Γ i ∪ Γ (i+1) ∪ ⋯ ∪ Γ (i+m)`, indexed by its **length**
`m` rather than by its right endpoint, so that the recursion is on `m` and the blueprint's
"choose `i ≤ j` with `j - i` minimum" is a plain strong induction on `m`. A consecutive pair is
`chainUnion Γ p 1`.

"`x` is in the outer face of `H`" is spelled, as everywhere in this development, as *`x` is off
the drawing and the face through it is unbounded* — `x ∈ exterior H drawing` together with
`¬ Bornology.IsBounded (face H drawing x)`. `Graph.unbounded_face_unique` is what makes that
"the" outer face, and `Graph.beyondSquare_subset_face` is how a consumer proves it.

## What is proved and what is assumed

The blueprint's proof is a minimal-counterexample argument on two measures: first the length of
the index interval, then the number of edges of the enclosing cycle lying outside `Γ (j-1)`.
Both minimisations are carried out here, as strong inductions, together with

* the reduction of "`x` lies in a bounded face" to "some cycle encloses `x`"
  (`Graph.encloses_of_isBounded_face`, from `Graph.face_cycles'`) and back
  (`Graph.isBounded_face_of_encloses`);
* 2-connectivity of every block, by iterating `Graph.IsTwoConnected.union`
  (`lem:union-two-connected`);
* the base case `j - i ≤ 1`, which is the blueprint's paragraph "If `j-i ≤ 1`, choose a
  consecutive pair `H` containing that union …";
* the two minimality consequences "`C` contains an edge of `Γ j` outside `Γ (j-1)`" and "`C`
  contains an edge of the earlier chain outside `Γ (j-1)`", each proved by pushing the cycle
  down into a shorter block with `Graph.IsCycleThrough.anti`;
* the splicing of a crosscut onto each of the two arcs (`Graph.exists_spliced_cycles`, from
  `Graph.exists_spliced_cycle`) and the edge count that makes the splice a strict improvement
  (`Graph.edgesOutside_splice_lt`, `Graph.exists_cycle_edgesOutside_lt`).

`Graph.Descent` is the middle paragraph of the blueprint's proof — from a cycle `C` of
`Γ i ∪ ⋯ ∪ Γ j` enclosing `x` and having an edge of `Γ j` and an edge of `Γ i ∪ ⋯ ∪ Γ (j-2)`
outside `Γ (j-1)`, produce a cycle of the same block enclosing `x` with strictly fewer edges
outside `Γ (j-1)`. It is a statement about **one** step, not about the chain's outer face.

It was assumed when this module was written. Both halves are now proved:

* `Schoenflies/CrosscutExists.lean` — combinatorial: build the crosscut, as
  `Graph.IsPlaneChain.crosscutExists`. Nothing geometric enters beyond
  `Graph.IsPlaneChain.disjoint_block_far`, "`Γ j` meets the earlier chain only through
  `Γ (j-1)`".
* `Schoenflies/CrosscutEncloses.lean` — geometric: "the path `R` lies on one side of `C` and is
  a crosscut there; by `thm:polygonal-crosscut`, at least one of `R ∪ C₁`, `R ∪ C₂` encloses
  `x`", as `Graph.crosscutEnclosesOff`. That module also carries the counterexample showing why
  the clause `x ∈ exterior H drawing` cannot be dropped — see the comment below, where the false
  version of it used to stand.

`Schoenflies/OuterChainClosed.lean` combines the two, and states `lem:outer-chain` with nothing
assumed.

## Blueprint

* `Graph.chainUnion` — `Γ i ∪ ⋯ ∪ Γ (i+m)`, with `chainUnion_le`, `le_chainUnion`,
  `chainUnion_finite`, `chainUnion_isTwoConnected` (the last is repeated
  `lem:union-two-connected`).
* `Graph.Encloses` — "that face is the interior of its boundary cycle, which therefore encloses
  `x`", as a property of a graph.
* `Graph.encloses_of_isBounded_face`, `Graph.isBounded_face_of_encloses` — the two directions
  of that reduction; the second is the blueprint's "the face of `H` containing `x` … lies in the
  bounded set `Int(C)` and therefore is not the outer face of `H`".
* `Graph.IsPlaneChain` — the hypotheses of `lem:outer-chain`; `Graph.OuterOnPairs` — its
  hypothesis on consecutive pairs.
* `Graph.IsCycleCrosscut` — the crosscut `R` of the cycle `C`, with the two arcs it cuts.
* `Graph.exists_spliced_cycles` — the two cycles `R ∪ C₁`, `R ∪ C₂`.
* `Graph.edgesOutside`, `Graph.edgesOutside_splice_lt`,
  `Graph.exists_cycle_edgesOutside_lt` — "it has fewer edges outside `Γ (j-1)` than `C`, since
  one nonempty outside portion of `C` has been replaced by `R ⊆ Γ (j-1)`".
* `Graph.Descent` — the crosscut paragraph of the proof; discharged in
  `Schoenflies/CrosscutEncloses.lean` from `Graph.CrosscutExists` alone.
* `Graph.IsPlaneChain.not_encloses` — the double minimisation.
* `Graph.IsPlaneChain.outer_chain` — **`lem:outer-chain`**, from `Graph.Descent`;
  `Graph.IsPlaneChain.outer_chain'` in `Schoenflies/OuterChainClosed.lean` is the same
  statement with nothing assumed.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

/-! ## Blocks of a chain -/

section General

variable {α β : Type*} {Γ : ℕ → Graph α β} {G K : Graph α β} {i m p : ℕ}

/-! ### Reading a cycle inside a subgraph

`Graph.IsCycleThrough.anti` is the cycle counterpart of `Graph.IsPath.anti`; it is what turns
"no edge of `C` is outside this block" into "`C` is a cycle of this block". -/

/-- Every edge on a cycle is an edge of the graph. -/
theorem IsCycleThrough.mem_edgeSet_cons {e g : β} {u v : α} {D : List β}
    (h : G.IsCycleThrough e u v D) (hg : g ∈ e :: D) : g ∈ E(G) := by
  rcases List.mem_cons.1 hg with rfl | hg
  · exact h.isLink.edge_mem
  · exact h.isPath.edge_mem hg

/-- A cycle all of whose edges belong to a subgraph is a cycle of that subgraph. -/
theorem IsCycleThrough.anti {e : β} {u v : α} {D : List β} (h : G.IsCycleThrough e u v D)
    (hKG : K ≤ G) (hE : ∀ g ∈ e :: D, g ∈ E(K)) : K.IsCycleThrough e u v D := by
  have he : e ∈ E(K) := hE e List.mem_cons_self
  have hl : K.IsLink e u v := (hKG.isLink_iff he).2 h.isLink
  exact ⟨hl, h.isPath.anti hKG hl.left_mem fun g hg => hE g (List.mem_cons_of_mem _ hg),
    h.notMem⟩

/-- A cycle of a subgraph is a cycle of the graph. -/
theorem IsCycleThrough.mono {e : β} {u v : α} {D : List β} (h : K.IsCycleThrough e u v D)
    (hKG : K ≤ G) : G.IsCycleThrough e u v D :=
  ⟨h.isLink.mono hKG, h.isPath.mono hKG, h.notMem⟩

/-! ### A crosscut of a cycle, with the two arcs it cuts

This is the combinatorial output of the blueprint's crosscut paragraph, bundled: the path `R` in
`F = Γ (j-1)`, its two endpoints `a, b` on the cycle, and the two arcs `D₁, D₂` the endpoints cut
the cycle into. Both arcs are required to carry an edge that `F` does not have — the blueprint's
"each arc contains an edge outside `Γ (j-1)`, because its endpoints belong to different maximal
subpaths of the intersection" — which is what makes the splice a strict improvement on **both**
sides, so that it does not matter which of the two spliced cycles turns out to enclose `x`. -/

end General

/-! ## Enclosing a point -/

/-! ## The chain -/

end Graph
end

section
-- module Solutions.Q146_CD.CrosscutEncloses
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `thm:polygonal-crosscut` at the level of sets, and the geometric half of the outer-chain descent

The blueprint sentence this module discharges is one line of the proof of `lem:outer-chain`:

> The path `R` lies on one side of `C` and is a crosscut there. By `thm:polygonal-crosscut`,
> exactly one of the two cycles `R ∪ C₁`, `R ∪ C₂` encloses `x`.

`Graph.CrosscutEncloses` of `Schoenflies/OuterChain.lean` is that sentence weakened to *at least*
one, which is all the descent uses; the weakening is not undone here.

## One theorem, no case split

The blueprint — and the note in `Schoenflies/OuterChain.lean` — distinguishes the crosscut running
inside `C` (settled by `Schoenflies.crosscutSplitsRegion`) from the crosscut running outside it
(`Schoenflies.IsPolygonalCrosscut.inside_exactly_one`). **Neither case distinction is needed.**
Both are consequences of Lemma 2.7, the parity identity

    π_{A₁ ∪ P} + π_{A₂ ∪ P} = π_J        at *every* point of the plane,

which holds with no geometry whatever (`Schoenflies.parity_split`), together with the *one*
direction of Theorem 2.3 that needs no realization of the two spliced curves:

    a closed chain whose cover separates has crossing count `0` on the unbounded region

(`Schoenflies.parity_eq_zero_of_mem_outside_cover`). If `x` were outside both spliced curves the
identity would read `0 + 0 = π_J(x)`, whereas `π_J(x) = 1` because `x` is inside `J`. That is the
whole proof of `Schoenflies.crosscut_inside_at_least_one`, and it is uniform in which side the
crosscut runs on. The `ClosedPolygon`-level `Schoenflies.IsPolygonalCrosscut.inside_exactly_one`,
whose `SameEdges` hypotheses cannot be met at graph vertices (see the section docstring of
`Schoenflies/FaceCyclesLand.lean`), is therefore not used at all.

The price is that the conclusion is "at least one" rather than "exactly one": the converse
direction of Theorem 2.3 for the spliced curves — `π = 1` forces the bounded region — *does* need
them realized, and the descent does not want it.

## The set-level statement is the artefact

`Schoenflies.crosscut_inside_at_least_one` takes sets and arcs, not polygons and not graphs:

    `J` a polygonal Jordan curve, `A₁, A₂` arcs from `p` to `q` covering it, `P` a polygonal arc
    from `p` to `q` meeting `J` only at `p, q`; then a point inside `J` and off `P` is inside
    `A₁ ∪ P` or inside `A₂ ∪ P`.

That is `thm:polygonal-crosscut` in the shape every plane-graph consumer wants, and
`Graph.crosscutEnclosesOff` is a two-page corollary of it. A second general fact falls out on the
way: `Schoenflies.two_arcs_inter_of_union` — two arcs with the same ends that cover a Jordan curve
meet **exactly** at those ends. That removes the "the two arcs meet only at the cut points" clause
from every consumer's obligations, which matters here because `Graph.IsCycleCrosscut` does not
record it (see below).

## Two defects of the interface handed to this module — read before integrating

**1. `Graph.CrosscutEncloses` as stated on `main` is false**, and the deliverable is
`Graph.CrosscutEnclosesOff`, which is it plus one hypothesis: `x ∈ exterior H drawing`. Nothing in
`Graph.CrosscutEncloses` prevents `x` from lying **on the crosscut's own drawing**: `x` is only
assumed to be inside the cycle `C`, and a crosscut running inside `C` may pass through `x`. Then
`x ∈ (A₁ ∪ P) ∩ (A₂ ∪ P)`, so `x` is inside neither spliced curve and the conclusion fails.

**The repair costs the chain nothing.** `Graph.OuterOnPairs` already puts `x` off the whole chain
(`Graph.IsPlaneChain.mem_exterior_chain`), and every block lies inside the chain
(`Graph.pointSet_mono`), so the clause can be produced where it is needed instead of being carried.
`Graph.IsPlaneChain.descent_of_crosscutOff` below therefore proves `Graph.Descent` **exactly as it
stands on `main`**, and `Graph.IsPlaneChain.outer_chain_of_crosscutExists` is `lem:outer-chain` with
`Graph.CrosscutEncloses` discharged outright. Nothing in `Schoenflies/OuterChain.lean` has to
change; `Graph.CrosscutEncloses` should simply be deleted, together with
`Graph.IsPlaneChain.descent_of_crosscut` and `Graph.IsPlaneChain.outer_chain_of_crosscut`, which the
two theorems here replace.

**2. `Graph.IsCycleCrosscut` does not record that the two arcs meet only at the two cut points**,
although `Graph.IsCycleThrough.split_at` — the theorem that builds them — produces exactly that
clause. It is not needed here, because `Schoenflies.two_arcs_inter_of_union` recovers the geometric
consequence from the Jordan curve; but a consumer that wants the *combinatorial* statement will
have to add the field.

## Blueprint

* `Schoenflies.two_arcs_inter_of_union` — §1: two arcs with the same ends covering a Jordan curve
  meet exactly at those ends. General; belongs beside `Schoenflies.two_arcs_unique` in
  `Schoenflies/Realization.lean`.
* `Schoenflies.crosscut_inside_at_least_one` — **`thm:polygonal-crosscut`**, at the level of sets:
  a point inside the curve and off the crosscut is inside one of the two spliced curves.
* `Graph.IsDrawing.mem_edgesCover_of_mem_walkVertices` — the converse of
  `Graph.IsDrawing.mem_walkVertices_of_mem_edgesCover`; general, belongs in
  `Schoenflies/Graph/CycleJordan.lean`.
* `Graph.CrosscutEnclosesOff`, `Graph.crosscutEnclosesOff` — the geometric half of the descent
  step of `lem:outer-chain`: `Graph.CrosscutEncloses` with the missing hypothesis restored,
  **proved**.
* `Graph.IsPlaneChain.descent_of_crosscutOff` — `Graph.Descent` from `Graph.CrosscutExists` alone;
  a drop-in replacement for `Graph.IsPlaneChain.descent_of_crosscut`.
* `Graph.IsPlaneChain.outer_chain_of_crosscutExists` — **`lem:outer-chain`**, assuming only the
  combinatorial half `Graph.CrosscutExists`.
-/

open Bornology Set

namespace Graph

open scoped Graph

open Schoenflies

variable {β : Type*} {H F : Graph Plane β} {drawing : β → ℝ → Plane}

/-! ## What a walk visits lies on what it draws

`Graph.IsDrawing.mem_walkVertices_of_mem_edgesCover` goes the other way; this direction is the
first half of the proof of `Graph.IsDrawing.pointSet_pathGraphOf`, extracted. -/

/-- **Every vertex a nonempty walk visits lies on what the walk draws.** The source is an end of
the first edge; every other visited vertex is an end of one of the edges by definition. -/
theorem IsDrawing.mem_edgesCover_of_mem_walkVertices (h : IsDrawing H drawing) {u v y : Plane}
    {W : List β} (hW : H.IsWalk u W v) (hne : W ≠ []) (hy : y ∈ H.walkVertices u W) :
    y ∈ edgesCover drawing W := by
  rcases mem_walkVertices_iff.1 hy with rfl | ⟨g, hg, hinc⟩
  · exact hW.left_mem_edgesCover h hne
  · exact mem_edgesCover hg (h.inc_mem_edgeArc hinc)

/-! ## The geometric half of the descent step

`Graph.CrosscutEncloses` of `Schoenflies/OuterChain.lean`, plus the hypothesis it is missing. -/

/-! ## `lem:outer-chain` needs only the combinatorial half now

The extra hypothesis of `Graph.CrosscutEnclosesOff` does **not** have to be threaded through
`Graph.Descent`: the chain hypothesis `Graph.OuterOnPairs` already puts `x` off the whole chain
(`Graph.IsPlaneChain.mem_exterior_chain`), and every block of the chain lies inside it. So the
repair costs the interface nothing at all — `Graph.Descent` is used here exactly as it stands on
`main`, and the two theorems below are drop-in replacements for
`Graph.IsPlaneChain.descent_of_crosscut` and `Graph.IsPlaneChain.outer_chain_of_crosscut` with
`Graph.CrosscutEncloses` discharged. -/

end Graph
end

section
-- module Solutions.Q146_CD.CrosscutExists
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Building the crosscut of the outer-chain descent

`Graph.CrosscutExists`, the combinatorial half of the descent step of `lem:outer-chain`,
discharged. Nothing here is geometric: the only fact about the plane that enters is
`Graph.IsPlaneChain.disjoint_block_far`, "`Γ j` meets the earlier chain only through
`Γ (j-1)`", and it is used exactly twice, to say that a vertex cannot lie on both
`Γ i ∪ ⋯ ∪ Γ (j-2)` and `Γ j`.

## The blueprint's argument, and how it is formalised here

The blueprint chooses points `a, b` in the relative interiors of an edge of `Γ j` and an edge
of the earlier chain, cuts the cycle `C` there, observes that each of the two arcs must meet
`Γ (j-1)`, and takes a minimum-length path of `Γ (j-1)` between two *maximal subpaths of
`C ∩ Γ (j-1)`* lying on different arcs.

Cutting a cycle at interior points of two of its edges is, combinatorially, the statement that
two distinct edges `g₁ ≠ g₂` of the cycle split the remaining edges into two arcs
(`Graph.IsCycleThrough.split_at_edges`): the closed walk reads

  `… ─g₁→ p ─W₁→ q ─g₂→ q' ─W₂→ p' ─g₁→ …`

and the two arcs are `W₁` and `W₂`, whose visited sets `S₁`, `S₂` are **disjoint** and
**cover** the vertices of the cycle. That pair of facts replaces the notion of a maximal
subpath entirely:

* "`a` and `b` lie on different maximal subpaths of `C ∩ Γ (j-1)`" becomes `a ∈ S₁`, `b ∈ S₂`;
* the property of maximal subpaths that the argument actually consumes — that no subpath of
  `C ∩ Γ (j-1)` joins two of them — becomes `Graph.exists_isCycleCrosscut`'s hypothesis
  `hpres`: *every edge of the cycle that `Γ (j-1)` also has keeps both of its ends on the same
  side*. That is immediate here, because the only cycle edges joining the two sides are `g₁`
  and `g₂`, and neither is an edge of `Γ (j-1)`.

With that, walking along cycle edges of `Γ (j-1)` cannot cross from `S₁` to `S₂`, and all four
minimality clauses of `Graph.IsCycleCrosscut` fall out of one minimisation: among all walks of
`Γ (j-1)` from `S₁` to `S₂`, take one of least length.

* it is a path, because any walk between its own two ends is a competitor
  (`Graph.IsWalk.isPath_of_minLength`);
* its internal vertices miss `C`, because a vertex of `C` on it lies in `S₁` or in `S₂`, and
  either way one of the two halves is a strictly shorter competitor;
* no edge of it is an edge of `C`: such an edge has both ends on `C`, hence both ends among
  `{a, b}` by the previous clause, hence joins `S₁` to `S₂` while lying in `Γ (j-1)`, which
  `hpres` forbids;
* each arc of `C` between `a` and `b` carries an edge outside `Γ (j-1)`, since otherwise the
  arc itself would be a walk of cycle edges of `Γ (j-1)` from `S₁` to `S₂`.

## Two general lemmas

`Graph.IsPath.split_at_edge` (cut a path at one of its edges, with the two freshness clauses
`Graph.IsCycleThrough.split_aux` asks for) and `Graph.IsCycleThrough.rotate` (present a cycle
through any one of its edges) are general facts about walks with nothing to do with this
development; they are the missing companions of `Graph.IsPath.split_meet` and
`Graph.IsCycleThrough.split_at` and belong in `Schoenflies/Graph/Walk.lean` and
`Schoenflies/FaceCyclesProof.lean` respectively.

## Blueprint

* `Graph.IsPath.split_at_edge`, `Graph.IsCycleThrough.rotate`,
  `Graph.IsCycleThrough.split_at_edges` — "choose points `a, b` in the relative interiors of
  these two edges. The two arcs of the cycle `C` from `a` to `b` are internally disjoint",
  read combinatorially (`lem:outer-chain`).
* `Graph.exists_isCycleCrosscut` — "since `Γ_{j-1}` is connected, there is a path in `Γ_{j-1}`
  from `P` to `C ∖ V(P)`. Choose such a path `R` of minimum length …", the whole minimality
  paragraph of `lem:outer-chain`, with the chain abstracted away into the two sides `S₁, S₂`.
* `Graph.IsPlaneChain.crosscutExists` — **`Graph.CrosscutExists`**, the combinatorial half of
  the descent step of `lem:outer-chain`.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

/-! ## Cutting a path at an edge, and rotating a cycle -/

section General

variable {α β : Type*} {G : Graph α β}

/-- **A path cut at one of its edges.** The two extra clauses are exactly what
`Graph.IsCycleThrough.split_aux` asks for: the near half never returns to the far end of the
cut edge, and a vertex reached by both halves is the near end of it.

This is the edge-indexed companion of `Graph.IsPath.split_meet`, which cuts at a vertex. -/
theorem IsPath.split_at_edge {u v : α} {W : List β} {g : β} (h : G.IsPath u W v) (hg : g ∈ W) :
    ∃ (W₁ W₂ : List β) (c d : α), W = W₁ ++ g :: W₂ ∧ G.IsPath u W₁ c ∧ G.IsLink g c d ∧
      G.IsPath d W₂ v ∧ c ∉ G.walkVertices d W₂ ∧
      ∀ z ∈ G.walkVertices u W₁, z ∈ G.walkVertices c (g :: W₂) → z = c := by
  induction h with
  | nil => simp at hg
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact ⟨[], W, u, w, rfl, .nil hl.left_mem, hl, hW, hfresh, fun z hz _ => by simpa using hz⟩
    obtain ⟨W₁, W₂, c, d, hWeq, h₁, hlg, h₂, hcd, hmeet⟩ := ih hg'
    have hsub₁ : W₁ ⊆ W := by rw [hWeq]; exact List.subset_append_left _ _
    have hsub₂ : g :: W₂ ⊆ W := by rw [hWeq]; exact List.subset_append_right _ _
    refine ⟨f :: W₁, W₂, c, d, by rw [hWeq]; rfl,
      .cons hl h₁ fun hmem => hfresh (walkVertices_mono hsub₁ hmem), hlg, h₂, hcd,
      fun z hz hz' => ?_⟩
    rcases mem_walkVertices_cons hl hz with hzu | hz''
    · -- The source of the extended prefix is fresh, so it cannot be reached by the far half.
      exfalso
      subst hzu
      refine hfresh ?_
      rcases mem_walkVertices_iff.1 hz' with heq | hcov
      · rw [heq]; exact walkVertices_mono hsub₁ h₁.target_mem_walkVertices
      · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)
    · exact hmeet z hz'' hz'

/-- **A cycle presented through any one of its edges.** `Graph.IsCycleThrough` names one edge
and one path; this re-presents the same cycle with a different edge named, which is what an
argument that has to start walking at a *given* edge needs. -/
theorem IsCycleThrough.rotate {e g : β} {u v : α} {D : List β} (hc : G.IsCycleThrough e u v D)
    (hg : g ∈ e :: D) :
    ∃ (c d : α) (W : List β), G.IsCycleThrough g c d W ∧ (g :: W).Perm (e :: D) := by
  rcases List.mem_cons.1 hg with rfl | hgD
  · exact ⟨u, v, D, hc, List.Perm.refl _⟩
  obtain ⟨A, B, c, d, hD, hA, hlg, hB, hcd, hmeet⟩ := hc.isPath.split_at_edge hgD
  have hne : c ≠ d := fun hh => hcd (hh ▸ mem_walkVertices_self)
  have hY : G.IsPath c [g] d := IsPath.single hlg hne
  -- A vertex reached both by the cut edge and by the far half is the far end of the cut edge.
  have hM2 : ∀ z ∈ G.walkVertices c [g], z ∈ G.walkVertices d B → z = d := by
    intro z hz hz'
    rcases mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, hinc⟩
    · exact absurd hz' hcd
    obtain rfl : f = g := by simpa using hf
    rcases hinc.eq_or_eq_of_isLink hlg with rfl | rfl
    · exact absurd hz' hcd
    · rfl
  obtain ⟨hpath, hperm, -⟩ :=
    hc.split_aux (X := A) (Y := [g]) (Z := B) (by rw [hD]; rfl) hA hY hB hne hmeet hM2
  -- The rotated cycle does not reuse its own named edge.
  have hnodup : (A ++ g :: B).Nodup := hD ▸ hc.isPath.nodup
  obtain ⟨-, hnd, -⟩ := List.nodup_append.1 hnodup
  have hgB : g ∉ B := (List.nodup_cons.1 hnd).1
  have hgA : g ∉ A := fun hmem =>
    List.disjoint_of_nodup_append hnodup hmem List.mem_cons_self
  have hge : g ≠ e := fun hh => hc.notMem (hh ▸ hgD)
  refine ⟨d, c, B ++ e :: A, ⟨hlg.symm, hpath, ?_⟩, hperm⟩
  simp only [List.mem_append, List.mem_cons, not_or]
  exact ⟨hgB, hge, hgA⟩

/-- Both ends of an edge of a cycle are vertices of the cycle. -/
theorem IsCycleThrough.mem_walkVertices_of_inc {e f : β} {u v z : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (hf : f ∈ e :: D) (hz : G.Inc f z) :
    z ∈ G.walkVertices u D := by
  rcases List.mem_cons.1 hf with rfl | hfD
  · rcases hz.eq_or_eq_of_isLink hc.isLink with rfl | rfl
    · exact mem_walkVertices_self
    · exact hc.isPath.target_mem_walkVertices
  · exact mem_walkVertices_of_mem_covered ⟨f, hfD, hz⟩

/-- **A cycle cut at two of its edges is two arcs.** This is the blueprint's "choose points
`a, b` in the relative interiors of these two edges; the two arcs of the cycle `C` from `a` to
`b` are internally disjoint", with the two interior points replaced by the two edges
themselves: the closed walk reads `… ─g₁→ p ─W₁→ q ─g₂→ q' ─W₂→ p' ─g₁→ …`, and the two arcs
`W₁, W₂` visit disjoint sets of vertices which together are all the vertices of the cycle. -/
theorem IsCycleThrough.split_at_edges {e g₁ g₂ : β} {u v : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (hg₁ : g₁ ∈ e :: D) (hg₂ : g₂ ∈ e :: D) (hne : g₁ ≠ g₂) :
    ∃ (p p' q q' : α) (W₁ W₂ : List β),
      G.IsLink g₁ p' p ∧ G.IsPath p W₁ q ∧ G.IsLink g₂ q q' ∧ G.IsPath q' W₂ p' ∧
        (g₁ :: (W₁ ++ g₂ :: W₂)).Perm (e :: D) ∧
        Disjoint (G.walkVertices p W₁) (G.walkVertices q' W₂) ∧
        G.walkVertices u D = G.walkVertices p W₁ ∪ G.walkVertices q' W₂ := by
  obtain ⟨p, p', Wc, hrot, hrperm⟩ := hc.rotate hg₁
  have hg₂c : g₂ ∈ Wc := by
    rcases List.mem_cons.1 (hrperm.mem_iff.2 hg₂) with rfl | hmem
    · exact absurd rfl hne
    · exact hmem
  obtain ⟨W₁, W₂, q, q', hWc, hW₁, hlg₂, hW₂, hqfresh, hmeet⟩ := hrot.isPath.split_at_edge hg₂c
  have hperm : (g₁ :: (W₁ ++ g₂ :: W₂)).Perm (e :: D) := by rw [← hWc]; exact hrperm
  -- The far arc's vertices are among those the cut edge reaches, so a vertex of both arcs
  -- would be the near end of `g₂`, which the far arc misses.
  have hsub : G.walkVertices q' W₂ ⊆ G.walkVertices q (g₂ :: W₂) := by
    intro z hz
    rcases mem_walkVertices_iff.1 hz with rfl | hcov
    · exact mem_walkVertices_of_mem_covered ⟨g₂, List.mem_cons_self, hlg₂.inc_right⟩
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hcov)
  have hdisj : Disjoint (G.walkVertices p W₁) (G.walkVertices q' W₂) := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    obtain rfl : z = q := hmeet z hz₁ (hsub hz₂)
    exact hqfresh hz₂
  -- Every vertex of the cycle lies on one of the two arcs, and conversely.
  have hmemC : ∀ (f : β) (z : α), f ∈ e :: D → G.Inc f z → z ∈ G.walkVertices u D :=
    fun _ _ hf hz => hc.mem_walkVertices_of_inc hf hz
  refine ⟨p, p', q, q', W₁, W₂, hrot.isLink.symm, hW₁, hlg₂, hW₂, hperm, hdisj,
    Set.Subset.antisymm (fun z hz => ?_) (Set.union_subset (fun z hz => ?_) fun z hz => ?_)⟩
  · -- A vertex of the cycle lies on an edge of it, hence on one of the two arcs.
    have hcov : z ∈ G.coveredVertices (e :: D) := by
      rcases mem_walkVertices_iff.1 hz with rfl | hcov
      · exact ⟨e, List.mem_cons_self, hc.isLink.inc_left⟩
      · exact coveredVertices_mono (List.subset_cons_self _ _) hcov
    obtain ⟨f, hf, hinc⟩ := hcov
    rcases List.mem_cons.1 (hperm.mem_iff.2 hf) with rfl | hf'
    · rcases hinc.eq_or_eq_of_isLink hrot.isLink with rfl | rfl
      · exact Or.inl mem_walkVertices_self
      · exact Or.inr hW₂.target_mem_walkVertices
    rcases List.mem_append.1 hf' with hf'' | hf''
    · exact Or.inl (mem_walkVertices_of_mem_covered ⟨f, hf'', hinc⟩)
    rcases List.mem_cons.1 hf'' with rfl | hf'''
    · rcases hinc.eq_or_eq_of_isLink hlg₂ with rfl | rfl
      · exact Or.inl hW₁.target_mem_walkVertices
      · exact Or.inr mem_walkVertices_self
    · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf''', hinc⟩)
  · rcases mem_walkVertices_iff.1 hz with heq | ⟨f, hf, hinc⟩
    · rw [heq]; exact hmemC g₁ p hg₁ hrot.isLink.inc_left
    · exact hmemC f z (hperm.mem_iff.1 (List.mem_cons_of_mem _ (List.mem_append_left _ hf))) hinc
  · rcases mem_walkVertices_iff.1 hz with heq | ⟨f, hf, hinc⟩
    · rw [heq]; exact hmemC g₂ q' hg₂ hlg₂.inc_right
    · exact hmemC f z (hperm.mem_iff.1
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hf)))) hinc

/-! ## The crosscut, from a two-sided cycle and a connected subgraph -/

end General

/-! ## The descent step's crosscut -/

end Graph
end

section
-- module Solutions.Q146_CD.ArcComplement
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A simple arc does not separate the plane

`thm:arc-complement`.  Two points off a simple arc `A` are covered by a chain of small
axis-parallel squares strung along `A`; the two points lie in the outer face of every
consecutive pair of links, hence — by `lem:outer-chain` — in the outer face of the whole chain,
which is an open connected set missing `A`.  `lem:polygonal-connected` then joins them there.

## The single-ambient-graph obligation, and how it is met

`Graph.IsPlaneChain` requires every link `Γ i` to be a subgraph of **one** ambient plane graph
with **one** drawing.  A link built as the polygonal overlay of its own squares would *not*
qualify: the total overlay cuts those same segments at the crossings with the squares of other
links as well, so a sub-overlay has edges the total overlay has subdivided further.

The construction is therefore inverted.  `familyPieces c N r` is **one** list holding the four
sides of every small square; `familyOverlay c N r` is the one overlay of that list; and a link
is carved out of it by restricting the *edge set*:

* `segGraph S` — the plane graph spanned by a set `S` of straight edges, with the ends of those
  edges as vertices.  `overlayGraph pieces points = segGraph {Q | Q ∈ overlayPieces pieces
  points}` holds by `rfl`, so `segGraph_mono` turns a subset of the overlay's edges into a
  subgraph of the overlay with nothing to prove.
* `squareGraph pieces points c r` — the edges of the overlay lying on the boundary of the square
  of radius `r` about `c`, spanned.  It occupies exactly that boundary
  (`pointSet_squareGraph`), and every cut point on the boundary is one of its vertices
  (`mem_vertexSet_squareGraph`), which is what `Graph.IsTwoConnected.union` needs.
* `familyChain c N m r i` — the `i`-th link: `Graph.chainUnion` of the `m + 1` square graphs of
  the `i`-th coarse subarc.  Consecutive links share the square at the sample they have in
  common; nonconsecutive links are disjoint.

`isPlaneChain_familyChain` is the theorem that this family is a `Graph.IsPlaneChain`, stated for
an arbitrary family of centres `c : ℕ → Plane` with two geometric hypotheses — consecutive
centres closer than one radius, nonconsecutive-block centres further apart than two radii.  The
arc enters only in `exists_face_of_notMem_arc`, where `c j = α(j/N)`.

## What is assumed

Three hypotheses, all named in the statements that carry them.

* `SquaresTwoConnected` — **the part of a polygonal overlay lying on the boundary of one of its
  squares is 2-connected.**  That part is the subdivided boundary cycle of an axis-parallel
  square: four sides, cut at finitely many interior points, every cut point a vertex, the four
  corners among the vertices.  It is a cycle, so `Graph.IsLongCycle.isTwoConnected` finishes;
  what a discharger must build is the cyclic order of the cut points along the four sides, for
  which `Schoenflies/SegmentOrder.lean` is the tool.  Nothing about the arc, the chain or the
  outer face enters the statement.
* `Graph.CrosscutExists` and `Graph.CrosscutEncloses` — the two halves of the descent step of
  `lem:outer-chain`, quoted from `Schoenflies/OuterChain.lean` unchanged.  Because the chain is
  built from choices made inside the proof of `exists_face_of_notMem_arc`, they appear there in
  ∀-form: `CrosscutExists` conditioned on `Graph.IsPlaneChain` (which is how a discharger will
  state it) and `CrosscutEncloses` for every point.

## Blueprint

* `segGraph`, `squareGraph`, `familyPieces`, `familyOverlay`, `familySquare`, `familyChain` —
  the construction of the proof of `thm:arc-complement`: "around every sample draw the boundary
  of the axis-parallel square of `ℓ^∞`-radius `δ/4`, and let `Γ_i` be the polygonal overlay
  (`lem:polygonal-overlay`) of the square boundaries associated with `A_i`".
* `familyChain_isTwoConnected` — "it follows inductively from `lem:union-two-connected` that
  `Γ_i` is 2-connected".
* `isPlaneChain_familyChain` — "consecutive graphs `Γ_i, Γ_{i+1}` share the square at their
  common sample.  If `|i-j| ≥ 2`, then `Γ_i` and `Γ_j` are disjoint".
* `outer_of_notMem_closedSquare`, `outerOnPairs_familyChain` — "the graph `Γ_i ∪ Γ_{i+1}` is
  contained in the `ℓ^∞`-square of radius `3d` centered at `a_i` … both `p` and `q` lie outside
  this containing square and hence in the outer face of the pair".
* `notMem_face_of_mem_openSquare` — "if it lies inside, the boundary cycle of that square
  separates it from the outer face of `G`".
* `exists_face_of_notMem_arc` — the whole proof of `thm:arc-complement` up to the last sentence.
* `isConnected_compl_arc`, `exists_simple_poly_compl_arc` — **`thm:arc-complement`**: the
  complement of a simple arc is connected, and any two of its points are joined in it by a
  simple polygonal arc.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## Part 1: the subgraph of the plane spanned by a set of straight edges -/

/-- **The plane graph spanned by a set of straight edges.**  Its vertices are the ends of
those edges and an edge links its two ends in either order — the shape of
`Schoenflies.overlayGraph`, with the edge list replaced by an arbitrary set.

This exists so that a *part* of one overlay can be spoken about as a graph in its own right
while remaining a subgraph of the whole overlay (`segGraph_mono`).  Building the part as an
overlay of its own source segments would not do: the total overlay cuts those segments at more
points, so a sub-overlay is not a subgraph of it. -/
def segGraph (S : Set Piece) : Graph Plane Piece where
  vertexSet := {v | ∃ P ∈ S, v = P.1 ∨ v = P.2}
  IsLink P x y := P ∈ S ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := S
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

variable {S T : Set Piece} {P : Piece} {x y v : Plane}

@[simp] theorem segGraph_vertexSet (S : Set Piece) :
    V(segGraph S) = {v | ∃ P ∈ S, v = P.1 ∨ v = P.2} := rfl

@[simp] theorem segGraph_edgeSet (S : Set Piece) : E(segGraph S) = S := rfl

@[simp] theorem segGraph_isLink :
    (segGraph S).IsLink P x y ↔ P ∈ S ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

/-! ## Part 2: the part of an overlay lying on one square

The chain graphs are assembled out of these.  Each is the set of overlay edges whose segment
lies on one small square boundary, spanned by `segGraph` — so it is a subgraph of the *total*
overlay, not an overlay of the four sides of that square alone. -/

/-! ## Part 3: the chain of square boundaries

Everything here is about a family of centres `c : ℕ → Plane` and one radius `r`; the arc enters
only in Part 5, where `c j = α (j / N)`.  Separating the two keeps the single-ambient-graph
bookkeeping free of parametrisation arithmetic. -/

/-! ## Part 4: the chain satisfies `Graph.IsPlaneChain`

This is the obligation `Schoenflies/OuterChain.lean` flagged: every link must be a subgraph of
**one** ambient plane graph with **one** drawing.  It is discharged by construction — every link
is a `Graph.chainUnion` of `familySquare`s, and every `familySquare` is a `segGraph` on a subset
of the edges of the one overlay `familyOverlay c N r`. -/

/-! ## Part 5: the outer face of the chain

Two plane facts, both general, and then the hypothesis of `lem:outer-chain` on consecutive
pairs. -/

/-! ## Part 6: from the Euclidean distance to the sup distance

The only place the two metrics have to be compared. `‖·‖ ≤ √2‖·‖∞` and `√2 < 2`, so half the
Euclidean distance is a *strict* lower bound for the sup distance — which is what turns the
blueprint's separation constants into square radii. -/

/-! ## Part 7: `thm:arc-complement`

The blueprint's proof, in its own order.  The two hypotheses `hce` and `hcen` are the two halves
of the descent step of `lem:outer-chain`, quoted verbatim from `Schoenflies/OuterChain.lean`;
`h2c` is the 2-connectivity of one subdivided square, discussed at `SquaresTwoConnected`. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.ArcMonotone
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A continuous injection between two arcs is monotone

Two parametrizations `f` and `f'` of two arcs, and a continuous injection `g` carrying the
first arc onto the second. Then `g` respects the order in which the two parametrizations
traverse their arcs: the composite parameter map

  `s ↦ (the parameter at which f' sits at g (f s))`

is strictly monotone on `[0, 1]` — increasing or decreasing according to whether `g` matches
the two parametrizations' starting points or swaps them. Consequently `g` carries a subarc of
the first arc onto a subarc of the second, with the *corresponding* parameters.

That last sentence is what every consumer wants, and it is `ArcMatch.image_image_uIcc`:

  `g '' (f '' uIcc s u) = f' '' uIcc (transferParam f f' g s) (transferParam f f' g u)`.

Stated over `uIcc`, it is **orientation-free**: `uIcc` is unordered, so the identity holds
whether the transfer map increases or decreases, and a consumer that does not know which way
round its two parametrizations run does not have to find out. Only the two corollaries about
*initial* and *terminal* subarcs (`image_initial`, `image_terminal`) need the matching-endpoint
hypothesis, and they take it explicitly.

## How the parameter map is built

No inverse parametrization is constructed as a continuous map. `arcParam f' p` picks, by choice,
*a* parameter in `[0, 1]` sitting at `p`; injectivity of `f'` makes it *the* parameter, and its
continuity along the composite is proved by hand from `Schoenflies.exists_ball_inter_subset_image`
— the statement, already on `main`, that a parametrization is an open map onto its arc. That is
exactly the continuity of the inverse, in the only form needed here, and it avoids constructing a
homeomorphism `↥I ≃ₜ ↥A` and pushing it through subtype coercions.

With the composite continuous and injective on `[0, 1]`, Mathlib's
`ContinuousOn.strictMonoOn_of_injOn_Icc'` supplies the monotone-or-antitone dichotomy.

## Blueprint

There is **no blueprint statement for this**. The manuscript uses it silently, in two places:

* `def:matched-pair`, clause 3 — "on each corresponding pair of edges, `g` restricts to a fixed
  chosen homeomorphism between them, matching endpoints". When an edge is subdivided, the two
  halves of that homeomorphism have to be the chosen homeomorphisms of the two new edges; that
  they *are* half-arc-to-half-arc, rather than merely arc-to-arc, is this file.
* `def:generated-structure`, operation 1 (edge subdivision) — "the corresponding point is
  inserted into the corresponding edge using the edge parametrization". "Corresponding" is the
  transfer map below, and the sentence's content is that inserting corresponding points splits
  the edge homeomorphism into two edge homeomorphisms.

Declarations:

* `Schoenflies.arcParam` — the parameter of a point on a parametrized arc.
* `Schoenflies.ArcMatch` — the hypothesis bundle: two parametrized arcs and a continuous
  injection of the first onto the second.
* `Schoenflies.transferParam` — the induced map on parameters.
* `Schoenflies.ArcMatch.continuousOn_param`, `…injOn_param`,
  `…strictMonoOn_or_strictAntiOn_param` — the monotonicity.
* `Schoenflies.ArcMatch.image_image_uIcc`, `…image_subarc` — the orientation-free conclusion.
* `Schoenflies.ArcMatch.image_initial`, `…image_terminal` — initial and terminal subarcs, given
  matching endpoints.
-/

open Set unitInterval

namespace Schoenflies

/-! ### The parameter of a point on a parametrized arc -/

open scoped Classical in
/-- The parameter in `[0, 1]` at which `f` sits at `p`, chosen; junk (`0`) when there is none.

Only ever used under an injectivity hypothesis, which makes the choice unique
(`arcParam_eq_of_apply`). -/
noncomputable def arcParam (f : ℝ → Plane) (p : Plane) : ℝ :=
  if h : ∃ s, s ∈ I ∧ f s = p then h.choose else 0

variable {f f' : ℝ → Plane} {g : Plane → Plane} {p : Plane} {s u : ℝ}

theorem arcParam_spec (hp : p ∈ f '' I) : arcParam f p ∈ I ∧ f (arcParam f p) = p := by
  have h : ∃ s, s ∈ I ∧ f s = p := by
    obtain ⟨s, hs, rfl⟩ := hp
    exact ⟨s, hs, rfl⟩
  rw [arcParam, dif_pos h]
  exact h.choose_spec

theorem arcParam_mem_I (hp : p ∈ f '' I) : arcParam f p ∈ I := (arcParam_spec hp).1

theorem apply_arcParam (hp : p ∈ f '' I) : f (arcParam f p) = p := (arcParam_spec hp).2

/-- Under injectivity the chosen parameter is the only one. -/
theorem arcParam_eq_of_apply (hi : InjOn f I) (hs : s ∈ I) (hfs : f s = p) : arcParam f p = s :=
  hi (arcParam_mem_I ⟨s, hs, hfs⟩) hs ((apply_arcParam ⟨s, hs, hfs⟩).trans hfs.symm)

/-! ### The hypothesis bundle -/

/-- Two parametrized arcs and a continuous injection of the first onto the second.

A `Prop`-valued bundle rather than seven separate hypotheses: every theorem below needs most of
them, and a consumer assembles it once. -/
structure ArcMatch (f f' : ℝ → Plane) (g : Plane → Plane) : Prop where
  /-- The source parametrization is continuous. -/
  continuousOn_src : ContinuousOn f I
  /-- …and injective. -/
  injOn_src : InjOn f I
  /-- The target parametrization is continuous. -/
  continuousOn_tgt : ContinuousOn f' I
  /-- …and injective. -/
  injOn_tgt : InjOn f' I
  /-- The map is continuous on the source arc. -/
  continuousOn_map : ContinuousOn g (f '' I)
  /-- …and injective on it. -/
  injOn_map : InjOn g (f '' I)
  /-- …and carries the source arc onto the target arc. -/
  image_eq : g '' (f '' I) = f' '' I

/-- The map `g` induces on parameters: send `s` to the parameter at which `f'` sits at
`g (f s)`.

A plain `def`, not depending on the `ArcMatch` proof, so that a consumer can name the target
parameter before it has assembled the hypotheses — which is exactly what
`Schoenflies/RealizeSubdivHomeo.lean` does. -/
noncomputable def transferParam (f f' : ℝ → Plane) (g : Plane → Plane) : ℝ → ℝ :=
  fun s => arcParam f' (g (f s))

namespace ArcMatch

variable (h : ArcMatch f f' g)
include h

theorem mem_image_map (hs : s ∈ I) : g (f s) ∈ f' '' I := by
  rw [← h.image_eq]
  exact ⟨f s, ⟨s, hs, rfl⟩, rfl⟩

theorem param_mem_I (hs : s ∈ I) : transferParam f f' g s ∈ I :=
  arcParam_mem_I (h.mem_image_map hs)

/-- **The defining property**: the target parametrization at the transferred parameter is the
image of the source parametrization. -/
theorem apply_param (hs : s ∈ I) : f' (transferParam f f' g s) = g (f s) :=
  apply_arcParam (h.mem_image_map hs)

/-- The transferred parameter is characterized, not merely chosen. -/
theorem param_eq (hu : u ∈ I) (heq : f' u = g (f s)) : transferParam f f' g s = u :=
  arcParam_eq_of_apply h.injOn_tgt hu heq

theorem injOn_param : InjOn (transferParam f f' g) I := by
  intro s hs u hu hsu
  -- Equal transferred parameters give equal images, and both maps are injective.
  have : g (f s) = g (f u) := by
    rw [← h.apply_param hs, ← h.apply_param hu, hsu]
  exact h.injOn_src hs hu (h.injOn_map ⟨s, hs, rfl⟩ ⟨u, hu, rfl⟩ this)

/-- **The transfer map is continuous.** This is the continuity of the inverse parametrization
`f'⁻¹`, in the only form needed, and it is proved from the fact that a parametrization is an open
map onto its arc: a prescribed parameter window around `transferParam f f' g s` pulls back to a
ball around `g (f s)`, and continuity of `g ∘ f` turns that into a parameter window around `s`. -/
theorem continuousOn_param : ContinuousOn (transferParam f f' g) I := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set u₀ := transferParam f f' g s with hu₀
  have hu₀I : u₀ ∈ I := h.param_mem_I hs
  have hval : f' u₀ = g (f s) := h.apply_param hs
  -- The point `g (f s)` is the image of the parameter window `Ioo (u₀ - ε) (u₀ + ε)`.
  have hx : g (f s) ∈ f' '' (Ioo (u₀ - ε) (u₀ + ε) ∩ I) :=
    ⟨u₀, ⟨⟨by linarith, by linarith⟩, hu₀I⟩, hval⟩
  obtain ⟨r, hr, hball⟩ :=
    exists_ball_inter_subset_image h.continuousOn_tgt h.injOn_tgt isOpen_Ioo hx
  -- `g ∘ f` is continuous within the parameter interval at `s`.
  have hcomp : ContinuousWithinAt (fun x => g (f x)) I s :=
    (h.continuousOn_map (f s) ⟨s, hs, rfl⟩).comp (h.continuousOn_src s hs) (mapsTo_image f I)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp hcomp r hr
  refine ⟨δ, hδ, fun {x} hxI hxs => ?_⟩
  have hin : g (f x) ∈ Metric.ball (g (f s)) r ∩ f' '' I :=
    ⟨Metric.mem_ball.mpr (hclose hxI hxs), h.mem_image_map hxI⟩
  obtain ⟨v, ⟨hvw, hvI⟩, hveq⟩ := hball hin
  -- Injectivity of `f'` identifies that parameter with the transferred one.
  have : transferParam f f' g x = v :=
    h.injOn_tgt (h.param_mem_I hxI) hvI ((h.apply_param hxI).trans hveq.symm)
  rw [Real.dist_eq, this, abs_lt]
  exact ⟨by linarith [hvw.1], by linarith [hvw.2]⟩

/-- **The transfer map is strictly monotone**, in one direction or the other. Which one is
decided by the endpoints; every conclusion below that does not mention an endpoint holds in
both cases. -/
theorem strictMonoOn_or_strictAntiOn_param :
    StrictMonoOn (transferParam f f' g) I ∨ StrictAntiOn (transferParam f f' g) I :=
  ContinuousOn.strictMonoOn_of_injOn_Icc' zero_le_one h.continuousOn_param h.injOn_param

/-! ### The image of a parameter interval -/

theorem param_mem_uIcc (hs : s ∈ I) (hu : u ∈ I) {x : ℝ} (hx : x ∈ uIcc s u) :
    transferParam f f' g x ∈ uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  have hxI : x ∈ I := uIcc_subset_I hs hu hx
  rw [mem_uIcc] at hx ⊢
  rcases h.strictMonoOn_or_strictAntiOn_param with hm | hm
  · rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨hm.monotoneOn hs hxI h₁, hm.monotoneOn hxI hu h₂⟩
    · exact Or.inr ⟨hm.monotoneOn hu hxI h₁, hm.monotoneOn hxI hs h₂⟩
  · rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨hm.antitoneOn hxI hu h₂, hm.antitoneOn hs hxI h₁⟩
    · exact Or.inl ⟨hm.antitoneOn hxI hs h₂, hm.antitoneOn hu hxI h₁⟩

/-- **The transfer map carries a parameter interval onto the corresponding one.** Stated over
`uIcc`, so it is indifferent to the direction of either traversal. -/
theorem image_param_uIcc (hs : s ∈ I) (hu : u ∈ I) :
    transferParam f f' g '' uIcc s u =
      uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h.param_mem_uIcc hs hu hx
  · -- The reverse inclusion is the intermediate value theorem; no monotonicity needed.
    exact intermediate_value_uIcc (h.continuousOn_param.mono (uIcc_subset_I hs hu))

/-- **The map carries a subarc onto the corresponding subarc.** The form every consumer wants,
and the reason for this file. -/
theorem image_image_uIcc (hs : s ∈ I) (hu : u ∈ I) :
    g '' (f '' uIcc s u) =
      f' '' uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  rw [← h.image_param_uIcc hs hu, ← image_comp, ← image_comp]
  refine image_congr fun x hx => ?_
  exact (h.apply_param (uIcc_subset_I hs hu hx)).symm

/-! ### Matching endpoints -/

/-- An interior parameter transfers to an interior parameter, without assuming which way the two
parametrizations run: the two endpoints go to the two endpoints in one order or the other, and
strict monotonicity keeps the inside inside. -/
theorem param_mem_Ioo_of_ends (hends : (transferParam f f' g 0 = 0 ∧ transferParam f f' g 1 = 1) ∨
    (transferParam f f' g 0 = 1 ∧ transferParam f f' g 1 = 0)) (hu : u ∈ Ioo (0 : ℝ) 1) :
    transferParam f f' g u ∈ Ioo (0 : ℝ) 1 := by
  have huI : u ∈ I := Ioo_subset_Icc_self hu
  rcases h.strictMonoOn_or_strictAntiOn_param with hm | hm
  · rcases hends with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have hlo := hm zero_mem_I huI hu.1
      have hhi := hm huI one_mem_I hu.2
      rw [e0] at hlo
      rw [e1] at hhi
      exact ⟨hlo, hhi⟩
    · -- Increasing yet sending `0` above `1`: impossible.
      have := hm zero_mem_I one_mem_I zero_lt_one
      rw [e0, e1] at this
      linarith
  · rcases hends with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have := hm zero_mem_I one_mem_I zero_lt_one
      rw [e0, e1] at this
      linarith
    · have hlo := hm huI one_mem_I hu.2
      have hhi := hm zero_mem_I huI hu.1
      rw [e1] at hlo
      rw [e0] at hhi
      exact ⟨hlo, hhi⟩

end ArcMatch

end Schoenflies
end

section
-- module Solutions.Q146_CD.GeneratedStructure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Generated matched cell structures

The spine of Part II. `def:generated-structure` says that every cell structure the Schönflies
construction ever meets is obtained from the initial two-face structure of
`prop:initial-pair` by a finite sequence of two elementary operations — *edge subdivision* and
*2-cell splitting by an ear* — performed simultaneously in the two realizations. This module
builds the two operations as `def`s on `Schoenflies.CellStructure`, closes them into the
inductive `Schoenflies.GeneratedStructure`, and proves the assertions of
`lem:cellulation-invariants` that are within reach.

## Blueprint

* `Schoenflies.CellStructure.SubdivData`, `Schoenflies.CellStructure.subdivideEdge` — the first
  elementary operation of `def:generated-structure` (tex, operation 1).
* `Schoenflies.CellStructure.SplitData`, `Schoenflies.CellStructure.splitFace` — the second
  (tex, operation 2).
* `Schoenflies.GeneratedStructure` — `def:generated-structure`, as the inductive closure of a
  base structure under the two operations.
* `Schoenflies.CellStructure.SubdivData.parent`,
  `Schoenflies.CellStructure.SplitData.parent`,
  `Schoenflies.CellStructure.SubdivData.sub_parent`,
  `Schoenflies.CellStructure.SplitData.sub_parent` — assertion (iv) of
  `lem:cellulation-invariants`, the parent map of one elementary refinement and the
  compatibility `σ ≼ τ → par σ ≼ par τ`.
* `Schoenflies.CellStructure.CombInvariants`, its two preservation theorems
  `Schoenflies.CellStructure.SubdivData.combInvariants` and
  `Schoenflies.CellStructure.SplitData.combInvariants`, and
  `Schoenflies.GeneratedStructure.combInvariants`, which closes the induction — assertions
  (iii), (v), (vi), together with the abstract form of (viii) and the bookkeeping facts about
  `≼_abs` that the blueprint uses silently.
* `Schoenflies.GeneratedStructure.trans` — refinement sequences compose.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition` — assertion (i) for one
  realization, and from it, with no further geometry:
  `.frontier_property` (assertion (ii)), `.sub_iff_subset_closure` and
  `Schoenflies.CellStructure.subset_closure_congr` (assertion (ix)), and `.face_eq`
  (assertion (viii)).
* `Schoenflies.CellStructure.SubdivData.IsRefinement` and
  `Schoenflies.CellStructure.SubdivData.IsRefinement.isCellDecomposition` — the induction step
  of assertion (i) over the *first* constructor: a realization of the subdivided structure that
  refines a realization of the old one inherits (i).
* `Schoenflies.crosscut_cell_partition` — the geometric content of one 2-cell split, from
  `Schoenflies.general_crosscut`, in the shape assertion (i) consumes.

**Not here.** The induction step of (i) over the *second* constructor, and assertion (vii) in
either. `crosscut_cell_partition` is the geometric input the split step needs; what is missing
is the `SplitData` analogue of `IsRefinement` — a relation between a realization of
`S.splitFace d` and one of `S`, saying that the ear is drawn as a crosscut of the realized open
2-cell — and the identification of the abstract boundary walk of a 2-cell with the Jordan curve
of assertion (vii). Assertions (ii), (viii) and (ix) are stated here against `(i)` as a
hypothesis, so later constructors can use the resulting theorem directly.

Two general graph facts are proved here for want of a home: `Schoenflies.subdivGraph` (with
`Schoenflies.subdivGraph_mono` and `Schoenflies.subdivGraph_eq_self`) and
`Schoenflies.isLink_of_le_of_mem_edgeSet`. The second belongs in `Schoenflies/Graph/`; nothing
on `main` states it.

## Design

**The base case is a parameter.** `prop:initial-pair` is being built elsewhere, so
`GeneratedStructure S₀ S` is relative to an arbitrary base `S₀`, and every invariant theorem
reads "the invariants of `S₀` propagate to `S`". That is both cleaner and independent of the
initial pair's schedule: the consumer supplies `S₀` and the base case, and gets the invariant
at every stage.

**`rem:intermediate-disconnection` is honoured by omission.** Nothing in this module mentions
`Realization.nonboundary`, let alone its connectedness: an intermediate stage really can have
disconnected open nonboundary part, and every statement here is proved without that hypothesis.

**`≼_abs` stays a raw datum.** `CellStructure.sub` is not made a preorder. The reflexivity and
transitivity facts that the blueprint uses are fields of `CombInvariants`, established for the
base and propagated, never assumed of an arbitrary `CellStructure`.

**Fidelity note on reflexivity.** The blueprint's two update lists (tex, operations 1 and 2)
do not mention the reflexive pairs of the *new* cells, while the base relation is declared to
contain "the reflexive pairs". Assertion (i) forces them: the closure of a new open cell
contains that cell, and (i) says a closed cell is the union of its open subcells. Both `subRel`
definitions below therefore declare `σ ≼ σ` for every new cell; that is the only place where
this module adds a pair the blueprint's prose does not list.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Schoenflies

variable {γ : Type*}

/-! ### Subdividing an edge of a graph

The graph-theoretic half of the first elementary operation, stated for an arbitrary graph so
that one definition serves both the skeleton and the outer cycle: when `H` does not carry `e`
from `x` to `y` — which is the case for the outer cycle whenever the subdivided edge is not an
outer edge — the construction leaves `H` alone (`subdivGraph_eq_self`). Without that, the
definition of `CellStructure.subdivideEdge` would need a case split on whether the subdivided
edge is outer, and every lemma about it would inherit the split. -/

variable {H K : Graph γ γ} {e x y v e₁ e₂ : γ}

/-! ### The cells of an abstract structure -/

namespace CellStructure

variable (S : CellStructure γ)

theorem mem_cells_of_mem_vertexSet {z : γ} (h : z ∈ V(S.skel)) : z ∈ S.cells :=
  Or.inl (Or.inl h)

theorem mem_cells_of_mem_edgeSet {z : γ} (h : z ∈ E(S.skel)) : z ∈ S.cells :=
  Or.inl (Or.inr h)

theorem mem_cells_of_mem_faces {z : γ} (h : z ∈ S.faces) : z ∈ S.cells := Or.inr h

/-- The cells of a walk: its edges, and the vertices it visits. This is what the blueprint
calls "the cells of the boundary walk `Bᵢ`". -/
def pathCells (u : γ) (W : List γ) : Set γ := {c | c ∈ W} ∪ S.skel.walkVertices u W

variable {S}

/-! ### Elementary operation 1: edge subdivision

Blueprint, `def:generated-structure`, operation 1: "the edge `e` is replaced by a new vertex
`v` and two new edges `e₁, e₂`, whose endpoints are `v` together with one old endpoint of `e`
each; the relation `≼_abs` is extended by declaring `v ≼ e₁` and `v ≼ e₂`, each old endpoint of
`e` a subcell of its adjacent new edge, and `v, e₁, e₂` subcells of exactly the old strict
supercells of `e`; all pairs not involving `e` are unchanged." -/

/-- **The orientation-aware replacement of a subdivided edge in a walk.**
`SubstWalk S edge left right newEdge₁ newEdge₂ u W W'` says that `W'` is obtained from `W`
by replacing each traversal of `edge` by the two new edges in the order in which the walk
crosses them.  The departing vertex `u` supplies the orientation information that the edge
list alone does not contain. -/
inductive SubstWalk (S : CellStructure γ) (edge left right newEdge₁ newEdge₂ : γ) :
    γ → List γ → List γ → Prop
  /-- The empty walk is unchanged. -/
  | nil (u : γ) : SubstWalk S edge left right newEdge₁ newEdge₂ u [] []
  /-- Crossing the subdivided edge from `left` to `right`. -/
  | forward {W W' : List γ}
      (h : SubstWalk S edge left right newEdge₁ newEdge₂ right W W') :
      SubstWalk S edge left right newEdge₁ newEdge₂ left (edge :: W)
        (newEdge₁ :: newEdge₂ :: W')
  /-- Crossing the subdivided edge from `right` to `left`. -/
  | backward {W W' : List γ}
      (h : SubstWalk S edge left right newEdge₁ newEdge₂ left W W') :
      SubstWalk S edge left right newEdge₁ newEdge₂ right (edge :: W)
        (newEdge₂ :: newEdge₁ :: W')
  /-- Any other edge is kept. -/
  | other {u w f : γ} {W W' : List γ} (hl : S.skel.IsLink f u w) (hf : f ≠ edge)
      (h : SubstWalk S edge left right newEdge₁ newEdge₂ w W W') :
      SubstWalk S edge left right newEdge₁ newEdge₂ u (f :: W) (f :: W')

/-- The data of one **edge subdivision**: the edge to be subdivided together with its two
endpoints, and three names — fresh, i.e. not cells of `S` — for the new vertex and the two new
edges. It also carries the orientation-aware replacement of every 2-cell boundary walk: the
direction in which a walk traverses an edge cannot be recovered from the edge list alone.

The operation is a `def` of this data, not an existential: everything downstream refers to
`d.newVertex`, `d.newEdge₁`, `d.newEdge₂` and `d.newBoundary` by name. -/
structure SubdivData (S : CellStructure γ) where
  /-- The subdivided 1-cell. -/
  edge : γ
  /-- One endpoint of the subdivided edge. -/
  left : γ
  /-- The other endpoint. -/
  right : γ
  /-- The inserted 0-cell. -/
  newVertex : γ
  /-- The new 1-cell from `left` to `newVertex`. -/
  newEdge₁ : γ
  /-- The new 1-cell from `newVertex` to `right`. -/
  newEdge₂ : γ
  /-- `edge` really runs from `left` to `right`. -/
  isLink : S.skel.IsLink edge left right
  /-- The new vertex is a fresh name. -/
  newVertex_notMem : newVertex ∉ S.cells
  /-- The first new edge is a fresh name. -/
  newEdge₁_notMem : newEdge₁ ∉ S.cells
  /-- The second new edge is a fresh name. -/
  newEdge₂_notMem : newEdge₂ ∉ S.cells
  /-- The three new names are distinct. -/
  newVertex_ne₁ : newVertex ≠ newEdge₁
  /-- The three new names are distinct. -/
  newVertex_ne₂ : newVertex ≠ newEdge₂
  /-- The three new names are distinct. -/
  newEdge_ne : newEdge₁ ≠ newEdge₂
  /-- The boundary lists after subdivision, chosen with the orientation of each old walk. -/
  newBoundary : γ → List γ
  /-- Every face boundary is a closed walk, and its new boundary is obtained by the
  orientation-aware edge replacement from the same starting vertex. -/
  boundary_subst : ∀ ⦃F⦄, F ∈ S.faces → ∃ u,
    S.skel.IsWalk u (S.boundary F) u ∧
      SubstWalk S edge left right newEdge₁ newEdge₂ u (S.boundary F) (newBoundary F)

namespace SubdivData

variable {S : CellStructure γ} (d : S.SubdivData)

/-- The three cells the subdivision creates. -/
def newCells : Set γ := {d.newVertex, d.newEdge₁, d.newEdge₂}

variable {d}

variable (d)

theorem edge_mem_edgeSet : d.edge ∈ E(S.skel) := d.isLink.edge_mem

theorem newEdge₁_notMem_edgeSet : d.newEdge₁ ∉ E(S.skel) := fun h =>
  d.newEdge₁_notMem (S.mem_cells_of_mem_edgeSet h)

theorem newEdge₂_notMem_edgeSet : d.newEdge₂ ∉ E(S.skel) := fun h =>
  d.newEdge₂_notMem (S.mem_cells_of_mem_edgeSet h)

theorem newEdge₁_notMem_outer : d.newEdge₁ ∉ E(S.outerGraph) := fun h =>
  d.newEdge₁_notMem_edgeSet (S.outerGraph_le.edgeSet_mono h)

theorem newEdge₂_notMem_outer : d.newEdge₂ ∉ E(S.outerGraph) := fun h =>
  d.newEdge₂_notMem_edgeSet (S.outerGraph_le.edgeSet_mono h)

/-- The subdivided skeleton. -/
def skeleton : Graph γ γ :=
  subdivGraph S.skel d.edge d.left d.right d.newVertex d.newEdge₁ d.newEdge₂
    d.newEdge_ne d.newEdge₁_notMem_edgeSet d.newEdge₂_notMem_edgeSet

/-- The subdivided outer cycle. When the subdivided edge is not an outer edge this is the old
outer cycle unchanged (`SubdivData.outer_eq`). -/
def outer : Graph γ γ :=
  subdivGraph S.outerGraph d.edge d.left d.right d.newVertex d.newEdge₁ d.newEdge₂
    d.newEdge_ne d.newEdge₁_notMem_outer d.newEdge₂_notMem_outer

theorem outer_le_skeleton : d.outer ≤ d.skeleton := subdivGraph_mono S.outerGraph_le

@[simp] theorem skeleton_vertexSet : V(d.skeleton) = insert d.newVertex V(S.skel) := by
  ext z
  simp only [skeleton, subdivGraph_vertexSet, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_insert_iff, d.isLink, and_true]
  tauto

@[simp] theorem skeleton_edgeSet :
    E(d.skeleton) = insert d.newEdge₁ (insert d.newEdge₂ (E(S.skel) \ {d.edge})) := by
  ext f
  simp only [skeleton, subdivGraph_edgeSet, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_insert_iff, d.isLink, and_true]
  tauto

theorem skeleton_isLink {f a b : γ} :
    d.skeleton.IsLink f a b ↔
      (S.skel.IsLink f a b ∧ f ≠ d.edge ∧ f ≠ d.newEdge₁ ∧ f ≠ d.newEdge₂) ∨
        (f = d.newEdge₁ ∧ s(a, b) = s(d.left, d.newVertex)) ∨
        (f = d.newEdge₂ ∧ s(a, b) = s(d.newVertex, d.right)) := by
  simp only [skeleton, subdivGraph_isLink, d.isLink, true_and]

/-- **The abstract subcell relation after an edge subdivision.** Read off the blueprint's
update list, in order: the old pairs that involve neither `e` nor a new cell; the reflexive
pairs of the new cells (see the fidelity note in the module docstring); `v ≼ e₁, e₂`; each old
endpoint below its adjacent new edge; and the new cells below exactly the old *strict*
supercells of `e`. -/
def subRel : γ → γ → Prop := fun σ τ =>
  (σ ∉ d.newCells ∧ τ ∉ d.newCells ∧ σ ≠ d.edge ∧ τ ≠ d.edge ∧ S.sub σ τ) ∨
    (σ = τ ∧ σ ∈ d.newCells) ∨
    (σ = d.newVertex ∧ (τ = d.newEdge₁ ∨ τ = d.newEdge₂)) ∨
    (σ = d.left ∧ τ = d.newEdge₁) ∨
    (σ = d.right ∧ τ = d.newEdge₂) ∨
    (σ ∈ d.newCells ∧ τ ≠ d.edge ∧ S.sub d.edge τ)

end SubdivData

open scoped Classical in
/-- **Elementary operation 1: edge subdivision.** The abstract-data update of
`def:generated-structure`, operation 1.

The boundary walks are the orientation-aware replacements carried by `SubdivData`.  They must
arrive as data because an edge list does not determine the direction in which its walk crosses
the subdivided edge; the two incident face boundaries can traverse it in opposite directions. -/
noncomputable def subdivideEdge (S : CellStructure γ) (d : S.SubdivData) : CellStructure γ where
  skel := d.skeleton
  faces := S.faces
  outerGraph := d.outer
  outerGraph_le := d.outer_le_skeleton
  boundary := d.newBoundary
  sub := d.subRel
  finite_vertexSet := by
    rw [d.skeleton_vertexSet]; exact S.finite_vertexSet.insert _
  finite_edgeSet := by
    rw [d.skeleton_edgeSet]
    exact ((S.finite_edgeSet.sdiff).insert _).insert _
  finite_faces := S.finite_faces
  disjoint_vertexSet_edgeSet := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [d.skeleton_vertexSet, Set.mem_insert_iff] at hz
    rw [d.skeleton_edgeSet, Set.mem_insert_iff, Set.mem_insert_iff] at hz'
    rcases hz with rfl | hz
    · rcases hz' with h | h | hz'
      · exact d.newVertex_ne₁ h
      · exact d.newVertex_ne₂ h
      · exact d.newVertex_notMem (S.mem_cells_of_mem_edgeSet hz'.1)
    · rcases hz' with rfl | rfl | hz'
      · exact d.newEdge₁_notMem (S.mem_cells_of_mem_vertexSet hz)
      · exact d.newEdge₂_notMem (S.mem_cells_of_mem_vertexSet hz)
      · exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet hz hz'.1
  disjoint_faces_vertexSet := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [d.skeleton_vertexSet, Set.mem_insert_iff] at hz'
    rcases hz' with rfl | hz'
    · exact d.newVertex_notMem (S.mem_cells_of_mem_faces hz)
    · exact Set.disjoint_left.1 S.disjoint_faces_vertexSet hz hz'
  disjoint_faces_edgeSet := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [d.skeleton_edgeSet, Set.mem_insert_iff, Set.mem_insert_iff] at hz'
    rcases hz' with rfl | rfl | hz'
    · exact d.newEdge₁_notMem (S.mem_cells_of_mem_faces hz)
    · exact d.newEdge₂_notMem (S.mem_cells_of_mem_faces hz)
    · exact Set.disjoint_left.1 S.disjoint_faces_edgeSet hz hz'.1

variable {S : CellStructure γ} (d : S.SubdivData)

@[simp] theorem subdivideEdge_skel : (S.subdivideEdge d).skel = d.skeleton := rfl

@[simp] theorem subdivideEdge_faces : (S.subdivideEdge d).faces = S.faces := rfl

@[simp] theorem subdivideEdge_outerGraph : (S.subdivideEdge d).outerGraph = d.outer := rfl

@[simp] theorem subdivideEdge_sub {σ τ : γ} :
    (S.subdivideEdge d).sub σ τ ↔ d.subRel σ τ := Iff.rfl

/-! ### Elementary operation 2: splitting a 2-cell by an ear

Blueprint, `def:generated-structure`, operation 2: "the 2-cell `R` is replaced by `R₁, R₂`; the
new interior vertices and edges of the ear `P` are added with their incidences along `P` (each
interior vertex a subcell of its two adjacent ear edges, each ear endpoint a subcell of its
adjacent ear edge); the relation `≼_abs` is extended by declaring every cell of the boundary
walk of `Rᵢ`, together with every cell of `P`, a subcell of `Rᵢ`, for `i = 1, 2`; no 2-cell is
declared a subcell of another, and all pairs not involving `R` or the new cells are unchanged."

The ear enters as a *graph* `ear` together with `Graph.IsPathGraph`, rather than as a bare list
of names: the incidences "along `P`" are then `ear.Inc`, and the union `S.skel.union ear` is
the new skeleton with no further bookkeeping. -/

/-- The data of one **2-cell split by an ear**: the split 2-cell, two fresh names for the two
new 2-cells, and the ear — a path graph whose two ends are old vertices and all of whose other
cells are fresh — together with the two boundary paths of the split cell between the ends of
the ear.

`sub_face` is the statement that the two boundary paths carry exactly the cells of the split
2-cell; `paths_meet` that they meet exactly at the two ends of the ear. Both are consequences of
the invariants at the stage being refined, and both are what the blueprint means by "the two
boundary paths between its endpoints".

**`paths_meet` used to read `paths_disjoint`** — that the two paths share no *edge* — and that
is too weak. Two edge-disjoint paths between the same two vertices may still share an interior
vertex: take parallel edges `e₁, f₁ : u — a` and `e₂, f₂ : a — v` and the paths `[e₁, e₂]`,
`[f₁, f₂]`. Every other field holds, and the two realized boundary paths then meet in three
points, so `IsCutPair.inter_eq` — which asks that the two arcs meet exactly at the two cut
points — is **false**, and with it the `isCutPair` field of `SplitData.IsCrosscutSplit`, hence
assertion (i) at the split constructor. The stronger clause is what a producer actually has,
since it picks the two paths as the two arcs of one boundary cycle; `paths_disjoint` below is
recovered from it. Found by the first module that ever built a realization of a split
(`Schoenflies/RealizeSplit.lean`), which had to carry it as a hypothesis. -/
structure SplitData (S : CellStructure γ) where
  /-- The 2-cell being split. -/
  face : γ
  /-- The first new 2-cell, bounded by `path₁` and the ear. -/
  face₁ : γ
  /-- The second new 2-cell, bounded by `path₂` and the ear. -/
  face₂ : γ
  /-- The inserted ear, as an abstract path graph. -/
  ear : Graph γ γ
  /-- One end of the ear. -/
  source : γ
  /-- The other end of the ear. -/
  target : γ
  /-- The ear's own edges, in order. -/
  earWalk : List γ
  /-- The first boundary path of the split 2-cell, from `source` to `target`. -/
  path₁ : List γ
  /-- The second boundary path. -/
  path₂ : List γ
  /-- The ear is a path graph between its two ends. -/
  isPathGraph : ear.IsPathGraph source earWalk target
  /-- The first boundary path really is a path of the skeleton between the ear's ends. -/
  isPath₁ : S.skel.IsPath source path₁ target
  /-- So is the second. -/
  isPath₂ : S.skel.IsPath source path₂ target
  /-- The ear's vertex names and edge names are distinct. -/
  ear_disjoint : Disjoint V(ear) E(ear)
  /-- The two ends of the ear are distinct. -/
  source_ne_target : source ≠ target
  /-- The split cell is a 2-cell. -/
  face_mem : face ∈ S.faces
  /-- The ear meets the old skeleton exactly in its two ends. -/
  vertexSet_inter : V(ear) ∩ V(S.skel) = {source, target}
  /-- Every edge of the ear is a fresh name. -/
  edge_fresh : ∀ ⦃f⦄, f ∈ E(ear) → f ∉ S.cells
  /-- Every interior vertex of the ear is a fresh name. -/
  vertex_fresh : ∀ ⦃z⦄, z ∈ V(ear) → z ≠ source → z ≠ target → z ∉ S.cells
  /-- The first new 2-cell has a fresh name. -/
  face₁_notMem : face₁ ∉ S.cells
  /-- The second new 2-cell has a fresh name. -/
  face₂_notMem : face₂ ∉ S.cells
  /-- The first new 2-cell is not a cell of the ear either. -/
  face₁_notMem_ear : face₁ ∉ V(ear) ∪ E(ear)
  /-- Nor is the second. -/
  face₂_notMem_ear : face₂ ∉ V(ear) ∪ E(ear)
  /-- The two new 2-cells are distinct. -/
  face_ne : face₁ ≠ face₂
  /-- The cells below the split 2-cell are exactly the cells of its two boundary paths. -/
  sub_face : ∀ ⦃σ⦄, S.sub σ face ↔
    σ = face ∨ σ ∈ S.pathCells source path₁ ∪ S.pathCells source path₂
  /-- **The two boundary paths meet exactly at the two ends of the ear.** Not merely that they
  share no edge — see the counterexample in the docstring above. -/
  paths_meet : S.pathCells source path₁ ∩ S.pathCells source path₂ = {source, target}

namespace SplitData

variable {S : CellStructure γ} (d : S.SplitData)

/-- All cells of the ear: its vertices, including its two old ends, and its edges. -/
def earCells : Set γ := V(d.ear) ∪ E(d.ear)

/-- The cells the split creates: the interior cells of the ear, its edges, and the two new
2-cells. The ear's two ends are *not* new — they are old vertices, and the blueprint is
explicit that they are their own parents. -/
def newCells : Set γ := (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) ∪ {d.face₁, d.face₂}

/-- The cells of the first boundary path. -/
def cells₁ : Set γ := S.pathCells d.source d.path₁

/-- The cells of the second boundary path. -/
def cells₂ : Set γ := S.pathCells d.source d.path₂

theorem source_mem_skel : d.source ∈ V(S.skel) := d.isPath₁.left_mem

theorem target_mem_skel : d.target ∈ V(S.skel) := d.isPath₁.right_mem

/-- A vertex of the ear other than its two ends is a fresh name; an end is an old vertex. -/
theorem mem_cells_of_mem_ear_vertexSet {z : γ} (hz : z ∈ V(d.ear)) (h : z ∈ S.cells) :
    z = d.source ∨ z = d.target := by
  by_contra hcon
  push Not at hcon
  exact d.vertex_fresh hz hcon.1 hcon.2 h

variable {d}

variable (d)

theorem disjoint_edgeSet : Disjoint E(S.skel) E(d.ear) :=
  Set.disjoint_left.2 fun _ hz hz' => d.edge_fresh hz' (S.mem_cells_of_mem_edgeSet hz)

/-- The skeleton after the split: the old skeleton with the ear glued in along its two ends. -/
def skeleton : Graph γ γ := S.skel.union d.ear

@[simp] theorem skeleton_vertexSet : V(d.skeleton) = V(S.skel) ∪ V(d.ear) := rfl

@[simp] theorem skeleton_edgeSet : E(d.skeleton) = E(S.skel) ∪ E(d.ear) := rfl

theorem le_skeleton : S.skel ≤ d.skeleton := Graph.left_le_union _ _

theorem finite_ear_vertexSet : V(d.ear).Finite := by
  rw [d.isPathGraph.vertexSet_eq]; exact d.isPathGraph.isWalk.finite_walkVertices

theorem finite_ear_edgeSet : E(d.ear).Finite := by
  rw [d.isPathGraph.edgeSet_eq]; exact d.earWalk.finite_toSet

/-- **The abstract subcell relation after a 2-cell split.** Read off the blueprint's update
list, in order: the old pairs involving neither `R` nor a new cell; the reflexive pairs of the
new cells (see the fidelity note in the module docstring); the incidences along the ear; and
the cells of `P` and of `Bᵢ`, together with `Rᵢ` itself, below `Rᵢ`. No 2-cell is below
another. -/
def subRel : γ → γ → Prop := fun σ τ =>
  (σ ∉ d.newCells ∧ τ ∉ d.newCells ∧ σ ≠ d.face ∧ τ ≠ d.face ∧ S.sub σ τ) ∨
    (σ = τ ∧ σ ∈ d.newCells) ∨
    d.ear.Inc τ σ ∨
    (τ = d.face₁ ∧ (σ = d.face₁ ∨ σ ∈ d.earCells ∨ σ ∈ d.cells₁)) ∨
    (τ = d.face₂ ∧ (σ = d.face₂ ∨ σ ∈ d.earCells ∨ σ ∈ d.cells₂))

end SplitData

open scoped Classical in
/-- **Elementary operation 2: 2-cell splitting by an ear.** The abstract-data update of
`def:generated-structure`, operation 2.

As with `CellStructure.subdivideEdge`, the boundary walks are a raw datum: the two new 2-cells
get the concatenation of their boundary path with the reversed ear, and nothing below reads
the orientation. -/
noncomputable def splitFace (S : CellStructure γ) (d : S.SplitData) : CellStructure γ where
  skel := d.skeleton
  faces := insert d.face₁ (insert d.face₂ (S.faces \ {d.face}))
  outerGraph := S.outerGraph
  outerGraph_le := S.outerGraph_le.trans d.le_skeleton
  boundary F :=
    if F = d.face₁ then d.path₁ ++ d.earWalk.reverse
    else if F = d.face₂ then d.path₂ ++ d.earWalk.reverse
    else S.boundary F
  sub := d.subRel
  finite_vertexSet := S.finite_vertexSet.union d.finite_ear_vertexSet
  finite_edgeSet := S.finite_edgeSet.union d.finite_ear_edgeSet
  finite_faces := ((S.finite_faces.sdiff).insert _).insert _
  disjoint_vertexSet_edgeSet := by
    rw [Set.disjoint_left]
    rintro z (hz | hz) (hz' | hz')
    · exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet hz hz'
    · exact d.edge_fresh hz' (S.mem_cells_of_mem_vertexSet hz)
    · rcases d.mem_cells_of_mem_ear_vertexSet hz (S.mem_cells_of_mem_edgeSet hz') with rfl | rfl
      · exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet d.source_mem_skel hz'
      · exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet d.target_mem_skel hz'
    · exact Set.disjoint_left.1 d.ear_disjoint hz hz'
  disjoint_faces_vertexSet := by
    rw [Set.disjoint_left]
    rintro z hz (hz' | hz')
    · rcases hz with rfl | rfl | ⟨hz, -⟩
      · exact d.face₁_notMem (S.mem_cells_of_mem_vertexSet hz')
      · exact d.face₂_notMem (S.mem_cells_of_mem_vertexSet hz')
      · exact Set.disjoint_left.1 S.disjoint_faces_vertexSet hz hz'
    · rcases hz with rfl | rfl | ⟨hz, -⟩
      · exact d.face₁_notMem_ear (Or.inl hz')
      · exact d.face₂_notMem_ear (Or.inl hz')
      · rcases d.mem_cells_of_mem_ear_vertexSet hz' (S.mem_cells_of_mem_faces hz) with rfl | rfl
        · exact Set.disjoint_left.1 S.disjoint_faces_vertexSet hz d.source_mem_skel
        · exact Set.disjoint_left.1 S.disjoint_faces_vertexSet hz d.target_mem_skel
  disjoint_faces_edgeSet := by
    rw [Set.disjoint_left]
    rintro z hz (hz' | hz')
    · rcases hz with rfl | rfl | ⟨hz, -⟩
      · exact d.face₁_notMem (S.mem_cells_of_mem_edgeSet hz')
      · exact d.face₂_notMem (S.mem_cells_of_mem_edgeSet hz')
      · exact Set.disjoint_left.1 S.disjoint_faces_edgeSet hz hz'
    · rcases hz with rfl | rfl | ⟨hz, -⟩
      · exact d.face₁_notMem_ear (Or.inr hz')
      · exact d.face₂_notMem_ear (Or.inr hz')
      · exact d.edge_fresh hz' (S.mem_cells_of_mem_faces hz)

variable {S : CellStructure γ} (c : S.SplitData)

@[simp] theorem splitFace_skel : (S.splitFace c).skel = c.skeleton := rfl

@[simp] theorem splitFace_faces :
    (S.splitFace c).faces = insert c.face₁ (insert c.face₂ (S.faces \ {c.face})) := rfl

@[simp] theorem splitFace_outerGraph : (S.splitFace c).outerGraph = S.outerGraph := rfl

@[simp] theorem splitFace_sub {σ τ : γ} : (S.splitFace c).sub σ τ ↔ c.subRel σ τ := Iff.rfl

end CellStructure

/-! ### Generated matched cell structures -/

/-- **`def:generated-structure`**: the closure of a base structure under the two elementary
operations.

The base is a *parameter*. The blueprint's base is the initial matched cellulation of
`prop:initial-pair`, which is being built elsewhere; parameterising over it makes every theorem
below read "the invariants propagate", with the base case supplied by the producer of `S₀`.

`rem:intermediate-disconnection` is honoured by omission: the realizations of a generated
structure are required only to be weakly admissible — connectedness of the open nonboundary
part is waived — and nothing in this file, or in any statement about
`GeneratedStructure`, mentions that connectedness. -/
inductive GeneratedStructure (S₀ : CellStructure γ) : CellStructure γ → Prop
  /-- The base structure is generated, by the empty sequence of operations. -/
  | base : GeneratedStructure S₀ S₀
  /-- Subdividing an edge of a generated structure gives a generated structure. -/
  | subdivideEdge {S : CellStructure γ} (h : GeneratedStructure S₀ S) (d : S.SubdivData) :
      GeneratedStructure S₀ (S.subdivideEdge d)
  /-- Splitting a 2-cell of a generated structure by an ear gives a generated structure. -/
  | splitFace {S : CellStructure γ} (h : GeneratedStructure S₀ S) (d : S.SplitData) :
      GeneratedStructure S₀ (S.splitFace d)

namespace CellStructure

/-! ### The combinatorial invariants

Assertions (iii), (v) and (vi) of `lem:cellulation-invariants`, together with the abstract form
of (viii) and the bookkeeping facts about `≼_abs` that the blueprint's proof uses without
comment (the relation relates cells to cells, it is reflexive, and a vertex is below each edge
it bounds). They are bundled because the induction propagates them together: the preservation
proof of each one reads the others at the previous stage. -/

/-- The combinatorial invariants of `lem:cellulation-invariants`. -/
structure CombInvariants (S : CellStructure γ) : Prop where
  /-- `≼_abs` relates cells to cells. -/
  sub_mem_left : ∀ ⦃σ τ⦄, S.sub σ τ → σ ∈ S.cells
  /-- `≼_abs` relates cells to cells. -/
  sub_mem_right : ∀ ⦃σ τ⦄, S.sub σ τ → τ ∈ S.cells
  /-- `≼_abs` is reflexive on cells. The blueprint declares the reflexive pairs in the base
  relation and preserves them under both constructors. -/
  sub_refl : ∀ ⦃σ⦄, σ ∈ S.cells → S.sub σ σ
  /-- Each endpoint of an edge is a subcell of it. -/
  sub_isLink : ∀ ⦃f a b⦄, S.skel.IsLink f a b → S.sub a f
  /-- **Abstract (viii)**: no 2-cell is a subcell of anything but itself. -/
  face_maximal : ∀ ⦃F τ⦄, F ∈ S.faces → S.sub F τ → τ = F
  /-- **(iii)**: every 2-cell boundary contains a nonboundary edge. -/
  nonboundary_edge : ∀ ⦃F⦄, F ∈ S.faces → ∃ f ∈ E(S.skel), f ∉ E(S.outerGraph) ∧ S.sub f F
  /-- **(v)**: every cell is a subcell of at least one 2-cell. -/
  mem_face : ∀ ⦃σ⦄, σ ∈ S.cells → ∃ F ∈ S.faces, S.sub σ F
  /-- **(vi)**: every outer edge is a subcell of exactly one 2-cell. -/
  outerEdge_unique : OuterEdgeUniqueFace S

/-! ### Edge subdivision preserves the combinatorial invariants -/

/-! ### A 2-cell split preserves the combinatorial invariants -/

/-! ### The invariants at every stage -/

/-! ### The geometric assertions

Assertion (i) is the only geometric input the rest need: (ii), (viii) and (ix) follow from it
formally, with no further topology beyond "a nonempty open set contained in a closure meets the
set". That is why they are stated here for an arbitrary realization satisfying (i), rather than
by induction: the induction is entirely in (i) and (vii), and those are the standing gap of this
module. -/

namespace Realization

/-- **Assertion (i)** of `lem:cellulation-invariants`, for one realization: the open cells are
nonempty and pairwise disjoint, they cover the closed domain `D`, and every closed cell is the
union of its open subcells — the last clause read against the *abstract* relation `≼_abs`,
which is what makes (ix) a formal consequence. -/
structure IsCellDecomposition {S : CellStructure γ} (R : S.Realization) (D : Set Plane) :
    Prop where
  /-- Every open cell is nonempty. -/
  nonempty : ∀ ⦃σ⦄, σ ∈ S.cells → (R.cell σ).Nonempty
  /-- Distinct open cells are disjoint. -/
  disjoint : ∀ ⦃σ τ⦄, σ ∈ S.cells → τ ∈ S.cells → σ ≠ τ → Disjoint (R.cell σ) (R.cell τ)
  /-- The open cells cover the closed domain. -/
  iUnion_eq : ⋃ σ ∈ S.cells, R.cell σ = D
  /-- Every closed cell is the union of its open subcells. -/
  closure_eq : ∀ ⦃τ⦄, τ ∈ S.cells →
    closure (R.cell τ) = ⋃ σ ∈ {σ | σ ∈ S.cells ∧ S.sub σ τ}, R.cell σ

end Realization

/-! ### Assertion (i) is preserved by an edge subdivision

The induction step of (i) over the first constructor. It relates two realizations of two
different structures, so it needs a name for "`R'` refines `R` along `d`": that is
`SubdivData.IsRefinement`, whose fields are exactly the blueprint's sentence "the corresponding
point is inserted into the corresponding edge using the edge parametrization", read as a
statement about the resulting open cells and their closures. -/

end CellStructure

/-! ### The geometric content of one 2-cell split

`thm:general-crosscut` is what the induction step of assertions (i) and (vii) applies at each
split. The two hypotheses it still carries on `main` — `thm:jordan` and `HasArcCollars` — are
threaded through verbatim; both are being discharged elsewhere. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryCycles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cyclic boundaries of abstract 2-cells

The abstract `CellStructure.boundary` field is only a list of edge names.  The finite-transfer
construction needs the stronger invariant that each face boundary is a simple cycle and that
its vertices and edges are exactly the strict subcells of the face.  This module packages that
invariant in the representation already used by `Graph.IsLongCycle`.

The distinguished edge `edge` closes the simple detour `walk`.  The list `edge :: walk` is a
closed walk when started at `target`: it crosses the distinguished edge backwards to `source`
and follows the detour back to `target`.  Two-edge cycles are allowed: an ear split can
legitimately create a digon even when the initial outer cycle has at least three vertices.
Stating the carrier clause with
`CellStructure.pathCells` makes it directly comparable with `SplitData.sub_face`.

## Blueprint

* `Schoenflies.CellStructure.FaceCycle`, `BoundaryCycles` — the maintained form of the
  sentence in `lem:cellulation-invariants` that the cells below every 2-cell form its boundary
  cycle.
-/

open Set
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*}

/-- A face boundary is a simple cycle, and its carrier is exactly the face's strict subcells.
This is data rather than a proposition because the finite-transfer step extracts its named
edge, vertices and complementary path. -/
structure FaceCycle (S : CellStructure γ) (F : γ) where
  /-- The indexed cell is a face of the structure. -/
  face_mem : F ∈ S.faces
  /-- A distinguished edge of the boundary cycle. -/
  edge : γ
  /-- One end of the distinguished edge and the source of the complementary path. -/
  source : γ
  /-- The other end, at which the displayed closed boundary list starts. -/
  target : γ
  /-- The complementary path from `source` to `target`. -/
  walk : List γ
  /-- The raw boundary datum is the distinguished edge followed by the complementary path. -/
  boundary_eq : S.boundary F = edge :: walk
  /-- The distinguished edge and complementary path form a simple cycle. -/
  isCycle : S.skel.IsCycleThrough edge source target walk
  /-- The face itself and the cells of the cycle are exactly the cells below the face. -/
  sub_face : ∀ ⦃σ⦄, S.sub σ F ↔
    σ = F ∨ σ ∈ S.pathCells target (edge :: walk)

/-- Every 2-cell of an abstract structure admits simple boundary-cycle data.  This is a
proposition so that membership proofs remain proof-irrelevant; `BoundaryCycles.faceCycle`
chooses the exported data once and for all. -/
structure BoundaryCycles (S : CellStructure γ) : Prop where
  /-- Existence of boundary-cycle data for each face. -/
  cycle : ∀ F, F ∈ S.faces → Nonempty (S.FaceCycle F)

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolygonalCarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_pair _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polygonal connectedness over a carrier

`Schoenflies.exists_poly_of_isPreconnected` joins two points of an *open* connected subset
of the plane by a polygonal path. The redrawing argument needs the same conclusion for a
carrier that is **not** open in the plane: the ambient set there is the plane minus finitely
many open squares, and the basic neighbourhood of a point on a square's boundary is a
half-disk or a three-quarter disk rather than a ball.

This module restates the clopen argument over an arbitrary carrier `C`. The only hypothesis
on `C` is that it is *locally polygonally connected*: every point has a relatively open
neighbourhood all of whose points it reaches by a polygonal path inside `C`. Openness of `C`
is used nowhere; the ball of the classical proof appears only in
`isLocallyPolyConnected_of_isOpen`, which is what recovers the old statement.

## Blueprint

Brick B6 of `lem:polygonal-redrawing` (H6): polygonal connectivity one level up.

* `PolyReaches` — "joined by a polygonal path inside `C`", as an inductive relation.
  **Note for the integrator:** `Schoenflies/LocallyPolygonal.lean` is being written
  concurrently and defines a relation of the same meaning; the two want unifying.
* `IsLocallyPolyConnected` — the hypothesis replacing openness.
* `PolyReaches.of_isPreconnected` — Lemma 1.1 (polygonal connectedness) over a carrier.
* `exists_poly_of_isPreconnected'` — the old `exists_poly_of_isPreconnected` re-derived from
  it, verbatim; the `example` below it is a machine check that the statements agree.
-/

open Metric Set

namespace Schoenflies

variable {C D : Set Plane} {x y z : Plane}

/-! ### Joined by a polygonal path inside a carrier -/

/-- `PolyReaches C x y`: there is a polygonal path from `x` to `y` all of whose segments lie
in `C`. Built at the far end — a path is extended by one segment at a time — because that is
the shape both halves of the clopen argument use. `refl` carries `x ∈ C` so that a constant
path witnesses membership, matching `poly [x] = {x}`. -/
inductive PolyReaches (C : Set Plane) (x : Plane) : Plane → Prop
  | refl (hx : x ∈ C) : PolyReaches C x x
  | step {y z : Plane} (h : PolyReaches C x y) (hseg : segment ℝ y z ⊆ C) : PolyReaches C x z

namespace PolyReaches

/-- A single segment inside `C` is already a polygonal path. -/
theorem of_segment (hseg : segment ℝ x y ⊆ C) : PolyReaches C x y :=
  (PolyReaches.refl (hseg (left_mem_segment ℝ x y))).step hseg

theorem trans (h₁ : PolyReaches C x y) (h₂ : PolyReaches C y z) : PolyReaches C x z := by
  induction h₂ with
  | refl _ => exact h₁
  | step _ hseg ih => exact ih.step hseg

/-- Symmetry: a path is run backwards one segment at a time, each reversed segment being the
same set. -/
theorem symm (h : PolyReaches C x y) : PolyReaches C y x := by
  induction h with
  | refl hx => exact PolyReaches.refl hx
  | @step y z _ hseg ih =>
    -- The last segment, reversed, joins `z` back to `y`; then follow the shorter path back.
    exact (of_segment (by rwa [segment_symm])).trans ih

theorem mono (hCD : C ⊆ D) (h : PolyReaches C x y) : PolyReaches D x y := by
  induction h with
  | refl hx => exact PolyReaches.refl (hCD hx)
  | step _ hseg ih => exact ih.step (hseg.trans hCD)

end PolyReaches

/-! ### The relation and the vertex-list representation agree -/

/-- A polygonal path in the sense of `PolyReaches` yields a vertex list with the carrier of
its polygon inside `C`. This is `poly_concat` used once per `step`. -/
theorem PolyReaches.exists_poly (h : PolyReaches C x y) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y := by
  induction h with
  | refl hx => exact ⟨[x], by simp, by simpa using hx, rfl, rfl⟩
  | @step _ z _ hseg ih =>
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := ih
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub hseg
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp

/-- Conversely a vertex list whose polygon lies in `C` joins its ends. -/
theorem polyReaches_of_poly_subset : ∀ {vs : List Plane} (hne : vs ≠ []), poly vs ⊆ C →
    PolyReaches C (vs.head hne) (vs.getLast hne)
  | [], hne, _ => absurd rfl hne
  | [v], _, hsub => PolyReaches.refl (hsub (by simp))
  | u :: v :: rest, _, hsub => by
    rw [poly_cons_cons] at hsub
    have hstep : PolyReaches C u v :=
      PolyReaches.of_segment (subset_union_left.trans hsub)
    have hrest := polyReaches_of_poly_subset (List.cons_ne_nil v rest)
      (subset_union_right.trans hsub)
    rw [List.getLast_cons (List.cons_ne_nil v rest)]
    exact hstep.trans hrest

/-! ### Local polygonal connectedness -/

/-- `C` is locally polygonally connected when every point of `C` has a relatively open
neighbourhood in `C` each of whose points it reaches by a polygonal path inside `C`.

The neighbourhood is presented as `V ∩ C` for an ambient open `V`, which is exactly what a
relatively open neighbourhood is; the paths are only required to stay inside `C`, not inside
the neighbourhood, since that is all the clopen argument uses and it is the weaker demand on
a producer. Ball, half-disk and three-quarter disk all qualify. -/
def IsLocallyPolyConnected (C : Set Plane) : Prop :=
  ∀ w ∈ C, ∃ V : Set Plane, IsOpen V ∧ w ∈ V ∧ ∀ z ∈ V ∩ C, PolyReaches C w z

/-- The relative-openness step, stated once because the clopen argument uses it twice — for
the reachable set and, run backwards, for its relative complement.

A subset of `C` closed under "reach one more point of `C` by a polygonal path" is relatively
open in `C`. The witness is the union of all ambient open sets that are polygonally attached
to a point of `S`; no choice is needed to assemble it. -/
theorem isRelOpen_of_polyReaches_stable (hloc : IsLocallyPolyConnected C) {S : Set Plane}
    (hS : S ⊆ C) (hstable : ∀ w ∈ S, ∀ z ∈ C, PolyReaches C w z → z ∈ S) :
    ∃ U : Set Plane, IsOpen U ∧ S ⊆ U ∧ U ∩ C ⊆ S := by
  refine ⟨⋃₀ {V : Set Plane | IsOpen V ∧ ∃ w ∈ S, ∀ z ∈ V ∩ C, PolyReaches C w z},
    isOpen_sUnion fun V hV => hV.1, fun w hw => ?_, ?_⟩
  · obtain ⟨V, hVopen, hwV, hVreach⟩ := hloc w (hS hw)
    exact ⟨V, ⟨hVopen, w, hw, hVreach⟩, hwV⟩
  · rintro z ⟨⟨V, ⟨_, w, hwS, hVreach⟩, hzV⟩, hzC⟩
    exact hstable w hwS z hzC (hVreach z ⟨hzV, hzC⟩)

/-! ### The theorem -/

/-- Lemma 1.1 (polygonal connectedness) over a carrier: in a relatively connected, locally
polygonally connected set, any two points are joined by a polygonal path inside the set.

The proof is the clopen argument. The points reachable from `x` are relatively open in `C`,
and so are the unreachable ones — the same lemma, since "unreachable" is stable under
reaching too, by symmetry. `IsPreconnected C` then forbids the split. -/
theorem PolyReaches.of_isPreconnected (hloc : IsLocallyPolyConnected C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) : PolyReaches C x y := by
  by_contra hxy
  set R : Set Plane := {w | w ∈ C ∧ PolyReaches C x w} with hRdef
  obtain ⟨U, hUopen, hRU, hUR⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := R) (fun _ hw => hw.1)
      (fun _ hw _ hzC hreach => ⟨hzC, hw.2.trans hreach⟩)
  obtain ⟨U', hU'open, hRU', hU'R⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := C \ R) (fun _ hw => hw.1)
      (fun w hw z hzC hreach => ⟨hzC, fun hzR => hw.2 ⟨hw.1, hzR.2.trans hreach.symm⟩⟩)
  obtain ⟨w, hwC, hwU, hwU'⟩ := hconn U U' hUopen hU'open
    (fun v hv => (em (v ∈ R)).imp (fun h => hRU h) (fun h => hRU' ⟨hv, h⟩))
    ⟨x, hx, hRU ⟨hx, PolyReaches.refl hx⟩⟩
    ⟨y, hy, hRU' ⟨hy, fun h => hxy h.2⟩⟩
  exact (hU'R ⟨hwU', hwC⟩).2 (hUR ⟨hwU, hwC⟩)

/-! ### Producers of the hypothesis -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolyLocal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_pair _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Local polygonal connectedness, in the form brick B7 consumes

`Schoenflies/LocallyPolygonal.lean` (brick B5) and `Schoenflies/PolygonalCarrier.lean`
(brick B6) were written independently and each carries its own "joined by a polygonal path
inside a set" relation — `PolyConnIn` as an existential over vertex lists, `PolyReaches` as
an inductive relation — with its own local form. This module makes them one, and then fixes
the shape problem that stops B5 from feeding B7.

## The shape problem

Both local forms ask only that the connecting path lie in `S`:

```
IsLocallyPolyConnAt S p  :  ∃ U open ∋ p, ∀ x y ∈ U ∩ S, PolyConnIn S x y
IsLocallyPolyConnected C :  ∀ w ∈ C, ∃ V open ∋ w, ∀ z ∈ V ∩ C, PolyReaches C w z
```

That is enough for B6 — the clopen argument only needs *some* path — but it is a property
with **no local content whatsoever**: any polygonally connected `S` satisfies it with
`U = univ`. In particular it does not survive intersection with an open set, and that is
exactly what B7 needs: `U_e` is a component of a relatively open piece of `M`, and a
replacement arc has to stay inside the thin tube, not merely inside `M`.

The fix is `IsLocallyPolyConnAt'`: *arbitrarily small* neighbourhoods `U` of `p` such that
any two points of `U ∩ S` are joined **inside `U ∩ S`**. B5's proof already produces this —
its paths are two segments inside convex pieces of the small square about `p`, and the
square's radius may be shrunk freely — so nothing geometric is lost, only misstated.
`isLocallyPolyConn'_compl_openSquare` and `isLocallyPolyConn'_compl_biUnion` are B5 in the
strengthened form, and `IsLocallyPolyConn'.weaken` recovers the original statements.

## Blueprint

Brick B5 ↔ brick B6 of `lem:polygonal-redrawing` (H6), and the interface B7 uses.

* `polyConnIn_iff_polyReaches` — the two relations agree.
* `IsLocallyPolyConn.isLocallyPolyConnected`, `IsLocallyPolyConnected.isLocallyPolyConn` —
  the two weak local forms agree, so B5 as originally stated does feed B6.
* `IsLocallyPolyConnAt'`, `IsLocallyPolyConn'` — the strengthened local form.
* `isLocallyPolyConnAt'_of_convex_cover` — the strengthened star lemma: a square about `p`
  cut by convex pieces, each of which contains `p` as soon as it is nonempty.
* `isLocallyPolyConnAt'_compl_openSquare`, `isLocallyPolyConn'_compl_biUnion` — **brick B5**,
  strengthened.
* `IsLocallyPolyConn'.inter_isOpen` — shrinkability: a relatively open piece of a locally
  polygonally connected set is locally polygonally connected.
* `IsRelOpenIn`, `isRelOpenIn_connectedComponentIn` — components of relatively open subsets
  are relatively open, the fact B7 quotes for `U_e`.
* `polyReaches_of_isPreconnected_of_isRelOpenIn`, `polyReaches_connectedComponentIn` — the
  payoff: two points of a connected relatively open piece are joined *inside that piece*.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {S T A B C W : Set Plane} {p x y z : Plane}

/-! ### The two relations agree

`PolyReaches.exists_poly` and `polyReaches_of_poly_subset` are both on `main`; this is the
one-line packaging that lets a producer of either relation serve a consumer of the other. -/

/-- The vertex-list relation of `LocallyPolygonal.lean` and the inductive relation of
`PolygonalCarrier.lean` are the same relation. -/
theorem polyConnIn_iff_polyReaches : PolyConnIn S x y ↔ PolyReaches S x y := by
  constructor
  · rintro ⟨vs, hne, hsub, hhead, hlast⟩
    have h := polyReaches_of_poly_subset hne hsub
    rwa [hhead, hlast] at h
  · intro h
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := h.exists_poly
    exact ⟨vs, hne, hsub, hhead, hlast⟩

alias ⟨PolyConnIn.polyReaches, PolyReaches.polyConnIn⟩ := polyConnIn_iff_polyReaches

/-! ### The two weak local forms agree

`IsLocallyPolyConn` quantifies over *pairs* of points of the neighbourhood,
`IsLocallyPolyConnected` only over paths *from the centre*; symmetry and transitivity of the
relation make the two equivalent. -/

/-- Brick B5's conclusion, read as brick B6's hypothesis. -/
theorem IsLocallyPolyConn.isLocallyPolyConnected (h : IsLocallyPolyConn S) :
    IsLocallyPolyConnected S := by
  intro w hw
  obtain ⟨U, hU, hwU, hconn⟩ := h w hw
  exact ⟨U, hU, hwU, fun z hz => (hconn w ⟨hwU, hw⟩ z hz).polyReaches⟩

/-! ### Squares are a neighbourhood basis

B5 builds its neighbourhoods as axis-parallel squares, and the strengthened local form needs
them arbitrarily small inside a given open set. -/

namespace Plane

/-- A square of half a radius sits inside the ball of that radius, because `√2 < 2`. The open
counterpart of `Plane.closedSquare_subset_ball`, restated here so that this module does not
have to import the graph layer. No sign condition on the radius: for `ε ≤ 0` the square is
already empty. -/
theorem openSquare_subset_ball (p : Plane) (ε : ℝ) : openSquare p (ε / 2) ⊆ ball p ε := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x p < ε / 2 := hx
  have hnorm : ‖x - p‖ ≤ Real.sqrt 2 * supDist x p := norm_le_sqrt_two_mul_supNorm _
  rw [mem_ball, dist_eq_norm]
  nlinarith [supDist_nonneg x p]

/-- Inside any open set around `p` there is a square about `p`, of radius at most any
prescribed positive bound. -/
theorem exists_openSquare_subset {W : Set Plane} {p : Plane} (hW : IsOpen W) (hp : p ∈ W)
    {s₀ : ℝ} (hs₀ : 0 < s₀) : ∃ s, 0 < s ∧ s ≤ s₀ ∧ openSquare p s ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW p hp
  exact ⟨min s₀ (ε / 2), lt_min hs₀ (by linarith), min_le_left _ _,
    (openSquare_mono (min_le_right _ _)).trans ((openSquare_subset_ball p ε).trans hball)⟩

end Plane

/-! ### The strengthened local form -/

/-- `S` is polygonally connected near `p` **inside arbitrarily small neighbourhoods**: for
every open `W` containing `p` there is an open `U ⊆ W` containing `p` such that any two points
of `U ∩ S` are joined by a polygonal path lying in `U ∩ S`.

Two strengthenings over `IsLocallyPolyConnAt`, and both are needed by brick B7. The path is
confined to the neighbourhood, not merely to `S`, because a replacement arc has to stay in its
tube; and the neighbourhoods run through a basis at `p`, because otherwise the property does
not survive intersecting `S` with an open set (`IsLocallyPolyConn'.inter_isOpen`). -/
def IsLocallyPolyConnAt' (S : Set Plane) (p : Plane) : Prop :=
  ∀ W : Set Plane, IsOpen W → p ∈ W →
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyReaches (U ∩ S) x y

/-- `S` is locally polygonally connected in the strengthened sense. -/
def IsLocallyPolyConn' (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt' S p

theorem IsLocallyPolyConnAt'.weaken (h : IsLocallyPolyConnAt' S p) :
    IsLocallyPolyConnAt S p := by
  obtain ⟨U, hU, hpU, -, hpath⟩ := h univ isOpen_univ (mem_univ p)
  exact ⟨U, hU, hpU, fun x hx y hy => ((hpath x hx y hy).mono inter_subset_right).polyConnIn⟩

/-- The strengthened form implies the original brick B5 statement, so nothing is lost by
replacing one with the other. -/
theorem IsLocallyPolyConn'.weaken (h : IsLocallyPolyConn' S) : IsLocallyPolyConn S :=
  fun p hp => (h p hp).weaken

/-- What brick B6 consumes. -/
theorem IsLocallyPolyConn'.isLocallyPolyConnected (h : IsLocallyPolyConn' S) :
    IsLocallyPolyConnected S := h.weaken.isLocallyPolyConnected

/-- The property is local: only the trace of `S` on a neighbourhood of `p` matters. This is
what reduces "finitely many squares" to "one square". -/
theorem IsLocallyPolyConnAt'.congr_nhds {V : Set Plane} (h : IsLocallyPolyConnAt' T p)
    (hV : IsOpen V) (hpV : p ∈ V) (heq : S ∩ V = T ∩ V) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ V) (hW.inter hV) ⟨hpW, hpV⟩
  have hUV : U ⊆ V := hUsub.trans inter_subset_right
  have hUST : U ∩ S = U ∩ T := by
    ext x
    constructor
    · rintro ⟨hxU, hxS⟩
      exact ⟨hxU, (heq.subset ⟨hxS, hUV hxU⟩).1⟩
    · rintro ⟨hxU, hxT⟩
      exact ⟨hxU, (heq.symm.subset ⟨hxT, hUV hxU⟩).1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_left, ?_⟩
  rw [hUST]
  exact hpath

/-- A neighbourhood of `p` already inside `S` settles the point: shrink it to a square, which
is convex, so a single segment joins any two of its points. -/
theorem isLocallyPolyConnAt'_of_nbhd_subset {V : Set Plane} (hV : IsOpen V) (hpV : p ∈ V)
    (hVS : V ⊆ S) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, -, hsub⟩ := Plane.exists_openSquare_subset (hV.inter hW) ⟨hpV, hpW⟩ one_pos
  refine ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs,
    hsub.trans inter_subset_right, fun x hx y hy => PolyReaches.of_segment ?_⟩
  exact ((convex_openSquare p s).segment_subset hx.1 hy.1).trans
    fun w hw => ⟨hw, hVS (hsub hw).1⟩

/-- **The strengthened star lemma**, and the whole geometric content of brick B5's three
shapes. Suppose that inside one square about `p` the trace of `S` is covered by convex sets
`H i`, that each `H i` meets that square only inside `S`, and that each `H i` which meets the
square contains `p`. Then `S` is locally polygonally connected at `p` in the strengthened
sense.

Two points of a small square about `p` are then joined by two segments through `p`, each
inside one convex piece of that *small* square — which is why the path never leaves the
neighbourhood. No piece is required to be nonempty and none is named, so the disk, the
half-disk and the three-quarter disk are all this statement. -/
theorem isLocallyPolyConnAt'_of_convex_cover {ι : Type*} {H : ι → Set Plane} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hconv : ∀ i, Convex ℝ (H i))
    (hsub : ∀ i, openSquare p s₀ ∩ H i ⊆ S)
    (hcover : openSquare p s₀ ∩ S ⊆ ⋃ i, H i)
    (hstar : ∀ i, ∀ z ∈ openSquare p s₀ ∩ H i, p ∈ H i) :
    IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, hss₀, hsW⟩ := Plane.exists_openSquare_subset hW hpW hs₀
  have hmono : openSquare p s ⊆ openSquare p s₀ := openSquare_mono hss₀
  have hpiece : ∀ i, openSquare p s ∩ H i ⊆ openSquare p s ∩ S :=
    fun i _ hx => ⟨hx.1, hsub i ⟨hmono hx.1, hx.2⟩⟩
  -- Every point of the small relative square is joined to the centre by one segment.
  have hto : ∀ x ∈ openSquare p s ∩ S, PolyReaches (openSquare p s ∩ S) x p := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover ⟨hmono hx.1, hx.2⟩)
    refine PolyReaches.of_segment (Subset.trans ?_ (hpiece i))
    exact ((convex_openSquare p s).inter (hconv i)).segment_subset ⟨hx.1, hxi⟩
      ⟨mem_openSquare_self hs, hstar i x ⟨hmono hx.1, hxi⟩⟩
  exact ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs, hsW,
    fun x hx y hy => (hto x hx).trans (hto y hy).symm⟩

/-! ### Brick B5, strengthened

The two theorems of `LocallyPolygonal.lean`, reproved in the strengthened form. The geometry
is unchanged — `Plane.exists_radius_sides` still does all the work — because the pieces the
old proof used were already inside the neighbourhood; only the statement moves. -/

/-- **The one-square case of brick B5, strengthened.** The complement of an open axis-parallel
square is polygonally connected near every point of the plane, by paths confined to the
neighbourhood. -/
theorem isLocallyPolyConnAt'_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt' (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt'_of_convex_cover
    (H := fun ib : Fin 2 × Bool => sideHalfPlane c r ib.1 ib.2) hs
    (fun ib => convex_sideHalfPlane c r ib.1 ib.2)
    (fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2))
    (fun x hx => compl_openSquare_subset_iUnion c r hx.2)
    (fun ib z hz => (hstar ib z hz).2)

/-- **Brick B5, strengthened.** The plane minus finitely many open axis-parallel squares whose
closed squares are pairwise disjoint is locally polygonally connected, with the connecting
paths confined to the neighbourhood.

The two cases are unchanged. Away from all the closed squares a small square about `p` lies
inside `M` outright. Otherwise `p` lies in exactly one closed square, and a small enough square
about `p` misses all the others, so near `p` the set `M` *is* the complement of that one open
square — which is what `IsLocallyPolyConnAt'.congr_nhds` says suffices. -/
theorem isLocallyPolyConn'_compl_biUnion {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn' ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) := by
  intro p _
  -- The room between `p` and a square it is outside of, as a radius bound.
  have room : ∀ c : Plane, ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ Q, p ∈ closedSquare c₀ (ρ c₀)
  · -- `p` is in the closed square about `c₀`, hence outside every other closed square.
    obtain ⟨c₀, hc₀Q, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ Q \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcQ, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀Q c hcQ fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite (hQ.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    refine (isLocallyPolyConnAt'_compl_openSquare c₀ (ρ c₀) p).congr_nhds
      (isOpen_openSquare p s) (mem_openSquare_self hs) ?_
    ext x
    constructor
    · rintro ⟨hxM, hxU⟩
      exact ⟨fun hcon => hxM (mem_biUnion hc₀Q hcon), hxU⟩
    · rintro ⟨hx₀, hxU⟩
      refine ⟨fun hcon => ?_, hxU⟩
      obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c s (hsle c ⟨hcQ, hcne⟩) x hxU hxc
  · -- `p` is outside every closed square, so a small square about `p` lies wholly in `M`.
    push Not at hnear
    have hfar : ∀ c ∈ Q, 0 < supDist p c - ρ c := by
      intro c hcQ
      have := hnear c hcQ
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hQ (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt'_of_nbhd_subset (isOpen_openSquare p s) (mem_openSquare_self hs)
      fun x hx hcon => ?_
    obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c s (hsle c hcQ) x hx hxc

/-! ### Shrinkability

The point of the strengthening. `IsLocallyPolyConn` does **not** have this property: it holds
for any polygonally connected `S` with `U = univ`, and the comb space — the segments
`{0} × [0,1]`, `{1/n} × [0,1]` and `[0,1] × {0}` — is polygonally connected while its
intersection with a thin open strip about `y = 1` is not locally polygonally connected at
`(0,1)`. -/

/-- **Shrinkability.** A relatively open piece of a locally polygonally connected set is
locally polygonally connected. Taking the neighbourhood inside `W` is what makes this work,
and it is the reason `IsLocallyPolyConnAt'` quantifies over all open `W ∋ p`. -/
theorem IsLocallyPolyConnAt'.inter_isOpen (h : IsLocallyPolyConnAt' S p) (hW : IsOpen W)
    (hpW : p ∈ W) : IsLocallyPolyConnAt' (S ∩ W) p := by
  intro W' hW' hpW'
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ W') (hW.inter hW') ⟨hpW, hpW'⟩
  have hUW : U ⊆ W := hUsub.trans inter_subset_left
  have hUS : U ∩ (S ∩ W) = U ∩ S :=
    Subset.antisymm (fun _ hx => ⟨hx.1, hx.2.1⟩) fun _ hx => ⟨hx.1, hx.2, hUW hx.1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_right, ?_⟩
  rw [hUS]
  exact hpath

theorem IsLocallyPolyConn'.inter_isOpen (h : IsLocallyPolyConn' S) (hW : IsOpen W) :
    IsLocallyPolyConn' (S ∩ W) :=
  fun _ hp => (h _ hp.1).inter_isOpen hW hp.2

/-! ### Relatively open subsets and their components -/

/-- `A` is relatively open in `S`: cut out of `S` by an ambient open set. -/
def IsRelOpenIn (S A : Set Plane) : Prop := ∃ W : Set Plane, IsOpen W ∧ A = S ∩ W

/-- The shape `isRelOpen_of_polyReaches_stable` delivers, read as relative openness. -/
theorem isRelOpenIn_of_exists (hAS : A ⊆ S) (h : ∃ U : Set Plane, IsOpen U ∧ A ⊆ U ∧ U ∩ S ⊆ A) :
    IsRelOpenIn S A := by
  obtain ⟨U, hU, hAU, hUA⟩ := h
  exact ⟨U, hU, Subset.antisymm (fun _ hx => ⟨hAS hx, hAU hx⟩) fun _ hx => hUA ⟨hx.2, hx.1⟩⟩

/-- Relative openness is transitive, which is how a component of a relatively open piece is
seen to be relatively open in the ambient set. -/
theorem IsRelOpenIn.trans (hA : IsRelOpenIn S A) (hB : IsRelOpenIn A B) : IsRelOpenIn S B := by
  obtain ⟨W, hW, rfl⟩ := hA
  obtain ⟨W', hW', rfl⟩ := hB
  exact ⟨W ∩ W', hW.inter hW', by rw [inter_assoc]⟩

/-- Shrinkability, phrased for a relatively open piece. -/
theorem IsLocallyPolyConn'.of_isRelOpenIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A) :
    IsLocallyPolyConn' A := by
  obtain ⟨W, hW, rfl⟩ := hA
  exact h.inter_isOpen hW

/-- **Components of relatively open subsets are relatively open.** For `S` locally polygonally
connected and `A` relatively open in `S`, each connected component of `A` is relatively open
in `S`.

The proof is `isRelOpen_of_polyReaches_stable`: a polygonal path inside `A` is a connected
subset of `A`, so it cannot leave the component it starts in, which is exactly the stability
that lemma asks for. -/
theorem isRelOpenIn_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsRelOpenIn S (connectedComponentIn A x) := by
  refine hA.trans (isRelOpenIn_of_exists (connectedComponentIn_subset A x) ?_)
  refine isRelOpen_of_polyReaches_stable (h.of_isRelOpenIn hA).isLocallyPolyConnected
    (connectedComponentIn_subset A x) fun w hw z _ hreach => ?_
  -- The polygon carrying the path is connected, lies in `A` and starts at `w`.
  obtain ⟨vs, hne, hsubA, hhead, hlast⟩ := hreach.exists_poly
  have hpoly : poly vs ⊆ connectedComponentIn A x := by
    rw [connectedComponentIn_eq hw]
    exact (isConnected_poly hne).isPreconnected.subset_connectedComponentIn
      (hhead ▸ head_mem_poly hne) hsubA
  exact hpoly (hlast ▸ getLast_mem_poly hne)

/-! ### The payoff -/

/-- **What brick B7 uses.** In a locally polygonally connected `S`, any two points of a
connected relatively open subset are joined by a polygonal path *inside that subset*. -/
theorem polyReaches_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    PolyReaches C x y :=
  PolyReaches.of_isPreconnected (h.of_isRelOpenIn hC).isLocallyPolyConnected hconn hx hy

/-- The component form, which is how `U_e` arises: a component of a relatively open piece is
both relatively open and polygonally connected in itself. -/
theorem polyReaches_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    {w : Plane} (hx : x ∈ connectedComponentIn A w) (hy : y ∈ connectedComponentIn A w) :
    PolyReaches (connectedComponentIn A w) x y :=
  polyReaches_of_isPreconnected_of_isRelOpenIn h (isRelOpenIn_connectedComponentIn h hA w)
    isPreconnected_connectedComponentIn hx hy

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Redrawing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygonal redrawing of a finite plane graph

Bricks B7 and B8 of `lem:polygonal-redrawing`, and the headline theorem: every finite plane
graph is drawn again, on the same abstract graph and the same vertices, with polygonal edges.
Since the vertices of a plane graph *are* plane points and the redrawing leaves them where
they are, the blueprint's "isomorphic plane drawing" is the identity isomorphism, and no
`Graph.IsIsomorphism` is built or needed.

## Three things the design did not have, and this module supplies

**Simple polygonal paths.** `Graph.IsDrawing.edge_param` asks for an *injective*
parametrisation, and brick B6 delivers only a `poly` vertex list, which may cross itself. The
blueprint's Lemma 1.1 makes the path simple "by subdividing at self-intersections and taking a
simple path in the resulting finite graph"; `Schoenflies/PolyPath.lean` deferred that half, and
without it brick B8 cannot discharge the drawing condition at all. `IsArcList` and
`PolyReaches.exists_arcList` supply it, by an induction over the inductive relation rather than
by an overlay graph: at each `step` the new segment is run *backwards* from its far end and
stopped the first time it meets the polygon already built, and the old path is truncated
there. That needs no plane geometry beyond `exists_first_mem_Icc`, and in particular no
connectivity theorem for the overlay graph.

**The contact point is on the frame.** `Graph.IsDrawing.exists_core` states that the core meets
the square about a vertex in exactly one point, but not that this point is on the square's
boundary — and if it were interior the core would not lie in the plane minus the open squares,
which is the carrier brick B5 speaks about, nor would the radial segment from the vertex reach
it. `Plane.supDist_eq_of_inter_eq_singleton` closes the gap by connectedness: an interior
contact point would make the core's trace on the square a nonempty proper clopen piece.

**Radial arithmetic.** That two radials of one square meet only at the centre, and that a
radial meets the plane minus the open squares only at its far end, are both the statement that
the sup distance to the centre is a faithful coordinate along a radius
(`Plane.supDist_lt_of_mem_segment`, `Plane.radial_meet`). These are the "distinct radials in
one square meet only at `v`" and "radials meet the replacement paths only at the designated
boundary points" of brick B8's design, and neither is free.

## Blueprint

Bricks B7 and B8 of `lem:polygonal-redrawing` (H6), and the lemma itself.

* `Plane.supNorm_smul`, `Plane.supDist_add_smul`, `Plane.supDist_lt_of_mem_segment`,
  `Plane.segment_subset_closedSquare`, `Plane.radial_meet` — the radial segments of brick B8.
* `Plane.supDist_eq_of_inter_eq_singleton` — a core's contact point lies on the frame of its
  square; the missing clause of brick B4.
* `lastP`, `poly_snoc`, `IsArcList` — a **simple** polygonal path, in the `u :: t`
  presentation that keeps every statement free of dependent nonemptiness proofs.
* `isArcBetween_poly` — the carrier of a simple polygonal path is an arc between its ends.
* `IsArcList.truncate`, `IsArcList.snoc` — cutting one at any of its points, and extending one
  by a segment that touches it only at its last vertex.
* `PolyReaches.exists_arcList` — **every polygonal path contains a simple one**; the deferred
  half of Lemma 1.1.
* `Graph.polygonal_redrawing` — `lem:polygonal-redrawing`, with bricks B7 and B8 inside its
  proof: the `ε` making the tubes about the cores pairwise disjoint, the component `U e` of
  the core inside its tube, and the assembly of radial, replacement path and radial.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ### Radial segments in a square

A segment from the centre of a square to a point of its boundary frame leaves the open square
only at its far end, and two such segments in one square meet only at the centre. Those two
facts are the whole of the "radials" half of brick B8, and both are statements about the sup
distance scaling along a segment. -/

namespace Plane

theorem supNorm_smul (a : ℝ) (x : Plane) : supNorm (a • x) = |a| * supNorm x := by
  have h0 : (a • x) 0 = a * x 0 := by simp
  have h1 : (a • x) 1 = a * x 1 := by simp
  simp only [supNorm, h0, h1, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg a)).symm

theorem supDist_add_smul (c u : Plane) (t : ℝ) : supDist (c + t • u) c = |t| * supNorm u := by
  have h : c + t • u - c = t • u := by abel
  rw [supDist, h, supNorm_smul]

/-- Everything on the segment from `c` to `p` except `p` itself is strictly nearer to `c` than
`p` is, in the sup metric. This is why a radial segment meets the frame of its square only at
its far end. -/
theorem supDist_lt_of_mem_segment {c p x : Plane} (hpc : 0 < supDist p c)
    (hx : x ∈ segment ℝ c p) (hne : x ≠ p) : supDist x c < supDist p c := by
  rw [segment_eq_image' ℝ c p] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  have hxt' : c + t • (p - c) = x := hxt
  have hval : supDist x c = t * supDist p c := by
    rw [← hxt', supDist_add_smul, abs_of_nonneg ht.1]; rfl
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with heq | h
    · refine absurd ?_ hne
      rw [← hxt', heq]
      module
    · exact h
  rw [hval]
  nlinarith

/-- A radial segment stays inside its square. -/
theorem openSquare_subset_closedSquare (c : Plane) (r : ℝ) :
    openSquare c r ⊆ closedSquare c r := fun x hx => show supDist x c ≤ r from le_of_lt hx

theorem segment_subset_closedSquare {c p : Plane} {r : ℝ} (hr : 0 ≤ r)
    (hpc : supDist p c ≤ r) : segment ℝ c p ⊆ closedSquare c r :=
  (convex_closedSquare c r).segment_subset (mem_closedSquare_self c hr) hpc

/-- **Two radials meet only at the centre.** Two segments from the centres of two squares of a
common radius `r` to points of their frames meet only where they can: if the centres are
distinct the squares are disjoint, and if they agree the two far ends are pinned by the sup
distance, which is injective along a radius. -/
theorem radial_meet {c c' p p' z : Plane} {r : ℝ} (hr : 0 < r) (hp : supDist p c = r)
    (hp' : supDist p' c' = r) (hpp' : p ≠ p')
    (hdisj : c ≠ c' → Disjoint (closedSquare c r) (closedSquare c' r))
    (hz : z ∈ segment ℝ c p) (hz' : z ∈ segment ℝ c' p') : z = c := by
  rcases eq_or_ne c c' with rfl | hcc'
  · -- One square: the two representations of `z` have the same parameter, which must be `0`.
    rw [segment_eq_image' ℝ c p] at hz
    rw [segment_eq_image' ℝ c p'] at hz'
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨s, hs, hzs⟩ := hz'
    have hzt' : c + t • (p - c) = z := hzt
    have hzs' : c + s • (p' - c) = z := hzs
    have h₁ : supDist z c = t * r := by
      rw [← hzt', supDist_add_smul, abs_of_nonneg ht.1, ← hp]; rfl
    have h₂ : supDist z c = s * r := by
      rw [← hzs', supDist_add_smul, abs_of_nonneg hs.1, ← hp']; rfl
    have hEq : t = s := mul_right_cancel₀ hr.ne' (h₁.symm.trans h₂)
    subst hEq
    have hsmul : t • (p - c) = t • (p' - c) := add_left_cancel (hzt'.trans hzs'.symm)
    have hkey : t • (p - p') = 0 := by linear_combination (norm := module) hsmul
    rcases smul_eq_zero.1 hkey with ht0 | hpp
    · rw [← hzt', ht0]; module
    · exact absurd (sub_eq_zero.1 hpp) hpp'
  · exact absurd (Set.disjoint_left.1 (hdisj hcc')
      (segment_subset_closedSquare hr.le hp.le hz)
      (segment_subset_closedSquare hr.le hp'.le hz')) not_false

end Plane

/-! ### Simple polygonal paths

`poly vs` is the carrier of a vertex list, and a general vertex list crosses itself. The
drawing condition of a plane graph asks for an *injective* parametrisation, so what brick B8
needs is a vertex list whose carrier is an **arc**. `IsArcList` is exactly the condition that
makes the concatenation of `Schoenflies/Concatenate.lean` apply at every step: consecutive
vertices differ, and each segment meets the rest of the polygon only at the vertex they
share.

The work of this section is `PolyReaches.exists_arcList`: *any* polygonal path inside a set
contains a simple one with the same ends. That is the half of the blueprint's Lemma 1.1 which
`Schoenflies/PolyPath.lean` deferred, and without it nothing downstream can discharge
`Graph.IsDrawing`. The induction is over the inductive relation `PolyReaches`, and the step
takes the *first* point at which the new segment, run backwards from its far end, meets the
polygon already built, truncates there and appends. -/

theorem lastP_append : ∀ (u : Plane) (t : List Plane) (z : Plane), lastP u (t ++ [z]) = z
  | _, [], _ => rfl
  | u, v :: t, z => by
    rw [List.cons_append, lastP_cons, lastP_append v t z]

theorem lastP_mem_poly (u : Plane) (t : List Plane) : lastP u t ∈ poly (u :: t) :=
  getLast_mem_poly (List.cons_ne_nil u t)

/-- Appending one vertex, in the `u :: t` presentation. -/
theorem poly_snoc (u : Plane) (t : List Plane) (z : Plane) :
    poly (u :: (t ++ [z])) = poly (u :: t) ∪ segment ℝ (lastP u t) z := by
  rw [← List.cons_append, poly_concat (List.cons_ne_nil u t) z]
  rfl

/-- The carrier of a simple polygonal path is an arc between its ends. The induction glues one
segment at a time with `Schoenflies.IsArcBetween.concatenate`; the meeting hypothesis is the
second clause of `IsArcList`. -/
theorem isArcBetween_poly : ∀ (u v : Plane) (rest : List Plane), IsArcList (u :: v :: rest) →
    IsArcBetween (poly (u :: v :: rest)) u (lastP v rest)
  | u, v, [], h => by
    rw [poly_cons_cons, poly_singleton]
    have : segment ℝ u v ∪ {v} = segment ℝ u v :=
      union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))
    rw [this]
    exact isArcBetween_segment h.1
  | u, v, w :: rest, h => by
    rw [poly_cons_cons, lastP_cons]
    refine (isArcBetween_segment h.1).concatenate (isArcBetween_poly v w rest h.2.2) ?_
    intro z hz hz'
    have : z ∈ segment ℝ u v ∩ poly (v :: w :: rest) := ⟨hz, hz'⟩
    rw [h.2.1] at this
    exact this

/-- **Truncation.** A simple polygonal path may be cut at any point of its carrier: the piece
up to that point is again a simple polygonal path, inside the original one. -/
theorem IsArcList.truncate : ∀ (u : Plane) (t : List Plane), IsArcList (u :: t) →
    ∀ {w : Plane}, w ∈ poly (u :: t) →
      ∃ t' : List Plane, IsArcList (u :: t') ∧ poly (u :: t') ⊆ poly (u :: t) ∧
        lastP u t' = w
  | u, [], _, w, hw => by
    rw [poly_singleton, mem_singleton_iff] at hw
    exact ⟨[], isArcList_singleton u, subset_rfl, hw.symm⟩
  | u, v :: rest, h, w, hw => by
    by_cases hrest : w ∈ poly (v :: rest)
    · obtain ⟨rest', hlist, hsub, hlast⟩ := IsArcList.truncate v rest h.2.2 hrest
      refine ⟨v :: rest', ⟨h.1, ?_, hlist⟩, ?_, by rw [lastP_cons, hlast]⟩
      · refine Subset.antisymm ?_ ?_
        · exact fun z hz => h.2.1 ▸ ⟨hz.1, hsub hz.2⟩
        · rintro z rfl
          exact ⟨right_mem_segment ℝ u z, head_mem_poly (List.cons_ne_nil z rest')⟩
      · rw [poly_cons_cons, poly_cons_cons]
        exact union_subset_union_right _ hsub
    · rw [poly_cons_cons] at hw
      have hseg : w ∈ segment ℝ u v := hw.resolve_right hrest
      rcases eq_or_ne w u with heq | hwu
      · refine ⟨[], isArcList_singleton u, ?_, heq.symm⟩
        rw [poly_singleton, poly_cons_cons]
        exact singleton_subset_iff.2 (Or.inl (left_mem_segment ℝ u v))
      · refine ⟨[w], ⟨Ne.symm hwu, ?_, isArcList_singleton w⟩, ?_, rfl⟩
        · rw [poly_singleton]
          exact Subset.antisymm inter_subset_right
            (singleton_subset_iff.2 ⟨right_mem_segment ℝ u w, rfl⟩)
        · rw [poly_cons_cons, poly_singleton, poly_cons_cons]
          have : segment ℝ u w ∪ {w} = segment ℝ u w :=
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u w))
          rw [this]
          exact subset_union_of_subset_left
            ((convex_segment u v).segment_subset (left_mem_segment ℝ u v) hseg) _

/-- **Extension.** A simple polygonal path may be extended by a segment that meets it only at
its own last vertex. -/
theorem IsArcList.snoc : ∀ (u : Plane) (t : List Plane), IsArcList (u :: t) →
    ∀ {z : Plane}, z ≠ lastP u t →
      segment ℝ (lastP u t) z ∩ poly (u :: t) = {lastP u t} →
      IsArcList (u :: (t ++ [z]))
  | u, [], _, z, hz, _ => by
    refine ⟨Ne.symm hz, ?_, isArcList_singleton z⟩
    rw [poly_singleton]
    exact Subset.antisymm inter_subset_right
      (singleton_subset_iff.2 ⟨right_mem_segment ℝ u z, rfl⟩)
  | u, v :: rest, h, z, hz, hmeet => by
    rw [List.cons_append]
    refine ⟨h.1, ?_, ?_⟩
    · -- The first segment still meets the rest only at `v`: the new piece is barred from it
      -- because it meets the whole old polygon only at its last vertex, which lies on the
      -- rest and hence, if it were on the first segment, would have to be `v`.
      rw [lastP_cons] at hz hmeet
      rw [poly_snoc]
      refine Subset.antisymm ?_ ?_
      · rintro y ⟨hy1, hy2 | hy2⟩
        · exact h.2.1 ▸ ⟨hy1, hy2⟩
        · have hylast : y = lastP v rest := by
            have : y ∈ segment ℝ (lastP v rest) z ∩ poly (u :: v :: rest) :=
              ⟨hy2, Or.inl hy1⟩
            rw [hmeet] at this
            exact this
          have : lastP v rest ∈ segment ℝ u v ∩ poly (v :: rest) :=
            ⟨hylast ▸ hy1, lastP_mem_poly v rest⟩
          rw [h.2.1] at this
          rw [hylast]
          exact this
      · rintro y rfl
        exact ⟨right_mem_segment ℝ u y, Or.inl (head_mem_poly (List.cons_ne_nil y rest))⟩
    · rw [lastP_cons] at hz hmeet
      refine IsArcList.snoc v rest h.2.2 hz (Subset.antisymm ?_ ?_)
      · exact fun y hy => hmeet ▸ ⟨hy.1, Or.inr hy.2⟩
      · exact singleton_subset_iff.2
          ⟨left_mem_segment ℝ _ _, lastP_mem_poly v rest⟩

/-- **Every polygonal path contains a simple one.** This is the half of Lemma 1.1 that
`Schoenflies/PolyPath.lean` deferred, and the reason brick B8 can discharge the injectivity
clause of `Graph.IsDrawing`.

The induction is on `PolyReaches`. At a `step` the new segment is run *backwards* from its far
end and stopped the first time it touches the polygon already built — `exists_first_mem_Icc`
of `Schoenflies/Graph/VertexSquares.lean` is exactly that. The old path is truncated there and
the stub appended; the stub meets the truncation only at the join, because everything strictly
before the stopping parameter misses the old polygon altogether. -/
theorem PolyReaches.exists_arcList {S : Set Plane} {x y : Plane} (h : PolyReaches S x y) :
    ∃ t : List Plane, IsArcList (x :: t) ∧ poly (x :: t) ⊆ S ∧ lastP x t = y := by
  induction h with
  | refl hx => exact ⟨[], isArcList_singleton x, by simpa using hx, rfl⟩
  | @step w z _ hseg ih =>
    obtain ⟨t, hlist, hsub, hlast⟩ := ih
    -- The straight run from `z` back to `w`, stopped the first time it meets the old polygon.
    set γ : ℝ → Plane := fun a => z + a • (w - z) with hγ
    have hγc : ContinuousOn γ (Icc 0 1) := (by fun_prop : Continuous γ).continuousOn
    have hγ1 : γ 1 = w := by simp [hγ]
    have hclosed : IsClosed (poly (x :: t)) := (isCompact_poly _).isClosed
    have hmem1 : γ 1 ∈ poly (x :: t) := by
      rw [hγ1, ← hlast]; exact lastP_mem_poly x t
    obtain ⟨s, hs, -, hsmem, hbefore⟩ :=
      exists_first_mem_Icc hγc hclosed (right_mem_Icc.2 zero_le_one) hmem1
    -- Everything on the stub, bar its far end, is before the stopping parameter.
    have himg : segment ℝ (γ s) z ⊆ γ '' Icc 0 s := by
      rw [segment_symm, segment_eq_image' ℝ z (γ s)]
      rintro u ⟨θ, hθ, rfl⟩
      refine ⟨θ * s, ⟨mul_nonneg hθ.1 hs.1, mul_le_of_le_one_left hs.1 hθ.2⟩, ?_⟩
      simp only [hγ]
      module
    have hstub : ∀ u ∈ segment ℝ (γ s) z, u ∈ poly (x :: t) → u = γ s := by
      intro u hu humem
      obtain ⟨a, ha, rfl⟩ := himg hu
      rcases eq_or_lt_of_le ha.2 with heq | hlt
      · rw [heq]
      · exact absurd humem (hbefore a ⟨ha.1, le_trans ha.2 hs.2⟩ hlt)
    -- The stub lies on the new segment, since `γ s` does.
    have hγs_seg : γ s ∈ segment ℝ z w := by
      rw [segment_eq_image' ℝ z w]
      exact ⟨s, hs, rfl⟩
    have hsegzw : segment ℝ z w ⊆ S := by rw [segment_symm]; exact hseg
    have hstubsub : segment ℝ (γ s) z ⊆ S :=
      Subset.trans ((convex_segment z w).segment_subset hγs_seg (left_mem_segment ℝ z w)) hsegzw
    obtain ⟨t', hlist', hsub', hlast'⟩ := IsArcList.truncate x t hlist hsmem
    rcases eq_or_ne z (γ s) with heq | hzne
    · exact ⟨t', hlist', hsub'.trans hsub, by rw [hlast']; exact heq.symm⟩
    · refine ⟨t' ++ [z], ?_, ?_, lastP_append x t' z⟩
      · refine IsArcList.snoc x t' hlist' (by rw [hlast']; exact hzne) ?_
        rw [hlast']
        refine Subset.antisymm (fun u hu => hstub u hu.1 (hsub' hu.2)) ?_
        exact singleton_subset_iff.2 ⟨left_mem_segment ℝ _ _, hlast' ▸ lastP_mem_poly x t'⟩
      · rw [poly_snoc, hlast']
        exact union_subset (hsub'.trans hsub) hstubsub

/-! ### The contact point of a core sits on the frame of its square

`Graph.IsDrawing.exists_core` says the core meets the square about `v` in exactly one point.
That point is on the *frame* of the square and not in its interior, which is what puts the
core in the plane minus the open squares and what makes the radial segment reach the core.
The argument is connectedness, not the parametrisation: were the contact point interior, it
would be a nonempty proper clopen piece of the core. -/

namespace Plane

/-- If a connected set meets a closed square in exactly one point and is not contained in that
square, the meeting point is on the frame: its sup distance to the centre is exactly the
radius. -/
theorem supDist_eq_of_inter_eq_singleton {K : Set Plane} {c p q : Plane} {r : ℝ}
    (hK : IsPreconnected K) (hp : K ∩ closedSquare c r = {p}) (hq : q ∈ K)
    (hqc : q ∉ closedSquare c r) : supDist p c = r := by
  have hpmem : p ∈ K ∩ closedSquare c r := by rw [hp]; rfl
  refine le_antisymm hpmem.2 (le_of_not_gt fun hlt => ?_)
  obtain ⟨w, hwK, hw1, hw2⟩ := hK (openSquare c r) (closedSquare c r)ᶜ
    (isOpen_openSquare c r) (isClosed_closedSquare c r).isOpen_compl
    (fun z hz => by
      by_cases hzc : z ∈ closedSquare c r
      · refine Or.inl ?_
        have hzp : z ∈ K ∩ closedSquare c r := ⟨hz, hzc⟩
        rw [hp, mem_singleton_iff] at hzp
        rw [hzp]
        exact hlt
      · exact Or.inr hzc)
    ⟨p, hpmem.1, hlt⟩ ⟨q, hq, hqc⟩
  exact hw2 (openSquare_subset_closedSquare c r hw1)

end Plane

end Schoenflies

/-! ### Bricks B7 and B8, and the redrawing itself -/

open Schoenflies

namespace Graph

/-- **The polygonal redrawing of a finite plane graph** (`lem:polygonal-redrawing`). A finite
plane graph is drawn again, on the *same* abstract graph and the *same* vertices, with every
edge a polygonal arc. The blueprint speaks of an isomorphic plane drawing; since the vertices
of a plane graph are plane points and the redrawing leaves them where they are, the
isomorphism is the identity and no `Graph.IsIsomorphism` appears.

The construction, in the order the proof takes it.

* **The squares** (brick B2). One radius `r` serves every vertex: the square about a vertex
  meets no other vertex, meets no arc of an edge it is not incident with, and distinct squares
  are disjoint.
* **The cores** (brick B4). Each edge's arc, cut back to what lies between its last exit from
  the square at one end and its first entry into the square at the other. A core carries no
  vertex, so distinct cores are disjoint; and — `Plane.supDist_eq_of_inter_eq_singleton` — its
  two contact points sit on the *frames* of the two squares, so the core lies in the plane `M`
  minus the open squares.
* **The tubes** (brick B7). One `ε` makes the `ε`-tubes about the cores pairwise disjoint, by
  compact separation and the single-bound lemma. `U e` is the connected component, inside
  `M ∩ tube e`, of the core; it is relatively open in `M`, so the strengthened brick B5 joins
  the two contact points by a polygonal path *inside* `U e`.
* **The assembly** (brick B8). The path is straightened to a simple one
  (`Schoenflies.PolyReaches.exists_arcList`), then a radial segment is prepended at each end.
  A radial meets `M` only at its far end and two radials meet only at their common centre, so
  the three pieces glue to an arc; `Schoenflies.isArcBetween_poly` produces the
  parametrisation that `IsDrawing.edge_param` demands. -/
theorem polygonal_redrawing {β : Type*} (G : Graph Plane β) [G.Finite]
    (drawing : β → ℝ → Plane) (h : IsDrawing G drawing) :
    ∃ redrawing : β → ℝ → Plane, IsDrawing G redrawing ∧
      ∀ e ∈ E(G), IsPolygonal (edgeArc redrawing e) := by
  classical
  obtain ⟨r, hr, hvert, hnoninc, hsqdisj⟩ := h.exists_vertexSquares
  -- The core of every edge, with the edge's two ends and the core's two contact points.
  have hdata : ∀ e ∈ E(G), ∃ a b p q : Plane, ∃ Kc : Set Plane,
      G.IsLink e a b ∧ Kc ⊆ edgeArc drawing e ∧ IsCompact Kc ∧ IsArcBetween Kc p q ∧
        Kc ∩ Plane.closedSquare a r = {p} ∧ Kc ∩ Plane.closedSquare b r = {q} ∧
        Disjoint Kc V(G) := by
    intro e he
    obtain ⟨a, b, hl⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain ⟨Kc, p, q, h1, h2, h3, h4, h5, h6⟩ :=
      h.exists_core hr hl (hsqdisj a hl.left_mem b hl.right_mem (h.ne_of_isLink hl))
    exact ⟨a, b, p, q, Kc, hl, h1, h2, h3, h4, h5, h6⟩
  choose! va vb pa pb core hlink hcoresub hcorecpt hcorearc hcoreA hcoreB hcoreV using hdata
  have hvaV : ∀ e ∈ E(G), va e ∈ V(G) := fun e he => (hlink e he).left_mem
  have hvbV : ∀ e ∈ E(G), vb e ∈ V(G) := fun e he => (hlink e he).right_mem
  have hvab : ∀ e ∈ E(G), va e ≠ vb e := fun e he => h.ne_of_isLink (hlink e he)
  have hpamem : ∀ e ∈ E(G), pa e ∈ core e ∩ Plane.closedSquare (va e) r := by
    intro e he; rw [hcoreA e he]; rfl
  have hpbmem : ∀ e ∈ E(G), pb e ∈ core e ∩ Plane.closedSquare (vb e) r := by
    intro e he; rw [hcoreB e he]; rfl
  have hcoreconn : ∀ e ∈ E(G), IsPreconnected (core e) :=
    fun e he => (hcorearc e he).isArc.isConnected.isPreconnected
  -- The contact points sit on the frames of their squares.
  have hpar : ∀ e ∈ E(G), Plane.supDist (pa e) (va e) = r := by
    intro e he
    refine Plane.supDist_eq_of_inter_eq_singleton (hcoreconn e he) (hcoreA e he)
      (hpbmem e he).1 fun hcon => ?_
    exact Set.disjoint_left.1 (hsqdisj (va e) (hvaV e he) (vb e) (hvbV e he) (hvab e he))
      hcon (hpbmem e he).2
  have hpbr : ∀ e ∈ E(G), Plane.supDist (pb e) (vb e) = r := by
    intro e he
    refine Plane.supDist_eq_of_inter_eq_singleton (hcoreconn e he) (hcoreB e he)
      (hpamem e he).1 fun hcon => ?_
    exact Set.disjoint_left.1 (hsqdisj (vb e) (hvbV e he) (va e) (hvaV e he)
      (Ne.symm (hvab e he))) hcon (hpamem e he).2
  -- The plane minus the open squares, and its local polygonal connectedness (brick B5).
  set M : Set Plane := (⋃ c ∈ V(G), Plane.openSquare c r)ᶜ with hMdef
  have hMloc : IsLocallyPolyConn' M :=
    isLocallyPolyConn'_compl_biUnion (Graph.finite_vertexSet (G := G)) (fun _ => r) hsqdisj
  have hMV : ∀ c ∈ V(G), c ∉ M := fun c hc hcM =>
    hcM (mem_biUnion hc (Plane.mem_openSquare_self hr))
  -- The cores avoid the open squares.
  have hcoreM : ∀ e ∈ E(G), core e ⊆ M := by
    intro e he z hz hcon
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 hcon
    have hzc' : z ∈ Plane.closedSquare c r := Plane.openSquare_subset_closedSquare c r hzc
    rcases eq_or_ne c (va e) with rfl | hca
    · have hzp : z ∈ core e ∩ Plane.closedSquare (va e) r := ⟨hz, hzc'⟩
      rw [hcoreA e he, mem_singleton_iff] at hzp
      rw [hzp] at hzc
      exact absurd (hpar e he) (ne_of_lt hzc)
    · rcases eq_or_ne c (vb e) with rfl | hcb
      · have hzp : z ∈ core e ∩ Plane.closedSquare (vb e) r := ⟨hz, hzc'⟩
        rw [hcoreB e he, mem_singleton_iff] at hzp
        rw [hzp] at hzc
        exact absurd (hpbr e he) (ne_of_lt hzc)
      · exact Set.disjoint_left.1
          (hnoninc c hc e he (not_inc_of_ne (hlink e he) hca hcb)) hzc' (hcoresub e he hz)
  -- Brick B7: one `ε` making the tubes about the cores pairwise disjoint.
  obtain ⟨ε, hε, hεall⟩ : ∃ ε > 0, ∀ e ∈ E(G), ∀ f ∈ E(G), f ≠ e →
      ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e ε => ∀ f ∈ E(G), f ≠ e → ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b)
      (fun e δ ε _ hδε hP f hf hfe a ha b hb =>
        le_trans (by linarith) (hP f hf hfe a ha b hb)) ?_
    intro e he
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun f ε => f ≠ e → ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b)
      (fun f δ ε _ hδε hP hfe a ha b hb => le_trans (by linarith) (hP hfe a ha b hb)) ?_
    intro f hf
    by_cases hfe : f = e
    · exact ⟨1, one_pos, fun hcon => absurd hfe hcon⟩
    · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos (hcorecpt e he) (hcorecpt f hf)
        (h.disjoint_of_subset_edgeArc he hf (Ne.symm hfe) (hcoresub e he) (hcoreV e he)
          (hcoresub f hf))
      exact ⟨ρ / 2, by linarith, fun _ a ha b hb => by have := hsep a ha b hb; linarith⟩
  set tube : β → Set Plane := fun e => ⋃ z ∈ core e, ball z ε with htubedef
  have htubeopen : ∀ e, IsOpen (tube e) := fun _ => isOpen_biUnion fun _ _ => isOpen_ball
  have htubedisj : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint (tube e) (tube f) := by
    intro e he f hf hef
    refine Set.disjoint_left.2 fun z hze hzf => ?_
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hze
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 hzf
    have h1 : dist a z < ε := by rw [dist_comm]; exact hza
    have h2 : dist z b < ε := hzb
    have h3 := hεall e he f hf (Ne.symm hef) a ha b hb
    have h4 := dist_triangle a z b
    linarith
  -- `U e` is the component of the core inside the tube, relatively open in `M`.
  set U : β → Set Plane := fun e => connectedComponentIn (M ∩ tube e) (pa e) with hUdef
  have hrel : ∀ e, IsRelOpenIn M (M ∩ tube e) := fun e => ⟨tube e, htubeopen e, rfl⟩
  have hcoreO : ∀ e ∈ E(G), core e ⊆ M ∩ tube e := fun e he z hz =>
    ⟨hcoreM e he hz, mem_iUnion₂.2 ⟨z, hz, mem_ball_self hε⟩⟩
  have hcoreU : ∀ e ∈ E(G), core e ⊆ U e := fun e he =>
    (hcoreconn e he).subset_connectedComponentIn (hpamem e he).1 (hcoreO e he)
  have hUM : ∀ e, U e ⊆ M := fun _ =>
    (connectedComponentIn_subset _ _).trans inter_subset_left
  have hUdisj : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint (U e) (U f) := fun e he f hf hef =>
    Set.disjoint_of_subset ((connectedComponentIn_subset _ _).trans inter_subset_right)
      ((connectedComponentIn_subset _ _).trans inter_subset_right) (htubedisj e he f hf hef)
  have hpaU : ∀ e ∈ E(G), pa e ∈ U e := fun e he => hcoreU e he (hpamem e he).1
  have hpbU : ∀ e ∈ E(G), pb e ∈ U e := fun e he => hcoreU e he (hpbmem e he).1
  have hpath : ∀ e ∈ E(G), PolyReaches (U e) (pa e) (pb e) := fun e he =>
    polyReaches_connectedComponentIn hMloc (hrel e) (hpaU e he) (hpbU e he)
  -- A radial segment meets `M` only at its far end, and stays inside its square.
  have hsegM : ∀ c p : Plane, c ∈ V(G) → Plane.supDist p c = r →
      ∀ z ∈ segment ℝ c p, z ∈ M → z = p := by
    intro c p hc hpc z hz hzM
    by_contra hne
    refine hzM (mem_biUnion hc ?_)
    have hlt := Plane.supDist_lt_of_mem_segment (by rw [hpc]; exact hr) hz hne
    rw [hpc] at hlt
    exact hlt
  have hsegSq : ∀ c p : Plane, Plane.supDist p c = r →
      segment ℝ c p ⊆ Plane.closedSquare c r :=
    fun c p hpc => Plane.segment_subset_closedSquare hr.le hpc.le
  -- The point set of a redrawn edge, before it is built.
  set Sset : β → Set Plane := fun e =>
    segment ℝ (va e) (pa e) ∪ U e ∪ segment ℝ (vb e) (pb e) with hSsetdef
  have hUcase : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → ∀ z ∈ U e, z ∉ Sset f := by
    intro e he f hf hef z hz hzf
    have hzM : z ∈ M := hUM e hz
    have hdis := Set.disjoint_left.1 (hUdisj e he f hf hef) hz
    rcases hzf with (hzf | hzf) | hzf
    · exact hdis ((hsegM (va f) (pa f) (hvaV f hf) (hpar f hf) z hzf hzM) ▸ hpaU f hf)
    · exact hdis hzf
    · exact hdis ((hsegM (vb f) (pb f) (hvbV f hf) (hpbr f hf) z hzf hzM) ▸ hpbU f hf)
  have hRadial : ∀ e ∈ E(G), ∀ c p : Plane, c ∈ V(G) → Plane.supDist p c = r → p ∈ U e →
      ∀ f ∈ E(G), e ≠ f → ∀ z ∈ segment ℝ c p, z ∈ Sset f → z = c := by
    intro e he c p hc hpc hpU f hf hef z hz hzf
    have hdis := Set.disjoint_left.1 (hUdisj e he f hf hef) hpU
    rcases hzf with (hzf | hzf) | hzf
    · exact Plane.radial_meet hr hpc (hpar f hf)
        (fun hEq => hdis (hEq ▸ hpaU f hf)) (fun hne => hsqdisj c hc _ (hvaV f hf) hne) hz hzf
    · exact absurd (hdis ((hsegM c p hc hpc z hz (hUM f hzf)) ▸ hzf)) not_false
    · exact Plane.radial_meet hr hpc (hpbr f hf)
        (fun hEq => hdis (hEq ▸ hpbU f hf)) (fun hne => hsqdisj c hc _ (hvbV f hf) hne) hz hzf
  have hSmeet : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → ∀ z ∈ Sset e, z ∈ Sset f →
      z = va e ∨ z = vb e := by
    intro e he f hf hef z hze hzf
    rcases hze with (hze | hze) | hze
    · exact Or.inl (hRadial e he (va e) (pa e) (hvaV e he) (hpar e he) (hpaU e he)
        f hf hef z hze hzf)
    · exact absurd hzf (hUcase e he f hf hef z hze)
    · exact Or.inr (hRadial e he (vb e) (pb e) (hvbV e he) (hpbr e he) (hpbU e he)
        f hf hef z hze hzf)
  have hSvert : ∀ e ∈ E(G), ∀ v ∈ V(G), v ∈ Sset e → v = va e ∨ v = vb e := by
    intro e he v hv hvS
    rcases hvS with (hvS | hvS) | hvS
    · refine Or.inl (by_contra fun hne => ?_)
      exact hvert (va e) (hvaV e he) v hv hne (hsegSq (va e) (pa e) (hpar e he) hvS)
    · exact absurd (hUM e hvS) (hMV v hv)
    · refine Or.inr (by_contra fun hne => ?_)
      exact hvert (vb e) (hvbV e he) v hv hne (hsegSq (vb e) (pb e) (hpbr e he) hvS)
  -- Brick B8: the redrawn edge, as a parametrisation.
  have harc : ∀ e ∈ E(G), ∃ g : ℝ → Plane,
      ContinuousOn g I ∧ InjOn g I ∧ g 0 = va e ∧ g 1 = vb e ∧
        IsPolygonal (g '' I) ∧ g '' I ⊆ Sset e := by
    intro e he
    obtain ⟨t, hlist, hsub, hlast⟩ := (hpath e he).exists_arcList
    have hpaM : ∀ z ∈ poly (pa e :: t), z ∈ M := fun z hz => hUM e (hsub hz)
    have hAP : va e ≠ pa e := by
      intro hEq
      have hx := hpar e he
      rw [← hEq, Plane.supDist_self] at hx
      exact hr.ne' hx.symm
    have hBQ : vb e ≠ pb e := by
      intro hEq
      have hx := hpbr e he
      rw [← hEq, Plane.supDist_self] at hx
      exact hr.ne' hx.symm
    have hpbpoly : pb e ∈ poly (pa e :: t) := hlast ▸ lastP_mem_poly (pa e) t
    -- The far radial meets the straightened path only at the far contact point.
    have hmeetQ : segment ℝ (pb e) (vb e) ∩ poly (pa e :: t) = {pb e} := by
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rw [segment_symm] at hz
        exact hsegM (vb e) (pb e) (hvbV e he) (hpbr e he) z hz.1 (hpaM z hz.2)
      · exact singleton_subset_iff.2 ⟨left_mem_segment ℝ _ _, hpbpoly⟩
    have hlist2 : IsArcList (pa e :: (t ++ [vb e])) :=
      IsArcList.snoc (pa e) t hlist (by rw [hlast]; exact hBQ)
        (by rw [hlast]; exact hmeetQ)
    have hpolysnoc : poly (pa e :: (t ++ [vb e]))
        = poly (pa e :: t) ∪ segment ℝ (pb e) (vb e) := by
      rw [poly_snoc, hlast]
    -- The near radial meets the rest only at the near contact point: the straightened path
    -- lives in `M`, and the far radial lives in the other square.
    have hmeetP : segment ℝ (va e) (pa e) ∩ poly (pa e :: (t ++ [vb e])) = {pa e} := by
      rw [hpolysnoc]
      refine Subset.antisymm ?_ ?_
      · rintro z ⟨hz1, hz2 | hz2⟩
        · exact hsegM (va e) (pa e) (hvaV e he) (hpar e he) z hz1 (hpaM z hz2)
        · rw [segment_symm] at hz2
          exact absurd (Set.disjoint_left.1
            (hsqdisj (va e) (hvaV e he) (vb e) (hvbV e he) (hvab e he))
            (hsegSq (va e) (pa e) (hpar e he) hz1)
            (hsegSq (vb e) (pb e) (hpbr e he) hz2)) not_false
      · exact singleton_subset_iff.2 ⟨right_mem_segment ℝ _ _,
          Or.inl (head_mem_poly (List.cons_ne_nil _ _))⟩
    have hlist3 : IsArcList (va e :: pa e :: (t ++ [vb e])) := ⟨hAP, hmeetP, hlist2⟩
    have harcb := isArcBetween_poly (va e) (pa e) (t ++ [vb e]) hlist3
    rw [lastP_append] at harcb
    obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := harcb
    refine ⟨g, hgc, hgi, hg0, hg1, ⟨_, hgim⟩, ?_⟩
    rw [hgim, poly_cons_cons, hpolysnoc]
    refine union_subset (subset_union_of_subset_left subset_union_left _)
      (union_subset (hsub.trans (subset_union_of_subset_left subset_union_right _)) ?_)
    rw [segment_symm]
    exact subset_union_right
  choose! F hFc hFi hF0 hF1 hFpoly hFsub using harc
  refine ⟨F, ⟨fun e he => ⟨hFc e he, hFi e he, ?_⟩, ?_, ?_⟩, fun e he => hFpoly e he⟩
  · rw [hF0 e he, hF1 e he]; exact hlink e he
  · intro e a b v hl hv hvarc
    have he : e ∈ E(G) := hl.edge_mem
    rcases hSvert e he v hv (hFsub e he hvarc) with hEq | hEq <;>
      rcases hl.eq_and_eq_or_eq_and_eq (hlink e he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (hEq.trans h1.symm)
    · exact Or.inr (hEq.trans h2.symm)
    · exact Or.inr (hEq.trans h2.symm)
    · exact Or.inl (hEq.trans h1.symm)
  · intro e f he hf hef z hze hzf
    have h1 := hSmeet e he f hf hef z (hFsub e he hze) (hFsub f hf hzf)
    have h2 := hSmeet f hf e he (Ne.symm hef) z (hFsub f hf hzf) (hFsub e he hze)
    refine ⟨?_, ?_, ?_⟩
    · rcases h1 with hEq | hEq
      · rw [hEq]; exact hvaV e he
      · rw [hEq]; exact hvbV e he
    · rcases h1 with hEq | hEq
      · rw [hEq]; exact (hlink e he).inc_left
      · rw [hEq]; exact (hlink e he).inc_right
    · rcases h2 with hEq | hEq
      · rw [hEq]; exact (hlink f hf).inc_left
      · rw [hEq]; exact (hlink f hf).inc_right

end Graph
end

section
-- module Solutions.Q146_CD.Graph_K33Planar
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Lemma 3.10: the utility graph is not planar, and Corollary 3.11 for its subdivisions

`Schoenflies/Graph/K33.lean` built the whole configuration: the six-cycle of a drawn `K(3,3)`
is a Jordan curve, each of the three remaining edges is a crosscut of it, two of the three lie
on the same side, their endpoints alternate, and any two of them are disjoint. This module
wires those five facts to `Schoenflies.alternating_crosscuts` and derives the contradiction; it
then does the blueprint's reduction of `cor:k33-subdivision` to `lem:k33`.

**One hypothesis is assumed and not proved: `Graph.IsHexRealization`. See "The gap" below.**
The remaining results use only the hypotheses in their statements.

## Blueprint

* `Graph.IsHexCrosscut` — the six-cycle, together with one of the three remaining edges, in the
  vocabulary `Schoenflies.IsPolygonalCrosscut` speaks: a `Schoenflies.ClosedPolygon`, its two
  arcs, the crosscut, and a reference point.
* `Graph.IsK33Config.endpoints_subset_arcA`, `…_arcB`, `…exists_reference_point`,
  `…isHexCrosscut` — the four *topological* clauses of `Schoenflies.IsPolygonalCrosscut`,
  discharged from the drawing, so that only the combinatorial realization has to be assumed.
* `Graph.IsHexRealization` — that combinatorial realization, and the one thing assumed here.
* `Graph.IsK33Config.exists_two_chords_same_region` — `lem:k33`, "two of the three lie on the
  same side", with the side named as a region of the complement rather than as one of a pair
  of open sets, which is the form the crosscut corollary consumes.
* `Graph.IsK33Config.false_of_isHexCrosscut` — the contradiction at a *fixed* pair of remaining
  edges: `cor:alternating-crosscuts` makes them meet, `chords_disjoint` says they do not.
* `Graph.IsK33Config.false_of_hexCrosscuts`, `…false_of_hexRealizations` — `lem:k33` for a
  drawing that is already polygonal.
* `Graph.IsK33Config.not_isDrawing` — `lem:k33`: a graph carrying a copy of `K(3,3)` has no
  plane drawing at all. `lem:polygonal-redrawing` reduces the general drawing to a polygonal
  one, which is the only place polygonality is used.
* `Graph.IsArcK33`, `Graph.k33Graph`, `Graph.IsArcK33.arcDrawing`, `…isDrawing`,
  `…isK33Config`, `…false_of_realization` — `cor:k33-subdivision`, first half: nine arcs in the
  plane meeting only where a `K(3,3)` forces them to already *are* a plane drawing of `K(3,3)`,
  on an abstract graph built here for the purpose.
* `Graph.IsK33Subdivision`, `…isArcK33`, `…false_of_realization` — `cor:k33-subdivision`: in a
  plane drawing of a subdivision, the branch paths draw nine such arcs.

## The gap: realizing the six-cycle as a `ClosedPolygon`

Every statement of `Schoenflies/PolygonalJordan.lean`, `Schoenflies/PolygonalCrosscut.lean` and
`Schoenflies/AlternatingCrosscuts.lean` is about a `Schoenflies.ClosedPolygon m` — a cyclic
*vertex list* with `vertex_inj`, `edges_meet` and `corner`. The six-cycle of a polygonally
drawn `K(3,3)` is a polygonal Jordan curve as a **point set**, and nothing in the development
turns a point set into a `ClosedPolygon`: there is no declaration anywhere whose conclusion is
`∃ m (C : ClosedPolygon m), C.carrier = _`. The only closed polygons that exist are the
hand-built `Schoenflies.triangle` and `Schoenflies.unitTriangle`.

`IsHexRealization` is exactly that missing step, stated for the one curve this argument needs
it for and pared down to its combinatorial core: four closed polygons and four equations
identifying their carriers and edge lists with the drawing. No topological side condition
survives in it — the reference point of Theorem 2.8 and the three "meets" clauses are proved
here from the drawing. It is *not proved here*, and every theorem below that mentions it is
therefore requires that realization as a hypothesis.

**Why the realization is allowed to change the drawing.** `IsHexRealization` asks for
`C.arc a k = arcA e s`, which pins the two ends of that arc — the vertices `x s` and
`y (s+1)` — to be *vertices* of `C`. A `Schoenflies.ClosedPolygon` has no straight vertices
(its `corner` field), so this is possible only if the six-cycle actually turns at `x s` and at
`y (s+1)`. A polygonal drawing need not do that: two of the three polygonal edges at a vertex
may leave it in exactly opposite directions, and then no closed polygon with that carrier has
that point as a vertex. A realization must therefore be free to bend the drawing at the six
vertices first, and `Graph.IsK33Config.not_isDrawing` gives it that freedom: it hands the
realization a polygonal drawing and accepts *any* drawing back. This restriction comes from
`Schoenflies.IsPolygonalCrosscut`, not from anything here; the alternative is a crosscut
interface that lets the two cut points be interior to edges of `C`.
-/

open Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3} {R : Set Plane}

/-! ### The missing realization, isolated

The six-cycle of a polygonally drawn `K(3,3)`, cut by the remaining edge `e s (s+1)`, presented
in the vocabulary of `Schoenflies.IsPolygonalCrosscut`: a `ClosedPolygon` whose carrier is the
six-cycle, whose two arcs from the cut are the two halves `arcA e s` and `arcB e s`, and whose
crosscut occupies exactly the remaining edge's arc. -/

/-! ### What must still be assumed: the combinatorial realization

Everything above is proved. What is not is that the six-cycle, its two arcs, and the two closed
curves the remaining edge forms with them are *closed polygons at all* — that a polygonal Jordan
curve given as a point set carries a cyclic vertex list. `IsHexRealization` says exactly that,
and nothing more: no reference point, no meeting condition, only the four `ClosedPolygon`s and
the four equations identifying their carriers and edge lists with the drawing. -/

/-! ## Corollary 3.11: no subdivision of `K(3,3)` has a plane drawing

The blueprint's proof replaces each branch path of a subdivision by the simple arc it draws and
then treats that arc as a single edge. Both halves are done here, in that order: first the
*abstract* statement that nine arcs meeting only where they must already carry a drawn
`K(3,3)` (`Graph.IsArcK33`), then the reduction of a drawn subdivision to nine such arcs. -/

instance instFinitePlaneProdFinOfNatNatK33Graph (x y : Fin 3 → Plane) : (k33Graph x y).Finite where
  finite_vertexSet := (Set.finite_range x).union (Set.finite_range y)
  finite_edgeSet := Set.finite_univ

/-! ### From a drawn subdivision to nine arcs -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_K33Land
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `lem:k33` and `cor:k33-subdivision`, with nothing assumed

`Schoenflies/Graph/K33Planar.lean` proves the nonplanarity of `K(3,3)` from
`Graph.IsHexRealization`; `Schoenflies/Graph/K33Closed.lean` reduces that to `Graph.Bendable` —
"every polygonal drawing can be redrawn so that no two edges leave a vertex along one line". This
module removes the hypothesis altogether. Nothing is bent.

## Where the hypothesis came from, and why it is not needed

`Schoenflies.ClosedPolygon` carries a `corner` field, and
`Schoenflies.ClosedPolygon.isCornerAt_vertex` shows the field is not slack: *every* vertex of
*every* `ClosedPolygon` presentation is a point at which the curve turns. So a crosscut interface
phrased with `ClosedPolygon`s — `Schoenflies.IsPolygonalCrosscut`, and hence
`Schoenflies.alternating_crosscuts` — can only cut the curve at corners, and a drawn `K(3,3)` puts
its branch points wherever it likes.

The blueprint's `cor:alternating-crosscuts` has no such condition: it is stated for a set-level
simple closed polygonal curve and simple polygonal arcs with endpoints anywhere on it. The fix is
to state the crosscut for `Schoenflies.PrePolygon` — `ClosedPolygon` without `corner` — whose
vertices may sit anywhere on the curve. `Schoenflies/PrePolygonSep.lean` already supplies the two
things Theorem 2.8 asks of such a curve: that its carrier separates the plane, and the two values
of the crossing parity. Everything else in the chain is about *edge lists*, and edge lists do not
know about corners.

## The one construction this needed

Three closed polygons enter Theorem 2.8 — the curve `C` and the two curves `Jᵢ` the crosscut
forms with the two arcs — and their **edge lists** must agree: `SameEdges Jᵢ.pieces (Aᵢ ++ K)`.
`Schoenflies/Graph/K33Closed.lean` found three realizations independently and matched them with
`Schoenflies.ClosedPolygon.arcPieces_eq`, whose proof is exactly where `corner` was consumed. For
`PrePolygon` no such matching theorem can exist: two presentations of one arc need not agree.

So the two spliced curves are not found — they are *built*. `Schoenflies.PrePolygon.exists_splice`
lays two chains with common ends end to end and returns a `PrePolygon` whose edge list is their
concatenation, so the three lists agree by construction and nothing has to be matched. The chains
themselves come from `Schoenflies.exists_prePolygon_arcs_oriented`, which needs
`Schoenflies.PrePolygon.insertLast` of `Schoenflies/PrePolygonArc.lean`: a point of the curve that
is not yet a vertex is interior to an edge, and an edge may be cut. That is the inverse of
`Schoenflies.PrePolygon.deleteLast`, and it is what makes "a `PrePolygon` may be presented with
vertices at any prescribed finite set of points of its carrier" a theorem
(`Schoenflies.PrePolygon.exists_prePolygon_vertices`).

## What this module rests on

The `Schoenflies.PrePolygon` arc apparatus — `chain`, `arcPieces`, `arc`, `arc_inter`,
`isArcBetween_arc`, `parity_splitting`, `parity_ne_iff_mem_farRegion`, `insertLast`,
`exists_prePolygon_vertices`, `Schoenflies.exists_prePolygon_split` and the segment-cutting
lemmas — is in `Schoenflies/PrePolygonArc.lean`, shared with `Schoenflies/FaceCyclesLand.lean`.
Only what is peculiar to the crosscut wiring is left here.

## Blueprint

* `Schoenflies.PrePolygon.exists_splice` — two arcs with common ends, laid end to end.
* `Schoenflies.PrePolygon.reverse`, `…reverse_arc`, `…sameEdges_reverse_arcPieces` — the polygon
  traversed the other way, which is what pins the direction of a prescribed arc.
* `Schoenflies.exists_prePolygon_arcs`, `…exists_prePolygon_arcs_oriented` — §1, the realization
  theorem **with the cut points anywhere on the curve**, tracking a prescribed splitting.
  Compare `Schoenflies.exists_closedPolygon_arcs`, which requires the cut points to be corners.
* `Schoenflies.IsPrePolygonalCrosscut` and its API up to
  `…alternating_inter_nonempty_of_same_side` — `thm:polygonal-crosscut` and
  `cor:alternating-crosscuts` in the blueprint's own generality: the split points need not be
  corners.
* `Graph.IsPreHexCrosscut`, `Graph.IsK33Config.isPreHexCrosscut` — the six-cycle of a polygonally
  drawn `K(3,3)`, cut at the two ends of one remaining edge, as such a crosscut. **This is what
  `Graph.IsHexRealization` was assuming, and it is proved here.**
* `Graph.IsK33Config.false_of_isPreHexCrosscut`, `…false_of_polygonal`,
  `Graph.IsK33Config.not_exists_isDrawing` — `lem:k33`.
* `Graph.IsArcK33.elim`, `Graph.IsK33Subdivision.elim` — `cor:k33-subdivision`.
* `Graph.k33Graph_not_exists_isDrawing` — `lem:k33` for the concrete graph.

## A note on names, for the integrator

The direct statements use eliminator-style names because the realization-parametric lemmas are
still in the import closure:

| realization-parametric lemma                      | direct theorem                             |
|---------------------------------------------------|--------------------------------------------|
| `Graph.IsK33Config.not_isDrawing` (K33Planar)      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsK33Config.not_isDrawing_of_bendable`      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsArcK33.false_of_realization`/`_bendable`  | `Graph.IsArcK33.elim`                      |
| `Graph.IsK33Subdivision.false_of_realization`/`…`  | `Graph.IsK33Subdivision.elim`              |
| `Graph.k33Graph_not_isDrawing`                     | `Graph.k33Graph_not_exists_isDrawing`      |

With this module in place `Graph.IsHexRealization`, `Graph.IsHexCrosscut`, `Graph.IsHexGeneric`
and `Graph.Bendable` have no consumers left.
-/

open Bornology Metric Set unitInterval
open scoped Graph

namespace Schoenflies

open Plane

/-! ## The realization theorem, tracking a prescribed splitting

`Schoenflies.exists_prePolygon_split` of `Schoenflies/PrePolygonArc.lean` presents the curve with
the two cut points among its vertices, with no corner condition on them. What remains is to say
*which* arc of that presentation is which of two prescribed arcs, and in which direction the
first is traversed. -/

/-- **The realization theorem, tracking a splitting into two named arcs.** -/
theorem exists_prePolygon_arcs {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      ((P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂) ∨
        (P.arc a k = A₂ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₁)) := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ := exists_prePolygon_split hJ hP hp hq hpq
  refine ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, ?_⟩
  have hD1 : IsArcBetween (P.arc a k) p q := by
    rw [← hpa, ← hqa]; exact P.isArcBetween_arc a hk1 hk2
  have hD2 : IsArcBetween (P.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    have h := P.isArcBetween_arc (a + (k : ZMod (m + 3))) (k := m + 3 - k) (by omega) (by omega)
    rw [zmod_add_sub_cancel (by omega) a] at h
    rw [← hpa, ← hqa]
    exact h.reverse
  have hDunion : P.arc a k ∪ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = C := by
    rw [P.arc_union a (by omega), hcar]
  have hDinter : P.arc a k ∩ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [P.arc_inter a hk1 hk2, hpa, hqa]
  rcases two_arcs_unique hunion hinter hDunion hDinter hA1 hA2 hD1 hD2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨e1.symm, e2.symm⟩
  · exact Or.inr ⟨e2.symm, e1.symm⟩

/-- **The realization of a splitting, with both the arcs and the direction fixed.** The two arcs
come out in the order they were given *and* the first is traversed from `p` to `q`; reading the
polygon backwards when it is not is what pins the direction.

This is the shape the crosscut wiring consumes, and — unlike
`Schoenflies.exists_closedPolygon_arcs_oriented` — it asks nothing of `p` and `q` beyond lying on
the curve. -/
theorem exists_prePolygon_arcs_oriented {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ := by
  obtain ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, hcase⟩ :=
    exists_prePolygon_arcs hJ hP hp hq hpq hA1 hA2 hunion hinter
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, e1, e2⟩
  · -- The realization runs the two arcs the other way round: read it backwards.
    have hneg : ((m + 3 - k : ℕ) : ZMod (m + 3)) = -(k : ZMod (m + 3)) := by
      linear_combination zmod_add_sub_cancel (m := m) (k := k) (by omega) 0
    refine ⟨m, P.reverse, -a, m + 3 - k, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [PrePolygon.reverse_carrier]; exact hcar
    · rw [PrePolygon.reverse_vertex, neg_neg]; exact hpa
    · rw [PrePolygon.reverse_vertex, hneg,
        show -(-a + -(k : ZMod (m + 3))) = a + (k : ZMod (m + 3)) by ring]
      exact hqa
    · have h := P.reverse_arc (a + (k : ZMod (m + 3))) (m + 3 - k)
      rw [hneg, show -(a + (k : ZMod (m + 3))) - -(k : ZMod (m + 3)) = -a by ring] at h
      rw [h]; exact e2
    · have h := P.reverse_arc a k
      rw [show m + 3 - (m + 3 - k) = k by omega, hneg,
        show -a + -(k : ZMod (m + 3)) = -a - (k : ZMod (m + 3)) by ring, h]
      exact e1

/-! ## Theorem 2.8 and Corollary 2.9 for a polygon presented with redundant vertices

`Schoenflies.IsPolygonalCrosscut` is stated for `ClosedPolygon`s, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that pins the two cut points to be *corners* of the
curve. Nothing in the proof of Theorem 2.8 needs the `corner` field: what it uses of `C`, `J₁`,
`J₂` is that their carriers separate the plane and that their crossing counts are the ones the
edge lists compute. `Schoenflies/PrePolygonSep.lean` supplies both for a `PrePolygon`, so the
whole chain goes through with the cut points anywhere on the curve. -/

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s : Fin 3} {R : Set Plane}

/-! ## The six-cycle and one remaining edge, as a crosscut

`Graph.IsHexCrosscut` of `Schoenflies/Graph/K33Planar.lean` is the same statement with
`Schoenflies.ClosedPolygon` for `Schoenflies.PrePolygon`; the change is what removes the corner
condition on the two cut points, which is the whole of the remaining gap. -/

namespace IsK33Config

/-- **The crosscut exists for any polygonal drawing.** The six-cycle is
realized as a `Schoenflies.PrePolygon` cut at the two ends of the remaining edge — possible
because a `PrePolygon` may have a vertex wherever one likes — and the two closed curves the
remaining edge forms with the two halves are then *built* from that realization and from one
presentation of the remaining edge, rather than found independently. That is what makes the three
edge lists agree, and it is why no matching lemma, and hence no general position, is needed. -/
theorem isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPreHexCrosscut drawing e s := by
  have hpq : x s ≠ y (s + 1) := h.x_ne_y s (s + 1)
  have hA1 := h.arcA_isArcBetween hd s
  have hA2 := h.arcB_isArcBetween hd s
  have hCh := hd.edge_isArcBetween (h.isLink s (s + 1))
  have hinterA := h.chord_inter_arcA hd s
  have hinterB := h.chord_inter_arcB hd s
  have hPch : IsPolygonal (edgeArc drawing (e s (s + 1))) :=
    hpoly _ (h.isLink s (s + 1)).edge_mem
  have hP1 : IsPolygonal (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    (h.isPolygonal_arcA hd hpoly s).union hPch ⟨x s, hA1.left_mem, hCh.left_mem⟩
  have hJ1 : IsJordanCurve (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA1 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterA ▸ ⟨hz1, hz2⟩
      simpa using hz
  -- The six-cycle, cut at the two ends of the remaining edge.
  obtain ⟨m, C, a, k, hCcar, hk1, hk2, hCa, hCak, hCarc1, hCarc2⟩ :=
    exists_prePolygon_arcs_oriented (h.hexagon_isJordanCurve hd) (h.isPolygonal_hexSet hd hpoly)
      (h.x_mem_hexSet hd s) (h.y_mem_hexSet hd (s + 1)) hpq hA1 hA2
      (arcs_union (drawing := drawing) (e := e) s) (h.arcs_inter hd s)
  -- The remaining edge, as the second arc of the curve it forms with the first half.
  obtain ⟨m₁, D, b, l, -, hl1, hl2, hDb, hDbl, hDarc1, hDarc2⟩ :=
    exists_prePolygon_arcs_oriented hJ1 hP1 (Or.inl hA1.left_mem) (Or.inl hA1.right_mem) hpq
      hA1 hCh rfl hinterA
  set c : ZMod (m₁ + 3) := b + (l : ZMod (m₁ + 3)) with hc
  set r : ℕ := m₁ + 3 - l with hr
  have hwrapD : c + (r : ZMod (m₁ + 3)) = b := zmod_add_sub_cancel (by omega) b
  have hDc : D.vertex c = y (s + 1) := hDbl
  have hDcr : D.vertex (c + (r : ZMod (m₁ + 3))) = x s := by rw [hwrapD]; exact hDb
  have hKcover : cover (D.arcPieces c r) = edgeArc drawing (e s (s + 1)) := hDarc2
  have hKinter : C.arc a k ∩ D.arc c r
      = ({C.vertex a, C.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc1, hDarc2, hCa, hCak]; exact hinterA
  -- The first spliced curve: the first half of the six-cycle, then the remaining edge.
  obtain ⟨n₁, J₁, hJ₁p⟩ := PrePolygon.exists_splice C D hk1 hk2 (by omega) (by omega)
    (by rw [hDc, hCak]) (by rw [hDcr, hCa]) hKinter
  -- The second spliced curve, with the remaining edge traversed the other way.
  have hwrapC : a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a :=
    zmod_add_sub_cancel (by omega) a
  set c' : ZMod (m₁ + 3) := -c - (r : ZMod (m₁ + 3)) with hc'
  have hDrev1 : D.reverse.vertex c' = x s := by
    rw [PrePolygon.reverse_vertex, hc', show -(-c - (r : ZMod (m₁ + 3))) = c + (r : ZMod (m₁ + 3))
      by ring]
    exact hDcr
  have hDrev2 : D.reverse.vertex (c' + (r : ZMod (m₁ + 3))) = y (s + 1) := by
    rw [PrePolygon.reverse_vertex, hc',
      show -(-c - (r : ZMod (m₁ + 3)) + (r : ZMod (m₁ + 3))) = c by ring]
    exact hDc
  have hKinter' : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∩ D.reverse.arc c' r
      = ({C.vertex (a + (k : ZMod (m + 3))),
          C.vertex (a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc2, hc', D.reverse_arc c r, hDarc2, hwrapC, hCa, hCak, Set.pair_comm]
    exact hinterB
  obtain ⟨n₂, J₂, hJ₂p⟩ := PrePolygon.exists_splice C D.reverse (a := a + (k : ZMod (m + 3)))
    (k := m + 3 - k) (b := c') (l := r) (by omega) (by omega) (by omega) (by omega)
    (by rw [hDrev1, hwrapC, hCa]) (by rw [hDrev2, hCak]) hKinter'
  -- The reference point, and the two "meets" clauses.
  have hsep : IsSeparating (hexSet drawing e) := hCcar ▸ C.isSeparating_carrier
  obtain ⟨yref, hyref, hdisj⟩ := h.exists_reference_point hd hsep s
  refine ⟨m, n₁, n₂, C, J₁, J₂, D.arcPieces c r, a, k, yref, hCcar, hCarc1, hCarc2, hKcover,
    ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hJ₁p]
  · rw [hJ₂p]
    exact SameEdges.append (SameEdges.refl _) (D.sameEdges_reverse_arcPieces c r)
  · rw [hKcover, hCcar, hCarc1, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcA hd s
  · rw [hKcover, hCcar, hCarc2, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcB hd s
  · rw [hCcar]; exact hyref
  · rw [hKcover, hCcar]; exact hdisj

/-! ### The contradiction -/

/-- **`lem:k33` for a drawing that is already polygonal, with nothing assumed.** -/
theorem false_of_polygonal (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) : False := by
  have hsep : IsSeparating (hexSet drawing e) := by
    obtain ⟨_, _, _, C, _, _, _, _, _, _, hcar, _⟩ := h.isPreHexCrosscut hd hpoly 0
    exact hcar ▸ C.isSeparating_carrier
  obtain ⟨s, t, hst, R, hR, h1, h2⟩ := h.exists_two_chords_same_region hd hsep
  have hpair : ∀ s t : Fin 3, s ≠ t → t = s + 1 ∨ s = t + 1 := by decide
  rcases hpair s t hst with rfl | rfl
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly s) hsep hR h1 h2
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly t) hsep hR h2 h1

/-- **Lemma 3.10 (nonplanarity of `K(3,3)`), with no hypothesis left.** A finite graph carrying a
copy of `K(3,3)` has no plane drawing.

`lem:polygonal-redrawing` replaces an arbitrary drawing by a polygonal one on the same graph and
the same vertices; the contradiction is then `false_of_polygonal`. This is
`Graph.IsK33Config.not_isDrawing` of `Schoenflies/Graph/K33Planar.lean` with its realization
hypothesis discharged, and `Graph.IsK33Config.not_isDrawing_of_bendable` of
`Schoenflies/Graph/K33Closed.lean` with `Graph.Bendable` discharged: no drawing has to be bent,
because the crosscut no longer needs the six vertices to be corners. -/
theorem not_exists_isDrawing [G.Finite] (h : IsK33Config G x y e) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly'⟩ := polygonal_redrawing G dr hdr
  exact h.false_of_polygonal hdr' hpoly'

end IsK33Config

/-- **`lem:k33` for nine arcs**: no nine arcs in the plane meet only where a
`K(3,3)` forces them to. -/
theorem IsArcK33.elim {P : Fin 3 → Fin 3 → Set Plane} (h : IsArcK33 x y P) : False :=
  h.isK33Config.not_exists_isDrawing ⟨h.arcDrawing, h.isDrawing⟩

end Graph
end

section
-- module Solutions.Q146_CD.JordanSeparates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A Jordan curve separates the plane

Half of the Jordan curve theorem: the complement of a Jordan curve `C` is disconnected. The
proof is the blueprint's — build a subdivision of `K(3,3)` out of the curve, a chord of it, a
detour above it, and a connecting arc, and appeal to `Graph.IsArcK33.elim`.

## The configuration

Fix a coordinate `i` in which `C` has nonzero width, and let `j` be the other one. Write `m`
and `M` for the extreme `i`-coordinates on `C`, and let `p₁`, `p₂` be the points of `C` on the
two supporting lines `{z | z i = m}`, `{z | z i = M}` with the largest `j`-coordinate. Two
points of a Jordan curve cut it into two arcs `C₁`, `C₂` (`IsJordanCurve.two_arcs`). Both meet
the middle line `{z | z i = (m + M) / 2}`, by the intermediate value theorem; a closest pair
`a ∈ C₁`, `b ∈ C₂` on that line spans a segment `L₄` whose interior misses `C`. Running up the
two supporting lines and across above the curve gives a polygonal set meeting `C` exactly in
`{p₁, p₂}` and missing `L₄`; a simple arc `L₅` inside it (`exists_simple_poly_of_poly`) is the
blueprint's detour.

The blueprint argues inside the unbounded component: it supposes `L₄ \ {a, b}` to lie there,
and concludes that it does not. Here the contradiction hypothesis is the statement being
negated — that the whole complement is preconnected — which is weaker to assume and gives the
same `K(3,3)`. Nothing about the unbounded component is needed, so nothing about it is proved;
`exists_unique_unbounded_connectedComponentIn_compl` at the end is the separate cheap fact.

*If* the complement were preconnected, a simple polygonal arc `R` inside it would join an
interior point of `L₄` to an interior point of `L₅`. Its last parameter on `L₄` and the first
one after that on `L₅` cut out a piece `L₆` meeting `L₄ ∪ L₅` only at its two ends — this is
why the blueprint takes such care over the order in which `c'` and `d'` are chosen. Cutting
`C₁` at `a`, `C₂` at `b`, `L₅` at the far end `d'` of `L₆` and `L₄` at its near end `c'`
produces nine arcs on the six points `{p₁, p₂, c'}`, `{a, b, d'}`, meeting only where a
`K(3,3)` forces them to. That is impossible, so the complement is not preconnected.

## Coordinates instead of a rotation

The blueprint rotates so that the direction of nonzero width becomes horizontal. Here the two
coordinate indices are carried as parameters `i ≠ j` of `not_isPreconnected_compl_of_coord`
instead, and the headline theorem picks whichever pair works. No rotation, no trigonometry and
no coordinate-swap symmetry lemma is needed: every step is symmetric in the two indices except
for which one is named.

The blueprint's opening step — a Jordan curve is not contained in a line — is not needed in
this form. All it is used for is a direction of nonzero width, and that follows from the curve
having two distinct points (`IsJordanCurve.exists_ne`). The degenerate configurations the
blueprint's step rules out are excluded downstream instead, by `C₁ ∩ C₂ = {p₁, p₂}`.

## Blueprint

* `Schoenflies.not_isPreconnected_compl_of_coord`,
  `Schoenflies.IsJordanCurve.not_isPreconnected_compl`,
  `Schoenflies.IsJordanCurve.exists_connectedComponentIn_ne` — `prop:jordan-disconnected`.
* `Schoenflies.exists_unique_unbounded_connectedComponentIn_compl` — the opening sentence of
  the blueprint's Jordan section: the complement of a compact set has exactly one unbounded
  component.
* `Graph.isArcK33_of_pieces` — the packaging of `cor:k33-subdivision` (through
  `Graph.IsArcK33.elim`) that this configuration fits.
* `Schoenflies.IsArcBetween.exists_split` — an arc cut at an interior point; the arc analogue
  of the second clause of `lem:jordan-circle`, which `Schoenflies.IsJordanCurve.two_arcs` is.

## For the integrator

Three groups of declarations here are general and have no home yet on `main`:

* `Schoenflies.Plane.coord_ext`, `axisVec`, `setCoord`, `coord_eq_of_mem_segment`,
  `le_coord_of_mem_segment`, `coord_le_of_mem_segment` belong beside the coordinate
  half-planes in `Schoenflies/Square.lean`.
* `Schoenflies.IsArcBetween.exists_split` belongs in `Schoenflies/Subarc.lean`, next to
  `IsArc.exists_isArcBetween_subset`; `Schoenflies.injective_three` is a `Fin 3` triviality.
* `Graph.isArcK33_of_pieces` belongs in `Schoenflies/Graph/K33Planar.lean`, next to
  `Graph.IsArcK33`.
-/

open Metric Set unitInterval

namespace Schoenflies

namespace Plane

/-- The unit vector along the coordinate axis `j`. -/
noncomputable def axisVec (j : Fin 2) : Plane :=
  mk (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)

@[simp] theorem axisVec_self (j : Fin 2) : axisVec j j = 1 := by
  fin_cases j <;> simp [axisVec]

/-- The point obtained from `z` by moving its `j`-th coordinate to `t` and leaving the other
coordinate where it was. This is how the two upper corners of the polygonal detour above the
curve are named without committing to which of the two coordinates is the horizontal one. -/
noncomputable def setCoord (z : Plane) (j : Fin 2) (t : ℝ) : Plane :=
  z + (t - z j) • axisVec j

@[simp] theorem setCoord_self (z : Plane) (j : Fin 2) (t : ℝ) : setCoord z j t j = t := by
  simp [setCoord]

/-! ### Coordinates along a segment -/

end Plane

/-! ### Cutting an arc at an interior point -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolyArcRealize
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing a simple polygonal arc as a `PolyArc`

`Schoenflies/ArcCollars.lean` proves blueprint Lemma 1.8 (b) — the two-sided collar of an arc,
hence `Schoenflies.HasArcCollars` — for an arc *presented by its vertex list*, a
`Schoenflies.PolyArc`, and carries the presentation itself as the hypothesis
`Schoenflies.IsPolyArcCarrier`. Nothing on `main` could supply that hypothesis for anything but
a straight segment, so `lem:crosscut-at-most-two` and `thm:general-crosscut` were not in fact
unblocked. This module closes the gap: a set that is both an arc between two points and
polygonal *is* the carrier of a `PolyArc`.

This is the arc analogue of `Schoenflies.exists_closedPolygon`, and the route is the one
`Schoenflies/Realization.lean` takes in the closed case, on a linear index instead of a cyclic
one. The closed-case machinery is reused verbatim wherever it does not mention the loop.

## The three steps

1. **Cut the point set into pieces.** `Schoenflies.exists_isClean` gives a finite list `Q` of
   nondegenerate segments occupying `P`, with pairwise disjoint interiors and no end interior to
   any of them; the two endpoints `a`, `b` of the arc are put on the cut list, so both are ends
   of pieces.
2. **Order the pieces along the arc.** The parametrisation `f` reaches an end of a piece at
   finitely many parameters; listed in increasing order they cut `[0, 1]` into gaps. A gap image
   is connected and misses the ends, so it lies in one piece interior; the interior is connected
   and covered by the closed gap images, so it lies in that one gap. Gaps and pieces correspond
   one to one and the ends, in the order `f` reaches them, are a *linear* vertex list.

   The only change from the closed case is bookkeeping at the far end. There the loop returns to
   `f 0`, so the parameters live in `[0, 1)` and the last gap wraps; here `f 1 = b` is a genuine
   extra vertex. Taking the parameter set to be `{t ∈ [0, 1) | f t` is an end of a piece`}` —
   *exactly* the set `Schoenflies/Realization.lean` uses — makes `Schoenflies.parNext` of the
   last index equal `1` by definition, which is precisely the missing right end. So
   `Schoenflies.par`, `Schoenflies.parNext` and `Schoenflies.exists_mem_gap` are used unchanged,
   and `n` parameters give `n` edges and `n + 1` vertices.
3. **Delete redundant vertices.** `Schoenflies.PreArc` is a `PolyArc` less its `corner` field,
   and `Schoenflies.PreArc.deleteVertex` removes one vertex at which the two edges are
   collinear. Each deletion shortens the list by one, so the induction terminates; unlike the
   cyclic case it can never get stuck, because a one-edge arc satisfies `corner` vacuously.

## Why the arc is not closed into a curve first

The tempting shortcut is to join `b` back to `a` by one extra polygonal path far from the arc,
apply `Schoenflies.exists_closedPolygon_arcs` to the resulting Jordan curve, and read the arc off
the cyclic list. It is circular. The return path has to meet `P` only at `a` and `b`, so it has
to leave `a` in a direction along which the arc does not run; knowing that there *is* such a
direction — that `P` is locally one segment at `a` — is a consequence of the realization, not an
input to it. A *straight* segment from `b` to `a` will not do either: an arc can perfectly well
cross the chord joining its endpoints. And avoiding `P` in the large needs `ℝ² ∖ P` connected,
which is `thm:arc-complement`, stated there with an explicit hypothesis. Route (A) below needs
none of this.

## Padding the vertex list

`PolyArc.vertex` is a function on all of `ℕ` asked to be *globally* injective — the convention
its docstring records, which supplies `A.tang i` and `A.len i` directly. A realization
produces `n + 1` vertices and nothing beyond, so the list has to be padded.
`Schoenflies.exists_injective_extend` does it once and for all, by walking off along the first
coordinate past every value the finite list takes.

## Blueprint

There is no blueprint label for this statement: like the closed-curve realization theorem of
`Schoenflies/Realization.lean` it is the bridge the blueprint takes for granted when it says
"let `P` be a simple polygonal arc with vertices `v_0, …, v_{n+1}`". Its consumers are
`lem:polygonal-collar` (b) and, through it, `lem:crosscut-at-most-two` and
`thm:general-crosscut`.

* `Schoenflies.exists_injective_extend` — a finite injective vertex list extends to an injective
  sequence.
* `Schoenflies.PreArc` — a `PolyArc` less the `corner` field: a simple polygonal arc presented by
  a vertex list, redundant vertices allowed. The arc analogue of `Schoenflies.PrePolygon`.
* `Schoenflies.skipIdx`, `Schoenflies.PreArc.deleteVertex`,
  `Schoenflies.PreArc.carrier_deleteVertex` — the blueprint's "delete redundant vertices at which
  two consecutive edges are collinear", as an operation. The arc analogue of
  `Schoenflies.PrePolygon.deleteLast`, and simpler: with a linear index no rotation is needed, so
  the vertex to be deleted stays where it is.
* `Schoenflies.PreArc.exists_polyArc` — the deletion run to completion. The arc analogue of
  `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`.
* `Schoenflies.exists_preArc_of_isArcBetween` — steps 1 and 2: a set-level simple polygonal arc
  is the carrier of a vertex list. The arc analogue of
  `Schoenflies.exists_prePolygon_of_isJordanCurve`.
* `Schoenflies.isPolyArcCarrier_of_isPolygonal` — **the realization theorem for arcs**, and the
  discharge of `Schoenflies.IsPolyArcCarrier`.
* `Schoenflies.hasArcCollars_of_isPolygonal` — blueprint Lemma 1.8 (b) for a set-level simple
  polygonal arc, with nothing left standing.
* `Schoenflies.IsCrosscut.hasArcCollars`, `Schoenflies.crosscut_at_most_two_of_isPolygonal` — the
  same at the call site of `thm:general-crosscut`.
-/

open Metric Set unitInterval

namespace Schoenflies

open Plane

/-! ## Padding a finite vertex list to an injective sequence

`PolyArc` asks for a globally injective `vertex : ℕ → Plane`; a realization only produces
`n + 2` points. The padding walks off along the first coordinate, past every value the finite
part takes, which keeps the extension injective and disjoint from the finite part. -/

/-! ## The index map of a deletion

On a linear index there is nothing to rotate: a vertex is deleted where it stands, and `skipIdx i`
is the inclusion of the shortened index set into the old one — the identity up to `i`, a shift by
one beyond it. It is the arc analogue of `Schoenflies.PrePolygon.emb`, and much simpler, because
that one has to wrap. -/

/-! ## Arcs before normalization

`PreArc` is `PolyArc` with the `corner` field removed, exactly as `Schoenflies.PrePolygon` is
`Schoenflies.ClosedPolygon` with it removed. Realization produces one of these; normalization
turns it into a `PolyArc`. -/

/-- A simple polygonal arc presented by its vertex list, with redundant vertices allowed:
`Schoenflies.PolyArc` less its `corner` field. -/
structure PreArc (n : ℕ) where
  /-- The vertices, in order along the arc. Only `vertex 0, …, vertex (n + 1)` are on it. -/
  vertex : ℕ → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}

namespace PreArc

variable {n i j k : ℕ}

/-- Edge `i` of the arc. -/
def edge (A : PreArc n) (i : ℕ) : Set Plane := segment ℝ (A.vertex i) (A.vertex (i + 1))

variable {A : PreArc n}

theorem vertex_ne : A.vertex i ≠ A.vertex (i + 1) := fun h => by
  have := A.vertex_inj h; omega

/-! ### Deleting a redundant vertex

The blueprint's opening move in the strip lemma, "delete redundant vertices at which two
consecutive edges are collinear", as an operation rather than an invariant. -/

/-- **A redundant vertex is interior to the segment joining its neighbours**, so the two edges
at it merge into a single one. This is `Schoenflies.PrePolygon.mem_openSegment_of_det_eq_zero'`
read on a linear index. -/
theorem edge_union_of_det_eq_zero (A : PreArc n) (hi : i < n)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    segment ℝ (A.vertex i) (A.vertex (i + 1 + 1)) = A.edge i ∪ A.edge (i + 1) :=
  segment_split (openSegment_subset_segment ℝ _ _
    (PrePolygon.mem_openSegment_of_det_eq_zero' vertex_ne
      (fun h => by have := A.vertex_inj h; omega)
      (A.edges_meet i (by omega) (i + 1) (by omega) (by omega)) hdet))

/-- The middle vertex of a merge lies on no other edge: it is an end of edge `i`, and an edge
meeting edge `i` there would have it as one of its own ends. -/
theorem vertex_notMem_edge (A : PreArc n) (hi : i < n) (hk : k ≤ n) (hk1 : k ≠ i)
    (hk2 : k ≠ i + 1) : A.vertex (i + 1) ∉ A.edge k := by
  intro hmem
  have h := A.edges_meet k hk i (by omega) hk1 ⟨hmem, right_mem_segment ℝ _ _⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> exact absurd (A.vertex_inj h) (by omega)

/-- **The shortened vertex list is still simple.** The merged edge is the union of the two it
replaces, and the only point that could escape the two-point bound — the deleted vertex — lies
on no other edge. -/
theorem skip_edges_meet (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    ∀ j ≤ n, ∀ k ≤ n, j ≠ k →
      segment ℝ (A.vertex (skipIdx i j)) (A.vertex (skipIdx i (j + 1))) ∩
          segment ℝ (A.vertex (skipIdx i k)) (A.vertex (skipIdx i (k + 1))) ⊆
        {A.vertex (skipIdx i j), A.vertex (skipIdx i (j + 1))} := by
  -- Away from `i` the new edge is an old one; at `i` it is the union of two old ones.
  have hplain : ∀ l, l ≠ i →
      segment ℝ (A.vertex (skipIdx i l)) (A.vertex (skipIdx i (l + 1))) = A.edge (skipIdx i l) :=
    fun l hl => by rw [skipIdx_succ hl]; rfl
  have hmerge : segment ℝ (A.vertex (skipIdx i i)) (A.vertex (skipIdx i (i + 1)))
      = A.edge i ∪ A.edge (i + 1) := by
    rw [skipIdx_of_le (le_refl i), skipIdx_of_lt (Nat.lt_succ_self i)]
    exact A.edge_union_of_det_eq_zero hi hdet
  have hle : ∀ l ≤ n, skipIdx i l ≤ n + 1 := by
    intro l hl; simp only [skipIdx]; split_ifs <;> omega
  intro j hj k hk hjk z hz
  by_cases hji : i = j
  · -- The merged edge on the left: the deleted vertex has to be ruled out by hand.
    subst hji
    have hk1 : skipIdx i k ≠ i := skipIdx_ne_left (Ne.symm hjk)
    have hk2 : skipIdx i k ≠ i + 1 := skipIdx_ne_right i k
    rw [skipIdx_of_le (le_refl i), skipIdx_of_lt (Nat.lt_succ_self i)]
    have hzk : z ∈ A.edge (skipIdx i k) := by
      rw [← hplain k (Ne.symm hjk)]; exact hz.2
    have hzj : z ∈ A.edge i ∪ A.edge (i + 1) := hmerge ▸ hz.1
    rcases hzj with hzj | hzj
    · have h := A.edges_meet i (by omega) (skipIdx i k) (hle k hk) (Ne.symm hk1) ⟨hzj, hzk⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact absurd (h ▸ hzk) (A.vertex_notMem_edge hi (hle k hk) hk1 hk2)
    · have h := A.edges_meet (i + 1) (by omega) (skipIdx i k) (hle k hk)
        (fun he => hk2 he.symm) ⟨hzj, hzk⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
      rcases h with h | h
      · exact absurd (h ▸ hzk) (A.vertex_notMem_edge hi (hle k hk) hk1 hk2)
      · exact Or.inr h
  · -- An untouched edge on the left: the bound is one instance of `edges_meet`.
    have hji' : j ≠ i := fun he => hji he.symm
    rw [skipIdx_succ hji']
    have hzj : z ∈ A.edge (skipIdx i j) := (hplain j hji') ▸ hz.1
    by_cases hki : i = k
    · subst hki
      have hj1 : skipIdx i j ≠ i := skipIdx_ne_left hji'
      have hj2 : skipIdx i j ≠ i + 1 := skipIdx_ne_right i j
      rcases (hmerge ▸ hz.2 : z ∈ A.edge i ∪ A.edge (i + 1)) with hzk | hzk
      · exact A.edges_meet (skipIdx i j) (hle j hj) i (by omega) hj1 ⟨hzj, hzk⟩
      · exact A.edges_meet (skipIdx i j) (hle j hj) (i + 1) (by omega) hj2 ⟨hzj, hzk⟩
    · have hki' : k ≠ i := fun he => hki he.symm
      have hzk : z ∈ A.edge (skipIdx i k) := (hplain k hki') ▸ hz.2
      exact A.edges_meet (skipIdx i j) (hle j hj) (skipIdx i k) (hle k hk)
        (fun he => hjk (skipIdx_injective i he)) ⟨hzj, hzk⟩

/-- **The vertex list with a redundant vertex deleted.** -/
def deleteVertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    PreArc n where
  vertex k := A.vertex (skipIdx i k)
  vertex_inj := A.vertex_inj.comp (skipIdx_injective i)
  edges_meet := A.skip_edges_meet hi hdet

@[simp] theorem deleteVertex_vertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0)
    (k : ℕ) : (A.deleteVertex hi hdet).vertex k = A.vertex (skipIdx i k) := rfl

end PreArc

/-! ## From a clean presentation to a linear vertex list

The arc reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the arc reaches them, are the vertex list
of a `PreArc` whose edges are the pieces.

The parameter set is taken inside `[0, 1)`, exactly as in the closed case, so that
`Schoenflies.parNext` of the last index is `1` by definition. That is not a trick: `f 1 = b` is
the last vertex, and this is what puts it there. Both `a` and `b` are forced onto the cut list,
which is what makes `0` a parameter and `b` an end of a piece. -/

/-! ## The realization theorem for arcs

Realization followed by normalization. This is the statement
`Schoenflies/ArcCollars.lean` names at the end of its file as the one thing it does not prove. -/

/-! ## The collar hypothesis at the call site of `thm:general-crosscut`

`Schoenflies.IsCrosscut` carries exactly what the discharge needs: `P` is an arc from `p` to `q`,
`P` is polygonal, and `P ∖ {p, q}` lies in `inside C`, whose openness comes from the curve being
closed. So `hcollars` is never again a hypothesis of the crosscut theorem — only `thm:jordan`
is. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.RefinementStars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Carriers, refinement compatibility, and the star lemmas

The interface between the *construction* of the nested cellulations and the *abstraction* the
limit homeomorphism uses. The blueprint says at the head of that section (tex, "The limit
homeomorphism of the interiors") that it "forgets how the decompositions were constructed and
uses only their nesting, matching, and shrinking properties"; everything below is therefore
stated for an abstract refinement relation `Realization.Refines` between two realizations of two
generated structures, and *not* for either elementary constructor. The two constructors enter
only at the very end, as the two theorems that produce a `Refines` from them.

## The carrier is a function

`Realization.carrier` is `car_Γ(x)` of the blueprint, exported as a total function `Plane → γ`
rather than as an existential: `σ_n(x)` is used on every line of the limit argument. Outside the
closed domain it is junk (whence the `[Nonempty γ]`), and every lemma about it carries the
hypothesis `x ∈ D` that makes it meaningful. Its characterising property is
`IsCellDecomposition.carrier_eq`: *any* cell whose open part contains `x` is the carrier.

## What `Refines` is, and why it is the right shape

`R'.Refines R par` says: `par` maps cells of the finer structure to cells of the coarser one and
2-cells to 2-cells, it is compatible with `≼_abs` (assertion (iv) of `lem:cellulation-invariants`),
and each *open* cell of the finer realization sits inside the open cell of its parent. The last
clause is the geometric content of the blueprint's proof of
`lem:refinement-compatibility`(a) — "a point in either new subedge or at the new vertex
had the old open edge as its old carrier" — and it implies the weaker
`closure (R'.cell σ) ⊆ closure (R.cell (par σ))` that part (b) needs.

`Refines` is a relation between two realizations of two *different* abstract structures over the
same name type `γ`, parametrised by the composite parent map. `Refines.trans` composes them, so
"a finite sequence of elementary refinements" needs no separate treatment: a consumer that builds
its stages one operation at a time gets the composite by iterating `trans`.

Part (c) of `lem:refinement-compatibility` — "corresponding cells have corresponding parents" —
is, under the representation of `CombinatorialInvariance.lean`, the statement that *one and the
same* `par : γ → γ` serves both realizations: cells are abstract names, and two `Refines`
instances sharing a `par` is exactly a compatible matched refinement. There is nothing to
transport, and the substance of (c) is its consequence, `Refines.carrier_congr`.

## Blueprint

* `Schoenflies.CellStructure.Realization.carrier` — `car_Γ(x)`, with
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.carrier_eq` its characterisation.
* `Schoenflies.CellStructure.Realization.Refines` — a refinement of one generated matched cell
  structure by another, with `Refines.trans` for a finite sequence of them.
* `lem:refinement-compatibility`:
  * (a) `Schoenflies.CellStructure.Realization.Refines.parent_carrier`;
  * (b) `Schoenflies.CellStructure.Realization.Refines.star_subset` (cells) and
    `Schoenflies.CellStructure.Realization.Refines.star_carrier_subset` (points);
  * (c) `Schoenflies.CellStructure.SkeletonHomeo.carrier_congr` (corresponding *skeleton points*
    have corresponding carriers, via
    `Schoenflies.CellStructure.SkeletonHomeo.image_cell`),
    `Schoenflies.CellStructure.Realization.Refines.carrier_congr` (and then at every earlier
    stage), and the form the limit argument actually cites,
    `Schoenflies.CellStructure.Realization.Refines.target_star_subset` (`T_{n+1}(x) ⊆ T_n(x)`).
* `lem:star-intersection` — `Schoenflies.CellStructure.Realization.star_inter_nonempty_congr`.
* `lem:star-face-mesh` — `Schoenflies.CellStructure.Realization.IsCellDecomposition.star_eq_faces`,
  with (a) `…diam_star_le`, `…diam_star_lt`, `…diam_star_carrier_lt` and (b)
  `Schoenflies.CellStructure.Realization.Refines.diam_cell_le`,
  `Schoenflies.CellStructure.Realization.Refines.diam_cell_le_of_forall`.
* `lem:cell-neighborhood` — `Schoenflies.CellStructure.Realization.cellNbhd` and
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.cell_neighborhood`.
* `rem:inductive-invariants` — honoured: nothing here is proved by a case check on the
  constructors. The inductive content lives in `GeneratedStructure.lean`; the two bridge theorems
  `Schoenflies.CellStructure.SubdivData.IsRefinement.refines` and
  `Schoenflies.CellStructure.SplitData.refines` are the only declarations that mention a
  constructor at all.

`Schoenflies.CellStructure.refines_of_elementary` is the shared bridge: both elementary
operations replace a single cell `c` by a set `N` of fresh cells and send `N` to `c`, so one
lemma serves both.
-/

open Set Metric Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace Realization

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-! ### Elementary facts about the closed star

`Realization.star` is the `St` of the blueprint and is defined in `CombinatorialInvariance.lean`;
these are the membership and containment lemmas its consumers need. -/

/-! ### The carrier of a point

`car_Γ(x)`, the unique open cell containing `x`. It is a total function; off the closed domain
its value is junk, and every lemma below supplies `x ∈ D`. -/

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-- Every open cell lies in the closed domain. -/
theorem cell_subset_domain (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) : R.cell σ ⊆ D := by
  rw [← h.iUnion_eq]
  exact Set.subset_biUnion_of_mem hσ

end IsCellDecomposition

/-! ### Refinement

The abstract relation "`R'` refines `R` with parent map `par`". It is deliberately not tied to
either elementary operation: the limit argument uses only these three clauses. -/

/-- **`R'` refines `R` along the parent map `par`.**

`R'` and `R` realize two different abstract structures over the same name type; `par` is the
composite parent map of `lem:cellulation-invariants`(iv). The three combinatorial
clauses say that `par` takes cells to cells, 2-cells to 2-cells, and respects `≼_abs`; the
geometric clause says that each *open* cell of the finer stage lies inside the open cell of its
parent, which is what makes carriers refine (part (a)). -/
structure Refines {S' S : CellStructure γ} (R' : S'.Realization) (R : S.Realization)
    (par : γ → γ) : Prop where
  /-- The parent of a cell is a cell. -/
  parent_mem_cells : ∀ ⦃σ⦄, σ ∈ S'.cells → par σ ∈ S.cells
  /-- The parent of a 2-cell is a 2-cell. -/
  parent_mem_faces : ∀ ⦃F⦄, F ∈ S'.faces → par F ∈ S.faces
  /-- **Assertion (iv)**: the parent map is compatible with the subcell relation. -/
  sub_parent : ∀ ⦃σ τ⦄, S'.sub σ τ → S.sub (par σ) (par τ)
  /-- Each open cell lies inside the open cell of its parent. -/
  cell_subset : ∀ ⦃σ⦄, σ ∈ S'.cells → R'.cell σ ⊆ R.cell (par σ)

/-! ### Matched refinements: part (c)

Two realizations of one abstract structure are matched; a *compatible matched refinement* is a
pair of `Refines` instances sharing one parent map. That sharing **is** the blueprint's
"corresponding cells have corresponding parents": the parent map is a map of abstract names, so
there is only ever one of it. The substance is the consequence recorded here. -/

/-! ### Intersection of corresponding stars -/

/-! ### Stars and the face mesh -/

/-! ### Finite cell neighborhoods -/

/-! ### Corresponding skeleton points

The second sentence of `lem:refinement-compatibility`(c). A point of the realized skeleton lies
in an open 0-cell or an open 1-cell, and the skeleton homeomorphism carries each of those onto
the open cell of the *same abstract name*; so corresponding skeleton points have carriers that
correspond, with nothing to transport. -/

end Realization

/-! ### The two elementary operations produce refinements

Both operations have the same shape: a single cell `c` is replaced by a set `N` of fresh cells,
and the parent map sends `N` to `c` and fixes everything else. `refines_of_elementary` proves the
geometric clause of `Refines` from that shape alone — the fresh cells must land inside `c`,
because any other cell of the old stage survives and is unmoved, and open cells of one stage are
disjoint. -/

/-! ### The interface, exercised

The limit homeomorphism opens with: "the sets `T_n(x)` are nonempty and compact … the cell-star
inclusion gives `T_{n+1}(x) ⊆ T_n(x)` … their diameters tend to zero … by
`lem:nested-compact` their intersection is one point". This anonymous example is a machine-checked
statement that the four facts that sentence needs come out of this module for an *abstract*
nested sequence: nothing below mentions how the stages were built, and the mesh hypothesis is
read in the target realization while the carrier is read in the source one. -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.CellulationInvariants
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The two cellulation invariants that need the crosscut theorem

`Schoenflies/GeneratedStructure.lean` proves seven of the nine assertions of
`lem:cellulation-invariants` — (ii), (iii), (iv), (v), (vi), (viii) and (ix), and (i) for the
edge-subdivision constructor. The two it leaves open are exactly the two whose induction step is
`thm:general-crosscut`:

* **(vii)** in each realization every 2-cell boundary is a Jordan curve and the open 2-cell is
  its bounded complementary region;
* **(i)** at the *split* constructor.

Both are proved here. `Schoenflies.crosscut_theorem` does not depend on `main`, and neither does
anything in this module.

## Realizations stay outside the inductive

`Schoenflies.GeneratedStructure` is purely abstract — it carries no realizations at all — while
(i), (vii), (viii) and (ix) are statements about realizations. `RefinementStars.lean` bridges
that by stating its lemmas for an arbitrary `Realization` satisfying `IsCellDecomposition`, and
this module follows the same pattern: the induction over the constructors is replaced by two
*step* theorems, one per constructor, each relating a realization of the refined structure to a
realization of the old one. A consumer building a sequence of stages carries the realizations
itself and applies the step theorem at each stage.

The alternative — realizations as fields of the inductive — was rejected for the reason
`RefinementStars.lean` gives: the limit argument "forgets how the decompositions were
constructed", so the abstract closure and the geometric invariants must be separable. It would
also force every consumer to commit to *two* realizations at the moment it builds an abstract
stage, which `thm:finite-transfer` does not do.

## What assertion (vii) is stated against, and why not the boundary walk

The blueprint phrases (vii) as "every 2-cell boundary **walk** is realized by a Jordan curve".
`CellStructure.boundary : γ → List γ` is a raw datum on which `CellStructure` imposes *no*
axiom whatever: nothing says `S.boundary F` is a closed walk, nothing ties it to `S.sub`, and
nothing ties it to `F`. A version of (vii) phrased against it therefore needs the separate
boundary-cycle invariant that the finite-transfer construction maintains.

So (vii) is stated against the cells: `Realization.faceBoundary F` is the union of the open
cells strictly below `F`, and `IsCellDecomposition.faceBoundary_eq_frontier` identifies it with
`frontier (R.cell F)` as soon as the open 2-cell is open. Assertion (vii) then reads: that
frontier is a Jordan curve, and `R.cell F` is its `inside`. This is the content every consumer
uses — (viii) needs only openness of the 2-cell, `lem:star-face-mesh` needs only the closed
2-cells, and the limit map needs `R.cell F = inside (…)`. Nothing downstream reads the cyclic
order of the walk.

## The orientation-aware update of `subdivideEdge`

`CellStructure.subdivideEdge` cannot compute a corrected boundary from an edge list alone: a
walk traverses `d.edge` in a definite direction, while the same interior edge occurs in the two
incident face boundaries with opposite orientations. `SubdivData` therefore carries the new
boundary lists as data, together with `SubstWalk` proofs that each list replaces the old closed
walk in the correct direction. `SubstWalk.isWalk` proves that every new boundary is again a
closed walk.

## Blueprint

* `Schoenflies.CellStructure.Realization.cellUnion`, `Schoenflies.CellStructure.subcells`,
  `Schoenflies.CellStructure.Realization.faceBoundary` — the realized point set of a set of
  abstract cells, and the boundary of a 2-cell read off the abstract data.
* `Schoenflies.CellStructure.Realization.IsFaceJordan` — **assertion (vii)** of
  `lem:cellulation-invariants`, for one realization.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition.face_eq_of_isFaceJordan`,
  `…sub_face_eq` — **assertion (viii)** with its openness hypothesis discharged by (vii).
* `Schoenflies.CellStructure.SubdivData.IsRefinement.isFaceJordan` — (vii) is preserved by an
  edge subdivision.
* `Schoenflies.CellStructure.SplitData.IsRefinement` — the split analogue of
  `SubdivData.IsRefinement`, and `…IsRefinement.isCellDecomposition` — **assertion (i) at the
  split constructor**.
* `Schoenflies.CellStructure.SplitData.IsRefinement.refines` — the one-liner
  `RefinementStars.lean` asked for, next to `SubdivData.IsRefinement.refines`.
* `Schoenflies.CellStructure.SplitData.IsCrosscutSplit`,
  `Schoenflies.CellStructure.SplitData.IsCrosscutSplit.isRefinement`,
  `Schoenflies.CellStructure.SplitData.IsCrosscutSplit.isFaceJordan` — the geometric input of one
  split (the ear drawn as a crosscut of the old Jordan face), and the two invariants
  *constructed* from it by `Schoenflies.crosscut_theorem`. This is the blueprint's
  "Theorem `thm:general-crosscut` decomposes the old open 2-cell into the disjoint union of the
  two new open 2-cells and the open cells of the ear, and gives
  `closure Rᵢ = Rᵢ ∪ P ∪ Bᵢ`".
* `Schoenflies.CellStructure.SubdivData.SubstWalk`,
  `Schoenflies.CellStructure.SubdivData.SubstWalk.isWalk`,
  `Schoenflies.CellStructure.SubdivData.boundary_isWalk` — the orientation-aware boundary-walk
  update. Not a blueprint statement: the blueprint's operation 1 does not spell the update
  out, and this is what it has to be.
-/

open Set Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace Realization

variable {R : S.Realization} {D : Set Plane} {F T σ τ : γ}

/-! ### The realized point set of a set of cells

Every geometric statement of `lem:cellulation-invariants` is about a *union of open cells*: the
closure of a cell, the boundary of a 2-cell, the realized ear, the realized boundary path. One
notation serves them all. -/

/-- The realized point set of a set of abstract cells: the union of their open cells. -/
def cellUnion (R : S.Realization) (Cs : Set γ) : Set Plane := ⋃ σ ∈ Cs, R.cell σ

theorem mem_cellUnion_iff {Cs : Set γ} {z : Plane} :
    z ∈ R.cellUnion Cs ↔ ∃ σ ∈ Cs, z ∈ R.cell σ := by
  simp only [cellUnion, Set.mem_iUnion, exists_prop]

theorem cell_subset_cellUnion {Cs : Set γ} (h : σ ∈ Cs) : R.cell σ ⊆ R.cellUnion Cs :=
  Set.subset_biUnion_of_mem (u := fun ρ => R.cell ρ) h

@[simp] theorem cellUnion_empty (R : S.Realization) : R.cellUnion ∅ = ∅ := Set.biUnion_empty _

@[simp] theorem cellUnion_singleton (R : S.Realization) (σ : γ) :
    R.cellUnion {σ} = R.cell σ := Set.biUnion_singleton _ _

/-! ### Assertion (vii)

"In each of the two realizations, every 2-cell boundary walk is realized by a Jordan curve, and
the open 2-cell is the bounded complementary region of that curve."

`Schoenflies.inside` is the union of the *bounded* complementary components of a set, so
"the bounded complementary region of the Jordan curve `J`" is literally `inside J`; and by
`Schoenflies.jordan_curve_theorem` it is a single region. -/

/-- **Assertion (vii)** of `lem:cellulation-invariants**, for one realization: every open 2-cell
is the bounded complementary region of a Jordan curve, namely its own frontier.

Stated against `frontier (R.cell F)` rather than against the boundary walk; see the module
docstring. Under assertion (i) the frontier *is* the union of the open cells strictly below `F`
(`IsCellDecomposition.faceBoundary_eq_frontier`), which is the blueprint's boundary walk read
as a set. -/
structure IsFaceJordan (R : S.Realization) : Prop where
  /-- The boundary of every 2-cell is a Jordan curve. -/
  isJordanCurve : ∀ ⦃F⦄, F ∈ S.faces → IsJordanCurve (frontier (R.cell F))
  /-- The open 2-cell is the bounded complementary region of that curve. -/
  cell_eq_inside : ∀ ⦃F⦄, F ∈ S.faces → R.cell F = inside (frontier (R.cell F))

end Realization

/-! ### Assertion (vii) is preserved by an edge subdivision

"An edge subdivision changes no 2-cell." Literally: the 2-cells of `S.subdivideEdge d` are those
of `S`, and each is an old cell distinct from the subdivided edge, so `SubdivData.IsRefinement`
leaves its open cell exactly where it was. -/

/-! ### Assertion (i) at the split constructor

The split analogue of `SubdivData.IsRefinement`, and the propagation of assertion (i) across it.
The blueprint's proof of this step is exactly

> `thm:general-crosscut` decomposes the old open 2-cell into the disjoint union of the two new
> open 2-cells and the open cells of the ear, and gives `closure Rᵢ = Rᵢ ∪ P ∪ Bᵢ`.

so those two identities, together with the incidences along the ear, are the fields of
`SplitData.IsRefinement`; `SplitData.IsCrosscutSplit` below constructs them from
`Schoenflies.crosscut_theorem`. -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayLift
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous lift of each actual terminal arc to angular and logarithmic
coordinates. The angular origin is the representative of the arc start. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

abbrev DiskRayTime := {t : PathTime // t < ⊤}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.Graph_Relabel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Relabelling the edges of a multigraph

Mathlib's `Graph.map` changes vertex names and deliberately leaves edge names fixed.  The ear
construction needs the complementary operation: give the finitely many edges of an ambient path
fresh abstract cell names while retaining every vertex and every incidence.

The relabelling map only has to be injective on the graph's edge set.  Walks, paths, and path
graphs then push forward by mapping their edge lists.
-/

open Set
open Schoenflies
open unitInterval
open scoped _root_.Graph

namespace Graph

variable {α β δ : Type*} {G : Graph α β} {f : β → δ}

/-! ### Relabelling a drawing -/

section Drawing

variable {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- The drawing with its edge argument translated back through an injective relabelling. -/
noncomputable def relabelDrawing [Nonempty β] (G : Graph α β) (f : β → δ)
    (drawing : β → ℝ → Plane) : δ → ℝ → Plane :=
  fun d => drawing (Function.invFunOn f E(G) d)

@[simp] theorem relabelDrawing_apply [Nonempty β] (hf : InjOn f E(G))
    {e : β} (he : e ∈ E(G)) :
    relabelDrawing G f drawing (f e) = drawing e := by
  rw [relabelDrawing, hf.leftInvOn_invFunOn he]

end Drawing

end Graph
end

section
-- module Solutions.Q146_CD.MatchedArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Matching and cutting simple polygonal arcs

An ear can have an arbitrary finite number of abstract edges.  On the target side we only
obtain one set-level polygonal crosscut.  This module supplies the two facts that reconcile
those descriptions.

* Two named arcs admit an endpoint-preserving homeomorphism, obtained by matching their
  parameters.
* An arc contained in a polygonal arc is polygonal.  Consequently the images of all source
  edge arcs under the parameter-matching homeomorphism are polygonal target edge arcs.
-/

open Set unitInterval

namespace Schoenflies

/-! ## The inverse of a compact parametrisation -/

/-! ## A subarc of a polygonal arc is polygonal -/

/-! ## Matching two named arcs -/

/-- A homeomorphism between two arcs, with the named endpoints matched in order.  The maps are
total functions because that is the shape needed by the split constructor; all inverse and
continuity assertions are restricted to the two arc carriers. -/
structure ArcHomeo (A B : Set Plane) (a b c d : Plane) where
  toFun : Plane → Plane
  invFun : Plane → Plane
  continuousOn_toFun : ContinuousOn toFun A
  continuousOn_invFun : ContinuousOn invFun B
  leftInvOn : LeftInvOn invFun toFun A
  rightInvOn : RightInvOn invFun toFun B
  image_eq : toFun '' A = B
  map_left : toFun a = c
  map_right : toFun b = d

namespace ArcHomeo

variable {A B : Set Plane} {a b c d : Plane}

theorem injOn (h : ArcHomeo A B a b c d) : InjOn h.toFun A := h.leftInvOn.injOn

end ArcHomeo

/-! ## Transporting a plane drawing along an arc homeomorphism -/

end Schoenflies

open Schoenflies

namespace Graph

variable {β : Type*} {A B : Set Plane} {a b c d : Plane} {G : Graph Plane β}
  {drawing : β → ℝ → Plane}

/-- Apply the map of an arc homeomorphism to every edge parametrisation. -/
def mapDrawing (m : Schoenflies.ArcHomeo A B a b c d) (drawing : β → ℝ → Plane) :
    β → ℝ → Plane := fun e t => m.toFun (drawing e t)

theorem edgeArc_mapDrawing (m : Schoenflies.ArcHomeo A B a b c d) (e : β) :
    edgeArc (mapDrawing m drawing) e = m.toFun '' edgeArc drawing e := by
  rw [edgeArc, edgeArc, ← Set.image_comp]
  rfl

/-- A drawing whose whole point set is one arc transports along an arc homeomorphism. -/
theorem IsDrawing.map_arcHomeo (h : IsDrawing G drawing)
    (m : Schoenflies.ArcHomeo A B a b c d)
    (hpoint : pointSet G drawing = A) :
    IsDrawing (G.map m.toFun) (mapDrawing m drawing) where
  edge_param := by
    intro e he
    obtain ⟨hc, hi, hl⟩ := h.edge_param he
    have hedge : edgeArc drawing e ⊆ A := hpoint ▸ edgeArc_subset_pointSet he
    refine ⟨m.continuousOn_toFun.comp hc (fun t ht => hedge ⟨t, ht, rfl⟩), ?_, ?_⟩
    · intro s hs t ht hst
      exact hi hs ht (m.injOn (hedge ⟨s, hs, rfl⟩) (hedge ⟨t, ht, rfl⟩) hst)
    · exact hl.map m.toFun
  vertex_mem_edgeArc := by
    intro e x y v hlink hv hz
    rcases hlink with ⟨x', y', hxy, rfl, rfl⟩
    rw [Graph.vertexSet_map] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    rw [edgeArc_mapDrawing] at hz
    obtain ⟨z, hz, hmz⟩ := hz
    have hvA : v' ∈ A := hpoint ▸ vertexSet_subset_pointSet hv'
    have hzA : z ∈ A := hpoint ▸ edgeArc_subset_pointSet hxy.edge_mem hz
    have hvz : v' = z := m.injOn hvA hzA hmz.symm
    rcases h.vertex_mem_edgeArc hxy hv' (hvz ▸ hz) with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]
  edge_inter := by
    intro e f he hf hef p hpe hpf
    rw [Graph.edgeSet_map] at he hf
    rw [edgeArc_mapDrawing] at hpe hpf
    obtain ⟨x, hxe, hxp⟩ := hpe
    obtain ⟨y, hyf, hyp⟩ := hpf
    have hxA : x ∈ A := hpoint ▸ edgeArc_subset_pointSet he hxe
    have hyA : y ∈ A := hpoint ▸ edgeArc_subset_pointSet hf hyf
    have hxy : x = y := m.injOn hxA hyA (hxp.trans hyp.symm)
    subst y
    obtain ⟨hxV, hie, hif⟩ := h.edge_inter he hf hef hxe hyf
    subst p
    exact ⟨by rw [Graph.vertexSet_map]; exact ⟨x, hxV, rfl⟩,
      hie.map m.toFun, hif.map m.toFun⟩

end Graph
end

section
-- module Solutions.Q146_CD.RealizeSplit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.relabelDrawing_apply
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing a 2-cell split

`Schoenflies/CellulationInvariants.lean` proves the *step* theorems of the second elementary
operation: given a realization `R'` of `S.splitFace d` standing in the relation
`SplitData.IsCrosscutSplit` to a realization `R` of `S`, the two invariants of
`lem:cellulation-invariants` propagate. Nothing built such an `R'`. This module does.

## Blueprint

* `def:generated-structure`, operation 2 — the 2-cell split whose realization is constructed
  here.
* `lem:cellulation-invariants` (i), (vii) — the invariants that
  `SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` derives from the output of
  this module.
* `thm:general-crosscut` (`Schoenflies.crosscut_theorem`) — what turns the constructed ear into
  the two new open 2-cells; it is applied inside `IsCrosscutSplit.isRefinement`, and this module
  supplies its hypotheses.

## What is constructed

* `Schoenflies.CellStructure.SplitData.EarCrosscut` — the geometric input: an assignment of
  points to the ear's vertices and of parametrizations to the ear's edges, drawing the ear as a
  polygonal crosscut of the realized open 2-cell.
* `Schoenflies.CellStructure.SplitData.realize` — the realization of `S.splitFace d` built from
  `R` and such an ear. It is a `def` with lemmas, not an existential: `splitPos`,
  `splitDrawing`, `splitCell` are its three components, each with its own reduction lemmas
  (`splitCell_face₁`, `splitCell_of_mem_cells`, `splitCell_earVertex`, `splitCell_earEdge`, …),
  and `realize_pos` / `realize_drawing` / `realize_cell` connect them to the record.
* `Schoenflies.CellStructure.SplitData.isCrosscutSplit_realize` — the constructed realization
  stands in the relation `IsCrosscutSplit` to `R`. Composed with
  `IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` this is the full induction step.

## What is assumed, and who discharges it

`realize` itself asks only for `EarCrosscut`, whose six fields — `pos_source`, `pos_target`,
`injOn`, `isDrawing`, `subset_face`, `polygonal` — say that the ear is drawn as a simple
polygonal arc from `R.pos d.source` to `R.pos d.target` whose interior lies in the open 2-cell,
plus the seventh, `disjoint_skeleton`, which is a fact about `R` alone and is discharged by
`Realization.disjoint_cell_skeletonSet` from assertion (i). A producer that starts from
`Schoenflies.exists_crosscut_of_polyAccessible` — a polygonal arc inside the face with both
ends on its boundary — and cuts that arc into the ear's edges has all seven in hand.

`isCrosscutSplit_realize` asks in addition only for `R.IsCellDecomposition D` and
`R.IsFaceJordan`.

It used to ask for a third thing — that the two boundary paths of the split 2-cell share nothing
but their two ends — because `SplitData` did not imply it: its field `paths_disjoint` forbade
the two paths a common *edge* but said nothing about a common interior *vertex*, and with a
common interior vertex the two realized paths meet in a third point, so the `IsCutPair` clause
of `IsCrosscutSplit` is false. That gap has since been closed at the source: `SplitData` now
carries `paths_meet` and derives `paths_disjoint` from it. What follows is the record of a
condition that
producer of the `SplitData` chooses them (as the two arcs of one boundary cycle) and so can
supply it. If a later wave prefers it as a field of `SplitData`, that is the right place for it.

## The general lemmas this needed

Three facts about drawings and paths had no home on `main` and are proved here in the root
`Graph` namespace. If a second consumer appears they belong in `Schoenflies/Graph/`:

* `Graph.IsPath.map`, `Graph.walkVertices_map`, `Graph.IsPathGraph.map` — a path pushes forward
  along an injective relabelling of the vertices. `Graph.IsWalk.map` was already on `main` (in
  `Schoenflies/CombinatorialInvariance.lean`); the path version needs the injectivity, because
  the freshness clause is a *non*-membership.
* `Graph.IsDrawing.isArcBetween_walkPointSet` — **the point set of a drawn path is a simple
  arc between its two ends.** This is the workhorse: it is what makes the realized ear an arc
  (so `IsCrosscut` applies) and what makes each realized boundary path an arc (so `IsCutPair`
  applies). The induction is on `Graph.IsPath`, and the freshness clause of a path is exactly
  what rules out the returning point that would break `IsArcBetween.concatenate`.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

/-! ### Pushing a path forward along a relabelling -/

section Map

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v : α} {W : List β}

theorem coveredVertices_map (f : α → α') :
    (G.map f).coveredVertices W = f '' G.coveredVertices W := by
  ext x
  simp only [mem_coveredVertices_iff, map_inc, Set.mem_image]
  constructor
  · rintro ⟨e, he, v, hv, rfl⟩
    exact ⟨v, ⟨e, he, hv⟩, rfl⟩
  · rintro ⟨v, ⟨e, he, hv⟩, rfl⟩
    exact ⟨e, he, v, hv, rfl⟩

theorem walkVertices_map (f : α → α') (u : α) (W : List β) :
    (G.map f).walkVertices (f u) W = f '' G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_map, Set.image_insert_eq]

/-- **A path pushes forward along an injective relabelling.** Unlike `Graph.IsWalk.map` this
needs the injectivity: the freshness clause is a non-membership, and only an injective map
reflects it. -/
theorem IsPath.map (hf : InjOn f V(G)) (h : G.IsPath u W v) : (G.map f).IsPath (f u) W (f v) := by
  induction h with
  | nil hx => exact .nil (by simpa using Set.mem_image_of_mem f hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.map f) ih ?_
    rw [walkVertices_map]
    rintro ⟨z, hz, hzf⟩
    have hzV : z ∈ V(G) := walkVertices_subset_vertexSet hW.isWalk.left_mem hz
    exact hfresh (hf hzV hl.left_mem hzf ▸ hz)

/-- Relabelling commutes with the union. Both sides resolve a shared edge name in favour of
the left-hand graph, and `Graph.map` keeps the edge set, so the two resolutions agree. -/
theorem map_union (G H : Graph α β) (f : α → α') :
    (G.union H).map f = (G.map f).union (H.map f) := by
  refine Graph.ext (by simp [Set.image_union]) fun e x y => ?_
  simp only [map_isLink, union_isLink, Relation.map_apply, edgeSet_map]
  constructor
  · rintro ⟨a, b, hab | ⟨he, hab⟩, rfl, rfl⟩
    · exact Or.inl ⟨a, b, hab, rfl, rfl⟩
    · exact Or.inr ⟨he, a, b, hab, rfl, rfl⟩
  · rintro (⟨a, b, hab, rfl, rfl⟩ | ⟨he, a, b, hab, rfl, rfl⟩)
    · exact ⟨a, b, Or.inl hab, rfl, rfl⟩
    · exact ⟨a, b, Or.inr ⟨he, hab⟩, rfl, rfl⟩

theorem IsPathGraph.map {P : Graph α β} (hf : InjOn f V(P)) (h : P.IsPathGraph u W v) :
    (P.map f).IsPathGraph (f u) W (f v) where
  isPath := h.isPath.map hf
  edgeSet_eq := by rw [edgeSet_map]; exact h.edgeSet_eq
  vertexSet_eq := by rw [vertexSet_map, walkVertices_map, h.vertexSet_eq]

end Map

section Drawing

variable {β : Type*} {H K : Graph Plane β} {drw : β → ℝ → Plane}

/-! ### The point set of a drawn path

`Graph.pointSet` reads the vertex set and the edge set of a graph. Along a walk both are read
off the list instead, and that is the form the induction below runs on. -/

/-- The point set a walk occupies: the vertices it visits together with the arcs of its
edges. For a path graph this is the whole of `Graph.pointSet` (`walkPointSet_eq_pointSet`). -/
def walkPointSet (H : Graph Plane β) (drw : β → ℝ → Plane) (u : Plane) (W : List β) : Set Plane :=
  H.walkVertices u W ∪ ⋃ e ∈ ({e | e ∈ W} : Set β), edgeArc drw e

theorem walkPointSet_eq_pointSet {u v : Plane} {W : List β} (h : H.IsPathGraph u W v) :
    walkPointSet H drw u W = pointSet H drw := by
  rw [walkPointSet, pointSet, h.vertexSet_eq, h.edgeSet_eq]

theorem walkPointSet_nil (u : Plane) : walkPointSet H drw u ([] : List β) = {u} := by
  rw [walkPointSet, walkVertices_nil]
  simp

/-- Peeling the first step off a walk peels its arc off the point set. The vertex the step
departs from is an end of that arc, which is why nothing is left behind. -/
theorem walkPointSet_cons (hD : IsDrawing H drw) {e : β} {u w : Plane} {W : List β}
    (hl : H.IsLink e u w) :
    walkPointSet H drw u (e :: W) = edgeArc drw e ∪ walkPointSet H drw w W := by
  have hu : u ∈ edgeArc drw e := (hD.edge_isArcBetween hl).left_mem
  have hset : ({f | f ∈ e :: W} : Set β) = insert e {f | f ∈ W} := by
    ext f; simp [List.mem_cons]
  rw [walkPointSet, walkPointSet, walkVertices_cons hl, hset, Set.biUnion_insert]
  refine Set.Subset.antisymm ?_ ?_
  · rintro z (hz | hz)
    · rcases hz with rfl | hz
      · exact Or.inl hu
      · exact Or.inr (Or.inl hz)
    · rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz)
  · rintro z (hz | hz | hz)
    · exact Or.inr (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr (Or.inr hz)

/-- **The point set of a drawn path is a simple arc between its two ends.**

The two pieces glued at each step are the arc of the first edge and the point set of the rest
of the path, and `IsArcBetween.concatenate` asks that they meet only at the vertex between
them. That is precisely the freshness clause of `Graph.IsPath`: the vertex the path departs
from is not among those the rest of it visits, and every point the first arc shares with the
rest of the drawing is a vertex the rest visits — a vertex by `vertex_mem_edgeArc` if it is
one of the rest's vertices, and by `edge_inter` if it lies on one of the rest's arcs. -/
theorem IsDrawing.isArcBetween_walkPointSet (hD : IsDrawing H drw) :
    ∀ {u v : Plane} {W : List β}, H.IsPath u W v → u ≠ v →
      IsArcBetween (walkPointSet H drw u W) u v := by
  intro u v W hp
  induction hp with
  | nil => exact fun h => absurd rfl h
  | @cons u w v e W hl hW hfresh ih =>
    intro _
    rw [walkPointSet_cons hD hl]
    have harc : IsArcBetween (edgeArc drw e) u w := hD.edge_isArcBetween hl
    by_cases hwv : w = v
    · subst hwv
      rw [hW.eq_nil_of_eq, walkPointSet_nil,
        Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.2 harc.right_mem)]
      exact harc
    · refine harc.concatenate (ih hwv) ?_
      intro z hz hz'
      -- every point the first arc shares with the rest is a vertex the rest visits
      have hzw : z ∈ H.walkVertices w W := by
        rcases hz' with hz' | hz'
        · exact hz'
        · obtain ⟨f, hf, hzf⟩ := Set.mem_iUnion₂.1 hz'
          have hfe : e ≠ f := by
            rintro rfl
            exact (List.nodup_cons.1 (IsPath.cons hl hW hfresh).nodup).1 hf
          exact mem_walkVertices_of_mem_covered ⟨f, hf,
            (hD.edge_inter hl.edge_mem (hW.isWalk.edge_mem hf) hfe hz hzf).2.2⟩
      have hzV : z ∈ V(H) := walkVertices_subset_vertexSet hW.isWalk.left_mem hzw
      rcases hD.vertex_mem_edgeArc hl hzV hz with rfl | rfl
      · exact absurd hzw hfresh
      · rfl

theorem IsDrawing.isArcBetween_pointSet (hD : IsDrawing H drw) {u v : Plane} {W : List β}
    (h : H.IsPathGraph u W v) (huv : u ≠ v) : IsArcBetween (pointSet H drw) u v := by
  rw [← walkPointSet_eq_pointSet h]
  exact hD.isArcBetween_walkPointSet h.isPath huv

end Drawing

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ## What a realization does to a walk

Two facts about an existing realization, both of the shape "the realized cells of a piece of
the skeleton occupy the point set that piece of the drawing occupies". They are what let the
crosscut theorem, which speaks of point sets, be fed from the cell structure, which speaks of
cells. -/

/-! ## The ear, drawn

`SplitData` fixes the *abstract* ear: a path graph `d.ear` glued to the skeleton at
`d.source` and `d.target`. Drawing it means choosing a point for each of its vertices and a
parametrization for each of its edges. `EarCrosscut` is the bundle of conditions under which
that drawing is a polygonal crosscut of the realized open 2-cell `R.cell d.face`. -/

namespace SplitData

variable (d : S.SplitData)

theorem source_mem_ear : d.source ∈ V(d.ear) :=
  (d.vertexSet_inter ▸ (Set.mem_insert _ _ : d.source ∈ ({d.source, d.target} : Set γ))).1

theorem target_mem_ear : d.target ∈ V(d.ear) :=
  (d.vertexSet_inter ▸
    (Set.mem_insert_of_mem _ rfl : d.target ∈ ({d.source, d.target} : Set γ))).1

/-- The drawn ear: the abstract ear pushed into the plane along the chosen positions. -/
def earGraph (d : S.SplitData) (earPos : γ → Plane) : Graph Plane γ := d.ear.map earPos

@[simp] theorem vertexSet_earGraph (earPos : γ → Plane) :
    V(d.earGraph earPos) = earPos '' V(d.ear) := Graph.vertexSet_map _ _

@[simp] theorem edgeSet_earGraph (earPos : γ → Plane) :
    E(d.earGraph earPos) = E(d.ear) := Graph.edgeSet_map _ _

/-- The point set the drawn ear occupies: the crosscut `P` of `thm:general-crosscut`. -/
def earSet (d : S.SplitData) (earPos : γ → Plane) (earDraw : γ → ℝ → Plane) : Set Plane :=
  Graph.pointSet (d.earGraph earPos) earDraw

/-- **The geometric input of one 2-cell split.** A position for each vertex of the abstract
ear and a parametrization for each of its edges, drawing the ear as a polygonal crosscut of
the realized open 2-cell `R.cell d.face`.

Every clause is a statement about the ear's own drawing, and every one of them is what the
finite-transfer module has in hand when it produces a crosscut from
`Schoenflies.exists_crosscut_of_polyAccessible`: it starts from a simple polygonal arc `P`
inside the face with its two ends on the boundary, and cuts `P` into the ear's edges. -/
structure EarCrosscut (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane)
    (earDraw : γ → ℝ → Plane) : Prop where
  /-- The ear starts where the old 0-cell `d.source` sits. -/
  pos_source : earPos d.source = R.pos d.source
  /-- …and ends where `d.target` sits. -/
  pos_target : earPos d.target = R.pos d.target
  /-- Distinct vertices of the ear are drawn at distinct points. -/
  injOn : InjOn earPos V(d.ear)
  /-- The ear is drawn as a plane graph. -/
  isDrawing : Graph.IsDrawing (d.earGraph earPos) earDraw
  /-- Every point of the drawn ear but its two ends is inside the old open 2-cell. -/
  subset_face : d.earSet earPos earDraw \ {R.pos d.source, R.pos d.target} ⊆ R.cell d.face
  /-- The old open 2-cell misses the old drawn skeleton. This is a property of `R` alone, not
  of the ear; it is carried here so that the construction below depends on no ambient domain.
  `Realization.disjoint_cell_skeletonSet` discharges it from assertion (i). -/
  disjoint_skeleton : Disjoint (R.cell d.face) R.skeletonSet
  /-- The drawn ear is polygonal. -/
  polygonal : IsPolygonal (d.earSet earPos earDraw)

namespace EarCrosscut

variable {d} {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
theorem source_ne_target_pos : R.pos d.source ≠ R.pos d.target := fun h =>
  d.source_ne_target (R.injOn_pos d.source_mem_skel d.target_mem_skel h)

theorem mem_earSet_of_mem_ear {z : γ} (hz : z ∈ V(d.ear)) : earPos z ∈ d.earSet earPos earDraw :=
  Graph.vertexSet_subset_pointSet (by rw [d.vertexSet_earGraph]; exact ⟨z, hz, rfl⟩)

theorem edgeArc_subset_earSet {f : γ} (hf : f ∈ E(d.ear)) :
    Graph.edgeArc earDraw f ⊆ d.earSet earPos earDraw :=
  Graph.edgeArc_subset_pointSet (by rw [d.edgeSet_earGraph]; exact hf)

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- On the two ends — the only vertices the ear shares with the old skeleton — the ear's
positions agree with the old ones. -/
theorem earPos_eq {z : γ} (hz : z ∈ V(d.ear)) (hz' : z ∈ V(S.skel)) : earPos z = R.pos z := by
  have : z ∈ ({d.source, d.target} : Set γ) := d.vertexSet_inter ▸ ⟨hz, hz'⟩
  rcases this with rfl | rfl
  exacts [hE.pos_source, hE.pos_target]

theorem pos_source_mem_earSet : R.pos d.source ∈ d.earSet earPos earDraw :=
  hE.pos_source ▸ mem_earSet_of_mem_ear d.source_mem_ear

theorem pos_target_mem_earSet : R.pos d.target ∈ d.earSet earPos earDraw :=
  hE.pos_target ▸ mem_earSet_of_mem_ear d.target_mem_ear

/-- An interior vertex of the ear is drawn strictly inside the old open 2-cell. -/
theorem earPos_mem_cell_face {z : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : earPos z ∈ R.cell d.face := by
  refine hE.subset_face ⟨mem_earSet_of_mem_ear hz, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h)
  · exact hs (hE.injOn hz d.source_mem_ear (h.trans hE.pos_source.symm))
  · exact ht (hE.injOn hz d.target_mem_ear (h.trans hE.pos_target.symm))

/-- **The drawn ear meets the old skeleton exactly in its two ends.** The interior of the ear
is inside the open 2-cell, and an open 2-cell misses the drawn skeleton. -/
theorem earSet_inter_skeletonSet :
    d.earSet earPos earDraw ∩ R.skeletonSet ⊆ {R.pos d.source, R.pos d.target} := by
  rintro x ⟨hx, hx'⟩
  by_contra hcon
  exact Set.disjoint_left.1 hE.disjoint_skeleton (hE.subset_face ⟨hx, hcon⟩) hx'

/-- **An ear edge's arc meets the ear's vertices exactly at its own two ends**, so dropping
all of the ear's vertices from it is the same as dropping its own two ends. This is what makes
the definition of the new open 1-cells independent of a choice of orientation. -/
theorem edgeArc_diff {f a b : γ} (hl : d.ear.IsLink f a b) :
    Graph.edgeArc earDraw f \ earPos '' V(d.ear) =
      Graph.edgeArc earDraw f \ {earPos a, earPos b} := by
  have hlm : (d.earGraph earPos).IsLink f (earPos a) (earPos b) := hl.map earPos
  refine Set.Subset.antisymm (Set.sdiff_subset_sdiff_right ?_) (fun x ⟨hx, hx'⟩ => ⟨hx, ?_⟩)
  · rintro _ (rfl | rfl)
    exacts [⟨a, hl.left_mem, rfl⟩, ⟨b, hl.right_mem, rfl⟩]
  · rintro ⟨w, hw, rfl⟩
    have hwV : earPos w ∈ V(d.earGraph earPos) := by
      rw [d.vertexSet_earGraph]; exact ⟨w, hw, rfl⟩
    exact hx' (hE.isDrawing.vertex_mem_edgeArc hlm hwV hx)

end EarCrosscut

/-! ## The realization built from a drawn ear -/

open scoped Classical in
/-- Where the split puts each 0-cell: the ear's vertices go where the ear's drawing puts them,
everything else stays. On the ear's two ends the two prescriptions agree. -/
noncomputable def splitPos (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane) :
    γ → Plane := fun z => if z ∈ V(d.ear) then earPos z else R.pos z

open scoped Classical in
/-- How the split draws each 1-cell. -/
noncomputable def splitDrawing (d : S.SplitData) (R : S.Realization)
    (earDraw : γ → ℝ → Plane) : γ → ℝ → Plane :=
  fun f => if f ∈ E(d.ear) then earDraw f else R.drawing f

open scoped Classical in
/-- The point set of each open cell after the split: the two new 2-cells are the two sides of
the crosscut, the ear's vertices and edges are their points and their open arcs, and every
surviving cell keeps its old point set. -/
noncomputable def splitCell (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane)
    (earDraw : γ → ℝ → Plane) : γ → Set Plane := fun σ =>
  if σ = d.face₁ then inside (R.cellUnion d.cells₁ ∪ d.earSet earPos earDraw)
  else if σ = d.face₂ then inside (R.cellUnion d.cells₂ ∪ d.earSet earPos earDraw)
  else if σ ∈ V(d.ear) ∧ σ ∉ V(S.skel) then {earPos σ}
  else if σ ∈ E(d.ear) then Graph.edgeArc earDraw σ \ earPos '' V(d.ear)
  else R.cell σ

variable {d} {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}

theorem splitPos_of_mem_ear {z : γ} (hz : z ∈ V(d.ear)) : d.splitPos R earPos z = earPos z := by
  classical
  simp only [splitPos, if_pos hz]

theorem splitPos_of_notMem_ear {z : γ} (hz : z ∉ V(d.ear)) : d.splitPos R earPos z = R.pos z := by
  classical
  simp only [splitPos, if_neg hz]

theorem EarCrosscut.splitPos_eq (hE : d.EarCrosscut R earPos earDraw) {z : γ}
    (hz : z ∈ V(S.skel)) : d.splitPos R earPos z = R.pos z := by
  by_cases hz' : z ∈ V(d.ear)
  · rw [splitPos_of_mem_ear hz', hE.earPos_eq hz' hz]
  · rw [splitPos_of_notMem_ear hz']

theorem splitDrawing_of_mem_ear {f : γ} (hf : f ∈ E(d.ear)) :
    d.splitDrawing R earDraw f = earDraw f := by
  classical
  simp only [splitDrawing, if_pos hf]

theorem splitDrawing_of_mem_skel {f : γ} (hf : f ∈ E(S.skel)) :
    d.splitDrawing R earDraw f = R.drawing f := by
  classical
  simp only [splitDrawing, if_neg (Set.disjoint_left.1 d.disjoint_edgeSet hf)]

theorem splitCell_of_mem_cells {σ : γ} (hσ : σ ∈ S.cells) :
    d.splitCell R earPos earDraw σ = R.cell σ := by
  classical
  have h₁ : σ ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem hσ
  have h₂ : σ ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem hσ
  have h₃ : ¬ (σ ∈ V(d.ear) ∧ σ ∉ V(S.skel)) := by
    rintro ⟨hv, hnv⟩
    rcases d.mem_cells_of_mem_ear_vertexSet hv hσ with rfl | rfl
    exacts [hnv d.source_mem_skel, hnv d.target_mem_skel]
  have h₄ : σ ∉ E(d.ear) := fun h => d.edge_fresh h hσ
  unfold splitCell
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄]

theorem EarCrosscut.splitCell_earVertex (hE : d.EarCrosscut R earPos earDraw) {z : γ}
    (hz : z ∈ V(d.ear)) : d.splitCell R earPos earDraw z = {earPos z} := by
  classical
  by_cases hz' : z ∈ V(S.skel)
  · rw [splitCell_of_mem_cells (S.mem_cells_of_mem_vertexSet hz'), R.cell_vertex hz',
      hE.earPos_eq hz hz']
  · have h₁ : z ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem_ear (Or.inl hz)
    have h₂ : z ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem_ear (Or.inl hz)
    unfold splitCell
    rw [if_neg h₁, if_neg h₂, if_pos (show z ∈ V(d.ear) ∧ z ∉ V(S.skel) from ⟨hz, hz'⟩)]

theorem splitCell_earEdge {f : γ} (hf : f ∈ E(d.ear)) :
    d.splitCell R earPos earDraw f = Graph.edgeArc earDraw f \ earPos '' V(d.ear) := by
  classical
  have h₁ : f ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem_ear (Or.inr hf)
  have h₂ : f ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem_ear (Or.inr hf)
  have h₃ : ¬ (f ∈ V(d.ear) ∧ f ∉ V(S.skel)) := fun h =>
    Set.disjoint_left.1 d.ear_disjoint h.1 hf
  unfold splitCell
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_pos hf]

theorem edgeArc_splitDrawing_of_mem_skel {f : γ} (hf : f ∈ E(S.skel)) :
    Graph.edgeArc (d.splitDrawing R earDraw) f = Graph.edgeArc R.drawing f := by
  rw [Graph.edgeArc, Graph.edgeArc, splitDrawing_of_mem_skel hf]

theorem edgeArc_splitDrawing_of_mem_ear {f : γ} (hf : f ∈ E(d.ear)) :
    Graph.edgeArc (d.splitDrawing R earDraw) f = Graph.edgeArc earDraw f := by
  rw [Graph.edgeArc, Graph.edgeArc, splitDrawing_of_mem_ear hf]

namespace EarCrosscut

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- The skeleton of the split structure, drawn: the old drawn skeleton with the drawn ear
glued on. -/
theorem splitGraph_eq :
    (S.splitFace d).skel.map (d.splitPos R earPos) = R.graph.union (d.earGraph earPos) := by
  change (S.skel.union d.ear).map (d.splitPos R earPos) = _
  rw [Graph.map_union]
  congr 1
  · exact Graph.map_eq_of_eqOn fun z hz => hE.splitPos_eq hz
  · exact Graph.map_eq_of_eqOn fun z hz => splitPos_of_mem_ear hz

/-- **The old drawn skeleton with the drawn ear glued on is a plane graph.** The three clauses
of `Graph.IsDrawing` all reduce, on a mixed pair, to the same fact: the ear meets the old
drawing only at its two ends, because its interior lies in an open 2-cell and an open 2-cell
misses the drawn skeleton. -/
theorem isDrawing_split :
    Graph.IsDrawing (R.graph.union (d.earGraph earPos)) (d.splitDrawing R earDraw) := by
  have hEskel : E(R.graph) = E(S.skel) := Realization.edgeSet_graph R
  have hcompat : R.graph.Compatible (d.earGraph earPos) :=
    Graph.Compatible.of_disjoint_edgeSet (by
      rw [hEskel, d.edgeSet_earGraph]; exact d.disjoint_edgeSet)
  have hle₁ : R.graph ≤ R.graph.union (d.earGraph earPos) := Graph.left_le_union _ _
  have hle₂ : d.earGraph earPos ≤ R.graph.union (d.earGraph earPos) := hcompat.right_le_union
  have hmeet := hE.earSet_inter_skeletonSet
  have hends : ∀ {x : Plane}, x ∈ ({R.pos d.source, R.pos d.target} : Set Plane) →
      x ∈ V(R.graph) ∧ x ∈ V(d.earGraph earPos) := by
    rintro x (rfl | rfl)
    · exact ⟨by rw [Realization.vertexSet_graph]; exact ⟨_, d.source_mem_skel, rfl⟩,
        by rw [d.vertexSet_earGraph]; exact ⟨d.source, d.source_mem_ear, hE.pos_source⟩⟩
    · exact ⟨by rw [Realization.vertexSet_graph]; exact ⟨_, d.target_mem_skel, rfl⟩,
        by rw [d.vertexSet_earGraph]; exact ⟨d.target, d.target_mem_ear, hE.pos_target⟩⟩
  have hcross : ∀ {x : Plane}, x ∈ d.earSet earPos earDraw → x ∈ R.skeletonSet →
      x ∈ V(R.graph) ∧ x ∈ V(d.earGraph earPos) := fun hx hx' => hends (hmeet ⟨hx, hx'⟩)
  have hmix : ∀ {p : Plane} {e g : γ}, e ∈ E(S.skel) → g ∈ E(d.ear) →
      p ∈ Graph.edgeArc R.drawing e → p ∈ Graph.edgeArc earDraw g →
      p ∈ V(R.graph.union (d.earGraph earPos)) ∧
        (R.graph.union (d.earGraph earPos)).Inc e p ∧
        (R.graph.union (d.earGraph earPos)).Inc g p := by
    intro p e g he hg hpe hpg
    have hp1 : p ∈ R.skeletonSet :=
      Graph.edgeArc_subset_pointSet (by rwa [hEskel]) hpe
    have hp2 : p ∈ d.earSet earPos earDraw := edgeArc_subset_earSet hg hpg
    obtain ⟨hpV1, hpV2⟩ := hcross hp2 hp1
    obtain ⟨a, b, hlab⟩ := Graph.exists_isLink_of_mem_edgeSet (show e ∈ E(R.graph) by rwa [hEskel])
    obtain ⟨c, c', hlcc⟩ := Graph.exists_isLink_of_mem_edgeSet
      (show g ∈ E(d.earGraph earPos) by rwa [d.edgeSet_earGraph])
    have hInc1 : R.graph.Inc e p := by
      rcases R.isDrawing.vertex_mem_edgeArc hlab hpV1 hpe with rfl | rfl
      exacts [hlab.inc_left, hlab.inc_right]
    have hInc2 : (d.earGraph earPos).Inc g p := by
      rcases hE.isDrawing.vertex_mem_edgeArc hlcc hpV2 hpg with rfl | rfl
      exacts [hlcc.inc_left, hlcc.inc_right]
    exact ⟨Or.inl hpV1, hInc1.mono hle₁, hInc2.mono hle₂⟩
  refine ⟨?_, ?_, ?_⟩
  · -- each edge is drawn by its own parametrization
    intro e he
    rcases he with he | he
    · rw [hEskel] at he
      obtain ⟨hc, hi, hl⟩ := R.isDrawing.edge_param (by rwa [Graph.edgeSet_map])
      rw [splitDrawing_of_mem_skel he]
      exact ⟨hc, hi, Graph.union_isLink.2 (Or.inl hl)⟩
    · rw [d.edgeSet_earGraph] at he
      obtain ⟨hc, hi, hl⟩ := hE.isDrawing.edge_param (by rwa [d.edgeSet_earGraph])
      rw [splitDrawing_of_mem_ear he]
      exact ⟨hc, hi, Graph.union_isLink.2
        (Or.inr ⟨by rw [hEskel]; exact Set.disjoint_right.1 d.disjoint_edgeSet he, hl⟩)⟩
  · -- an edge's arc meets the vertices only at its own ends
    intro e x y v hl hv hmem
    rcases Graph.union_isLink.1 hl with hl | ⟨-, hl⟩
    · have he : e ∈ E(S.skel) := by rw [← hEskel]; exact hl.edge_mem
      rw [edgeArc_splitDrawing_of_mem_skel he] at hmem
      have hvg : v ∈ V(R.graph) := by
        rcases hv with hv | hv
        · exact hv
        · exact (hcross (Graph.vertexSet_subset_pointSet hv)
            (Graph.edgeArc_subset_pointSet (by rwa [hEskel]) hmem)).1
      exact R.isDrawing.vertex_mem_edgeArc hl hvg hmem
    · have he : e ∈ E(d.ear) := by rw [← d.edgeSet_earGraph]; exact hl.edge_mem
      rw [edgeArc_splitDrawing_of_mem_ear he] at hmem
      have hvg : v ∈ V(d.earGraph earPos) := by
        rcases hv with hv | hv
        · exact (hcross (edgeArc_subset_earSet he hmem)
            (Graph.vertexSet_subset_pointSet hv)).2
        · exact hv
      exact hE.isDrawing.vertex_mem_edgeArc hl hvg hmem
  · -- two distinct edges meet only at shared vertices
    intro e f he hf hef p hpe hpf
    rcases he with he | he <;> rcases hf with hf | hf
    · rw [hEskel] at he hf
      rw [edgeArc_splitDrawing_of_mem_skel he] at hpe
      rw [edgeArc_splitDrawing_of_mem_skel hf] at hpf
      obtain ⟨hpV, hIe, hIf⟩ := R.isDrawing.edge_inter (by rwa [Graph.edgeSet_map])
        (by rwa [Graph.edgeSet_map]) hef hpe hpf
      exact ⟨Or.inl hpV, hIe.mono hle₁, hIf.mono hle₁⟩
    · rw [hEskel] at he
      rw [d.edgeSet_earGraph] at hf
      rw [edgeArc_splitDrawing_of_mem_skel he] at hpe
      rw [edgeArc_splitDrawing_of_mem_ear hf] at hpf
      exact hmix he hf hpe hpf
    · rw [d.edgeSet_earGraph] at he
      rw [hEskel] at hf
      rw [edgeArc_splitDrawing_of_mem_ear he] at hpe
      rw [edgeArc_splitDrawing_of_mem_skel hf] at hpf
      obtain ⟨hv, h1, h2⟩ := hmix hf he hpf hpe
      exact ⟨hv, h2, h1⟩
    · rw [d.edgeSet_earGraph] at he hf
      rw [edgeArc_splitDrawing_of_mem_ear he] at hpe
      rw [edgeArc_splitDrawing_of_mem_ear hf] at hpf
      obtain ⟨hpV, hIe, hIf⟩ := hE.isDrawing.edge_inter (by rwa [d.edgeSet_earGraph])
        (by rwa [d.edgeSet_earGraph]) hef hpe hpf
      exact ⟨Or.inr hpV, hIe.mono hle₂, hIf.mono hle₂⟩

end EarCrosscut

namespace EarCrosscut

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- The drawn ear is a path graph in the plane. -/
theorem isPathGraph_earGraph :
    (d.earGraph earPos).IsPathGraph (R.pos d.source) d.earWalk (R.pos d.target) := by
  have := d.isPathGraph.map hE.injOn
  rwa [hE.pos_source, hE.pos_target] at this

/-- **The drawn ear is a simple arc between the two old 0-cells it is glued to.** -/
theorem isArcBetween_earSet :
    IsArcBetween (d.earSet earPos earDraw) (R.pos d.source) (R.pos d.target) :=
  hE.isDrawing.isArcBetween_pointSet hE.isPathGraph_earGraph source_ne_target_pos

end EarCrosscut

/-! ## The realization -/

/-- **The realization of a 2-cell split.**

The old realization `R`, a drawing of the ear as a polygonal crosscut of the old open 2-cell,
and assertion (i) at the old stage produce a realization of `S.splitFace d`:

* the ear's interior 0-cells go where the ear's drawing puts them, and its 1-cells to their
  open arcs;
* the two new 2-cells go to the two sides of the crosscut, `inside (Bᵢ ∪ P)`;
* every surviving cell keeps its old point set.

This is the object the whole split step of `lem:cellulation-invariants` was missing:
`SplitData.isCrosscutSplit_realize` puts it in the relation `IsCrosscutSplit` to `R`, and
`IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` then propagates both invariants. -/
noncomputable def realize (R : S.Realization) (d : S.SplitData) (earPos : γ → Plane)
    (earDraw : γ → ℝ → Plane) (hE : d.EarCrosscut R earPos earDraw) :
    (S.splitFace d).Realization where
  pos := d.splitPos R earPos
  drawing := d.splitDrawing R earDraw
  injOn_pos := by
    have hsep : ∀ ⦃x y : γ⦄, x ∈ V(S.skel) → y ∈ V(d.ear) → y ∉ V(S.skel) →
        d.splitPos R earPos x ≠ d.splitPos R earPos y := by
      intro x y hx hy hyn hxy
      rw [hE.splitPos_eq hx, splitPos_of_mem_ear hy] at hxy
      have h1 : R.pos x ∈ R.cell d.face := by
        rw [hxy]
        exact hE.earPos_mem_cell_face hy (fun h => hyn (h ▸ d.source_mem_skel))
          (fun h => hyn (h ▸ d.target_mem_skel))
      have h2 : R.pos x ∈ R.skeletonSet :=
        Graph.vertexSet_subset_pointSet (by rw [Realization.vertexSet_graph]; exact ⟨x, hx, rfl⟩)
      exact Set.disjoint_left.1 hE.disjoint_skeleton h1 h2
    intro x hx y hy hxy
    have hx' : x ∈ V(S.skel) ∪ V(d.ear) := hx
    have hy' : y ∈ V(S.skel) ∪ V(d.ear) := hy
    rcases hx' with hxs | hxe <;> rcases hy' with hys | hye
    · rw [hE.splitPos_eq hxs, hE.splitPos_eq hys] at hxy
      exact R.injOn_pos hxs hys hxy
    · by_cases hyy : y ∈ V(S.skel)
      · rw [hE.splitPos_eq hxs, hE.splitPos_eq hyy] at hxy
        exact R.injOn_pos hxs hyy hxy
      · exact absurd hxy (hsep hxs hye hyy)
    · by_cases hxx : x ∈ V(S.skel)
      · rw [hE.splitPos_eq hxx, hE.splitPos_eq hys] at hxy
        exact R.injOn_pos hxx hys hxy
      · exact absurd hxy.symm (hsep hys hxe hxx)
    · rw [splitPos_of_mem_ear hxe, splitPos_of_mem_ear hye] at hxy
      exact hE.injOn hxe hye hxy
  isDrawing := by
    rw [hE.splitGraph_eq]
    exact hE.isDrawing_split
  cell := d.splitCell R earPos earDraw
  cell_vertex := by
    intro v hv
    have hv' : v ∈ V(S.skel) ∪ V(d.ear) := hv
    rcases hv' with hv' | hv'
    · rw [splitCell_of_mem_cells (S.mem_cells_of_mem_vertexSet hv'), R.cell_vertex hv',
        hE.splitPos_eq hv']
    · rw [hE.splitCell_earVertex hv', splitPos_of_mem_ear hv']
  cell_edge := by
    intro e x y hl
    have hl' : (S.skel.union d.ear).IsLink e x y := hl
    rcases Graph.union_isLink.1 hl' with hk | ⟨-, hk⟩
    · rw [splitCell_of_mem_cells (S.mem_cells_of_mem_edgeSet hk.edge_mem), R.cell_edge hk,
        edgeArc_splitDrawing_of_mem_skel hk.edge_mem, hE.splitPos_eq hk.left_mem,
        hE.splitPos_eq hk.right_mem]
    · rw [splitCell_earEdge hk.edge_mem, hE.edgeArc_diff hk,
        edgeArc_splitDrawing_of_mem_ear hk.edge_mem, splitPos_of_mem_ear hk.left_mem,
        splitPos_of_mem_ear hk.right_mem]

variable (hE : d.EarCrosscut R earPos earDraw)

@[simp] theorem realize_pos : (realize R d earPos earDraw hE).pos = d.splitPos R earPos := rfl

@[simp] theorem realize_drawing :
    (realize R d earPos earDraw hE).drawing = d.splitDrawing R earDraw := rfl

@[simp] theorem realize_cell :
    (realize R d earPos earDraw hE).cell = d.splitCell R earPos earDraw := rfl

end SplitData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.MatchedSplit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.relabelDrawing_apply
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The skeleton homeomorphism across a 2-cell split

`Schoenflies/RealizeSplit.lean` builds **one** realization of `S.splitFace d` from a realization
`R` of `S` and a drawing of the ear as a polygonal crosscut. A *matched* cellulation is two
realizations of one abstract structure together with the skeleton homeomorphism between them
(`def:matched-pair` clause 3), so the split has to be performed on both sides at once and the
skeleton homeomorphism has to be carried across. That is what this module does.

## Blueprint

* `def:matched-pair`, clause 3 — the chosen homeomorphism `g : |Γ| → |Γ'|`, recorded as
  `Schoenflies.CellStructure.SkeletonHomeo`, extended across one split.
* `def:generated-structure`, operation 2 — the 2-cell split, whose two realizations are the
  output of `Schoenflies.CellStructure.SplitData.realize`.

## What is constructed

* `Schoenflies.CellStructure.SplitData.skeletonSet_realize` — **the split's realized 1-skeleton
  is the old one together with the drawn ear**, as a point set. Everything else rests on this.
* `Schoenflies.CellStructure.SplitData.EarHomeo` — the chosen homeomorphism between the two
  drawn ears (see the next section).
* `Schoenflies.CellStructure.SplitData.EarHomeo.symm` — the same chosen matching with source
  and target reversed, used by finite-transfer direction (b).
* `Schoenflies.CellStructure.SplitData.splitMap` / `splitInvMap` — the transported map and its
  inverse, as plain functions `Plane → Plane`: `g` on the old skeleton, the ear map off it.
* `Schoenflies.CellStructure.SplitData.splitHomeo` — the `SkeletonHomeo` between the two split
  realizations. A `def` with lemmas, not an `∃`-packaged bundle.
* `Schoenflies.CellStructure.SplitData.splitHomeo_eqOn` — **the transported map agrees with `g`
  on the whole old skeleton.** This is exactly `Schoenflies.StageSequence.skelHomeo_succ` at a
  split step, and it is the reason the construction is "extend `g` by the ear map" rather than
  "rebuild a homeomorphism from scratch".

## How the ear map is presented, and why

Two shapes were available.

(a) **As data**: a map `Plane → Plane` (with an inverse) carrying the drawn source ear onto the
drawn target ear, vertex to corresponding vertex and edge arc to corresponding edge arc.

(b) **Built edge by edge** from the two `EarCrosscut`s, by composing one edge's parametrization
with the inverse of the other's.

This module takes **(a)**, as `EarHomeo`. The reason is the consumer, not the construction:
`def:matched-pair` clause 3 says that `g` *restricts to a fixed chosen homeomorphism* on each
corresponding pair of cells, so a caller assembling a matched pair is holding such a chosen
homeomorphism already — for the old cells it is `g` itself, and for the ear's cells it is
whatever the producer of the two crosscuts chose. Shape (b) would manufacture a second,
different homeomorphism from the two parametrizations, and the caller would then have to prove
that its own choice agrees with the manufactured one. It would also silently fix an orientation
of every ear edge: `Graph.IsDrawing.edge_param` is orientation-free, so `earDraw₁ f 0` and
`earDraw₂ f 0` need not be the ends that correspond, and (b) would need the `SubdivData.leftParam`
trick of `Schoenflies/RealizeSubdiv.lean` replayed per edge.

Every field of `EarHomeo` is therefore something the caller supplies, and none of them mentions
`R₁`, `R₂` or `g`: the ear map is a statement about the two drawn ears alone. In particular
**no compatibility hypothesis between `m` and `g` is asked for**, because none is needed: at the
ear's two ends `m.toFun` and `g.toFun` are *forced* to agree, both being pinned to
`R₂.pos d.source` and `R₂.pos d.target` — `m` by `earPos_apply` together with the two `pos_source`
/ `pos_target` clauses of the two `EarCrosscut`s, and `g` by its own `pos_apply`. That is
`EarHomeo.toFun_pos_source` / `toFun_pos_target` below.

## The proof, in one paragraph

The new skeleton is a union of two **closed** sets — the old realized skeleton
(`Realization.isCompact_skeletonSet`) and the drawn ear, which is an arc
(`EarCrosscut.isArcBetween_earSet`) and hence compact. Continuity of the transported map is the
pasting lemma `Schoenflies.Plane.continuousOn_union_of_isClosed` on those two pieces; the two
pieces meet exactly in the ear's two ends (`EarCrosscut.earSet_inter_skeletonSet`, which is
`SplitData.vertexSet_inter` made geometric), and there the two prescriptions agree. Injectivity
and the two inverse laws are injectivity on each piece plus the fact that the *images* also meet
only in the two images of the ends — for which the target-side
`EarCrosscut.earSet_inter_skeletonSet` is again what is spent. `pos_apply` and `edgeArc_image`
split into the old cells, where `g`'s own fields serve verbatim, and the ear's cells, where
`EarHomeo`'s two matching clauses are the statement.

## What is *not* here

The **subdivision** analogue — the transported skeleton homeomorphism across an edge
subdivision — is deliberately absent. It is being built concurrently on branch
`wt/arc-monotone`, where the missing ingredient (a homeomorphism between two arcs fixing their
ends is monotone, hence carries initial subarcs to initial subarcs — see the section
"What is *not* here" of `Schoenflies/RealizeSubdiv.lean`) is the actual content. Nothing below
depends on it, and nothing below should be duplicated there: this module is the split case only.

## The general lemma this needed

`Graph.pointSet_congr` — the point set of a plane graph depends on the drawing only through the
arcs of the graph's own edges. It is stated in the root `Graph` namespace next to
`Graph.pointSet_union` (which lives in `Schoenflies/FaceCycles.lean`); if a second consumer
appears it belongs there or in `Schoenflies/Graph/Drawing.lean`.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β}

/-- **The point set of a plane graph only sees the arcs of its own edges.** Two drawings that
agree, arc for arc, on `E(G)` give `G` the same point set. This is what makes the split's
`splitDrawing` — which is `R.drawing` on the old edges and `earDraw` on the ear's — restrict on
each half of the union to the drawing that half came with. -/
theorem pointSet_congr {drw drw' : β → ℝ → Plane}
    (h : ∀ ⦃e⦄, e ∈ E(G) → edgeArc drw e = edgeArc drw' e) :
    pointSet G drw = pointSet G drw' := by
  rw [pointSet, pointSet]
  exact congrArg _ (Set.iUnion₂_congr fun e he => h he)

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-- **A realized 0-cell is a point of the realized 1-skeleton.** The inlined form of this
appears at least four times on `main` (`SkeletonHomeo.symm`, `Realization.disjoint_skeleton`
arguments in `Schoenflies/RealizeSplit.lean`, …); it belongs next to
`Realization.skeletonSet` in `Schoenflies/CombinatorialInvariance.lean`. -/
theorem Realization.pos_mem_skeletonSet (R : S.Realization) {v : γ} (hv : v ∈ V(S.skel)) :
    R.pos v ∈ R.skeletonSet :=
  Graph.vertexSet_subset_pointSet (by rw [Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)

namespace SplitData

variable {d : S.SplitData}

/-! ## The realized 1-skeleton of a split

A 2-cell split adds the drawn ear to the drawn 1-skeleton and changes nothing else. This is the
geometric statement the whole module rests on: it turns every clause of `SkeletonHomeo`, which
quantifies over the *new* skeleton, into a pair of clauses over the two closed pieces. -/

/-- **The realized 1-skeleton after a 2-cell split is the old one together with the drawn ear.**

`EarCrosscut.splitGraph_eq` says the new drawn graph is the union of the old one with the drawn
ear; `Graph.pointSet_union` splits the point set of that union; and `Graph.pointSet_congr`
replaces the split drawing by the drawing each half came with. -/
theorem skeletonSet_realize {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
    (hE : d.EarCrosscut R earPos earDraw) :
    (d.realize R earPos earDraw hE).skeletonSet = R.skeletonSet ∪ d.earSet earPos earDraw := by
  have hstep : (d.realize R earPos earDraw hE).skeletonSet =
      Graph.pointSet (R.graph.union (d.earGraph earPos)) (d.splitDrawing R earDraw) := by
    rw [← hE.splitGraph_eq]
    rfl
  rw [hstep, Graph.pointSet_union]
  congr 1
  · exact Graph.pointSet_congr fun e he =>
      edgeArc_splitDrawing_of_mem_skel (by rwa [Realization.edgeSet_graph] at he)
  · exact Graph.pointSet_congr fun e he =>
      edgeArc_splitDrawing_of_mem_ear (by rwa [d.edgeSet_earGraph] at he)

/-- The drawn ear is closed: it is a simple arc, hence compact. -/
theorem isClosed_earSet {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
    (hE : d.EarCrosscut R earPos earDraw) : IsClosed (d.earSet earPos earDraw) :=
  hE.isArcBetween_earSet.isArc.isCompact.isClosed

/-! ## The chosen homeomorphism between the two drawn ears -/

/-- **The chosen homeomorphism between two drawings of one abstract ear.**

This is `def:matched-pair` clause 3 restricted to the cells the split creates: a homeomorphism
between the two drawn ears which matches corresponding vertices and corresponding edges. It is
data, not a proposition, and it mentions neither realization: everything it says is a statement
about the two drawings of `d.ear`.

`earPos_apply` and `edgeArc_image` are the two matching clauses. Together they force
`toFun '' (source ear) = (target ear)` (`EarHomeo.image_earSet`), which is why no separate
surjectivity clause is asked for. The inverse is supplied as data, exactly as in
`CellStructure.SkeletonHomeo`, so that no compactness argument is needed to speak of a
homeomorphism. -/
structure EarHomeo (d : S.SplitData) (earPos₁ : γ → Plane) (earDraw₁ : γ → ℝ → Plane)
    (earPos₂ : γ → Plane) (earDraw₂ : γ → ℝ → Plane) where
  /-- The map. -/
  toFun : Plane → Plane
  /-- Its inverse. -/
  invFun : Plane → Plane
  /-- The map is continuous on the source ear. -/
  continuousOn_toFun : ContinuousOn toFun (d.earSet earPos₁ earDraw₁)
  /-- The inverse is continuous on the target ear. -/
  continuousOn_invFun : ContinuousOn invFun (d.earSet earPos₂ earDraw₂)
  /-- The inverse undoes the map. -/
  leftInvOn : LeftInvOn invFun toFun (d.earSet earPos₁ earDraw₁)
  /-- The map undoes the inverse. -/
  rightInvOn : RightInvOn invFun toFun (d.earSet earPos₂ earDraw₂)
  /-- Corresponding vertices of the ear correspond. -/
  earPos_apply : ∀ ⦃z⦄, z ∈ V(d.ear) → toFun (earPos₁ z) = earPos₂ z
  /-- Corresponding edges of the ear correspond. -/
  edgeArc_image : ∀ ⦃f⦄, f ∈ E(d.ear) →
    toFun '' Graph.edgeArc earDraw₁ f = Graph.edgeArc earDraw₂ f

namespace EarHomeo

variable {earPos₁ earPos₂ : γ → Plane} {earDraw₁ earDraw₂ : γ → ℝ → Plane}
  (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂)

/-- **The chosen map carries the source ear onto the target ear.** The point set of a drawn
graph is its vertices together with its edge arcs, and the two matching clauses handle those
two halves. -/
theorem image_earSet :
    m.toFun '' d.earSet earPos₁ earDraw₁ = d.earSet earPos₂ earDraw₂ := by
  rw [earSet, earSet, Graph.pointSet, Graph.pointSet, Set.image_union, Set.image_iUnion₂]
  congr 1
  · rw [d.vertexSet_earGraph, d.vertexSet_earGraph, ← Set.image_comp]
    exact Set.image_congr fun z hz => m.earPos_apply hz
  · rw [d.edgeSet_earGraph, d.edgeSet_earGraph]
    exact Set.iUnion₂_congr fun f hf => m.edgeArc_image hf

theorem injOn : InjOn m.toFun (d.earSet earPos₁ earDraw₁) := m.leftInvOn.injOn

theorem mapsTo :
    MapsTo m.toFun (d.earSet earPos₁ earDraw₁) (d.earSet earPos₂ earDraw₂) :=
  fun _ hx => m.image_earSet ▸ Set.mem_image_of_mem _ hx

/-- The inverse carries the target ear back into the source ear. Not a field: every point of
the target ear is the image of a point of the source ear, and there the inverse is a left
inverse. -/
theorem mapsTo_invFun :
    MapsTo m.invFun (d.earSet earPos₂ earDraw₂) (d.earSet earPos₁ earDraw₁) := by
  intro y hy
  rw [← m.image_earSet] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [m.leftInvOn hx]
  exact hx

/-- Reverse a chosen matching of two realized ears.  Direction (b) of finite transfer first
constructs the ear on the target side, so it naturally obtains the matching in the opposite
direction from the one consumed by `GeneratedPair.split`. -/
def symm : d.EarHomeo earPos₂ earDraw₂ earPos₁ earDraw₁ where
  toFun := m.invFun
  invFun := m.toFun
  continuousOn_toFun := m.continuousOn_invFun
  continuousOn_invFun := m.continuousOn_toFun
  leftInvOn := m.rightInvOn
  rightInvOn := m.leftInvOn
  earPos_apply := by
    intro z hz
    rw [← m.earPos_apply hz]
    apply m.leftInvOn
    exact Graph.vertexSet_subset_pointSet (by
      rw [d.vertexSet_earGraph]
      exact ⟨z, hz, rfl⟩)
  edgeArc_image := by
    intro f hf
    rw [← m.edgeArc_image hf]
    exact m.leftInvOn.image_image'
      (Graph.edgeArc_subset_pointSet (by rw [d.edgeSet_earGraph]; exact hf))

@[simp] theorem symm_toFun : m.symm.toFun = m.invFun := rfl

@[simp] theorem symm_invFun : m.symm.invFun = m.toFun := rfl

variable {R₁ R₂ : S.Realization}

/-- **At the ear's source end the chosen map is pinned to the old 0-cell's target position.**
This — with `SkeletonHomeo.pos_apply` — is why no compatibility hypothesis between the ear map
and `g` has to be asked for. -/
theorem toFun_pos_source (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.toFun (R₁.pos d.source) = R₂.pos d.source := by
  rw [← hE₁.pos_source, m.earPos_apply d.source_mem_ear, hE₂.pos_source]

theorem toFun_pos_target (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.toFun (R₁.pos d.target) = R₂.pos d.target := by
  rw [← hE₁.pos_target, m.earPos_apply d.target_mem_ear, hE₂.pos_target]

theorem invFun_pos_source (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.invFun (R₂.pos d.source) = R₁.pos d.source := by
  rw [← m.toFun_pos_source hE₁ hE₂, m.leftInvOn hE₁.pos_source_mem_earSet]

theorem invFun_pos_target (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.invFun (R₂.pos d.target) = R₁.pos d.target := by
  rw [← m.toFun_pos_target hE₁ hE₂, m.leftInvOn hE₁.pos_target_mem_earSet]

end EarHomeo

/-! ## The transported map -/

variable {R₁ R₂ : S.Realization} {earPos₁ earPos₂ : γ → Plane}
  {earDraw₁ earDraw₂ : γ → ℝ → Plane}

open scoped Classical in
/-- **The transported skeleton map**: `g` on the old realized skeleton, the chosen ear map off
it. Written with a test on the old skeleton rather than on the ear so that agreement with `g`
— `splitHomeo_eqOn`, i.e. `StageSequence.skelHomeo_succ` — holds by definition. -/
noncomputable def splitMap (g : SkeletonHomeo R₁ R₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) : Plane → Plane :=
  fun x => if x ∈ R₁.skeletonSet then g.toFun x else m.toFun x

open scoped Classical in
/-- The transported inverse, by the same recipe on the target side. -/
noncomputable def splitInvMap (g : SkeletonHomeo R₁ R₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) : Plane → Plane :=
  fun y => if y ∈ R₂.skeletonSet then g.invFun y else m.invFun y

variable {g : SkeletonHomeo R₁ R₂} {m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂}

theorem splitMap_of_mem_skeletonSet {x : Plane} (hx : x ∈ R₁.skeletonSet) :
    splitMap g m x = g.toFun x := by
  classical
  simp only [splitMap, if_pos hx]

theorem splitMap_eqOn_skeletonSet : EqOn (splitMap g m) g.toFun R₁.skeletonSet :=
  fun _ hx => splitMap_of_mem_skeletonSet hx

theorem splitInvMap_of_mem_skeletonSet {y : Plane} (hy : y ∈ R₂.skeletonSet) :
    splitInvMap g m y = g.invFun y := by
  classical
  simp only [splitInvMap, if_pos hy]

theorem splitInvMap_of_notMem_skeletonSet {y : Plane} (hy : y ∉ R₂.skeletonSet) :
    splitInvMap g m y = m.invFun y := by
  classical
  simp only [splitInvMap, if_neg hy]

variable (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁) (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂)

include hE₁ hE₂

/-- **On the drawn ear the transported map is the chosen ear map** — including at the two ends,
where the two prescriptions agree because both are pinned to the target position of the old
0-cell. -/
theorem splitMap_of_mem_earSet {x : Plane} (hx : x ∈ d.earSet earPos₁ earDraw₁) :
    splitMap g m x = m.toFun x := by
  classical
  by_cases hs : x ∈ R₁.skeletonSet
  · rw [splitMap, if_pos hs]
    have hends := hE₁.earSet_inter_skeletonSet ⟨hx, hs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with rfl | rfl
    · rw [g.pos_apply d.source_mem_skel, m.toFun_pos_source hE₁ hE₂]
    · rw [g.pos_apply d.target_mem_skel, m.toFun_pos_target hE₁ hE₂]
  · rw [splitMap, if_neg hs]

theorem splitMap_eqOn_earSet : EqOn (splitMap g m) m.toFun (d.earSet earPos₁ earDraw₁) :=
  fun _ hx => splitMap_of_mem_earSet hE₁ hE₂ hx

/-- On the drawn target ear the transported inverse is the chosen ear map's inverse. -/
theorem splitInvMap_eqOn_earSet :
    EqOn (splitInvMap g m) m.invFun (d.earSet earPos₂ earDraw₂) := by
  classical
  intro y hy
  by_cases hs : y ∈ R₂.skeletonSet
  · rw [splitInvMap, if_pos hs]
    have hends := hE₂.earSet_inter_skeletonSet ⟨hy, hs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with rfl | rfl
    · have h : g.invFun (R₂.pos d.source) = R₁.pos d.source := g.symm.pos_apply d.source_mem_skel
      rw [h, m.invFun_pos_source hE₁ hE₂]
    · have h : g.invFun (R₂.pos d.target) = R₁.pos d.target := g.symm.pos_apply d.target_mem_skel
      rw [h, m.invFun_pos_target hE₁ hE₂]
  · rw [splitInvMap, if_neg hs]

/-- **A point of the source ear off the old skeleton is carried off the old target skeleton.**
The image lies on the target ear, and the target ear meets the target skeleton only in the two
ends — whose preimages under the (injective) ear map are the two ends on the source side, which
*are* on the source skeleton. -/
theorem toFun_notMem_skeletonSet {x : Plane} (hx : x ∈ d.earSet earPos₁ earDraw₁)
    (hs : x ∉ R₁.skeletonSet) : m.toFun x ∉ R₂.skeletonSet := by
  intro hcon
  have hends := hE₂.earSet_inter_skeletonSet ⟨m.mapsTo hx, hcon⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
  rcases hends with heq | heq
  · rw [← m.toFun_pos_source hE₁ hE₂] at heq
    exact hs (m.injOn hx hE₁.pos_source_mem_earSet heq ▸ R₁.pos_mem_skeletonSet d.source_mem_skel)
  · rw [← m.toFun_pos_target hE₁ hE₂] at heq
    exact hs (m.injOn hx hE₁.pos_target_mem_earSet heq ▸ R₁.pos_mem_skeletonSet d.target_mem_skel)

/-! ## The skeleton homeomorphism across the split -/

/-- **The skeleton homeomorphism, transported across a 2-cell split.**

Given two realizations of one abstract cell structure, the skeleton homeomorphism `g` between
them, a drawing of the ear as a polygonal crosscut on *each* side, and the chosen homeomorphism
between the two drawn ears, this is the skeleton homeomorphism between the two split
realizations — `def:matched-pair` clause 3 for the structure `S.splitFace d`.

It is an *extension* of `g`, not a new map: `splitHomeo_eqOn` says it agrees with `g` on the
whole old realized skeleton, which is precisely the field `StageSequence.skelHomeo_succ`. -/
noncomputable def splitHomeo (g : SkeletonHomeo R₁ R₂)
    (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁) (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) :
    SkeletonHomeo (d.realize R₁ earPos₁ earDraw₁ hE₁) (d.realize R₂ earPos₂ earDraw₂ hE₂) where
  toFun := splitMap g m
  invFun := splitInvMap g m
  continuousOn_toFun := by
    rw [skeletonSet_realize hE₁]
    refine Plane.continuousOn_union_of_isClosed R₁.isCompact_skeletonSet.isClosed
      (isClosed_earSet hE₁) (g.continuousOn_toFun.congr splitMap_eqOn_skeletonSet) ?_
    exact m.continuousOn_toFun.congr (splitMap_eqOn_earSet hE₁ hE₂)
  continuousOn_invFun := by
    rw [skeletonSet_realize hE₂]
    refine Plane.continuousOn_union_of_isClosed R₂.isCompact_skeletonSet.isClosed
      (isClosed_earSet hE₂) (g.continuousOn_invFun.congr fun _ hy =>
        splitInvMap_of_mem_skeletonSet hy) ?_
    exact m.continuousOn_invFun.congr (splitInvMap_eqOn_earSet hE₁ hE₂)
  leftInvOn := by
    rw [skeletonSet_realize hE₁]
    rintro x (hx | hx)
    · rw [splitMap_of_mem_skeletonSet hx,
        splitInvMap_of_mem_skeletonSet (g.image_skeletonSet ▸ Set.mem_image_of_mem _ hx),
        g.leftInvOn hx]
    · by_cases hs : x ∈ R₁.skeletonSet
      · rw [splitMap_of_mem_skeletonSet hs,
          splitInvMap_of_mem_skeletonSet (g.image_skeletonSet ▸ Set.mem_image_of_mem _ hs),
          g.leftInvOn hs]
      · rw [splitMap_of_mem_earSet hE₁ hE₂ hx,
          splitInvMap_of_notMem_skeletonSet (toFun_notMem_skeletonSet hE₁ hE₂ hx hs),
          m.leftInvOn hx]
  rightInvOn := by
    rw [skeletonSet_realize hE₂]
    rintro y (hy | hy)
    · rw [splitInvMap_of_mem_skeletonSet hy,
        splitMap_of_mem_skeletonSet (g.symm.image_skeletonSet ▸ Set.mem_image_of_mem _ hy),
        g.rightInvOn hy]
    · by_cases hs : y ∈ R₂.skeletonSet
      · rw [splitInvMap_of_mem_skeletonSet hs,
          splitMap_of_mem_skeletonSet (g.symm.image_skeletonSet ▸ Set.mem_image_of_mem _ hs),
          g.rightInvOn hs]
      · rw [splitInvMap_of_notMem_skeletonSet hs,
          splitMap_of_mem_earSet hE₁ hE₂ (m.mapsTo_invFun hy), m.rightInvOn hy]
  pos_apply := by
    intro v hv
    have hv' : v ∈ V(S.skel) ∪ V(d.ear) := hv
    rcases hv' with hv' | hv'
    · change splitMap g m (d.splitPos R₁ earPos₁ v) = d.splitPos R₂ earPos₂ v
      rw [hE₁.splitPos_eq hv', hE₂.splitPos_eq hv',
        splitMap_of_mem_skeletonSet (R₁.pos_mem_skeletonSet hv'), g.pos_apply hv']
    · change splitMap g m (d.splitPos R₁ earPos₁ v) = d.splitPos R₂ earPos₂ v
      rw [splitPos_of_mem_ear hv', splitPos_of_mem_ear hv',
        splitMap_of_mem_earSet hE₁ hE₂ (EarCrosscut.mem_earSet_of_mem_ear hv'),
        m.earPos_apply hv']
  edgeArc_image := by
    intro e he
    have he' : e ∈ E(S.skel) ∪ E(d.ear) := he
    rcases he' with he' | he'
    · change splitMap g m '' Graph.edgeArc (d.splitDrawing R₁ earDraw₁) e =
        Graph.edgeArc (d.splitDrawing R₂ earDraw₂) e
      rw [edgeArc_splitDrawing_of_mem_skel he', edgeArc_splitDrawing_of_mem_skel he',
        Set.image_congr (fun x hx => splitMap_of_mem_skeletonSet
          (Graph.edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph]) hx)),
        g.edgeArc_image he']
    · change splitMap g m '' Graph.edgeArc (d.splitDrawing R₁ earDraw₁) e =
        Graph.edgeArc (d.splitDrawing R₂ earDraw₂) e
      rw [edgeArc_splitDrawing_of_mem_ear he', edgeArc_splitDrawing_of_mem_ear he',
        Set.image_congr (fun x hx => splitMap_of_mem_earSet hE₁ hE₂
          (EarCrosscut.edgeArc_subset_earSet he' hx)),
        m.edgeArc_image he']

@[simp] theorem splitHomeo_toFun : (splitHomeo g hE₁ hE₂ m).toFun = splitMap g m := rfl

@[simp] theorem splitHomeo_invFun : (splitHomeo g hE₁ hE₂ m).invFun = splitInvMap g m := rfl

end SplitData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.SkeletonLocal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Local structure of a polygonal skeleton

Close enough to any of its points, a finite union of segments and points looks like a *star*:
the point itself together with finitely many radial segments leaving it, one per local branch.
This module proves that, and hands the accessibility argument the form it needs.

## What is exported, and why in this shape

The data is `Schoenflies.localDirs S x`, the set of unit vectors `d` such that some initial
segment `[x, x + ε • d]` lies in `S`. It is defined for an arbitrary set, with no choices in
it: nothing about a segment decomposition of `S` enters the definition, so no consumer has to
carry one. "Pairwise distinct directions" is then not a clause to be proved but the meaning of
the word *set*, and the blueprint's real content becomes `localDirs_finite`.

The radius is the one genuinely existential ingredient — there is no canonical `r₀` — so it is
named by a predicate rather than returned inside an `∃`-packaged bundle of properties:

  `Schoenflies.IsLocalRadius S x r` : `0 < r`, and every point within `r` of `x` lies in `S`
  exactly when it is `x` itself or leaves `x` in a local direction.

That single membership criterion is equivalent to the blueprint's picture and implies all of
its parts, each proved here as a lemma about `IsLocalRadius` and hence available at every
radius below the one produced: the closed-disk formula
(`IsLocalRadius.closedBall_inter`), the open disk minus `S` as a *cone* over the complement of
the local rays (`IsLocalRadius.ball_diff_eq_cone`), and the star-shapedness that the
accessibility lemma actually cites (`IsLocalRadius.openSegment_subset_ball_diff`).

## What the consumer (`lem:polygonal-side-accessibility`) needs

That lemma takes `y` in a face `F` inside the disk, and wants a polygonal arc from `x` into
`F`. `IsLocalRadius.openSegment_subset_ball_diff` gives `(x, y) ⊆ B(x, r) \ S` directly, and
`openSegment ℝ x y ∪ {y}` is connected and disjoint from the skeleton — which is everything
the blueprint's "pick the sector containing `y`, then a short segment from `x` into it" is used
for. The decomposition of the punctured disk into its *individual* sectors, one per pair of
cyclically adjacent local directions, is therefore **not** proved here: it needs a cyclic
order on directions, and no consumer needs it. `IsLocalRadius.ball_diff_eq_cone` records the
sectors in aggregate — as one `Plane.cone` over all free directions at once.

## Blueprint

* `Schoenflies.localDirs`, `Schoenflies.localDirs_finite` — the finitely many local branch
  directions at `x` of Lemma "Local structure of a polygonal skeleton"
  (`lem:local-skeleton-structure`).
* `Schoenflies.IsLocalRadius`, `Schoenflies.exists_isLocalRadius`,
  `Schoenflies.IsLocalRadius.closedBall_inter` — the radius `r₀`, and "for every `0 < r ≤ r₀`
  the closed disk meets `|G|` exactly in finitely many straight segments from `x` with
  pairwise distinct directions" (same lemma).
* `Schoenflies.IsLocalRadius.ball_diff_eq_cone` — "consequently `B(x,r) \ |G|` is a finite
  union of open circular sectors" (same lemma), in aggregate form.
* `Schoenflies.IsLocalRadius.openSegment_subset_ball_diff` — the form
  `lem:polygonal-side-accessibility` cites: a short straight segment from `x` towards any
  point of the punctured disk misses the skeleton.
* `Graph.IsDrawing.exists_cover`, `Graph.IsDrawing.exists_isLocalRadius`,
  `Graph.IsDrawing.finite_localDirs` — the same statements for a finite plane graph all of
  whose edges are polygonal.
* `Graph.IsDrawing.openSegment_subset_face` — the access arc of
  `lem:polygonal-side-accessibility`, assembled: a straight segment from `x` to a point of the
  exterior inside a local disk lies, minus `x`, in that point's face.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

variable {S T F : Set Plane} {ps : List Piece} {x y z c d : Plane} {r R ε t : ℝ}

/-! ### Radial segments

`segment ℝ x (x + r • d)` with `d` a unit vector is the closed radius of length `r` leaving
`x` in the direction `d`. Two facts run the whole module: a point lies on it exactly when it
is near enough and points the right way (`mem_radial_iff`), and cutting a longer radius by a
smaller ball leaves the shorter radius (`radial_inter_closedBall`). -/

/-- The unit vector along a positive multiple of a unit vector is that vector. -/
theorem dir_smul_of_isDirection (hd : Plane.IsDirection d) (ht : 0 < t) :
    Plane.dir (t • d) = d := by
  have hn : ‖t • d‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hd.norm, mul_one]
  rw [Plane.dir, hn, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

/-- A nonzero vector is its own length times its own direction. -/
theorem smul_norm_dir (h : d ≠ 0) : ‖d‖ • Plane.dir d = d := by
  rw [Plane.dir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]

/-- Membership in a radius: near enough, and pointing the right way. -/
theorem mem_radial_iff (hd : Plane.IsDirection d) (hr : 0 < r) :
    z ∈ segment ℝ x (x + r • d) ↔ dist z x ≤ r ∧ (z = x ∨ Plane.dir (z - x) = d) := by
  constructor
  · intro hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    have hsub : x + θ • (x + r • d - x) - x = (θ * r) • d := by module
    have hnorm : dist (x + θ • (x + r • d - x)) x = θ * r := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), hd.norm, mul_one]
    refine ⟨by rw [hnorm]; nlinarith, ?_⟩
    rcases eq_or_lt_of_le hθ0 with rfl | hθpos
    · left; simp
    · exact Or.inr (by rw [hsub, dir_smul_of_isDirection hd (by positivity)])
  · rintro ⟨hdist, hz⟩
    rcases eq_or_ne z x with rfl | hzx
    · exact left_mem_segment ℝ _ _
    have hdir : Plane.dir (z - x) = d := hz.resolve_left hzx
    have hne : z - x ≠ 0 := sub_ne_zero.2 hzx
    have hL : ‖z - x‖ • d = z - x := by rw [← hdir]; exact smul_norm_dir hne
    have hdn : ‖z - x‖ ≤ r := by rwa [dist_eq_norm] at hdist
    -- The parameter is the fraction of the radius already travelled.
    refine ⟨1 - ‖z - x‖ / r, ‖z - x‖ / r, by
      have := (div_le_one hr).2 hdn; linarith, by positivity, by ring, ?_⟩
    have hθ : ‖z - x‖ / r * r = ‖z - x‖ := div_mul_cancel₀ _ hr.ne'
    calc (1 - ‖z - x‖ / r) • x + (‖z - x‖ / r) • (x + r • d)
        = x + (‖z - x‖ / r * r) • d := by module
      _ = x + ‖z - x‖ • d := by rw [hθ]
      _ = z := by rw [hL]; module

/-- Cutting a radius by a smaller concentric disk leaves the shorter radius. -/
theorem radial_inter_closedBall (hd : Plane.IsDirection d) (hr : 0 < r) (hrR : r ≤ R) :
    segment ℝ x (x + R • d) ∩ closedBall x r = segment ℝ x (x + r • d) := by
  ext z
  simp only [mem_inter_iff, mem_closedBall, mem_radial_iff hd (lt_of_lt_of_le hr hrR),
    mem_radial_iff hd hr]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hrR, h.2⟩, h.1⟩⟩

/-- A segment out of `x` is the radius of its own length in its own direction. -/
theorem segment_eq_radial (h : c ≠ x) :
    segment ℝ x c = segment ℝ x (x + dist x c • Plane.dir (c - x)) := by
  have hne : c - x ≠ 0 := sub_ne_zero.2 h
  have : x + dist x c • Plane.dir (c - x) = c := by
    rw [dist_eq_norm', smul_norm_dir hne]
    module
  rw [this]

/-- **Inside a disk too small to reach `c`, the segment `[x, c]` is exactly a radius.** This is
the one geometric step behind the whole module: it turns each straight piece through `x` into
one or two radial segments. -/
theorem segment_inter_closedBall (hcx : c ≠ x) (hr : 0 < r) (hrc : r ≤ dist x c) :
    segment ℝ x c ∩ closedBall x r = segment ℝ x (x + r • Plane.dir (c - x)) := by
  rw [segment_eq_radial hcx]
  exact radial_inter_closedBall (Plane.isDirection_dir (sub_ne_zero.2 hcx)) hr hrc

/-! ### The local directions of a set -/

/-- The *local directions* of `S` at `x`: the unit vectors along which `S` contains an initial
segment issuing from `x`.

Choice-free and stated for an arbitrary set, so that a consumer never has to name a segment
decomposition of `S`. Being a *set* of unit vectors, its members are automatically pairwise
distinct — the blueprint's "with pairwise distinct directions". -/
def localDirs (S : Set Plane) (x : Plane) : Set Plane :=
  {d | Plane.IsDirection d ∧ ∃ ε : ℝ, 0 < ε ∧ segment ℝ x (x + ε • d) ⊆ S}

/-! ### The pieces through a point

Everything is now bookkeeping over a finite list of segments and a finite set of stray points.
`GoodRadius x P r` collects what a radius must avoid on account of one piece: pieces missing
`x` must stay outside the disk, and pieces through `x` must not end inside it. -/

/-- The radius conditions imposed at `x` by one piece: a piece missing `x` stays clear of the
closed disk, and an endpoint of a piece through `x` is never inside it. -/
def GoodRadius (x : Plane) (P : Piece) (r : ℝ) : Prop :=
  (x ∉ P.seg → ∀ z ∈ P.seg, r < dist x z) ∧
    (P.1 ≠ x → r ≤ dist x P.1) ∧ (P.2 ≠ x → r ≤ dist x P.2)

theorem GoodRadius.mono {P : Piece} (h : GoodRadius x P r) (hle : ε ≤ r) :
    GoodRadius x P ε :=
  ⟨fun hx z hz => lt_of_le_of_lt hle (h.1 hx z hz), fun h1 => hle.trans (h.2.1 h1),
    fun h2 => hle.trans (h.2.2 h2)⟩

theorem exists_goodRadius (x : Plane) (P : Piece) : ∃ r > 0, GoodRadius x P r := by
  by_cases hx : x ∈ P.seg
  · -- Only the endpoints matter; a coincident endpoint imposes nothing.
    refine ⟨min (if P.1 = x then 1 else dist x P.1) (if P.2 = x then 1 else dist x P.2), ?_,
      fun h => absurd hx h, ?_, ?_⟩
    · refine lt_min ?_ ?_ <;> split_ifs with h
      · exact one_pos
      · exact dist_pos.2 (Ne.symm h)
      · exact one_pos
      · exact dist_pos.2 (Ne.symm h)
    · intro h1
      exact le_trans (min_le_left _ _) (le_of_eq (if_neg h1))
    · intro h2
      exact le_trans (min_le_right _ _) (le_of_eq (if_neg h2))
  · -- A piece missing `x` is a compact set at positive distance from `x`.
    obtain ⟨ρ, hρ, hd⟩ := Plane.exists_dist_pos isCompact_singleton (isCompact_segment P.1 P.2)
      (Set.disjoint_singleton_left.2 hx)
    have hall : ∀ z ∈ P.seg, ρ ≤ dist x z := fun z hz => hd x rfl z hz
    refine ⟨ρ / 2, by positivity, fun _ z hz => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact lt_of_lt_of_le (by linarith) (hall z hz)
    · exact le_trans (by linarith) (hall P.1 (left_mem_segment ℝ _ _))
    · exact le_trans (by linarith) (hall P.2 (right_mem_segment ℝ _ _))

/-- Auxiliary: the directions in which the pieces of `ps` leave `x`. Unlike `localDirs` this
depends on the chosen segment decomposition; the two are proved equal at any good radius. -/
def pieceDirs (ps : List Piece) (x : Plane) : Set Plane :=
  {d | ∃ P ∈ ps, x ∈ P.seg ∧
    ((P.1 ≠ x ∧ d = Plane.dir (P.1 - x)) ∨ (P.2 ≠ x ∧ d = Plane.dir (P.2 - x)))}

theorem isDirection_of_mem_pieceDirs (h : d ∈ pieceDirs ps x) : Plane.IsDirection d := by
  obtain ⟨P, -, -, (⟨h1, rfl⟩ | ⟨h2, rfl⟩)⟩ := h
  · exact Plane.isDirection_dir (sub_ne_zero.2 h1)
  · exact Plane.isDirection_dir (sub_ne_zero.2 h2)

/-- A radius in a piece direction, at a good radius, stays inside the pieces. -/
theorem radial_subset_cover (hgood : ∀ P ∈ ps, GoodRadius x P r) (hr : 0 < r)
    (hd : d ∈ pieceDirs ps x) : segment ℝ x (x + r • d) ⊆ cover ps := by
  obtain ⟨P, hP, hxP, hcase⟩ := hd
  -- Both cases are the same computation with the two endpoints exchanged.
  have key : ∀ c ∈ P.seg, c ≠ x → r ≤ dist x c →
      segment ℝ x (x + r • Plane.dir (c - x)) ⊆ cover ps := by
    intro c hc hcx hrc
    have h1 : segment ℝ x (x + r • Plane.dir (c - x)) ⊆ segment ℝ x c := by
      rw [← segment_inter_closedBall hcx hr hrc]
      exact inter_subset_left
    have h2 : segment ℝ x c ⊆ P.seg := (convex_segment P.1 P.2).segment_subset hxP hc
    exact h1.trans (h2.trans (Set.subset_biUnion_of_mem (u := fun P : Piece => P.seg) hP))
  rcases hcase with ⟨h1, rfl⟩ | ⟨h2, rfl⟩
  · exact key P.1 (left_mem_segment ℝ _ _) h1 ((hgood P hP).2.1 h1)
  · exact key P.2 (right_mem_segment ℝ _ _) h2 ((hgood P hP).2.2 h2)

/-- At a good radius, the pieces meet the closed disk only in `x` and the radii. -/
theorem cover_inter_closedBall_subset (hgood : ∀ P ∈ ps, GoodRadius x P r) (hr : 0 < r) :
    cover ps ∩ closedBall x r ⊆ insert x (⋃ d ∈ pieceDirs ps x, segment ℝ x (x + r • d)) := by
  rintro z ⟨hzc, hzb⟩
  obtain ⟨P, hP, hzP⟩ : ∃ P ∈ ps, z ∈ P.seg := by
    simpa only [cover, mem_iUnion, exists_prop] using hzc
  have hdist : dist x z ≤ r := by rw [dist_comm]; exact mem_closedBall.1 hzb
  -- A piece meeting the disk at all must pass through `x`.
  have hxP : x ∈ P.seg := by
    by_contra hx
    exact absurd hdist (not_le.2 ((hgood P hP).1 hx z hzP))
  -- Split the piece at `x`; each half is a radius, unless it has collapsed onto `x`.
  rw [Piece.seg, segment_split hxP] at hzP
  rcases hzP with hz | hz
  · rw [segment_symm] at hz
    rcases eq_or_ne P.1 x with h1 | h1
    · rw [h1, segment_same] at hz
      exact Or.inl hz
    · have hmem : Plane.dir (P.1 - x) ∈ pieceDirs ps x := ⟨P, hP, hxP, Or.inl ⟨h1, rfl⟩⟩
      refine Or.inr (mem_biUnion hmem ?_)
      rw [← segment_inter_closedBall h1 hr ((hgood P hP).2.1 h1)]
      exact ⟨hz, hzb⟩
  · rcases eq_or_ne P.2 x with h2 | h2
    · rw [h2, segment_same] at hz
      exact Or.inl hz
    · have hmem : Plane.dir (P.2 - x) ∈ pieceDirs ps x := ⟨P, hP, hxP, Or.inr ⟨h2, rfl⟩⟩
      refine Or.inr (mem_biUnion hmem ?_)
      rw [← segment_inter_closedBall h2 hr ((hgood P hP).2.2 h2)]
      exact ⟨hz, hzb⟩

/-! ### The membership criterion -/

/-- **`r` is a local radius for `S` at `x`**: within distance `r` of `x`, the set `S` consists
of `x` together with the rays leaving `x` in the local directions.

This one criterion is the whole local picture; the disk formula, the sector description and
the star-shapedness are all derived from it below, and each therefore holds at every positive
radius below a local radius (`IsLocalRadius.mono`). -/
def IsLocalRadius (S : Set Plane) (x : Plane) (r : ℝ) : Prop :=
  0 < r ∧ ∀ z, dist z x ≤ r → (z ∈ S ↔ z = x ∨ Plane.dir (z - x) ∈ localDirs S x)

/-! ### A local radius exists

The construction: choose a radius good for every piece and strictly below the distance to
every stray point other than `x`. -/

theorem exists_pos_goodRadius (hF : F.Finite) (ps : List Piece) (x : Plane) :
    ∃ r > 0, (∀ P ∈ ps, GoodRadius x P r) ∧ ∀ p ∈ F, p ≠ x → r < dist x p := by
  obtain ⟨r₁, hr₁, h₁⟩ :=
    exists_pos_forall_of_finite (List.finite_toSet ps) (P := fun P r => GoodRadius x P r)
      (fun _ _ _ _ hle h => h.mono hle) (fun P _ => exists_goodRadius x P)
  have hex : ∀ p ∈ F, ∃ ε > 0, (p ≠ x → ε < dist x p) := by
    intro p _
    rcases eq_or_ne p x with rfl | hne
    · exact ⟨1, one_pos, fun h => absurd rfl h⟩
    · have hpos : 0 < dist x p := dist_pos.2 (Ne.symm hne)
      exact ⟨dist x p / 2, half_pos hpos, fun _ => by linarith⟩
  obtain ⟨r₂, hr₂, h₂⟩ :=
    exists_pos_forall_of_finite hF (P := fun p r => p ≠ x → r < dist x p)
      (fun _ _ _ _ hle h hne => lt_of_le_of_lt hle (h hne)) hex
  exact ⟨min r₁ r₂, lt_min hr₁ hr₂,
    fun P hP => (h₁ P hP).mono (min_le_left _ _),
    fun p hp hne => lt_of_le_of_lt (min_le_right _ _) (h₂ p hp hne)⟩

/-- Every piece direction is a local direction: at a good radius the whole radius fits in the
pieces. -/
theorem pieceDirs_subset_localDirs (hS : S = F ∪ cover ps) (hr : 0 < r)
    (hgood : ∀ P ∈ ps, GoodRadius x P r) : pieceDirs ps x ⊆ localDirs S x := fun _ hd =>
  ⟨isDirection_of_mem_pieceDirs hd, r, hr,
    (radial_subset_cover hgood hr hd).trans (hS ▸ subset_union_right)⟩

/-- The membership criterion, phrased with the auxiliary `pieceDirs`. -/
theorem mem_iff_of_goodRadius (hS : S = F ∪ cover ps) (hr : 0 < r) (hx : x ∈ S)
    (hgood : ∀ P ∈ ps, GoodRadius x P r) (hFgood : ∀ p ∈ F, p ≠ x → r < dist x p)
    (hz : dist z x ≤ r) : z ∈ S ↔ z = x ∨ Plane.dir (z - x) ∈ pieceDirs ps x := by
  constructor
  · intro hzS
    rcases eq_or_ne z x with rfl | hzx
    · exact Or.inl rfl
    rw [hS] at hzS
    rcases hzS with hzF | hzc
    · -- A stray point inside the disk can only be `x` itself.
      exact absurd (hFgood z hzF hzx) (not_lt.2 (by rw [dist_comm]; exact hz))
    · rcases cover_inter_closedBall_subset hgood hr ⟨hzc, mem_closedBall.2 hz⟩ with h | h
      · exact absurd h hzx
      · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 h
        have := (mem_radial_iff (isDirection_of_mem_pieceDirs hd) hr).1 hzd
        exact Or.inr (((this.2.resolve_left hzx)) ▸ hd)
  · rintro (rfl | hd)
    · exact hx
    rcases eq_or_ne z x with rfl | hzx
    · exact hx
    have hmem : z ∈ segment ℝ x (x + r • Plane.dir (z - x)) :=
      (mem_radial_iff (isDirection_of_mem_pieceDirs hd) hr).2 ⟨hz, Or.inr rfl⟩
    exact hS ▸ Or.inr (radial_subset_cover hgood hr hd hmem)

/-- Conversely, at a good radius every local direction comes from a piece. This is where the
germ hypothesis in `localDirs` is cashed in: a short segment in `S` leaving `x` lands in a
piece, and that piece must pass through `x`. -/
theorem localDirs_subset_pieceDirs (hS : S = F ∪ cover ps) (hr : 0 < r)
    (hgood : ∀ P ∈ ps, GoodRadius x P r) (hFgood : ∀ p ∈ F, p ≠ x → r < dist x p) :
    localDirs S x ⊆ pieceDirs ps x := by
  rintro d hd
  obtain ⟨hdir, ε, hε, hsub⟩ := hd
  have hx : x ∈ S := hsub (left_mem_segment ℝ _ _)
  set t := min ε r with ht
  have htpos : 0 < t := lt_min hε hr
  -- Walk a distance `t` along the germ; the point reached is in `S` and inside the disk.
  have hmem : x + t • d ∈ segment ℝ x (x + ε • d) :=
    (mem_radial_iff hdir hε).2 ⟨by
        rw [dist_eq_norm, show x + t • d - x = t • d by module, norm_smul, Real.norm_eq_abs,
          abs_of_pos htpos, hdir.norm, mul_one]
        exact min_le_left _ _,
      Or.inr (by rw [show x + t • d - x = t • d by module, dir_smul_of_isDirection hdir htpos])⟩
  have hdist : dist (x + t • d) x ≤ r := by
    rw [dist_eq_norm, show x + t • d - x = t • d by module, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos, hdir.norm, mul_one]
    exact min_le_right _ _
  have hne : x + t • d ≠ x := by
    intro h
    have : t • d = 0 := by
      have := sub_eq_zero.2 h
      rw [show x + t • d - x = t • d by module] at this
      exact this
    rcases smul_eq_zero.1 this with h' | h'
    · exact absurd h' htpos.ne'
    · exact hdir.ne_zero h'
  have := (mem_iff_of_goodRadius hS hr hx hgood hFgood hdist).1 (hsub hmem)
  rcases this with h | h
  · exact absurd h hne
  · rwa [show x + t • d - x = t • d by module, dir_smul_of_isDirection hdir htpos] at h

/-- **A local radius exists.** Lemma "Local structure of a polygonal skeleton", for a set
presented as finitely many points together with finitely many segments. -/
theorem exists_isLocalRadius (hF : F.Finite) (hS : S = F ∪ cover ps) (hx : x ∈ S) :
    ∃ r, IsLocalRadius S x r := by
  obtain ⟨r, hr, hgood, hFgood⟩ := exists_pos_goodRadius hF ps x
  refine ⟨r, hr, fun z hz => ?_⟩
  rw [mem_iff_of_goodRadius hS hr hx hgood hFgood hz]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (pieceDirs_subset_localDirs hS hr hgood h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (localDirs_subset_pieceDirs hS hr hgood hFgood h)

/-! ### What a local radius gives -/

end Schoenflies

/-! ### Finite polygonal plane graphs -/

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {x : Plane}

/-- **The point set of a finite plane graph with polygonal edges is its vertex set together
with finitely many straight segments.** The blueprint's "write every edge as a finite union of
straight segments". -/
theorem IsDrawing.exists_cover [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) :
    ∃ ps : List Piece, pointSet G drawing = V(G) ∪ cover ps := by
  classical
  -- One vertex list per edge, then all their segments concatenated.
  choose! vs hvs using hpoly
  refine ⟨(Graph.edgeFinset G).toList.flatMap fun e => segsOf (vs e), ?_⟩
  rw [pointSet]
  congr 1
  rw [cover_flatMap_list]
  ext z
  simp only [mem_iUnion, exists_prop, Finset.mem_toList, mem_edgeFinset]
  refine exists_congr fun e => and_congr_right fun he => ?_
  -- An edge arc carries two distinct points, so its chain has not collapsed.
  have h01 : drawing e 0 ≠ drawing e 1 := by
    intro hcontra
    have := (h.edge_param he).2.1 zero_mem_I one_mem_I hcontra
    norm_num at this
  have hm0 : drawing e 0 ∈ edgeArc drawing e := ⟨0, zero_mem_I, rfl⟩
  have hm1 : drawing e 1 ∈ edgeArc drawing e := ⟨1, one_mem_I, rfl⟩
  rw [hvs e he] at hm0 hm1
  rw [cover_segsOf_eq hm0 hm1 h01, ← hvs e he]

/-- A finite polygonal plane graph without isolated vertices is carried exactly by finitely
many nondegenerate straight segments.  The incidence hypothesis removes the isolated-vertex
term from `IsDrawing.exists_cover`: every vertex already belongs to the segment cover. -/
theorem IsDrawing.exists_segmentCover [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hincident : ∀ z ∈ V(G), ∃ e, G.Inc e z) :
    ∃ ps : List Piece, (∀ P ∈ ps, P.Nondeg) ∧ cover ps = pointSet G drawing ∧
      ∀ P ∈ ps, ∃ e ∈ E(G), P.seg ⊆ edgeArc drawing e := by
  classical
  choose! vs hvs using hpoly
  let ps := (Graph.edgeFinset G).toList.flatMap fun e => segsOf (vs e)
  have hnd : ∀ P ∈ ps, P.Nondeg := by
    intro P hP
    obtain ⟨e, -, hPe⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg _ P hPe
  have hcover : cover ps = ⋃ e ∈ E(G), edgeArc drawing e := by
    dsimp only [ps]
    rw [cover_flatMap_list]
    ext z
    simp only [mem_iUnion, exists_prop, Finset.mem_toList, mem_edgeFinset]
    refine exists_congr fun e => and_congr_right fun he => ?_
    have h01 : drawing e 0 ≠ drawing e 1 := by
      intro hcontra
      have := (h.edge_param he).2.1 zero_mem_I one_mem_I hcontra
      norm_num at this
    have hm0 : drawing e 0 ∈ edgeArc drawing e := ⟨0, zero_mem_I, rfl⟩
    have hm1 : drawing e 1 ∈ edgeArc drawing e := ⟨1, one_mem_I, rfl⟩
    rw [hvs e he] at hm0 hm1
    rw [cover_segsOf_eq hm0 hm1 h01, ← hvs e he]
  have hvertices : V(G) ⊆ ⋃ e ∈ E(G), edgeArc drawing e := by
    intro z hz
    obtain ⟨e, hinc⟩ := hincident z hz
    obtain ⟨w, hlink⟩ := hinc
    exact Set.mem_iUnion₂_of_mem hlink.edge_mem
      (h.edge_isArcBetween hlink).left_mem
  refine ⟨ps, hnd, ?_, ?_⟩
  · rw [hcover, pointSet]
    exact (Set.union_eq_right.mpr hvertices).symm
  · intro P hP
    obtain ⟨e, heList, hPe⟩ := List.mem_flatMap.1 hP
    have he : e ∈ E(G) := by
      rwa [Finset.mem_toList, mem_edgeFinset] at heList
    have h01 : drawing e 0 ≠ drawing e 1 := by
      intro hcontra
      have := (h.edge_param he).2.1 zero_mem_I one_mem_I hcontra
      norm_num at this
    have hm0 : drawing e 0 ∈ edgeArc drawing e := ⟨0, zero_mem_I, rfl⟩
    have hm1 : drawing e 1 ∈ edgeArc drawing e := ⟨1, one_mem_I, rfl⟩
    rw [hvs e he] at hm0 hm1
    refine ⟨e, he, fun z hz => ?_⟩
    rw [hvs e he, ← cover_segsOf_eq hm0 hm1 h01]
    exact Set.mem_iUnion₂_of_mem hPe hz

/-- **Local structure of a polygonal skeleton** (`lem:local-skeleton-structure`): a point of a
finite polygonal plane graph has a local radius, hence a disk in which the graph is exactly
finitely many radial segments. -/
theorem IsDrawing.exists_isLocalRadius [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (hx : x ∈ pointSet G drawing) :
    ∃ r, IsLocalRadius (pointSet G drawing) x r := by
  obtain ⟨ps, hps⟩ := h.exists_cover hpoly
  exact Schoenflies.exists_isLocalRadius (Graph.finite_vertexSet G) hps hx

end Graph
end

section
-- module Solutions.Q146_CD.FiniteTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite transfer, direction (a): toward the square

`thm:finite-transfer` is the largest single statement of the manuscript. This module states it —
in full, with every hypothesis — for **direction (a)** only, and proves as much of its four-step
proof as is within reach of what is on `main`.

Direction (b) is deliberately absent: its extra accessibility problem at the wild source
boundary needs `lem:tangent-cone`, `lem:compact-separation`(c) and the fresh-point bookkeeping
of the target mesh, none of which enters (a).

## The statement, and how it is read

The blueprint's (a) reads: *let `(Γ, Γ')` be a generated matched cellulation; suppose `H` is a
finite 2-connected plane graph containing a subdivision of `Γ`, with outer cycle `C`, with every
nonboundary edge polygonal, and with `|H| ∖ C` connected; then the common subdivision can be
made on `Γ'`, and `H` can be transferred to an admissible target realization `H'`; the resulting
generated matched cellulation refines the old one by explicit parent maps.*

Four objects carry that sentence.

* `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible` and
  `Schoenflies.CellStructure.Realization.IsAdmissible` — `def:admissible-graph`. The weak form
  is exactly the strong one with connectedness of the open nonboundary part waived, which is
  what `def:generated-structure` requires of an intermediate stage and what
  `rem:intermediate-disconnection` insists on.
* `Schoenflies.GeneratedPair` — a generated matched cell structure *with its geometry*: the
  abstract structure, its two realizations, the skeleton homeomorphism, and the two cell
  decompositions. This is the Lean form of "`(Γ, Γ')` is a generated matched cellulation".
  It is a bundle of **data**, not an existential: every consumer reads `.src`, `.tgt`, `.homeo`
  by name.
* `Schoenflies.IsSourceExtension` — the hypotheses on `H`.
* `Schoenflies.IsTransferOf` — the conclusion, relating the new pair to the old one by an
  explicit parent map.

The one place where the Lean statement is *weaker in form* than the prose, and deliberately so:
"`H` can be transferred" is recorded as `T.src.skeletonSet = pointSet H Hdraw`, an equality of
point sets, rather than as a graph isomorphism onto `H`. The reason is step 1: the common
subdivision inserts a vertex at every intersection of a new edge with an old one, so the source
realization of the transferred structure realizes a *subdivision* of `H`, never `H` itself. What
survives verbatim is what the construction uses downstream — the occupied set, the
2-connectivity (which `lem:combinatorial-invariance` moves to the target) and the refinement.

## What is proved here

* **Step 1, the overlay** — `Schoenflies.exists_overlay_of_biUnion_finite`: the union of
  finitely many nondegenerate polygonal sets is the point set of a finite plane graph drawn by
  straight segments. That is `lem:polygonal-overlay` in the form step 1 needs, bridging
  `Schoenflies.polygonal_overlay`, which is stated for a list of segments, to the finite family
  of polygonal *arcs* a skeleton stage arrives as.
* **Step 4, target side** — `Schoenflies.exists_target_crosscut` and
  `Schoenflies.exists_target_crosscut_split`. In direction (a) the target face `F*` is a
  polygonal Jordan region in the square by `lem:cellulation-invariants`(vii); every point of its
  boundary is polygonally accessible from its interior by `lem:polygonal-side-accessibility`
  (target half); and `lem:accessible-endpoints` gives a polygonal crosscut `P* ⊆ closure F*`
  from `v*` to `w*`, which by `thm:general-crosscut` splits `F*` into exactly the two Jordan
  regions bounded by `P*` and the two boundary paths. These constructions supply the complete
  target-side argument.
* **The second sentence of step 2** — `…IsCellDecomposition.exists_unique_face_subset_cell` and
  `…IsCellDecomposition.exists_face_of_ear`: the interior of an ear lies in one current face,
  because it is connected and disjoint from the current skeleton, and its two endpoints then lie
  on that face's boundary cycle. `IsCellDecomposition.cellsAbsorb` derives the formerly named
  `CellsAbsorb` premise from the maintained cell-decomposition and Jordan-face invariants, so
  this requires no additional interface.
* **One ear insertion, step 3** — `exists_sourceEarStepData`,
  `EarCrosscut.exists_matched_target`, `earStepConstruction`, and `earStep`. The ambient source
  path is given fresh abstract cell names, its face split is realized on both sides, and a
  parameter-matching homeomorphism divides the target polygonal crosscut into exactly the same
  abstract edges. Matching source and target crosscuts then produce the next pair, compose both
  refinement maps, preserve every bundle invariant, and enlarge the occupied source graph by
  exactly the supplied ear, under the necessary `[Infinite γ]` name supply.
* **The last paragraph of the proof** — `Schoenflies.GeneratedPair.src_isAdmissible` and
  `Schoenflies.GeneratedPair.tgt_isAdmissible`. Admissibility of the *final* object is
  recovered from `lem:combinatorial-invariance`: the reproduced realization has the same
  2-connectivity and the same connectedness of the open nonboundary part as the given one.
  This uses only the hypotheses of the finite-transfer statement.
* **The induction scheme, steps 2 and 3** — `Schoenflies.transfer_of_ears`. With `earStep`
  supplying each insertion, `lem:relative-ear` in its iterated form
  (`Graph.IsTwoConnected.ear_decomposition`) transfers the whole extension. This is the backbone
  of the induction, and it honours `rem:intermediate-disconnection`: the invariant carried
  through the induction, `Schoenflies.IsPartialTransferOf`, asks only for *weak* admissibility,
  and connectedness of the open nonboundary part is restored only at the very end.

## Completion of step 1

This module keeps `Schoenflies.CommonSubdivision` as the compositional interface consumed by the
ear induction.  `Schoenflies/CommonSubdivision.lean` constructs it: it traces the part of `H`
supported on the old skeleton, proves that trace 2-connected, and carries all of its finitely many
vertices through matched source/target edge subdivisions.  Consequently direction (a) is exposed
there as `Schoenflies.finite_transfer_toward_square`.

## Blueprint

* `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible`,
  `Schoenflies.CellStructure.Realization.IsAdmissible` — `def:admissible-graph`.
* `Schoenflies.GeneratedPair` — `def:generated-structure` with its two realizations,
  `def:matched-pair` and `def:matched-cellulation` folded in.
* `Schoenflies.IsSourceExtension` — the hypotheses of `thm:finite-transfer`(a) on `H`.
* `Schoenflies.IsPartialTransferOf`, `Schoenflies.IsTransferOf` — the conclusion of
  `thm:finite-transfer`, at an intermediate stage and at the end.
* `Schoenflies.exists_target_crosscut`, `Schoenflies.exists_target_crosscut_split` —
  the fourth paragraph of the proof of `thm:finite-transfer`, direction (a):
  `lem:cellulation-invariants`(vii) + `lem:polygonal-side-accessibility` +
  `lem:accessible-endpoints` + `thm:general-crosscut`.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition.exists_unique_face_subset_cell`,
  `…IsCellDecomposition.exists_face_of_ear`,
  `…IsCellDecomposition.sub_of_pos_mem_closure_cell` — "the interior of each ear lies in one
  current face", with the two supporting facts
  `Schoenflies.CellStructure.Realization.cell_subset_skeletonSet` (hoisted to
  `Schoenflies/CombinatorialInvariance.lean`) and
  `Schoenflies.CellStructure.Realization.mem_faces_of_notMem_skeletonSet`.
* `Schoenflies.CellStructure.Realization.pos_mem_closure_cell_congr`,
  `Schoenflies.exists_target_ear` — "let `F*, v*, w*` be the corresponding face and endpoints in
  the other realization", and the whole fourth paragraph assembled from the source-side data.
* `Schoenflies.GeneratedPair.src_isAdmissible`, `Schoenflies.GeneratedPair.tgt_isAdmissible` —
  the last paragraph of the proof, via `lem:combinatorial-invariance`.
* `Schoenflies.exists_overlay_of_biUnion_finite` — `lem:polygonal-overlay` and
  `rem:polygonal-overlay-convention`, for a finite family of polygonal sets: the first half of
  step 1.
* `Schoenflies.earStep` — step 3; `Schoenflies.CommonSubdivision` — the step-1 interface,
  discharged by `Schoenflies.commonSubdivision` in `CommonSubdivision.lean`.
* `Schoenflies.transfer_of_ears_of_commonSubdivision_of_earStep`,
  `Schoenflies.finite_transfer_toward_square_of_commonSubdivision_of_earStep` — the
  finite-transfer induction parametrized by its two construction interfaces.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*}

/-! ### `def:admissible-graph`

An admissible graph in the closed Jordan domain is a finite 2-connected plane graph whose outer
cycle is `C`, whose edges not contained in `C` are polygonal arcs with interiors in `D`, and
whose open nonboundary part `|Γ| ∖ C` is connected. A *weakly* admissible graph satisfies
everything but the last clause.

`outer` is the realized outer cycle and `dom` the closed domain; the open domain is `dom ∖
outer`. On the source side that reads `C` and `C ∪ D`; on the target side `S` and `Q`. -/

namespace CellStructure

namespace Realization

variable {S : CellStructure γ}

/-- **A weakly admissible realization** — `def:admissible-graph` with connectedness of the open
nonboundary part waived, which is what `def:generated-structure` requires of every intermediate
stage (`rem:intermediate-disconnection`). -/
structure IsWeaklyAdmissible (R : S.Realization) (outer dom : Set Plane) : Prop where
  /-- The drawn skeleton is 2-connected. -/
  isTwoConnected : R.graph.IsTwoConnected
  /-- The realized outer cycle is the prescribed curve. -/
  outerSet_eq : R.outerSet = outer
  /-- Every nonboundary edge is a polygonal arc. -/
  isPolygonal : ∀ ⦃e⦄, e ∈ E(S.skel) → e ∉ E(S.outerGraph) → IsPolygonal (edgeArc R.drawing e)
  /-- Every nonboundary edge has its interior in the open domain. Endpoints may lie on the
  outer cycle, as for a crosscut. -/
  cell_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → e ∉ E(S.outerGraph) → R.cell e ⊆ dom \ outer
  /-- The whole skeleton lies in the closed domain. -/
  skeletonSet_subset : R.skeletonSet ⊆ dom

end Realization

end CellStructure

/-! ### A generated matched cell structure, with its geometry

`def:generated-structure` says what the *abstract* object is; `GeneratedStructure` in
`Schoenflies/GeneratedStructure.lean` is that. What a transfer produces, and what the
finite-transfer theorem consumes, is the abstract object together with its two realizations, the
skeleton homeomorphism between them, and the two cell decompositions of
`lem:cellulation-invariants`(i). That bundle is `GeneratedPair`.

It is data, not a `Prop`: a consumer reads `.src`, `.tgt`, `.homeo`, `.str` by name. -/

/-- **A generated matched cell structure with its two realizations.** The Lean form of
"`(Γ, Γ')` is a generated matched cellulation", except that only *weak* admissibility is a
field — `rem:intermediate-disconnection` — with the connected form carried separately by the
consumers that have it. -/
structure GeneratedPair (S₀ : CellStructure γ) (srcOuter srcDom tgtOuter tgtDom : Set Plane)
    where
  /-- The abstract cell structure. -/
  str : CellStructure γ
  /-- It is generated from the base by a finite sequence of elementary operations. -/
  generated : GeneratedStructure S₀ str
  /-- The maintained combinatorial invariants of the current abstract structure. -/
  str_combInvariants : str.CombInvariants
  /-- Every current face has a simple cyclic abstract boundary. -/
  str_boundaryCycles : str.BoundaryCycles
  /-- The realization in the closed Jordan domain. -/
  src : str.Realization
  /-- The realization in the closed square. -/
  tgt : str.Realization
  /-- The skeleton homeomorphism `g : |Γ| → |Γ'|` of `def:matched-pair`. -/
  homeo : CellStructure.SkeletonHomeo src tgt
  /-- **Assertion (i)** on the source side. -/
  src_isCellDecomposition : src.IsCellDecomposition srcDom
  /-- **Assertion (i)** on the target side. -/
  tgt_isCellDecomposition : tgt.IsCellDecomposition tgtDom
  /-- **Assertion (vii)** on the source side: every face is the inside of its Jordan frontier. -/
  src_isFaceJordan : src.IsFaceJordan
  /-- **Assertion (vii)** on the target side.  A split needs this geometric information in
  addition to the cell-decomposition clauses. -/
  tgt_isFaceJordan : tgt.IsFaceJordan
  /-- The open part of the target domain. -/
  tgtInterior_isOpen : IsOpen (tgtDom \ tgtOuter)
  /-- Its frontier is already part of the target skeleton. -/
  tgtInterior_frontier_subset : frontier (tgtDom \ tgtOuter) ⊆ tgt.skeletonSet
  /-- Every target edge is polygonal, including the distinguished outer edges. -/
  tgt_isPolygonal : ∀ ⦃e⦄, e ∈ E(str.skel) → IsPolygonal (edgeArc tgt.drawing e)
  /-- The source realization is weakly admissible. -/
  src_isWeaklyAdmissible : src.IsWeaklyAdmissible srcOuter srcDom
  /-- The target realization is weakly admissible. -/
  tgt_isWeaklyAdmissible : tgt.IsWeaklyAdmissible tgtOuter tgtDom

/-! ### The hypotheses of direction (a) on the given extension

*`H` is a finite 2-connected plane graph containing a subdivision of `Γ`, with outer cycle `C`,
with every nonboundary edge polygonal, and with `|H| ∖ C` connected.*

"Contains a subdivision of `Γ`" is recorded by three clauses: every old vertex is a vertex of
`H`; the old skeleton is inside `|H|`; and any edge of `H` whose nonvertex part meets an *open*
old edge lies inside that old edge. Together those say that each old edge is cut into a chain of
`H`-edges. A transverse crossing is allowed only at a vertex of `H`, exactly as produced by the
polygonal overlay.

"With outer cycle `C`, with every nonboundary edge polygonal" is `edge_dichotomy`: each edge of
`H` either lies inside the outer curve or is polygonal with its interior in the open domain.
Recording the outer cycle as a *subgraph* would put data inside a `Prop`; this reading is what
every step of the proof actually uses, and `outer ⊆ pointSet H Hdraw` comes for free from
`skeletonSet_subset`. -/

/-! ### The conclusion

`IsPartialTransferOf T P B par` is the invariant the induction of steps 2–3 carries: `T` is a
generated pair refining `P` along `par` whose source realization occupies exactly what the
current subgraph `B` of `H` occupies. It asks for **no** connectedness of the open nonboundary
part — `rem:intermediate-disconnection` — because an ear with both endpoints on the outer cycle
really does disconnect it, and later ears reconnect it.

`IsTransferOf` is the same with admissibility of both final realizations added; that is the
theorem's conclusion, and `GeneratedPair.src_isAdmissible` / `GeneratedPair.tgt_isAdmissible`
are what produce it from the connectedness hypothesis on `H`. -/

/-! #### The output data of one realized ear

The former `EarStep` interface ended directly in an existential `GeneratedPair`.  That hid all
of the actual constructor data and made the last half of the proof impossible to reuse or
inspect.  `EarStepData` exposes the abstract split, its two geometric crosscuts, and the chosen
map between them.  Its `pair` and `isPartialTransferOf_pair` declarations below perform the
assembly. -/

/-! #### Locating the source face of a graph-theoretic ear -/

/-! ### The two assumed steps

Both are strictly weaker than `thm:finite-transfer`(a) itself, and both are statements a later
module can discharge without circularity.

`CommonSubdivision` is **step 1**: after overlaying the proposed polygonal nonboundary edges
with the old polygonal nonboundary skeleton and subdividing at every intersection — and
transferring each new point to the other realization along the chosen edge parametrization —
the old skeleton is literally a subgraph of the new one on both sides. In Lean that is: some
2-connected subgraph `K ≤ H` carries a generated pair refining the given one. It is not the
theorem: it makes only edge subdivisions, inserts no ear, and its conclusion is about a subgraph
of `H`, not about `H`.

`EarStep` is **step 3**: one ear insertion — at most two edge subdivisions followed by one
2-cell split — carries a partial transfer of `B` to a partial transfer of `B` with the ear glued
on. Its geometric core in direction (a) is `Schoenflies.exists_target_crosscut_split` below,
which is proved here; only the abstract-data bookkeeping around it is assumed.

**`EarStep` carries `[Infinite γ]`, and without it the hypothesis is false.** Every cell of
every structure in sight is a *name* drawn from the one type `γ`: `V(skel)`, `E(skel)` and
`faces` are three disjoint subsets of it. An ear insertion consumes fresh names — one per
interior vertex of the ear, one per ear edge, and two for the 2-cells the split creates
(`SplitData.edge_fresh`, `.vertex_fresh`, `.face₁_notMem`, `.face₂_notMem`) — while the
conclusion `IsPartialTransferOf T' P (B ∪ ear) Hdraw par'` forces `T'` to realize a subdivision
of the enlarged graph, so `V(B ∪ ear) ⊆ V(T'.src.graph) = T'.src.pos '' V(T'.str.skel)` and the
new skeleton must occupy strictly more of the plane than the old one. On a finite `γ` those
demands eventually exceed the supply: a structure realizing a subdivision of a 2-connected graph
with `e` edges needs at least `e` edge names, at least as many vertex names, and at least one
face name per complementary region, all pairwise distinct inside `γ`. A `γ` large enough to
carry the transfer of `B` and too small to carry the transfer of `B` with one more ear makes the
hypotheses of `EarStep` satisfiable and its conclusion unsatisfiable.

That argument is prose, not machine-checked: pinning it down needs a `GeneratedPair` over an
exactly-exhausted finite `γ`, which is a page of construction for a defect the type class
removes outright. What *is* machine-checked is that nothing below needs more than `Infinite γ`,
and the consumer instantiates `γ := ℕ`. The rule that found this is the standing one: a
hypothesis must be a statement one believes, and `EarStep` without a supply of fresh names is
not one. -/

/-! ### Steps 2 and 3: the induction through the ear sequence -/

/-! ### `thm:finite-transfer`(a) -/

/-! ### Step 4, direction (a): the target crosscut

*In part (a), `F*` is a polygonal Jordan region in the square, by
`lem:cellulation-invariants`(vii). Every point of its boundary is polygonally accessible from its
interior. `lem:accessible-endpoints` therefore gives a polygonal crosscut `P* ⊆ closure F*` from
`v*` to `w*`.* Then: *`thm:general-crosscut` says that the crosscut splits the face into exactly
the two Jordan regions bounded by the crosscut together with those two paths.*

That whole paragraph is proved below. It is stated for a *target* face — a
member of a family of components of `Q ∖ |G|` for an ambient open region `Q` whose frontier
belongs to the skeleton — because that is the shape
`Graph.polygonal_side_accessibility_target` consumes, and it is the shape a target realization
of a generated structure has: `Q` is the open square, `|G|` the target skeleton, and the family
is the set of realized open 2-cells. -/

/-! ### Completing the ear step -/

/-! ### The ear's endpoints, transferred

*Let `F*, v*, w*` be the corresponding face and endpoints in the other realization.* Under the
representation of `Schoenflies/CombinatorialInvariance.lean` there is nothing to transport: `F`
and the two endpoint 0-cells are cells of the **one** abstract structure both realizations
realize, and assertion (ix) turns "the source endpoint lies on the boundary of the source face"
into the abstract statement `a ≼ F`, which reads back in the target realization. -/

/-! ### Step 1: the overlay

*By `lem:polygonal-overlay`, using the convention of `rem:polygonal-overlay-convention`, first
overlay the proposed polygonal nonboundary edges with the old polygonal nonboundary skeleton and
subdivide at all intersections.*

`Schoenflies.polygonal_overlay` does that for a **list of segments**. What step 1 has instead is
a finite family of polygonal *arcs* — the old nonboundary edges and the proposed new ones — so
the two have to be bridged. `Schoenflies.exists_overlay_of_biUnion_finite` is that bridge, and it
is the half of step 1 that is proved here: the union of finitely many nondegenerate polygonal
sets is the point set of a finite plane graph drawn by straight segments, whose vertices are the
ends of the subdivided pieces and therefore include every intersection point.

The nondegeneracy hypothesis is necessary, not cosmetic: a one-point set is polygonal
(`poly [a] = {a}`) and is not the point set of any overlay graph, whose vertices are the ends of
nondegenerate segments.

The matching-subdivision half of step 1 is completed in `CommonSubdivision.lean`: every source
subdivision point is transported through the chosen edge parametrization to the other
realization. -/

/-! ### The interface, exercised

`thm:finite-transfer` exists to feed the recursion of the quantitative-refinement section, which
consumes a transfer only through `Realization.Refines`. This anonymous example is a
machine-checked statement that the conclusion of `finite_transfer_toward_square` delivers exactly
what that recursion reads: the source carrier refines (`lem:refinement-compatibility`(a)), the
same parent map serves both sides (part (c)), and the closed target star of a fixed source point
shrinks (`T_{n+1}(x) \subseteq T_n(x)`).

Nothing below mentions how the transfer was built. If a later change to `IsTransferOf` stopped
serving that recursion, this would break. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.RealizeSubdiv
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing an edge subdivision

`Schoenflies/GeneratedStructure.lean` performs the *abstract* edge subdivision
(`CellStructure.subdivideEdge`) and states what it means for a realization of the subdivided
structure to refine a realization of the old one (`SubdivData.IsRefinement`);
`Schoenflies/CellulationInvariants.lean` propagates assertions (i), (iv) and (vii) across such a
refinement. Nothing built such a realization. This module does.

The construction is the blueprint's own sentence — "the corresponding point is inserted into the
corresponding edge using the edge parametrization" — made into data: pick a parameter
`t ∈ (0,1)`, put the new 0-cell at `R.drawing d.edge t`, and draw the two new 1-cells with the
two halves of the old parametrization, each rescaled to `[0,1]`.

## The orientation of the drawn edge

`IsDrawing.edge_param` is deliberately orientation-free: it says
`G.IsLink e (drawing e 0) (drawing e 1)`, so `drawing d.edge 0` may be *either* `pos d.left` or
`pos d.right`. But `d.newEdge₁` runs from `d.left` to `d.newVertex` by definition of
`subdivideEdge`, so which half of the parametrization draws it is not fixed in advance.

Assuming `drawing d.edge 0 = pos d.left` would be a false hypothesis for half of all inputs, and
the caller cannot repair it (swapping `d.left` with `d.right` in the `SubdivData` also swaps the
two new edge *names*, producing a different abstract structure). So the orientation is read off
instead: `SubdivData.leftParam` is the endpoint parameter, `0` or `1`, at which the drawn edge
sits at `d.left`. Every statement below is orientation-free; only the two lemmas
`SubdivData.drawing_leftParam` and `SubdivData.drawing_rightParam` look inside.

Because of that, the construction is phrased with `Schoenflies.subarc` — the general affine
reparametrization already on `main` — rather than with `firstHalf` / `secondHalf`, which are the
two halves in the standard orientation and are recorded here as the named special case.

## No side conditions

`SubdivData.realize` takes no geometric hypothesis beyond `t ∈ Ioo 0 1`. Everything else it
needs — that `d.edge` is drawn, injectively and continuously, between the positions of `d.left`
and `d.right`, and that an interior point of a drawn edge is not a vertex — is already carried by
`CellStructure.Realization`, and is extracted here rather than assumed.

## The transported skeleton homeomorphism is not here, but it exists

**Closed, in `Schoenflies/RealizeSubdivHomeo.lean`** (`SubdivData.realizeHomeo`), on top of
`Schoenflies/ArcMonotone.lean`, which supplies the missing fact named at the end of this
section. What follows is the record of why it could not be done here.

`SkeletonHomeo.realize` is absent from *this* module. Six of its eight fields are immediate —
`skeletonSet_realize` below says the realized 1-skeleton is *literally the same set* after a
subdivision, so the map, its inverse, both continuity clauses and both inverse clauses transport
verbatim, and
`pos_apply` at the new 0-cell is the statement `g.toFun (R₁.drawing d.edge t₁) =
R₂.drawing d.edge t₂` that a caller choosing corresponding parameters supplies anyway.

What is missing is `edgeArc_image` at the two new edges: that `g` carries the *half* arc from
`R₁.pos d.left` to the new source point onto the half arc from `R₂.pos d.left` to the new target
point. This is true but is not implied by the `SkeletonHomeo` data pointwise: it needs the fact
that a homeomorphism between two arcs matching their endpoints is monotone, hence carries
initial subarcs to initial subarcs. That fact was not on `main` when this module was written,
and assuming the two clauses would have been assuming the conclusion, so nothing was stated
here. `Schoenflies/ArcMonotone.lean`
now proves it — `ArcMatch`, `transferParam`, `image_image_uIcc` — and
`Schoenflies/RealizeSubdivHomeo.lean` builds the transported homeomorphism from it, orientation
of the two realizations handled rather than assumed.

## Blueprint

* `def:generated-structure`, operation 1 (edge subdivision) — the geometric half of the
  operation, whose abstract half is `CellStructure.subdivideEdge`.
* `lem:cellulation-invariants` (i) and (iv), the paragraph "Suppose first that an open edge `e`
  is subdivided at a new vertex `v`": `SubdivData.isRefinement_realize` produces exactly the
  hypotheses that `SubdivData.IsRefinement.isCellDecomposition_and_isFaceJordan` consumes.

Declarations:

* `Schoenflies.uIcc_union_uIcc`, `Schoenflies.uIcc_inter_uIcc` — a parameter interval cut at an
  interior point.
* `Schoenflies.subarc_image_union`, `Schoenflies.subarc_image_inter` — the two subarcs of a cut
  cover the arc and meet exactly at the cut point.
* `Schoenflies.firstHalf`, `Schoenflies.secondHalf` — the two halves of a drawn edge in the
  standard orientation, with their endpoint values, continuity, injectivity, images, meet and
  union.
* `Schoenflies.CellStructure.SubdivData.leftParam` / `rightParam` — the orientation of the drawn
  edge.
* `Schoenflies.CellStructure.SubdivData.realize` — the realization of the subdivided structure.
* `Schoenflies.CellStructure.SubdivData.isRefinement_realize` — it refines the given one.
* `Schoenflies.CellStructure.SubdivData.realize_isCellDecomposition_and_isFaceJordan` — the
  induction step of `lem:cellulation-invariants` over the first constructor, now constructed
  with all necessary data constructed here.
* `Schoenflies.CellStructure.SubdivData.skeletonSet_realize` — a subdivision does not move the
  realized 1-skeleton.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open _root_.Graph

/-! ### Cutting a parameter interval at an interior point -/

variable {a b t : ℝ}

/-! ### The two subarcs of a cut -/

variable {f : ℝ → Plane}

/-! ### The two halves of a drawn edge

The special case `a = 0`, `b = 1` of the previous section, in the notation a consumer holding a
`Graph.IsDrawing` writes. -/

variable {β : Type*} {drawing : β → ℝ → Plane} {e : β}

/-! ### The orientation of the drawn subdivided edge -/

namespace CellStructure

namespace SubdivData

variable {γ : Type*} {S : CellStructure γ} (d : S.SubdivData) (R : S.Realization)

/-- What the realization already knows about the subdivided edge: it is an edge of the drawn
skeleton. -/
theorem edge_mem_edgeSet_graph : d.edge ∈ E(R.graph) := by
  rw [Realization.edgeSet_graph]; exact d.edge_mem_edgeSet

theorem continuousOn_drawing_edge : ContinuousOn (R.drawing d.edge) I :=
  (R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)).1

theorem injOn_drawing_edge : InjOn (R.drawing d.edge) I :=
  (R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)).2.1

theorem isLink_drawn_edge : R.graph.IsLink d.edge (R.pos d.left) (R.pos d.right) :=
  d.isLink.map R.pos

open scoped Classical in
/-- **The orientation of the drawn subdivided edge**: the endpoint parameter, `0` or `1`, at
which `R.drawing d.edge` sits at `R.pos d.left`.

`IsDrawing.edge_param` fixes only the unordered pair of endpoint values, so this cannot be read
off the structure; it is decided by a case distinction, once, here. -/
noncomputable def leftParam : ℝ := if R.drawing d.edge 0 = R.pos d.left then 0 else 1

/-- The endpoint parameter at which the drawn subdivided edge sits at `R.pos d.right`. -/
noncomputable def rightParam : ℝ := 1 - d.leftParam R

theorem leftParam_eq_zero_or_one : d.leftParam R = 0 ∨ d.leftParam R = 1 := by
  unfold leftParam
  split_ifs
  exacts [Or.inl rfl, Or.inr rfl]

/-- **The two endpoint parameters land on the two endpoints.** The only lemma that looks inside
`leftParam`; everything downstream is orientation-free. -/
theorem drawing_params :
    R.drawing d.edge (d.leftParam R) = R.pos d.left ∧
      R.drawing d.edge (d.rightParam R) = R.pos d.right := by
  have hd := R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)
  rcases (d.isLink_drawn_edge R).eq_and_eq_or_eq_and_eq hd.2.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hL : d.leftParam R = 0 := if_pos h0.symm
    refine ⟨by rw [hL]; exact h0.symm, ?_⟩
    have hR : d.rightParam R = 1 := by rw [rightParam, hL]; ring
    rw [hR]; exact h1.symm
  · -- Here `R.pos d.left = R.drawing d.edge 1`; the other reading would collapse the two
    -- endpoint values, which injectivity forbids.
    have hne : ¬ (R.drawing d.edge 0 = R.pos d.left) := fun hcon =>
      zero_ne_one (hd.2.1 zero_mem_I one_mem_I (by rw [hcon, h0]))
    have hL : d.leftParam R = 1 := if_neg hne
    refine ⟨by rw [hL]; exact h0.symm, ?_⟩
    have hR : d.rightParam R = 0 := by rw [rightParam, hL]; ring
    rw [hR]; exact h1.symm

theorem drawing_leftParam : R.drawing d.edge (d.leftParam R) = R.pos d.left :=
  (d.drawing_params R).1

theorem drawing_rightParam : R.drawing d.edge (d.rightParam R) = R.pos d.right :=
  (d.drawing_params R).2

theorem leftParam_mem_I : d.leftParam R ∈ I := by
  rcases d.leftParam_eq_zero_or_one R with h | h <;> rw [h]
  exacts [zero_mem_I, one_mem_I]

theorem rightParam_mem_I : d.rightParam R ∈ I := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact one_mem_I
  · rw [rightParam, h, sub_self]; exact zero_mem_I

/-- The two endpoint parameters span the whole parameter interval, in whichever order. -/
theorem uIcc_params : uIcc (d.leftParam R) (d.rightParam R) = I := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact uIcc_zero_one
  · rw [rightParam, h, sub_self, uIcc_comm]; exact uIcc_zero_one

theorem leftParam_ne (ht : t ∈ Ioo (0 : ℝ) 1) : d.leftParam R ≠ t := by
  rcases d.leftParam_eq_zero_or_one R with h | h <;> rw [h]
  exacts [ht.1.ne, ht.2.ne']

theorem rightParam_ne (ht : t ∈ Ioo (0 : ℝ) 1) : d.rightParam R ≠ t := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact ht.2.ne'
  · rw [rightParam, h, sub_self]; exact ht.1.ne

theorem mem_uIcc_params (ht : t ∈ Ioo (0 : ℝ) 1) : t ∈ uIcc (d.leftParam R) (d.rightParam R) := by
  rw [d.uIcc_params R]; exact Ioo_subset_Icc_self ht

/-- **An interior point of a drawn edge is not a vertex.** The one geometric fact the
construction needs that is not simply read off a field, and the reason `SubdivData.realize`
needs no side condition. -/
theorem newPos_notMem_vertexSet (ht : t ∈ Ioo (0 : ℝ) 1) :
    R.drawing d.edge t ∉ V(R.graph) := by
  intro hmem
  have harc : R.drawing d.edge t ∈ edgeArc R.drawing d.edge :=
    ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  have hinj := d.injOn_drawing_edge R
  rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hmem harc with h | h
  · exact d.leftParam_ne R ht
      (hinj (d.leftParam_mem_I R) (Ioo_subset_Icc_self ht) ((d.drawing_leftParam R).trans h.symm))
  · exact d.rightParam_ne R ht
      (hinj (d.rightParam_mem_I R) (Ioo_subset_Icc_self ht)
        ((d.drawing_rightParam R).trans h.symm))

theorem newPos_ne_pos (ht : t ∈ Ioo (0 : ℝ) 1) {v : γ} (hv : v ∈ V(S.skel)) :
    R.drawing d.edge t ≠ R.pos v := fun h =>
  d.newPos_notMem_vertexSet R ht (by rw [h, Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)

/-! ### Freshness of the three new names, in the forms used below -/

theorem ne_newVertex_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newVertex := fun h =>
  d.newVertex_notMem (h ▸ hz)

theorem ne_newEdge₁_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newEdge₁ := fun h =>
  d.newEdge₁_notMem (h ▸ hz)

theorem ne_newEdge₂_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newEdge₂ := fun h =>
  d.newEdge₂_notMem (h ▸ hz)

/-! ### The links of the subdivided skeleton -/

theorem isLink_newEdge₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
  d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem isLink_newEdge₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
  d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- An old edge other than the subdivided one keeps its ends. -/
theorem skeleton_isLink_of_old {f x y : γ} (hfe : f ≠ d.edge) (h : S.skel.IsLink f x y) :
    d.skeleton.IsLink f x y :=
  d.skeleton_isLink.2 (Or.inl ⟨h, hfe,
    fun hc => d.newEdge₁_notMem_edgeSet (hc ▸ h.edge_mem),
    fun hc => d.newEdge₂_notMem_edgeSet (hc ▸ h.edge_mem)⟩)

/-- …and gains none: for an old edge the two skeleta have the same links. -/
theorem skeleton_isLink_old_iff {f x y : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    d.skeleton.IsLink f x y ↔ S.skel.IsLink f x y := by
  refine ⟨fun h => ?_, d.skeleton_isLink_of_old hfe⟩
  rcases d.skeleton_isLink.1 h with ⟨h, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact h
  · exact absurd hf d.newEdge₁_notMem_edgeSet
  · exact absurd hf d.newEdge₂_notMem_edgeSet

/-! ### The realization of the subdivided structure -/

open scoped Classical in
/-- The positions after the subdivision: the new 0-cell goes to the point of the drawn edge at
parameter `t`, and every old 0-cell stays where it was. -/
noncomputable def realizePos (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → Plane :=
  fun z => if z = d.newVertex then R.drawing d.edge t else R.pos z

open scoped Classical in
/-- The parametrizations after the subdivision: the two new 1-cells are drawn by the two halves
of the old parametrization, cut at `t` and rescaled to `[0, 1]`; every old 1-cell keeps its own.

`d.newEdge₁` runs from `d.left`, so the half that draws it starts at `d.leftParam R`, which is
`0` or `1` according to the orientation of the old parametrization. -/
noncomputable def realizeDrawing (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → ℝ → Plane :=
  fun f =>
    if f = d.newEdge₁ then subarc (R.drawing d.edge) (d.leftParam R) t
    else if f = d.newEdge₂ then subarc (R.drawing d.edge) t (d.rightParam R)
    else R.drawing f

open scoped Classical in
/-- The open cells after the subdivision: the new 0-cell is the new point, each new open 1-cell
is its half arc without its two endpoints, and every surviving cell is unchanged. -/
noncomputable def realizeCell (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → Set Plane :=
  fun c =>
    if c = d.newVertex then {R.drawing d.edge t}
    else if c = d.newEdge₁ then
      R.drawing d.edge '' uIcc (d.leftParam R) t \ {R.pos d.left, R.drawing d.edge t}
    else if c = d.newEdge₂ then
      R.drawing d.edge '' uIcc t (d.rightParam R) \ {R.drawing d.edge t, R.pos d.right}
    else R.cell c

/-- The drawn skeleton after the subdivision. -/
noncomputable def realizeGraph (d : S.SubdivData) (R : S.Realization) (t : ℝ) : Graph Plane γ :=
  d.skeleton.map (d.realizePos R t)

variable {d R}

@[simp] theorem realizePos_newVertex : d.realizePos R t d.newVertex = R.drawing d.edge t :=
  if_pos rfl

theorem realizePos_of_ne {z : γ} (h : z ≠ d.newVertex) : d.realizePos R t z = R.pos z := if_neg h

theorem realizePos_of_mem_cells {z : γ} (h : z ∈ S.cells) : d.realizePos R t z = R.pos z :=
  realizePos_of_ne (d.ne_newVertex_of_mem_cells h)

theorem realizePos_of_mem_vertexSet {z : γ} (h : z ∈ V(S.skel)) : d.realizePos R t z = R.pos z :=
  realizePos_of_mem_cells (S.mem_cells_of_mem_vertexSet h)

@[simp] theorem realizeDrawing_newEdge₁ :
    d.realizeDrawing R t d.newEdge₁ = subarc (R.drawing d.edge) (d.leftParam R) t := if_pos rfl

@[simp] theorem realizeDrawing_newEdge₂ :
    d.realizeDrawing R t d.newEdge₂ = subarc (R.drawing d.edge) t (d.rightParam R) := by
  rw [realizeDrawing, if_neg d.newEdge_ne.symm, if_pos rfl]

theorem realizeDrawing_of_ne {f : γ} (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) :
    d.realizeDrawing R t f = R.drawing f := by rw [realizeDrawing, if_neg h₁, if_neg h₂]

theorem realizeDrawing_of_mem_cells {f : γ} (h : f ∈ S.cells) :
    d.realizeDrawing R t f = R.drawing f :=
  realizeDrawing_of_ne (d.ne_newEdge₁_of_mem_cells h) (d.ne_newEdge₂_of_mem_cells h)

@[simp] theorem realizeCell_newVertex : d.realizeCell R t d.newVertex = {R.drawing d.edge t} :=
  if_pos rfl

@[simp] theorem realizeCell_newEdge₁ : d.realizeCell R t d.newEdge₁ =
    R.drawing d.edge '' uIcc (d.leftParam R) t \ {R.pos d.left, R.drawing d.edge t} := by
  rw [realizeCell, if_neg d.newVertex_ne₁.symm, if_pos rfl]

@[simp] theorem realizeCell_newEdge₂ : d.realizeCell R t d.newEdge₂ =
    R.drawing d.edge '' uIcc t (d.rightParam R) \ {R.drawing d.edge t, R.pos d.right} := by
  rw [realizeCell, if_neg d.newVertex_ne₂.symm, if_neg d.newEdge_ne.symm, if_pos rfl]

theorem realizeCell_of_mem_cells {c : γ} (h : c ∈ S.cells) : d.realizeCell R t c = R.cell c := by
  rw [realizeCell, if_neg (d.ne_newVertex_of_mem_cells h), if_neg (d.ne_newEdge₁_of_mem_cells h),
    if_neg (d.ne_newEdge₂_of_mem_cells h)]

/-! ### The two half arcs -/

theorem edgeArc_newEdge₁ : edgeArc (d.realizeDrawing R t) d.newEdge₁ =
    R.drawing d.edge '' uIcc (d.leftParam R) t := by
  rw [edgeArc, realizeDrawing_newEdge₁, subarc_image]

theorem edgeArc_newEdge₂ : edgeArc (d.realizeDrawing R t) d.newEdge₂ =
    R.drawing d.edge '' uIcc t (d.rightParam R) := by
  rw [edgeArc, realizeDrawing_newEdge₂, subarc_image]

theorem edgeArc_of_ne {f : γ} (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) :
    edgeArc (d.realizeDrawing R t) f = edgeArc R.drawing f := by
  rw [edgeArc, edgeArc, realizeDrawing_of_ne h₁ h₂]

/-! ### The two cell-shape fields of a realization -/

/-- Every 0-cell of the subdivided structure is realized by its point. -/
theorem cell_vertex_realize ⦃v : γ⦄ (hv : v ∈ V(d.skeleton)) :
    d.realizeCell R t v = {d.realizePos R t v} := by
  rw [d.skeleton_vertexSet, mem_insert_iff] at hv
  rcases hv with rfl | hv
  · rw [realizeCell_newVertex, realizePos_newVertex]
  · rw [realizeCell_of_mem_cells (S.mem_cells_of_mem_vertexSet hv),
      realizePos_of_mem_vertexSet hv, R.cell_vertex hv]

/-- Every 1-cell of the subdivided structure is realized by its open arc. -/
theorem cell_edge_realize ⦃g x y : γ⦄ (hl : d.skeleton.IsLink g x y) :
    d.realizeCell R t g =
      edgeArc (d.realizeDrawing R t) g \ {d.realizePos R t x, d.realizePos R t y} := by
  rcases d.skeleton_isLink.1 hl with ⟨hlS, -, hg₁, hg₂⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩
  · rw [realizeCell_of_mem_cells (S.mem_cells_of_mem_edgeSet hlS.edge_mem),
      edgeArc_of_ne hg₁ hg₂, realizePos_of_mem_vertexSet hlS.left_mem,
      realizePos_of_mem_vertexSet hlS.right_mem, R.cell_edge hlS]
  · rw [realizeCell_newEdge₁, edgeArc_newEdge₁]
    rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex]
    · rw [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex, pair_comm]
  · rw [realizeCell_newEdge₂, edgeArc_newEdge₂]
    rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex]
    · rw [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex, pair_comm]

section

variable (ht : t ∈ Ioo (0 : ℝ) 1)
include ht

/-- Distinct 0-cells of the subdivided structure sit at distinct points: the new one is an
interior point of a drawn edge, so it is none of the old ones. -/
theorem injOn_realizePos : InjOn (d.realizePos R t) V(d.skeleton) := by
  intro p hp q hq hpq
  rw [d.skeleton_vertexSet, mem_insert_iff] at hp hq
  rcases hp with rfl | hp
  · rcases hq with rfl | hq
    · rfl
    · rw [realizePos_newVertex, realizePos_of_mem_vertexSet hq] at hpq
      exact absurd hpq (d.newPos_ne_pos R ht hq)
  · rcases hq with rfl | hq
    · rw [realizePos_of_mem_vertexSet hp, realizePos_newVertex] at hpq
      exact absurd hpq.symm (d.newPos_ne_pos R ht hp)
    · rw [realizePos_of_mem_vertexSet hp, realizePos_of_mem_vertexSet hq] at hpq
      exact R.injOn_pos hp hq hpq

theorem edgeArc_newEdge₁_subset :
    edgeArc (d.realizeDrawing R t) d.newEdge₁ ⊆ edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₁, edgeArc]
  exact image_mono ((uIcc_left_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset)

theorem edgeArc_newEdge₂_subset :
    edgeArc (d.realizeDrawing R t) d.newEdge₂ ⊆ edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₂, edgeArc]
  exact image_mono ((uIcc_right_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset)

/-- **The two new arcs cover the old one.** -/
theorem edgeArc_new_union : edgeArc (d.realizeDrawing R t) d.newEdge₁ ∪
    edgeArc (d.realizeDrawing R t) d.newEdge₂ = edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₁, edgeArc_newEdge₂, ← image_union,
    uIcc_union_uIcc (d.mem_uIcc_params R ht), d.uIcc_params R, edgeArc]

/-- **The two new arcs meet exactly at the new point.** -/
theorem edgeArc_new_inter : edgeArc (d.realizeDrawing R t) d.newEdge₁ ∩
    edgeArc (d.realizeDrawing R t) d.newEdge₂ = {R.drawing d.edge t} := by
  rw [edgeArc_newEdge₁, edgeArc_newEdge₂,
    ← (d.injOn_drawing_edge R).mono (d.uIcc_params R).subset |>.image_inter
      (uIcc_left_subset (d.mem_uIcc_params R ht)) (uIcc_right_subset (d.mem_uIcc_params R ht)),
    uIcc_inter_uIcc (d.mem_uIcc_params R ht), image_singleton]

/-- The far endpoint of the old edge misses the near half. -/
theorem posRight_notMem_edgeArc_newEdge₁ :
    R.pos d.right ∉ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁, ← d.drawing_rightParam R]
  rintro ⟨s, hs, hseq⟩
  have hsI : s ∈ I :=
    ((uIcc_left_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset) hs
  have : s = d.rightParam R := d.injOn_drawing_edge R hsI (d.rightParam_mem_I R) hseq
  exact right_notMem_uIcc_left (d.mem_uIcc_params R ht) (d.rightParam_ne R ht) (this ▸ hs)

theorem posLeft_notMem_edgeArc_newEdge₂ :
    R.pos d.left ∉ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂, ← d.drawing_leftParam R]
  rintro ⟨s, hs, hseq⟩
  have hsI : s ∈ I :=
    ((uIcc_right_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset) hs
  have : s = d.leftParam R := d.injOn_drawing_edge R hsI (d.leftParam_mem_I R) hseq
  exact left_notMem_uIcc_right (d.mem_uIcc_params R ht) (d.leftParam_ne R ht) (this ▸ hs)

/-- The new point lies on no old edge but the subdivided one. -/
theorem newPos_notMem_edgeArc_of_ne {f : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    R.drawing d.edge t ∉ edgeArc R.drawing f := fun hva =>
  d.newPos_notMem_vertexSet R ht
    (R.isDrawing.arcs_meet_at_vertex (d.edge_mem_edgeSet_graph R)
      (by rw [edgeSet_map]; exact hf) (Ne.symm hfe)
      ⟨t, Ioo_subset_Icc_self ht, rfl⟩ hva)

/-! ### The subdivided drawn skeleton -/

omit ht in
theorem realizeGraph_edgeSet : E(d.realizeGraph R t) = E(d.skeleton) := edgeSet_map _ _

omit ht in
theorem realizePos_image_vertexSet : d.realizePos R t '' V(S.skel) = R.pos '' V(S.skel) :=
  image_congr fun _ hv => realizePos_of_mem_vertexSet hv

omit ht in
theorem realizeGraph_vertexSet :
    V(d.realizeGraph R t) = insert (R.drawing d.edge t) V(R.graph) := by
  rw [realizeGraph, vertexSet_map, d.skeleton_vertexSet, image_insert_eq, realizePos_newVertex,
    realizePos_image_vertexSet, Realization.vertexSet_graph]

omit ht in
theorem mem_realizeGraph_vertexSet_of_mem {p : Plane} (hp : p ∈ V(R.graph)) :
    p ∈ V(d.realizeGraph R t) := by
  rw [realizeGraph_vertexSet]; exact mem_insert_of_mem _ hp

omit ht in
/-- An edge of the subdivided drawn skeleton that is neither new is an old edge, and not the
subdivided one. -/
theorem mem_edgeSet_skel_of_ne {f : γ} (hf : f ∈ E(d.realizeGraph R t))
    (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) : f ∈ E(S.skel) ∧ f ≠ d.edge := by
  rw [realizeGraph_edgeSet, d.skeleton_edgeSet] at hf
  simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff] at hf
  rcases hf with rfl | rfl | h
  exacts [absurd rfl h₁, absurd rfl h₂, h]

omit ht in
/-- For an old edge the two drawn skeleta have the same links. -/
theorem realizeGraph_isLink_old {f : γ} {x y : Plane} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    (d.realizeGraph R t).IsLink f x y ↔ R.graph.IsLink f x y := by
  constructor
  · rintro ⟨p, q, hpq, rfl, rfl⟩
    rw [d.skeleton_isLink_old_iff hf hfe] at hpq
    rw [realizePos_of_mem_vertexSet hpq.left_mem, realizePos_of_mem_vertexSet hpq.right_mem]
    exact hpq.map R.pos
  · rintro ⟨p, q, hpq, rfl, rfl⟩
    exact ⟨p, q, d.skeleton_isLink_of_old hfe hpq,
      realizePos_of_mem_vertexSet hpq.left_mem, realizePos_of_mem_vertexSet hpq.right_mem⟩

omit ht in
theorem realizeGraph_inc_old {f : γ} {p : Plane} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    (d.realizeGraph R t).Inc f p ↔ R.graph.Inc f p :=
  exists_congr fun _ => realizeGraph_isLink_old hf hfe

omit ht in
theorem realizeGraph_isLink_newEdge₁ :
    (d.realizeGraph R t).IsLink d.newEdge₁ (R.pos d.left) (R.drawing d.edge t) := by
  have h := d.isLink_newEdge₁.map (d.realizePos R t)
  rwa [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex] at h

omit ht in
theorem realizeGraph_isLink_newEdge₂ :
    (d.realizeGraph R t).IsLink d.newEdge₂ (R.drawing d.edge t) (R.pos d.right) := by
  have h := d.isLink_newEdge₂.map (d.realizePos R t)
  rwa [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex] at h

/-- A vertex on the first new arc is one of its two ends. -/
theorem mem_edgeArc_newEdge₁_vertex {p : Plane} (hp : p ∈ V(d.realizeGraph R t))
    (hpa : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁) :
    p = R.pos d.left ∨ p = R.drawing d.edge t := by
  rw [realizeGraph_vertexSet, mem_insert_iff] at hp
  rcases hp with rfl | hp
  · exact Or.inr rfl
  · rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hp
      (edgeArc_newEdge₁_subset ht hpa) with h | h
    · exact Or.inl h
    · exact absurd (h ▸ hpa) (posRight_notMem_edgeArc_newEdge₁ ht)

/-- A vertex on the second new arc is one of its two ends. -/
theorem mem_edgeArc_newEdge₂_vertex {p : Plane} (hp : p ∈ V(d.realizeGraph R t))
    (hpa : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂) :
    p = R.drawing d.edge t ∨ p = R.pos d.right := by
  rw [realizeGraph_vertexSet, mem_insert_iff] at hp
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hp
      (edgeArc_newEdge₂_subset ht hpa) with h | h
    · exact absurd (h ▸ hpa) (posLeft_notMem_edgeArc_newEdge₂ ht)
    · exact Or.inr h

/-! ### Where two edges of the subdivided drawing meet -/

/-- The two new edges meet exactly at the new vertex. -/
theorem edge_inter_new_new {p : Plane}
    (hp₁ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (hp₂ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₁ p ∧
      (d.realizeGraph R t).Inc d.newEdge₂ p := by
  have hmem : p ∈ ({R.drawing d.edge t} : Set Plane) := by
    rw [← edgeArc_new_inter ht]; exact ⟨hp₁, hp₂⟩
  rw [mem_singleton_iff] at hmem
  subst hmem
  exact ⟨by rw [realizeGraph_vertexSet]; exact mem_insert _ _,
    (realizeGraph_isLink_newEdge₁).inc_right, (realizeGraph_isLink_newEdge₂).inc_left⟩

/-- The first new edge meets an old edge only at the position of `d.left`. -/
theorem edge_inter_newEdge₁_old {g : γ} (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) {p : Plane}
    (hp₁ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₁ p ∧
      (d.realizeGraph R t).Inc g p := by
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, -, hpgInc⟩ := R.isDrawing.edge_inter (d.edge_mem_edgeSet_graph R)
    (by rw [edgeSet_map]; exact hg) (Ne.symm hge)
    (edgeArc_newEdge₁_subset ht hp₁) hpg
  rcases mem_edgeArc_newEdge₁_vertex ht (mem_realizeGraph_vertexSet_of_mem hpV) hp₁ with
    h | h
  · subst h
    exact ⟨mem_realizeGraph_vertexSet_of_mem hpV, (realizeGraph_isLink_newEdge₁).inc_left,
      (realizeGraph_inc_old hg hge).2 hpgInc⟩
  · exact absurd (h ▸ hpV) (d.newPos_notMem_vertexSet R ht)

/-- The second new edge meets an old edge only at the position of `d.right`. -/
theorem edge_inter_newEdge₂_old {g : γ} (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) {p : Plane}
    (hp₂ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂)
    (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₂ p ∧
      (d.realizeGraph R t).Inc g p := by
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, -, hpgInc⟩ := R.isDrawing.edge_inter (d.edge_mem_edgeSet_graph R)
    (by rw [edgeSet_map]; exact hg) (Ne.symm hge)
    (edgeArc_newEdge₂_subset ht hp₂) hpg
  rcases mem_edgeArc_newEdge₂_vertex ht (mem_realizeGraph_vertexSet_of_mem hpV) hp₂ with
    h | h
  · exact absurd (h ▸ hpV) (d.newPos_notMem_vertexSet R ht)
  · subst h
    exact ⟨mem_realizeGraph_vertexSet_of_mem hpV,
      (realizeGraph_isLink_newEdge₂).inc_right, (realizeGraph_inc_old hg hge).2 hpgInc⟩

omit ht in
/-- Two old edges meet where they met before. -/
theorem edge_inter_old_old {f g : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge)
    (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) (hfg : f ≠ g) {p : Plane}
    (hpf : p ∈ edgeArc (d.realizeDrawing R t) f) (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc f p ∧ (d.realizeGraph R t).Inc g p := by
  have hfc := S.mem_cells_of_mem_edgeSet hf
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc) (d.ne_newEdge₂_of_mem_cells hfc)] at hpf
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, h₁, h₂⟩ := R.isDrawing.edge_inter (by rw [edgeSet_map]; exact hf)
    (by rw [edgeSet_map]; exact hg) hfg hpf hpg
  exact ⟨mem_realizeGraph_vertexSet_of_mem hpV, (realizeGraph_inc_old hf hfe).2 h₁,
    (realizeGraph_inc_old hg hge).2 h₂⟩

/-! ### The subdivided drawing -/

/-- **The subdivided data really is a drawing.** -/
theorem isDrawing_realize : IsDrawing (d.realizeGraph R t) (d.realizeDrawing R t) where
  edge_param := by
    intro f hf
    rw [realizeGraph_edgeSet, d.skeleton_edgeSet] at hf
    simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | ⟨hfS, hfe⟩
    · rw [realizeDrawing_newEdge₁]
      refine ⟨continuousOn_subarc (d.continuousOn_drawing_edge R) (d.leftParam_mem_I R)
          (Ioo_subset_Icc_self ht),
        injOn_subarc ((d.injOn_drawing_edge R).mono
          (uIcc_subset_I (d.leftParam_mem_I R) (Ioo_subset_Icc_self ht))) (d.leftParam_ne R ht),
        ?_⟩
      rw [subarc_zero, subarc_one, d.drawing_leftParam R]
      exact realizeGraph_isLink_newEdge₁
    · rw [realizeDrawing_newEdge₂]
      refine ⟨continuousOn_subarc (d.continuousOn_drawing_edge R) (Ioo_subset_Icc_self ht)
          (d.rightParam_mem_I R),
        injOn_subarc ((d.injOn_drawing_edge R).mono
          (uIcc_subset_I (Ioo_subset_Icc_self ht) (d.rightParam_mem_I R)))
          (Ne.symm (d.rightParam_ne R ht)), ?_⟩
      rw [subarc_zero, subarc_one, d.drawing_rightParam R]
      exact realizeGraph_isLink_newEdge₂
    · have hfc := S.mem_cells_of_mem_edgeSet hfS
      rw [realizeDrawing_of_mem_cells hfc]
      have hd := R.isDrawing.edge_param
        (show f ∈ E(R.graph) by rw [Realization.edgeSet_graph]; exact hfS)
      exact ⟨hd.1, hd.2.1, (realizeGraph_isLink_old hfS hfe).2 hd.2.2⟩
  vertex_mem_edgeArc := by
    intro f x y v hl hv hva
    by_cases hf₁ : f = d.newEdge₁
    · subst hf₁
      rcases hl.eq_and_eq_or_eq_and_eq (realizeGraph_isLink_newEdge₁) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact mem_edgeArc_newEdge₁_vertex ht hv hva
      · exact (mem_edgeArc_newEdge₁_vertex ht hv hva).symm
    · by_cases hf₂ : f = d.newEdge₂
      · subst hf₂
        rcases hl.eq_and_eq_or_eq_and_eq (realizeGraph_isLink_newEdge₂) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact mem_edgeArc_newEdge₂_vertex ht hv hva
        · exact (mem_edgeArc_newEdge₂_vertex ht hv hva).symm
      · obtain ⟨hfS, hfe⟩ := mem_edgeSet_skel_of_ne hl.edge_mem hf₁ hf₂
        rw [edgeArc_of_ne hf₁ hf₂] at hva
        rw [realizeGraph_isLink_old hfS hfe] at hl
        rw [realizeGraph_vertexSet, mem_insert_iff] at hv
        rcases hv with rfl | hv
        · exact absurd hva (newPos_notMem_edgeArc_of_ne ht hfS hfe)
        · exact R.isDrawing.vertex_mem_edgeArc hl hv hva
  edge_inter := by
    intro f g hf hg hfg p hpf hpg
    by_cases hf₁ : f = d.newEdge₁
    · subst hf₁
      by_cases hg₂ : g = d.newEdge₂
      · subst hg₂
        exact edge_inter_new_new ht hpf hpg
      · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg (Ne.symm hfg) hg₂
        exact edge_inter_newEdge₁_old ht hgS hge hpf hpg
    · by_cases hf₂ : f = d.newEdge₂
      · subst hf₂
        by_cases hg₁ : g = d.newEdge₁
        · subst hg₁
          obtain ⟨h₁, h₂, h₃⟩ := edge_inter_new_new ht hpg hpf
          exact ⟨h₁, h₃, h₂⟩
        · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg hg₁ (Ne.symm hfg)
          exact edge_inter_newEdge₂_old ht hgS hge hpf hpg
      · obtain ⟨hfS, hfe⟩ := mem_edgeSet_skel_of_ne hf hf₁ hf₂
        by_cases hg₁ : g = d.newEdge₁
        · subst hg₁
          obtain ⟨h₁, h₂, h₃⟩ := edge_inter_newEdge₁_old ht hfS hfe hpg hpf
          exact ⟨h₁, h₃, h₂⟩
        · by_cases hg₂ : g = d.newEdge₂
          · subst hg₂
            obtain ⟨h₁, h₂, h₃⟩ := edge_inter_newEdge₂_old ht hfS hfe hpg hpf
            exact ⟨h₁, h₃, h₂⟩
          · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg hg₁ hg₂
            exact edge_inter_old_old hfS hfe hgS hge hfg hpf hpg

/-! ### The two new open edges, as arcs -/

end

/-! ### The realization of the subdivided structure -/

/-- **The realization of an edge subdivision.** The new 0-cell goes to the point of the drawn
edge at parameter `t`, the two new 1-cells are drawn by the two halves of that parametrization,
and every surviving cell is exactly where it was.

There is no geometric side condition: everything the construction needs is already carried by
`R`, and is extracted by the lemmas above rather than assumed. -/
noncomputable def realize (d : S.SubdivData) (R : S.Realization) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : (S.subdivideEdge d).Realization where
  pos := d.realizePos R t
  drawing := d.realizeDrawing R t
  injOn_pos := injOn_realizePos ht
  isDrawing := isDrawing_realize ht
  cell := d.realizeCell R t
  cell_vertex := cell_vertex_realize
  cell_edge := cell_edge_realize

variable (ht : t ∈ Ioo (0 : ℝ) 1)

@[simp] theorem realize_pos : (d.realize R t ht).pos = d.realizePos R t := rfl

@[simp] theorem realize_drawing : (d.realize R t ht).drawing = d.realizeDrawing R t := rfl

@[simp] theorem realize_cell : (d.realize R t ht).cell = d.realizeCell R t := rfl

include ht

/-! ### The realization refines the old one -/

/-! ### The subdivision does not move the skeleton

Cutting an edge in two adds a point that was already on the drawing and replaces one arc by two
whose union is that arc. So the realized 1-skeleton is literally the same set — which is what
lets a skeleton homeomorphism be transported across a subdivision without being rebuilt. -/

theorem pointSet_realize :
    pointSet (d.realizeGraph R t) (d.realizeDrawing R t) = pointSet R.graph R.drawing := by
  have hedge : (⋃ f ∈ E(R.graph), edgeArc R.drawing f) =
      edgeArc R.drawing d.edge ∪ ⋃ f ∈ E(S.skel) \ {d.edge}, edgeArc R.drawing f := by
    rw [← biUnion_insert, insert_sdiff_singleton,
      insert_eq_of_mem (show d.edge ∈ E(S.skel) from d.edge_mem_edgeSet), Realization.edgeSet_graph]
  have hnew : (⋃ f ∈ E(d.realizeGraph R t), edgeArc (d.realizeDrawing R t) f) =
      edgeArc R.drawing d.edge ∪ ⋃ f ∈ E(S.skel) \ {d.edge}, edgeArc R.drawing f := by
    rw [realizeGraph_edgeSet, d.skeleton_edgeSet, biUnion_insert, biUnion_insert,
      iUnion₂_congr (fun f (hf : f ∈ E(S.skel) \ {d.edge}) =>
        edgeArc_of_ne (d := d) (R := R) (t := t)
          (d.ne_newEdge₁_of_mem_cells (S.mem_cells_of_mem_edgeSet hf.1))
          (d.ne_newEdge₂_of_mem_cells (S.mem_cells_of_mem_edgeSet hf.1))),
      ← union_assoc, edgeArc_new_union ht]
  have hM : R.drawing d.edge t ∈ edgeArc R.drawing d.edge := ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  rw [pointSet, pointSet, hnew, hedge, realizeGraph_vertexSet, insert_union,
    insert_eq_of_mem (mem_union_right _ (mem_union_left _ hM))]

/-- **An edge subdivision does not move the realized 1-skeleton.** -/
theorem skeletonSet_realize : (d.realize R t ht).skeletonSet = R.skeletonSet := pointSet_realize ht

end SubdivData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.RealizeSubdivHomeo
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Transporting a skeleton homeomorphism across an edge subdivision

`Schoenflies/RealizeSubdiv.lean` builds `SubdivData.realize`, the realization of a subdivided
cell structure, and closes with the observation that it does **not** move the realized
1-skeleton (`SubdivData.skeletonSet_realize`). It also names what was missing: a
`CellStructure.SkeletonHomeo` between two realizations does not, by itself, carry the *half*
arcs of a subdivided edge onto each other. That gap is what `Schoenflies/ArcMonotone.lean`
fills, and this module spends.

`SubdivData.realizeHomeo` is the transported homeomorphism. As a point map it is *unchanged* —
`realizeHomeo_toFun` is `rfl` — which is exactly what `CellStructure.LimitTower.skelHomeo_succ`
in `Schoenflies/LimitMap.lean` asks for ("an edge subdivision leaves the skeleton map unchanged
as a point map"), and through it `Schoenflies.StageSequence`.

## The target parameter, and the two orientations

Subdividing at parameter `t` on the source side means subdividing at the parameter on the
target side where `R₂.drawing d.edge` sits at `g.toFun (R₁.drawing d.edge t)`. That is
`SubdivData.targetParam`, a plain `def` built from `Schoenflies.transferParam`; a caller never
has to guess it, and `SubdivData.drawing_targetParam` is its defining property.

`RealizeSubdiv.lean` warns that `IsDrawing.edge_param` is orientation-free, so `drawing e 0` may
be either end of `e`, and reads the orientation off with `SubdivData.leftParam`. The same issue
arises here on the `R₂` side, **and it is not forced**: the two realizations are independent
data, so nothing prevents `R₁` from drawing `d.edge` from `d.left` and `R₂` from drawing it from
`d.right`. This module does not assume otherwise. It does not need a second case distinction
either, because the transfer map handles it:

  `SubdivData.targetParam_leftParam` : `targetParam (leftParam R₁) = leftParam R₂`

holds whatever the two orientations are — `g` carries `R₁.pos d.left` to `R₂.pos d.left`, and
`leftParam R₂` is by definition the parameter sitting there. Correspondingly the arc identity
imported from `ArcMonotone` is stated over `uIcc`, which is unordered, so the two halves match
up without either orientation ever being named. The one place the orientations do surface is
`SubdivData.targetParam_ends`, which records that the pair `(targetParam 0, targetParam 1)` is
`(0, 1)` or `(1, 0)` — the input `ArcMonotone.param_mem_Ioo_of_ends` needs to know the new
target parameter is interior.

## Blueprint

* `def:matched-pair`, clause 3 — the transported `edgeArc_image` at the two new 1-cells is
  precisely "on each corresponding pair of edges, `g` restricts to a chosen homeomorphism
  between them, matching endpoints", propagated through operation 1.
* `def:generated-structure`, operation 1 (edge subdivision) — "the corresponding point is
  inserted into the corresponding edge"; `SubdivData.targetParam` is "corresponding".

Declarations:

* `Schoenflies.CellStructure.SubdivData.arcMatch_edge` — the drawn subdivided edge, its image,
  and `g` between them, as an `ArcMatch`.
* `Schoenflies.CellStructure.SubdivData.targetParam` — the corresponding parameter on the target
  side, with `drawing_targetParam`, `targetParam_leftParam`, `targetParam_rightParam`,
  `targetParam_ends`, `targetParam_mem_Ioo`.
* `Schoenflies.CellStructure.SubdivData.realizeHomeo` — the transported skeleton homeomorphism,
  with `realizeHomeo_toFun` / `realizeHomeo_invFun` / `realizeHomeo_eqOn`.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open _root_.Graph

namespace CellStructure

namespace SubdivData

variable {γ : Type*} {S : CellStructure γ} {R₁ R₂ : S.Realization}
  (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) {t : ℝ}

/-! ### The drawn subdivided edge, on both sides -/

theorem edgeArc_subset_skeletonSet (R : S.Realization) :
    R.drawing d.edge '' I ⊆ R.skeletonSet :=
  edgeArc_subset_pointSet (d.edge_mem_edgeSet_graph R)

/-- **The subdivided edge is drawn on both sides, and `g` carries one drawing onto the other.**
Everything the arc-monotonicity machinery needs, assembled from fields of `R₁`, `R₂` and `g`;
no new hypothesis. -/
theorem arcMatch_edge : ArcMatch (R₁.drawing d.edge) (R₂.drawing d.edge) g.toFun where
  continuousOn_src := d.continuousOn_drawing_edge R₁
  injOn_src := d.injOn_drawing_edge R₁
  continuousOn_tgt := d.continuousOn_drawing_edge R₂
  injOn_tgt := d.injOn_drawing_edge R₂
  continuousOn_map := g.continuousOn_toFun.mono (d.edgeArc_subset_skeletonSet R₁)
  injOn_map := g.injOn.mono (d.edgeArc_subset_skeletonSet R₁)
  image_eq := g.edgeArc_image d.edge_mem_edgeSet

/-! ### The corresponding parameter on the target side -/

/-- **The parameter at which the target drawing sits at the image of the source point.**

A `def`, not an existential: the subdivided target realization is `d.realize R₂ (d.targetParam g
t) _`, and every lemma below refers to it by name. -/
noncomputable def targetParam (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) (t : ℝ) : ℝ :=
  transferParam (R₁.drawing d.edge) (R₂.drawing d.edge) g.toFun t

/-- **The defining property of the target parameter.** -/
theorem drawing_targetParam (ht : t ∈ I) :
    R₂.drawing d.edge (d.targetParam g t) = g.toFun (R₁.drawing d.edge t) :=
  (d.arcMatch_edge g).apply_param ht

/-- The endpoint of the subdivided edge at `d.left` corresponds to the endpoint at `d.left`,
whichever way round either realization happens to draw the edge. -/
theorem targetParam_leftParam : d.targetParam g (d.leftParam R₁) = d.leftParam R₂ := by
  refine (d.arcMatch_edge g).param_eq (d.leftParam_mem_I R₂) ?_
  rw [d.drawing_leftParam R₂, d.drawing_leftParam R₁]
  exact (g.pos_apply d.isLink.left_mem).symm

/-- …and likewise at `d.right`. -/
theorem targetParam_rightParam : d.targetParam g (d.rightParam R₁) = d.rightParam R₂ := by
  refine (d.arcMatch_edge g).param_eq (d.rightParam_mem_I R₂) ?_
  rw [d.drawing_rightParam R₂, d.drawing_rightParam R₁]
  exact (g.pos_apply d.isLink.right_mem).symm

/-- **The two endpoint parameters go to the two endpoint parameters**, in one order or the
other. This is the only statement in the file that mentions the orientations at all, and it is
here only because interiority of the new target parameter needs it. -/
theorem targetParam_ends :
    (d.targetParam g 0 = 0 ∧ d.targetParam g 1 = 1) ∨
      (d.targetParam g 0 = 1 ∧ d.targetParam g 1 = 0) := by
  have hL := d.targetParam_leftParam g
  have hR := d.targetParam_rightParam g
  rw [rightParam, rightParam] at hR
  rcases d.leftParam_eq_zero_or_one R₁ with h1 | h1 <;>
      rcases d.leftParam_eq_zero_or_one R₂ with h2 | h2 <;>
      simp only [h1, h2, sub_zero, sub_self] at hL hR
  · exact Or.inl ⟨hL, hR⟩
  · exact Or.inr ⟨hL, hR⟩
  · exact Or.inr ⟨hR, hL⟩
  · exact Or.inl ⟨hR, hL⟩

/-- **An interior source parameter has an interior target parameter** — so the target
realization can be subdivided at it. -/
theorem targetParam_mem_Ioo (ht : t ∈ Ioo (0 : ℝ) 1) : d.targetParam g t ∈ Ioo (0 : ℝ) 1 :=
  (d.arcMatch_edge g).param_mem_Ioo_of_ends (d.targetParam_ends g) ht

/-- **`g` carries a piece of the drawn edge onto the corresponding piece.** The whole content of
`Schoenflies/ArcMonotone.lean`, specialized to the subdivided edge. -/
theorem image_edge_uIcc {s u : ℝ} (hs : s ∈ I) (hu : u ∈ I) :
    g.toFun '' (R₁.drawing d.edge '' uIcc s u) =
      R₂.drawing d.edge '' uIcc (d.targetParam g s) (d.targetParam g u) :=
  (d.arcMatch_edge g).image_image_uIcc hs hu

/-! ### The transported skeleton homeomorphism -/

/-- **The skeleton homeomorphism, transported across an edge subdivision.**

The point map is untouched: a subdivision does not move the realized 1-skeleton
(`skeletonSet_realize`), so six of the eight fields are the old ones read through that equality.
The two that are not — `pos_apply` at the new 0-cell and `edgeArc_image` at the two new 1-cells
— are `drawing_targetParam` and `image_edge_uIcc`. -/
noncomputable def realizeHomeo (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    SkeletonHomeo (d.realize R₁ t ht)
      (d.realize R₂ (d.targetParam g t) (d.targetParam_mem_Ioo g ht)) where
  toFun := g.toFun
  invFun := g.invFun
  continuousOn_toFun := by
    rw [skeletonSet_realize ht]; exact g.continuousOn_toFun
  continuousOn_invFun := by
    rw [skeletonSet_realize (d.targetParam_mem_Ioo g ht)]; exact g.continuousOn_invFun
  leftInvOn := by
    rw [skeletonSet_realize ht]; exact g.leftInvOn
  rightInvOn := by
    rw [skeletonSet_realize (d.targetParam_mem_Ioo g ht)]; exact g.rightInvOn
  pos_apply := by
    intro v hv
    rw [subdivideEdge_skel, d.skeleton_vertexSet, mem_insert_iff] at hv
    simp only [realize_pos]
    rcases hv with rfl | hv
    · rw [realizePos_newVertex, realizePos_newVertex]
      exact (d.drawing_targetParam g (Ioo_subset_Icc_self ht)).symm
    · rw [realizePos_of_mem_vertexSet hv, realizePos_of_mem_vertexSet hv]
      exact g.pos_apply hv
  edgeArc_image := by
    intro e he
    rw [subdivideEdge_skel, d.skeleton_edgeSet] at he
    simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff] at he
    simp only [realize_drawing]
    rcases he with rfl | rfl | ⟨heS, hee⟩
    · -- The first new edge: the half from `d.left` to the new point, on both sides.
      rw [edgeArc_newEdge₁, edgeArc_newEdge₁,
        d.image_edge_uIcc g (d.leftParam_mem_I R₁) (Ioo_subset_Icc_self ht),
        d.targetParam_leftParam g]
    · -- The second new edge: the half from the new point to `d.right`.
      rw [edgeArc_newEdge₂, edgeArc_newEdge₂,
        d.image_edge_uIcc g (Ioo_subset_Icc_self ht) (d.rightParam_mem_I R₁),
        d.targetParam_rightParam g]
    · -- An untouched edge: both drawings are the old ones.
      have hc := S.mem_cells_of_mem_edgeSet heS
      rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hc) (d.ne_newEdge₂_of_mem_cells hc),
        edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hc) (d.ne_newEdge₂_of_mem_cells hc)]
      exact g.edgeArc_image heS

@[simp] theorem realizeHomeo_toFun (ht : t ∈ Ioo (0 : ℝ) 1) :
    (d.realizeHomeo g ht).toFun = g.toFun := rfl

@[simp] theorem realizeHomeo_invFun (ht : t ∈ Ioo (0 : ℝ) 1) :
    (d.realizeHomeo g ht).invFun = g.invFun := rfl

end SubdivData

end CellStructure

end Schoenflies
end


