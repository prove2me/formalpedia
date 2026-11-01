-- Prove2me | Definitions.Def_Q146C011
-- name    : Q146C011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:31:46.921492+00:00
-- url     : https://prove2.me/theorems/69090b58-6777-4089-a7ba-b532a1f3f094
-- title:
--   Definitions bundle Q146C011 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 229 declarations of OpenAI's Lean: 39 definitions, 3 inductive types or structures, 1 instance and 186 theorems. The definitions and types are `OAI.CircleDomainRigidity.FiniteJordanConfiguration.chosenStep`, `OAI.CircleDomainRigidity.FiniteJordanConfiguration.cumulativeMap`, `OAI.CircleDomainRigidity.FiniteJordanConfiguration.iterate`, `OAI.CircleDomainRigidity.FiniteJordanConfiguration.stageMap`, `Schoenflies.AnchoredInitialData.generatedPair`, `Schoenflies.CellStructure.OuterIncidenceAtMostTwo`, `Schoenflies.CellStructure.OuterIncidenceAtMostTwoEverywhere`, `Schoenflies.CellStructure.OuterOnlyAt`, `Schoenflies.GeneratedPair.SourceEndpointReady`, `Schoenflies.GeneratedPair.SubdivideTargetAtData`, `Schoenflies.GeneratedPair.SubdivideTargetSetData`, `Schoenflies.QuantitativeForwardStage.parent`, `Schoenflies.QuantitativeReverseStage.parent`, `Schoenflies.QuantitativeSchedule.CentresDense`, `Schoenflies.QuantitativeSuccessor.parent`, `Schoenflies.TargetCommonSubdivision`, `Schoenflies.TargetCommonSubdivisionData`, `Schoenflies.TargetEarEndpointAccessibility`, `Schoenflies.TargetEarFreshInvariant`, `Schoenflies.TargetEarStep`, `Schoenflies.TargetEarStepConstruction`, `Schoenflies.attachRings`, `Schoenflies.attachSpokes`, `Schoenflies.denseQuantitativeSchedule`, `Schoenflies.denseQuantitativeStageSequence`, `Schoenflies.meshAssembly`, `Schoenflies.meshCore`, `Schoenflies.meshEar`, `Schoenflies.prescribedAnchoredInitialData`, `Schoenflies.prescribedJordanStageSequence`, `Schoenflies.prescribedSourceAnchorSet`, `Schoenflies.prescribedTargetAnchorSet`, `Schoenflies.quantitativeFreshTargetSet`, `Schoenflies.quantitativeParent`, `Schoenflies.quantitativeStage`, `Schoenflies.quantitativeStageSequence`, `Schoenflies.ringArc`, `Schoenflies.ringGraph`, `Schoenflies.scheduledQuantitativeSuccessor`, `Schoenflies.spokeGraph` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundaryAnchors`, `BoundaryContinuity2`, `CircleDomains_Topology_PlanarSchoenfliesProof`, `CircleDomains_Uniformization_ConformalJordanCapImage`, `CircleDomains_Uniformization_JordanCircularizationSequence`, `CircleDomains_Uniformization_JordanCircularizationStep`, `CommonSubdivision`, `Endgame`, `FiniteTransferTarget`, `FreshDenseSelection`, `InitialGenerated`, `InitialOuterCycle`, `InteriorHomeomorphism`, `JordanSchoenflies`, `QuantitativeForwardStages`, `QuantitativeRecursion`, `QuantitativeStages`, `SquareMesh`, `SquareMeshClosed`, `StageTower`, `StageTransition`, `TargetOverlay`.
--
--   **Imports.** It imports the published bundle `Def_KoebeCircleDomains`; the bundles `Q146C009` and `Q146C010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q146C012`; the proofs of `OAI.CircleDomainRigidity.exists_round_invariant_principal_approximation_with_coefficient`, `OAI.CircleDomainRigidity.finiteJordanModelUniformization`, `OAI.CircleDomainRigidity.principalConductivityScalarSolver`, `OAI.CircleDomainRigidity.principalRealBeltrami`, `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C009
import Definitions.Def_Q146C010

section
-- module Solutions.Q146_CD.Endgame
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The endgame: from the square extension to the relative Jordan–Schönflies theorem

This module carries the whole tail of the manuscript — `prop:square-reduction`,
`thm:closed-interior-extension`, `prop:pointed-extension`, `prop:exterior-extension` and
`thm:main` — parametrically over the square-extension interface.

Every theorem below takes `Schoenflies.SquareExtension` as an explicit hypothesis and assumes
nothing else. In particular the standing hypothesis `harc` that older modules thread is
discharged here at the call site, from `Schoenflies.arc_complement` in
`Schoenflies/JordanClosed.lean`; it no longer appears in any signature. The implication proved
by this module is

    SquareExtension  ⟹  thm:main.

`Schoenflies/JordanSchoenflies.lean` supplies `SquareExtension` from the quantitative
boundary construction and therefore closes this implication without an extra hypothesis.

## What `SquareExtension` says

`Schoenflies.SquareExtension` is `thm:square-extension` written in the `Schoenflies.IsHomeoOn`
style of `Schoenflies/Inversion.lean`: for every Jordan curve `C` and every restricted
homeomorphism `u : C → S` (with named inverse `v`) there are maps `F`, `G` restricting to
mutually inverse homeomorphisms between `C ∪ Int(C)` and `Q`, with `F = u` on `C`. Here
`S = Schoenflies.modelCurve` and `Q = Schoenflies.Plane.closedSquare 0 1`; `S = ∂Q` is
`Schoenflies.modelCurve_eq_frontier`, so this is literally the blueprint's `Q = [-1,1]²`,
`S = ∂Q`.

## The chain

* `prop:square-reduction` is the blueprint's: pick a homeomorphism `h : C' → S`
  (`lem:jordan-circle`), extend `h ∘ f` and `h` to the square, and compose one with the inverse
  of the other. `thm:closed-interior-extension` is the same statement — under the standing
  assumption of `SquareExtension` the reduction *is* the theorem — and is recorded separately
  because everything downstream cites it by that name.
* `prop:pointed-extension` is the interesting one. Given the closed-interior extension `Φ` and
  a square chart `Θ` of the *target* disc, the two points `Θ(Φ(a))` and `Θ(b)` are interior to
  `Q`, because `Θ` carries `C'` onto `∂Q` and hence — being a bijection — `Int(C')` onto
  `Q ∖ ∂Q`. `lem:square-point-mover` then supplies a boundary-fixing self-homeomorphism `M` of
  `Q` moving the first to the second, and `Θ⁻¹ ∘ M ∘ Θ ∘ Φ` is the pointed extension: it agrees
  with `Φ` on `C` because `M` fixes `∂Q` pointwise. This discharges
  `Schoenflies.PointedInteriorExtension`, the last hypothesis of `prop:exterior-extension`.
* `thm:main` is the closed pasting lemma applied twice, once to `F` and once to its inverse.
  The one point the blueprint leaves implicit is that the pasted map is *injective*: the
  interior extension carries `Int(C)` onto `Int(C')` and the exterior extension carries
  `Ext(C)` onto `Ext(C')`, so the two pieces cannot collide. Both facts are instances of
  `Schoenflies.image_eq_diff_of_bijOn_union`, which is the "a bijection matching one part of a
  partition matches the other part" principle.

## The parametric construction interface

Within this deliberately parametric module, every conclusion depends on the *Prop*
`SquareExtension`, so no `def` can produce the maps without an application of choice to that
hypothesis. What is exported as data independently of the interface is
`Schoenflies.paste` (the pasted map itself, with its two evaluation lemmas) and
`Schoenflies.IsHomeoOn.homeomorphOfUniv` (the passage from a global `IsHomeoOn` to a genuine
`Plane ≃ₜ Plane`). The theorems below return the maps in the unbundled `∃ F G, IsHomeoOn F G …`
shape of `Schoenflies.exterior_extension`, which composes.

## Blueprint

* `Schoenflies.SquareExtension` — the **`thm:square-extension`** interface, discharged in
  `Schoenflies/JordanSchoenflies.lean`.
* `Schoenflies.square_reduction` — `prop:square-reduction`.
* `Schoenflies.closed_interior_extension` — **`thm:closed-interior-extension`**.
* `Schoenflies.pointed_extension` — `prop:pointed-extension`; it proves
  `Schoenflies.PointedInteriorExtension` of `Schoenflies/Inversion.lean`.
* `Schoenflies.exterior_extension_of_squareExtension` — `prop:exterior-extension`, restated
  with `harc` discharged and only `SquareExtension` left.
* `Schoenflies.jordan_schoenflies_of_squareExtension`,
  `Schoenflies.jordan_schoenflies_homeomorph_of_squareExtension`,
  `Schoenflies.jordan_schoenflies_of_homeomorph_of_squareExtension` — **`thm:main`**, the relative
  Jordan–Schönflies theorem, in the unbundled, the bundled, and the blueprint's own shape.

Supporting material with no blueprint statement, all general and all candidates for hoisting
into the module that owns `Schoenflies.IsHomeoOn`:
`Schoenflies.exists_isHomeoOn_of_homeomorph`, `Schoenflies.IsHomeoOn.homeomorphOfUniv`,
`Schoenflies.IsHomeoOn.image_inv_eq`, `Schoenflies.image_eq_diff_of_bijOn_union`,
`Schoenflies.paste` and `Schoenflies.Plane.IsSquareMover.isHomeoOn`.
-/

open Bornology Metric Set

namespace Schoenflies

/-! ### Restricted homeomorphisms: three general tools

`Schoenflies.IsHomeoOn` (in `Schoenflies/Inversion.lean`) is the unbundled "restricts to a
homeomorphism of `S` onto `T`". Three facts about it are needed below and are not there; they
are general, and the section comment at `IsHomeoOn` already asks for the whole notion to be
hoisted, so these should travel with it. -/

/-! ### The pasted map

`thm:main` glues the interior and the exterior extension. The glued map is `Set.piecewise`
under a different name, spelled so that the two evaluation lemmas below are the only interface
the proof needs. -/

/-! ### The square `Q` and its boundary `S`

The blueprint's `Q = [-1,1]²` is `Plane.closedSquare 0 1` and its boundary `S = ∂Q` is
`modelCurve`, by `modelCurve_eq_frontier`. One consequence is needed: removing the boundary
from the closed square leaves the open square, which is where `lem:square-point-mover` wants
its two points. -/

/-! ### `thm:square-extension`, assumed

This is the one statement the module assumes, and the only thing standing between the library
and `thm:main`. It is the last big theorem of the manuscript; its proof occupies the whole of
Part II §§"Strongly accessible boundary points"–"Continuity at the Jordan curve". -/

/-! ### Disjointness of a curve from its two regions

A curve is disjoint from either of its two regions, and adding it and removing it again is the
identity. The pastings below use these constantly. -/

variable {C C' : Set Plane}

/-! ### `prop:square-reduction` and `thm:closed-interior-extension`

The blueprint's proof verbatim: choose `h : C' → S` by `lem:jordan-circle`, extend `h ∘ f` and
`h` over the two closed discs by `thm:square-extension`, and take `Ψ⁻¹ ∘ Φ`. -/

/-! ### `prop:pointed-extension`

The blueprint's proof, with one step made explicit: the square chart `Θ` of the *target* disc
carries `Int(C')` onto `Q ∖ ∂Q = Q°`, because it carries `C'` onto `∂Q` and is a bijection of
the closed disc onto `Q`. That is what puts the two points `Θ(Φ(a))` and `Θ(b)` in the open
square, where `lem:square-point-mover` lives. -/

/-- **`prop:pointed-extension` (pointed closed-interior extension).** A boundary homeomorphism
`f : C → C'` and prescribed points `a ∈ Int(C)`, `b ∈ Int(C')` admit a closed-interior
extension `H` with `H(a) = b`.

This is `Schoenflies.PointedInteriorExtension`, the hypothesis of
`Schoenflies.exterior_extension`, discharged. -/
theorem pointed_extension (hsq : SquareExtension) : PointedInteriorExtension := by
  intro C C' f g a b hC hC' hfg ha hb
  -- The unpointed extension, and a square chart of the target disc.
  obtain ⟨Φ, Φ', hΦ, hΦeq⟩ := square_reduction hsq hC hC' hfg
  obtain ⟨e⟩ := hC'.homeomorph_modelCurve
  obtain ⟨h, k, hhk, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨Θ, Θ', hΘ, hΘeq⟩ := hsq C' h k hC' hhk
  -- `Θ` carries the boundary onto `∂Q`, hence the interior onto `Q ∖ ∂Q = Q°`.
  have hΘC : Θ '' C' = modelCurve := (Set.EqOn.image_eq hΘeq).trans hhk.image_eq
  have hΘin : Θ '' inside C' = Plane.openSquare 0 1 := by
    rw [← closedSquare_sdiff_modelCurve]
    exact image_eq_diff_of_bijOn_union hΘ.bijOn hΘC (disjoint_curve_inside C')
  -- `Φ` carries `Int(C)` onto `Int(C')`, so `Φ a` is an interior point of the target.
  have hΦin : Φ '' inside C = inside C' := image_inside_eq hΦ hΦeq hfg.image_eq
  have haΦ : Φ a ∈ inside C' := by rw [← hΦin]; exact ⟨a, ha, rfl⟩
  have hx : Θ (Φ a) ∈ Plane.openSquare 0 1 := by rw [← hΘin]; exact ⟨Φ a, haΦ, rfl⟩
  have hy : Θ b ∈ Plane.openSquare 0 1 := by rw [← hΘin]; exact ⟨b, hb, rfl⟩
  -- `lem:square-point-mover`: a boundary-fixing self-homeomorphism of `Q` moving one to the
  -- other. Conjugating it by `Θ` and composing with `Φ` is the pointed extension.
  obtain ⟨M, N, hM, hMx, -⟩ := Plane.exists_squareMover hx hy
  refine ⟨_, _, ((hΦ.comp hΘ).comp hM.isHomeoOn).comp hΘ.symm, fun z hz => ?_, ?_⟩
  · have h1 : f z ∈ C' := hfg.mapsTo hz
    change Θ' (M (Θ (Φ z))) = f z
    rw [hΦeq hz]
    -- `M` is the identity on `∂Q`, and `Θ (f z)` lies there.
    have h2 : Θ (f z) ∈ frontier (Plane.closedSquare 0 1) := by
      rw [← modelCurve_eq_frontier, ← hΘC]
      exact ⟨f z, h1, rfl⟩
    rw [hM.eqOn_frontier h2]
    exact hΘ.invOn.1 (Set.mem_union_left _ h1)
  · change Θ' (M (Θ (Φ a))) = b
    rw [hMx]
    exact hΘ.invOn.1 (Set.mem_union_right _ hb)

/-! ### `prop:exterior-extension`, from the square extension

`Schoenflies.exterior_extension` in `Schoenflies/Inversion.lean` is proved already; it carries
two hypotheses, the standing `harc` of `thm:jordan` and `PointedInteriorExtension`. Part I
discharges the first (`Schoenflies.arc_complement`) and the previous theorem discharges the
second, so only `SquareExtension` survives. -/

/-- **`prop:exterior-extension` (closed-exterior extension)**, with everything discharged but
the square extension: every homeomorphism between two Jordan curves extends to a homeomorphism
of their closed exteriors. -/
theorem exterior_extension_of_squareExtension (hsq : SquareExtension) {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C') ∧ EqOn F f C :=
  exterior_extension (fun _ hA => arc_complement hA) (pointed_extension hsq) hC hC' hfg

/-! ### `thm:main`

The closed pasting lemma, twice. The blueprint's proof is three sentences; the two facts it
leaves implicit are that the closed interior and the closed exterior are *closed* (they are the
closures of the two regions, `IsRegionOf.closure_eq`) and that the pasted map is injective,
which is `image_inside_eq` and `image_outside_eq`. -/

/-- **`thm:main`, the relative Jordan–Schönflies theorem.** Every homeomorphism between two
Jordan curves extends to a homeomorphism of the whole plane.

This form takes `Schoenflies.SquareExtension` as its sole auxiliary theorem. It is the unbundled
form; `Schoenflies.jordan_schoenflies_homeomorph_of_squareExtension` packages the result as a
self-homeomorphism of the plane. -/
theorem jordan_schoenflies_of_squareExtension (hsq : SquareExtension)
    {f g : Plane → Plane} (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G univ univ ∧ EqOn F f C := by
  have hsC : IsSeparating C := jordan_curve_theorem hC
  have hsC' : IsSeparating C' := jordan_curve_theorem hC'
  obtain ⟨Fi, Gi, hFi, hFieq⟩ := closed_interior_extension hsq hC hC' hfg
  obtain ⟨Fe, Ge, hFe, hFeeq⟩ := exterior_extension_of_squareExtension hsq hC hC' hfg
  -- The four "region onto region" facts that make the paste injective.
  have hFiin : Fi '' inside C = inside C' := image_inside_eq hFi hFieq hfg.image_eq
  have hFeout : Fe '' outside C = outside C' := image_outside_eq hFe hFeeq hfg.image_eq
  have hGiin : Gi '' inside C' = inside C := hFi.image_inv_eq Set.subset_union_right hFiin
  have hGeout : Ge '' outside C' = outside C := hFe.image_inv_eq Set.subset_union_right hFeout
  -- The inverse maps agree on `C'`, where both are `g`.
  have hGieq : EqOn Gi g C' := by
    intro w hw
    have hgw : g w ∈ C := hfg.mapsTo_inv hw
    have hFw : Fi (g w) = w := by rw [hFieq hgw]; exact hfg.invOn.2 hw
    calc Gi w = Gi (Fi (g w)) := by rw [hFw]
      _ = g w := hFi.invOn.1 (Set.mem_union_left _ hgw)
  have hGeeq : EqOn Ge g C' := by
    intro w hw
    have hgw : g w ∈ C := hfg.mapsTo_inv hw
    have hFw : Fe (g w) = w := by rw [hFeeq hgw]; exact hfg.invOn.2 hw
    calc Ge w = Ge (Fe (g w)) := by rw [hFw]
      _ = g w := hFe.invOn.1 (Set.mem_union_left _ hgw)
  -- Evaluation of the two pasted maps on each of the two closed pieces. Off the closed
  -- interior the paste is `Fe` by definition; *on* the closed interior it is `Fi`, and the two
  -- agree on the overlap `C`, where both are `f`.
  have hFint : EqOn (paste (C ∪ inside C) Fi Fe) Fi (C ∪ inside C) := fun _ hz => paste_of_mem hz
  have hFext : EqOn (paste (C ∪ inside C) Fi Fe) Fe (C ∪ outside C) := by
    rintro z (hzC | hzout)
    · rw [paste_of_mem (Set.mem_union_left _ hzC), hFieq hzC, hFeeq hzC]
    · refine paste_of_notMem fun hz => ?_
      exact Set.disjoint_left.1 disjoint_inside_outside
        (hz.resolve_left fun h => Set.disjoint_left.1 (disjoint_curve_outside C) h hzout) hzout
  have hGint : EqOn (paste (C' ∪ inside C') Gi Ge) Gi (C' ∪ inside C') :=
    fun _ hw => paste_of_mem hw
  have hGext : EqOn (paste (C' ∪ inside C') Gi Ge) Ge (C' ∪ outside C') := by
    rintro w (hwC | hwout)
    · rw [paste_of_mem (Set.mem_union_left _ hwC), hGieq hwC, hGeeq hwC]
    · refine paste_of_notMem fun hw => ?_
      exact Set.disjoint_left.1 disjoint_inside_outside
        (hw.resolve_left fun h => Set.disjoint_left.1 (disjoint_curve_outside C') h hwout) hwout
  refine ⟨paste (C ∪ inside C) Fi Fe, paste (C' ∪ inside C') Gi Ge,
    ⟨mapsTo_univ _ _, mapsTo_univ _ _, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- continuity of `F`: the closed pasting lemma on the two closed sides
    rw [← union_inside_union_outside C]
    exact Plane.continuousOn_union_of_isClosed (isClosed_union_inside hsC)
      (isClosed_union_outside hsC) (hFi.continuousOn.congr hFint)
      (hFe.continuousOn.congr hFext)
  · rw [← union_inside_union_outside C']
    exact Plane.continuousOn_union_of_isClosed (isClosed_union_inside hsC')
      (isClosed_union_outside hsC') (hFi.continuousOn_inv.congr hGint)
      (hFe.continuousOn_inv.congr hGext)
  · -- `G ∘ F = id`. The exterior case is where injectivity lives: `Fe z` is *exterior*, so the
    -- paste for `G` reads it with `Ge` and not with `Gi`.
    intro z _
    by_cases hz : z ∈ C ∪ inside C
    · rw [hFint hz, hGint (hFi.mapsTo hz), hFi.invOn.1 hz]
    · have hzout : z ∈ outside C := mem_outside_of_notMem_union_inside hz
      have hzL : z ∈ C ∪ outside C := Or.inr hzout
      have hFz : Fe z ∈ outside C' := by rw [← hFeout]; exact ⟨z, hzout, rfl⟩
      rw [hFext hzL, hGext (Or.inr hFz), hFe.invOn.1 hzL]
  · -- `F ∘ G = id`
    intro w _
    by_cases hw : w ∈ C' ∪ inside C'
    · rw [hGint hw, hFint (hFi.mapsTo_inv hw), hFi.invOn.2 hw]
    · have hwout : w ∈ outside C' := mem_outside_of_notMem_union_inside hw
      have hwL : w ∈ C' ∪ outside C' := Or.inr hwout
      have hGw : Ge w ∈ outside C := by rw [← hGeout]; exact ⟨w, hwout, rfl⟩
      rw [hGext hwL, hFext (Or.inr hGw), hFe.invOn.2 hwL]
  · exact fun z hz => (hFint (Set.mem_union_left _ hz)).trans (hFieq hz)

/-- **`thm:main`**, with the extension packaged as a self-homeomorphism of the plane. This is
the blueprint's statement: *there is a homeomorphism `F : ℝ² → ℝ²` whose restriction to `C` is
`f`*. -/
theorem jordan_schoenflies_homeomorph_of_squareExtension (hsq : SquareExtension)
    {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F : Plane ≃ₜ Plane, EqOn F f C := by
  obtain ⟨F, G, hFG, hFeq⟩ := jordan_schoenflies_of_squareExtension hsq hC hC' hfg
  exact ⟨hFG.homeomorphOfUniv, hFeq⟩

/-- **`thm:main`**, taking the boundary homeomorphism in bundled form, which is how the
blueprint states it: `f : C → C'` a homeomorphism of subspaces. -/
theorem jordan_schoenflies_of_homeomorph_of_squareExtension (hsq : SquareExtension)
    (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z := by
  obtain ⟨f, g, hfg, hfe⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, hF⟩ := jordan_schoenflies_homeomorph_of_squareExtension hsq hC hC' hfg
  exact ⟨F, fun z => (hF z.2).trans (hfe z z.2)⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryContinuity2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.relabelDrawing_apply _root_.Graph.traceGraph_isLink _root_.Graph.traceGraph_vertexSet _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.EarStepData.pair_src _root_.Schoenflies.EarStepData.pair_tgt _root_.Schoenflies.GeneratedPair.split_str _root_.Schoenflies.GeneratedPair.subdivide_src _root_.Schoenflies.GeneratedPair.subdivide_tgt _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.StageSequence.limitTower_region _root_.Schoenflies.StageSequence.limitTower_region' _root_.Schoenflies.TargetEarStepData.pair_src _root_.Schoenflies.TargetEarStepData.pair_tgt _root_.Schoenflies.TargetSegmentCover.mem_openTargetEdgePieces _root_.Schoenflies.TargetSegmentCover.mem_squareMeshPieces _root_.Schoenflies.attachGraph_pointSet _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.mem_currentOverlayPieces _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Continuity at the Jordan curve, and `thm:square-extension`

The last three statements of the manuscript: `lem:crosscut-side-correspondence`,
`prop:boundary-continuity`, and the assembly of `thm:square-extension` from them.

`Schoenflies/BoundaryContinuity.lean` proves the statement with the real combinatorial content,
`lem:skeleton-crosscuts` (`Graph.IsStageOn.exists_crosscut`), for one finite
plane graph. This module takes the crosscuts as given and finishes the section.

## The construction inputs

This module isolates the construction-dependent data as explicit hypotheses. They are supplied
for the quantitative stage recursion in `Schoenflies/InteriorHomeomorphism.lean` and
`Schoenflies/BoundaryAnchors.lean`. Nothing else is assumed: `thm:jordan` and
`thm:general-crosscut` are used through `Schoenflies/JordanClosed.lean`, where their hypotheses
are supplied.

* **`prop:interior-homeomorphism`** enters as `IsHomeoOn F F' (inside C) (Plane.openSquare 0 1)`
  — the `Schoenflies.IsHomeoOn` shape of `Schoenflies/Inversion.lean`: a map, a named inverse,
  and the continuity and inverse laws on the two sets.
* **`lem:skeleton-crosscuts` + `prop:skeleton-agreement`** enter as
  `Schoenflies.HasAnchorCrosscuts`: for two distinct anchors `a, b` a crosscut `P` of `C` from
  `a` to `b`, a crosscut `P'` of `Q°` from `u a` to `u b`, and the agreement
  `F '' (P ∖ {a,b}) = P' ∖ {u a, u b}`. This is exactly what the finite skeleton homeomorphism
  produces once `Graph.IsStageOn.exists_crosscut` has been run in the stage containing `a`
  and `b` (see `Graph.IsStageOn.exists_isCrosscut` below, which does the packaging).
* **`lem:anchor-density`** enters as the two clauses `𝒜 ⊆ C` and `C ⊆ closure 𝒜`, plus its
  "incident with a nonboundary edge" clause in the germ form `Schoenflies.HasSpokes`: at an
  anchor `c`, arbitrarily small connected pieces `J` of the Jordan domain which cling to `c`
  and whose `F`-images cling to `u c`. That is the initial subarc of the spoke at `c`, and its
  image, which is the initial subarc of the target spoke — the *only* use the blueprint makes
  of the spokes, in the paragraph of `lem:crosscut-side-correspondence` beginning "Choose
  `c ∈ 𝒜` in the relative interior of `Aᵢ`".

`Schoenflies.HasLimitHomeomorphism` bundles the four over all curves, and
`Schoenflies.squareExtension_of_hasLimitHomeomorphism` derives
`Schoenflies.SquareExtension` — the exact `def` of
`Schoenflies/Endgame.lean` — from it. The proof of `HasLimitHomeomorphism` assembled in
`Schoenflies/JordanSchoenflies.lean` closes the full theorem.

## The two arguments

*Which side maps to which side* is `Schoenflies.crosscut_side_correspondence`. The homeomorphism
of the interiors carries `Int(C) ∖ P` onto `Q° ∖ P'` (`Schoenflies.image_inside_sdiff`), hence
carries each of the two components onto one of the two; the labels are pinned by a spoke germ
`J` at an anchor `c` in the relative interior of `A₁`. `J` is connected, misses `P` because it
is small and `c ∉ P`, so it lies in one side; `c ∈ closure J` and `closure(Uᵢ) ∩ C = Aᵢ` force
that side to be `U₁`. The same two facts on the target, applied to `F '' J`, force `F '' U₁` to
be `U'₁`.

*Boundary continuity* is `Schoenflies.tendsto_nhdsWithin_inside`. The blueprint argues on a
subsequence; the filter form of the same argument avoids extracting one. If `F` does not tend
to `u p` along `𝓝[Int C] p`, then `l' = 𝓝[Int C] p ⊓ 𝓟 (F⁻¹ Wᶜ)` is a nonzero filter for some
open `W ∋ u p`, and compactness of `Q` gives a cluster point `q ∈ Wᶜ` of `F` along `l'`. If
`q ∈ Q°` then pushing `l'` through `F'` shows `p = F' q ∈ Int(C)`, impossible. Otherwise
`q ∈ S`; anchors `a, b` separating `p` from `r = u⁻¹ q` give a crosscut whose `p`-side contains
every point of `Int(C)` near `p`, so `l'` sits on that side, so `q` lies in the closure of the
corresponding target side, whose trace on `S` is `u(A₁)` — and `r ∉ A₁`.

## Blueprint

* `Graph.IsStageOn.exists_isCrosscut` — **`lem:skeleton-crosscuts`** repackaged as
  `Schoenflies.IsCrosscut`, the form `thm:general-crosscut` consumes.
* `Schoenflies.IsCutPair.separates`, `Schoenflies.exists_separating_anchors` — the selection
  step of `prop:boundary-continuity`: two anchors putting two prescribed points of the curve on
  opposite arcs. Uses **`lem:anchor-density`** through the density hypothesis alone.
* `Schoenflies.IsCrosscut.image_of_injOn`, `Schoenflies.image_sdiff_eq_of_eqOn` — the two
  steps a consumer performs to discharge `Schoenflies.HasAnchorCrosscuts` from a finite skeleton
  homeomorphism. No blueprint statement of their own; they are the second paragraph of the
  proof of **`lem:skeleton-crosscuts`**, "the finite skeleton homeomorphism sends `P` to a
  simple path `P'`".
* `Schoenflies.crosscut_side_correspondence` — **`lem:crosscut-side-correspondence`**.
* `Schoenflies.extendByBoundary`, `Schoenflies.tendsto_nhdsWithin_inside`,
  `Schoenflies.boundary_continuity` — **`prop:boundary-continuity`**.
* `Schoenflies.isHomeoOn_extendByBoundary`,
  `Schoenflies.squareExtension_of_hasLimitHomeomorphism` —
  **`thm:square-extension`**.
-/

open Bornology Filter Metric Schoenflies Set Topology
open scoped _root_.Graph

namespace Schoenflies

variable {C 𝒜 A₁ A₂ B₁ B₂ P P' : Set Plane} {u v F F' : Plane → Plane} {a b p r : Plane}

/-! ### Two elementary facts about the model square

`Q° = Int(S)`: the open square is the Jordan domain of the model curve. This is the bridge
between the shape `prop:interior-homeomorphism` is stated in (a homeomorphism onto
`Plane.openSquare 0 1`) and the shape `thm:general-crosscut` speaks in (`inside modelCurve`). -/

/-! ### Pushing arcs forward

`lem:crosscut-side-correspondence` labels the target sides by `u(A₁)` and `u(A₂)`, so the two
target arcs have to be produced as images. Nothing here is specific to the square. -/

/-! ### Anchors that separate

The selection step of `prop:boundary-continuity`. Given two distinct points `p, r` of the curve
and a dense set `𝒜` of anchors, we need anchors `a, b` with `p` and `r` on opposite arcs of `C`
from `a` to `b`. Density produces one anchor on each of the two open arcs of `C` from `p` to
`r`; the separation is then automatic, because an arc from `a` to `b` avoiding `p` and `r`
would be a connected subset of `C ∖ {p, r}` meeting both of its two (relatively open) halves. -/

/-! ### The hypotheses

Two predicates, one for each thing that is still being built. Both are *statements about one
curve*, so a consumer can discharge them curve by curve. -/

/-! ### Discharging `HasAnchorCrosscuts` from a skeleton homeomorphism

The two steps a consumer has to perform, isolated so that they need not be reinvented: the
image of a crosscut under the finite skeleton homeomorphism is again a crosscut, and the
agreement clause follows from agreement of the limit map with that homeomorphism on the
crosscut. Neither says anything about the square, so both apply to the source and the target
side of any of the stages. -/

/-! ### `lem:crosscut-side-correspondence` -/

/-- **The limit map carries `Int(C) ∖ P` onto `Q° ∖ P'`.** This is the whole use made of
`prop:skeleton-agreement`: it turns a homeomorphism of the interiors into a homeomorphism of
the cut interiors. -/
theorem image_inside_sdiff (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hP : IsCrosscut C P a b) (hP' : IsCrosscut modelCurve P' (u a) (u b))
    (hagree : F '' (P \ {a, b}) = P' \ {u a, u b}) :
    F '' (inside C \ P) = inside modelCurve \ P' := by
  have hFin : F '' inside C = inside modelCurve := by rw [hF.image_eq, inside_modelCurve]
  rw [inside_sdiff_crosscut hP, hF.injOn.image_sdiff_subset hP.sdiff_subset, hagree, hFin,
    ← inside_sdiff_crosscut hP']

/-- **`lem:crosscut-side-correspondence`, one inclusion.** The side of the crosscut whose
closure meets `C` in `A₁` is carried into the side of the target crosscut whose closure meets
`S` in `u(A₁)`.

This is where the spokes are used, and the only place. -/
theorem image_crosscut_side_subset (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜) (hspoke : HasSpokes C 𝒜 u F)
    (hcut : IsCutPair C a b A₁ A₂) (hP : IsCrosscut C P a b)
    (hP' : IsCrosscut modelCurve P' (u a) (u b)) (hagree : F '' (P \ {a, b}) = P' \ {u a, u b}) :
    F '' inside (A₁ ∪ P) ⊆ inside (u '' A₁ ∪ P') := by
  classical
  have hcut' : IsCutPair modelCurve (u a) (u b) (u '' A₁) (u '' A₂) :=
    hcut.image_of_isHomeoOn hu
  obtain ⟨hsrc1, hsrc2, -, -, -, -, -, -, hsrc9, hsrc10⟩ := crosscut_theorem hP hcut
  obtain ⟨htgt1, htgt2, -, -, -, -, -, -, htgt9, htgt10⟩ := crosscut_theorem hP' hcut'
  have hdiff := image_inside_sdiff hF hP hP' hagree
  -- the four sides, and their openness
  have hopenS : ∀ A : Set Plane, IsArcBetween A a b → IsOpen (inside (A ∪ P)) := fun A hA =>
    isOpen_inside (hA.isArc.isCompact.union hP.arc.isArc.isCompact).isClosed
  have hopenT : ∀ A : Set Plane, IsArcBetween A (u a) (u b) → IsOpen (inside (A ∪ P')) :=
    fun A hA => isOpen_inside (hA.isArc.isCompact.union hP'.arc.isArc.isCompact).isClosed
  have hS1 := hopenS A₁ hcut.fst
  have hS2 := hopenS A₂ hcut.snd
  have hT1 := hopenT _ hcut'.fst
  have hT2 := hopenT _ hcut'.snd
  -- the image of the first side is connected and lands in the union of the two target sides
  have hW1sub : inside (A₁ ∪ P) ⊆ inside C \ P := by rw [hsrc1]; exact subset_union_left
  have hconn : IsPreconnected (F '' inside (A₁ ∪ P)) := by
    refine IsPreconnected.image ?_ F (hF.continuousOn.mono fun z hz => (hW1sub hz).1)
    exact ((jordan_curve_theorem (hP.isJordanCurve_union hcut)).isConnected_inside).2
  have himsub : F '' inside (A₁ ∪ P) ⊆ inside (u '' A₁ ∪ P') ∪ inside (u '' A₂ ∪ P') := by
    rw [← htgt1, ← hdiff]
    exact image_mono hW1sub
  -- it therefore lands in one of the two; the spoke germ says which
  by_cases hmeet : (F '' inside (A₁ ∪ P) ∩ inside (u '' A₁ ∪ P')).Nonempty
  · exact hconn.subset_left_of_subset_union hT1 hT2 htgt2 himsub hmeet
  rw [not_nonempty_iff_eq_empty] at hmeet
  exfalso
  have hother : F '' inside (A₁ ∪ P) ⊆ inside (u '' A₂ ∪ P') := by
    intro w hw
    refine (himsub hw).resolve_left fun h' => ?_
    exact (eq_empty_iff_forall_notMem.1 hmeet w) ⟨hw, h'⟩
  -- an anchor in the relative interior of `A₁`
  obtain ⟨c, hc𝒜, hcA1, hcA2⟩ := exists_anchor_mem_arc hsub hdense hcut
  have hcC : c ∈ C := hsub hc𝒜
  have hca : c ≠ a := fun h => hcA2 (h ▸ hcut.snd.left_mem)
  have hcb : c ≠ b := fun h => hcA2 (h ▸ hcut.snd.right_mem)
  -- the anchor is off the crosscut, so a small ball around it misses the crosscut
  have hcP : c ∉ P := by
    intro h
    have : c ∈ ({a, b} : Set Plane) := by rw [← hP.inter_eq]; exact ⟨h, hcC⟩
    rcases this with h' | h'
    · exact hca h'
    · exact hcb h'
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 hP.arc.isArc.isClosed.isOpen_compl c hcP
  obtain ⟨J, hJin, hJconn, hJball, hJc, hJuc⟩ := hspoke c hc𝒜 ε hε
  have hJsub : J ⊆ inside C \ P := fun z hz => ⟨hJin hz, hball (hJball hz)⟩
  have hJcov : J ⊆ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by rw [← hsrc1]; exact hJsub
  -- the germ lies on the `A₁` side, because it clings to `c ∈ A₁ ∖ A₂`
  have hJ1 : J ⊆ inside (A₁ ∪ P) := by
    by_cases hJ1 : (J ∩ inside (A₁ ∪ P)).Nonempty
    · exact hJconn.subset_left_of_subset_union hS1 hS2 hsrc2 hJcov hJ1
    · rw [not_nonempty_iff_eq_empty] at hJ1
      have hJ2 : J ⊆ inside (A₂ ∪ P) := fun z hz =>
        (hJcov hz).resolve_left fun h' => (eq_empty_iff_forall_notMem.1 hJ1 z) ⟨hz, h'⟩
      have : c ∈ A₂ := by
        rw [← hsrc10]
        exact ⟨closure_mono hJ2 hJc, hcC⟩
      exact absurd this hcA2
  -- so its image lies on the `u(A₁)` side, contradicting `hother`
  have : u c ∈ u '' A₂ := by
    rw [← htgt10]
    refine ⟨closure_mono (subset_trans (image_mono hJ1) hother) hJuc, hu.mapsTo hcC⟩
  obtain ⟨w, hwA2, hw⟩ := this
  exact hcA2 (hu.injOn (hcut.snd_subset hwA2) hcC hw ▸ hwA2)

/-! ### `prop:boundary-continuity` -/

/-- **`prop:boundary-continuity`, the substance.** Approaching a point `p` of the curve from
inside, the limit map tends to `u p`.

The blueprint extracts a subsequence; the same argument runs on the filter
`l' = 𝓝[Int C] p ⊓ 𝓟 (F⁻¹ Wᶜ)` without extracting one. -/
theorem tendsto_nhdsWithin_inside (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) (hp : p ∈ C) :
    Tendsto F (𝓝[inside C] p) (𝓝 (u p)) := by
  classical
  by_contra hcon
  rw [Filter.tendsto_def] at hcon
  push Not at hcon
  obtain ⟨s, hs, hsnot⟩ := hcon
  obtain ⟨W, hWs, hWopen, hWmem⟩ := _root_.mem_nhds_iff.1 hs
  have hWnot : F ⁻¹' W ∉ 𝓝[inside C] p := fun h =>
    hsnot (mem_of_superset h (preimage_mono hWs))
  -- the filter of approach that stays away from `W`
  set l' : Filter Plane := 𝓝[inside C] p ⊓ 𝓟 (F ⁻¹' Wᶜ) with hl'
  haveI : l'.NeBot := by
    refine ⟨fun h => hWnot ?_⟩
    rw [hl', Filter.inf_principal_eq_bot] at h
    simpa using h
  have hl'in : inside C ∈ l' := mem_inf_of_left self_mem_nhdsWithin
  have hl'W : F ⁻¹' Wᶜ ∈ l' := mem_inf_of_right (mem_principal_self _)
  have hl'p : l' ≤ 𝓝 p := le_trans inf_le_left nhdsWithin_le_nhds
  -- compactness of the square gives a cluster point of the image
  have hmapK : map F l' ≤ 𝓟 (Plane.closedSquare 0 1) := by
    rw [le_principal_iff, mem_map]
    filter_upwards [hl'in] with z hz using Plane.openSquare_subset_closedSquare 0 1 (hF.mapsTo hz)
  obtain ⟨q, hqK, hqcl⟩ := (isCompact_closedSquare 0 1).exists_clusterPt hmapK
  have hqW : q ∈ Wᶜ := by
    have hle : map F l' ≤ 𝓟 Wᶜ := by rw [le_principal_iff]; exact hl'W
    have := mem_closure_iff_clusterPt.2 (hqcl.mono hle)
    rwa [hWopen.isClosed_compl.closure_eq] at this
  have hqne : q ≠ u p := fun h => hqW (h ▸ hWmem)
  -- the cluster point lies on the boundary of the square: otherwise the inverse map would
  -- send it back to `p`, which is not an interior point
  have hqcurve : q ∈ modelCurve := by
    by_contra hq
    have hqopen : q ∈ Plane.openSquare 0 1 := by
      rw [← closedSquare_sdiff_modelCurve]; exact ⟨hqK, hq⟩
    have hmapO : map F l' ≤ 𝓟 (Plane.openSquare 0 1) := by
      rw [le_principal_iff, mem_map]
      filter_upwards [hl'in] with z hz using hF.mapsTo hz
    set m : Filter Plane := 𝓝 q ⊓ map F l' with hm
    haveI : m.NeBot := hqcl
    have hm1 : m ≤ 𝓝[Plane.openSquare 0 1] q :=
      le_inf inf_le_left (le_trans inf_le_right hmapO)
    have h1 : Tendsto F' m (𝓝 (F' q)) := (hF.continuousOn_inv q hqopen).mono_left hm1
    have h2 : Tendsto F' m (𝓝 p) := by
      refine le_trans (map_mono (inf_le_right : m ≤ map F l')) ?_
      rw [Filter.map_map]
      have heq : (F' ∘ F) =ᶠ[l'] id := by
        filter_upwards [hl'in] with z hz using hF.invOn.1 hz
      rw [Filter.map_congr heq, Filter.map_id]
      exact hl'p
    have hpin : p ∈ inside C := tendsto_nhds_unique h1 h2 ▸ hF.mapsTo_inv hqopen
    exact inside_subset_compl hpin hp
  -- the boundary case: separate `p` from the preimage of `q` by two anchors
  have hrC : v q ∈ C := hu.mapsTo_inv hqcurve
  have hur : u (v q) = q := hu.invOn.2 hqcurve
  have hpr : p ≠ v q := fun h => hqne (by rw [← hur, ← h])
  obtain ⟨a, ha𝒜, b, hb𝒜, A₁, A₂, hab, hcut, hpA1, hpA2, hrA2, hrA1⟩ :=
    exists_separating_anchors hC hsub hdense hp hrC hpr
  obtain ⟨P, P', hP, hP', hagree⟩ := hcross ha𝒜 hb𝒜 hab
  have hcut' : IsCutPair modelCurve (u a) (u b) (u '' A₁) (u '' A₂) :=
    hcut.image_of_isHomeoOn hu
  have hside := image_crosscut_side_subset hu hF hsub hdense hspoke hcut hP hP' hagree
  obtain ⟨hsrc1, -, -, -, -, -, -, -, -, hsrc10⟩ := crosscut_theorem hP hcut
  obtain ⟨-, -, -, -, -, -, -, -, htgt9, -⟩ := crosscut_theorem hP' hcut'
  -- `p` is off the crosscut and off the closure of the far side
  have hpa : p ≠ a := fun h => hpA2 (h ▸ hcut.snd.left_mem)
  have hpb : p ≠ b := fun h => hpA2 (h ▸ hcut.snd.right_mem)
  have hpP : p ∉ P := by
    intro h
    have : p ∈ ({a, b} : Set Plane) := by rw [← hP.inter_eq]; exact ⟨h, hp⟩
    rcases this with h' | h'
    · exact hpa h'
    · exact hpb h'
  have hpfar : p ∉ closure (inside (A₂ ∪ P)) := fun h => hpA2 (hsrc10 ▸ ⟨h, hp⟩)
  -- hence every nearby point of the domain is on the `p` side
  have hV : IsOpen (Pᶜ ∩ (closure (inside (A₂ ∪ P)))ᶜ) :=
    hP.arc.isArc.isClosed.isOpen_compl.inter isClosed_closure.isOpen_compl
  have hnear : inside (A₁ ∪ P) ∈ 𝓝[inside C] p := by
    refine mem_nhdsWithin.2 ⟨_, hV, ⟨hpP, hpfar⟩, ?_⟩
    rintro z ⟨⟨hz1, hz2⟩, hzin⟩
    have : z ∈ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by rw [← hsrc1]; exact ⟨hzin, hz1⟩
    exact this.resolve_right fun h' => hz2 (subset_closure h')
  -- so the cluster point sits in the closure of the corresponding target side
  have hmapW : map F l' ≤ 𝓟 (inside (u '' A₁ ∪ P')) := by
    rw [le_principal_iff, mem_map]
    filter_upwards [mem_inf_of_left hnear] with z hz using hside ⟨z, hz, rfl⟩
  have hqclos : q ∈ closure (inside (u '' A₁ ∪ P')) :=
    mem_closure_iff_clusterPt.2 (hqcl.mono hmapW)
  have hqA1 : q ∈ u '' A₁ := by rw [← htgt9]; exact ⟨hqclos, hqcurve⟩
  obtain ⟨w, hwA1, hw⟩ := hqA1
  have : v q = w := by
    rw [← hw, hu.invOn.1 (hcut.fst_subset hwA1)]
  exact hrA1 (this ▸ hwA1)

/-- **`prop:boundary-continuity`.** The glued map is continuous on the closed Jordan domain. -/
theorem boundary_continuity (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) :
    ContinuousOn (extendByBoundary C u F) (C ∪ inside C) := by
  have heqC : EqOn (extendByBoundary C u F) u C := fun _ hz => extendByBoundary_of_mem hz
  have heqD : EqOn (extendByBoundary C u F) F (inside C) := fun _ hz =>
    extendByBoundary_of_notMem (inside_subset_compl hz)
  intro z hz
  rcases hz with hzC | hzin
  · -- at a point of the curve: split the approach into the boundary part and the inner part
    rw [ContinuousWithinAt, extendByBoundary_of_mem hzC, nhdsWithin_union, Filter.tendsto_sup]
    constructor
    · exact Tendsto.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqC).symm
        (hu.continuousOn z hzC)
    · exact Tendsto.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqD).symm
        (tendsto_nhdsWithin_inside hC hu hF hsub hdense hcross hspoke hzC)
  · -- at an interior point the map is `F` on a neighbourhood
    have hopen : IsOpen (inside C) := isOpen_inside hC.isClosed
    have hmem : inside C ∈ 𝓝 z := hopen.mem_nhds hzin
    have hFat : ContinuousAt F z := hF.continuousOn.continuousAt hmem
    exact (hFat.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hmem heqD)).continuousWithinAt

/-! ### `thm:square-extension` -/

/-- **`thm:square-extension`, for one curve.** The glued map restricts to a homeomorphism of the
closed Jordan domain onto the closed square, and extends `u`.

Continuity of the inverse is not proved directly: the domain is compact and the square is
Hausdorff, so the continuous bijection `F̄` is a closed map, which is exactly what
`continuousOn_iff_isClosed` asks of the inverse. -/
theorem isHomeoOn_extendByBoundary (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) :
    IsHomeoOn (extendByBoundary C u F) (extendByBoundary modelCurve v F')
      (C ∪ inside C) (Plane.closedSquare 0 1) := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  have hcont : ContinuousOn (extendByBoundary C u F) (C ∪ inside C) :=
    boundary_continuity hC hu hF hsub hdense hcross hspoke
  have hK : IsCompact (C ∪ inside C) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_union_inside hsep)
      (hC.isCompact.isBounded.union hsep.isBounded_inside)
  -- the two `MapsTo` clauses
  have hmaps : MapsTo (extendByBoundary C u F) (C ∪ inside C) (Plane.closedSquare 0 1) := by
    rintro z (hz | hz)
    · rw [extendByBoundary_of_mem hz]
      exact modelCurve_subset_closedSquare (hu.mapsTo hz)
    · rw [extendByBoundary_of_notMem (inside_subset_compl hz)]
      exact Plane.openSquare_subset_closedSquare 0 1 (hF.mapsTo hz)
  have hmaps' : MapsTo (extendByBoundary modelCurve v F') (Plane.closedSquare 0 1)
      (C ∪ inside C) := by
    intro w hw
    by_cases hwc : w ∈ modelCurve
    · rw [extendByBoundary_of_mem hwc]
      exact Or.inl (hu.mapsTo_inv hwc)
    · have hwo : w ∈ Plane.openSquare 0 1 := by
        rw [← closedSquare_sdiff_modelCurve]; exact ⟨hw, hwc⟩
      rw [extendByBoundary_of_notMem hwc]
      exact Or.inr (hF.mapsTo_inv hwo)
  -- the two inverse laws
  have hleft : LeftInvOn (extendByBoundary modelCurve v F') (extendByBoundary C u F)
      (C ∪ inside C) := by
    rintro z (hz | hz)
    · rw [extendByBoundary_of_mem hz, extendByBoundary_of_mem (hu.mapsTo hz)]
      exact hu.invOn.1 hz
    · have hFz : F z ∈ Plane.openSquare 0 1 := hF.mapsTo hz
      have : F z ∉ modelCurve := by
        rw [← inside_modelCurve] at hFz
        exact inside_subset_compl hFz
      rw [extendByBoundary_of_notMem (inside_subset_compl hz),
        extendByBoundary_of_notMem this]
      exact hF.invOn.1 hz
  have hright : RightInvOn (extendByBoundary modelCurve v F') (extendByBoundary C u F)
      (Plane.closedSquare 0 1) := by
    intro w hw
    by_cases hwc : w ∈ modelCurve
    · rw [extendByBoundary_of_mem hwc, extendByBoundary_of_mem (hu.mapsTo_inv hwc)]
      exact hu.invOn.2 hwc
    · have hwo : w ∈ Plane.openSquare 0 1 := by
        rw [← closedSquare_sdiff_modelCurve]; exact ⟨hw, hwc⟩
      have : F' w ∉ C := inside_subset_compl (hF.mapsTo_inv hwo)
      rw [extendByBoundary_of_notMem hwc, extendByBoundary_of_notMem this]
      exact hF.invOn.2 hwo
  -- continuity of the inverse, by compactness
  refine ⟨hmaps, hmaps', hcont, ?_, hleft, hright⟩
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨extendByBoundary C u F '' (t ∩ (C ∪ inside C)), ?_, ?_⟩
  · exact ((hK.inter_left ht).image_of_continuousOn
      (hcont.mono inter_subset_right)).isClosed
  · ext w
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hwt, hw⟩
      exact ⟨⟨_, ⟨hwt, hmaps' hw⟩, hright hw⟩, hw⟩
    · rintro ⟨⟨z, ⟨hzt, hzK⟩, rfl⟩, hw⟩
      exact ⟨by rw [hleft hzK]; exact hzt, hw⟩

/-! ### The assembled hypothesis, and `Schoenflies.SquareExtension` -/

/-- **`thm:square-extension`.** Every homeomorphism of a Jordan curve onto the model square
boundary extends to a homeomorphism of the closed Jordan domain onto the closed square. -/
theorem squareExtension_of_hasLimitHomeomorphism (h : HasLimitHomeomorphism) :
    SquareExtension := by
  intro C u v hC hu
  obtain ⟨𝒜, F, F', hsub, hdense, hF, hcross, hspoke⟩ := h C u v hC hu
  exact ⟨extendByBoundary C u F, extendByBoundary modelCurve v F',
    isHomeoOn_extendByBoundary hC hu hF hsub hdense hcross hspoke,
    fun _ hz => extendByBoundary_of_mem hz⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialGenerated
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Stage 0: the initial pair as a `GeneratedPair`

`Schoenflies/FiniteTransfer.lean` defines `Schoenflies.GeneratedPair`, the object every stage of
the Schönflies recursion is and that `thm:finite-transfer` consumes and produces. Nothing built
one. This module builds the first: the initial matched pair of `prop:initial-pair`, which is
generated from itself by the empty sequence of elementary operations.

## What has to be shown

The two realizations, the skeleton homeomorphism and weak admissibility are all in
`Schoenflies/InitialPair.lean` and `Schoenflies/InitialPairFixed.lean` already, or one step from
what is there. The work is the two `IsCellDecomposition` fields — assertion (i) of
`lem:cellulation-invariants` — and they are the same work twice, because both realizations have
the same shape: a `HexData` whose six outer arcs form a Jordan curve and whose chord is a
crosscut of it. So assertion (i) is proved **once**, for an arbitrary `HexData` carrying that
crosscut configuration (`Schoenflies.HexData.isCellDecomposition`), and instantiated on each
side. The same is true of weak admissibility (`Schoenflies.HexData.isWeaklyAdmissible`).

The four clauses go as follows.

* `nonempty` — the seven 0-cells are points; the seven open 1-cells are arcs minus their two
  endpoints (`IsArcBetween.nonempty_diff`); the two 2-cells are the two sides of the crosscut,
  nonempty by `thm:general-crosscut`.
* `disjoint` — fifteen cells, but only five kinds of pair. Two vertices are distinct points;
  a vertex misses every open edge it is not an end of (`HexData.mem_outer_iff`,
  `.mem_chord_iff`), and is an end of the ones it does meet; two open edges are disjoint by the
  two meeting conditions of `HexData`; every 1- or 0-cell lies on the skeleton and every 2-cell
  is inside the curve and off the crosscut; and the two 2-cells are the two sides of one
  crosscut.
* `iUnion_eq` — the 0-cells and open 1-cells reassemble the skeleton `C ∪ P`
  (`HexData.iUnion_cellSet`), and the two 2-cells exhaust `D ∖ P`
  (`thm:general-crosscut`), so together they are `C ∪ D`.
* `closure_eq` — a finite case check against `Schoenflies.initSub`, the base value of `≼_abs`
  that the blueprint fixes. The four `initSub_iff_*` lemmas below read it off, and then the only
  topology needed is `closure (A ∖ {p, q}) = A` for an arc (`IsArcBetween.closure_diff`) and the
  closure of a crosscut side (`Schoenflies.crosscut_cell_partition`).

## The input is `InitialData`, not `AnchoredInitialData`

`AnchoredInitialData` adds exactly two fields, `a ∈ 𝒜` and `b ∈ 𝒜`. Nothing in `GeneratedPair`
mentions the anchor set: the anchoring is what lets a *later* stage run a fresh crosscut into `a`
or `b`, and it is read off `AnchoredInitialData.stronglyAccessible_a` at that point. So the pair
is built from `InitialData` — the weaker input — and
`Schoenflies.AnchoredInitialData.generatedPair` is the one-line specialisation for a consumer
holding the anchored form.

## Blueprint

* `Schoenflies.combInvariants_initialStructure` — `lem:cellulation-invariants` (iii), (v), (vi)
  and abstract (viii) for the base structure: the base case of
  `Schoenflies.GeneratedStructure.combInvariants`, which the whole recursion needs.
* `Schoenflies.initSub_iff_vert`, `.._edge`, `.._chord`, `.._face` — the base value of `≼_abs`
  (tex 1590–1602) read as "the subcells of each cell are exactly these".
* `Schoenflies.HexData.isCellDecomposition` — `lem:cellulation-invariants`(i) for either
  realization of `prop:initial-pair`, with `HexData.iUnion_cellSet`,
  `HexData.biUnion_of_three_edges` and `HexData.biUnion_faceCells` as its two reassembly steps.
* `Schoenflies.HexData.isWeaklyAdmissible` — `def:admissible-graph` minus the connectedness
  clause, for either realization.
* `Schoenflies.InitialData.generatedPair`, `Schoenflies.AnchoredInitialData.generatedPair` —
  `def:generated-structure` at stage 0: `prop:initial-pair` is a generated matched cellulation.
* `Schoenflies.HexData.isOpen_cellSet_face`,
  `Schoenflies.InitialData.isOpen_sourceRealization_cell_face`,
  `.isOpen_targetRealization_cell_face` — openness of the two 2-cells: the hypothesis
  `lem:cellulation-invariants`(viii) takes and `IsCellDecomposition` does not record.
* `Schoenflies.infinite_initialCell` — the base case meets the recursion: `thm:finite-transfer`
  needs `[Infinite γ]`, and `InitialCell` supplies it through its spare constructor `aux`.
* `Schoenflies.modelCurve_union_inside` — `S ∪ Int(S) = Q`, the closed target domain.
* `Schoenflies.InitialData.generatedPair_src_isAdmissible`, `.generatedPair_tgt_isAdmissible` —
  the *strong* form of
  `def:admissible-graph` on both sides, which the initial pair does satisfy
  (`rem:intermediate-disconnection` waives it only at intermediate stages).
* `Schoenflies.IsArcBetween.closure_diff` — general; belongs in `Schoenflies/Subarc.lean`.
-/

open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

open _root_.Graph

/-! ### An arc is the closure of its interior

General, and stated nowhere on `main`: `Schoenflies/Subarc.lean` has the two endpoint lemmas and
`IsArcBetween.isConnected_diff`, but not the closure identity itself. The integrator should hoist
this next to `IsArcBetween.right_mem_closure_diff`. -/

/-! ### The cells of the initial structure, and `≼_abs`

`initialStructure` declares every one of `InitialCell`'s four *named* constructors a cell. The
fifth, `InitialCell.aux`, is the spare supply of fresh names that `def:generated-structure`
needs and that `thm:finite-transfer` asks for as `[Infinite γ]`; no `aux` name is a cell.

`recOnCells` is the shape every clause of assertion (i) below uses: case analysis on a *cell*,
with the spare names ruled out by the membership hypothesis the clause already carries. -/

/-! ### The combinatorial invariants at the base

`Schoenflies.GeneratedStructure.combInvariants` propagates `lem:cellulation-invariants` (iii),
(v), (vi) and abstract (viii) along the two elementary operations *given the base case*. This is
the base case. Assertion (vi) is `Schoenflies.outerEdgeUniqueFace_initialStructure`, already on
`main`; the other seven clauses are read off `initSub`. -/

/-! ### The open cells of a `HexData`

Everything assertion (i) needs about the fifteen realized open cells, stated for an arbitrary
`HexData` so that the source and the target realization are served by one proof. Nothing in this
section mentions the crosscut configuration; that enters only for the two 2-cells. -/

/-! ### The closed square, as a domain

`GeneratedPair` asks for the *closed* target domain. `Schoenflies.inside_modelCurve` identifies
the Jordan domain of `S` with the open square, so the closed domain `S ∪ Int(S)` is literally
`Q = [-1,1]²`. -/

/-! ### The initial pair is a `GeneratedPair`

Both realizations are instances of the two `HexData` theorems above; all that is left is to
present the hypotheses in the shape they take, which on the source side means rewriting
`d.src.outerArcs` to `C` and on the target side `d.tgt.outerArcs` to `S`. -/

/-- **Stage 0 from the anchored initial pair.** `AnchoredInitialData` adds only the clause
`a, b ∈ 𝒜`, which no field of `GeneratedPair` mentions; it is what lets a later stage run a fresh
crosscut into `a` or `b` (`AnchoredInitialData.stronglyAccessible_a`). So the pair is built from
the underlying `InitialData`, and this is the specialisation for a consumer holding the anchored
form. -/
noncomputable def AnchoredInitialData.generatedPair {C : Set Plane} {A : AnchorSet C}
    (D : AnchoredInitialData C A) :
    GeneratedPair initialStructure C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  D.toInitialData.generatedPair

/-! ### The base case meets the recursion

`Schoenflies.finite_transfer_toward_square` and `Schoenflies.EarStep` carry `[Infinite γ]`, and
`FiniteTransfer.lean` argues that without it `EarStep` is *false*: an ear insertion consumes
fresh cell names for the ear's interior vertices, its edges and the two 2-cells the split
creates, so a naming type that the current stage has exhausted refutes it.

The initial structure names fifteen cells. `InitialCell` therefore carries a fifth constructor,
`InitialCell.aux : ℕ → InitialCell`, which is the spare supply and nothing else: no `aux` name is
a cell, every `aux` name has empty open cell, and `initSub` relates none of them — the reflexive
clause of `≼_abs` is restricted to `Schoenflies.cellNames` precisely so that
`CombInvariants.sub_mem_left` and `.sub_mem_right`, which say that `≼_abs` relates cells to
cells, stay true.

The alternative was a relabelling of a `CellStructure` and both of its realizations along an
injection `InitialCell ↪ γ` into an infinite naming type. That is several hundred lines and buys
nothing the spare constructor does not, since the base of `GeneratedStructure` is a parameter and
stage 0 uses only the `base` constructor — no inductive derivation has to be transported. -/

instance instInfiniteInitialCell : Infinite InitialCell :=
  Infinite.of_injective InitialCell.aux fun _ _ h => by injection h

/-! ### The interface, exercised

A machine-checked statement that stage 0 delivers exactly what `thm:finite-transfer` reads off a
`GeneratedPair`: the abstract structure carries the combinatorial invariants, the source and
target realizations are cell decompositions of the two closed domains, and both are admissible in
the strong sense. Nothing below mentions how the pair was built. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.CommonSubdivision
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Common subdivision for finite transfer

This module proves step 1 of finite transfer.  The part of the extension graph supported on the
old source skeleton is extracted as a trace graph.  It is a subdivision of the old skeleton and
remains 2-connected.  Its finitely many vertices are then inserted, one at a time, into both
realizations of the generated pair.  `CellStructure.SubdivData.realizeHomeo` transports every
source subdivision parameter to the matching target edge.

The resulting theorem `Schoenflies.commonSubdivision` discharges the former
`Schoenflies.CommonSubdivision` interface under the same infinite name-supply assumption used by
the ear construction.

## Blueprint

* `Schoenflies.commonSubdivision` — the common-subdivision part of step 1 in the proof of
  `thm:finite-transfer`(a).
* `Schoenflies.finite_transfer_toward_square` — `thm:finite-transfer`(a).
* `Schoenflies.IsPlaneSubdivisionExtension.trace_isTwoConnected` — the trace theorem for two
  arbitrary plane drawings, used when assembling target/mesh overlays.
-/

open Set
open scoped Graph

namespace Schoenflies

namespace GeneratedPair

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- The output of inserting one target skeleton point into a matched generated pair. -/
structure SubdivideTargetAtData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (p : Plane) where
  /-- The pair after the possible subdivision. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The new-to-old cell parent map. -/
  parent : γ → γ
  /-- Source refinement along `parent`. -/
  refines_src : pair.src.Refines P.src parent
  /-- Target refinement along the same `parent`. -/
  refines_tgt : pair.tgt.Refines P.tgt parent
  /-- The occupied source skeleton is unchanged. -/
  sourceSkeletonSet_eq : pair.src.skeletonSet = P.src.skeletonSet
  /-- The occupied target skeleton is unchanged. -/
  skeletonSet_eq : pair.tgt.skeletonSet = P.tgt.skeletonSet
  /-- The transported skeleton map agrees with the old one. -/
  homeo_eqOn : Set.EqOn pair.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The requested point and every old vertex are target vertices of the new pair. -/
  vertexSet_eq : V(pair.tgt.graph) = insert p V(P.tgt.graph)

/-- Every target skeleton point can be made a vertex by one matched subdivision. -/
theorem exists_subdivideTargetAtData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {p : Plane}
    (hp : p ∈ P.tgt.skeletonSet) : Nonempty (SubdivideTargetAtData P p) := by
  let q := P.homeo.invFun p
  have hq : q ∈ P.src.skeletonSet := by
    rw [← P.homeo.symm.image_skeletonSet]
    exact ⟨p, hp, rfl⟩
  obtain ⟨w⟩ := exists_subdivideAtData P hq
  exact ⟨{
    pair := w.pair
    parent := w.parent
    refines_src := w.refines_src
    refines_tgt := w.refines_tgt
    sourceSkeletonSet_eq := w.skeletonSet_eq
    skeletonSet_eq := w.targetSkeletonSet_eq
    homeo_eqOn := w.homeo_eqOn
    vertexSet_eq := by
      rw [w.targetVertexSet_eq, P.homeo.rightInvOn hp]
  }⟩

/-- The output of inserting a finite set of target skeleton points. -/
structure SubdivideTargetSetData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (s : Set Plane) where
  /-- The pair after all subdivisions. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite new-to-old cell parent map. -/
  parent : γ → γ
  /-- Source refinement along `parent`. -/
  refines_src : pair.src.Refines P.src parent
  /-- Target refinement along the same `parent`. -/
  refines_tgt : pair.tgt.Refines P.tgt parent
  /-- The occupied source skeleton is unchanged. -/
  sourceSkeletonSet_eq : pair.src.skeletonSet = P.src.skeletonSet
  /-- The occupied target skeleton is unchanged. -/
  skeletonSet_eq : pair.tgt.skeletonSet = P.tgt.skeletonSet
  /-- The final skeleton map agrees with the original one on the original source skeleton. -/
  homeo_eqOn : Set.EqOn pair.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- Every requested point is a vertex of the final target graph. -/
  vertexSet_subset : s ⊆ V(pair.tgt.graph)

/-- Every finite set of target skeleton points can simultaneously be made vertices. -/
theorem exists_subdivideTargetSetData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {s : Set Plane}
    (hs : s.Finite) (hsub : s ⊆ P.tgt.skeletonSet) :
    Nonempty (SubdivideTargetSetData P s) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      exact ⟨{
        pair := P
        parent := id
        refines_src := CellStructure.Realization.Refines.refl P.src
        refines_tgt := CellStructure.Realization.Refines.refl P.tgt
        sourceSkeletonSet_eq := rfl
        skeletonSet_eq := rfl
        homeo_eqOn := fun _ _ => rfl
        vertexSet_subset := Set.empty_subset _
      }⟩
  | @insert a s ha hs ih =>
      have hskeleton : s ⊆ P.tgt.skeletonSet := fun x hx =>
        hsub (Set.mem_insert_of_mem a hx)
      obtain ⟨w⟩ := ih hskeleton
      have haSkeleton : a ∈ w.pair.tgt.skeletonSet := by
        rw [w.skeletonSet_eq]
        exact hsub (Set.mem_insert a s)
      obtain ⟨q⟩ := exists_subdivideTargetAtData w.pair haSkeleton
      exact ⟨{
        pair := q.pair
        parent := w.parent ∘ q.parent
        refines_src := q.refines_src.trans w.refines_src
        refines_tgt := q.refines_tgt.trans w.refines_tgt
        sourceSkeletonSet_eq := q.sourceSkeletonSet_eq.trans w.sourceSkeletonSet_eq
        skeletonSet_eq := q.skeletonSet_eq.trans w.skeletonSet_eq
        homeo_eqOn := by
          intro x hx
          calc
            q.pair.homeo.toFun x = w.pair.homeo.toFun x :=
              q.homeo_eqOn (by rwa [w.sourceSkeletonSet_eq])
            _ = P.homeo.toFun x := w.homeo_eqOn hx
        vertexSet_subset := by
          intro x hx
          rw [q.vertexSet_eq]
          rcases hx with rfl | hx
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (w.vertexSet_subset hx)
      }⟩

end GeneratedPair

end Schoenflies
end

section
-- module Solutions.Q146_CD.FiniteTransferTarget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.attachUnion_succ _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.StageSequence.limitTower_region _root_.Schoenflies.StageSequence.limitTower_region' _root_.Schoenflies.TargetSegmentCover.mem_openTargetEdgePieces _root_.Schoenflies.TargetSegmentCover.mem_squareMeshPieces _root_.Schoenflies.attachGraph_pointSet _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.mem_currentOverlayPieces _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite transfer, direction (b): toward the Jordan domain

Direction (b) starts with an extension of the **target** realization and reproduces it on the
source side.  This module begins its construction with the target analogue of the common
subdivision from direction (a).  The graph-theoretic extension assumptions are exactly
`Schoenflies.IsSourceExtension`, applied to `P.tgt`: only the side on which the realization lives
changes.

The trace of the target extension supported on the old target skeleton is 2-connected.  Its
finitely many vertices are inserted by `GeneratedPair.exists_subdivideTargetSetData`; each target
point is transported backwards through the skeleton homeomorphism, and the resulting source
parameter is then carried forward by `SubdivData.realizeHomeo`.  Thus the same subdivision is
made on both sides and both refinement maps share one parent map.

The reverse ear bookkeeping is also completed here.  The ambient target path is injectively
renamed, realized as a target crosscut, and then matched to a polygonal source crosscut by
reversing `EarHomeo`.  Off the wild curve, endpoint accessibility is derived from
polygonal-side accessibility.  At a fresh anchor, this module constructs the compact carrier of
closed nonboundary edges and discharges compactness, cell absorption, and coverage before
applying `Schoenflies.polyAccessible_of_stronglyAccessible_in`.  `TargetBoundaryAnchored` and
the compatibility of the evolving skeleton map now supply strong accessibility automatically.
Consequently the only remaining input is `TargetEarFreshCombinatorics`: the prescribed ear
order must say that a wild-boundary endpoint is absent from the current nonboundary carrier and
incident with one unique current source face.

## Blueprint

* `Schoenflies.IsTargetPartialTransferOf`, `Schoenflies.TargetCommonSubdivision` — the
  target-to-source analogues of the direction-(a) transfer interfaces.
* `Schoenflies.targetCommonSubdivision` — step 1 of `thm:finite-transfer`(b).
* `Schoenflies.TargetEarStepData`, `Schoenflies.exists_targetSideEarStepData` — the complete
  target-path relabelling and split data for one reverse ear.
* `Schoenflies.TargetEarEndpointAccessibility`,
  `Schoenflies.targetEarStep_of_endpointAccessibility` — the reverse ear construction reduced
  to its exact source-side geometric invariant.
* `Schoenflies.GeneratedPair.sourceNonboundaryGraph`,
  `Schoenflies.GeneratedPair.source_polyAccessible_of_fresh` — the compact source carrier and
  the fresh-anchor accessibility theorem with all cellulation hypotheses discharged.
* `Schoenflies.TargetBoundaryAnchored`, `Schoenflies.TargetEarFreshCombinatorics`,
  `Schoenflies.targetEarFreshInvariant_of_boundaryAnchored` — the fixed anchor geometry split
  cleanly from the remaining prescribed-ear combinatorics.
* `Schoenflies.targetTransferOfEars`,
  `Schoenflies.finite_transfer_toward_source_of_freshInvariant` — the relative-ear induction
  and direction-(b) theorem assuming only that combinatorial invariant.
-/

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- The evolving target skeleton contains the original target skeleton.  This is transported
from the corresponding source inclusion through the two compatible skeleton homeomorphisms. -/
theorem IsTargetPartialTransferOf.targetSkeletonSet_subset
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (hT : IsTargetPartialTransferOf T P B Hdraw par) :
    P.tgt.skeletonSet ⊆ T.tgt.skeletonSet := by
  intro y hy
  rw [← P.homeo.image_skeletonSet] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxT : x ∈ T.src.skeletonSet := hT.sourceSkeletonSet_subset hx
  have himage : T.homeo.toFun x ∈ T.tgt.skeletonSet := by
    rw [← T.homeo.image_skeletonSet]
    exact Set.mem_image_of_mem T.homeo.toFun hxT
  rwa [hT.homeo_eqOn hx] at himage

/-- A current abstract vertex lying over the original target skeleton has the original source
preimage.  This is the pointwise compatibility needed to recognize prescribed source anchors
after any number of reverse-ear insertions. -/
theorem IsTargetPartialTransferOf.source_pos_eq_invFun_target_pos
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (hT : IsTargetPartialTransferOf T P B Hdraw par) {v : γ}
    (hv : v ∈ V(T.str.skel)) (hvP : T.tgt.pos v ∈ P.tgt.skeletonSet) :
    T.src.pos v = P.homeo.invFun (T.tgt.pos v) := by
  have hinvP : P.homeo.invFun (T.tgt.pos v) ∈ P.src.skeletonSet := by
    rw [← P.homeo.symm.image_skeletonSet]
    exact ⟨T.tgt.pos v, hvP, rfl⟩
  apply T.homeo.injOn
  · exact T.src.pos_mem_skeletonSet hv
  · exact hT.sourceSkeletonSet_subset hinvP
  · rw [T.homeo.pos_apply hv, hT.homeo_eqOn hinvP,
      P.homeo.rightInvOn hvP]

/-- Step 1 of direction (b), as the interface consumed by its relative-ear induction. -/
def TargetCommonSubdivision
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
      (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsTargetPartialTransferOf T₀ P K Hdraw par₀

/-- One target ear insertion, expressed as the step consumed by relative-ear induction. -/
def TargetEarStep [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par' : γ → γ),
        IsTargetPartialTransferOf T' P (B.union (H.pathGraphOf a D)) Hdraw par'

namespace TargetEarStepData

variable {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {a : Plane} {D : List γ}

/-- The assembled pair realizes the enlarged target subgraph and refines the original pair. -/
theorem isTargetPartialTransferOf_pair
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {b : Plane}
    {par : γ → γ} (w : TargetEarStepData T B H Hdraw a D)
    (hdraw : H.IsDrawing Hdraw) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (hT : IsTargetPartialTransferOf T P B Hdraw par) :
    IsTargetPartialTransferOf w.pair P (B.union (H.pathGraphOf a D)) Hdraw
      (par ∘ w.splitData.parent) where
  refines_src :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.srcCrosscut
      T.str_combInvariants T.src_isCellDecomposition T.src_isFaceJordan).2.2).trans
      hT.refines_src
  refines_tgt :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.tgtCrosscut
      T.str_combInvariants T.tgt_isCellDecomposition T.tgt_isFaceJordan).2.2).trans
      hT.refines_tgt
  sourceSkeletonSet_subset :=
    hT.sourceSkeletonSet_subset.trans
      (w.splitData.skeletonSet_subset_realize w.srcCrosscut)
  homeo_eqOn := by
    intro x hx
    calc
      w.pair.homeo.toFun x = T.homeo.toFun x :=
        w.splitData.splitHomeo_eqOn
          (g := T.homeo) (hE₁ := w.srcCrosscut) (hE₂ := w.tgtCrosscut)
          (m := w.earHomeo) (hT.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := hT.homeo_eqOn hx
  skeletonSet_eq := by
    change (w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut).skeletonSet = _
    rw [w.splitData.skeletonSet_realize, hT.skeletonSet_eq, w.tgtEarSet_eq,
      Graph.pointSet_union, hdraw.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)]
  vertexSet_subset := by
    change V(B.union (H.pathGraphOf a D)) ⊆
      V((w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut).graph)
    exact w.vertexSet_subset

end TargetEarStepData

/-- The nontrivial reverse-ear constructor, before the already-present-edge branch is folded
back in. -/
def TargetEarStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (_hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      Nonempty (TargetEarStepData T B H Hdraw a D)

/-- Fold the explicit nontrivial reverse-ear constructor into the total `TargetEarStep`
interface. -/
theorem targetEarStep_of_data [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hbuild : TargetEarStepConstruction P H Hdraw hH) :
    TargetEarStep P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint T par hT
  rcases Graph.ear_edges_notMem_or_union_eq hBH hpath hab haB hbB hint with hnew | hsame
  · obtain ⟨w⟩ := hbuild B a b D hB hBH hpath hab haB hbB hint hnew T par hT
    exact ⟨w.pair, par ∘ w.splitData.parent,
      w.isTargetPartialTransferOf_pair hH.isDrawing hpath hab hT⟩
  · refine ⟨T, par, ?_⟩
    rw [hsame]
    exact hT

/-! ### Locating and realizing the target half of a reverse ear -/

/-- A nontrivial target ear lies in one current target face and determines its two abstract
endpoint vertices. -/
theorem exists_target_face_of_ear
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {par : γ → γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    (hT : IsTargetPartialTransferOf T P B Hdraw par) :
    ∃ u v F, u ∈ V(T.str.skel) ∧ v ∈ V(T.str.skel) ∧ u ≠ v ∧
      T.tgt.pos u = a ∧ T.tgt.pos v = b ∧ F ∈ T.str.faces ∧
      Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell F ∧
      T.str.sub u F ∧ T.str.sub v F := by
  have haT := hT.vertexSet_subset haB
  have hbT := hT.vertexSet_subset hbB
  rw [CellStructure.Realization.vertexSet_graph] at haT hbT
  obtain ⟨u, hu, hua⟩ := haT
  obtain ⟨v, hv, hvb⟩ := hbT
  have huv : u ≠ v := by
    intro huv
    apply hab
    rw [← hua, ← hvb, huv]
  have harc : IsArcBetween (Graph.edgesCover Hdraw D) a b :=
    hH.isDrawing.path_isArcBetween hpath (hpath.ne_nil hab)
  let N := Graph.edgesCover Hdraw D \ {a, b}
  have hNconn : IsPreconnected N := harc.isConnected_diff.isPreconnected
  have hNne : N.Nonempty := harc.isConnected_diff.nonempty
  have hND : N ⊆ tgtDom := by
    intro x hx
    exact hH.pointSet_subset
      (Graph.edgesCover_subset_pointSet (fun g hg => hpath.edge_mem hg) hx.1)
  have hNdisj : Disjoint N T.tgt.skeletonSet := by
    rw [hT.skeletonSet_eq]
    refine Set.disjoint_left.2 fun x hx hxB ↦ hx.2 ?_
    exact hH.isDrawing.edgesCover_inter_pointSet hBH hpath hint hnew ⟨hx.1, hxB⟩
  obtain ⟨F, hF, hNF, huF, hvF, -⟩ :=
    T.tgt_isCellDecomposition.exists_face_of_ear
      (T.tgt_isCellDecomposition.cellsAbsorb T.tgt_isFaceJordan)
      hNconn hNne hND hNdisj hu hv
      (hua ▸ harc.left_mem_closure_diff) (hvb ▸ harc.right_mem_closure_diff)
  exact ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hNF, huF, hvF⟩

/-- No edge of a genuine target ear is contained in the outer curve.  Such an edge would lie
simultaneously in the old target skeleton and in the open current face. -/
theorem target_ear_edge_not_outer
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {F : γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hpath : H.IsPath a D b) (hF : F ∈ T.str.faces)
    (hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell F) :
    ∀ e ∈ D, ¬ Graph.edgeArc Hdraw e ⊆ tgtOuter := by
  intro e he houter
  have houterSkel : tgtOuter ⊆ T.tgt.skeletonSet := by
    intro z hz
    apply T.tgt.outerSet_subset_skeletonSet
    rw [T.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hz
  have harcPair : edgeArc Hdraw e ⊆ ({a, b} : Set Plane) := by
    intro z hz
    by_contra hzpair
    have hzCell : z ∈ T.tgt.cell F :=
      hinside ⟨Graph.mem_edgesCover he hz, hzpair⟩
    have hzSkel : z ∈ T.tgt.skeletonSet := houterSkel (houter hz)
    exact Set.disjoint_left.1
      (T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition hF) hzCell hzSkel
  obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet (hpath.edge_mem he)
  have harc := hH.isDrawing.edge_isArcBetween hxy
  have hxyne := hH.isDrawing.ne_of_isLink hxy
  rcases harcPair harc.left_mem with rfl | rfl <;>
    rcases harcPair harc.right_mem with rfl | rfl
  · exact hxyne rfl
  · exact harc.not_subset_pair harcPair
  · exact harc.not_subset_pair (by simpa [Set.pair_comm] using harcPair)
  · exact hxyne rfl

/-- Every edge of a genuine target ear is polygonal. -/
theorem target_ear_edge_polygonal
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {F : γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hpath : H.IsPath a D b) (hF : F ∈ T.str.faces)
    (hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell F) :
    ∀ e ∈ D, IsPolygonal (Graph.edgeArc Hdraw e) := by
  intro e he
  rcases hH.edge_dichotomy (hpath.edge_mem he) with houter | hpoly
  · exact absurd houter (target_ear_edge_not_outer hH hpath hF hinside e he)
  · exact hpoly.1

/-- Injectively rename a nontrivial ambient target ear with fresh abstract cells and realize it
as a crosscut of the target face that contains its open arc. -/
theorem exists_targetSideEarStepData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
      H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      (∀ g ∈ D, g ∉ E(B)) →
      ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
        IsTargetPartialTransferOf T P B Hdraw par →
        Nonempty (TargetSideEarStepData T B H Hdraw a b D) := by
  classical
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hinside, huF, hvF⟩ :=
    exists_target_face_of_ear hH hBH hpath hab haB hbB hint hnew hT
  let paths := T.str_boundaryCycles.boundaryPaths F hF u v hu hv huF hvF huv
  let Q : Graph Plane γ := H.pathGraphOf a D
  have hQle : Q ≤ H := Graph.pathGraphOf_le hpath.isWalk
  have hQpath : Q.IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  have haQ : a ∈ V(Q) := Graph.mem_vertexSet_pathGraphOf_self
  have hbQ : b ∈ V(Q) := by
    rw [Graph.pathGraphOf_vertexSet]
    exact hpath.target_mem_walkVertices
  have hQfinV : V(Q).Finite := hpath.isWalk.finite_vertexSet_pathGraphOf
  have hQfinE : E(Q).Finite := hpath.isWalk.finite_edgeSet_pathGraphOf
  have huCell : u ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hu
  have hvCell : v ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hv
  obtain ⟨vname, vname_a, vname_b, vname_inj, vname_fresh⟩ :=
    exists_injective_pinned_avoiding T.str.finite_cells huCell hvCell huv hQfinV hab
  let newVertices : Set γ := vname '' (V(Q) \ {a, b})
  have hnewVertices_fin : newVertices.Finite := hQfinV.sdiff.image vname
  have hnewVertices_avoid : Disjoint newVertices T.str.cells := by
    rw [Set.disjoint_left]
    rintro z ⟨x, ⟨hxQ, hxab⟩, rfl⟩ hzCell
    exact vname_fresh x hxQ (fun h => hxab (Or.inl h)) (fun h => hxab (Or.inr h)) hzCell
  let edgeUsed : Set γ := T.str.cells ∪ newVertices
  have hedgeUsed_fin : edgeUsed.Finite := T.str.finite_cells.union hnewVertices_fin
  letI : Finite E(Q) := Set.finite_coe_iff.mpr hQfinE
  obtain ⟨freshEdge, freshEdge_inj, freshEdge_avoid⟩ :=
    exists_injective_avoiding edgeUsed hedgeUsed_fin E(Q)
  let ename : γ → γ := fun e => if he : e ∈ E(Q) then freshEdge ⟨e, he⟩ else u
  have ename_apply {e : γ} (he : e ∈ E(Q)) : ename e = freshEdge ⟨e, he⟩ := by
    simp [ename, he]
  have ename_inj : InjOn ename E(Q) := by
    intro e he f hf hef
    have hsub : (⟨e, he⟩ : E(Q)) = ⟨f, hf⟩ := by
      apply freshEdge_inj
      calc
        freshEdge ⟨e, he⟩ = ename e := (ename_apply he).symm
        _ = ename f := hef
        _ = freshEdge ⟨f, hf⟩ := ename_apply hf
    exact congrArg (fun z : E(Q) => z.1) hsub
  have ename_avoid {e : γ} (he : e ∈ E(Q)) : ename e ∉ edgeUsed := by
    rw [ename_apply he]
    exact freshEdge_avoid ⟨e, he⟩
  let newEdges : Set γ := ename '' E(Q)
  have hnewEdges_fin : newEdges.Finite := hQfinE.image ename
  have hnewEdges_avoid : Disjoint newEdges edgeUsed := by
    rw [Set.disjoint_left]
    rintro z ⟨e, he, rfl⟩
    exact ename_avoid he
  let faceUsed : Set γ := edgeUsed ∪ newEdges
  have hfaceUsed_fin : faceUsed.Finite := hedgeUsed_fin.union hnewEdges_fin
  obtain ⟨freshFace, freshFace_inj, freshFace_avoid⟩ :=
    exists_injective_avoiding faceUsed hfaceUsed_fin (Fin 2)
  let face₁ : γ := freshFace 0
  let face₂ : γ := freshFace 1
  let relabelled : Graph Plane γ := Q.relabelEdges ename ename_inj
  let ear : Graph γ γ := relabelled.map vname
  have hVear : V(ear) = vname '' V(Q) := by simp [ear, relabelled]
  have hEear : E(ear) = ename '' E(Q) := by simp [ear, relabelled]
  have hearPath : ear.IsPathGraph u (D.map ename) v := by
    have hrel := hQpath.relabelEdges ename_inj
    have hmap := hrel.map (by simpa [relabelled] using vname_inj)
    simpa [ear, relabelled, vname_a, vname_b] using hmap
  have hear_disjoint : Disjoint V(ear) E(ear) := by
    rw [Set.disjoint_left]
    rintro z hzV hzE
    rw [hVear] at hzV
    rw [hEear] at hzE
    obtain ⟨x, hxQ, rfl⟩ := hzV
    obtain ⟨e, heQ, heq⟩ := hzE
    have hedgeAvoid := ename_avoid heQ
    apply hedgeAvoid
    rcases eq_or_ne x a with rfl | hxa
    · exact Or.inl (by rw [heq, vname_a]; exact huCell)
    rcases eq_or_ne x b with rfl | hxb
    · exact Or.inl (by rw [heq, vname_b]; exact hvCell)
    · exact Or.inr ⟨x, ⟨hxQ, by simp [hxa, hxb]⟩, heq.symm⟩
  have hvertex_inter : V(ear) ∩ V(T.str.skel) = {u, v} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzEar, hzOld⟩
      rw [hVear] at hzEar
      obtain ⟨x, hxQ, rfl⟩ := hzEar
      rcases eq_or_ne x a with rfl | hxa
      · simp [vname_a]
      rcases eq_or_ne x b with rfl | hxb
      · simp [vname_b]
      exfalso
      exact vname_fresh x hxQ hxa hxb (T.str.mem_cells_of_mem_vertexSet hzOld)
    · rintro z (rfl | rfl)
      · exact ⟨hVear ▸ ⟨a, haQ, vname_a⟩, hu⟩
      · exact ⟨hVear ▸ ⟨b, hbQ, vname_b⟩, hv⟩
  have hface₁Avoid : face₁ ∉ faceUsed := freshFace_avoid 0
  have hface₂Avoid : face₂ ∉ faceUsed := freshFace_avoid 1
  let d : T.str.SplitData := {
    face := F
    face₁ := face₁
    face₂ := face₂
    ear := ear
    source := u
    target := v
    earWalk := D.map ename
    path₁ := paths.path₁
    path₂ := paths.path₂
    isPathGraph := hearPath
    isPath₁ := paths.isPath₁
    isPath₂ := paths.isPath₂
    ear_disjoint := hear_disjoint
    source_ne_target := huv
    face_mem := hF
    vertexSet_inter := hvertex_inter
    edge_fresh := by
      intro e he
      rw [hEear] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact fun hmem => ename_avoid hf (Or.inl hmem)
    vertex_fresh := by
      intro z hz hzu hzv
      rw [hVear] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxa : x ≠ a := fun h => hzu (h ▸ vname_a)
      have hxb : x ≠ b := fun h => hzv (h ▸ vname_b)
      exact vname_fresh x hx hxa hxb
    face₁_notMem := fun h => hface₁Avoid (Or.inl (Or.inl h))
    face₂_notMem := fun h => hface₂Avoid (Or.inl (Or.inl h))
    face₁_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₁Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₁Avoid (Or.inr hz)
    face₂_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₂Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₂Avoid (Or.inr hz)
    face_ne := fun h => Fin.zero_ne_one (freshFace_inj h)
    sub_face := paths.sub_face
    paths_meet := paths.paths_meet
  }
  let tgtPos : γ → Plane := Function.invFunOn vname V(Q)
  let tgtDraw : γ → ℝ → Plane := Graph.relabelDrawing Q ename Hdraw
  have hQdraw : Graph.IsDrawing Q Hdraw := hH.isDrawing.mono hQle
  have hrelDraw : Graph.IsDrawing relabelled tgtDraw := hQdraw.relabelEdges ename_inj
  have hearGraph : d.earGraph tgtPos = relabelled := by
    change (relabelled.map vname).map tgtPos = relabelled
    simpa [tgtPos, relabelled] using
      (Graph.map_map_invFunOn (G := relabelled) (f := vname)
        (by simpa [relabelled] using vname_inj))
  have htgtSet : d.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D := by
    rw [CellStructure.SplitData.earSet, hearGraph, Graph.pointSet_relabelEdges ename_inj]
    simpa [Q] using hH.isDrawing.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)
  have htgtEdgeOrig := target_ear_edge_polygonal hH hpath hF hinside
  have htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) →
      IsPolygonal (Graph.edgeArc tgtDraw e) := by
    intro e he
    change e ∈ E(ear) at he
    rw [hEear] at he
    obtain ⟨f, hfQ, rfl⟩ := he
    rw [Graph.edgeArc_relabelDrawing ename_inj hfQ]
    apply htgtEdgeOrig f
    rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ
  have htgtPoly : IsPolygonal (d.earSet tgtPos tgtDraw) := by
    rw [htgtSet]
    exact hQdraw.isPolygonal_edgesCover
      (fun f hfQ => htgtEdgeOrig f (by
        rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ))
      hpath.pathGraphOf.isWalk (hpath.ne_nil hab)
  have htgt : d.EarCrosscut T.tgt tgtPos tgtDraw := {
    pos_source := by
      change tgtPos u = T.tgt.pos u
      rw [hua]
      change Function.invFunOn vname V(Q) u = a
      rw [← vname_a, vname_inj.leftInvOn_invFunOn haQ]
    pos_target := by
      change tgtPos v = T.tgt.pos v
      rw [hvb]
      change Function.invFunOn vname V(Q) v = b
      rw [← vname_b, vname_inj.leftInvOn_invFunOn hbQ]
    injOn := by
      change InjOn (Function.invFunOn vname V(Q)) V(ear)
      rw [hVear]
      exact Function.invFunOn_injOn_image vname V(Q)
    isDrawing := by rw [hearGraph]; exact hrelDraw
    subset_face := by
      rw [htgtSet]
      simpa [d, hua, hvb] using hinside
    disjoint_skeleton := T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition hF
    polygonal := htgtPoly
  }
  refine ⟨{
    splitData := d
    tgtPos := tgtPos
    tgtDraw := tgtDraw
    tgtCrosscut := htgt
    tgtEdgePolygonal := htgtEdgePoly
    target_pos_source := hua
    target_pos_target := hvb
    tgtEarSet_eq := htgtSet
    vertexSet_subset := ?_
  }⟩
  change V(B.union (H.pathGraphOf a D)) ⊆
    V((T.str.splitFace d).skel.map (d.splitPos T.tgt tgtPos))
  rw [htgt.splitGraph_eq]
  intro x hx
  rcases hx with hxB | hxQ
  · exact Or.inl (hT.vertexSet_subset hxB)
  · apply Or.inr
    rw [hearGraph, Graph.vertexSet_relabelEdges]
    exact hxQ

/-- The skeleton homeomorphism sends an abstract vertex on the source outer curve to the
corresponding abstract vertex on the target outer curve. -/
theorem GeneratedPair.target_pos_mem_outer_of_source_pos_mem_outer
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {v : γ}
    (hv : v ∈ V(T.str.skel)) (hx : T.src.pos v ∈ srcOuter) :
    T.tgt.pos v ∈ tgtOuter := by
  have hxOuter : T.src.pos v ∈ T.src.outerSet :=
    T.src_isWeaklyAdmissible.outerSet_eq.symm ▸ hx
  have himage : T.homeo.toFun (T.src.pos v) ∈ T.tgt.outerSet := by
    rw [← T.homeo.image_outerSet]
    exact Set.mem_image_of_mem T.homeo.toFun hxOuter
  rw [T.homeo.pos_apply hv] at himage
  rwa [T.tgt_isWeaklyAdmissible.outerSet_eq] at himage

/-- The relative anchored-boundary condition supplies the strong-accessibility half of
readiness at both outer endpoints of a nontrivial target ear.  Compatibility of the evolving
skeleton map with the original one identifies those endpoints with the original inverse
images. -/
theorem targetEarEndpointStronglyAccessible_of_newBoundaryAnchored
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {par : γ → γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : NewTargetBoundaryAnchored P P.tgt.skeletonSet H Hdraw)
    (hBH : B ≤ H) (hnew : ∀ g ∈ D, g ∉ E(B))
    (hpath : H.IsPath a D b) (hab : a ≠ b)
    (hT : IsTargetPartialTransferOf T P B Hdraw par)
    (w : TargetSideEarStepData T B H Hdraw a b D) :
    (T.src.pos w.splitData.source ∈ srcOuter →
      StronglyAccessible (srcDom \ srcOuter) (T.src.pos w.splitData.source)) ∧
    (T.src.pos w.splitData.target ∈ srcOuter →
      StronglyAccessible (srcDom \ srcOuter) (T.src.pos w.splitData.target)) := by
  let d := w.splitData
  have hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell d.face := by
    intro x hx
    apply w.tgtCrosscut.subset_face
    refine ⟨?_, ?_⟩
    · rw [w.tgtEarSet_eq]
      exact hx.1
    · simpa only [w.target_pos_source, w.target_pos_target] using hx.2
  have hnotOuter := target_ear_edge_not_outer hH hpath d.face_mem hinside
  obtain ⟨eₛ, heₛ, hincₛ⟩ :=
    hpath.isWalk.exists_inc_source (hpath.ne_nil hab)
  obtain ⟨eₜ, heₜ, hincₜ⟩ :=
    hpath.reverse.isWalk.exists_inc_source (hpath.reverse.ne_nil (Ne.symm hab))
  have heₜD : eₜ ∈ D := by simpa using heₜ
  have target_mem_original : ∀ {v : γ}, T.tgt.pos v ∈ tgtOuter →
      T.tgt.pos v ∈ P.tgt.skeletonSet := by
    intro v hv
    apply P.tgt.outerSet_subset_skeletonSet
    exact (Set.ext_iff.mp P.tgt_isWeaklyAdmissible.outerSet_eq (T.tgt.pos v)).mpr hv
  constructor
  · intro hx
    have hy := T.target_pos_mem_outer_of_source_pos_mem_outer d.source_mem_skel hx
    have haOuter : a ∈ tgtOuter := by rwa [← w.target_pos_source]
    rw [hT.source_pos_eq_invFun_target_pos d.source_mem_skel
      (target_mem_original hy), w.target_pos_source]
    exact hanchor hBH (by rw [← hT.skeletonSet_eq]; exact hT.targetSkeletonSet_subset)
      (hpath.edge_mem heₛ) (hnew eₛ heₛ) hincₛ haOuter (hnotOuter eₛ heₛ)
  · intro hx
    have hy := T.target_pos_mem_outer_of_source_pos_mem_outer d.target_mem_skel hx
    have hbOuter : b ∈ tgtOuter := by rwa [← w.target_pos_target]
    rw [hT.source_pos_eq_invFun_target_pos d.target_mem_skel
      (target_mem_original hy), w.target_pos_target]
    exact hanchor hBH (by rw [← hT.skeletonSet_eq]; exact hT.targetSkeletonSet_subset)
      (hpath.edge_mem heₜD) (hnew eₜ heₜD) hincₜ hbOuter (hnotOuter eₜ heₜD)

/-! ### The exact geometric obligation on the source side -/

/-- An abstract skeleton vertex is outer-only when every current edge incident with it belongs
to the distinguished outer graph. -/
def CellStructure.OuterOnlyAt (S : CellStructure γ) (v : γ) : Prop :=
  ∀ {e : γ}, S.skel.Inc e v → e ∈ E(S.outerGraph)

/-- At most two distinct outer edges are incident with the vertex.  This is the exact local
consequence of "the distinguished outer graph is a cycle" used by reverse transfer. -/
def CellStructure.OuterIncidenceAtMostTwo (S : CellStructure γ) (v : γ) : Prop :=
  ∀ ⦃e f g : γ⦄, S.outerGraph.Inc e v → S.outerGraph.Inc f v →
    S.outerGraph.Inc g v → e = f ∨ e = g ∨ f = g

/-- The distinguished outer graph is locally at most two-branched at every vertex. -/
def CellStructure.OuterIncidenceAtMostTwoEverywhere (S : CellStructure γ) : Prop :=
  ∀ v, S.OuterIncidenceAtMostTwo v

/-- A graph whose outer edges form one simple cycle is locally at most two-branched.  Rotate
the cycle to one incident edge; every other edge at that endpoint lies on the complementary
simple path, which has only one incident edge at either end. -/
theorem CellStructure.OuterEdgesFormCycle.outerIncidenceAtMostTwoEverywhere
    {S : CellStructure γ} (h : S.OuterEdgesFormCycle) :
    S.OuterIncidenceAtMostTwoEverywhere := by
  obtain ⟨e, u, v, D, hc, hE⟩ := h
  intro z f g k hf hg hk
  have hfC : f ∈ e :: D := by
    change f ∈ ({f | f ∈ e :: D} : Set γ)
    rw [← hE]
    exact hf.edge_mem
  have hgC : g ∈ e :: D := by
    change g ∈ ({f | f ∈ e :: D} : Set γ)
    rw [← hE]
    exact hg.edge_mem
  have hkC : k ∈ e :: D := by
    change k ∈ ({f | f ∈ e :: D} : Set γ)
    rw [← hE]
    exact hk.edge_mem
  obtain ⟨a, b, W, hrot, hperm⟩ := hc.rotate hfC
  have hg' : g = f ∨ g ∈ W := List.mem_cons.1 (hperm.mem_iff.2 hgC)
  have hk' : k = f ∨ k ∈ W := List.mem_cons.1 (hperm.mem_iff.2 hkC)
  rcases hf.eq_or_eq_of_isLink hrot.isLink with rfl | rfl
  · rcases hg' with rfl | hgW
    · exact Or.inl rfl
    rcases hk' with rfl | hkW
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr
        (hrot.isPath.inc_source_unique hgW hkW hg hk))
  · rcases hg' with rfl | hgW
    · exact Or.inl rfl
    rcases hk' with rfl | hkW
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (hrot.isPath.reverse.inc_source_unique
        (by simpa using hgW) (by simpa using hkW) hg hk))

namespace CellStructure.SubdivData

/-- Every abstract walk admits the orientation-aware edge substitution prescribed by a
subdivision. -/
theorem exists_substWalk_of_isWalk {S : CellStructure γ} (d : S.SubdivData)
    {u v : γ} {W : List γ} (hW : S.skel.IsWalk u W v) :
  ∃ W', d.SubstWalk u W W' := by
  induction hW with
  | nil _ =>
      refine ⟨[], ?_⟩
      exact CellStructure.SubstWalk.nil (S := S) (edge := d.edge)
        (left := d.left) (right := d.right) (newEdge₁ := d.newEdge₁)
        (newEdge₂ := d.newEdge₂) _
  | @cons u w v f W hl hW ih =>
      obtain ⟨W', hsub⟩ := ih
      by_cases hfe : f = d.edge
      · subst f
        rcases hl.eq_and_eq_or_eq_and_eq d.isLink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨d.newEdge₁ :: d.newEdge₂ :: W', .forward hsub⟩
        · exact ⟨d.newEdge₂ :: d.newEdge₁ :: W', .backward hsub⟩
      · exact ⟨f :: W', .other hl hfe hsub⟩

/-- If the subdivided edge occurs in the input, both replacement edges occur in the output. -/
theorem SubstWalk.newEdges_mem_output_of_mem_input {S : CellStructure γ}
    {d : S.SubdivData} {u : γ} {W W' : List γ}
    (hsub : d.SubstWalk u W W') (he : d.edge ∈ W) :
    d.newEdge₁ ∈ W' ∧ d.newEdge₂ ∈ W' := by
  induction hsub with
  | nil => simp at he
  | forward => simp
  | backward => simp
  | @other u w f W W' hl hne hs ih =>
      have heW : d.edge ∈ W := by
        rcases List.mem_cons.1 he with h | h
        · exact absurd h.symm hne
        · exact h
      exact ⟨List.mem_cons_of_mem _ (ih heW).1, List.mem_cons_of_mem _ (ih heW).2⟩

/-- With the subdivided edge present, the output edge names are exactly the two replacements
and the surviving input names. -/
theorem SubstWalk.mem_output_iff_of_mem_input {S : CellStructure γ}
    {d : S.SubdivData} {u x : γ} {W W' : List γ}
    (hsub : d.SubstWalk u W W') (he : d.edge ∈ W) :
    x ∈ W' ↔ x = d.newEdge₁ ∨ x = d.newEdge₂ ∨ (x ∈ W ∧ x ≠ d.edge) := by
  constructor
  · intro hx
    rcases hsub.mem_input_of_mem_output hx with rfl | rfl | hxW
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨hxW, fun h => hsub.edge_notMem_output (h ▸ hx)⟩)
  · rintro (rfl | rfl | ⟨hxW, hne⟩)
    · exact (hsub.newEdges_mem_output_of_mem_input he).1
    · exact (hsub.newEdges_mem_output_of_mem_input he).2
    · exact hsub.mem_output_of_mem_input_of_ne hxW hne

/-- Edge subdivision preserves the fact that the distinguished outer edges form one simple
cycle.  When the subdivided edge is outer, substitute it in the closed cycle walk and pull the
resulting cycle down from the new skeleton to the new outer graph. -/
theorem outerEdgesFormCycle {S : CellStructure γ} (d : S.SubdivData)
    (hcycle : S.OuterEdgesFormCycle) :
    (S.subdivideEdge d).OuterEdgesFormCycle := by
  by_cases heOuter : d.edge ∈ E(S.outerGraph)
  · obtain ⟨e, u, v, D, hc, hE⟩ := hcycle
    have heList : d.edge ∈ e :: D := by
      change d.edge ∈ ({f | f ∈ e :: D} : Set γ)
      rw [← hE]
      exact heOuter
    have hclosedOuter : S.outerGraph.IsWalk v (e :: D) v :=
      .cons hc.isLink.symm hc.isPath.isWalk
    have hclosed : S.skel.IsWalk v (e :: D) v := hclosedOuter.mono S.outerGraph_le
    obtain ⟨W', hsub⟩ := d.exists_substWalk_of_isWalk hclosed
    obtain ⟨e', u', D', hW', hc'⟩ :=
      SubstWalk.exists_isCycleThrough hsub hclosed (hc.mono S.outerGraph_le)
    have houtput : ∀ f ∈ W', f ∈ E(d.outer) := by
      intro f hf
      rw [d.outer_edgeSet_of_mem heOuter]
      rcases (hsub.mem_output_iff_of_mem_input heList).1 hf with rfl | rfl | ⟨hfC, hfe⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · have hfOld : f ∈ E(S.outerGraph) := by
          rw [hE]
          exact hfC
        have hfDiff : f ∈ E(S.outerGraph) \ {d.edge} := ⟨hfOld, by simpa using hfe⟩
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hfDiff)
    have hcOuter : d.outer.IsCycleThrough e' u' v D' := by
      apply hc'.anti d.outer_le_skeleton
      intro f hf
      exact houtput f (hW' ▸ hf)
    refine ⟨e', u', v, D', hcOuter, ?_⟩
    have hEdges : E(d.outer) = {f | f ∈ W'} := by
      ext f
      rw [d.outer_edgeSet_of_mem heOuter]
      change (f = d.newEdge₁ ∨ f = d.newEdge₂ ∨
          (f ∈ E(S.outerGraph) ∧ f ≠ d.edge)) ↔ f ∈ W'
      rw [hsub.mem_output_iff_of_mem_input heList]
      constructor
      · rintro (h | h | ⟨hf, hne⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨by
            change f ∈ ({f | f ∈ e :: D} : Set γ)
            rwa [← hE], hne⟩)
      · rintro (h | h | ⟨hf, hne⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨by
            rw [hE]
            exact hf, hne⟩)
    simpa only [CellStructure.subdivideEdge_outerGraph, hW'] using hEdges
  · unfold CellStructure.OuterEdgesFormCycle
    rw [CellStructure.subdivideEdge_outerGraph, d.outer_eq heOuter]
    exact hcycle

end CellStructure.SubdivData

/-- Splitting a face leaves the distinguished outer graph unchanged. -/
theorem CellStructure.SplitData.outerEdgesFormCycle {S : CellStructure γ}
    (d : S.SplitData) (hcycle : S.OuterEdgesFormCycle) :
    (S.splitFace d).OuterEdgesFormCycle := by
  unfold CellStructure.OuterEdgesFormCycle
  rw [CellStructure.splitFace_outerGraph]
  exact hcycle

/-- Every generated structure keeps one simple cycle as its distinguished outer edge set. -/
theorem GeneratedStructure.outerEdgesFormCycle {S₀ S : CellStructure γ}
    (h : GeneratedStructure S₀ S) (h₀ : S₀.OuterEdgesFormCycle) :
    S.OuterEdgesFormCycle := by
  induction h with
  | base => exact h₀
  | subdivideEdge _ d ih => exact d.outerEdgesFormCycle ih
  | splitFace _ d ih => exact d.outerEdgesFormCycle ih

/-- The local two-branch condition needed by square-mesh reverse transfer is therefore a
generated-structure invariant as soon as the base outer edges form a simple cycle. -/
theorem GeneratedStructure.outerIncidenceAtMostTwoEverywhere
    {S₀ S : CellStructure γ} (h : GeneratedStructure S₀ S)
    (h₀ : S₀.OuterEdgesFormCycle) : S.OuterIncidenceAtMostTwoEverywhere :=
  (h.outerEdgesFormCycle h₀).outerIncidenceAtMostTwoEverywhere

/-- A vertex on a nonloop simple cycle has two distinct incident cycle edges.  The face-cycle
application obtains nonloopness from either geometric realization. -/
theorem CellStructure.FaceCycle.exists_distinct_incident_edges
    {S : CellStructure γ} {F v : γ} (c : S.FaceCycle F)
    (hloopless : ∀ ⦃e x y : γ⦄, S.skel.IsLink e x y → x ≠ y)
    (hv : v ∈ V(S.skel)) (hvF : S.sub v F) :
    ∃ e f, e ≠ f ∧ e ∈ c.edge :: c.walk ∧ f ∈ c.edge :: c.walk ∧
      S.skel.Inc e v ∧ S.skel.Inc f v := by
  have hvW := c.mem_walk_of_vertex_sub hv hvF
  have huv : c.source ≠ c.target := hloopless c.isCycle.isLink
  by_cases hvu : v = c.source
  · subst hvu
    obtain ⟨f, hf, hfinc⟩ :=
      c.isCycle.isPath.isWalk.exists_inc_source (c.isCycle.isPath.ne_nil huv)
    exact ⟨c.edge, f, fun hef => c.isCycle.notMem (hef ▸ hf),
      List.mem_cons_self, List.mem_cons_of_mem _ hf, c.isCycle.isLink.inc_left, hfinc⟩
  by_cases hvq : v = c.target
  · subst hvq
    obtain ⟨f, hf, hfinc⟩ := c.isCycle.isPath.reverse.isWalk.exists_inc_source
      (c.isCycle.isPath.reverse.ne_nil (Ne.symm huv))
    have hfD : f ∈ c.walk := by simpa using hf
    exact ⟨c.edge, f, fun hef => c.isCycle.notMem (hef ▸ hfD),
      List.mem_cons_self, List.mem_cons_of_mem _ hfD, c.isCycle.isLink.inc_right, hfinc⟩
  obtain ⟨W₁, W₂, hwalk, h₁, h₂, -⟩ := c.isCycle.isPath.split hvW
  obtain ⟨e, he, heinc⟩ :=
    h₁.reverse.isWalk.exists_inc_source (h₁.reverse.ne_nil hvu)
  obtain ⟨f, hf, hfinc⟩ := h₂.isWalk.exists_inc_source (h₂.ne_nil hvq)
  have heW₁ : e ∈ W₁ := by simpa using he
  have hef : e ≠ f := by
    intro heq
    have hnodup : (W₁ ++ W₂).Nodup := hwalk ▸ c.isCycle.isPath.nodup
    apply List.disjoint_of_nodup_append hnodup heW₁
    rwa [heq]
  have heD : e ∈ c.walk := hwalk ▸ List.mem_append_left W₂ heW₁
  have hfD : f ∈ c.walk := hwalk ▸ List.mem_append_right W₁ hf
  exact ⟨e, f, hef, List.mem_cons_of_mem _ heD, List.mem_cons_of_mem _ hfD, heinc, hfinc⟩

/-- A nonouter edge of the evolving abstract skeleton incident at a current ambient vertex
produces a nonouter edge of the ambient graph incident at the same geometric point.  No edge
labels need to agree: a sufficiently small vertex square meets only ambient edges incident at
that vertex, while the open cell of the abstract edge accumulates at its endpoint. -/
theorem IsTargetPartialTransferOf.exists_ambient_nonouter_incident
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    [B.Finite]
    (hT : IsTargetPartialTransferOf T P B Hdraw par)
    (hBdraw : B.IsDrawing Hdraw) {v e : γ}
    (hvB : T.tgt.pos v ∈ V(B)) (hvOuter : T.tgt.pos v ∈ tgtOuter)
    (hinc : T.str.skel.Inc e v) (heOuter : e ∉ E(T.str.outerGraph)) :
    ∃ f ∈ E(B), B.Inc f (T.tgt.pos v) ∧
      ¬ edgeArc Hdraw f ⊆ tgtOuter := by
  obtain ⟨w, hl⟩ := hinc
  have harc := T.tgt.isDrawing.edge_isArcBetween (hl.map T.tgt.pos)
  have hclosure : T.tgt.pos v ∈ closure (T.tgt.cell e) := by
    rw [T.tgt.cell_edge hl]
    exact harc.left_mem_closure_diff
  obtain ⟨r, hr, hvert, hedge⟩ := hBdraw.exists_square_at hvB
  obtain ⟨z, hzNear, hzCell⟩ := mem_closure_iff.1 hclosure
    (Plane.openSquare (T.tgt.pos v) r) (Plane.isOpen_openSquare _ _)
    (Plane.mem_openSquare_self hr)
  have hzClosed : z ∈ Plane.closedSquare (T.tgt.pos v) r :=
    Plane.openSquare_subset_closedSquare _ _ hzNear
  have hzOuter : z ∉ tgtOuter :=
    (T.tgt_isWeaklyAdmissible.cell_subset hl.edge_mem heOuter hzCell).2
  have hzSkel : z ∈ T.tgt.skeletonSet :=
    T.tgt.cell_subset_skeletonSet (Or.inr hl.edge_mem) hzCell
  have hzB : z ∈ pointSet B Hdraw := by
    rw [← hT.skeletonSet_eq]
    exact hzSkel
  rcases hzB with hzV | hzE
  · have hzv : z = T.tgt.pos v := by
      by_contra hne
      exact hvert z hzV hne hzClosed
    exact absurd (hzv ▸ hvOuter) hzOuter
  · obtain ⟨f, hf, hzf⟩ := Set.mem_iUnion₂.1 hzE
    have hfinc : B.Inc f (T.tgt.pos v) := by
      by_contra hninc
      exact Set.disjoint_left.1 (hedge f hf hninc) hzClosed hzf
    exact ⟨f, hf, hfinc, fun hsub => hzOuter (hsub hzf)⟩

/-- If no new nonouter ambient edge can coexist at the boundary with a nonouter edge of the
current trace, then both boundary endpoints of the next reverse ear are outer-only in the
current abstract skeleton.  Any current nonouter abstract edge would reflect to just such a
current ambient edge. -/
theorem targetEarEndpointsOuterOnly_of_noNewNonouterIncidence
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hnoNew : NoNewNonouterIncidenceAtBoundary
      P.tgt.skeletonSet H Hdraw tgtOuter)
    {B : Graph Plane γ} {a b : Plane} {D : List γ} {par : γ → γ}
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hT : IsTargetPartialTransferOf T P B Hdraw par)
    (w : TargetSideEarStepData T B H Hdraw a b D) :
    (T.src.pos w.splitData.source ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.source) ∧
    (T.src.pos w.splitData.target ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.target) := by
  letI : H.Finite := hH.finite
  letI : B.Finite := Graph.Finite.of_le hBH
  have hBdraw := hH.isDrawing.mono hBH
  have hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆
      T.tgt.cell w.splitData.face := by
    intro x hx
    apply w.tgtCrosscut.subset_face
    refine ⟨?_, ?_⟩
    · rw [w.tgtEarSet_eq]
      exact hx.1
    · simpa only [w.target_pos_source, w.target_pos_target] using hx.2
  have hnotOuter := target_ear_edge_not_outer hH hpath w.splitData.face_mem hinside
  obtain ⟨eₛ, heₛ, hincₛ⟩ :=
    hpath.isWalk.exists_inc_source (hpath.ne_nil hab)
  obtain ⟨eₜ, heₜ, hincₜ⟩ :=
    hpath.reverse.isWalk.exists_inc_source (hpath.reverse.ne_nil (Ne.symm hab))
  have heₜD : eₜ ∈ D := by simpa using heₜ
  have endpoint_outerOnly : ∀ {v : γ} {y : Plane} {e : γ},
      v ∈ V(T.str.skel) → T.tgt.pos v = y → y ∈ V(B) →
      e ∈ D → H.Inc e y → ¬ edgeArc Hdraw e ⊆ tgtOuter →
      T.src.pos v ∈ srcOuter → T.str.OuterOnlyAt v := by
    intro v y e hv hpos hyB heD heinc henot hx
    have hyOuter : y ∈ tgtOuter := by
      rw [← hpos]
      exact T.target_pos_mem_outer_of_source_pos_mem_outer hv hx
    intro g hg
    by_contra hgOuter
    have hvB : T.tgt.pos v ∈ V(B) := by rwa [hpos]
    have hvOuter : T.tgt.pos v ∈ tgtOuter := by rwa [hpos]
    obtain ⟨f, hfB, hfincB, hfnot⟩ :=
      hT.exists_ambient_nonouter_incident hBdraw hvB hvOuter hg hgOuter
    exact hnoNew hBH (by rw [← hT.skeletonSet_eq]; exact hT.targetSkeletonSet_subset)
      hyOuter (hpath.edge_mem heD) hfB heinc
      (hpos ▸ hfincB) henot hfnot (hnew e heD)
  constructor
  · intro hx
    exact endpoint_outerOnly (v := w.splitData.source) (y := a) (e := eₛ)
      w.splitData.source_mem_skel w.target_pos_source haB
      heₛ hincₛ (hnotOuter eₛ heₛ) hx
  · intro hx
    exact endpoint_outerOnly (v := w.splitData.target) (y := b) (e := eₜ)
      w.splitData.target_mem_skel w.target_pos_target hbB
      heₜD hincₜ (hnotOuter eₜ heₜD) hx

/-- At an outer-only vertex with at most two outer branches, the selected incident face is the
only incident face.  Each simple face boundary contributes two distinct edges at the vertex;
the two-branch bound forces two such face boundaries to share an outer edge, and
`CombInvariants.outerEdge_unique` then identifies their face names. -/
theorem GeneratedPair.unique_source_face_of_outerOnly
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {v F : γ}
    (hv : v ∈ V(T.str.skel)) (hF : F ∈ T.str.faces) (hvF : T.str.sub v F)
    (houter : T.str.OuterOnlyAt v) (htwo : T.str.OuterIncidenceAtMostTwo v) :
    ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
      T.src.pos v ∈ closure R → R = T.src.cell F := by
  have hloopless : ∀ ⦃e x y : γ⦄, T.str.skel.IsLink e x y → x ≠ y := by
    intro e x y hxy hxyEq
    exact T.tgt.isDrawing.ne_of_isLink (hxy.map T.tgt.pos) (congrArg T.tgt.pos hxyEq)
  have face_edges : ∀ {Z : γ}, Z ∈ T.str.faces → T.str.sub v Z →
      ∃ e f, e ≠ f ∧ T.str.outerGraph.Inc e v ∧ T.str.outerGraph.Inc f v ∧
        T.str.sub e Z ∧ T.str.sub f Z := by
    intro Z hZ hvZ
    let c := T.str_boundaryCycles.faceCycle Z hZ
    obtain ⟨e, f, hef, heC, hfC, heinc, hfinc⟩ :=
      c.exists_distinct_incident_edges hloopless hv hvZ
    have heOuter : e ∈ E(T.str.outerGraph) := houter heinc
    have hfOuter : f ∈ E(T.str.outerGraph) := houter hfinc
    exact ⟨e, f, hef, (T.str.outerGraph_le.inc_congr heOuter).2 heinc,
      (T.str.outerGraph_le.inc_congr hfOuter).2 hfinc,
      c.sub_of_mem_pathCells (Or.inl heC), c.sub_of_mem_pathCells (Or.inl hfC)⟩
  obtain ⟨e₁, e₂, he₁₂, he₁inc, he₂inc, he₁F, -⟩ := face_edges hF hvF
  intro R hR hvR
  obtain ⟨Z, hZ, rfl⟩ := hR
  have hvZ : T.str.sub v Z :=
    T.src_isCellDecomposition.sub_of_pos_mem_closure_cell hv hZ hvR
  obtain ⟨f₁, f₂, hf₁₂, hf₁inc, hf₂inc, hf₁Z, hf₂Z⟩ := face_edges hZ hvZ
  have hcommon : e₁ = f₁ ∨ e₁ = f₂ := by
    rcases htwo he₁inc he₂inc hf₁inc with hbad | h | h
    · exact absurd hbad he₁₂
    · exact Or.inl h
    · rcases htwo he₁inc he₂inc hf₂inc with hbad | h' | hbad'
      · exact absurd hbad he₁₂
      · exact Or.inr h'
      · exact absurd (h.symm.trans hbad') hf₁₂
  have he₁Outer : e₁ ∈ E(T.str.outerGraph) := he₁inc.edge_mem
  obtain ⟨Q, hQ, huniq⟩ := T.str_combInvariants.outerEdge_unique he₁Outer
  have he₁Z : T.str.sub e₁ Z := hcommon.elim
    (fun h => h ▸ hf₁Z) (fun h => h ▸ hf₂Z)
  exact congrArg T.src.cell
    ((huniq Z ⟨hZ, he₁Z⟩).trans (huniq F ⟨hF, he₁F⟩).symm)

/-- An outer-only abstract vertex is absent from the compact nonboundary-edge carrier.  The
point-set statement includes the possible case where the vertex lies on the arc of an edge;
the drawing axiom turns that case back into incidence with the same edge. -/
theorem GeneratedPair.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {v : γ}
    (hv : v ∈ V(T.str.skel)) (houter : T.str.OuterOnlyAt v) :
    T.src.pos v ∉ pointSet T.sourceNonboundaryGraph T.src.drawing := by
  have abstract_incident : ∀ {e : γ}, T.src.graph.Inc e (T.src.pos v) →
      T.str.skel.Inc e v := by
    intro e hinc
    change (T.str.skel.map T.src.pos).Inc e (T.src.pos v) at hinc
    rw [Graph.map_inc] at hinc
    obtain ⟨w, hincw, hvw⟩ := hinc
    have heq : v = w := T.src.injOn_pos hv hincw.vertex_mem hvw
    rwa [heq]
  intro hx
  rcases hx with hxV | hxE
  · change T.src.pos v ∈ T.sourceNonboundaryVertices at hxV
    obtain ⟨e, -, heOuter, hinc⟩ := hxV
    exact heOuter (houter (abstract_incident hinc))
  · obtain ⟨e, heCore, hxe⟩ := Set.mem_iUnion₂.1 hxE
    change e ∈ E((T.src.graph.deleteEdges E(T.str.outerGraph)).induce
      T.sourceNonboundaryVertices) at heCore
    obtain ⟨p, q, hpq⟩ :=
      (T.src.graph.deleteEdges E(T.str.outerGraph)).induce
        T.sourceNonboundaryVertices |>.exists_isLink_of_mem_edgeSet heCore
    have heDeleted : e ∈ E(T.src.graph.deleteEdges E(T.str.outerGraph)) := hpq.1.edge_mem
    obtain ⟨heSrc, heOuter⟩ := Graph.mem_edgeSet_deleteEdges_iff.1 heDeleted
    obtain ⟨x, y, hxy⟩ := T.src.graph.exists_isLink_of_mem_edgeSet heSrc
    have hvSrc : T.src.pos v ∈ V(T.src.graph) := by
      rw [CellStructure.Realization.vertexSet_graph]
      exact ⟨v, hv, rfl⟩
    have hinc : T.src.graph.Inc e (T.src.pos v) := by
      rcases T.src.isDrawing.vertex_mem_edgeArc hxy hvSrc hxe with h | h
      · exact h ▸ hxy.inc_left
      · exact h ▸ hxy.inc_right
    exact heOuter (houter (abstract_incident hinc))

theorem GeneratedPair.isCompact_sourceNonboundaryGraph
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    IsCompact (pointSet T.sourceNonboundaryGraph T.src.drawing) :=
  (T.src.isDrawing.mono T.sourceNonboundaryGraph_le).isCompact_pointSet

/-- Inside the open Jordan domain, avoiding the compact nonboundary-edge carrier is equivalent
to avoiding the whole current skeleton; the remaining part of the latter is the outer curve. -/
theorem GeneratedPair.source_cellsAbsorbIn_nonboundary
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    CellsAbsorbIn (srcDom \ srcOuter)
      (pointSet T.sourceNonboundaryGraph T.src.drawing)
      {A | ∃ F ∈ T.str.faces, A = T.src.cell F} := by
  intro N hND hN hNdisj R hR hmeet
  apply (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
    N hN ?_ R hR hmeet
  rw [Set.disjoint_left]
  intro x hxN hxSkel
  rw [T.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSkel
  rcases hxSkel with hxCore | hxOuter
  · exact Set.disjoint_left.1 hNdisj hxN hxCore
  · exact (hND hxN).2 hxOuter

/-- Every point of the open source domain outside the compact nonboundary-edge carrier lies in
one current source face. -/
theorem GeneratedPair.exists_source_face_of_mem_interior_notMem_nonboundary
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {x : Plane}
    (hx : x ∈ srcDom \ srcOuter)
    (hxCore : x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing) :
    ∃ R ∈ {A : Set Plane | ∃ F ∈ T.str.faces, A = T.src.cell F}, x ∈ R := by
  have hxSkel : x ∉ T.src.skeletonSet := by
    rw [T.skeletonSet_eq_sourceNonboundaryGraph_union]
    rintro (hcore | houter)
    · exact hxCore hcore
    · exact hx.2 houter
  have hxDom : x ∈ ⋃ σ ∈ T.str.cells, T.src.cell σ := by
    rw [T.src_isCellDecomposition.iUnion_eq]
    exact hx.1
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hxDom
  have hσFace : σ ∈ T.str.faces := by
    rcases hσ with (hv | he) | hface
    · exact absurd (T.src.cell_subset_skeletonSet (Or.inl hv) hxσ) hxSkel
    · exact absurd (T.src.cell_subset_skeletonSet (Or.inr he) hxσ) hxSkel
    · exact hface
  exact ⟨T.src.cell σ, ⟨σ, hσFace, rfl⟩, hxσ⟩

/-- A fresh strongly accessible boundary anchor is accessible from its unique incident current
source face.  Compactness, absorption, and coverage are all discharged from the generated-pair
invariants; the three hypotheses are exactly the data maintained by the prescribed ear order. -/
theorem GeneratedPair.source_polyAccessible_of_fresh
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} {x : Plane}
    (hstrong : StronglyAccessible (srcDom \ srcOuter) x)
    (hfresh : x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing)
    (hunique : ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
      x ∈ closure R → R = T.src.cell F) :
    PolyAccessible (T.src.cell F) x := by
  exact polyAccessible_of_stronglyAccessible_in hstrong
    T.isCompact_sourceNonboundaryGraph hfresh T.source_cellsAbsorbIn_nonboundary
    (fun _ hy hycore =>
      T.exists_source_face_of_mem_interior_notMem_nonboundary hy hycore) hunique

/-- A point in the closure of a current source face is polygonally accessible whenever it is
off the wild outer curve.  The polygonal graph used by `polygonal_side_accessibility` is the
current skeleton with its outer edges deleted; adjoining the compact outer curve recovers the
whole source skeleton. -/
theorem GeneratedPair.source_polyAccessible_of_notMem_outer
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} {x : Plane} (hF : F ∈ T.str.faces) (hx : x ∈ closure (T.src.cell F))
    (hxOuter : x ∉ srcOuter) : PolyAccessible (T.src.cell F) x := by
  let G := T.src.graph.deleteEdges E(T.str.outerGraph)
  let O := T.str.outerGraph.map T.src.pos
  have hOle : O ≤ T.src.graph := T.str.outerGraph_le.map T.src.pos
  have hGunion : G.union O = T.src.graph := by
    apply Graph.eq_of_le_of_subset_subset (Graph.union_le Graph.deleteEdges_le hOle)
    · intro z hz
      exact Or.inl (by rwa [Graph.vertexSet_deleteEdges])
    · intro e he
      by_cases heOuter : e ∈ E(T.str.outerGraph)
      · exact Or.inr (by rwa [Graph.edgeSet_map])
      · exact Or.inl (Graph.mem_edgeSet_deleteEdges_iff.2 ⟨he, heOuter⟩)
  have hK : T.src.skeletonSet = pointSet G T.src.drawing ∪ srcOuter := by
    change pointSet T.src.graph T.src.drawing = _
    rw [← hGunion, Graph.pointSet_union]
    change pointSet G T.src.drawing ∪ T.src.outerSet = _
    rw [T.src_isWeaklyAdmissible.outerSet_eq]
  letI : G.Finite := Graph.Finite.of_le Graph.deleteEdges_le
  have hGdraw : G.IsDrawing T.src.drawing := T.src.isDrawing.mono Graph.deleteEdges_le
  have hGpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc T.src.drawing e) := by
    intro e he
    rw [Graph.mem_edgeSet_deleteEdges_iff] at he
    exact T.src_isWeaklyAdmissible.isPolygonal he.1 he.2
  let cells : Set (Set Plane) := {A | ∃ Z ∈ T.str.faces, A = T.src.cell Z}
  have hFcells : T.src.cell F ∈ cells := ⟨F, hF, rfl⟩
  have hdisj : Disjoint (T.src.cell F) T.src.skeletonSet :=
    T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF
  letI : O.Finite := Graph.Finite.of_le hOle
  have houterCompact : IsCompact srcOuter := by
    rw [← T.src_isWeaklyAdmissible.outerSet_eq]
    exact T.src.isCompact_skeletonSet.of_isClosed_subset
      (T.src.isDrawing.mono hOle).isClosed_pointSet T.src.outerSet_subset_skeletonSet
  exact Graph.polygonal_side_accessibility hGdraw hGpoly
    houterCompact hK (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
    hFcells hdisj hx hxOuter

/-- The two ways a source endpoint is ready for a reverse ear: it is off the wild curve, or it
is a fresh strongly accessible anchor incident with one prescribed current face. -/
def GeneratedPair.SourceEndpointReady
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (F : γ) (x : Plane) : Prop :=
  x ∉ srcOuter ∨
    StronglyAccessible (srcDom \ srcOuter) x ∧
      x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing ∧
      ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
        x ∈ closure R → R = T.src.cell F

/-- The relative no-new-incidence boundary condition, together with the static two-branch
invariant of generated outer graphs, supplies all reverse-ear fresh combinatorics. -/
theorem targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerIncidenceAtMostTwo
    [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hnoNew : NoNewNonouterIncidenceAtBoundary
      P.tgt.skeletonSet H Hdraw tgtOuter)
    (htwo : ∀ (S : CellStructure γ), GeneratedStructure S₀ S →
      S.OuterIncidenceAtMostTwoEverywhere) :
    TargetEarFreshCombinatorics P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hsourceOuterOnly, htargetOuterOnly⟩ :=
    targetEarEndpointsOuterOnly_of_noNewNonouterIncidence P hH hnoNew hBH hpath hab
      haB hbB hnew hT w
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  have htwoT := htwo T.str T.generated
  constructor
  · intro hx
    have houter : T.str.OuterOnlyAt d.source := hsourceOuterOnly hx
    exact ⟨T.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt d.source_mem_skel houter,
      T.unique_source_face_of_outerOnly d.source_mem_skel d.face_mem hsourceSub
        houter (htwoT d.source)⟩
  · intro hx
    have houter : T.str.OuterOnlyAt d.target := htargetOuterOnly hx
    exact ⟨T.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt d.target_mem_skel houter,
      T.unique_source_face_of_outerOnly d.target_mem_skel d.face_mem htargetSub
        houter (htwoT d.target)⟩

/-- The relative no-new-incidence condition and an outer cycle on the base structure supply
the reverse-ear fresh combinatorics. -/
theorem targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerCycle [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hnoNew : NoNewNonouterIncidenceAtBoundary
      P.tgt.skeletonSet H Hdraw tgtOuter)
    (hcycle : S₀.OuterEdgesFormCycle) :
    TargetEarFreshCombinatorics P H Hdraw :=
  targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerIncidenceAtMostTwo
    P hH hnoNew fun _ h => h.outerIncidenceAtMostTwoEverywhere hcycle

/-- The combinatorial/anchoring invariant still required from the prescribed target ear order:
both source endpoints selected by every nontrivial target ear are ready in the preceding sense. -/
def TargetEarFreshInvariant [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∀ w : TargetSideEarStepData T B H Hdraw a b D,
        T.SourceEndpointReady w.splitData.face (T.src.pos w.splitData.source) ∧
        T.SourceEndpointReady w.splitData.face (T.src.pos w.splitData.target)

/-- Relative anchoring of new ambient boundary edges and the remaining fresh-incidence
combinatorics together give the complete reverse-ear readiness invariant. -/
theorem targetEarFreshInvariant_of_newBoundaryAnchored [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : NewTargetBoundaryAnchored P P.tgt.skeletonSet H Hdraw)
    (hcomb : TargetEarFreshCombinatorics P H Hdraw) :
    TargetEarFreshInvariant P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hstrongₛ, hstrongₜ⟩ :=
    targetEarEndpointStronglyAccessible_of_newBoundaryAnchored
      hH hanchor hBH hnew hpath hab hT w
  obtain ⟨hcombₛ, hcombₜ⟩ :=
    hcomb B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  constructor
  · by_cases hx : T.src.pos w.splitData.source ∈ srcOuter
    · obtain ⟨hfresh, hunique⟩ := hcombₛ hx
      exact Or.inr ⟨hstrongₛ hx, hfresh, hunique⟩
    · exact Or.inl hx
  · by_cases hx : T.src.pos w.splitData.target ∈ srcOuter
    · obtain ⟨hfresh, hunique⟩ := hcombₜ hx
      exact Or.inr ⟨hstrongₜ hx, hfresh, hunique⟩
    · exact Or.inl hx

/-- Both source endpoints of every nontrivial target ear are polygonally accessible from the
source face selected by that ear.  This is the geometric invariant direction (b) must maintain:
off the wild curve it follows from polygonal-side accessibility, while a fresh wild-boundary
endpoint is supplied by `polyAccessible_of_stronglyAccessible`. -/
def TargetEarEndpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∀ w : TargetSideEarStepData T B H Hdraw a b D,
        PolyAccessible (T.src.cell w.splitData.face) (T.src.pos w.splitData.source) ∧
        PolyAccessible (T.src.cell w.splitData.face) (T.src.pos w.splitData.target)

/-- The fresh-anchor invariant implies the endpoint-accessibility invariant: the off-curve
branch uses polygonal-side accessibility, and the fresh branch uses the compact carrier and
unique-face theorem above. -/
theorem targetEarEndpointAccessibility_of_freshInvariant [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hfresh : TargetEarFreshInvariant P H Hdraw) :
    TargetEarEndpointAccessibility P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hsourceReady, htargetReady⟩ :=
    hfresh B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  have hsourceClosure : T.src.pos d.source ∈ closure (T.src.cell d.face) := by
    have hsub := T.src_isCellDecomposition.subset_closure
      (T.str.mem_cells_of_mem_vertexSet d.source_mem_skel)
      (T.str.mem_cells_of_mem_faces d.face_mem) hsourceSub
    rw [T.src.cell_vertex d.source_mem_skel] at hsub
    exact hsub (Set.mem_singleton _)
  have htargetClosure : T.src.pos d.target ∈ closure (T.src.cell d.face) := by
    have hsub := T.src_isCellDecomposition.subset_closure
      (T.str.mem_cells_of_mem_vertexSet d.target_mem_skel)
      (T.str.mem_cells_of_mem_faces d.face_mem) htargetSub
    rw [T.src.cell_vertex d.target_mem_skel] at hsub
    exact hsub (Set.mem_singleton _)
  constructor
  · rcases hsourceReady with houter | ⟨hstrong, hnew, hunique⟩
    · exact T.source_polyAccessible_of_notMem_outer d.face_mem hsourceClosure houter
    · exact T.source_polyAccessible_of_fresh hstrong hnew hunique
  · rcases htargetReady with houter | ⟨hstrong, hnew, hunique⟩
    · exact T.source_polyAccessible_of_notMem_outer d.face_mem htargetClosure houter
    · exact T.source_polyAccessible_of_fresh hstrong hnew hunique

/-- Endpoint accessibility supplies the missing source crosscut, after which the already-proved
arc matching and split constructor complete one nontrivial reverse ear. -/
theorem targetEarStepConstruction_of_endpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    TargetEarStepConstruction P H Hdraw hH := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨w⟩ := exists_targetSideEarStepData P H Hdraw hH
    B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨hsource, htarget⟩ :=
    haccess B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  let d := w.splitData
  have hends : T.src.pos d.source ≠ T.src.pos d.target := fun h =>
    d.source_ne_target (T.src.injOn_pos d.source_mem_skel d.target_mem_skel h)
  obtain ⟨A, hApoly, hAarc, hAsub⟩ :=
    exists_simple_arc_of_polyAccessible
      (T.src_isFaceJordan.isOpen d.face_mem)
      (T.src_isFaceJordan.isConnected d.face_mem).isPreconnected
      hends hsource htarget
  obtain ⟨srcPos, srcDraw, reverseHomeo, hsrc, hsrcEdgePoly⟩ :=
    w.tgtCrosscut.exists_matched_target hApoly hAarc hAsub
      (T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition d.face_mem)
  exact ⟨{
    splitData := d
    srcPos := srcPos
    srcDraw := srcDraw
    tgtPos := w.tgtPos
    tgtDraw := w.tgtDraw
    srcCrosscut := hsrc
    tgtCrosscut := w.tgtCrosscut
    earHomeo := reverseHomeo.symm
    srcEdgePolygonal := hsrcEdgePoly
    tgtEdgePolygonal := w.tgtEdgePolygonal
    tgtEarSet_eq := w.tgtEarSet_eq
    vertexSet_subset := w.vertexSet_subset
  }⟩

/-- One reverse ear follows from the endpoint-accessibility invariant. -/
theorem targetEarStep_of_endpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    TargetEarStep P H Hdraw :=
  targetEarStep_of_data hH
    (targetEarStepConstruction_of_endpointAccessibility P H Hdraw hH haccess)

/-- Explicit output data for the target common-subdivision construction. -/
structure TargetCommonSubdivisionData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) where
  /-- The part of `H` supported on the old target skeleton. -/
  graph : Graph Plane γ
  /-- The matched pair after inserting every vertex of `graph`. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite parent map from the subdivided pair to `P`. -/
  parent : γ → γ
  /-- The traced graph remains 2-connected. -/
  graph_isTwoConnected : graph.IsTwoConnected
  /-- The traced graph is a subgraph of the given target extension. -/
  graph_le : graph ≤ H
  /-- The refined pair realizes the traced target graph. -/
  isTargetPartialTransferOf : IsTargetPartialTransferOf pair P graph Hdraw parent

/-- Construct the target trace, its matched subdivision, and the composite parent map. -/
noncomputable def targetCommonSubdivisionData [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    TargetCommonSubdivisionData P H Hdraw := by
  classical
  let K := Graph.traceGraph H Hdraw P.tgt.skeletonSet
  have hKle : K ≤ H := Graph.traceGraph_le _
  letI : H.Finite := hH.finite
  letI : K.Finite := Graph.Finite.of_le hKle
  have hK2 : K.IsTwoConnected :=
    trace_isTwoConnected hH P.tgt_isWeaklyAdmissible.isTwoConnected
  have hvertices : V(K) ⊆ P.tgt.skeletonSet := by
    intro x hx
    rw [Graph.traceGraph_vertexSet] at hx
    exact hx.2
  let w := Classical.choice (GeneratedPair.exists_subdivideTargetSetData P
    (Graph.finite_vertexSet K) hvertices)
  exact {
    graph := K
    pair := w.pair
    parent := w.parent
    graph_isTwoConnected := hK2
    graph_le := hKle
    isTargetPartialTransferOf := {
      refines_src := w.refines_src
      refines_tgt := w.refines_tgt
      sourceSkeletonSet_subset := by
        rw [w.sourceSkeletonSet_eq]
      homeo_eqOn := w.homeo_eqOn
      skeletonSet_eq := w.skeletonSet_eq.trans (trace_pointSet hH).symm
      vertexSet_subset := w.vertexSet_subset
    }
  }

/-- **Step 1 of finite transfer, direction (b): construct the target common subdivision.** -/
theorem targetCommonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    TargetCommonSubdivision P H Hdraw := by
  let w := targetCommonSubdivisionData hH
  exact ⟨w.graph, w.pair, w.parent, w.graph_isTwoConnected, w.graph_le,
    w.isTargetPartialTransferOf⟩

/-- Iterate a target ear step from a common subdivision through the whole extension graph. -/
theorem targetTransferOfEars [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hsub : TargetCommonSubdivision P H Hdraw) (hstep : TargetEarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P H Hdraw par := by
  haveI := hH.finite
  obtain ⟨K, T₀, par₀, hK, hKH, hbase⟩ := hsub
  refine hH.isTwoConnected.ear_decomposition
    (motive := fun B => ∃ T par, IsTargetPartialTransferOf T P B Hdraw par)
    (fun g x => hH.isDrawing.not_isLoopAt g x) hK hKH ⟨T₀, par₀, hbase⟩ ?_
  rintro B a b D hB - hBH ⟨T, par, hT⟩ hpath hab haB hbB hint
  exact hstep B a b D hB hBH hpath hab haB hbB hint T par hT

/-- Direction (b), assuming only the target ear step. -/
theorem finite_transfer_toward_source_of_targetEarStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hstep : TargetEarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par := by
  obtain ⟨T, par, hT⟩ :=
    targetTransferOfEars hH (targetCommonSubdivision hH) hstep
  have hconnTgt : IsConnected T.tgt.nonboundary := by
    rw [CellStructure.Realization.nonboundary,
      T.tgt_isWeaklyAdmissible.outerSet_eq, hT.skeletonSet_eq]
    exact hH.isConnected
  have hconnSrc : IsConnected T.src.nonboundary :=
    T.homeo.isConnected_nonboundary_iff.2 hconnTgt
  exact ⟨T, par, hT, T.src_isAdmissible hconnSrc, T.tgt_isAdmissible hconnSrc⟩

/-- Direction (b), reduced to the precise geometric endpoint-accessibility invariant maintained
by the prescribed outer-cycle ear order. -/
theorem finite_transfer_toward_source_of_endpointAccessibility [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_targetEarStep hH
    (targetEarStep_of_endpointAccessibility P H Hdraw hH haccess)

/-- Direction (b), reduced to the prescribed ear order's concrete fresh-anchor and
unique-incident-face invariant.  All geometric accessibility and reverse-split construction is
discharged. -/
theorem finite_transfer_toward_source_of_freshInvariant [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hfresh : TargetEarFreshInvariant P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_endpointAccessibility hH
    (targetEarEndpointAccessibility_of_freshInvariant P H Hdraw hfresh)

/-- Direction (b), with strong accessibility discharged by relative anchoring of new target
boundary edges.  The only remaining hypothesis is the fresh-carrier and unique-face
combinatorics of the ear order. -/
theorem finite_transfer_toward_source_of_newBoundaryAnchored [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : NewTargetBoundaryAnchored P P.tgt.skeletonSet H Hdraw)
    (hcomb : TargetEarFreshCombinatorics P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_freshInvariant hH
    (targetEarFreshInvariant_of_newBoundaryAnchored P H Hdraw hH hanchor hcomb)

/-- **Finite transfer, direction (b), from relative ambient boundary geometry.**  Boundary
endpoints must be anchored, and a genuinely new nonouter edge must not coexist there with a
nonouter edge already in the current trace.  The abstract base needs one distinguished outer
cycle. -/
theorem finite_transfer_toward_source_of_relativeBoundaryGeometry [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : NewTargetBoundaryAnchored P P.tgt.skeletonSet H Hdraw)
    (hnoNew : NoNewNonouterIncidenceAtBoundary
      P.tgt.skeletonSet H Hdraw tgtOuter)
    (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_newBoundaryAnchored hH hanchor
    (targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerCycle
      P hH hnoNew hcycle)

end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialOuterCycle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.instInfiniteInitialCell
attribute [-simp] _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.StageSequence.limitTower_region _root_.Schoenflies.StageSequence.limitTower_region' _root_.Schoenflies.TargetSegmentCover.mem_openTargetEdgePieces
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The initial distinguished outer graph is a simple cycle

Reverse finite transfer ultimately needs only the local fact that at most two distinguished
outer edges meet at a vertex. `Schoenflies.GeneratedStructure.outerEdgesFormCycle` propagates
the stronger and more natural invariant that the complete outer edge set is one simple cycle.
This module supplies its base case for the concrete initial hexagon.

## Blueprint

* `Schoenflies.outerEdgesFormCycle_initialStructure` — the distinguished outer graph of the
  initial matched cellulation is its six-edge simple cycle.
-/

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

/-- The initial distinguished outer edge set is exactly the six-edge hexagonal cycle. -/
theorem outerEdgesFormCycle_initialStructure : initialStructure.OuterEdgesFormCycle := by
  refine ⟨.edge 0, .vert 0, .vert 1,
    [.edge 5, .edge 4, .edge 3, .edge 2, .edge 1], ?_, ?_⟩
  · exact ⟨initOuter_isLink_edge 0, isPath_initOuter_complement, by simp⟩
  · ext c
    change c ∈ InitialCell.outerEdges ↔
      c ∈ [InitialCell.edge 0, .edge 5, .edge 4, .edge 3, .edge 2, .edge 1]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, rfl⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMesh
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.familySquare_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareGraph_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The anchored square mesh

The geometric core of Proposition `prop:anchored-square-mesh`, in vocabulary that exists today:
Part II's cellulations, `V_boundary` and fresh points `u(𝒜)` are not built here, so the mesh is
stated as a **finite plane graph with a straight-line drawing**, with the clauses of the
proposition as separate theorems about it.

## The construction

`squareMesh δ fresh anchors` is `meshCount δ` concentric ring frames of radii
`1/N, 2/N, …, 1` inside `Q = [-1,1]²`, together with one full-length radial spoke
`[z, N⁻¹ • z]` at each fresh boundary point `z`. The list of segments is handed to
`overlayGraph` (Lemma 3.7), which subdivides at every crossing; the anchors are added to the
cut points, which is what makes each of them a vertex.

**This is not literally the blueprint's construction, and the difference is deliberate.** The
blueprint has one collar `λ ≤ ‖x‖∞ ≤ 1` plus a rectangular grid filling `λQ`. Here the collar
is repeated `N` times and there is no grid at all: the innermost square `N⁻¹ Q` is a *single*
cell, of diameter `2√2/N < δ`. That removes the "choose fine enough horizontal and vertical
coordinates, including the four corners and all the points `λ z_i`" step entirely, and makes
the whole mesh radial, so that one estimate — `‖tz - sw‖ ≤ t‖z - w‖ + |t - s|‖w‖`, the
blueprint's own — covers every cell. Nothing downstream can tell the difference: the clauses
are the interface.

The blueprint's cyclic ordering of the fresh points is likewise gone. Where it says "choose
`z_0, …, z_{m-1}` in cyclic order so that each boundary arc between consecutive ones has
diameter `< δ/4`", this module takes the order-free consequence as a hypothesis,
`FreshDense fresh δ`: *every connected subset of `S` avoiding all the fresh points has diameter
at most `δ/2`*. A set-level statement needs no ordering, and it is exactly what the blueprint's
own argument (parametrize `S` by a circle, cut it into small arcs, put one fresh point inside
each) produces.

## What is proved, and what is not

The clauses about faces, anchors, edges reaching `S` and connectedness of `|T| ∖ S` are proved
in full. Two gaps, both stated plainly:

* **The outer cycle is proved only as a point set.** `squareMesh_cover_outerEdges` says the
  edges whose segments lie on `S` occupy exactly `S`. That these edges form a **cycle** of the
  graph is *not* proved: it needs the fresh points, the anchors and the four corners put in
  cyclic order along `S`, which is precisely the ordering this construction was designed to
  avoid. A later module wanting the outer cycle must build it.
* **2-connectivity is not proved at all.** It is not present as a hypothesis either — a
  hypothesis restating the goal would be worthless. The route is the blueprint's: the innermost
  ring is a cycle, and each annulus between consecutive rings is added one rectangle at a time
  by `Graph.IsTwoConnected.union`, each added cycle sharing at least two vertices with what is
  already there. Nothing in this module obstructs it.

Connectedness of `|T| ∖ S` needs at least one fresh point (`hz₀ : z₀ ∈ fresh`): with no spokes
the rings are disjoint frames.

## Blueprint

* `ringSet`, `ringPieces`, `spokePiece`, `meshSegments` — the mesh as a list of segments.
* `meshGraph`, `squareMesh` — Proposition "Anchored square mesh", the construction itself.
* `FreshDense` — the order-free form of "consecutive fresh points bound an arc of diameter
  `< δ/4`".
* `squareMesh_face_small` — clause 1: every bounded 2-cell has diameter `< δ`, and lies in `Q`.
* `squareMesh_anchor_mem_vertexSet` — clause 2: every boundary vertex survives.
* `squareMesh_inner_edge_at_fresh`, `squareMesh_unique_inner_edge` — clauses 3 and 4: a new
  internal edge meeting `S` ends at a fresh point, and exactly one such edge is incident with
  each fresh point.
* `squareMesh_cover_outerEdges` — the point-set half of "`S` is the outer cycle" (see above).
* `squareMesh_isConnected_diff` — clause 6: `|T| ∖ S` is connected.
* `radial_diam_bound` — the blueprint's radial estimate, isolated from all graph language.
* `subdivide_covers_source`, `subdivide_end_of_mem` — two general facts about `subdivide` that
  belong in `Schoenflies/Subdivide.lean`.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### Rings: the frame of a square about the origin -/

/-! ### Radial segments

Every point of a segment between two multiples of `z` is itself a multiple of `z`, with the
coefficient running through the corresponding real segment. This is the only fact about spokes
the whole module uses: along a spoke the coefficient — equivalently, by
`supNorm_smul_of_mem_modelCurve`, the sup norm — is a faithful coordinate. -/

/-! ### Spokes -/

/-! ### Two more facts about `subdivide`

Both are general and belong beside the others in `Schoenflies/Subdivide.lean`; they are here
because that module is on `main`.

`subdivide_covers_source` refines `subdivide_cover`: a point of a *named* source piece lies on
a piece of the subdivision *inside that source*. Without the "inside that source" clause one
cannot tell, of a point where two sources cross, which of them the piece through it came from
— and the whole description of the mesh's edges is by their source.

`subdivide_end_of_mem` is the converse of `subdivide_avoids`: a cut point that lies on a source
piece is not merely absent from every interior, it is an **endpoint** of a piece inside that
source. That is what makes a prescribed point a vertex of the overlay graph. -/

/-! ### Enlarging the list of cut points

Both cut-point conditions ask only that certain points *be* in the list, so both survive
adding more. That is what lets the mesh prescribe extra vertices — the anchors — on top of the
cut points the overlay itself needs. -/

/-! ### The mesh, as a list of segments

`N` concentric ring frames of radii `1/N, 2/N, …, 1`, and one full-length radial spoke at each
fresh boundary point. There is no rectangular grid: the innermost region is the square of
radius `1/N`, which is a single cell of diameter `2√2/N`, so filling it is unnecessary once `N`
is large. That is the one deviation from the blueprint's construction, and it removes the whole
"choose horizontal and vertical coordinates" step. -/

/-! ### The mesh as a plane graph

The cut points are the ones `exists_cut_points` supplies for the mesh segments, *together with*
the prescribed anchors. Enlarging the list is harmless — `EndsAreCut.mono` and
`MeetsAreCut.mono` — and it is what makes each anchor a vertex. -/

/-! ### Clause 2: the anchors are vertices on `S` -/

/-! ### Clause 3: the outer edges occupy exactly `S`

The blueprint asks for `S` to be the union of the edge arcs of a *cycle*. What is proved here
is the point-set half: the edges whose arcs lie on `S` occupy exactly `S`. See the module
docstring. -/

/-! ### Clause 4: the edges that reach `S` from inside

An edge of the mesh that meets `S` without lying on it is a subsegment of a spoke, and it
touches `S` at that spoke's fresh point only. -/

/-! ### Clause 1: every bounded face is small

The estimate is the blueprint's, in radial coordinates. A connected set missing the mesh
misses every ring, so its sup norm — continuous, hence with a preconnected image in `ℝ` —
stays inside one open interval `(k/N, (k+1)/N)` between consecutive ring radii. Inside the
innermost square that is already the whole bound; outside it the radial projection
`x ↦ ‖x‖∞⁻¹ • x` maps the set into `S`, connectedly, and away from every fresh point, because
a point projecting to a fresh point lies on that point's spoke. The blueprint's

  `‖x - y‖ ≤ ‖tz - tw‖ + ‖tw - sw‖ < δ/4 + δ/4 + δ/4`

is then `t‖z - w‖ + |t - s|‖w‖`, with `‖z - w‖` controlled by `FreshDense` and `|t - s|` by
one ring thickness. -/

/-! ### Clause 5: the mesh minus `S` is connected

The inner rings and the spokes-minus-their-outer-endpoint are each connected, every inner ring
meets every spoke, and every spoke meets the innermost ring. So a single point of the innermost
ring reaches everything, which is what `isPreconnected_of_forall` asks for. At least one fresh
point is needed: with no spokes the rings are disjoint circles. -/

/-! ### The mesh of a given size

`meshCount δ` rings make both the innermost square and one ring thickness small compared with
`δ`; `2 √2 < δ N` is the single inequality the whole diameter estimate rests on. -/

/-- The mesh occupies a subset of `Q`. -/
theorem squareMesh_pointSet_subset {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing ⊆ Plane.closedSquare 0 1 := by
  rw [squareMesh_pointSet]
  exact cover_meshSegments_subset (two_le_meshCount δ) hfresh

/-- **Clause 5.** The mesh minus `S` is connected. -/
theorem squareMesh_isConnected_diff {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) {z₀ : Plane}
    (hz₀ : z₀ ∈ fresh) :
    IsConnected
      (Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing \ modelCurve) := by
  rw [squareMesh_pointSet]
  exact isConnected_cover_diff_modelCurve (two_le_meshCount δ) hfresh hz₀

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMeshClosed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.extendOverlay_finite
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Graph.traceGraph_isLink _root_.Graph.traceGraph_vertexSet _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.EarStepData.pair_src _root_.Schoenflies.EarStepData.pair_tgt _root_.Schoenflies.GeneratedPair.split_str _root_.Schoenflies.GeneratedPair.subdivide_src _root_.Schoenflies.GeneratedPair.subdivide_tgt _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.StageSequence.limitTower_region _root_.Schoenflies.StageSequence.limitTower_region' _root_.Schoenflies.TargetEarStepData.pair_src _root_.Schoenflies.TargetEarStepData.pair_tgt _root_.Schoenflies.TargetSegmentCover.mem_openTargetEdgePieces _root_.Schoenflies.TargetSegmentCover.mem_squareMeshPieces _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.mem_currentOverlayPieces _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The anchored square mesh, closed

`Schoenflies/SquareMesh.lean` builds `Schoenflies.squareMesh δ fresh anchors` and proves the
geometric clauses of `prop:anchored-square-mesh`; `Schoenflies/SquareMeshConnected.lean`,
`Schoenflies/SquareMeshFixed.lean` and `Schoenflies/LocalGrid.lean` add the grid combinatorics,
the outer cycle from an explicit path-subdivision hypothesis, and the degenerate cases. This
module proves that path-subdivision hypothesis for the mesh.

## The hypothesis that is discharged here

`Schoenflies.SubdividesToPath pieces points` says: *the overlay edges lying inside a source
segment are exactly the edges of a path of the overlay from one end of that segment to the
other.* `SquareMeshFixed.lean` states it as an explicit hypothesis, and its docstring says the
theorem does not exist on `main`.

It does exist. `Schoenflies.exists_incWalk_insideEdges` in `Schoenflies/SquareCycle.lean` is
exactly that statement in the vocabulary of `Graph.IsIncWalk` — a walk along which
`dist P.1 ·` strictly increases — and `Graph.IsIncWalk.isPath` turns it into a path. The two
modules were simply never in one import chain: `SquareCycle.lean` was imported only by
`Schoenflies/JordanClosed.lean`. `Schoenflies.subdividesToPath_of_overlay` is the four-line
bridge, allowing the results of `SquareMeshFixed.lean` to be applied directly to the mesh.

## The outer cycle, as data

`Schoenflies.meshGraph_outer_cycle` is existential — its own docstring says *"once that
hypothesis is discharged by a theorem exporting the chain as a `def`, this should be restated
with the cycle as data"*. That is done here: `outerCycleEdge`, `outerCycleStart`,
`outerCycleEnd`, `outerCycleThird` and `outerCycleDetour` are `def`s, and the three clauses
are separate lemmas about them. A consumer needing the outer cycle of the mesh takes these
five names, not an `∃` it has to destructure at every use.

## Clause 5, and the hypothesis that is actually true

Clause 5 — *the skeleton of `T` is 2-connected* — was absent from every earlier module, and for
a good reason: it is **false** for `Schoenflies.squareMesh δ fresh anchors` when `fresh` has
fewer than two distinct points (`Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton`),
and `Schoenflies.FreshDense fresh δ` alone does not repair it
(`Schoenflies.freshDense_not_isTwoConnected`). What repairs it is `FreshDense fresh δ` together
with `δ < 4`, which forces two distinct fresh points
(`Schoenflies.exists_two_distinct_fresh_of_freshDense`). The blueprint's caller uses
`δ = ε_n = 2⁻ⁿ`, far below `4`, so the hypothesis is free at the only call site.

The assembly is the blueprint's, with one correction. The blueprint says *"adding these finitely
many cycles one at a time"*, but the **first** addition cannot be a cycle: distinct rings of the
mesh are disjoint, so no two of them share the two vertices `lem:union-two-connected` needs. The
first addition is an **ear** — down the spoke at `z`, round the inner ring, back up the spoke at
`w` — and that is precisely where the two distinct fresh points are spent. After it, every
further ring shares the crossing points `r • z ≠ r • w` with the spokes and goes in by
`lem:union-two-connected`, and every further spoke is an ear between the outer and inner rings.
`Graph.IsTwoConnected.of_le_of_vertexSet_subset` then transfers 2-connectivity from the assembly
to the mesh, since every mesh vertex lies on a ring or on a spoke.

## The proposition, clause by clause

`prop:anchored-square-mesh` is exported as **data with its clauses as separate lemmas**: the
object is the `def` `Schoenflies.squareMesh δ fresh anchors`, and nothing is `∃`-packaged.

1. every 2-cell has diameter `< δ` — `Schoenflies.squareMesh_face_small`;
2. every anchor on `S` is a boundary vertex — `Schoenflies.squareMesh_anchor_mem_vertexSet`;
3. every new internal edge meeting `S` ends at a fresh point —
   `Schoenflies.squareMesh_inner_edge_at_fresh`;
4. exactly one such edge at each fresh point — `Schoenflies.squareMesh_unique_inner_edge`;
5. the skeleton is 2-connected — **`Schoenflies.squareMesh_isTwoConnected`** (this module);
6. `|T| ∖ S` is connected — `Schoenflies.squareMesh_isConnected_diff`.

and the outer cycle, which `def:admissible-graph` and every downstream consumer need as a
genuine cycle rather than a point set — `Schoenflies.squareMesh_isLongCycle_outerCycle`,
`Schoenflies.squareMesh_outerCycle_edgesCover` (this module).

## Blueprint

* `subdividesToPath_of_overlay`, `meshSubdividesToPath` — `lem:polygonal-overlay`: the
  subdivision of one source segment is a path of the overlay. This discharges
  `Schoenflies.SubdividesToPath`.
* `meshGraph_outer_cycle_of_mem_modelCurve`, `squareMesh_outer_cycle` —
  `prop:anchored-square-mesh` clause 3 as a **cycle**, with no hypothesis beyond `fresh ⊆ S`.
* `outerCycleEdge`, `outerCycleStart`, `outerCycleEnd`, `outerCycleThird`, `outerCycleDetour`,
  `squareMesh_isLongCycle_outerCycle`, `squareMesh_outerCycle_subset_modelCurve`,
  `squareMesh_outerCycle_edgesCover` — the same cycle as data with its clauses as lemmas.
* `rsideT`/`rsideL`/`rsideB`/`rsideR` and `meshGraph_ring_cycle` — the outer-cycle argument at
  every radius: each ring of the mesh is a long cycle occupying exactly that ring.
* `ringGraph`, `ringGraph_isTwoConnected`, `mem_vertexSet_ringGraph` — each ring as a named
  2-connected subgraph, via `Schoenflies.squareGraph` at centre `0`.
* `spokePiece_inter_ringSet`, `smul_mem_meshPoints`, `smul_mem_vertexSet_ringGraph` —
  the crossing points `r • z` as vertices, from the `MeetsAreCut` clause of `meshPoints`.
* `spokeWalk`, `spokeGraph` — each spoke as a path of the mesh.
* `meshEar`, `meshEar_isPath`, `meshCore_isTwoConnected` — `lem:subdivision-ear-preserve` (b):
  the ear that joins the outer ring to the inner one.
* `attachRings`, `attachSpokes` and their 2-connectivity — `lem:union-two-connected` and
  `lem:subdivision-ear-preserve` iterated, the blueprint's *"adding these finitely many cycles
  one at a time"*.
* `meshGraph_isTwoConnected`, `squareMesh_isTwoConnected` — `prop:anchored-square-mesh`
  clause 5.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### `SubdividesToPath` is a theorem

The membership clause of `Schoenflies.SubdividesToPath` and the membership clause of
`Schoenflies.insideEdges` are the same statement: `Q ∈ E(overlayGraph pieces points)` unfolds
to `Q ∈ overlayPieces pieces points` by `Iff.rfl`. So the only work is to turn the increasing
walk into a path, which `Graph.IsIncWalk.isPath` does. -/

/-- **The subdivision of a source segment is a path of the overlay.** This is
`Schoenflies.SubdividesToPath`, the hypothesis `Schoenflies/SquareMeshFixed.lean` carries
through all of its results, proved from `Schoenflies.exists_incWalk_insideEdges`. -/
theorem subdividesToPath_of_overlay {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) : SubdividesToPath pieces points := by
  intro P hP hPnd
  obtain ⟨W, hW, hinc⟩ := exists_incWalk_insideEdges hnd hEnds hMeets hP hPnd
  exact ⟨W, hinc.isPath, hW⟩

/-- The mesh's own instance of `Schoenflies.SubdividesToPath`. -/
theorem meshSubdividesToPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors) :=
  subdividesToPath_of_overlay (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)

/-! ### The outer cycle, with no hypothesis -/

/-! ### The outer cycle as data

Five `def`s and three lemmas, replacing the five-fold existential above. The `dite` is what
makes the definition total: the hypothesis `fresh ⊆ S` is not available inside a `def`, so the
data is junk when it fails and the lemmas carry the hypothesis. -/

/-! ### The four sides of a ring of arbitrary radius

`Schoenflies/SquareMeshFixed.lean` names the four sides of the *outer* ring — `sideT`, `sideL`,
`sideB`, `sideR` — and proves the handful of coordinate facts that the outer-cycle argument
runs on. Every inner ring needs the same facts, so they are restated here with the radius as a
parameter; `rsideT 1 = sideT` and so on, definitionally. -/

/-- Every side of every ring of the mesh is a mesh segment. -/
theorem ring_ringPieces_mem {N : ℕ} {fresh : List Plane} {r : ℝ} (hr : r ∈ meshRadii N)
    {R : Piece} (hR : R ∈ ringPieces r) : R ∈ meshSegments N fresh :=
  mem_meshSegments.2 (Or.inl ⟨r, hr, hR⟩)

/-! ### Every ring of the mesh is a cycle

`Schoenflies.meshGraph_outer_cycle` proves this for the outer ring, `r = 1`, and every step of
its proof is about the four sides of that ring and nothing else. With the sides of a ring of
arbitrary radius now available, the same argument runs verbatim at every radius: the four sides
are four overlay paths, three concatenations glue them into one path once round the ring, and
the last edge of the fourth is peeled off to close the cycle.

This is the theorem the blueprint's *"adding these finitely many cycles one at a time"* needs
for the inner rings, and which `Schoenflies/SquareMeshFixed.lean` names as missing. -/


/-! ### Each ring of the mesh, as a named 2-connected subgraph

`Schoenflies/SquareCycle.lean` proves that the part of *any* polygonal overlay lying on the
boundary of a square whose four sides are among the overlay's source segments is a long cycle,
and is 2-connected — at any centre and any positive radius. The rings of the mesh are exactly
that, at centre `0`: `squarePieces 0 r` and `ringPieces r` are the same list. So each ring comes
with a name, `ringGraph`, a 2-connectivity proof, and the two membership lemmas the assembly of
clause 5 needs, at no cost. -/

/-- The four sides of the square of radius `r` about the origin are the four sides of the ring
of radius `r`: the two lists are equal, entry for entry. -/
theorem squarePieces_zero (r : ℝ) : squarePieces 0 r = ringPieces r := by
  simp [squarePieces, ringPieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE]

/-- The frontier of the closed square of radius `r` about the origin is the ring of radius
`r`. -/
theorem frontier_closedSquare_zero {r : ℝ} (hr : 0 ≤ r) :
    frontier (Plane.closedSquare 0 r) = ringSet r := by
  rw [← cover_squarePieces 0 hr, squarePieces_zero, cover_ringPieces hr]

/-- **The ring of radius `r` of the mesh, as a subgraph**: the mesh edges lying on that ring. -/
noncomputable def ringGraph (N : ℕ) (fresh anchors : List Plane) (r : ℝ) : Graph Plane Piece :=
  squareGraph (meshSegments N fresh) (meshPoints N fresh anchors) 0 r

theorem ringGraph_le (N : ℕ) (fresh anchors : List Plane) (r : ℝ) :
    ringGraph N fresh anchors r ≤ meshGraph N fresh anchors :=
  squareGraph_le

/-- The sides of the ring of radius `r` are mesh segments, for every radius the mesh uses. -/
theorem squarePieces_zero_subset_meshSegments {N : ℕ} {fresh : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) : ∀ P ∈ squarePieces 0 r, P ∈ meshSegments N fresh := by
  rw [squarePieces_zero]
  exact fun P hP => ring_ringPieces_mem hr hP

/-- **Every ring of the mesh is a 2-connected subgraph.** -/
theorem ringGraph_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) : (ringGraph N fresh anchors r).IsTwoConnected :=
  squareGraph_isTwoConnected (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)
    (meshRadii_pos hN hr) (squarePieces_zero_subset_meshSegments hr)

/-- **A cut point of the mesh lying on a ring is a vertex of that ring.** This is what makes the
crossing points of the spokes with the rings usable as the shared vertices of
`lem:union-two-connected`. -/
theorem mem_vertexSet_ringGraph {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) {y : Plane} (hy : y ∈ meshPoints N fresh anchors)
    (hyr : y ∈ ringSet r) : y ∈ V(ringGraph N fresh anchors r) :=
  mem_vertexSet_squareGraph (meshSegments_nondeg hN hfresh) (meshRadii_pos hN hr).le
    (squarePieces_zero_subset_meshSegments hr) hy
    (by rw [frontier_closedSquare_zero (meshRadii_pos hN hr).le]; exact hyr)


/-! ### Where a spoke crosses a ring

`Schoenflies/SquareMeshFixed.lean` records the crossing points `r • z` as the thing its
assembly of clause 5 lacked: *"the crossing points `r • z` as vertices (which needs the
`MeetsAreCut` clause of `meshPoints`)"*. That is what this section supplies. The sup norm is a
faithful coordinate along a spoke (`Schoenflies.supNorm_smul_of_mem_modelCurve`), so a spoke
meets the ring of radius `r` in the single point `r • z`; a singleton meet forces both ends of
the `MeetsAreCut` segment to be that point; and `mem_vertexSet_ringGraph` then makes it a
vertex of the ring. -/

/-- **A spoke meets a ring in exactly one point.** -/
theorem spokePiece_inter_ringSet {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve)
    {r : ℝ} (hr : r ∈ meshRadii N) : (spokePiece N z).seg ∩ ringSet r = {r • z} := by
  have hrpos : 0 < r := meshRadii_pos hN hr
  ext x
  rw [spokePiece_seg hN]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hx⟩
    have : t = r := by
      rw [← supNorm_smul_of_mem_modelCurve (le_trans (inv_cast_pos hN).le ht.1) hz]
      exact hx
    simp [this]
  · rintro rfl
    exact ⟨⟨r, ⟨inv_le_of_mem_meshRadii hN hr, meshRadii_le_one hN hr⟩, rfl⟩,
      supNorm_smul_of_mem_modelCurve hrpos.le hz⟩

theorem smul_mem_ringSet {r : ℝ} (hr : 0 ≤ r) {z : Plane} (hz : z ∈ modelCurve) :
    r • z ∈ ringSet r := supNorm_smul_of_mem_modelCurve hr hz

/-- **Every crossing point of a spoke with a ring is a cut point of the mesh.** The meet of the
spoke with the side of the ring through the crossing point is the single point `r • z`, and
`MeetsAreCut` returns a segment with both ends among the cut points; a segment equal to a
singleton has both ends there. -/
theorem smul_mem_meshPoints {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) : r • z ∈ meshPoints N fresh anchors := by
  have hzm : z ∈ modelCurve := hfresh z hz
  have hrpos : 0 < r := meshRadii_pos hN hr
  -- the side of the ring through the crossing point
  have hmemring : r • z ∈ cover (ringPieces r) := by
    rw [cover_ringPieces hrpos.le]; exact smul_mem_ringSet hrpos.le hzm
  obtain ⟨Q, hQ, hxQ⟩ := mem_cover_iff.1 hmemring
  set P : Piece := spokePiece N z with hP
  have hPmem : P ∈ meshSegments N fresh := spokePiece_mem_meshSegments hz
  have hQmem : Q ∈ meshSegments N fresh := ring_ringPieces_mem hr hQ
  have hQring : Q.seg ⊆ ringSet r := ringPieces_seg_subset hrpos.le hQ
  -- the spoke is not a ring side: its two ends have different sup norms
  have hPQ : P ≠ Q := by
    intro h
    have h1 : Plane.supNorm z = r := hQring (h ▸ left_mem_segment ℝ P.1 P.2)
    have h2 : Plane.supNorm (((N : ℝ)⁻¹) • z) = r := hQring (h ▸ right_mem_segment ℝ P.1 P.2)
    rw [supNorm_smul_of_mem_modelCurve (inv_cast_pos hN).le hzm] at h2
    rw [show Plane.supNorm z = 1 from hzm] at h1
    exact absurd (h2.trans h1.symm) (ne_of_lt (inv_cast_lt_one hN))
  -- the meet is the crossing point, and nothing else
  have hmeetsub : meetOf P Q ⊆ {r • z} := by
    rw [← spokePiece_inter_ringSet hN hzm hr]
    exact fun x hx => ⟨hx.1, hQring hx.2⟩
  have hmeetmem : r • z ∈ meetOf P Q :=
    ⟨((spokePiece_inter_ringSet hN hzm hr).symm ▸ rfl : r • z ∈ (spokePiece N z).seg ∩ ringSet r).1,
      hxQ⟩
  obtain ⟨u, v, huv, hu, -⟩ :=
    meshPoints_meetsAreCut N fresh anchors P hPmem Q hQmem hPQ ⟨_, hmeetmem⟩
  have : u = r • z := hmeetsub (huv ▸ left_mem_segment ℝ u v)
  exact this ▸ hu

/-- **The crossing point is a vertex of the ring it lies on.** -/
theorem smul_mem_vertexSet_ringGraph {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) : r • z ∈ V(ringGraph N fresh anchors r) :=
  mem_vertexSet_ringGraph hN hfresh hr (smul_mem_meshPoints hN hfresh anchors hz hr)
    (smul_mem_ringSet (meshRadii_pos hN hr).le (hfresh z hz))

/-- Two distinct fresh points have distinct crossing points on every ring. -/
theorem smul_ne_smul {r : ℝ} (hr : r ≠ 0) {z w : Plane} (hzw : z ≠ w) : r • z ≠ r • w := by
  intro h
  exact hzw (smul_right_injective Plane hr h)


/-! ### The spokes, as paths of the mesh

`Schoenflies.SubdividesToPath` — now a theorem — turns each spoke into a path of the mesh from
its outer end `z` to its inner end `N⁻¹ • z`. The path is exported as data, `spokeWalk`, so
that the assembly can name it; and the crossing points are shown to be among the vertices it
visits, which is what makes each ring attachable at two of them. -/

/-- **A cut point lying on a source segment is a vertex of the path that subdivides it.** The
edges of the path cover the segment, and a cut point is interior to no edge of an overlay, so
it is an *end* of one of them. -/
theorem mem_walkVertices_of_mem_points {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {P : Piece} (hP : P ∈ pieces) {W : List Piece}
    (hW : ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg))
    {q : Plane} (hq : q ∈ points) (hqP : q ∈ P.seg) :
    q ∈ (overlayGraph pieces points).walkVertices P.1 W := by
  have hcov : Graph.edgesCover segmentDrawing W = P.seg := edgesCover_eq_seg hP hW
  rw [← hcov] at hqP
  obtain ⟨Q, hQ, hqQ⟩ := Graph.mem_edgesCover_iff.1 hqP
  rw [edgeArc_segmentDrawing] at hqQ
  have hQmem : Q ∈ overlayPieces pieces points := ((hW Q).1 hQ).1
  have hint : q ∉ Q.interior := overlayPieces_avoids hnd q hq Q hQmem
  have hend : q = Q.1 ∨ q = Q.2 := by
    by_contra hcon
    push Not at hcon
    exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hqQ)
  exact Graph.mem_walkVertices_of_mem_covered
    (Graph.mem_coveredVertices hQ (overlayGraph_inc hQmem hend))

open scoped Classical in
/-- **The subdivision of the spoke at a fresh point, as data**: the list of mesh edges lying
inside `spokePiece N z`, in order from `z` inwards. Junk when `z` is not a fresh point of the
model curve. -/
noncomputable def spokeWalk (N : ℕ) (fresh anchors : List Plane) (z : Plane) : List Piece :=
  if h : ∃ W : List Piece,
      (meshGraph N fresh anchors).IsPath z W (((N : ℝ)⁻¹) • z) ∧
        ∀ Q, Q ∈ W ↔ (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg)
    then h.choose else []

theorem spokeWalk_spec {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    (meshGraph N fresh anchors).IsPath z (spokeWalk N fresh anchors z) (((N : ℝ)⁻¹) • z) ∧
      ∀ Q, Q ∈ spokeWalk N fresh anchors z ↔
        (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg) := by
  classical
  have h : ∃ W : List Piece,
      (meshGraph N fresh anchors).IsPath z W (((N : ℝ)⁻¹) • z) ∧
        ∀ Q, Q ∈ W ↔ (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg) :=
    meshSubdividesToPath hN hfresh anchors _ (spokePiece_mem_meshSegments hz)
      (spokePiece_nondeg hN (hfresh z hz))
  rw [spokeWalk, dif_pos h]
  exact h.choose_spec

theorem spokeWalk_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    (meshGraph N fresh anchors).IsPath z (spokeWalk N fresh anchors z) (((N : ℝ)⁻¹) • z) :=
  (spokeWalk_spec hN hfresh anchors hz).1

theorem spokeWalk_seg_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {Q : Piece} (hQ : Q ∈ spokeWalk N fresh anchors z) : Q.seg ⊆ (spokePiece N z).seg :=
  (((spokeWalk_spec hN hfresh anchors hz).2 Q).1 hQ).2

/-- **Every crossing point on a spoke is a vertex the spoke's path visits.** -/
theorem smul_mem_walkVertices_spokeWalk {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) :
    r • z ∈ (meshGraph N fresh anchors).walkVertices z (spokeWalk N fresh anchors z) := by
  have hmem : r • z ∈ (spokePiece N z).seg :=
    ((spokePiece_inter_ringSet hN (hfresh z hz) hr).symm.subset rfl).1
  exact mem_walkVertices_of_mem_points (meshSegments_nondeg hN hfresh)
    (spokePiece_mem_meshSegments hz) (spokeWalk_spec hN hfresh anchors hz).2
    (smul_mem_meshPoints hN hfresh anchors hz hr) hmem

/-- Every vertex the spoke's path visits lies on the spoke. -/
theorem walkVertices_spokeWalk_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {x : Plane}
    (hx : x ∈ (meshGraph N fresh anchors).walkVertices z (spokeWalk N fresh anchors z)) :
    x ∈ (spokePiece N z).seg :=
  walkVertices_subset_of_edges (left_mem_segment ℝ _ _)
    (fun _ hQ => spokeWalk_seg_subset hN hfresh anchors hz hQ) hx


/-! ### The core: outer ring, two spokes, inner ring

The blueprint assembles clause 5 by *"adding these finitely many cycles one at a time"*, but
the first addition cannot be a cycle: distinct rings of the mesh are disjoint, so no two of
them share the two vertices `lem:union-two-connected` asks for. What joins them is an **ear** —
a path with both ends on the outer ring — and the only such path runs down one spoke, round
part of the inner ring, and back up another spoke. That is why clause 5 needs **two distinct
fresh points**, and why it is false with fewer
(`Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton`).

Once that ear is in place the inner ring shares the two crossing points `N⁻¹ • z` and
`N⁻¹ • w` with it, and `Graph.IsTwoConnected.union` applies; from then on every further ring
shares `r • z` and `r • w`, and every further spoke is an ear between the outer and inner
rings. -/

/-- **Distinct spokes are disjoint** — the blueprint's *"two radial segments in the annulus can
meet only if they lie on the same ray, and then their endpoints on `S` are equal"*. -/
theorem spokePiece_disjoint {N : ℕ} (hN : 2 ≤ N) {z w : Plane} (hz : z ∈ modelCurve)
    (hw : w ∈ modelCurve) (hzw : z ≠ w) {x : Plane} (hxz : x ∈ (spokePiece N z).seg)
    (hxw : x ∈ (spokePiece N w).seg) : False := by
  rw [spokePiece_seg hN] at hxz hxw
  obtain ⟨t, ht, hxt⟩ := hxz
  obtain ⟨s, hs, hxs⟩ := hxw
  have hxt' : t • z = x := hxt
  have hxs' : s • w = x := hxs
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (inv_cast_pos hN) ht.1
  have hspos : (0 : ℝ) ≤ s := le_trans (inv_cast_pos hN).le hs.1
  have h1 : Plane.supNorm x = t := by
    rw [← hxt']; exact supNorm_smul_of_mem_modelCurve htpos.le hz
  have h2 : Plane.supNorm x = s := by
    rw [← hxs']; exact supNorm_smul_of_mem_modelCurve hspos hw
  rw [show s = t from by rw [← h2, h1]] at hxs'
  exact hzw (smul_right_injective Plane (ne_of_gt htpos) (hxt'.trans hxs'.symm))

theorem ringGraph_edge_seg_subset {N : ℕ} {fresh anchors : List Plane} {r : ℝ} (hr : 0 ≤ r)
    {Q : Piece} (hQ : Q ∈ E(ringGraph N fresh anchors r)) : Q.seg ⊆ ringSet r := by
  rw [← frontier_closedSquare_zero hr]
  exact (mem_edgeSet_squareGraph_iff.1 hQ).2

open scoped Classical in
/-- An arc of the ring of radius `r` between two of its vertices, as data. The ring is
2-connected, hence connected, so such a path exists; *which* of the two arcs is chosen does not
matter — only that it is a path inside the ring. -/
noncomputable def ringArc (N : ℕ) (fresh anchors : List Plane) (r : ℝ) (a b : Plane) :
    List Piece :=
  if h : ∃ P : List Piece, (ringGraph N fresh anchors r).IsPath a P b then h.choose else []

theorem ringArc_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) {a b : Plane} (ha : a ∈ V(ringGraph N fresh anchors r))
    (hb : b ∈ V(ringGraph N fresh anchors r)) :
    (ringGraph N fresh anchors r).IsPath a (ringArc N fresh anchors r a b) b := by
  classical
  have h : ∃ P : List Piece, (ringGraph N fresh anchors r).IsPath a P b :=
    (ringGraph_isTwoConnected hN hfresh anchors hr).connected.exists_isPath ha hb
  rw [ringArc, dif_pos h]
  exact h.choose_spec

/-- **The ear**: down the spoke at `z`, round the inner ring, and back up the spoke at `w`. -/
noncomputable def meshEar (N : ℕ) (fresh anchors : List Plane) (z w : Plane) : List Piece :=
  spokeWalk N fresh anchors z ++
    ringArc N fresh anchors ((N : ℝ)⁻¹) (((N : ℝ)⁻¹) • z) (((N : ℝ)⁻¹) • w) ++
    (spokeWalk N fresh anchors w).reverse

theorem meshEar_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshGraph N fresh anchors).IsPath z (meshEar N fresh anchors z w) w := by
  set G := meshGraph N fresh anchors with hG
  set rmin : ℝ := ((N : ℝ)⁻¹) with hrmin
  have hrm : rmin ∈ meshRadii N := inv_mem_meshRadii hN
  have hrmpos : 0 < rmin := inv_cast_pos hN
  have hzm : z ∈ modelCurve := hfresh z hz
  have hwm : w ∈ modelCurve := hfresh w hw
  -- the three pieces
  have hP1 : G.IsPath z (spokeWalk N fresh anchors z) (rmin • z) :=
    spokeWalk_isPath hN hfresh anchors hz
  have hP3 : G.IsPath (rmin • w) (spokeWalk N fresh anchors w).reverse w :=
    (spokeWalk_isPath hN hfresh anchors hw).reverse
  have harc := ringArc_isPath hN hfresh anchors hrm
    (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
    (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)
  have hP2 : G.IsPath (rmin • z) (ringArc N fresh anchors rmin (rmin • z) (rmin • w))
      (rmin • w) := harc.mono (ringGraph_le N fresh anchors rmin)
  -- where each piece's vertices live
  have harcseg : ∀ Q ∈ ringArc N fresh anchors rmin (rmin • z) (rmin • w), Q.seg ⊆ ringSet rmin :=
    fun Q hQ => ringGraph_edge_seg_subset hrmpos.le (harc.isWalk.edgeSet_subset Q hQ)
  have hV2 : ∀ x ∈ G.walkVertices (rmin • z)
      (ringArc N fresh anchors rmin (rmin • z) (rmin • w)), x ∈ ringSet rmin :=
    fun x hx => walkVertices_subset_of_edges (smul_mem_ringSet hrmpos.le hzm) harcseg hx
  have hV3 : ∀ x ∈ G.walkVertices (rmin • w) (spokeWalk N fresh anchors w).reverse,
      x ∈ (spokePiece N w).seg := by
    refine fun x hx => walkVertices_subset_of_edges ?_ (fun Q hQ =>
      spokeWalk_seg_subset hN hfresh anchors hw (List.mem_reverse.1 hQ)) hx
    exact ((spokePiece_inter_ringSet hN hwm hrm).symm.subset rfl).1
  -- first append: the spoke at `z`, then the inner arc, meeting only at `rmin • z`
  have hp1 : G.IsPath z (spokeWalk N fresh anchors z ++
      ringArc N fresh anchors rmin (rmin • z) (rmin • w)) (rmin • w) := by
    refine hP1.append_of_disjoint hP2 fun x hx hx2 => ?_
    have hxs : x ∈ (spokePiece N z).seg :=
      walkVertices_spokeWalk_subset hN hfresh anchors hz hx
    have := (spokePiece_inter_ringSet hN hzm hrm).subset ⟨hxs, hV2 x hx2⟩
    exact this
  have hV1 : ∀ x ∈ G.walkVertices z (spokeWalk N fresh anchors z ++
      ringArc N fresh anchors rmin (rmin • z) (rmin • w)),
      x ∈ (spokePiece N z).seg ∪ ringSet rmin := by
    refine fun x hx => walkVertices_subset_of_edges (Or.inl (left_mem_segment ℝ _ _))
      (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    · exact (spokeWalk_seg_subset hN hfresh anchors hz h).trans Set.subset_union_left
    · exact (harcseg Q h).trans Set.subset_union_right
  -- second append: back up the spoke at `w`, meeting only at `rmin • w`
  refine hp1.append_of_disjoint hP3 fun x hx hx2 => ?_
  have hxw : x ∈ (spokePiece N w).seg := hV3 x hx2
  rcases hV1 x hx with h | h
  · exact absurd (spokePiece_disjoint hN hzm hwm hzw h hxw) not_false
  · exact (spokePiece_inter_ringSet hN hwm hrm).subset ⟨hxw, h⟩


/-! ### The assembly

`meshCore` is the outer ring, the ear, and the inner ring. `attachRings` then adds every ring
by `lem:union-two-connected` at the two crossing points `r • z ≠ r • w`, and `attachSpokes`
adds every remaining spoke by `lem:subdivision-ear-preserve` (b) — its two ends are `u` on the
outer ring and `N⁻¹ • u` on the inner one, both already present. Finally every vertex of the
mesh lies on a ring or on a spoke, so the assembled graph spans the mesh and
`Graph.IsTwoConnected.of_le_of_vertexSet_subset` transfers 2-connectivity to the mesh itself. -/

/-- The spoke at `u`, as a subgraph of the mesh. -/
noncomputable def spokeGraph (N : ℕ) (fresh anchors : List Plane) (u : Plane) :
    Graph Plane Piece :=
  (meshGraph N fresh anchors).pathGraphOf u (spokeWalk N fresh anchors u)

theorem spokeGraph_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh) :
    spokeGraph N fresh anchors u ≤ meshGraph N fresh anchors :=
  Graph.pathGraphOf_le (spokeWalk_isPath hN hfresh anchors hu).isWalk

/-- A crossing point on a ring other than the outer one is not the fresh point itself. -/
theorem smul_ne_self {N : ℕ} (hN : 2 ≤ N) {u : Plane} (hu : u ∈ modelCurve) {r : ℝ}
    (hr : r ∈ meshRadii N) (hr1 : r ≠ 1) : r • u ≠ u := by
  intro h
  have h1 : Plane.supNorm (r • u) = r :=
    supNorm_smul_of_mem_modelCurve (meshRadii_pos hN hr).le hu
  rw [h, show Plane.supNorm u = 1 from hu] at h1
  exact hr1 h1.symm

/-- An inner crossing point is *covered* by the spoke's path — it is an end of one of its
edges, not merely its source. -/
theorem smul_mem_coveredVertices_spokeWalk {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) (hr1 : r ≠ 1) :
    r • u ∈ (meshGraph N fresh anchors).coveredVertices (spokeWalk N fresh anchors u) := by
  rcases Graph.mem_walkVertices_iff.1
    (smul_mem_walkVertices_spokeWalk hN hfresh anchors hu hr) with h | h
  · exact absurd h (smul_ne_self hN (hfresh u hu) hr hr1)
  · exact h

/-- **The core**: outer ring, ear, inner ring. -/
noncomputable def meshCore (N : ℕ) (fresh anchors : List Plane) (z w : Plane) :
    Graph Plane Piece :=
  ((ringGraph N fresh anchors 1).union
      ((meshGraph N fresh anchors).pathGraphOf z (meshEar N fresh anchors z w))).union
    (ringGraph N fresh anchors ((N : ℝ)⁻¹))

theorem meshCore_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    meshCore N fresh anchors z w ≤ meshGraph N fresh anchors :=
  Graph.union_le
    (Graph.union_le (ringGraph_le N fresh anchors 1)
      (Graph.pathGraphOf_le (meshEar_isPath hN hfresh anchors hz hw hzw).isWalk))
    (ringGraph_le N fresh anchors _)

/-- A fresh point is a vertex of the outer ring. -/
theorem mem_vertexSet_ringGraph_one {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh) :
    u ∈ V(ringGraph N fresh anchors 1) := by
  have := smul_mem_vertexSet_ringGraph hN hfresh anchors hu (one_mem_meshRadii hN)
  rwa [one_smul] at this

/-- **The core is 2-connected.** -/
theorem meshCore_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshCore N fresh anchors z w).IsTwoConnected := by
  set G := meshGraph N fresh anchors with hG
  set rmin : ℝ := ((N : ℝ)⁻¹) with hrmin
  have hrm : rmin ∈ meshRadii N := inv_mem_meshRadii hN
  have hear := meshEar_isPath hN hfresh anchors hz hw hzw
  have hearle : G.pathGraphOf z (meshEar N fresh anchors z w) ≤ G :=
    Graph.pathGraphOf_le hear.isWalk
  -- the ear, attached to the outer ring
  have h1 : ((ringGraph N fresh anchors 1).union
      (G.pathGraphOf z (meshEar N fresh anchors z w))).IsTwoConnected :=
    (ringGraph_isTwoConnected hN hfresh anchors (one_mem_meshRadii hN)).ear
      (Graph.Compatible.of_le_le (ringGraph_le N fresh anchors 1) hearle)
      hear.isPathGraph_pathGraphOf hzw
      (mem_vertexSet_ringGraph_one hN hfresh anchors hz)
      (mem_vertexSet_ringGraph_one hN hfresh anchors hw)
  -- the crossing points, which the ear visits
  have hrne : rmin ≠ 1 := (inv_cast_lt_one hN).ne
  have hmemz : rmin • z ∈ V(G.pathGraphOf z (meshEar N fresh anchors z w)) :=
    Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
      (fun _ hQ => List.mem_append_left _ (List.mem_append_left _ hQ))
      (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hz hrm hrne))
  have hmemw : rmin • w ∈ V(G.pathGraphOf z (meshEar N fresh anchors z w)) :=
    Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
      (fun _ hQ => List.mem_append_right _ (List.mem_reverse.2 hQ))
      (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hw hrm hrne))
  exact h1.union (Graph.Compatible.of_le_le
      (Graph.union_le (ringGraph_le N fresh anchors 1) hearle) (ringGraph_le N fresh anchors rmin))
    (ringGraph_isTwoConnected hN hfresh anchors hrm)
    (smul_ne_smul (ne_of_gt (inv_cast_pos hN)) hzw)
    (Or.inr hmemz) (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
    (Or.inr hmemw) (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)


/-! ### Adding every ring and every spoke -/

/-- Both crossing points of a spoke lie on the ear, whichever ring they belong to. -/
theorem smul_mem_walkVertices_meshEar {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) {r : ℝ} (hr : r ∈ meshRadii N) :
    r • z ∈ (meshGraph N fresh anchors).walkVertices z (meshEar N fresh anchors z w) ∧
      r • w ∈ (meshGraph N fresh anchors).walkVertices z (meshEar N fresh anchors z w) := by
  have hear := meshEar_isPath hN hfresh anchors hz hw hzw
  constructor
  · exact Graph.walkVertices_mono
      (fun _ hQ => List.mem_append_left _ (List.mem_append_left _ hQ))
      (smul_mem_walkVertices_spokeWalk hN hfresh anchors hz hr)
  · by_cases h1 : r = 1
    · rw [h1, one_smul]; exact hear.isWalk.target_mem_walkVertices
    · exact Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
        (fun _ hQ => List.mem_append_right _ (List.mem_reverse.2 hQ))
        (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hw hr h1))

/-- The rings of the mesh, attached one at a time — `lem:union-two-connected` iterated. -/
noncomputable def attachRings (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece) :
    List ℝ → Graph Plane Piece
  | [] => K
  | r :: rs => (attachRings N fresh anchors K rs).union (ringGraph N fresh anchors r)

/-- The spokes of the mesh, attached one at a time — `lem:subdivision-ear-preserve` (b)
iterated. -/
noncomputable def attachSpokes (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece) :
    List Plane → Graph Plane Piece
  | [] => K
  | u :: us => (attachSpokes N fresh anchors K us).union (spokeGraph N fresh anchors u)

theorem le_attachRings (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece)
    (l : List ℝ) : K ≤ attachRings N fresh anchors K l := by
  induction l with
  | nil => exact le_refl K
  | cons r rs ih => exact ih.trans (Graph.left_le_union _ _)

theorem le_attachSpokes (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece)
    (l : List Plane) : K ≤ attachSpokes N fresh anchors K l := by
  induction l with
  | nil => exact le_refl K
  | cons u us ih => exact ih.trans (Graph.left_le_union _ _)

theorem attachRings_le {N : ℕ} {fresh anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) (l : List ℝ) :
    attachRings N fresh anchors K l ≤ meshGraph N fresh anchors := by
  induction l with
  | nil => exact hK
  | cons r rs ih => exact Graph.union_le ih (ringGraph_le _ _ _ _)

theorem attachSpokes_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) {l : List Plane} (hl : ∀ u ∈ l, u ∈ fresh) :
    attachSpokes N fresh anchors K l ≤ meshGraph N fresh anchors := by
  induction l with
  | nil => exact hK
  | cons u us ih =>
    exact Graph.union_le (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (spokeGraph_le hN hfresh anchors (hl u List.mem_cons_self))

theorem ringGraph_le_attachRings {N : ℕ} {fresh anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) {l : List ℝ} {r : ℝ} (hr : r ∈ l) :
    ringGraph N fresh anchors r ≤ attachRings N fresh anchors K l := by
  induction l with
  | nil => exact absurd hr (List.not_mem_nil)
  | cons r' rs ih =>
    rcases List.mem_cons.1 hr with rfl | h
    · exact (Graph.Compatible.of_le_le (attachRings_le hK rs)
        (ringGraph_le N fresh anchors r)).right_le_union
    · exact (ih h).trans (Graph.left_le_union _ _)

theorem spokeGraph_le_attachSpokes {N : ℕ} {fresh anchors : List Plane}
    {K : Graph Plane Piece} (hK : K ≤ meshGraph N fresh anchors) {l : List Plane} {u : Plane}
    (hN : 2 ≤ N) (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (hl : ∀ x ∈ l, x ∈ fresh)
    (hu : u ∈ l) : spokeGraph N fresh anchors u ≤ attachSpokes N fresh anchors K l := by
  induction l with
  | nil => exact absurd hu (List.not_mem_nil)
  | cons u' us ih =>
    rcases List.mem_cons.1 hu with rfl | h
    · exact (Graph.Compatible.of_le_le
        (attachSpokes_le hN hfresh hK fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (spokeGraph_le hN hfresh anchors (hl u List.mem_cons_self))).right_le_union
    · exact (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h).trans (Graph.left_le_union _ _)

theorem attachRings_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) {K : Graph Plane Piece}
    (hK : K.IsTwoConnected) (hKle : K ≤ meshGraph N fresh anchors)
    (hzK : ∀ r ∈ meshRadii N, r • z ∈ V(K)) (hwK : ∀ r ∈ meshRadii N, r • w ∈ V(K))
    {l : List ℝ} (hl : ∀ r ∈ l, r ∈ meshRadii N) :
    (attachRings N fresh anchors K l).IsTwoConnected := by
  induction l with
  | nil => exact hK
  | cons r rs ih =>
    have hrm : r ∈ meshRadii N := hl r List.mem_cons_self
    have hacc := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hmono := (le_attachRings N fresh anchors K rs).vertexSet_mono
    exact hacc.union (Graph.Compatible.of_le_le
        (attachRings_le hKle rs) (ringGraph_le N fresh anchors r))
      (ringGraph_isTwoConnected hN hfresh anchors hrm)
      (smul_ne_smul (ne_of_gt (meshRadii_pos hN hrm)) hzw)
      (hmono (hzK r hrm)) (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
      (hmono (hwK r hrm)) (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)

theorem attachSpokes_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {K : Graph Plane Piece}
    (hK : K.IsTwoConnected) (hKle : K ≤ meshGraph N fresh anchors)
    (houter : ∀ u ∈ fresh, u ∈ V(K)) (hinner : ∀ u ∈ fresh, ((N : ℝ)⁻¹) • u ∈ V(K))
    {l : List Plane} (hl : ∀ u ∈ l, u ∈ fresh) :
    (attachSpokes N fresh anchors K l).IsTwoConnected := by
  induction l with
  | nil => exact hK
  | cons u us ih =>
    have hu : u ∈ fresh := hl u List.mem_cons_self
    have hacc := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hmono := (le_attachSpokes N fresh anchors K us).vertexSet_mono
    refine hacc.ear (Graph.Compatible.of_le_le
        (attachSpokes_le hN hfresh hKle fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (spokeGraph_le hN hfresh anchors hu))
      (spokeWalk_isPath hN hfresh anchors hu).isPathGraph_pathGraphOf ?_
      (hmono (houter u hu)) (hmono (hinner u hu))
    exact fun h => smul_ne_self hN (hfresh u hu) (inv_mem_meshRadii hN)
      (inv_cast_lt_one hN).ne h.symm


/-! ### Clause 5: the skeleton of the mesh is 2-connected -/

/-- **The whole mesh, assembled**: the core, then every ring, then every spoke. -/
noncomputable def meshAssembly (N : ℕ) (fresh anchors : List Plane) (z w : Plane) :
    Graph Plane Piece :=
  attachSpokes N fresh anchors
    (attachRings N fresh anchors (meshCore N fresh anchors z w) (meshRadii N)) fresh

theorem meshAssembly_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    meshAssembly N fresh anchors z w ≤ meshGraph N fresh anchors :=
  attachSpokes_le hN hfresh
    (attachRings_le (meshCore_le hN hfresh anchors hz hw hzw) (meshRadii N)) fun _ hx => hx

theorem meshAssembly_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshAssembly N fresh anchors z w).IsTwoConnected := by
  have hcore := meshCore_isTwoConnected hN hfresh anchors hz hw hzw
  have hcorele := meshCore_le hN hfresh anchors hz hw hzw
  -- both crossing points of every ring lie on the ear, hence in the core
  have hzK : ∀ r ∈ meshRadii N, r • z ∈ V(meshCore N fresh anchors z w) := fun r hr =>
    Or.inl (Or.inr (smul_mem_walkVertices_meshEar hN hfresh anchors hz hw hzw hr).1)
  have hwK : ∀ r ∈ meshRadii N, r • w ∈ V(meshCore N fresh anchors z w) := fun r hr =>
    Or.inl (Or.inr (smul_mem_walkVertices_meshEar hN hfresh anchors hz hw hzw hr).2)
  have hrings := attachRings_isTwoConnected hN hfresh hz hw hzw hcore hcorele hzK hwK
    (l := meshRadii N) fun _ hx => hx
  refine attachSpokes_isTwoConnected hN hfresh hrings
    (attachRings_le hcorele (meshRadii N)) ?_ ?_ fun _ hx => hx
  · exact fun u hu => (le_attachRings N fresh anchors _ (meshRadii N)).vertexSet_mono
      (Or.inl (Or.inl (mem_vertexSet_ringGraph_one hN hfresh anchors hu)))
  · exact fun u hu => (le_attachRings N fresh anchors _ (meshRadii N)).vertexSet_mono
      (Or.inr (smul_mem_vertexSet_ringGraph hN hfresh anchors hu (inv_mem_meshRadii hN)))

/-- **The assembly spans the mesh.** Every vertex of the mesh is an end of an edge, every edge
lies inside a mesh segment, and a mesh segment is either a ring side — putting the vertex on
that ring — or a spoke, putting it on that spoke's path. -/
theorem vertexSet_meshGraph_subset_meshAssembly {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    V(meshGraph N fresh anchors) ⊆ V(meshAssembly N fresh anchors z w) := by
  have hcorele := meshCore_le hN hfresh anchors hz hw hzw
  intro v hv
  obtain ⟨Q, hQ, hvQ⟩ := meshGraph_mem_vertexSet.1 hv
  obtain ⟨R, hR, hsub⟩ := meshGraph_edge_source hQ
  have hvseg : v ∈ Q.seg := by
    rcases hvQ with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have hvR : v ∈ R.seg := hsub hvseg
  have hvp : v ∈ meshPoints N fresh anchors :=
    overlayPieces_ends_cut (meshPoints_endsAreCut N fresh anchors) Q hQ v hvQ
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨u, hu, rfl⟩
  · -- `v` lies on the ring of radius `r`
    have hvring : v ∈ V(ringGraph N fresh anchors r) :=
      mem_vertexSet_ringGraph hN hfresh hr hvp
        (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr hvR)
    exact (le_attachSpokes N fresh anchors _ fresh).vertexSet_mono
      ((ringGraph_le_attachRings hcorele hr).vertexSet_mono hvring)
  · -- `v` lies on the spoke at `u`
    have hvwalk : v ∈ (meshGraph N fresh anchors).walkVertices u (spokeWalk N fresh anchors u) :=
      mem_walkVertices_of_mem_points (meshSegments_nondeg hN hfresh)
        (spokePiece_mem_meshSegments hu) (spokeWalk_spec hN hfresh anchors hu).2 hvp hvR
    exact (spokeGraph_le_attachSpokes (l := fresh)
      (attachRings_le hcorele (meshRadii N)) hN hfresh (fun _ hx => hx) hu).vertexSet_mono hvwalk

/-- **`prop:anchored-square-mesh`, clause 5, for `meshGraph`: the skeleton is 2-connected.**

The hypothesis is *two distinct fresh points*, and it is exactly right:
`Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton` shows the conclusion is
**false** with fewer. -/
theorem meshGraph_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshGraph N fresh anchors).IsTwoConnected :=
  (meshAssembly_isTwoConnected hN hfresh anchors hz hw hzw).of_le_of_vertexSet_subset
    (meshAssembly_le hN hfresh anchors hz hw hzw)
    (vertexSet_meshGraph_subset_meshAssembly hN hfresh anchors hz hw hzw)

/-- **`prop:anchored-square-mesh`, clause 5, for `squareMesh`.**

`Schoenflies.FreshDense fresh δ` alone does **not** suffice — `freshDense_not_isTwoConnected`
is the counterexample — but `FreshDense` together with `δ < 4` does, because it forces two
distinct fresh points (`Schoenflies.exists_two_distinct_fresh_of_freshDense`). The blueprint's
caller uses `δ = ε_n = 2⁻ⁿ`, far below `4`. -/
theorem squareMesh_isTwoConnected {fresh : List Plane} (hfresh : ∀ x ∈ fresh, x ∈ modelCurve)
    {δ : ℝ} (hdense : FreshDense fresh δ) (hδ : δ < 4) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsTwoConnected := by
  obtain ⟨z, hz, w, hw, hzw⟩ := exists_two_distinct_fresh_of_freshDense hdense hδ
  exact meshGraph_isTwoConnected (two_le_meshCount δ) hfresh anchors hz hw hzw

end Schoenflies
end

section
-- module Solutions.Q146_CD.TargetOverlay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.extendOverlay_finite
attribute [-simp] _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.StageSequence.limitTower_region _root_.Schoenflies.StageSequence.limitTower_region' _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.mem_currentOverlayPieces _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Overlaying a target skeleton with the anchored square mesh

A fresh square mesh does not generally contain the current target skeleton: already at stage
zero the target has an arbitrary straight chord which need not be radial or lie on a mesh ring.
The ambient graph for reverse finite transfer must therefore be the polygonal overlay of the
two finite segment families.

`TargetSegmentCover` writes the whole current target skeleton as a finite exact segment cover.
It also remembers which old abstract edge supplied each segment; that provenance is what will
prove the subdivision clause after transverse intersections have been made vertices.

`TargetSegmentCover.meshOverlay` is the combined graph.  It overlays the target cover with the
already-subdivided edges of the anchored mesh, and its cut list contains both the mesh anchors
and every old target vertex.  The basic carrier, drawing, containment, edge-source, and
2-connectivity facts are established here.  The nonouter target-edge carriers form a canonical
finite connected cover of the old open skeleton.  A uniform positive width for this cover,
together with the radial mesh estimate, shows that every sufficiently fine dense mesh meets
every cover piece.  Consequently the combined overlay is a complete source extension at some
positive scale below `4`.  Relative boundary anchoring and no-new-nonouter-incidence are proved
for clean fresh lists and transported through edge relabelling, so the overlay now feeds directly
into reverse finite transfer.  `FreshDenseSelection.lean` constructs the required finite clean
separator list from the dense strongly-accessible boundary points and packages the resulting
reverse-transfer stage.

## Blueprint

* `Schoenflies.TargetSegmentCover` — the finite segment presentation of the current polygonal
  target skeleton.
* `Schoenflies.GeneratedPair.exists_targetSegmentCover` — every generated pair supplies that
  presentation.
* `Schoenflies.TargetSegmentCover.meshOverlay` — the current target skeleton overlaid with the
  anchored square mesh.
* `Schoenflies.TargetSegmentCover.meshOverlay_pointSet` — the combined graph occupies exactly
  the union of the two carriers.
* `Schoenflies.TargetSegmentCover.meshOverlay_isTwoConnected` — the two subdivision traces glue
  along two fresh boundary vertices to make the combined overlay 2-connected.
* `Schoenflies.TargetSegmentCover.noNewNonouterIncidenceAtBoundary_meshOverlay` — clean fresh
  spokes cannot create a second nonouter incidence against the current target trace.
* `Schoenflies.finiteOpenTargetCover` — the nonouter edge carriers, with the model curve
  removed, form a finite connected nontrivial cover of the old open target skeleton.
* `Schoenflies.exists_fine_openTarget_scale` — every generated target has a positive scale
  below `4` at which all pieces of that cover are wider than the mesh.
* `Schoenflies.TargetSegmentCover.exists_scale_isSourceExtension_relabelledMeshOverlay` — at
  that scale, every dense anchored mesh gives the complete relabelled source extension.
* `Schoenflies.TargetSegmentCover.finite_transfer_toward_source_relabelledMeshOverlay_of_outerCycle`
  — the accessible clean overlay performs the complete reverse finite transfer.
-/

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

namespace TargetSegmentCover

variable {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}

/-- The current target skeleton is contained in the combined overlay. -/
theorem targetSkeleton_subset_meshOverlay (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    P.tgt.skeletonSet ⊆
      Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing := by
  rw [Q.meshOverlay_pointSet]
  exact subset_union_left

/-- Every old target vertex is explicitly retained as a vertex of the combined overlay. -/
theorem targetVertices_subset_meshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    V(P.tgt.graph) ⊆ V(Q.meshOverlay delta fresh anchors) := by
  intro x hx
  change x ∈ V(overlayGraph (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.meshPieces_nondeg hfresh delta anchors)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right anchors (by
      rw [Finset.mem_toList, mem_vertexFinset]
      exact hx)
  · rw [meshPieces, cover_append, Q.cover_eq]
    exact Or.inl (Graph.vertexSet_subset_pointSet hx)

/-- Every square-mesh vertex is an endpoint of a source piece for the combined overlay. -/
theorem squareMeshVertices_subset_meshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    V(squareMesh delta fresh anchors) ⊆ V(Q.meshOverlay delta fresh anchors) := by
  intro x hx
  obtain ⟨R, hR, hxR⟩ := meshGraph_mem_vertexSet.1 hx
  change x ∈ V(overlayGraph (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.meshPieces_nondeg hfresh delta anchors)
  · exact attachPoints_endsAreCut _ _ R
      (List.mem_append_right Q.pieces (mem_squareMeshPieces.2 hR)) x hxR
  · exact mem_cover_iff.2 ⟨R,
      List.mem_append_right Q.pieces (mem_squareMeshPieces.2 hR), by
        rcases hxR with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩

/-- Away from the vertices created by the overlay, an overlay edge meeting an old open target
edge is one of its subdivision pieces.  At a transverse crossing the common point is an overlay
vertex, so the hypothesis is intentionally false there. -/
theorem meshOverlay_edge_subset (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    ∀ ⦃e⦄, e ∈ E(P.str.skel) → ∀ ⦃R : Piece⦄,
      R ∈ E(Q.meshOverlay delta fresh anchors) →
      (edgeArc segmentDrawing R ∩
        (P.tgt.cell e \ V(Q.meshOverlay delta fresh anchors))).Nonempty →
      edgeArc segmentDrawing R ⊆ edgeArc P.tgt.drawing e := by
  intro e he R hR hmeet
  obtain ⟨z, hzR, hzCell, hznotOverlay⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hzOldArc : z ∈ edgeArc P.tgt.drawing e := by
    rw [P.tgt.cell_edge hab] at hzCell
    exact hzCell.1
  have hznotOldVertex : z ∉ V(P.tgt.graph) := by
    intro hzV
    rcases P.tgt.isDrawing.vertex_mem_edgeArc (hab.map P.tgt.pos) hzV hzOldArc with
      hza | hzb
    · rw [P.tgt.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hza])
    · rw [P.tgt.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hzb])
  have hzSkeleton : z ∈ P.tgt.skeletonSet :=
    P.tgt.cell_subset_skeletonSet (Or.inr he) hzCell
  have hzCover : z ∈ cover Q.pieces := by
    rw [Q.cover_eq]
    exact hzSkeleton
  obtain ⟨A, hA, hzA⟩ := ClosedPolygon.exists_of_mem_cover hzCover
  obtain ⟨g, hg, hAg⟩ := Q.source A hA
  have hzg : z ∈ edgeArc P.tgt.drawing g := hAg hzA
  have heg : e = g := P.tgt.isDrawing.unique_edge_at
    (by change e ∈ E(P.str.skel); exact he)
    (by change g ∈ E(P.str.skel); exact hg)
    hznotOldVertex hzOldArc hzg
  have hAold : A.seg ⊆ edgeArc P.tgt.drawing e := by rwa [heg]
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.meshPieces delta fresh anchors)
        (anchors ++ P.tgt.graph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_left _ hA) hzA
  have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-- The combined overlay locally contains an edge subdivision of the old target drawing. -/
theorem target_isPlaneSubdivisionExtension (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    IsPlaneSubdivisionExtension P.tgt.graph P.tgt.drawing
      (Q.meshOverlay delta fresh anchors) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := P.tgt.isDrawing
  isDrawing := Q.meshOverlay_isDrawing hfresh delta anchors
  vertexSet_subset := Q.targetVertices_subset_meshOverlay hfresh delta anchors
  pointSet_subset := by
    change P.tgt.skeletonSet ⊆ _
    exact Q.targetSkeleton_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he R hR hmeet
    have heS : e ∈ E(P.str.skel) := by
      rwa [P.tgt.edgeSet_graph] at he
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heS
    apply Q.meshOverlay_edge_subset hfresh delta anchors heS hR
    obtain ⟨z, hzR, hze, hznot⟩ := hmeet
    refine ⟨z, hzR, ?_, hznot⟩
    rw [P.tgt.cell_edge hab]
    refine ⟨hze, ?_⟩
    intro hzEnds
    rcases hzEnds with hza | hzb
    · apply hznot
      rw [hza]
      exact Q.targetVertices_subset_meshOverlay hfresh delta anchors (by
        rw [P.tgt.vertexSet_graph]
        exact ⟨a, hab.left_mem, rfl⟩)
    · apply hznot
      rw [hzb]
      exact Q.targetVertices_subset_meshOverlay hfresh delta anchors (by
        rw [P.tgt.vertexSet_graph]
        exact ⟨b, hab.right_mem, rfl⟩)

/-- The combined overlay also locally contains an edge subdivision of the anchored square
mesh.  Using the mesh's already-subdivided edges as source pieces makes the proof immediate. -/
theorem squareMesh_isPlaneSubdivisionExtension (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    IsPlaneSubdivisionExtension (squareMesh delta fresh anchors) segmentDrawing
      (Q.meshOverlay delta fresh anchors) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := squareMesh_isDrawing hfresh delta anchors
  isDrawing := Q.meshOverlay_isDrawing hfresh delta anchors
  vertexSet_subset := Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
  pointSet_subset := Q.squareMesh_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he R hR hmeet
    obtain ⟨z, hzR, hze, hznot⟩ := hmeet
    obtain ⟨R', hR', hzR', hR'e⟩ :=
      exists_overlayPiece_mem_subset
        (points := attachPoints (Q.meshPieces delta fresh anchors)
          (anchors ++ P.tgt.graph.vertexFinset.toList))
        (P₀ := e) (List.mem_append_right Q.pieces (mem_squareMeshPieces.2 he))
        (by rwa [edgeArc_segmentDrawing] at hze)
    have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
      rwa [edgeArc_segmentDrawing]
    have hRR' : R = R' :=
      (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
        hR hR' hznot hzR hzR'Arc
    rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
    exact hR'e

/-- The old-target trace inside the combined overlay remains 2-connected. -/
theorem targetTrace_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    (Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
      P.tgt.skeletonSet).IsTwoConnected :=
  (Q.target_isPlaneSubdivisionExtension hfresh delta anchors).trace_isTwoConnected
    P.tgt_isWeaklyAdmissible.isTwoConnected

/-- Under the usual density hypotheses, the square-mesh trace inside the combined overlay
remains 2-connected. -/
theorem squareMeshTrace_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) :
    (Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
      (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)).IsTwoConnected :=
  (Q.squareMesh_isPlaneSubdivisionExtension hfresh delta anchors).trace_isTwoConnected
    (squareMesh_isTwoConnected hfresh hdense hdelta anchors)

/-- The combined target/mesh overlay is 2-connected.  The two subdivision traces are glued at
two distinct fresh boundary vertices, and together they contain every overlay vertex. -/
theorem meshOverlay_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) :
    (Q.meshOverlay delta fresh anchors).IsTwoConnected := by
  let T := Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
    P.tgt.skeletonSet
  let M := Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
    (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)
  have hT2 : T.IsTwoConnected := Q.targetTrace_isTwoConnected hfresh delta anchors
  have hM2 : M.IsTwoConnected :=
    Q.squareMeshTrace_isTwoConnected hfresh hdense hdelta anchors
  obtain ⟨z, hz, w, hw, hzw⟩ := exists_two_distinct_fresh_of_freshDense hdense hdelta
  have hzSquare : z ∈ V(squareMesh delta fresh anchors) :=
    end_mem_vertexSet_meshGraph (spokePiece_mem_meshSegments hz) (Or.inl rfl)
  have hwSquare : w ∈ V(squareMesh delta fresh anchors) :=
    end_mem_vertexSet_meshGraph (spokePiece_mem_meshSegments hw) (Or.inl rfl)
  have hzOverlay : z ∈ V(Q.meshOverlay delta fresh anchors) :=
    Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
      hzSquare
  have hwOverlay : w ∈ V(Q.meshOverlay delta fresh anchors) :=
    Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
      hwSquare
  have hzTarget : z ∈ P.tgt.skeletonSet := by
    apply P.tgt.outerSet_subset_skeletonSet
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hfresh z hz
  have hwTarget : w ∈ P.tgt.skeletonSet := by
    apply P.tgt.outerSet_subset_skeletonSet
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hfresh w hw
  have hzMesh : z ∈ Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hzSquare
  have hwMesh : w ∈ Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hwSquare
  have hzT : z ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hzOverlay, hzTarget⟩
  have hwT : w ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hwOverlay, hwTarget⟩
  have hzM : z ∈ V(M) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hzOverlay, hzMesh⟩
  have hwM : w ∈ V(M) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hwOverlay, hwMesh⟩
  have hcompat : T.Compatible M :=
    Graph.Compatible.of_le_le (Graph.traceGraph_le _) (Graph.traceGraph_le _)
  have hU2 : (T.union M).IsTwoConnected :=
    hT2.union hcompat hM2 hzw hzT hzM hwT hwM
  apply hU2.of_le_of_vertexSet_subset
    (Graph.union_le (Graph.traceGraph_le _) (Graph.traceGraph_le _))
  intro x hx
  rw [Graph.vertexSet_union]
  have hxPoint : x ∈ Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hx
  rw [Q.meshOverlay_pointSet] at hxPoint
  rcases hxPoint with hxTarget | hxMesh
  · exact Or.inl (by rw [Graph.traceGraph_vertexSet]; exact ⟨hx, hxTarget⟩)
  · exact Or.inr (by rw [Graph.traceGraph_vertexSet]; exact ⟨hx, hxMesh⟩)

/-- The combined overlay stays in the closed target square. -/
theorem meshOverlay_pointSet_subset (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing ⊆
      Plane.closedSquare 0 1 := by
  rw [Q.meshOverlay_pointSet]
  exact Set.union_subset P.tgt_isWeaklyAdmissible.skeletonSet_subset
    (squareMesh_pointSet_subset hfresh delta anchors)

/-- Every combined-overlay edge either lies on the model curve or is a polygonal edge whose
nonvertex points lie in the open target square.  A nonouter edge cannot meet the model curve
away from overlay vertices: the outer-ring segment through such a point would give a second
edge of the plane drawing there. -/
theorem meshOverlay_edge_dichotomy (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    ∀ ⦃R⦄, R ∈ E(Q.meshOverlay delta fresh anchors) →
      edgeArc segmentDrawing R ⊆ modelCurve ∨
        (IsPolygonal (edgeArc segmentDrawing R) ∧
          edgeArc segmentDrawing R \ V(Q.meshOverlay delta fresh anchors) ⊆
            Plane.closedSquare 0 1 \ modelCurve) := by
  intro R hR
  by_cases houter : edgeArc segmentDrawing R ⊆ modelCurve
  · exact Or.inl houter
  · refine Or.inr ⟨?_, ?_⟩
    · rw [edgeArc_segmentDrawing]
      exact isPolygonal_segment _ _
    · intro x hx
      refine ⟨Q.meshOverlay_pointSet_subset hfresh delta anchors
        (Graph.edgeArc_subset_pointSet hR hx.1), ?_⟩
      intro hxOuter
      have hxMeshOuter :
          x ∈ ⋃ A ∈ outerEdges (meshCount delta) fresh anchors, A.seg := by
        rw [squareMesh_cover_outerEdges]
        exact hxOuter
      obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hxMeshOuter
      obtain ⟨R', hR', hxR', hR'A⟩ :=
        exists_overlayPiece_mem_subset
          (points := attachPoints (Q.meshPieces delta fresh anchors)
            (anchors ++ P.tgt.graph.vertexFinset.toList))
          (P₀ := A) (List.mem_append_right Q.pieces
            (mem_squareMeshPieces.2 hA.1)) hxA
      have hxR'Arc : x ∈ edgeArc segmentDrawing R' := by
        rwa [edgeArc_segmentDrawing]
      have hRR' : R = R' :=
        (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
          hR hR' hx.2 hx.1 hxR'Arc
      apply houter
      rw [hRR', edgeArc_segmentDrawing]
      exact hR'A.trans hA.2

/-- Two mesh-sourced, nonouter overlay edges incident at the same boundary point coincide.
The square mesh has one spoke there; both overlay pieces start at the boundary end of that
spoke, so their segment carriers are nested, and planarity identifies their edge names. -/
theorem meshOverlay_mesh_edges_eq_at_boundary (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) {z : Plane} (hz : z ∈ modelCurve)
    {R S : Piece} (hR : R ∈ E(Q.meshOverlay delta fresh anchors))
    (hS : S ∈ E(Q.meshOverlay delta fresh anchors))
    (hRinc : (Q.meshOverlay delta fresh anchors).Inc R z)
    (hSinc : (Q.meshOverlay delta fresh anchors).Inc S z)
    (hRnot : ¬ edgeArc segmentDrawing R ⊆ modelCurve)
    (hSnot : ¬ edgeArc segmentDrawing S ⊆ modelCurve)
    {A C : Piece} (hA : A ∈ E(squareMesh delta fresh anchors))
    (hC : C ∈ E(squareMesh delta fresh anchors))
    (hRA : R.seg ⊆ A.seg) (hSC : S.seg ⊆ C.seg) : R = S := by
  have hdraw := Q.meshOverlay_isDrawing hfresh delta anchors
  have hzRarc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hRinc
  have hzSarc : z ∈ edgeArc segmentDrawing S := hdraw.inc_mem_edgeArc hSinc
  have hzRseg : z ∈ R.seg := by rwa [edgeArc_segmentDrawing] at hzRarc
  have hzSseg : z ∈ S.seg := by rwa [edgeArc_segmentDrawing] at hzSarc
  have hzA : z ∈ A.seg := hRA hzRseg
  have hzC : z ∈ C.seg := hSC hzSseg
  have hAnot : ¬ A.seg ⊆ modelCurve := by
    intro hAouter
    apply hRnot
    rw [edgeArc_segmentDrawing]
    exact hRA.trans hAouter
  have hCnot : ¬ C.seg ⊆ modelCurve := by
    intro hCouter
    apply hSnot
    rw [edgeArc_segmentDrawing]
    exact hSC.trans hCouter
  obtain ⟨w, hwFresh, hAw, hwA, -⟩ :=
    squareMesh_inner_edge_at_fresh hfresh delta hA ⟨z, hzA, hz⟩ hAnot
  obtain ⟨v, hvFresh, hCv, hvC, -⟩ :=
    squareMesh_inner_edge_at_fresh hfresh delta hC ⟨z, hzC, hz⟩ hCnot
  have hzw : z = w := by
    have : z ∈ ({w} : Set Plane) := hAw ▸ ⟨hzA, hz⟩
    simpa only [Set.mem_singleton_iff] using this
  have hzv : z = v := by
    have : z ∈ ({v} : Set Plane) := hCv ▸ ⟨hzC, hz⟩
    simpa only [Set.mem_singleton_iff] using this
  have hzFresh : z ∈ fresh := hzw ▸ hwFresh
  have hzAend : z = A.1 ∨ z = A.2 := hzw ▸ hwA
  have hzCend : z = C.1 ∨ z = C.2 := hzv ▸ hvC
  obtain ⟨U, hU, huniq⟩ :=
    squareMesh_unique_inner_edge hfresh delta anchors hzFresh
  have hAU : A = U := huniq A ⟨hA, hzAend, hAnot⟩
  have hCU : C = U := huniq C ⟨hC, hzCend, hCnot⟩
  have hAC : A = C := hAU.trans hCU.symm
  have hSA : S.seg ⊆ A.seg := by rwa [hAC]
  have hcomp := piece_segments_comparable_of_common_source_end
    (meshGraph_edge_nondeg (two_le_meshCount delta) hfresh hA)
    hzAend hRA hSA (Q.meshOverlay_inc_endpoint hRinc)
      (Q.meshOverlay_inc_endpoint hSinc)
  rcases hcomp with hsub | hsub
  · exact eq_of_edgeArc_subset hdraw hR hS (by
      simpa only [edgeArc_segmentDrawing] using hsub)
  · exact (eq_of_edgeArc_subset hdraw hS hR (by
      simpa only [edgeArc_segmentDrawing] using hsub)).symm

/-- The relative no-new-incidence property of a clean overlay survives its injective edge
renaming. -/
theorem noNewNonouterIncidenceAtBoundary_relabelledMeshOverlay
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (havoid : FreshAvoidsTargetNonouterEdges P fresh)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors)) :
    NoNewNonouterIncidenceAtBoundary P.tgt.skeletonSet
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing)
      modelCurve := by
  intro B hBH hbase z d k hz hd hk hdinc hkinc hdnot hknot hdnew
  obtain ⟨R, hR, rfl⟩ := hd
  have hkH : k ∈ E((Q.meshOverlay delta fresh anchors).relabelEdges name hname) :=
    hBH.edgeSet_mono hk
  obtain ⟨S, hS, rfl⟩ := hkH
  obtain ⟨R', hR', hR'name, hR'inc⟩ :=
    (Graph.relabelEdges_inc (Q.meshOverlay delta fresh anchors) name hname
      (name R) z).1 hdinc
  have hR'R : R' = R := hname hR' hR hR'name
  subst R'
  have hSincRelabelled :
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname).Inc
        (name S) z := (hBH.inc_congr hk).1 hkinc
  obtain ⟨S', hS', hS'name, hS'inc⟩ :=
    (Graph.relabelEdges_inc (Q.meshOverlay delta fresh anchors) name hname
      (name S) z).1 hSincRelabelled
  have hS'S : S' = S := hname hS' hS hS'name
  subst S'
  have hdraw := Q.meshOverlay_isDrawing hfresh delta anchors
  have hdrawRelabelled := hdraw.relabelEdges hname
  have hRnot : ¬ edgeArc segmentDrawing R ⊆ modelCurve := by
    intro hsub
    apply hdnot
    rwa [Graph.edgeArc_relabelDrawing hname hR]
  have hSnot : ¬ edgeArc segmentDrawing S ⊆ modelCurve := by
    intro hsub
    apply hknot
    rwa [Graph.edgeArc_relabelDrawing hname hS]
  have hzRarc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hR'inc
  have hzRseg : z ∈ R.seg := by rwa [edgeArc_segmentDrawing] at hzRarc
  rcases Q.meshOverlay_edge_source_squareMesh hR with hROld | hRMesh
  · obtain ⟨A, hA, hRA⟩ := hROld
    obtain ⟨e, he, hAe⟩ := Q.source A hA
    have hRbase :
        edgeArc ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing)
          (name R) ⊆ P.tgt.skeletonSet := by
      rw [Graph.edgeArc_relabelDrawing hname hR, edgeArc_segmentDrawing]
      exact hRA.trans (hAe.trans (Graph.edgeArc_subset_pointSet (by
        rw [P.tgt.edgeSet_graph]
        exact he)))
    exact (hdnew (edge_mem_of_edgeArc_subset_pointSet hdrawRelabelled hBH
      ⟨R, hR, rfl⟩ (hRbase.trans hbase))).elim
  · obtain ⟨A, hA, hRA⟩ := hRMesh
    have hzA : z ∈ A.seg := hRA hzRseg
    have hAnot : ¬ A.seg ⊆ modelCurve := by
      intro hAouter
      apply hRnot
      rw [edgeArc_segmentDrawing]
      exact hRA.trans hAouter
    obtain ⟨w, hwFresh, hAw, -, -⟩ :=
      squareMesh_inner_edge_at_fresh hfresh delta hA ⟨z, hzA, hz⟩ hAnot
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hAw ▸ ⟨hzA, hz⟩
      simpa only [Set.mem_singleton_iff] using this
    have hzFresh : z ∈ fresh := hzw ▸ hwFresh
    rcases Q.meshOverlay_edge_source_squareMesh hS with hSOld | hSMesh
    · obtain ⟨C, hC, hSC⟩ := hSOld
      obtain ⟨e, he, hCe⟩ := Q.source C hC
      have heNotOuter : e ∉ E(P.str.outerGraph) := by
        intro heOuter
        apply hSnot
        rw [edgeArc_segmentDrawing]
        apply hSC.trans
        apply hCe.trans
        intro x hx
        rw [← P.tgt_isWeaklyAdmissible.outerSet_eq]
        exact Graph.edgeArc_subset_pointSet (by
          rw [Graph.edgeSet_map]
          exact heOuter) hx
      apply havoid z hzFresh e he heNotOuter
      apply hCe
      apply hSC
      have hzSarc : z ∈ edgeArc segmentDrawing S := hdraw.inc_mem_edgeArc hS'inc
      rwa [edgeArc_segmentDrawing] at hzSarc
    · obtain ⟨C, hC, hSC⟩ := hSMesh
      have hRS : R = S := Q.meshOverlay_mesh_edges_eq_at_boundary hfresh delta anchors
        hz hR hS hR'inc hS'inc hRnot hSnot hA hC hRA hSC
      exact hdnew (hRS ▸ hk)

/-- A connected old-skeleton piece wider than the mesh scale must meet the mesh.  Otherwise the
radial mesh estimate bounds all of its pairwise distances by a number strictly below `delta`. -/
theorem mesh_hits_openTarget_of_locallyWider
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    {fresh : List Plane}
    {delta : ℝ} (hdelta : 0 < delta) (hdense : FreshDense fresh delta)
    (hwide : OpenTargetLocallyWiderThan P delta) (anchors : List Plane) :
    ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty := by
  intro z hz
  obtain ⟨A, hA, hAconn, hzA, x, hxA, y, hyA, hxy⟩ := hwide z hz
  refine ⟨A, hA, hAconn, hzA, ?_⟩
  have hmeet :
      (A ∩ Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
    have hdisj : ∀ u ∈ A, u ∉ cover (meshSegments (meshCount delta) fresh) := by
      intro u huA huMesh
      apply hempty u
      refine ⟨huA, ?_⟩
      rwa [squareMesh_pointSet]
    have hzOpen := hA hzA
    have hzlt : Plane.supNorm z < 1 := by
      refine lt_of_le_of_ne
        (mem_closedSquare_zero_one.1
          (P.tgt_isWeaklyAdmissible.skeletonSet_subset hzOpen.1)) ?_
      exact hzOpen.2
    obtain ⟨-, hdist⟩ := radial_diam_bound (two_le_meshCount delta)
      (meshCount_spec hdelta).le hdense hAconn hdisj hzA hzlt
    have hNpos : (0 : ℝ) < meshCount delta := by
      exact_mod_cast Nat.zero_lt_of_lt (two_le_meshCount delta)
    have hthin : Real.sqrt 2 / (meshCount delta : ℝ) < delta / 2 := by
      rw [div_lt_div_iff₀ hNpos two_pos]
      linarith [meshCount_spec hdelta]
    have := hdist x hxA y hyA
    linarith
  obtain ⟨u, huA, huMesh⟩ := hmeet
  exact ⟨u, huA, huMesh, (hA huA).2⟩

/-- If every connected piece of the old open skeleton meets the connected open part of the
mesh, their union is connected.  This is the set-theoretic core of the quantitative
mesh-hitting argument. -/
theorem meshOverlay_isConnected_diff_of_hits (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {z₀ : Plane} (hz₀ : z₀ ∈ fresh) (delta : ℝ) (anchors : List Plane)
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsConnected
      (Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing \ modelCurve) := by
  let M := Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \ modelCurve
  have hM : IsConnected M := squareMesh_isConnected_diff hfresh delta anchors hz₀
  obtain ⟨r₀, hr₀⟩ := hM.nonempty
  have hunion : IsConnected ((P.tgt.skeletonSet \ modelCurve) ∪ M) := by
    refine ⟨⟨r₀, Or.inr hr₀⟩, isPreconnected_of_forall r₀ ?_⟩
    intro z hz
    rcases hz with hzOld | hzMesh
    · obtain ⟨A, hA, hAconn, hzA, w, hwA, hwM⟩ := hhit z hzOld
      refine ⟨A ∪ M, Set.union_subset (hA.trans subset_union_left) subset_union_right,
        Or.inr hr₀, Or.inl hzA, ?_⟩
      exact hAconn.union' ⟨w, hwA, hwM⟩ hM.isPreconnected
    · exact ⟨M, subset_union_right, hr₀, hzMesh, hM.isPreconnected⟩
  rw [Q.meshOverlay_pointSet]
  have heq :
      (P.tgt.skeletonSet ∪
          Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing) \ modelCurve =
        (P.tgt.skeletonSet \ modelCurve) ∪ M := by
    ext x
    constructor
    · rintro ⟨hxOld | hxMesh, hxOuter⟩
      · exact Or.inl ⟨hxOld, hxOuter⟩
      · exact Or.inr ⟨hxMesh, hxOuter⟩
    · rintro (⟨hxOld, hxOuter⟩ | ⟨hxMesh, hxOuter⟩)
      · exact ⟨Or.inl hxOld, hxOuter⟩
      · exact ⟨Or.inr hxMesh, hxOuter⟩
  rw [heq]
  exact hunion

/-- After injective edge relabelling, the combined overlay is a target extension as soon as its
two genuinely global assembly properties—2-connectivity and connectedness off the boundary—are
available.  Every local subdivision and geometric field is discharged above. -/
theorem isSourceExtension_relabelledMeshOverlay
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (htwo : (Q.meshOverlay delta fresh anchors).IsTwoConnected)
    (hconnected : IsConnected
      (Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing \ modelCurve)) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) where
  finite := Graph.Finite.relabelEdges hname
  isDrawing := (Q.meshOverlay_isDrawing hfresh delta anchors).relabelEdges hname
  isTwoConnected := htwo.relabelEdges hname
  vertexSet_subset := by
    rw [Graph.vertexSet_relabelEdges]
    exact Q.targetVertices_subset_meshOverlay hfresh delta anchors
  skeletonSet_subset := by
    rw [Graph.pointSet_relabelEdges hname]
    exact Q.targetSkeleton_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he d hd hmeet
    obtain ⟨R, hR, rfl⟩ := hd
    rw [Graph.edgeArc_relabelDrawing hname hR,
      Graph.vertexSet_relabelEdges] at hmeet
    rw [Graph.edgeArc_relabelDrawing hname hR]
    exact Q.meshOverlay_edge_subset hfresh delta anchors he hR hmeet
  pointSet_subset := by
    rw [Graph.pointSet_relabelEdges hname]
    exact Q.meshOverlay_pointSet_subset hfresh delta anchors
  edge_dichotomy := by
    intro d hd
    obtain ⟨R, hR, rfl⟩ := hd
    rw [Graph.edgeArc_relabelDrawing hname hR,
      Graph.vertexSet_relabelEdges]
    exact Q.meshOverlay_edge_dichotomy hfresh delta anchors hR
  isConnected := by
    rw [Graph.pointSet_relabelEdges hname]
    exact hconnected

/-- The mesh-hitting condition is enough to discharge the connectedness field of the target
extension.  Thus only 2-connectivity and the quantitative fact that the mesh meets every
connected piece of the old open skeleton remain. -/
theorem isSourceExtension_relabelledMeshOverlay_of_hits
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {z₀ : Plane} (hz₀ : z₀ ∈ fresh)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (htwo : (Q.meshOverlay delta fresh anchors).IsTwoConnected)
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) :=
  Q.isSourceExtension_relabelledMeshOverlay hfresh delta anchors name hname htwo
    (Q.meshOverlay_isConnected_diff_of_hits hfresh hz₀ delta anchors hhit)

/-- With a dense fresh boundary list, 2-connectivity and the nonempty-fresh requirement are
automatic.  The mesh-hitting condition is then the only remaining assembly hypothesis. -/
theorem isSourceExtension_relabelledMeshOverlay_of_dense_hits
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) := by
  obtain ⟨z, hz, -, -, -⟩ := exists_two_distinct_fresh_of_freshDense hdense hdelta
  exact Q.isSourceExtension_relabelledMeshOverlay_of_hits hfresh hz delta anchors name hname
    (Q.meshOverlay_isTwoConnected hfresh hdense hdelta anchors) hhit

/-- A sufficiently fine mesh gives the target extension from the local-width condition alone:
the radial diameter estimate supplies the mesh hits, while density supplies 2-connectivity. -/
theorem isSourceExtension_relabelledMeshOverlay_of_locallyWider
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdelta : 0 < delta) (hdense : FreshDense fresh delta)
    (hdelta4 : delta < 4) (hwide : OpenTargetLocallyWiderThan P delta)
    (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors)) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) :=
  Q.isSourceExtension_relabelledMeshOverlay_of_dense_hits hfresh hdense hdelta4 anchors
    name hname (mesh_hits_openTarget_of_locallyWider P hdelta hdense hwide anchors)

/-- **Reverse finite transfer through the combined target/mesh overlay.**  Once the overlay is
a source extension, strong accessibility of its fresh anchors and avoidance of the finitely
many old nonouter target edges discharge all remaining reverse-ear hypotheses. -/
theorem finite_transfer_toward_source_relabelledMeshOverlay_of_outerCycle
    [Infinite γ] (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (havoid : FreshAvoidsTargetNonouterEdges P fresh)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (hH : IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing))
    (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
        (par : γ → γ),
      IsTargetTransferOf T P
        ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
        ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) par :=
  finite_transfer_toward_source_of_relativeBoundaryGeometry hH
    (Q.newTargetBoundaryAnchored_relabelledMeshOverlay
      hfresh hstrong delta anchors name hname)
    (Q.noNewNonouterIncidenceAtBoundary_relabelledMeshOverlay
      hfresh havoid delta anchors name hname)
    hcycle

/-- At a locally wide scale, the dense clean overlay automatically supplies both the source
extension and its reverse finite transfer; fresh abstract edge names are chosen internally. -/
theorem exists_finite_transfer_toward_source_meshOverlay_of_locallyWider
    [Infinite γ] (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (havoid : FreshAvoidsTargetNonouterEdges P fresh)
    {delta : ℝ} (hdelta : 0 < delta) (hdense : FreshDense fresh delta)
    (hdelta4 : delta < 4) (hwide : OpenTargetLocallyWiderThan P delta)
    (anchors : List Plane) (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (name : Piece → γ) (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
        (T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
        (par : γ → γ),
      IsTargetTransferOf T P
        ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
        ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) par := by
  obtain ⟨name, hname, -⟩ := Q.exists_meshOverlay_edgeRelabeling delta fresh anchors
  have hH := Q.isSourceExtension_relabelledMeshOverlay_of_locallyWider
    hfresh hdelta hdense hdelta4 hwide anchors name hname
  obtain ⟨T, par, hT⟩ :=
    Q.finite_transfer_toward_source_relabelledMeshOverlay_of_outerCycle
      hfresh hstrong havoid delta anchors name hname hH hcycle
  exact ⟨name, hname, T, par, hT⟩

/-- The complete reverse-transfer scale may be forced below any prescribed positive bound. -/
theorem exists_scale_finite_transfer_toward_source_meshOverlay_lt
    [Infinite γ] (Q : TargetSegmentCover P) (hcycle : S₀.OuterEdgesFormCycle)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 4 ∧ delta < bound ∧
      ∀ (fresh anchors : List Plane),
        (∀ z ∈ fresh, z ∈ modelCurve) →
        (∀ z ∈ fresh,
          StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)) →
        FreshAvoidsTargetNonouterEdges P fresh → FreshDense fresh delta →
        ∃ (name : Piece → γ)
            (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
            (T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
            (par : γ → γ),
          IsTargetTransferOf T P
            ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
            ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) par := by
  obtain ⟨delta, hdelta, hdelta4, hdeltabound, hwide⟩ :=
    exists_fine_openTarget_scale_lt P hbound
  refine ⟨delta, hdelta, hdelta4, hdeltabound, ?_⟩
  intro fresh anchors hfresh hstrong havoid hdense
  exact Q.exists_finite_transfer_toward_source_meshOverlay_of_locallyWider
    hfresh hstrong havoid hdelta hdense hdelta4 hwide anchors hcycle

end TargetSegmentCover

end Schoenflies
end

section
-- module Solutions.Q146_CD.FreshDenseSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.extendOverlay_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Selecting a finite dense list of fresh boundary anchors

`FreshDense fresh delta` is the order-free condition used by the anchored square mesh: every
connected subset of the model curve avoiding `fresh` has diameter at most `delta / 2`.

A dense set of eligible anchors contains a finite list with this property.  For each pair of
model-curve points at distance at least `delta / 2`, two eligible anchors separate the pair.
The same anchors separate every nearby pair, because the complementary sides of the associated
cut arcs are open.  The far-pair set is compact, so finitely many such neighborhoods cover it.
Any connected set avoiding all selected anchors must therefore have the required diameter.

## Blueprint

* `Schoenflies.exists_finite_freshDense_of_dense` — a dense eligible subset of the model curve
  supplies a finite `FreshDense` list at every positive scale.
* `Schoenflies.TargetSegmentCover.MeshOverlayTransferData` — the complete output of one
  reverse overlay-transfer stage, packaged for the stage recursion.
* `Schoenflies.TargetSegmentCover.nonempty_meshOverlayTransferData_inside` — in the standard
  closed Jordan domain, separation and the outer-cycle invariant construct that stage data.
* `Schoenflies.TargetSegmentCover.MeshOverlayTransferData.diam_targetStar_lt` — the transferred
  target stars have diameter less than twice the selected mesh scale.
-/

open Metric Set Topology
open scoped Graph

namespace Schoenflies

/-! ### Fresh lists for a generated target overlay -/

namespace TargetSegmentCover

variable {S₀ : CellStructure γ} {srcOuter srcDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}

/-- The packaged reverse-transfer data can be selected below any positive prescribed scale. -/
theorem exists_meshOverlayTransferData_lt_of_accessibleBoundary_dense
    [Infinite γ] (Q : TargetSegmentCover P)
    (haccessible : modelCurve ⊆ closure (accessibleTargetBoundary P))
    (hcycle : S₀.OuterEdgesFormCycle) (anchors : List Plane)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ w : MeshOverlayTransferData Q anchors, w.delta < bound := by
  obtain ⟨delta, hdelta, hdelta4, hdeltabound, htransfer⟩ :=
    Q.exists_scale_finite_transfer_toward_source_meshOverlay_lt hcycle hbound
  obtain ⟨fresh, hfresh, hstrong, havoid, hdense, hnet⟩ :=
    exists_clean_freshDense_of_accessibleTargetBoundary_dense
      P haccessible hdelta
  obtain ⟨name, hname, T, par, hT⟩ :=
    htransfer fresh anchors hfresh hstrong havoid hdense
  exact ⟨{
    delta := delta
    fresh := fresh
    delta_pos := hdelta
    delta_lt_four := hdelta4
    fresh_mem := hfresh
    fresh_accessible := hstrong
    fresh_avoids := havoid
    fresh_dense := hdense
    fresh_net := hnet
    name := name
    name_inj := hname
    pair := T
    parent := par
    transfer := hT }, hdeltabound⟩

/-- In the standard closed Jordan domain, a reverse-transfer stage exists below every positive
prescribed scale. -/
theorem exists_meshOverlayTransferData_lt_inside
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}
    (Q : TargetSegmentCover P) (hsep : IsSeparating C)
    (hcycle : S₀.OuterEdgesFormCycle) (anchors : List Plane)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ w : MeshOverlayTransferData Q anchors, w.delta < bound :=
  exists_meshOverlayTransferData_lt_of_accessibleBoundary_dense Q
    (accessibleTargetBoundary_dense_inside P hsep) hcycle anchors hbound

end TargetSegmentCover

end Schoenflies
end

section
-- module Solutions.Q146_CD.StageTransition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The common output of one transferred stage

Both directions of finite transfer produce the four pieces of data needed between consecutive
matched cellulations: compatible source and target refinements, growth of the realized source
skeleton, and agreement of the new skeleton homeomorphism with the old one.  `StageTransition`
packages that shared output and proves that transitions compose.

## Blueprint

* `Schoenflies.StageTransition` — one step of the quantitative-refinement recursion, stripped of
  the particular ambient graph used to construct it.
* `Schoenflies.IsPartialTransferOf.stageTransition`,
  `Schoenflies.IsTargetPartialTransferOf.stageTransition` — both finite-transfer directions
  expose the same stage interface.
* `Schoenflies.StageTransition.trans` — consecutive transferred refinements compose.
-/

open Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

namespace StageTransition

variable {P Q T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {par₁ par₂ : γ → γ}

/-- Target skeletons grow as well.  This follows from source-skeleton growth and agreement of
the two skeleton homeomorphisms on the old source skeleton. -/
theorem targetSkeletonSet_subset {par : γ → γ}
    (h : StageTransition T P par) : P.tgt.skeletonSet ⊆ T.tgt.skeletonSet := by
  rw [← P.homeo.image_skeletonSet, ← T.homeo.image_skeletonSet]
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h.sourceSkeletonSet_subset hx, h.homeo_eqOn hx⟩

end StageTransition

/-- Direction (b)'s induction invariant supplies the identical stage transition. -/
theorem IsTargetPartialTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTargetPartialTransferOf T P B Hdraw par) : StageTransition T P par where
  refines_src := h.refines_src
  refines_tgt := h.refines_tgt
  sourceSkeletonSet_subset := h.sourceSkeletonSet_subset
  homeo_eqOn := h.homeo_eqOn

/-- The admissible conclusion of direction (b) forgets to the same stage transition. -/
theorem IsTargetTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTargetTransferOf T P H Hdraw par) : StageTransition T P par :=
  h.toIsTargetPartialTransferOf.stageTransition

end Schoenflies
end

section
-- module Solutions.Q146_CD.QuantitativeStages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.extendOverlay_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Quantitative successor stages

The reverse half of the quantitative-refinement recursion is now a closed construction.  From
one generated pair over the closed Jordan domain and one requested positive bound, it selects an
exact finite target-segment cover, a sufficiently fine square-mesh overlay, finitely many clean
accessible boundary anchors, and the reverse finite transfer.  Its target stars are smaller than
the requested bound.

## Blueprint

* `Schoenflies.QuantitativeReverseStage` — all construction data for one reverse quantitative
  successor.
* `Schoenflies.exists_quantitativeReverseStage` — construction from separation
  and the persistent outer-cycle invariant.
* `Schoenflies.QuantitativeReverseStage.transition` — the output is a `StageTransition`.
* `Schoenflies.QuantitativeReverseStage.diam_targetStar_lt_bound` — the uniform half of
  `prop:shrinking-stars` at this successor.
* `Schoenflies.TargetFaceMesh.refine` — subsequent forward transfers preserve the target
  face-mesh estimate.
-/

open Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}
  {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}

namespace TargetFaceMesh

variable {T : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}
  {par : γ → γ} {bound : ℝ}

/-- A target face-mesh estimate gives the corresponding factor-two bound on every star. -/
theorem diam_star_lt (hmesh : TargetFaceMesh P bound)
    {σ : γ} (hσ : σ ∈ P.str.cells) :
    Metric.diam (P.tgt.star σ) < 2 * bound :=
  P.tgt_isCellDecomposition.diam_star_lt P.str_combInvariants
    (Plane.isBounded_closedSquare 0 1) hσ
    (fun _ hF _ => hmesh hF)

end TargetFaceMesh

namespace QuantitativeReverseStage

variable {anchors : List Plane} {bound : ℝ}
  (w : QuantitativeReverseStage P anchors bound)

/-- The common abstract parent map from the successor to the old stage. -/
abbrev parent : γ → γ := w.overlay.parent

/-- Reverse finite transfer supplies exactly the common transition interface used by the tower. -/
theorem transition : StageTransition w.pair P w.parent :=
  w.overlay.transfer.stageTransition

end QuantitativeReverseStage

/-- **Quantitative reverse successor.** Every generated stage over the closed
Jordan domain admits a reverse transferred refinement whose target stars are smaller than any
specified positive bound. -/
theorem exists_quantitativeReverseStage [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hsep : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (anchors : List Plane) {bound : ℝ} (hbound : 0 < bound) :
    Nonempty (QuantitativeReverseStage P anchors bound) := by
  obtain ⟨Q⟩ := P.exists_targetSegmentCover
  have hhalf : 0 < bound / 2 := by positivity
  obtain ⟨w, hw⟩ := Q.exists_meshOverlayTransferData_lt_inside
    hsep hcycle anchors hhalf
  exact ⟨{ cover := Q, overlay := w, delta_lt_half_bound := hw }⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.StageTower
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.pieceListGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# From a sequence of transferred stages to a `LimitTower`

Two interfaces in this library were designed from opposite ends and have never met.

* `Schoenflies.GeneratedPair` (`FiniteTransfer.lean`) is what `thm:finite-transfer` consumes and
  produces: one abstract cell structure, its two realizations, the skeleton homeomorphism, the
  two cell decompositions, and weak admissibility on both sides.
* `Schoenflies.CellStructure.LimitTower` (`LimitMap.lean`) is what the limit section consumes:
  the same data indexed by `ℕ`, plus the nesting and the two halves of `prop:shrinking-stars`.

This module joins them. `Schoenflies.StageSequence` is a sequence of `GeneratedPair`s carrying
exactly the extra data the recursion of `quantitative-refinement` produces at each step — the
shared parent map, the growth of the source skeleton, the nesting of the skeleton maps, and the
two shrinking estimates — and `StageSequence.limitTower` turns one into a `LimitTower` for the
concrete source and target of the problem.

Every field is either read off a
`GeneratedPair` or is one of the four recorded facts about the concrete domains. The point of
writing it before the recursion exists is that it pins the interface down: the recursion now has
a single named target, and any mismatch between what `thm:finite-transfer` delivers and what the
limit section demands shows up here rather than at the end. Two such mismatches would otherwise
have been easy to miss, and both check out:

* `LimitTower` wants the *same* parent map on both sides (`srcRefines` and `tgtRefines` along one
  `par n`). `IsPartialTransferOf` delivers exactly that — its `refines_src` and `refines_tgt`
  share `par` — which is `lem:refinement-compatibility`(c).
* `LimitTower` wants the two cell decompositions against *closed* domains `C ∪ D` and `Q`, and
  `GeneratedPair` is parametrized by exactly those two sets.

## The four facts about the concrete domains

`LimitTower` asks for the source domain to be closed and bounded and its interior open, and the
same for the target. On the source side `IsSeparating C` gives all three:
`Schoenflies.isClosed_union_inside`, `Schoenflies.union_inside_sdiff` with
`IsSeparating.isOpen_inside`, and boundedness through `C = frontier (inside C) ⊆ closure (inside C)`
— which is why `isBounded_dom` needs no extra hypothesis, though `LimitMap.lean` warns that it is
not optional (`Metric.diam` is `0` on an unbounded set). On the target side they are the standard
facts about the square.

## Blueprint

* `Schoenflies.StageSequence` — the output of the recursion of the section *Quantitative
  refinement*: the stage-`n` matched cellulations `(Γ_n, Γ'_n)` with their parent maps and the
  two convergence statements of `prop:shrinking-stars`.
* `Schoenflies.StageSequence.limitTower` — the passage to the head of the section *The limit
  homeomorphism of the interiors*, i.e. to `tex 2568`'s "we now forget how the decompositions
  were constructed".
* `Schoenflies.StageSequence.isHomeoOn_F`, `.interior_homeomorphism` —
  **`prop:interior-homeomorphism`** for a stage sequence, which is the third conjunct of
  `Schoenflies.HasLimitHomeomorphism`.
-/

open Bornology Filter Metric Set Topology
open scoped Graph

namespace Schoenflies

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}

/-! ### The concrete domains

`LimitTower` is stated for arbitrary closed domains; the construction uses two. These are the
facts it asks about them, collected so that `limitTower` below reads as a repackaging. -/

/-! ### A sequence of transferred stages -/

namespace StageSequence

variable (T : StageSequence γ S₀ C)

/-- **`prop:interior-homeomorphism` for a stage sequence**, in the `Schoenflies.IsHomeoOn` shape
`Schoenflies.HasLimitHomeomorphism` asks for: the limit map is a homeomorphism of the open
Jordan domain onto the open square. -/
theorem isHomeoOn_F :
    IsHomeoOn T.limitTower.F T.limitTower.inv (inside C) (Plane.openSquare 0 1) := by
  have h := T.limitTower.isHomeoOn_F
  rwa [limitTower_region, limitTower_region'] at h

/-- **`prop:skeleton-agreement`** for a stage sequence: on the closed domain the limit map agrees
with every stage's skeleton homeomorphism wherever that stage's skeleton reaches.

This is the bridge that will discharge `Schoenflies.HasAnchorCrosscuts`: the crosscut a stage
produces between two anchors lies in that stage's skeleton, so `F` carries it to the target
crosscut by the *finite* map, and `Schoenflies.image_sdiff_eq_of_eqOn` finishes. -/
theorem F_eq_skelHomeo {n : ℕ} {x : Plane} (hx : x ∈ (T.stage n).src.skeletonSet)
    (hxD : x ∈ C ∪ inside C) : T.limitTower.F x = (T.stage n).homeo.toFun x :=
  CellStructure.LimitTower.F_eq_skelHomeo hx hxD

end StageSequence

end Schoenflies
end

section
-- module Solutions.Q146_CD.QuantitativeForwardStages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Quantitative forward local-grid stages

The local-grid attachment supplies a complete raw grid in the source skeleton.
This module turns that containment into the pointwise source-star estimate used by
`prop:shrinking-stars`, and records that the target face mesh from the preceding reverse stage
survives the forward refinement.
-/

open Metric Set

namespace Schoenflies

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}
  {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}

/-- The frame of a positive local-grid square is contained in its raw grid carrier. -/
theorem localGrid_frame_subset {p : Plane} {s : ℝ} {k : ℕ}
    (hs : 0 < s) (hk : 1 ≤ k) :
    Plane.closedSquare p s \ Plane.openSquare p s ⊆
      cover (localGridEdges p s k) := by
  intro z hz
  have hclosed := hz.1
  rw [Plane.closedSquare_eq_inter] at hclosed
  have hopen := hz.2
  rw [Plane.openSquare_eq_inter] at hopen
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hclosed
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, not_and_or, not_lt] at hopen
  rcases hopen with hX | hY
  · rcases hX with hleft | hright
    · exact mem_cover_of_coord_eq hs hk (Nat.zero_le k) hz.1 (by
        rw [localGridX_zero]
        linarith [hclosed.1.1])
    · exact mem_cover_of_coord_eq hs hk (le_refl k) hz.1 (by
        rw [localGridX_last hk]
        linarith [hclosed.1.2])
  · rcases hY with hbottom | htop
    · exact mem_cover_of_coord_eq' hs hk (Nat.zero_le k) hz.1 (by
        rw [localGridY_zero]
        linarith [hclosed.2.1])
    · exact mem_cover_of_coord_eq' hs hk (le_refl k) hz.1 (by
        rw [localGridY_last hk]
        linarith [hclosed.2.2])

namespace LocalGridForwardStageData

variable {p : Plane} {s epsilon : ℝ}
  (w : LocalGridForwardStageData P p s epsilon)

/-- Every new source face incident with a point in the open grid window stays inside that
window.  Its connected open cell cannot cross the grid's outer frame, which is now part of the
source skeleton. -/
theorem face_subset_openSquare (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    {x : Plane} (hx : x ∈ Plane.openSquare p s)
    {F : γ} (hF : F ∈ w.pair.str.faces)
    (hsub : w.pair.str.sub (w.pair.src.carrier x) F) :
    w.pair.src.cell F ⊆ Plane.openSquare p s := by
  have hxClosed : x ∈ Plane.closedSquare p s := by
    change Plane.supDist x p ≤ s
    exact hx.le
  have hxDom : x ∈ C ∪ inside C := (hwindow hxClosed).1
  have hxCell : x ∈ w.pair.src.cell (w.pair.src.carrier x) :=
    w.pair.src_isCellDecomposition.mem_cell_carrier hxDom
  have hxClosure : x ∈ closure (w.pair.src.cell F) :=
    w.pair.src_isCellDecomposition.mem_closure_face
      (w.pair.src_isCellDecomposition.mem_cells_carrier hxDom) hF hsub hxCell
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.isOpen_iff.1 (Plane.isOpen_openSquare p s) x hx
  obtain ⟨y, hyFace, hyDist⟩ := Metric.mem_closure_iff.1 hxClosure ρ hρ
  have hyOpen : y ∈ Plane.openSquare p s := hball (by
    rw [mem_ball, dist_comm]
    exact hyDist)
  have hfrontier : frontier (Plane.openSquare p s) ⊆ w.pair.src.skeletonSet := by
    intro z hz
    apply w.localGrid_subset
    rw [localGrid_eq, pieceListGraph_pointSet]
    exact localGrid_frame_subset hs (one_le_localGridCount s epsilon)
      (frontier_openSquare_subset p s hz)
  exact subset_of_isPreconnected_of_frontier_disjoint
    (Plane.isOpen_openSquare p s)
    (w.pair.src_isFaceJordan.isConnected hF).isPreconnected
    ((w.pair.src.disjoint_cell_skeletonSet
      w.pair.src_isCellDecomposition hF).mono_right hfrontier)
    ⟨y, hyFace, hyOpen⟩

/-- Every source face incident with a point in the open window has closed diameter at most the
chosen local-grid mesh bound. -/
theorem diam_closure_face_le (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    {x : Plane} (hx : x ∈ Plane.openSquare p s)
    {F : γ} (hF : F ∈ w.pair.str.faces)
    (hsub : w.pair.str.sub (w.pair.src.carrier x) F) :
    diam (closure (w.pair.src.cell F)) ≤ epsilon := by
  rw [Metric.diam_closure]
  apply Metric.diam_le_of_forall_dist_le hepsilon.le
  intro y hy z hz
  apply le_of_lt
  refine lt_trans ?_ (localGridCount_spec (s := s) hepsilon)
  apply dist_lt_of_avoiding_localGrid (p := p) hs
    (one_le_localGridCount s epsilon)
    (w.pair.src_isFaceJordan.isConnected hF).isPreconnected
    ((w.face_subset_openSquare hs hwindow hx hF hsub).trans fun q hq => by
      change Plane.supDist q p ≤ s
      exact hq.le)
  · intro q hq hqGrid
    exact Set.disjoint_left.1
      (w.pair.src.disjoint_cell_skeletonSet
        w.pair.src_isCellDecomposition hF) hq
      (w.localGrid_subset (by
        rw [localGrid_eq, pieceListGraph_pointSet]
        exact hqGrid))
  · exact hy
  · exact hz

/-- **`lem:grid-star-estimate`.** At a point in the open grid window, the new source star has
diameter at most twice the selected mesh bound. -/
theorem diam_sourceStar_le (hC : IsSeparating C)
    (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    {x : Plane} (hx : x ∈ Plane.openSquare p s) :
    diam (w.pair.src.star (w.pair.src.carrier x)) ≤ 2 * epsilon := by
  have hxClosed : x ∈ Plane.closedSquare p s := by
    change Plane.supDist x p ≤ s
    exact hx.le
  have hxDom : x ∈ C ∪ inside C := (hwindow hxClosed).1
  exact w.pair.src_isCellDecomposition.diam_star_le
    w.pair.str_combInvariants (isBounded_union_inside hC)
    (w.pair.src_isCellDecomposition.mem_cells_carrier hxDom)
    (fun F hF hsub => w.diam_closure_face_le hs hepsilon hwindow hx hF hsub)

end LocalGridForwardStageData

namespace QuantitativeForwardStage

variable {p : Plane} {windowEpsilon meshEpsilon targetBound : ℝ}
  (w : QuantitativeForwardStage P p windowEpsilon meshEpsilon targetBound)

/-- The shared parent map to the preceding stage. -/
abbrev parent : γ → γ := w.forward.parent

omit [Nonempty γ] in
/-- The forward successor exposes the common transition interface. -/
theorem transition : StageTransition w.pair P w.parent := w.forward.transition

/-- The local-grid estimate in the window form used by `prop:shrinking-stars`. -/
theorem diam_sourceStar_le (hC : IsSeparating C)
    (hp : p ∈ inside C)
    (hwindowEpsilon : 0 < windowEpsilon) (hmeshEpsilon : 0 < meshEpsilon)
    {x : Plane} (hx : x ∈ openWindow C windowEpsilon p) :
    diam (w.pair.src.star (w.pair.src.carrier x)) ≤ 2 * meshEpsilon := by
  have hwindow : window C windowEpsilon p ⊆ (C ∪ inside C) \ C := by
    intro z hz
    have hzInside := window_subset_inside hC.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty hC hp hwindowEpsilon hz
    exact ⟨Or.inr hzInside, inside_subset_compl hzInside⟩
  exact w.forward.diam_sourceStar_le hC
    (windowRadius_pos hC.isJordanCurve.isCompact hC.isJordanCurve.nonempty
      (fun hpC => inside_subset_compl hp hpC))
    hmeshEpsilon hwindow hx

end QuantitativeForwardStage

namespace QuantitativeSuccessor

variable {anchors : List Plane} {p : Plane}
  {windowEpsilon sourceBound targetBound : ℝ}
  (w : QuantitativeSuccessor P anchors p windowEpsilon sourceBound targetBound)

/-- The composite shared parent map to the preceding full stage. -/
abbrev parent : γ → γ := w.reverse.parent ∘ w.forward.parent

omit [Nonempty γ] in
/-- The reverse and forward transitions compose to one full-stage transition. -/
theorem transition : StageTransition w.pair P w.parent :=
  w.forward.transition.trans w.reverse.transition

omit [Nonempty γ] in
/-- The uniform target-star estimate survives the following forward refinement. -/
theorem diam_targetStar_lt {σ : γ} (hσ : σ ∈ w.pair.str.cells) :
    diam (w.pair.tgt.star σ) < targetBound := by
  have hstar := TargetFaceMesh.diam_star_lt w.forward.targetFaceMesh hσ
  linarith [w.reverse.delta_lt_half_bound]

/-- The pointwise source-star estimate at every point caught by this stage's window. -/
theorem diam_sourceStar_le (hC : IsSeparating C) (hp : p ∈ inside C)
    (hwindowEpsilon : 0 < windowEpsilon) (hsourceBound : 0 < sourceBound)
    {x : Plane} (hx : x ∈ openWindow C windowEpsilon p) :
    diam (w.pair.src.star (w.pair.src.carrier x)) ≤ 2 * sourceBound :=
  w.forward.diam_sourceStar_le hC hp hwindowEpsilon hsourceBound hx

end QuantitativeSuccessor

omit [Nonempty γ] in
/-- **Quantitative successor.** Starting from any generated stage, construct a
refinement with the requested target-star bound and a source-star bound throughout the selected
window. -/
theorem GeneratedPair.exists_quantitativeSuccessor [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (anchors : List Plane) {p : Plane} (hp : p ∈ inside C)
    {windowEpsilon sourceBound targetBound : ℝ}
    (hwindowEpsilon : 0 < windowEpsilon) (hsourceBound : 0 < sourceBound)
    (htargetBound : 0 < targetBound) :
    Nonempty (QuantitativeSuccessor P anchors p
      windowEpsilon sourceBound targetBound) := by
  obtain ⟨r⟩ := exists_quantitativeReverseStage P
    hC hcycle anchors htargetBound
  obtain ⟨f⟩ := r.pair.exists_quantitativeForwardStage hC hp
    hwindowEpsilon hsourceBound
    r.overlay.transfer.src_isAdmissible.isConnected_nonboundary r.targetFaceMesh
  exact ⟨{ reverse := r, forward := f }⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.QuantitativeRecursion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The recursive quantitative stage construction

This module iterates the two-sided quantitative successor. Window centres are
read from a recurrent sequence and all three quantitative parameters use a dyadic scale.
-/

open Filter Metric Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

namespace QuantitativeSchedule

variable (q : QuantitativeSchedule C)

theorem centre_mem (n : ℕ) : q.centre n ∈ inside C := q.centreBase_mem _

end QuantitativeSchedule

variable [Infinite γ]
  (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
  (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
  (q : QuantitativeSchedule C)

/-- Choose a quantitative successor at stage `n`. -/
noncomputable def scheduledQuantitativeSuccessor
    (n : ℕ)
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)) :
    QuantitativeSuccessor P (q.anchors n) (q.centre n)
      (dyadicScale n) (dyadicScale n) (dyadicTargetBound n) :=
  Classical.choice (P.exists_quantitativeSuccessor hC hcycle (q.anchors n)
    (q.centre_mem n) (dyadicScale_pos n) (dyadicScale_pos n)
      (dyadicTargetBound_pos n))

/-- The recursively chosen generated pairs. -/
noncomputable def quantitativeStage : ℕ →
    GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  fun n => Nat.rec P₀
    (fun k P => (scheduledQuantitativeSuccessor hC hcycle q k P).pair) n

@[simp] theorem quantitativeStage_zero :
    quantitativeStage P₀ hC hcycle q 0 = P₀ := rfl

@[simp] theorem quantitativeStage_succ (n : ℕ) :
    quantitativeStage P₀ hC hcycle q (n + 1) =
      (scheduledQuantitativeSuccessor hC hcycle q n
        (quantitativeStage P₀ hC hcycle q n)).pair := by
  rfl

/-- The composite parent map selected at successor `n`. -/
noncomputable def quantitativeParent (n : ℕ) : γ → γ :=
  (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).parent

/-- Consecutive recursively chosen stages satisfy the common transition interface. -/
theorem quantitativeTransition (n : ℕ) :
    StageTransition
      (quantitativeStage P₀ hC hcycle q (n + 1))
      (quantitativeStage P₀ hC hcycle q n)
      (quantitativeParent P₀ hC hcycle q n) := by
  rw [quantitativeStage_succ]
  exact (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).transition

/-- Every noninitial target star satisfies the scheduled dyadic bound. -/
theorem quantitativeStage_diam_targetStar_lt (n : ℕ) {σ : γ}
    (hσ : σ ∈ (quantitativeStage P₀ hC hcycle q (n + 1)).str.cells) :
    diam ((quantitativeStage P₀ hC hcycle q (n + 1)).tgt.star σ) <
      dyadicTargetBound n := by
  rw [quantitativeStage_succ] at hσ ⊢
  exact (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).diam_targetStar_lt hσ

/-- Every target star satisfies the stage-indexed uniform bound, including stage zero. -/
theorem quantitativeStage_diam_targetStar_le (n : ℕ) {σ : γ}
    (hσ : σ ∈ (quantitativeStage P₀ hC hcycle q n).str.cells) :
    diam ((quantitativeStage P₀ hC hcycle q n).tgt.star σ) ≤
      quantitativeTargetEps n := by
  cases n with
  | zero =>
      have hstar : P₀.tgt.star σ ⊆ Plane.closedSquare 0 1 :=
        (P₀.tgt_isCellDecomposition.star_subset_closure_domain
          P₀.str_combInvariants).trans
            (Plane.isClosed_closedSquare 0 1).closure_subset
      have hsquare : Plane.closedSquare 0 1 ⊆ ball (0 : Plane) 2 := by
        simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using
          (Plane.closedSquare_subset_ball (c := (0 : Plane)) (ρ := 2) (by norm_num))
      change diam (P₀.tgt.star σ) ≤ 4
      calc
        diam (P₀.tgt.star σ) ≤ 2 * (2 : ℝ) :=
          Metric.diam_le_of_subset_closedBall (by norm_num)
            (hstar.trans (hsquare.trans ball_subset_closedBall))
        _ = 4 := by norm_num
  | succ n =>
      exact (quantitativeStage_diam_targetStar_lt P₀ hC hcycle q n hσ).le

/-- At every point caught by the stage-`n` window, the successor source star satisfies the
scheduled dyadic bound. -/
theorem quantitativeStage_diam_sourceStar_le (n : ℕ) {x : Plane}
    (hx : x ∈ openWindow C (dyadicScale n) (q.centre n)) :
    diam ((quantitativeStage P₀ hC hcycle q (n + 1)).src.star
      ((quantitativeStage P₀ hC hcycle q (n + 1)).src.carrier x)) ≤
        2 * dyadicScale n := by
  rw [quantitativeStage_succ]
  exact (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).diam_sourceStar_le
      hC (q.centre_mem n) (dyadicScale_pos n) (dyadicScale_pos n) hx

/-- Source stars at a fixed point shrink monotonically through all later recursive stages. -/
theorem quantitativeStage_sourceStar_subset_of_le {n m : ℕ} (hnm : n ≤ m)
    {x : Plane} (hx : x ∈ C ∪ inside C) :
    (quantitativeStage P₀ hC hcycle q m).src.star
        ((quantitativeStage P₀ hC hcycle q m).src.carrier x) ⊆
      (quantitativeStage P₀ hC hcycle q n).src.star
        ((quantitativeStage P₀ hC hcycle q n).src.carrier x) := by
  induction m, hnm using Nat.le_induction with
  | base => exact subset_rfl
  | @succ m hnm ih =>
      exact ((quantitativeTransition P₀ hC hcycle q m).refines_src.star_carrier_subset
        (quantitativeStage P₀ hC hcycle q (m + 1)).str_combInvariants
        (quantitativeStage P₀ hC hcycle q m).src_isCellDecomposition
        (quantitativeStage P₀ hC hcycle q (m + 1)).src_isCellDecomposition hx).trans ih

/-- Metric density of the base centre sequence inside the Jordan domain. -/
def QuantitativeSchedule.CentresDense (q : QuantitativeSchedule C) : Prop :=
  ∀ x ∈ inside C, ∀ δ : ℝ, 0 < δ →
    ∃ k, Plane.supDist (q.centreBase k) x < δ

/-- A canonical schedule obtained by taking a dense sequence in the open Jordan domain.
The auxiliary anchor list may be empty: each target-mesh constructor adds whatever fresh
boundary anchors it needs. -/
noncomputable def denseQuantitativeSchedule (hC : IsSeparating C) :
    QuantitativeSchedule C := by
  letI : Nonempty (inside C) := hC.isConnected_inside.nonempty.to_subtype
  exact
    { centreBase := fun n => (TopologicalSpace.denseSeq (inside C) n : Plane)
      centreBase_mem := fun n => (TopologicalSpace.denseSeq (inside C) n).property
      anchors := fun _ => [] }

theorem denseQuantitativeSchedule_centresDense (hC : IsSeparating C) :
    (denseQuantitativeSchedule hC).CentresDense := by
  letI : Nonempty (inside C) := hC.isConnected_inside.nonempty.to_subtype
  intro x hx δ hδ
  obtain ⟨k, hk⟩ :=
    (TopologicalSpace.denseRange_denseSeq (inside C)).exists_dist_lt
      (⟨x, hx⟩ : inside C) hδ
  refine ⟨k, lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) ?_⟩
  rw [dist_comm] at hk
  simpa only [denseQuantitativeSchedule, Subtype.dist_eq] using hk

/-- The recurrent dense windows and dyadic mesh bounds force pointwise convergence of the
source-star diameters. -/
theorem tendsto_quantitativeStage_diam_sourceStar
    (hdense : q.CentresDense) {x : Plane} (hx : x ∈ inside C) :
    Tendsto (fun n => diam ((quantitativeStage P₀ hC hcycle q n).src.star
      ((quantitativeStage P₀ hC hcycle q n).src.carrier x))) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro η hη
  have hxC : x ∉ C := fun hxC => inside_subset_compl hx hxC
  have hr : 0 < supRadius C x :=
    supRadius_pos hC.isJordanCurve.isCompact hC.isJordanCurve.nonempty hxC
  obtain ⟨k, hk⟩ := hdense x hx (supRadius C x / 8) (by positivity)
  have hthreshold : 0 < min (supRadius C x / 8) (η / 2) := by positivity
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 tendsto_dyadicScale
    _ hthreshold
  obtain ⟨n, hnN₀, hncentre⟩ := exists_le_recur_eq q.centreBase k N₀
  have hnscaleDist := hN₀ n hnN₀
  have hnscale : dyadicScale n < min (supRadius C x / 8) (η / 2) := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (dyadicScale_pos n)] at hnscaleDist
    exact hnscaleDist
  have hnwindow : x ∈ openWindow C (dyadicScale n) (q.centre n) := by
    apply mem_openWindow_of_supDist_lt hC.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty
    · rw [QuantitativeSchedule.centre, hncentre]
      exact hk
    · exact hnscale.trans_le (min_le_left _ _)
  have hnstar := quantitativeStage_diam_sourceStar_le P₀ hC hcycle q n hnwindow
  refine ⟨n + 1, fun m hm => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg diam_nonneg]
  exact lt_of_le_of_lt
    (Metric.diam_mono
      (quantitativeStage_sourceStar_subset_of_le P₀ hC hcycle q hm (Or.inr hx))
      ((quantitativeStage P₀ hC hcycle q (n + 1)).src_isCellDecomposition.isBounded_star
        (quantitativeStage P₀ hC hcycle q (n + 1)).str_combInvariants
        (isBounded_union_inside hC)))
    (lt_of_le_of_lt hnstar (by
      have := hnscale.trans_le (min_le_right _ _)
      linarith))

/-- The complete quantitative recursion, in the exact interface consumed by the limit-map
construction. -/
noncomputable def quantitativeStageSequence
    (hbase : S₀.CombInvariants) (hdense : q.CentresDense) :
    StageSequence γ S₀ C where
  stage := quantitativeStage P₀ hC hcycle q
  par := quantitativeParent P₀ hC hcycle q
  transition := quantitativeTransition P₀ hC hcycle q
  eps := quantitativeTargetEps
  diam_tgtStar_le := quantitativeStage_diam_targetStar_le P₀ hC hcycle q
  tendsto_eps := tendsto_quantitativeTargetEps
  tendsto_diam_srcStar := by
    intro x hx
    exact tendsto_quantitativeStage_diam_sourceStar P₀ hC hcycle q hdense hx
  base := hbase
  isSeparating := hC

/-- The recursion with its canonical dense schedule.  No convergence hypothesis remains in
this interface. -/
noncomputable def denseQuantitativeStageSequence (hbase : S₀.CombInvariants) :
    StageSequence γ S₀ C :=
  quantitativeStageSequence P₀ hC hcycle (denseQuantitativeSchedule hC) hbase
    (denseQuantitativeSchedule_centresDense hC)

end Schoenflies
end

section
-- module Solutions.Q146_CD.InteriorHomeomorphism
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The interior homeomorphism

This module starts the quantitative recursion at the canonical initial matched pair.  It closes
the construction of the nested stage sequence and therefore obtains the limit homeomorphism
between the inside of an arbitrary Jordan curve and the open square.
-/

open Set

namespace Schoenflies

variable {C : Set Plane}

/-- The initial-pair interface and the endgame interface express the same restricted
homeomorphism data with fields in a different order. -/
theorem IsHomeoOn.toIsSetHomeoOn {u v : Plane → Plane} {X Y : Set Plane}
    (h : IsHomeoOn u v X Y) : IsSetHomeoOn u v X Y where
  continuousOn := h.continuousOn
  continuousOn_inv := h.continuousOn_inv
  mapsTo := h.mapsTo
  mapsTo_inv := h.mapsTo_inv
  leftInvOn := h.invOn.1
  rightInvOn := h.invOn.2

/-- The anchored initial pair using the boundary homeomorphism supplied by the caller. -/
noncomputable def prescribedAnchoredInitialData (hC : IsJordanCurve C)
    (u v : Plane → Plane) (hu : IsHomeoOn u v C modelCurve) :
    AnchoredInitialData C (anchorSet hC) :=
  (exists_anchoredInitialData_of_homeo hC (anchorSet hC) u v
    hu.toIsSetHomeoOn).choose

theorem prescribedAnchoredInitialData_u (hC : IsJordanCurve C)
    (u v : Plane → Plane) (hu : IsHomeoOn u v C modelCurve) :
    (prescribedAnchoredInitialData hC u v hu).toInitialData.u = u :=
  (exists_anchoredInitialData_of_homeo hC (anchorSet hC) u v
    hu.toIsSetHomeoOn).choose_spec.1

/-- The quantitative sequence starting with a prescribed boundary homeomorphism. -/
noncomputable def prescribedJordanStageSequence (hC : IsJordanCurve C)
    (u v : Plane → Plane) (hu : IsHomeoOn u v C modelCurve) :
    StageSequence InitialCell initialStructure C :=
  denseQuantitativeStageSequence
    (prescribedAnchoredInitialData hC u v hu).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      combInvariants_initialStructure

/-- The limit map selected from the prescribed initial pair agrees pointwise with the caller's
boundary homeomorphism. -/
theorem prescribedJordanStageSequence_F_eq_boundary (hC : IsJordanCurve C)
    (u v : Plane → Plane) (hu : IsHomeoOn u v C modelCurve) :
    EqOn (prescribedJordanStageSequence hC u v hu).limitTower.F u C := by
  intro x hx
  let D := prescribedAnchoredInitialData hC u v hu
  let T := prescribedJordanStageSequence hC u v hu
  have hxskel : x ∈ (T.stage 0).src.skeletonSet := by
    change x ∈ D.toInitialData.sourceRealization.skeletonSet
    rw [D.toInitialData.sourceRealization_skeletonSet]
    exact Or.inl hx
  calc
    T.limitTower.F x = (T.stage 0).homeo.toFun x :=
      T.F_eq_skelHomeo hxskel (Or.inl hx)
    _ = D.toInitialData.skeletonHomeo.toFun x := by rfl
    _ = D.toInitialData.u x := D.toInitialData.skeletonHomeo_eq_u hx
    _ = u x := by rw [prescribedAnchoredInitialData_u hC u v hu]

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryAnchors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Boundary anchors retained by the quantitative recursion

Every reverse quantitative stage selects a finite metric net of accessible points on the model
curve.  This module takes their countable union, proves it dense, transports it through the
prescribed boundary homeomorphism, and records the finite-stage witness for every transported
source anchor.

## Blueprint

This discharges `lem:anchor-density` and constructs the `HasAnchorCrosscuts` and `HasSpokes`
inputs used in `prop:boundary-continuity`.
-/

open Filter Metric Set
open scoped Graph

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

/-- An admissible realization of the closed Jordan domain is exactly a finite stage in the
form consumed by the skeleton-crosscut theorem. -/
theorem CellStructure.Realization.IsAdmissible.isStageOn
    {S : CellStructure γ} {R : S.Realization}
    (h : R.IsAdmissible C (C ∪ inside C)) :
    Graph.IsStageOn R.graph R.drawing C (inside C) where
  isDrawing := R.isDrawing
  polygonal := by
    intro e he hnonboundary
    have heSkel : e ∈ E(S.skel) := by rwa [R.edgeSet_graph] at he
    apply h.isPolygonal heSkel
    intro heOuter
    apply hnonboundary
    have heOuterMap : e ∈ E(S.outerGraph.map R.pos) := by
      rw [Graph.edgeSet_map]
      exact heOuter
    rw [← h.outerSet_eq]
    exact Graph.edgeArc_subset_pointSet heOuterMap
  disjoint := Set.disjoint_left.2 fun x hxC hxInside => inside_subset_compl hxInside hxC
  vertex_mem := by
    intro x hxV hxC
    have hxDom : x ∈ C ∪ inside C := h.skeletonSet_subset
      (Graph.vertexSet_subset_pointSet hxV)
    exact hxDom.resolve_left hxC
  edge_split := by
    intro e x y hlink
    have heSkel : e ∈ E(S.skel) := by
      rw [← R.edgeSet_graph]
      exact hlink.edge_mem
    by_cases heOuter : e ∈ E(S.outerGraph)
    · have heOuterMap : e ∈ E(S.outerGraph.map R.pos) := by
        rw [Graph.edgeSet_map]
        exact heOuter
      rw [← h.outerSet_eq]
      exact Or.inl (Graph.edgeArc_subset_pointSet heOuterMap)
    · right
      obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet heSkel
      have hcell := h.cell_subset heSkel heOuter
      rw [R.cell_edge hab, union_inside_sdiff] at hcell
      rcases hlink.eq_and_eq_or_eq_and_eq (hab.map R.pos) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcell
      · simpa only [Set.pair_comm] using hcell
  isConnected_diff := by
    rw [← h.outerSet_eq]
    exact h.isConnected_nonboundary

/-- A vertex approached by points of the graph off `C` is incident with an edge not contained
in `C`.  A sufficiently small vertex square excludes every other vertex and every nonincident
edge. -/
theorem Graph.IsDrawing.exists_nonboundary_incident_of_mem_closure
    {G : Graph Plane γ} {drawing : γ → ℝ → Plane} [G.Finite]
    (h : G.IsDrawing drawing) {c : Plane} (hcV : c ∈ V(G)) (hcC : c ∈ C)
  (hclosure : c ∈ closure (Graph.pointSet G drawing \ C)) :
    ∃ e, G.Inc e c ∧ Graph.Nonboundary drawing C e := by
  obtain ⟨r, hr, hvert, hedge⟩ := h.exists_square_at hcV
  obtain ⟨z, hzOpen, hzGraph, hzC⟩ := mem_closure_iff.1 hclosure
    (Plane.openSquare c r) (Plane.isOpen_openSquare c r) (Plane.mem_openSquare_self hr)
  have hzClosed : z ∈ Plane.closedSquare c r :=
    Plane.openSquare_subset_closedSquare c r hzOpen
  rcases hzGraph with hzV | hzE
  · have hzc : z = c := by
      by_contra hne
      exact hvert z hzV hne hzClosed
    exact absurd hcC (hzc ▸ hzC)
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
    have hinc : G.Inc e c := by
      by_contra hninc
      exact Set.disjoint_left.1 (hedge e he hninc) hzClosed hze
    exact ⟨e, hinc, fun hsub => hzC (hsub hze)⟩

/-- The set-level interior part of a finite stage is the point set of the trace subgraph whose
support is the open region. -/
theorem Graph.pointSet_traceGraph_eq_interiorPart
    {G : Graph Plane γ} {drawing : γ → ℝ → Plane}
    (h : G.IsDrawing drawing) (D : Set Plane) :
    Graph.pointSet (Graph.traceGraph G drawing D) drawing =
      Graph.interiorPart G drawing D := by
  apply Set.Subset.antisymm
  · rintro z (hzV | hzE)
    · exact Or.inl hzV
    · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
      obtain ⟨x, y, hxy⟩ :=
        (Graph.traceGraph G drawing D).exists_isLink_of_mem_edgeSet he
      have ht := (Graph.traceGraph_isLink D).1 hxy
      exact Or.inr (Set.mem_iUnion₂.2 ⟨e, ⟨ht.2.1.edge_mem, ht.1⟩, hze⟩)
  · rintro z (hzV | hzE)
    · exact Or.inl hzV
    · obtain ⟨e, ⟨he, heD⟩, hze⟩ := Set.mem_iUnion₂.1 hzE
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      have harc := h.edge_isArcBetween hxy
      apply Or.inr
      exact Set.mem_iUnion₂.2 ⟨e, by
        rw [Graph.edgeSet_eq_setOf_exists_isLink]
        exact ⟨x, y, (Graph.traceGraph_isLink D).2
          ⟨heD, hxy, heD harc.left_mem, heD harc.right_mem⟩⟩, hze⟩

/-- A nonempty walk is polygonal when the edge arcs actually used by that walk are polygonal;
no condition on unused (and possibly wild outer) edges is needed. -/
theorem Graph.IsDrawing.isPolygonal_edgesCover_of_mem
    {G : Graph Plane γ} {drawing : γ → ℝ → Plane}
    (h : G.IsDrawing drawing) {a b : Plane} {W : List γ}
    (hW : G.IsWalk a W b) (hne : W ≠ [])
    (hpoly : ∀ e ∈ W, IsPolygonal (Graph.edgeArc drawing e)) :
    IsPolygonal (Graph.edgesCover drawing W) := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons a c b e W hlink hW ih =>
      rcases eq_or_ne W [] with rfl | hWne
      · simpa using hpoly e (List.mem_cons_self ..)
      · rw [Graph.edgesCover_cons]
        exact (hpoly e (List.mem_cons_self ..)).union
          (ih hWne fun f hf => hpoly f (List.mem_cons_of_mem e hf))
          ⟨c, (h.edge_isArcBetween hlink).right_mem,
            hW.left_mem_edgesCover h hWne⟩

/-- A skeleton homeomorphism carries the union of any finite list of corresponding edges onto
the union of the same edge list in the target realization. -/
theorem CellStructure.SkeletonHomeo.image_edgesCover
    {S : CellStructure γ} {R₁ R₂ : S.Realization}
    (g : CellStructure.SkeletonHomeo R₁ R₂) {W : List γ}
    (hW : ∀ e ∈ W, e ∈ E(S.skel)) :
    g.toFun '' Graph.edgesCover R₁.drawing W = Graph.edgesCover R₂.drawing W := by
  induction W with
  | nil => simp
  | cons e W ih =>
      rw [Graph.edgesCover_cons, Graph.edgesCover_cons, Set.image_union,
        g.edgeArc_image (hW e (List.mem_cons_self ..)),
        ih (fun f hf => hW f (List.mem_cons_of_mem e hf))]

/-- Strengthened skeleton-crosscut extraction: the crosscut is the carrier of a simple graph
path all of whose edges are nonboundary.  This edge-list form can be transported to a matched
realization edge by edge. -/
theorem Graph.IsStageOn.exists_crosscut_path
    {G : Graph Plane γ} {drawing : γ → ℝ → Plane} [G.Finite]
    (h : G.IsStageOn drawing C (inside C)) (hC : IsJordanCurve C)
    {a b : Plane} (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : ∃ e, G.Inc e a ∧ Graph.Nonboundary drawing C e)
    (hb : ∃ e, G.Inc e b ∧ Graph.Nonboundary drawing C e) :
    ∃ W : List γ, G.IsPath a W b ∧
      (∀ e ∈ W, Graph.Nonboundary drawing C e) ∧
      IsCrosscut C (Graph.edgesCover drawing W) a b := by
  classical
  by_cases hbig : ∃ (e : γ) (x y : Plane),
      G.IsLink e x y ∧ Graph.Nonboundary drawing C e ∧ x ∈ C ∧ y ∈ C
  · obtain ⟨e, x, y, hlink, hnonboundary, hxC, hyC⟩ := hbig
    have hlab : G.IsLink e a b :=
      h.isLink_of_ends_mem hlink hnonboundary hxC hyC hab ha hb
    have hpath : G.IsPath a [e] b := Graph.IsPath.single hlab hab
    have hpoly : IsPolygonal (Graph.edgesCover drawing [e]) := by
      rw [Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty]
      exact h.polygonal hlab.edge_mem hnonboundary
    have hinter : Graph.edgesCover drawing [e] \ {a, b} ⊆ inside C := by
      rw [Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty]
      rcases h.edge_split hlab with houter | hinter
      · exact absurd houter hnonboundary
      · exact hinter
    exact ⟨[e], hpath, fun f hf => by
        have hfe : f = e := by simpa using hf
        subst f
        exact hnonboundary,
      ⟨hC, h.isDrawing.path_isArcBetween hpath (by simp), hpoly,
        haC, hbC, hinter⟩⟩
  · have hcase : ∀ ⦃e : γ⦄ ⦃x y : Plane⦄, G.IsLink e x y →
        Graph.Nonboundary drawing C e → x ∈ C → y ∉ C :=
      fun e x y hlink hnonboundary hxC hyC =>
        hbig ⟨e, x, y, hlink, hnonboundary, hxC, hyC⟩
    obtain ⟨ea, ⟨ya, hla⟩, hanb⟩ := ha
    obtain ⟨eb, ⟨yb, hlb⟩, hbnb⟩ := hb
    have hyaD : ya ∈ inside C :=
      h.vertex_mem hla.right_mem (hcase hla hanb haC)
    have hybD : yb ∈ inside C :=
      h.vertex_mem hlb.right_mem (hcase hlb hbnb hbC)
    let K := Graph.traceGraph G drawing (inside C)
    have hKle : K ≤ G := Graph.traceGraph_le _
    letI : K.Finite := Graph.Finite.of_le hKle
    have hKpoint : Graph.pointSet K drawing =
        Graph.interiorPart G drawing (inside C) :=
      Graph.pointSet_traceGraph_eq_interiorPart h.isDrawing (inside C)
    have hyaK : ya ∈ V(K) := by
      rw [Graph.traceGraph_vertexSet]
      exact ⟨hla.right_mem, hyaD⟩
    have hybK : yb ∈ V(K) := by
      rw [Graph.traceGraph_vertexSet]
      exact ⟨hlb.right_mem, hybD⟩
    have hKconn : K.Connected := Graph.connected_of_isPreconnected_pointSet
      (h.isDrawing.mono hKle)
      (hKpoint.symm ▸ h.isPreconnected_interiorPart hcase) ⟨ya, hyaK⟩
    obtain ⟨W, hWK⟩ := hKconn.exists_isPath hyaK hybK
    have hWG : G.IsPath ya W yb := hWK.mono hKle
    have hybne : yb ≠ b := fun heq =>
      h.notMem_of_mem_curve hbC (heq ▸ hybD)
    have hlast : G.IsPath yb [eb] b := Graph.IsPath.single hlb.symm hybne
    have htail : G.IsPath ya (W ++ [eb]) b := by
      apply hWG.append hlast
      intro y hyW hyLast
      have hyK : y ∈ V(K) := by
        rw [Graph.walkVertices_congr_of_le hKle
          (fun e he => hWK.edge_mem he)] at hyW
        exact Graph.walkVertices_subset_vertexSet hWK.left_mem hyW
      have hyD : y ∈ inside C := by
        rw [Graph.traceGraph_vertexSet] at hyK
        exact hyK.2
      rcases Graph.mem_walkVertices_iff.1 hyLast with rfl | hyCovered
      · rfl
      · obtain ⟨e, he, hinc⟩ := hyCovered
        have heq : e = eb := by simpa using he
        subst e
        rcases hinc.eq_or_eq_of_isLink hlb with rfl | rfl
        · exact absurd hbC (h.notMem_curve hyD)
        · rfl
    have hafresh : a ∉ G.walkVertices ya (W ++ [eb]) := by
      intro haTail
      rcases Graph.mem_walkVertices_iff.1 haTail with haya | haCovered
      · exact h.notMem_of_mem_curve haC (haya ▸ hyaD)
      · rw [Graph.coveredVertices_append] at haCovered
        rcases haCovered with haW | haeb
        · have haK : a ∈ V(K) := by
            have hcoverEq : G.coveredVertices W = K.coveredVertices W :=
              Graph.coveredVertices_congr_of_le hKle (fun e he => hWK.edge_mem he)
            exact Graph.coveredVertices_subset_vertexSet (hcoverEq ▸ haW)
          rw [Graph.traceGraph_vertexSet] at haK
          exact h.notMem_of_mem_curve haC haK.2
        · obtain ⟨e, he, hinc⟩ := haeb
          have heq : e = eb := by simpa using he
          subst e
          rcases hinc.eq_or_eq_of_isLink hlb with heq | heq
          · exact hab heq
          · exact h.notMem_of_mem_curve haC (heq ▸ hybD)
    let Wfull := ea :: (W ++ [eb])
    have hfull : G.IsPath a Wfull b := Graph.IsPath.cons hla htail hafresh
    have hfullne : Wfull ≠ [] := List.cons_ne_nil _ _
    have hWnonboundary : ∀ e ∈ Wfull, Graph.Nonboundary drawing C e := by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hanb
      rcases List.mem_append.1 he with heW | heLast
      · have heK := hWK.edge_mem heW
        obtain ⟨x, y, hxyK⟩ := K.exists_isLink_of_mem_edgeSet heK
        have ht := (Graph.traceGraph_isLink (inside C)).1 hxyK
        intro houter
        have hxArc := (h.isDrawing.edge_isArcBetween ht.2.1).left_mem
        exact h.notMem_of_mem_curve (houter hxArc) (ht.1 hxArc)
      · have heq : e = eb := by simpa using heLast
        exact heq ▸ hbnb
    have hpoly : IsPolygonal (Graph.edgesCover drawing Wfull) :=
      Graph.IsDrawing.isPolygonal_edgesCover_of_mem h.isDrawing hfull.isWalk hfullne
        (fun e he => h.polygonal (hfull.edge_mem he) (hWnonboundary e he))
    have hinter : Graph.edgesCover drawing Wfull \ {a, b} ⊆ inside C := by
      rintro z ⟨hzCover, hzab⟩
      apply h.pointSet_diff_subset
      refine ⟨Graph.edgesCover_subset_pointSet
        (fun e he => hfull.edge_mem he) hzCover, fun hzC => ?_⟩
      obtain ⟨e, he, hze⟩ := Graph.mem_edgesCover_iff.1 hzCover
      rcases List.mem_cons.1 he with rfl | he
      · rcases h.edgeArc_inter_curve hla hanb ⟨hze, hzC⟩ with rfl | rfl
        · exact hzab (Or.inl rfl)
        · exact h.notMem_of_mem_curve hzC hyaD
      · rcases List.mem_append.1 he with heW | heLast
        · have heK := hWK.edge_mem heW
          obtain ⟨x, y, hxyK⟩ := K.exists_isLink_of_mem_edgeSet heK
          have ht := (Graph.traceGraph_isLink (inside C)).1 hxyK
          exact h.notMem_of_mem_curve hzC (ht.1 hze)
        · have heq : e = eb := by simpa using heLast
          subst e
          rcases h.edgeArc_inter_curve hlb hbnb ⟨hze, hzC⟩ with rfl | rfl
          · exact hzab (Or.inr rfl)
          · exact h.notMem_of_mem_curve hzC hybD
    exact ⟨Wfull, hfull, hWnonboundary,
      ⟨hC, h.isDrawing.path_isArcBetween hfull hfullne, hpoly,
        haC, hbC, hinter⟩⟩

/-- Every radial half-spoke has arbitrarily small connected tails accumulating at its missing
outer endpoint. -/
theorem exists_halfSpoke_tail {N : ℕ} (hN : 2 ≤ N) (z : Plane)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ A : Set Plane, A ⊆ halfSpoke N z ∧ IsPreconnected A ∧ A ⊆ ball z delta ∧
      z ∈ closure A := by
  let f : ℝ → Plane := fun t => t • z
  have hf : Continuous f := continuous_id.smul continuous_const
  obtain ⟨kappa, hkappa, hclose⟩ :=
    Metric.continuousAt_iff.1 hf.continuousAt delta hdelta
  let mu : ℝ := min ((1 - (N : ℝ)⁻¹) / 2) (kappa / 2)
  have hinv : (N : ℝ)⁻¹ < 1 := inv_cast_lt_one hN
  have hmu : 0 < mu := by
    apply lt_min
    · linarith
    · linarith
  have hmugap : mu ≤ (1 - (N : ℝ)⁻¹) / 2 := min_le_left _ _
  have hmukappa : mu ≤ kappa / 2 := min_le_right _ _
  let a : ℝ := 1 - mu
  have ha : a < 1 := by simp only [a] <;> linarith
  have hinva : (N : ℝ)⁻¹ ≤ a := by simp only [a] <;> linarith
  refine ⟨f '' Ico a 1, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨t, ht, rfl⟩
    exact smul_mem_halfSpoke (hinva.trans ht.1) ht.2 z
  · exact ((isConnected_Ico ha).image f hf.continuousOn).isPreconnected
  · rintro y ⟨t, ht, rfl⟩
    rw [mem_ball]
    have htmu : 1 - t ≤ mu := by
      have := ht.1
      simp only [a] at this
      linarith
    have htkappa : dist t 1 < kappa := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le)]
      linarith
    simpa only [f, one_smul] using hclose htkappa
  · have h1cl : (1 : ℝ) ∈ closure (Ico a 1) := by
      rw [closure_Ico ha.ne]
      exact ⟨ha.le, le_rfl⟩
    have hclosure := mem_closure_image hf.continuousAt h1cl
    simpa only [f, one_smul] using hclosure

/-- All target-boundary points selected as fresh spoke endpoints by some reverse stage. -/
def quantitativeFreshTargetSet [Infinite γ]
    (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (q : QuantitativeSchedule C) : Set Plane :=
  {z | ∃ n, z ∈ (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).reverse.overlay.fresh}

theorem quantitativeFreshTargetSet_subset [Infinite γ]
    (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (q : QuantitativeSchedule C) :
    quantitativeFreshTargetSet P₀ hC hcycle q ⊆ modelCurve := by
  rintro z ⟨n, hn⟩
  exact (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).reverse.overlay.fresh_mem z hn

/-- The radial half-spoke attached to a fresh target anchor at successor `n` is retained by
the target skeleton of the complete two-sided successor. -/
theorem quantitativeFresh_halfSpoke_subset_targetSkeleton [Infinite γ]
    (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (q : QuantitativeSchedule C) {n : ℕ} {z : Plane}
    (hz : z ∈ (scheduledQuantitativeSuccessor hC hcycle q n
      (quantitativeStage P₀ hC hcycle q n)).reverse.overlay.fresh) :
    halfSpoke (meshCount ((scheduledQuantitativeSuccessor hC hcycle q n
      (quantitativeStage P₀ hC hcycle q n)).reverse.overlay.delta)) z ⊆
      (quantitativeStage P₀ hC hcycle q (n + 1)).tgt.skeletonSet := by
  let w := scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)
  rw [quantitativeStage_succ]
  change halfSpoke (meshCount w.reverse.overlay.delta) z ⊆ w.pair.tgt.skeletonSet
  intro y hy
  apply w.forward.transition.targetSkeletonSet_subset
  have hyMesh : y ∈ Graph.pointSet
      (squareMesh w.reverse.overlay.delta w.reverse.overlay.fresh (q.anchors n))
      segmentDrawing := by
    rw [squareMesh_pointSet]
    exact spokePiece_seg_subset_cover (two_le_meshCount w.reverse.overlay.delta) hz
      (halfSpoke_subset (two_le_meshCount w.reverse.overlay.delta) z hy)
  have hyOverlay := w.reverse.cover.squareMesh_subset_meshOverlay
    w.reverse.overlay.delta w.reverse.overlay.fresh (q.anchors n) hyMesh
  rw [w.reverse.overlay.transfer.skeletonSet_eq, Graph.pointSet_relabelEdges]
  exact hyOverlay

/-- The selected target anchors are dense on the model curve. -/
theorem quantitativeFreshTargetSet_dense [Infinite γ]
    (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (q : QuantitativeSchedule C) :
    modelCurve ⊆ closure (quantitativeFreshTargetSet P₀ hC hcycle q) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 tendsto_dyadicTargetBound η hη
  let w := scheduledQuantitativeSuccessor hC hcycle q N
    (quantitativeStage P₀ hC hcycle q N)
  obtain ⟨z, hz, hxz⟩ := w.reverse.overlay.fresh_net x hx
  have hboundDist := hN N le_rfl
  have hbound : dyadicTargetBound N < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (dyadicTargetBound_pos N)] at hboundDist
    exact hboundDist
  exact ⟨z, ⟨N, hz⟩,
    lt_trans hxz (lt_trans w.reverse.delta_lt_half_bound (by linarith))⟩

variable {u v : Plane → Plane} (hC : IsJordanCurve C)
  (hu : IsHomeoOn u v C modelCurve)

/-- The target anchor set for the recursion started with the prescribed boundary map. -/
noncomputable def prescribedTargetAnchorSet : Set Plane :=
  let hsep := jordan_curve_theorem hC
  quantitativeFreshTargetSet
    (prescribedAnchoredInitialData hC u v hu).generatedPair hsep
      outerEdgesFormCycle_initialStructure (denseQuantitativeSchedule hsep)

/-- The corresponding source anchors, transported by the prescribed boundary inverse. -/
noncomputable def prescribedSourceAnchorSet : Set Plane :=
  v '' prescribedTargetAnchorSet hC hu

theorem prescribedTargetAnchorSet_subset :
    prescribedTargetAnchorSet hC hu ⊆ modelCurve := by
  exact quantitativeFreshTargetSet_subset
    (prescribedAnchoredInitialData hC u v hu).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC))

theorem prescribedTargetAnchorSet_dense :
    modelCurve ⊆ closure (prescribedTargetAnchorSet hC hu) := by
  exact quantitativeFreshTargetSet_dense
    (prescribedAnchoredInitialData hC u v hu).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC))

theorem prescribedSourceAnchorSet_subset :
    prescribedSourceAnchorSet hC hu ⊆ C := by
  rintro x ⟨z, hz, rfl⟩
  exact hu.mapsTo_inv (prescribedTargetAnchorSet_subset hC hu hz)

/-- Density pulls back through the inverse side of a relative homeomorphism. -/
theorem IsHomeoOn.subset_closure_image_inv
    {f g : Plane → Plane} {s t A : Set Plane}
    (h : IsHomeoOn f g s t) (hA : A ⊆ t) (hdense : t ⊆ closure A) :
    s ⊆ closure (g '' A) := by
  intro x hx
  have hfx : f x ∈ t := h.mapsTo hx
  have hcont : ContinuousWithinAt g A (f x) :=
    (h.continuousOn_inv (f x) hfx).mono hA
  have hcl : g (f x) ∈ closure (g '' A) :=
    hcont.mem_closure_image (hdense hfx)
  rwa [h.invOn.1 hx] at hcl

/- Density transports back through the prescribed boundary homeomorphism. -/
theorem prescribedSourceAnchorSet_dense :
    C ⊆ closure (prescribedSourceAnchorSet hC hu) := by
  exact IsHomeoOn.subset_closure_image_inv hu
    (prescribedTargetAnchorSet_subset hC hu)
    (prescribedTargetAnchorSet_dense hC hu)

/-- Every stage skeleton homeomorphism still agrees with the prescribed boundary map. -/
theorem prescribedJordanStage_homeo_eq_boundary (n : ℕ) :
    EqOn ((prescribedJordanStageSequence hC u v hu).stage n).homeo.toFun u C := by
  intro x hx
  let T := prescribedJordanStageSequence hC u v hu
  have hxouter : x ∈ (T.stage n).src.outerSet := by
    rw [(T.stage n).src_isWeaklyAdmissible.outerSet_eq]
    exact hx
  have hxskel : x ∈ (T.stage n).src.skeletonSet :=
    (T.stage n).src.outerSet_subset_skeletonSet hxouter
  exact (T.F_eq_skelHomeo hxskel (Or.inl hx)).symm.trans
    (prescribedJordanStageSequence_F_eq_boundary hC u v hu hx)

/-- On the model curve, the inverse of every finite-stage skeleton map is the prescribed
boundary inverse. -/
theorem prescribedJordanStage_invFun_eq_boundaryInv (n : ℕ) {z : Plane}
    (hz : z ∈ modelCurve) :
    ((prescribedJordanStageSequence hC u v hu).stage n).homeo.invFun z = v z := by
  let T := prescribedJordanStageSequence hC u v hu
  let x := (T.stage n).homeo.invFun z
  have hzouter : z ∈ (T.stage n).tgt.outerSet := by
    rw [(T.stage n).tgt_isWeaklyAdmissible.outerSet_eq]
    exact hz
  have hzskel : z ∈ (T.stage n).tgt.skeletonSet :=
    (T.stage n).tgt.outerSet_subset_skeletonSet hzouter
  have hxouter : x ∈ (T.stage n).src.outerSet := by
    rw [← (T.stage n).homeo.symm.image_outerSet]
    exact ⟨z, hzouter, rfl⟩
  have hxC : x ∈ C := by
    rw [(T.stage n).src_isWeaklyAdmissible.outerSet_eq] at hxouter
    exact hxouter
  apply hu.injOn hxC (hu.mapsTo_inv hz)
  calc
    u x = (T.stage n).homeo.toFun x :=
      (prescribedJordanStage_homeo_eq_boundary hC hu n hxC).symm
    _ = z := (T.stage n).homeo.rightInvOn hzskel
    _ = u (v z) := (hu.invOn.2 hz).symm

/-- Every noninitial prescribed stage is source-admissible; it is the output of the forward
half of the preceding quantitative successor. -/
theorem prescribedJordanStage_succ_src_isAdmissible (n : ℕ) :
    ((prescribedJordanStageSequence hC u v hu).stage (n + 1)).src.IsAdmissible
      C (C ∪ inside C) := by
  change (quantitativeStage
    (prescribedAnchoredInitialData hC u v hu).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
    (denseQuantitativeSchedule (jordan_curve_theorem hC)) (n + 1)).src.IsAdmissible
      C (C ∪ inside C)
  rw [quantitativeStage_succ]
  exact (scheduledQuantitativeSuccessor
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
    (denseQuantitativeSchedule (jordan_curve_theorem hC)) n
    (quantitativeStage
      (prescribedAnchoredInitialData hC u v hu).generatedPair
      (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC)) n)).forward.forward.src_isAdmissible

/-- Each transported source anchor comes with the reverse stage at which it was selected and
the exact finite-stage source endpoint realizing it. -/
theorem prescribedSourceAnchorSet_stageWitness {c : Plane}
    (hc : c ∈ prescribedSourceAnchorSet hC hu) :
    ∃ n z, z ∈ (scheduledQuantitativeSuccessor
        (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
        (denseQuantitativeSchedule (jordan_curve_theorem hC)) n
        ((prescribedJordanStageSequence hC u v hu).stage n)).reverse.overlay.fresh ∧
      c = v z ∧
      ((prescribedJordanStageSequence hC u v hu).stage n).homeo.invFun z = c := by
  obtain ⟨z, hz, rfl⟩ := hc
  obtain ⟨n, hn⟩ := hz
  refine ⟨n, z, hn, rfl, ?_⟩
  apply prescribedJordanStage_invFun_eq_boundaryInv hC hu n
  exact prescribedTargetAnchorSet_subset hC hu ⟨n, hn⟩

/-- Every selected source anchor is approached by the open nonboundary part of one finite-stage
skeleton.  This retains precisely the finite combinatorial germ needed to find an incident
nonboundary edge after making the anchor a vertex. -/
theorem prescribedSourceAnchorSet_stageClosure {c : Plane}
    (hc : c ∈ prescribedSourceAnchorSet hC hu) :
    ∃ n, c ∈ closure
      (((prescribedJordanStageSequence hC u v hu).stage (n + 1)).src.skeletonSet \ C) := by
  obtain ⟨n, z, hz, hcz, -⟩ := prescribedSourceAnchorSet_stageWitness hC hu hc
  let T := prescribedJordanStageSequence hC u v hu
  let w := scheduledQuantitativeSuccessor
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
    (denseQuantitativeSchedule (jordan_curve_theorem hC)) n (T.stage n)
  change z ∈ w.reverse.overlay.fresh at hz
  have hzCurve : z ∈ modelCurve := w.reverse.overlay.fresh_mem z hz
  have hhalf : halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
      (T.stage (n + 1)).tgt.skeletonSet := by
    change halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
      (quantitativeStage
        (prescribedAnchoredInitialData hC u v hu).generatedPair
        (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
        (denseQuantitativeSchedule (jordan_curve_theorem hC)) (n + 1)).tgt.skeletonSet
    exact quantitativeFresh_halfSpoke_subset_targetSkeleton
      (prescribedAnchoredInitialData hC u v hu).generatedPair
      (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC)) hz
  have hzSkel : z ∈ (T.stage (n + 1)).tgt.skeletonSet := by
    have hzOuter : z ∈ (T.stage (n + 1)).tgt.outerSet := by
      rw [(T.stage (n + 1)).tgt_isWeaklyAdmissible.outerSet_eq]
      exact hzCurve
    exact (T.stage (n + 1)).tgt.outerSet_subset_skeletonSet hzOuter
  obtain ⟨A, hAhalf, -, -, hzA⟩ := exists_halfSpoke_tail
    (two_le_meshCount w.reverse.overlay.delta) z one_pos
  have hzHalf : z ∈ closure (halfSpoke (meshCount w.reverse.overlay.delta) z) :=
    closure_mono hAhalf hzA
  have hInvImage : (T.stage (n + 1)).homeo.invFun ''
      halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
        (T.stage (n + 1)).src.skeletonSet \ C := by
    rintro x ⟨y, hyHalf, rfl⟩
    have hySkel : y ∈ (T.stage (n + 1)).tgt.skeletonSet := hhalf hyHalf
    have hxSkel : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.skeletonSet := by
      rw [← (T.stage (n + 1)).homeo.symm.image_skeletonSet]
      exact ⟨y, hySkel, rfl⟩
    refine ⟨hxSkel, fun hxC => ?_⟩
    have hxOuter : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.outerSet := by
      rw [(T.stage (n + 1)).src_isWeaklyAdmissible.outerSet_eq]
      exact hxC
    have hyOuter : y ∈ (T.stage (n + 1)).tgt.outerSet := by
      rw [← (T.stage (n + 1)).homeo.image_outerSet]
      exact ⟨(T.stage (n + 1)).homeo.invFun y, hxOuter,
        (T.stage (n + 1)).homeo.rightInvOn hySkel⟩
    have hyCurve : y ∈ modelCurve := by
      rw [← (T.stage (n + 1)).tgt_isWeaklyAdmissible.outerSet_eq]
      exact hyOuter
    exact halfSpoke_disjoint_modelCurve
      (two_le_meshCount w.reverse.overlay.delta) hzCurve y hyHalf hyCurve
  have hInvClosure : (T.stage (n + 1)).homeo.invFun z ∈ closure
      ((T.stage (n + 1)).homeo.invFun ''
        halfSpoke (meshCount w.reverse.overlay.delta) z) := by
    have hcont :=
      ((T.stage (n + 1)).homeo.continuousOn_invFun z hzSkel).mono hhalf
    exact ContinuousWithinAt.mem_closure_image hcont hzHalf
  refine ⟨n, ?_⟩
  have hcInv : (T.stage (n + 1)).homeo.invFun z = c := by
    rw [prescribedJordanStage_invFun_eq_boundaryInv hC hu (n + 1) hzCurve, ← hcz]
  rw [← hcInv]
  exact closure_mono hInvImage hInvClosure

/-- The dense prescribed anchor set has the spoke germs required by boundary continuity.  A
fresh radial target segment is already present at the reverse half-stage; target-skeleton
monotonicity retains it through the following forward refinement, and the finite-stage inverse
transports an arbitrarily short tail into the Jordan domain. -/
theorem prescribedSourceAnchorSet_hasSpokes :
    HasSpokes C (prescribedSourceAnchorSet hC hu) u
      (prescribedJordanStageSequence hC u v hu).limitTower.F := by
  intro c hc epsilon hepsilon
  obtain ⟨n, z, hz, hcz, -⟩ := prescribedSourceAnchorSet_stageWitness hC hu hc
  let T := prescribedJordanStageSequence hC u v hu
  let w := scheduledQuantitativeSuccessor
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
    (denseQuantitativeSchedule (jordan_curve_theorem hC)) n (T.stage n)
  change z ∈ w.reverse.overlay.fresh at hz
  have hzCurve : z ∈ modelCurve := w.reverse.overlay.fresh_mem z hz
  have hhalf : halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
      (T.stage (n + 1)).tgt.skeletonSet := by
    change halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
      (quantitativeStage
        (prescribedAnchoredInitialData hC u v hu).generatedPair
        (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
        (denseQuantitativeSchedule (jordan_curve_theorem hC)) (n + 1)).tgt.skeletonSet
    exact quantitativeFresh_halfSpoke_subset_targetSkeleton
      (prescribedAnchoredInitialData hC u v hu).generatedPair
      (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC)) hz
  have hzSkel : z ∈ (T.stage (n + 1)).tgt.skeletonSet := by
    have hzOuter : z ∈ (T.stage (n + 1)).tgt.outerSet := by
      rw [(T.stage (n + 1)).tgt_isWeaklyAdmissible.outerSet_eq]
      exact hzCurve
    exact (T.stage (n + 1)).tgt.outerSet_subset_skeletonSet hzOuter
  obtain ⟨delta, hdelta, hclose⟩ := Metric.continuousWithinAt_iff.1
    ((T.stage (n + 1)).homeo.continuousOn_invFun z hzSkel) epsilon hepsilon
  obtain ⟨A, hAhalf, hAconn, hAball, hzcl⟩ :=
    exists_halfSpoke_tail (two_le_meshCount w.reverse.overlay.delta) z hdelta
  have hAskel : A ⊆ (T.stage (n + 1)).tgt.skeletonSet := hAhalf.trans hhalf
  let J : Set Plane := (T.stage (n + 1)).homeo.invFun '' A
  have hJinside : J ⊆ inside C := by
    rintro x ⟨y, hyA, rfl⟩
    have hySkel : y ∈ (T.stage (n + 1)).tgt.skeletonSet := hAskel hyA
    have hxSkel : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.skeletonSet := by
      rw [← (T.stage (n + 1)).homeo.symm.image_skeletonSet]
      exact ⟨y, hySkel, rfl⟩
    have hxDom : (T.stage (n + 1)).homeo.invFun y ∈ C ∪ inside C :=
      (T.stage (n + 1)).src_isCellDecomposition.skeletonSet_subset_domain hxSkel
    apply hxDom.resolve_left
    intro hxC
    have hxOuter : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.outerSet := by
      rw [(T.stage (n + 1)).src_isWeaklyAdmissible.outerSet_eq]
      exact hxC
    have hyOuter : y ∈ (T.stage (n + 1)).tgt.outerSet := by
      rw [← (T.stage (n + 1)).homeo.image_outerSet]
      exact ⟨(T.stage (n + 1)).homeo.invFun y, hxOuter,
        (T.stage (n + 1)).homeo.rightInvOn hySkel⟩
    have hyCurve : y ∈ modelCurve := by
      rw [← (T.stage (n + 1)).tgt_isWeaklyAdmissible.outerSet_eq]
      exact hyOuter
    exact halfSpoke_disjoint_modelCurve
      (two_le_meshCount w.reverse.overlay.delta) hzCurve y (hAhalf hyA) hyCurve
  have hJconn : IsPreconnected J := by
    exact hAconn.image (T.stage (n + 1)).homeo.invFun
      ((T.stage (n + 1)).homeo.continuousOn_invFun.mono hAskel)
  have hstageInv : (T.stage (n + 1)).homeo.invFun z = v z :=
    prescribedJordanStage_invFun_eq_boundaryInv hC hu (n + 1) hzCurve
  have hJball : J ⊆ ball c epsilon := by
    rintro x ⟨y, hyA, rfl⟩
    rw [mem_ball, hcz, ← hstageInv]
    exact hclose (hAskel hyA) (hAball hyA)
  have hccl : c ∈ closure J := by
    have hcont :=
      ((T.stage (n + 1)).homeo.continuousOn_invFun z hzSkel).mono hAskel
    have hcl := ContinuousWithinAt.mem_closure_image hcont hzcl
    rw [hstageInv, ← hcz] at hcl
    exact hcl
  have hAim : A ⊆ T.limitTower.F '' J := by
    intro y hyA
    have hySkel : y ∈ (T.stage (n + 1)).tgt.skeletonSet := hAskel hyA
    have hxSkel : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.skeletonSet := by
      rw [← (T.stage (n + 1)).homeo.symm.image_skeletonSet]
      exact ⟨y, hySkel, rfl⟩
    have hxDom : (T.stage (n + 1)).homeo.invFun y ∈ C ∪ inside C :=
      (T.stage (n + 1)).src_isCellDecomposition.skeletonSet_subset_domain hxSkel
    refine ⟨(T.stage (n + 1)).homeo.invFun y, ⟨y, hyA, rfl⟩, ?_⟩
    rw [T.F_eq_skelHomeo hxSkel hxDom,
      (T.stage (n + 1)).homeo.rightInvOn hySkel]
  have huc : u c = z := by
    rw [hcz]
    exact hu.invOn.2 hzCurve
  refine ⟨J, hJinside, hJconn, hJball, hccl, ?_⟩
  rw [huc]
  exact closure_mono hAim hzcl

/-- Any two distinct prescribed anchors are joined by a finite-stage crosscut, and the same
abstract edge path in the matched target skeleton is its image.  The limit map agrees with
that finite skeleton map on the source crosscut. -/
theorem prescribedSourceAnchorSet_hasAnchorCrosscuts :
    HasAnchorCrosscuts C (prescribedSourceAnchorSet hC hu) u
      (prescribedJordanStageSequence hC u v hu).limitTower.F := by
  classical
  intro a b ha hb hab
  have haC : a ∈ C := prescribedSourceAnchorSet_subset hC hu ha
  have hbC : b ∈ C := prescribedSourceAnchorSet_subset hC hu hb
  obtain ⟨na, hacl⟩ := prescribedSourceAnchorSet_stageClosure hC hu ha
  obtain ⟨nb, hbcl⟩ := prescribedSourceAnchorSet_stageClosure hC hu hb
  let T := prescribedJordanStageSequence hC u v hu
  let N := max na nb
  let P := T.stage (N + 1)
  have hna : na + 1 ≤ N + 1 := Nat.add_le_add_right (Nat.le_max_left na nb) 1
  have hnb : nb + 1 ≤ N + 1 := Nat.add_le_add_right (Nat.le_max_right na nb) 1
  have haclP : a ∈ closure (P.src.skeletonSet \ C) := by
    apply closure_mono ?_ hacl
    rintro x ⟨hx, hxC⟩
    exact ⟨T.limitTower.skeletonSet_mono_le hna hx, hxC⟩
  have hbclP : b ∈ closure (P.src.skeletonSet \ C) := by
    apply closure_mono ?_ hbcl
    rintro x ⟨hx, hxC⟩
    exact ⟨T.limitTower.skeletonSet_mono_le hnb hx, hxC⟩
  have haSkel : a ∈ P.src.skeletonSet := by
    apply P.src.outerSet_subset_skeletonSet
    rw [P.src_isWeaklyAdmissible.outerSet_eq]
    exact haC
  have hbSkel : b ∈ P.src.skeletonSet := by
    apply P.src.outerSet_subset_skeletonSet
    rw [P.src_isWeaklyAdmissible.outerSet_eq]
    exact hbC
  obtain ⟨r⟩ := P.exists_subdivideSetData ((Set.finite_singleton b).insert a) (by
    rintro x (rfl | rfl)
    · exact haSkel
    · exact hbSkel)
  have haV : a ∈ V(r.pair.src.graph) := r.vertexSet_subset (Or.inl rfl)
  have hbV : b ∈ V(r.pair.src.graph) := r.vertexSet_subset (Or.inr rfl)
  have haclr : a ∈ closure (r.pair.src.skeletonSet \ C) := by
    rw [r.skeletonSet_eq]
    exact haclP
  have hbclr : b ∈ closure (r.pair.src.skeletonSet \ C) := by
    rw [r.skeletonSet_eq]
    exact hbclP
  have hPAdmissible : P.src.IsAdmissible C (C ∪ inside C) :=
    prescribedJordanStage_succ_src_isAdmissible hC hu N
  have hrAdmissible : r.pair.src.IsAdmissible C (C ∪ inside C) := by
    apply r.pair.src_isAdmissible
    rw [r.pair.src_nonboundary_eq, r.skeletonSet_eq, ← P.src_nonboundary_eq]
    exact hPAdmissible.isConnected_nonboundary
  have hrTargetAdmissible :
      r.pair.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) :=
    r.pair.tgt_isAdmissible hrAdmissible.isConnected_nonboundary
  letI : r.pair.src.graph.Finite := CellStructure.Realization.finite_graph r.pair.src
  have hsourceStage := hrAdmissible.isStageOn
  have htargetStage : Graph.IsStageOn r.pair.tgt.graph r.pair.tgt.drawing
      modelCurve (inside modelCurve) := by
    apply CellStructure.Realization.IsAdmissible.isStageOn
    rw [modelCurve_union_inside]
    exact hrTargetAdmissible
  obtain ⟨ea, hea⟩ :=
    Graph.IsDrawing.exists_nonboundary_incident_of_mem_closure
      (G := r.pair.src.graph) (drawing := r.pair.src.drawing) (C := C)
      r.pair.src.isDrawing haV haC haclr
  obtain ⟨eb, heb⟩ :=
    Graph.IsDrawing.exists_nonboundary_incident_of_mem_closure
      (G := r.pair.src.graph) (drawing := r.pair.src.drawing) (C := C)
      r.pair.src.isDrawing hbV hbC hbclr
  obtain ⟨W, hWsrc, hWnonboundary, hPcross⟩ :=
    Graph.IsStageOn.exists_crosscut_path hsourceStage hC hab haC hbC
      ⟨ea, hea⟩ ⟨eb, heb⟩
  let Q : Set Plane := Graph.edgesCover r.pair.src.drawing W
  let Q' : Set Plane := r.pair.homeo.toFun '' Q
  have hQSkel : Q ⊆ r.pair.src.skeletonSet :=
    Graph.edgesCover_subset_pointSet (fun e he => hWsrc.edge_mem he)
  have hWedge : ∀ e ∈ W, e ∈ E(r.pair.str.skel) := by
    intro e he
    rw [← r.pair.src.edgeSet_graph]
    exact hWsrc.edge_mem he
  have hWnotOuter : ∀ e ∈ W, e ∉ E(r.pair.str.outerGraph) := by
    intro e he heOuter
    apply hWnonboundary e he
    intro x hx
    have hxOuter : x ∈ r.pair.src.outerSet :=
      Graph.edgeArc_subset_pointSet (by
        rw [Graph.edgeSet_map]
        exact heOuter) hx
    rwa [r.pair.src_isWeaklyAdmissible.outerSet_eq] at hxOuter
  rw [CellStructure.Realization.vertexSet_graph] at haV hbV
  obtain ⟨alpha, halpha, halphaPos⟩ := haV
  obtain ⟨beta, hbeta, hbetaPos⟩ := hbV
  have hsrcPathMapped : (r.pair.str.skel.map r.pair.src.pos).IsPath
      (r.pair.src.pos alpha) W (r.pair.src.pos beta) := by
    rw [halphaPos, hbetaPos]
    exact hWsrc
  obtain ⟨beta', hAbstractPath, hbeta'Pos⟩ :=
    Graph.IsPath.exists_lift_map r.pair.src.injOn_pos halpha hsrcPathMapped
  have hbeta'eq : beta' = beta :=
    r.pair.src.injOn_pos hAbstractPath.right_mem hbeta hbeta'Pos
  subst beta'
  have htargetPath : r.pair.tgt.graph.IsPath
      (r.pair.tgt.pos alpha) W (r.pair.tgt.pos beta) := by
    exact Graph.IsPath.map r.pair.tgt.injOn_pos hAbstractPath
  have htargetPoly : IsPolygonal (Graph.edgesCover r.pair.tgt.drawing W) :=
    Graph.IsDrawing.isPolygonal_edgesCover_of_mem r.pair.tgt.isDrawing
      htargetPath.isWalk (hWsrc.ne_nil hab) (fun e he =>
        hrTargetAdmissible.isPolygonal (hWedge e he) (hWnotOuter e he))
  have hQ'image : Q' = Graph.edgesCover r.pair.tgt.drawing W := by
    exact CellStructure.SkeletonHomeo.image_edgesCover r.pair.homeo hWedge
  have hga : r.pair.homeo.toFun a = u a := by
    calc
      r.pair.homeo.toFun a = P.homeo.toFun a := r.homeo_eqOn haSkel
      _ = u a := prescribedJordanStage_homeo_eq_boundary hC hu (N + 1) haC
  have hgb : r.pair.homeo.toFun b = u b := by
    calc
      r.pair.homeo.toFun b = P.homeo.toFun b := r.homeo_eqOn hbSkel
      _ = u b := prescribedJordanStage_homeo_eq_boundary hC hu (N + 1) hbC
  have hQ'target : IsCrosscut modelCurve Q'
      (r.pair.homeo.toFun a) (r.pair.homeo.toFun b) := by
    apply hPcross.image_of_injOn hQSkel r.pair.homeo.continuousOn_toFun
      r.pair.homeo.injOn isJordanCurve_modelCurve
    · change IsPolygonal Q'
      rw [hQ'image]
      exact htargetPoly
    · rw [hga]
      exact hu.mapsTo haC
    · rw [hgb]
      exact hu.mapsTo hbC
    · rintro y ⟨x, ⟨hxQ, hyEnds⟩, rfl⟩
      have hxSkel : x ∈ r.pair.src.skeletonSet := hQSkel hxQ
      have hySkel : r.pair.homeo.toFun x ∈ r.pair.tgt.skeletonSet := by
        rw [← r.pair.homeo.image_skeletonSet]
        exact Set.mem_image_of_mem _ hxSkel
      apply htargetStage.pointSet_diff_subset
      refine ⟨hySkel, fun hyCurve => ?_⟩
      have hyOuter : r.pair.homeo.toFun x ∈ r.pair.tgt.outerSet := by
        rw [r.pair.tgt_isWeaklyAdmissible.outerSet_eq]
        exact hyCurve
      have hxOuter : x ∈ r.pair.src.outerSet := by
        rw [← r.pair.homeo.symm.image_outerSet]
        exact ⟨r.pair.homeo.toFun x, hyOuter,
          r.pair.homeo.leftInvOn hxSkel⟩
      have hxC : x ∈ C := by
        rw [← r.pair.src_isWeaklyAdmissible.outerSet_eq]
        exact hxOuter
      have hxEnds : x ∈ ({a, b} : Set Plane) := by
        have hxInter : x ∈ Q ∩ C := ⟨hxQ, hxC⟩
        rw [hPcross.inter_eq] at hxInter
        exact hxInter
      rcases hxEnds with rfl | rfl
      · exact hyEnds (Or.inl rfl)
      · exact hyEnds (Or.inr rfl)
  have hFQ : Set.EqOn T.limitTower.F r.pair.homeo.toFun (Q \ {a, b}) := by
    intro x hx
    have hxP : x ∈ P.src.skeletonSet := by
      rw [← r.skeletonSet_eq]
      exact hQSkel hx.1
    have hxDom : x ∈ C ∪ inside C :=
      P.src_isCellDecomposition.skeletonSet_subset_domain hxP
    calc
      T.limitTower.F x = P.homeo.toFun x := T.F_eq_skelHomeo hxP hxDom
      _ = r.pair.homeo.toFun x := (r.homeo_eqOn hxP).symm
  have hagree : T.limitTower.F '' (Q \ {a, b}) =
      Q' \ {r.pair.homeo.toFun a, r.pair.homeo.toFun b} := by
    exact image_sdiff_eq_of_eqOn hQSkel r.pair.homeo.injOn
      hPcross.arc.left_mem hPcross.arc.right_mem hFQ
  refine ⟨Q, Q', hPcross, ?_, ?_⟩
  · simpa only [hga, hgb] using hQ'target
  · simpa only [hga, hgb] using hagree

end Schoenflies
end

section
-- module Solutions.Q146_CD.JordanSchoenflies
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Jordan–Schönflies theorem

The quantitative stage recursion supplies the interior homeomorphism.  Its fresh target nets
give a dense source anchor set; radial mesh spokes supply the boundary germs, and finite-stage
nonboundary edge paths supply matched crosscuts. These data prove `HasLimitHomeomorphism`, then
`SquareExtension`, and finally the relative Jordan–Schönflies theorem.

## Blueprint

The declarations below close `thm:square-extension` and `thm:main`; the intervening square
reduction, closed-interior, pointed, and exterior extensions are supplied by `Endgame.lean`.
-/

open Set

namespace Schoenflies

/-- All four inputs to boundary continuity are supplied by the prescribed quantitative stage
sequence. -/
theorem hasLimitHomeomorphism : HasLimitHomeomorphism := by
  intro C u v hC hu
  let T := prescribedJordanStageSequence hC u v hu
  exact ⟨prescribedSourceAnchorSet hC hu, T.limitTower.F, T.limitTower.inv,
    prescribedSourceAnchorSet_subset hC hu,
    prescribedSourceAnchorSet_dense hC hu,
    T.isHomeoOn_F,
    prescribedSourceAnchorSet_hasAnchorCrosscuts hC hu,
    prescribedSourceAnchorSet_hasSpokes hC hu⟩

/-- **`thm:square-extension`.** Every homeomorphism from a Jordan curve to the boundary of the
model square extends over the corresponding closed domains. -/
theorem squareExtension : SquareExtension :=
  squareExtension_of_hasLimitHomeomorphism hasLimitHomeomorphism

variable {C C' : Set Plane}

/-- **The blueprint's bundled statement.** Every homeomorphism between two
Jordan curves extends to a self-homeomorphism of the plane. -/
theorem jordan_schoenflies_of_homeomorph
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z :=
  jordan_schoenflies_of_homeomorph_of_squareExtension squareExtension hC hC' e

end Schoenflies
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarSchoenfliesProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The relative Jordan–Schoenflies theorem extends continuous circle embeddings.
The `schoenflies-lean` formalization is applied after converting the circle
embeddings to interval loops, without smoothness assumptions. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma circle_embedding_range_isJordanCurve (γ : Circle → Schoenflies.Plane)
    (hγ : Continuous γ) (hinj : Injective γ) :
    Schoenflies.IsJordanCurve (range γ) := by
  refine ⟨γ ∘ standardCircleTraversal, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (hγ.comp continuous_standardCircleTraversal).continuousOn
  · exact congrArg γ standardCircleTraversal_closes
  · exact hinj.injOn.comp standardCircleTraversal_injOn (mapsTo_univ _ _)
  · rw [image_comp, standardCircleTraversal_image, image_univ]

lemma planarSchoenflies : PlanarSchoenflies := by
  intro γ hγ hinj
  let e : ℂ ≃ₜ Schoenflies.Plane := complexPlaneCoordinates.toHomeomorph.symm
  let c0 : Circle → Schoenflies.Plane := fun z => e (z : ℂ)
  let c1 : Circle → Schoenflies.Plane := fun z => e (γ z)
  have hc0 : Continuous c0 := e.continuous.comp continuous_subtype_val
  have hi0 : Injective c0 := e.injective.comp Subtype.val_injective
  have hc1 : Continuous c1 := e.continuous.comp hγ
  have hi1 : Injective c1 := e.injective.comp hinj
  let e0 : Circle ≃ₜ range c0 := (hc0.isClosedEmbedding hi0).isEmbedding.toHomeomorph
  let e1 : Circle ≃ₜ range c1 := (hc1.isClosedEmbedding hi1).isEmbedding.toHomeomorph
  obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    (circle_embedding_range_isJordanCurve c0 hc0 hi0)
    (circle_embedding_range_isJordanCurve c1 hc1 hi1) (e0.symm.trans e1)
  refine ⟨e.trans (F.trans e.symm), ?_⟩
  intro z
  have hh : F (e (z : ℂ)) = e (γ z) := by
    simpa only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
      e0, e1, Topology.IsEmbedding.toHomeomorph_apply_coe, c0, c1] using hF (e0 z)
  change e.symm (F (e (z : ℂ))) = γ z
  rw [hh, e.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalJordanCapImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact Jordan hole lying in the domain of a conformal open embedding
has another actual Jordan hole as its image. -/
open Set Function
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_conformal_jordan_cap_image
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hi : InjOn f U) (hinf : ∞ ∈ U) (hfix : f ∞=∞)
    (H : ℂ ≃ₜ ℂ) (hHU : closedTerminalCap H ⊆ U) :
    ∃ K : ℂ ≃ₜ ℂ, f '' closedTerminalCap H = closedTerminalCap K := by
  obtain ⟨hd,ho,hij⟩ := hf.finite_open_embedding hU hi hinf hfix
  have hsub : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' U :=
    fun z hz => hHU ⟨z,hz,rfl⟩
  obtain ⟨K,_hKi,hKc,_hKf⟩ := exists_jordan_image_disk planarSchoenflies
    (hU.preimage OnePoint.continuous_coe) hd.continuousOn ho hij H hsub
  refine ⟨K,?_⟩
  rw [closedTerminalCap, ← finite_part_sphere_image
    (fun z hz => finite_image_of_fixes_infty hi hinf hfix (hsub hz)), hKc]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_JordanCircularizationStep
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One exact Koebe circularization step on a finite family of disjoint
Jordan holes. The selected hole becomes round, all other holes are the
actual conformal images, and the entire exterior is carried bijectively
onto the new exterior. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_jordan_circularization_step_full {I : Type*} [Finite I]
    (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) (j : I) :
    ∃ (K : I → ℂ ≃ₜ ℂ) (F : Sphere → Sphere) (c : ℂ) (r : ℝ),
      0 < r ∧ IsPrincipalNormalized F ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (K i))) ∧
      jordanInterior (K j)=ball c r ∧
      (∀ i, i≠j → F '' closedTerminalCap (H i)=closedTerminalCap (K i)) ∧
      IsConformalEquivalence F (closedTerminalCap (H j))ᶜ
        ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ) ∧
      IsConformalEquivalence F (openCompletedRegion H) (openCompletedRegion K) := by
  classical
  obtain ⟨F,c,r,hr,hnorm,hF⟩ := exists_principal_jordan_circle_map (H j)
  let D := ((↑) : ℂ → Sphere) '' closedBall c r
  have hS : IsOpen (closedTerminalCap (H j))ᶜ :=
    (isCompact_closedTerminalCap (H j)).isClosed.isOpen_compl
  have hinf : ∞ ∈ (closedTerminalCap (H j))ᶜ := by
    rintro ⟨z,_hz,he⟩
    exact OnePoint.coe_ne_infty z he
  have hold := disjoint_closedTerminalCaps H hdisj
  have hinside (i : I) (hi : i≠j) :
      closedTerminalCap (H i) ⊆ (closedTerminalCap (H j))ᶜ := by
    intro p hp hpj
    exact Set.disjoint_left.mp (hold hi) hp hpj
  have himages (i : I) (hi : i≠j) :
      ∃ K : ℂ ≃ₜ ℂ, F '' closedTerminalCap (H i)=closedTerminalCap K :=
    exists_conformal_jordan_cap_image hF.1 hS hF.bijOn.injOn hinf hnorm.1 (H i)
      (hinside i hi)
  let J := roundJordanAt c r hr
  let K : I → ℂ ≃ₜ ℂ := fun i => if hi : i=j then J else (himages i hi).choose
  have hKj : K j=J := by simp [K]
  have hselected : closedTerminalCap (K j)=D := by
    rw [hKj]
    exact congrArg (fun S : Set ℂ => ((↑) : ℂ → Sphere) '' S)
      (roundJordanAt_closure c r hr)
  have hother (i : I) (hi : i≠j) :
      F '' closedTerminalCap (H i)=closedTerminalCap (K i) := by
    simpa only [K,dite_eq_right hi] using (himages i hi).choose_spec
  have hout (i : I) (hi : i≠j) : closedTerminalCap (K i) ⊆ Dᶜ := by
    rw [← hother i hi]
    rintro _ ⟨p,hp,rfl⟩
    exact hF.bijOn.mapsTo (hinside i hi hp)
  have hnew : Pairwise (Disjoint on fun i => closedTerminalCap (K i)) := by
    intro i k hik
    change Disjoint (closedTerminalCap (K i)) (closedTerminalCap (K k))
    by_cases hij : i=j
    · subst i
      rw [hselected]
      exact Set.disjoint_left.mpr (fun p hp hk => hout k hik.symm hk hp)
    by_cases hkj : k=j
    · subst k
      rw [hselected]
      exact Set.disjoint_left.mpr (fun p hp hk => hout i hij hp hk)
    apply Set.disjoint_left.mpr
    intro p hp hk
    rw [← hother i hij] at hp
    rw [← hother k hkj] at hk
    obtain ⟨x,hx,rfl⟩ := hp
    obtain ⟨y,hy,he⟩ := hk
    have hyx : y=x := hF.bijOn.injOn (hinside k hkj hy) (hinside i hij hx) he
    exact Set.disjoint_left.mp (hold hik) hx (hyx ▸ hy)
  have hnewplane : Pairwise (Disjoint on fun i => closure (jordanInterior (K i))) := by
    intro i k hik
    exact Set.disjoint_left.mpr (fun z hz hk =>
      Set.disjoint_left.mp (hnew hik) ⟨z,hz,rfl⟩ ⟨z,hk,rfl⟩)
  have hsource : openCompletedRegion H ⊆ (closedTerminalCap (H j))ᶜ := by
    intro p hp hpj
    exact hp (mem_iUnion.mpr ⟨j,hpj⟩)
  have himage : F '' openCompletedRegion H=openCompletedRegion K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩ hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      by_cases hij : i=j
      · subst i
        rw [hselected] at hi
        exact hF.bijOn.mapsTo (hsource hx) hi
      · rw [← hother i hij] at hi
        obtain ⟨z,hz,he⟩ := hi
        have hzx : z=x := hF.bijOn.injOn (hinside i hij hz) (hsource hx) he
        exact hx (mem_iUnion.mpr ⟨i,hzx ▸ hz⟩)
    · intro y hy
      have hyout : y ∈ Dᶜ := by
        intro hyd
        exact hy (mem_iUnion.mpr ⟨j,hselected.symm ▸ hyd⟩)
      obtain ⟨x,hxS,hxy⟩ := hF.bijOn.surjOn hyout
      refine ⟨x,?_,hxy⟩
      intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      by_cases hij : i=j
      · exact hxS (hij ▸ hi)
      · apply hy
        apply mem_iUnion.mpr
        refine ⟨i,?_⟩
        rw [← hother i hij, ← hxy]
        exact mem_image_of_mem F hi
  refine ⟨K,F,c,r,hr,hnorm,hnewplane,?_,hother,hF,?_⟩
  · rw [hKj]
    exact roundJordanAt_interior c r hr
  · rw [← himage]
    exact isConformalEquivalence_of_injOn (fun p hp => hF.1 p (hsource hp))
      (isOpen_openCompletedRegion H) (hF.bijOn.injOn.mono hsource)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_JordanCircularizationSequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sequence of finite Jordan configurations and normalized
conformal maps obtained by successive one-hole circularizations. -/
open Set Function Metric Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace FiniteJordanConfiguration
variable {I : Type*} [Finite I]

lemma step_nonempty (C : FiniteJordanConfiguration I) (j : I) : Nonempty (Step C j) := by
  obtain ⟨K,F,c,r,hr,hp,hd,hsel,ho,hext,hconf⟩ :=
    exists_jordan_circularization_step_full C.hole C.disjoint j
  exact ⟨⟨⟨K,hd⟩,F,c,r,hr,hp,hsel,ho,hconf,hext⟩⟩

def chosenStep (C : FiniteJordanConfiguration I) (j : I) : Step C j :=
  Classical.choice (step_nonempty C j)

def iterate (C : FiniteJordanConfiguration I) (schedule : ℕ → I) : ℕ → FiniteJordanConfiguration I
  | 0 => C
  | n+1 => (chosenStep (iterate C schedule n) (schedule n)).target

def stageMap (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) : Sphere → Sphere :=
  (chosenStep (iterate C schedule n) (schedule n)).map

def cumulativeMap (C : FiniteJordanConfiguration I) (schedule : ℕ → I) : ℕ → Sphere → Sphere
  | 0 => id
  | n+1 => stageMap C schedule n ∘ cumulativeMap C schedule n

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
end


