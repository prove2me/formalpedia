-- Prove2me | Definitions.Def_Q146C001
-- name    : Q146C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:03:39.981981+00:00
-- url     : https://prove2.me/theorems/60584d16-ec9d-4115-b099-1ceebbec2e0d
-- title:
--   Definitions bundle Q146C001 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 375 declarations of OpenAI's Lean: 122 definitions, 13 inductive types or structures, 2 instances and 238 theorems. The definitions and types are `Graph.IsIncWalk`, `OAI.Bernstein.Sard.nonflatCriticalStratum`, `OAI.Bernstein.Sard.sixFlatSet`, `OAI.CircleDomainRigidity.AllowedTaggedPath`, `OAI.CircleDomainRigidity.AnalyticReflectionData`, `OAI.CircleDomainRigidity.AnalyticReflectionData.poleNormalized`, `OAI.CircleDomainRigidity.AnalyticReflectionData.poleParameter`, `OAI.CircleDomainRigidity.AnalyticReflectionData.principal`, `OAI.CircleDomainRigidity.AnalyticReflectionData.reflectedApproximation`, `OAI.CircleDomainRigidity.AnalyticReflectionData.reflectedLimit`, `OAI.CircleDomainRigidity.AnalyticReflectionData.reflectedSphere`, `OAI.CircleDomainRigidity.AnalyticReflectionData.reflectionDefect`, `OAI.CircleDomainRigidity.AnalyticReflectionData.straighteningApproximation`, `OAI.CircleDomainRigidity.AppendingConstructionState`, `OAI.CircleDomainRigidity.AppendingPairData`, `OAI.CircleDomainRigidity.CompactRegularLevelFlow`, `OAI.CircleDomainRigidity.CompactRegularLevelFlow.levelTrajectory`, `OAI.CircleDomainRigidity.CompactScalarModel`, `OAI.CircleDomainRigidity.CompactScalarModel.postcompose`, `OAI.CircleDomainRigidity.CompactScalarModel.postcomposeWithScalarTransport`, `OAI.CircleDomainRigidity.EuclideanPlane`, `OAI.CircleDomainRigidity.FiniteCompactTests`, `OAI.CircleDomainRigidity.FiniteJordanConfiguration`, `OAI.CircleDomainRigidity.FiniteJordanConfiguration.region`, `OAI.CircleDomainRigidity.FiniteTransfer.closedTerminalCap`, `OAI.CircleDomainRigidity.FiniteTransfer.cutoffCore`, `OAI.CircleDomainRigidity.FiniteTransfer.openCompletedRegion`, `OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain`, `OAI.CircleDomainRigidity.FiniteTransfer.sphericalCore`, `OAI.CircleDomainRigidity.FiniteTransfer.sphericalDiskUnion`, `OAI.CircleDomainRigidity.HasPrincipalCoefficient`, `OAI.CircleDomainRigidity.IsPlanarRegularValue`, `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.PlaneLocalWeakComplex`, `OAI.CircleDomainRigidity.PlaneLocalWeakComplex.HasBoundedDistortion`, `OAI.CircleDomainRigidity.PlaneQuasiconformalCalculus`, `OAI.CircleDomainRigidity.PrincipalMapLimit`, `OAI.CircleDomainRigidity.PrincipalSmoothApproximation` and 95 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `ArcCollars`, `ArcComplementPrep`, `Cannon_Conformal_Sphere`, `CircleDomains_Modulus_MobiusNormalization`, `CircleDomains_Modulus_PathLengthKernel`, `CircleDomains_Modulus_PathVariation`, `CircleDomains_Modulus_PhysicalDyadicLength`, `CircleDomains_Modulus_ResidualIncidence`, `CircleDomains_Modulus_TranslatedPhysicalBarrier`, `CircleDomains_Probability_HorizontalNullPair`, `CircleDomains_Probability_PathHitLaws`, `CircleDomains_Probability_PathLengthMeasure`, `CircleDomains_Reflection_AnalyticReflectionData`, `CircleDomains_Reflection_AnalyticStraighteningResidual`, `CircleDomains_Reflection_PrincipalReflectionDefect`, `CircleDomains_Reflection_ReflectedApproximationLimit`, `CircleDomains_Reflection_ReflectedSphereNormalization`, `CircleDomains_Reflection_RoundDiskReflection`, `CircleDomains_Reflection_RoundReflectionCoefficient`, `CircleDomains_Reflection_RoundReflectionDifferential`, `CircleDomains_Rigidity_PrincipalRealBeltrami`, `CircleDomains_Selection_AppendedScalarPairs`, `CircleDomains_Selection_AppendingPairData`, `CircleDomains_Selection_DyadicTimes`, `CircleDomains_Selection_OuterContours`, `CircleDomains_Selection_PhysicalSubpaths`, `CircleDomains_Selection_PointDustContourSelection`, `CircleDomains_Selection_RecursiveTestConstruction`, `CircleDomains_Selection_RegularLevelFlow`, `CircleDomains_Selection_ResidualConstraints`, `CircleDomains_Selection_ResidualVisits`, `CircleDomains_Selection_TagCodeSpace`, `CircleDomains_Selection_TagContainment`, `CircleDomains_Selection_TagDelay`, `CircleDomains_Selection_TagValidity`, `CircleDomains_Sobolev_AppendingEnergyTolerance`, `CircleDomains_Sobolev_BarrierDifferentialError`, `CircleDomains_Sobolev_BarrierEnergyAssembly`, `CircleDomains_Sobolev_BarrierL2Error`, `CircleDomains_Sobolev_CompactMollifierSampling`, `CircleDomains_Sobolev_CompactSobolevCutoff`, `CircleDomains_Sobolev_ComplexSobolevTransport`, `CircleDomains_Sobolev_L2ProductConvergence`, `CircleDomains_Sobolev_L2ThreeTermBound`, `CircleDomains_Sobolev_LocalPairChainRule`, `CircleDomains_Sobolev_LocalPairChainWitness`, `CircleDomains_Sobolev_LocalSobolevSmoothing`, `CircleDomains_Sobolev_LocalWeakBarrierBound`, `CircleDomains_Sobolev_MollificationEnergy`, `CircleDomains_Sobolev_PhysicalRoundIntegrals`, `CircleDomains_Sobolev_PositiveSobolevApproximation`, `CircleDomains_Sobolev_PrincipalSmoothApproximation`, `CircleDomains_Sobolev_PrincipalSmoothLimit`, `CircleDomains_Sobolev_PrincipalWeakDirections`, `CircleDomains_Sobolev_QuasiconformalSobolev`, `CircleDomains_Sobolev_SavedBarrierEnergy`, `CircleDomains_Sobolev_SavedBarrierEnergySlack`, `CircleDomains_Sobolev_SmoothContours`, `CircleDomains_Sobolev_SmoothJordanNeighborhoods`, `CircleDomains_Sobolev_SobolevConformalTransport`, `CircleDomains_Sobolev_SobolevRepresentative`, `CircleDomains_Sobolev_UniformLocalMollification`, `CircleDomains_Sobolev_VerticalWeakConstant`, `CircleDomains_Sobolev_WeakBarrierEstimate`, `CircleDomains_Sobolev_WeakBarrierMeasurability`, `CircleDomains_Sobolev_WeakCovectorGradient`, `CircleDomains_Sobolev_WeakPairDifferential`, `CircleDomains_Sobolev_WeakPairL2`, `CircleDomains_Topology_BasePathCodes`, `CircleDomains_Topology_CenteredJordanCoordinate`, `CircleDomains_Topology_ClippedPaths`, `CircleDomains_Topology_CompactClopenRefinement`, `CircleDomains_Topology_CompactPairChainRule`, `CircleDomains_Topology_CompactScalarModel`, `CircleDomains_Topology_CutoffCore`, `CircleDomains_Topology_DiskCentering`, `CircleDomains_Topology_EuclideanPlaneCoordinates`, `CircleDomains_Topology_FiniteCompactTests`, `CircleDomains_Topology_JordanContours`, `CircleDomains_Topology_LimitSphereExtension`, `CircleDomains_Topology_PathTags`, `CircleDomains_Topology_PhysicalPlaneCoordinates`, `CircleDomains_Topology_PlanarPairCalculus`, `CircleDomains_Topology_PlaneHomeomorphFromSphere`, `CircleDomains_Topology_PlaneQuotientRepresentative`, `CircleDomains_Topology_RegularLevelOpenOrbit`, `CircleDomains_Topology_SphereCoefficient`, `CircleDomains_Topology_SphereJordanCoordinates`, `CircleDomains_Topology_SphereLevels`, `CircleDomains_Topology_SpherePlaneContinuity`, `CircleDomains_Transfer_CompletedChart`, `CircleDomains_Transfer_CoreGeometry`, `CircleDomains_Transfer_ResidualImage`, `CircleDomains_Transfer_ScalarModelPostcomposition`, `CircleDomains_Uniformization_Conformal`, `CircleDomains_Uniformization_ConformalComposition`, `CircleDomains_Uniformization_FiniteCompletion`, `CircleDomains_Uniformization_FiniteCompletionUniformization`, `CircleDomains_Uniformization_JordanCircularizationSequence`, `CircleDomains_Uniformization_MobiusConformal`, `CircleDomains_Uniformization_PrincipalCoefficientLimit`, `CombinatorialInvariance`, `Curve`, `GeneratedStructure`, `Graph_RelativeEar`, `Graph_TwoConnected`, `Jordan`, `KLS_Sobolev_SobolevApproximation`, `KLS_Sobolev_WeakDerivatives`, `KLS_Sobolev_Witnesses`, `PolyArcRealize`, `Realization`, `RealizeSubdiv`, `SquareCycle`, `StableBernstein_Estimates_PuncturedSard`, `Subarc`, `TwoArcs`.
--
--   **Imports.** It imports the published bundle `Def_KoebeCircleDomains`; the bundle `OAIQ046C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q146C003`, `Q146C004` and `Q146C005`; the statements `OAI.CircleDomainRigidity.PrincipalSmoothApproximation.exists_principal_limit_data`, `OAI.CircleDomainRigidity.exists_principal_smooth_approximation` and `OAI.CircleDomainRigidity.exists_round_invariant_principal_approximation_with_coefficient`; the proofs of `OAI.CircleDomainRigidity.PrincipalSmoothApproximation.exists_principal_limit_data` and `OAI.CircleDomainRigidity.exists_principal_smooth_approximation`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_OAIQ046C002

section
-- module Solutions.Q146_CD.Compat
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
/-- Mathlib d13f23b's `LipschitzOnWith.comp_absolutelyContinuousOnInterval`: a Lipschitz function of an
absolutely continuous one is absolutely continuous (Boltzmann EntropyIntegralBalance and JetSupersolutions,
oaiq-080). -/
theorem _root_.LipschitzOnWith.comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {s : Set ℝ} {K : NNReal}
    {a b : ℝ} (hg : LipschitzOnWith K g s) (hmaps : ∀ t ∈ Set.uIcc a b, f t ∈ s)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  have h0 := hf
  unfold AbsolutelyContinuousOnInterval at h0 ⊢
  have h1 := h0.const_mul (K : ℝ)
  rw [mul_zero] at h1
  refine squeeze_zero' ?_ ?_ h1
  · exact Filter.Eventually.of_forall (fun E => Finset.sum_nonneg (fun i _ => dist_nonneg))
  · refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall (fun E hE => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' := hE.left i hi
    have := hg (hmaps _ hi'.left) (hmaps _ hi'.right)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) this
    rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist, ENNReal.coe_toReal] at h2
/-- The `LipschitzWith` form of the previous lemma (JetSupersolutions, oaiq-080). -/
theorem _root_.LipschitzWith.comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {K : NNReal}
    {a b : ℝ} (hg : LipschitzWith K g) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b :=
  (hg.lipschitzOnWith (s := Set.univ)).comp_absolutelyContinuousOnInterval (fun _ _ => Set.mem_univ _) hf
end OAICompat434

end OAI
end

section
-- module Solutions.Q146_CD.Curve
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-! ### The unit interval, as a subset of `ℝ` -/

theorem isConnected_I : IsConnected I := isConnected_Icc zero_le_one

/-! ### Elementary properties -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Subarc
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- A subinterval of the unit interval stays inside it: `uIcc` is the convex hull of its two
endpoints, and the unit interval is convex. -/
theorem uIcc_subset_I (ha : a ∈ I) (hb : b ∈ I) : uIcc a b ⊆ I :=
  uIcc_subset_Icc ha hb

/-! ### Subarcs -/

/-! ### The arc without its endpoints -/

/-! ### The interior of an arc, set-level

`openArc` is stated for a parametrisation. Three separate modules needed the same facts stated
for the *set* — `IsArcBetween A p q` gives `A ∖ {p, q}` connected, nonempty, and having both
endpoints in its closure — and each proved them again from scratch, one of them twice under two
names. Two of those copies were literally the same statement in modules that do not import each
other, so the build never noticed: alpha-equivalent `Prop`s are defeq under proof irrelevance,
and Lean's import checker accepts them. They live here now. -/

/-! ### A parametrisation is an open map onto its arc -/

/-! ### The subarc basis -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.ArcCollars
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-! ### The turned vector of a reversed direction -/

/-! ## The constants

`ArcStrip` is the arc analogue of `Schoenflies.StripData`: the blueprint's "choose the blocks so
that consecutive ones overlap and nonadjacent closures are disjoint", with every constant named.
Three fields have no counterpart in the closed case, and they are what makes the collar a collar
*of `K` inside `D`*: `ball_subset` and `tube_subset` put every piece inside the prescribed open
set, and `sep_ends` keeps `K` clear of the two ends of the arc, where the collar has no pieces.

`sep_ends` is not a restriction in the intended application: the two endpoints of a crosscut lie
outside `D` and `K` lies inside, so the distance from `K` to either endpoint is positive and `R`
is chosen below it. -/

/-! ### Two shapes of bounded union

Both tracks and the collar are unions over an initial segment of `ℕ`. These two rewrites are the
only interface to that indexing. -/

theorem mem_iUnion_le_nat {α : Type*} {F : ℕ → Set α} {m : ℕ} {x : α} :
    x ∈ (⋃ i, ⋃ (_ : i ≤ m), F i) ↔ ∃ i ≤ m, x ∈ F i := by
  simp only [Set.mem_iUnion, exists_prop]

theorem mem_iUnion_lt_nat {α : Type*} {F : ℕ → Set α} {m : ℕ} {x : α} :
    x ∈ (⋃ i, ⋃ (_ : i < m), F i) ↔ ∃ i < m, x ∈ F i := by
  simp only [Set.mem_iUnion, exists_prop]

/-! ## Chaining a linear family

The union of the left pieces is connected because consecutive pieces overlap. Unlike the cyclic
case there is no closing overlap to discard: the chain `0, 1, …, N` is exactly the spanning tree
of the overlap graph. -/

/-- A family of connected sets indexed by an initial segment of `ℕ`, in which every member meets
its successor, has connected union. -/
theorem isConnected_iUnion_chain {α : Type*} [TopologicalSpace α] {F : ℕ → Set α} :
    ∀ N : ℕ, (∀ k ≤ N, IsConnected (F k)) → (∀ k < N, (F k ∩ F (k + 1)).Nonempty) →
      IsConnected (⋃ k, ⋃ (_ : k ≤ N), F k) := by
  intro N
  induction N with
  | zero =>
      intro hconn _
      have h : (⋃ k, ⋃ (_ : k ≤ 0), F k) = F 0 := by
        ext y
        rw [mem_iUnion_le_nat]
        exact ⟨fun ⟨k, hk, hy⟩ => by rwa [Nat.le_zero.1 hk] at hy, fun hy => ⟨0, le_refl 0, hy⟩⟩
      rw [h]
      exact hconn 0 (le_refl 0)
  | succ N ih =>
      intro hconn hmeet
      have h : (⋃ k, ⋃ (_ : k ≤ N + 1), F k) = (⋃ k, ⋃ (_ : k ≤ N), F k) ∪ F (N + 1) := by
        ext y
        simp only [mem_iUnion_le_nat, Set.mem_union]
        constructor
        · rintro ⟨k, hk, hy⟩
          rcases Nat.lt_or_ge k (N + 1) with hlt | hge
          · exact Or.inl ⟨k, by omega, hy⟩
          · exact Or.inr (by rwa [show k = N + 1 by omega] at hy)
        · rintro (⟨k, hk, hy⟩ | hy)
          · exact ⟨k, by omega, hy⟩
          · exact ⟨N + 1, le_refl _, hy⟩
      rw [h]
      obtain ⟨z, hz1, hz2⟩ := hmeet N (by omega)
      exact IsConnected.union ⟨z, mem_iUnion_le_nat.2 ⟨N, le_refl N, hz1⟩, hz2⟩
        (ih (fun k hk => hconn k (by omega)) fun k hk => hmeet k (by omega))
        (hconn (N + 1) (le_refl _))

/-- One positive offset below an accuracy, below a geometric bound, and small enough against a
germ threshold. This is the arc's replacement for the `exists_common_bound` of
`Schoenflies/StripLocal.lean`, which is private there. -/
theorem exists_offset_bound {ε b X k : ℝ} (hε : 0 < ε) (hb : 0 < b) (hX : 0 < X) (hk : 0 < k) :
    ∃ σ : ℝ, 0 < σ ∧ σ < ε ∧ σ < b ∧ σ * k < X := by
  refine ⟨min (min (ε / 2) (b / 2)) (X / (2 * k)),
    lt_min (lt_min (by linarith) (by linarith)) (by positivity), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  · have h : min (min (ε / 2) (b / 2)) (X / (2 * k)) ≤ X / (2 * k) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h hk.le
    have h3 : X / (2 * k) * k = X / 2 := by field_simp
    rw [h3] at h2
    linarith

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
-- module Solutions.Q146_CD.ArcComplementPrep
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

variable {r : ℝ}

/-- A real number is within `r` of `a` exactly when it lies on the segment from `a - r` to
`a + r`, in either order. Stated through `uIcc` so that the two orders are one lemma. -/
theorem mem_segment_abs {a r x : ℝ} (hr : 0 ≤ r) :
    x ∈ segment ℝ (a - r) (a + r) ↔ |x - a| ≤ r := by
  rw [segment_eq_Icc (by linarith), mem_Icc, abs_le]
  constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem mem_segment_abs' {a r x : ℝ} (hr : 0 ≤ r) :
    x ∈ segment ℝ (a + r) (a - r) ↔ |x - a| ≤ r := by
  rw [segment_symm]; exact mem_segment_abs hr

end Plane

open Plane

/-! ### The square as a `ClosedPolygon`

Four corners in counterclockwise order. `edges_meet` splits into the four adjacent pairs,
where `segment_inter_shared` applies because consecutive sides are perpendicular, and the two
opposite pairs, which are disjoint because opposite sides are pinned to different values of
one coordinate. -/

variable {r : ℝ}

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

/-- Membership in a real segment from two inequalities, in whichever order the ends come. -/
theorem mem_segment_of_bounds {u v y : ℝ} (h : u ≤ y ∧ y ≤ v ∨ v ≤ y ∧ y ≤ u) :
    y ∈ segment ℝ u v := by
  rw [segment_eq_uIcc, Set.mem_uIcc]
  exact h

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

/-- The `i`-th point of the even partition of `[0,1]` into `n` pieces. -/
noncomputable def sample (n i : ℕ) : ℝ := (i : ℝ) / n

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
-- module Solutions.Q146_CD.Cannon_Conformal_Sphere
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonSphereReflection
open Set Metric Topology
open scoped OnePoint

lemma reflection_infty : reflection ∞=((0:ℂ):S) := by
  change CannonMobius.inv ∞=_
  exact CannonMobius.inv_infty
lemma reflection_zero : reflection ((0:ℂ):S)=∞ := by
  change CannonMobius.inv ((starRingEnd ℂ 0:ℂ):S)=_
  simpa only [map_zero] using CannonMobius.inv_zero
lemma reflection_coe {z : ℂ} (hz : z≠0) :
    reflection (z:S)=((starRingEnd ℂ z)⁻¹:ℂ) := by
  change CannonMobius.inv ((starRingEnd ℂ z:ℂ):S)=_
  exact CannonMobius.inv_coe ((map_ne_zero (starRingEnd ℂ)).mpr hz)

lemma reflection_involutive : Function.Involutive reflection := by
  intro p
  induction p using OnePoint.rec with
  | infty => rw [reflection_infty,reflection_zero]
  | coe z =>
    by_cases hz : z=0
    · subst z; rw [reflection_zero,reflection_infty]
    · rw [reflection_coe hz,reflection_coe (inv_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hz))]
      simp

end CannonSphereReflection

end
end
end
end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_Conformal
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sphere conformality and circle-domain statements

The concrete Riemann-sphere charts define conformal equivalences,
round disks, and conformal removability. The two circle-domain statements
express unrestricted uniformization and rigidity under removability.
-/

noncomputable section

open Set
open scoped OnePoint

namespace CircleDomainRigidity

/-- Sphere inversion exchanges zero and infinity and is its own inverse. -/
theorem sphereInv_involutive : Function.Involutive sphereInv := by
  intro p
  cases p using OnePoint.rec with
  | infty => simp [sphereInv]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [sphereInv]
    · simp [sphereInv, hz, inv_ne_zero hz]

@[simp] theorem sphereInv_sphereInv (p : Sphere) : sphereInv (sphereInv p) = p :=
  sphereInv_involutive p

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalComposition
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Composition in the concrete sphere charts

The finite and infinite charts are locally inverse at their centers.
The ordinary complex chain rule therefore proves composition of the
actual conformal-equivalence predicate used by the main statements.
-/

open Set Filter Classical
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

def chartTransform (p : Sphere) : Sphere ≃ₜ Sphere :=
  if p = ∞ then CannonMobius.inversion else Homeomorph.refl _

theorem chartTransform_involutive (p : Sphere) : Function.Involutive (chartTransform p) := by
  by_cases hp : p = ∞
  · rw [chartTransform, ite_eq_left hp]
    change Function.Involutive CannonMobius.inv
    exact CannonMobius.inv_involutive
  · simp only [chartTransform, ite_eq_right hp, Homeomorph.refl_apply]
    exact fun _ => rfl

theorem chart_eq_coordinate_transform (p q : Sphere) :
    chart p q = CannonMobius.coordinate (chartTransform p q) := by
  unfold chart chartTransform
  split_ifs <;> rfl

theorem chartSymm_eq_transform (p : Sphere) (z : ℂ) :
    chartSymm p z = chartTransform p (z : Sphere) := by
  unfold chartSymm chartTransform
  split_ifs <;> rfl

theorem chartTransform_center_ne_infty (p : Sphere) : chartTransform p p ≠ ∞ := by
  by_cases hp : p = ∞
  · subst p
    rw [chartTransform, ite_eq_left rfl]
    change CannonMobius.inv ∞ ≠ ∞
    exact OnePoint.coe_ne_infty 0
  · rw [chartTransform, ite_eq_right hp]
    exact hp

theorem chartSymm_chart_of_ne (p q : Sphere) (hq : chartTransform p q ≠ ∞) :
    chartSymm p (chart p q) = q := by
  rw [chartSymm_eq_transform, chart_eq_coordinate_transform, CannonMobius.coe_coordinate hq]
  exact chartTransform_involutive p q

theorem chartSymm_chart_self (p : Sphere) : chartSymm p (chart p p) = p :=
  chartSymm_chart_of_ne p p (chartTransform_center_ne_infty p)

theorem continuous_chartSymm (p : Sphere) : Continuous (chartSymm p) := by
  have heq : chartSymm p = fun z : ℂ => chartTransform p (z : Sphere) :=
    funext (chartSymm_eq_transform p)
  rw [heq]
  exact (chartTransform p).continuous.comp OnePoint.continuous_coe

theorem eventually_chartSymm_chart (p : Sphere) :
    ∀ᶠ q in 𝓝 p, chartSymm p (chart p q) = q := by
  have hn : ∀ᶠ q in 𝓝 p, chartTransform p q ≠ ∞ :=
    ((chartTransform p).continuous.continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds (chartTransform_center_ne_infty p))
  exact hn.mono (fun q hq => chartSymm_chart_of_ne p q hq)

theorem IsConformalAt.comp {f g : Sphere → Sphere} {p : Sphere}
    (hg : IsConformalAt g (f p)) (hf : IsConformalAt f p) : IsConformalAt (g ∘ f) p := by
  obtain ⟨hfc, df, hdf, hfder⟩ := hf
  obtain ⟨hgc, dg, hdg, hgder⟩ := hg
  refine ⟨hgc.comp hfc, dg * df, mul_ne_zero hdg hdf, ?_⟩
  have hx : chart (f p) (f (chartSymm p (chart p p))) = chart (f p) (f p) := by
    rw [chartSymm_chart_self]
  have hgder' : HasDerivAt
      (fun z => chart (g (f p)) (g (chartSymm (f p) z))) dg
      (chart (f p) (f (chartSymm p (chart p p)))) := hx.symm ▸ hgder
  have hd := hgder'.comp (chart p p) hfder
  have hcont : Tendsto (fun z => f (chartSymm p z)) (𝓝 (chart p p)) (𝓝 (f p)) := by
    have hfc' : ContinuousAt f (chartSymm p (chart p p)) := by
      rw [chartSymm_chart_self]
      exact hfc
    have hc := hfc'.comp (continuous_chartSymm p).continuousAt
    simpa only [Function.comp_def, chartSymm_chart_self] using hc.tendsto
  have he := hcont.eventually (eventually_chartSymm_chart (f p))
  apply hd.congr_of_eventuallyEq
  filter_upwards [he] with z hz
  change chart (g (f p)) (g (f (chartSymm p z))) =
    chart (g (f p)) (g (chartSymm (f p) (chart (f p) (f (chartSymm p z)))))
  rw [hz]

theorem IsConformalOn.comp {f g : Sphere → Sphere} {U V : Set Sphere}
    (hg : IsConformalOn g V) (hf : IsConformalOn f U) (hUV : MapsTo f U V) :
    IsConformalOn (g ∘ f) U :=
  fun p hp => (hg (f p) (hUV hp)).comp (hf p hp)

theorem IsConformalEquivalence.trans
    {f g : Sphere → Sphere} {U V W : Set Sphere}
    (hf : IsConformalEquivalence f U V) (hg : IsConformalEquivalence g V W) :
    IsConformalEquivalence (g ∘ f) U W := by
  obtain ⟨hfc, hfUV, fi, hfic, hfiVU, hfleft, hfright⟩ := hf
  obtain ⟨hgc, hgVW, gi, hgic, hgiWV, hgleft, hgright⟩ := hg
  refine ⟨hgc.comp hfc hfUV, hgVW.comp hfUV, fi ∘ gi,
    hfic.comp hgic hgiWV, hfiVU.comp hgiWV, ?_, ?_⟩
  · intro z hz
    simp only [Function.comp_apply, hgleft (f z) (hfUV hz), hfleft z hz]
  · intro w hw
    simp only [Function.comp_apply, hfright (gi w) (hgiWV hw), hgright w hw]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MobiusNormalization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete Möbius normalizations

Affine changes and inversion are homeomorphisms of the concrete sphere.
Their matrix actions agree with the projective-line action used in the
definition of round disks.
-/

open Set Filter Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

def affineHomeomorph (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a * z + b
  invFun z := (z - b) / a
  left_inv z := by dsimp; field_simp <;> ring
  right_inv z := by dsimp; field_simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def affineSphere (a b : ℂ) (ha : a ≠ 0) : Sphere ≃ₜ Sphere :=
  (affineHomeomorph a b ha).onePointCongr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereLevels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying finite-length level topology to the actual sphere quotient

Choose a compatible metric on `OnePoint ℂ` by its standard homeomorphism
with the unit sphere in three-dimensional Euclidean space. This keeps the
original topology definitionally unchanged. The quotient obtained from
Moore's published decomposition input then satisfies the already proved
finite-physical-length level theorem. No metric or level regularity of
the quotient is left as an additional premise.
-/

open Set Metric MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

noncomputable def roundSphereEquiv :
    Sphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)

/-- A fixed compatible sphere metric, pulled back from the Euclidean
unit sphere. Its topology is the original one-point topology. -/
noncomputable abbrev sphereMetric : MetricSpace Sphere :=
  roundSphereEquiv.isEmbedding.comapMetricSpace roundSphereEquiv

attribute [local instance] sphereMetric

noncomputable abbrev sphereBorel : MeasurableSpace Sphere := borel Sphere

attribute [local instance] sphereBorel

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathHitLaws
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed path-hit relations and the joint upper semicontinuity of their probabilities.
The time interval is compact, so projection of the closed incidence relation is closed.
Weak convergence and the existing Portmanteau theorem then apply to the product with
the moving point mass. This supplies the actual hit function used in law fusion. -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

abbrev PathTime := Icc (0 : ℝ) 1

section Paths

variable {X : Type*} [MetricSpace X]

def pathHitSet : Set (C(PathTime, X) × X) :=
  {p | ∃ t : PathTime, p.1 t = p.2}

end Paths

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathVariation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel length data for ordinary continuous metric paths. These are applied
to physical-domain subarcs when forming the path occupation kernel. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathVariation_lowerSemicontinuous (A : Set PathTime) :
    LowerSemicontinuous (fun γ : C(PathTime, X) => eVariationOn γ A) := by
  unfold eVariationOn
  apply lowerSemicontinuous_iSup
  intro p
  apply Continuous.lowerSemicontinuous
  apply continuous_finsetSum
  intro i _
  exact (continuous_eval_const _).edist (continuous_eval_const _)

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathVariation (A : Set PathTime) :
    Measurable (fun γ : C(PathTime, X) => eVariationOn γ A) :=
  (pathVariation_lowerSemicontinuous A).measurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathLengthMeasure
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arclength measure of an ordinary rectifiable continuous metric path.
It is atomless and assigns each interval its actual metric variation. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

abbrev RectifiablePath (X : Type*) [MetricSpace X] :=
  {γ : C(PathTime, X) // BoundedVariationOn γ univ}

def pathLengthFunction (γ : RectifiablePath X) : StieltjesFunction PathTime where
  toFun t := variationOnFromTo γ.val univ ⊥ t
  mono' := monotoneOn_univ.mp
    (variationOnFromTo.monotoneOn γ.property.locallyBoundedVariationOn (mem_univ _))
  right_continuous' _t := γ.property.continuousWithinAt_variationOnFromTo_Ici
    γ.val.continuous.continuousAt.continuousWithinAt

def pathLengthMeasure (γ : RectifiablePath X) : Measure PathTime :=
  (pathLengthFunction γ).measure

theorem continuous_pathLengthFunction (γ : RectifiablePath X) :
    Continuous (pathLengthFunction γ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : ContinuousAt γ.val t := γ.val.continuous.continuousAt
  have hR : ContinuousWithinAt (variationOnFromTo γ.val univ ⊥) (Ici t) t :=
    γ.property.continuousWithinAt_variationOnFromTo_Ici hc.continuousWithinAt
  have hL : ContinuousWithinAt (variationOnFromTo γ.val univ ⊥) (Iic t) t := by
    have H : Filter.Tendsto (fun y => eVariationOn γ.val (univ ∩ Icc y t)) (nhdsWithin t univ)
        (nhds 0) :=
      γ.property.tendsto_eVariationOn_Icc_zero_left (by simpa using hc.continuousWithinAt)
    have H2 : Filter.Tendsto (fun y => (eVariationOn γ.val (univ ∩ Icc y t)).toReal)
        (nhdsWithin t (Iic t)) (nhds 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (H.mono_left (nhdsWithin_mono t (subset_univ (Iic t))))
      simpa [Function.comp_def] using this
    have H3 := (tendsto_const_nhds (x := variationOnFromTo γ.val univ ⊥ t)).sub H2
    rw [sub_zero] at H3
    unfold ContinuousWithinAt
    apply H3.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [← variationOnFromTo.add γ.property.locallyBoundedVariationOn (mem_univ _) (mem_univ t)
      (mem_univ y), variationOnFromTo.eq_of_ge (a := t) (b := y) _ _ hy]
    ring
  exact continuousAt_iff_continuous_left_right.mpr ⟨hL, hR⟩

instance instIsFiniteMeasureElemRealPathTimePathLengthMeasure (γ : RectifiablePath X) : IsFiniteMeasure (pathLengthMeasure γ) :=
  (pathLengthFunction γ).isFiniteMeasure_of_forall_abs_le
    (fun _ => variationOnFromTo.abs_le_eVariationOn γ.property)

instance instNullSingletonClassElemRealPathTimePathLengthMeasure (γ : RectifiablePath X) : NullSingletonClass (pathLengthMeasure γ) := by
  constructor
  intro t
  rw [pathLengthMeasure, StieltjesFunction.measure_singleton]
  have ht : ContinuousWithinAt (pathLengthFunction γ) (Iic t) t :=
    (continuous_pathLengthFunction γ).continuousAt.continuousWithinAt
  rw [ht.leftLim_eq, sub_self, ENNReal.ofReal_zero]

theorem pathLengthMeasure_Ioc (γ : RectifiablePath X) {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure γ (Ioc a b) = eVariationOn γ.val (Icc a b) := by
  rw [pathLengthMeasure, StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (variationOnFromTo γ.val univ ⊥ b -
    variationOnFromTo γ.val univ ⊥ a) = _
  rw [variationOnFromTo.sub_right γ.property.locallyBoundedVariationOn
    (mem_univ _) (mem_univ _) (mem_univ _), variationOnFromTo.eq_of_le _ _ hab,
    univ_inter, ENNReal.ofReal_toReal]
  exact γ.property.mono (subset_univ _)

theorem pathLengthMeasure_Icc (γ : RectifiablePath X) {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure γ (Icc a b) = eVariationOn γ.val (Icc a b) := by
  rw [← measure_congr (Ioc_ae_eq_Icc (μ := pathLengthMeasure γ))]
  exact pathLengthMeasure_Ioc γ hab

theorem pathLengthMeasure_univ (γ : RectifiablePath X) :
    pathLengthMeasure γ univ = eVariationOn γ.val univ := by
  simpa only [Icc_bot_top] using pathLengthMeasure_Icc γ (bot_le : (⊥ : PathTime) ≤ ⊤)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathLengthKernel
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arclength measures form a Borel kernel on rectifiable paths. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathLengthMeasure :
    Measurable (pathLengthMeasure (X := X)) := by
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc PathTime))
    (isPiSystem_Ioc id id)
  · rintro s ⟨a, b, hab, rfl⟩
    have hm : Measurable (fun γ : RectifiablePath X => eVariationOn γ.val (Icc a b)) :=
      (measurable_pathVariation (X := X) (Icc a b)).comp measurable_subtype_coe
    simpa only [pathLengthMeasure_Ioc _ hab.le] using hm
  · have hm : Measurable (fun γ : RectifiablePath X => eVariationOn γ.val univ) :=
      (measurable_pathVariation (X := X) univ).comp measurable_subtype_coe
    simpa only [pathLengthMeasure_univ] using hm

def pathLengthKernel : ProbabilityTheory.Kernel (RectifiablePath X) PathTime where
  toFun := pathLengthMeasure
  measurable' := measurable_pathLengthMeasure

@[simp] theorem pathLengthKernel_apply (γ : RectifiablePath X) :
    pathLengthKernel γ = pathLengthMeasure γ := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathTags
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient tagged-path code space and its compact residual-time sections.
An active slot contains a nonempty finite label tuple, its circle levels,
and the two ends of its open time interval. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

abbrev TagParameters (n : ℕ) :=
  (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle) × PathTime × PathTime

abbrev TagData := Σ n : ℕ, TagParameters n

def TagSlot := Unit ⊕ TagData

def tagLeft : TagSlot → PathTime :=
  Sum.elim (fun _ => ⊤) (fun t => t.2.2.2.1)

def tagRight : TagSlot → PathTime :=
  Sum.elim (fun _ => ⊥) (fun t => t.2.2.2.2)

abbrev TaggedPath (X : Type*) [TopologicalSpace X] :=
  C(PathTime, X) × (ℕ → TagSlot)

def residualTimeGraph {X : Type*} [TopologicalSpace X] (B : Set X) :
    Set (TaggedPath X × PathTime) :=
  {q | q.1.1 q.2 ∈ B ∧ ∀ k,
    q.2 ≤ tagLeft (q.1.2 k) ∨ tagRight (q.1.2 k) ≤ q.2}

def residualTimes {X : Type*} [TopologicalSpace X] (B : Set X) (Γ : TaggedPath X) :
    Set PathTime := {t | (Γ, t) ∈ residualTimeGraph B}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualVisits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual residual visit multiplicities and tolls on closed test intervals. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def residualToll (B : Set X) (I : Set PathTime) (m : X → ℝ≥0∞) (Γ : TaggedPath X) : ℝ≥0∞ :=
  ∑' t : PathTime, if t ∈ residualTimes B Γ ∧ t ∈ I then m (Γ.1 t) else 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ResidualIncidence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel residual incidences after finite point deletions. Compact time
projection proves these directly, including the prior-path and level tests. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]

def residualIncidence (B : Set X) (I : Set PathTime) (R : Set (Y × X))
    (P : Set X) : Set (TaggedPath X × Y) :=
  {q | ∃ t ∈ residualTimes B q.1, t ∈ I ∧ (q.2, q.1.1 t) ∈ R ∧ q.1.1 t ∉ P}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ResidualImage
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact residual images and their Borel incidence masses. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def residualImage (B : Set X) (Γ : TaggedPath X) : Set X :=
  Γ.1 '' residualTimes B Γ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualConstraints
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational-interval residual constraints in the allowed path definition
are Borel. The incidence side uses the actual prior law or level measure;
the toll side retains parameter multiplicity after each finite deletion. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

abbrev RationalPathTime := {q : ℚ // q ∈ Icc (0 : ℚ) 1}

def RationalPathTime.toTime (q : RationalPathTime) : PathTime :=
  ⟨(q.val : ℝ), by
    constructor
    · exact_mod_cast q.property.1
    · exact_mod_cast q.property.2⟩

def deletedWeight {X : Type*} (P : Set X) (m : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  if x ∈ P then 0 else m x

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def ResidualIncidenceBound (B : Set X) (I : Set PathTime) (R : Set (Y × X))
    (P : Set X) (ν : Measure Y) (m : X → ℝ≥0∞) (Γ : TaggedPath X) : Prop :=
  ν {y | (Γ, y) ∈ residualIncidence B I R P} ≤
    residualToll B I (deletedWeight P m) Γ

def ResidualConstraintFamily (B : Set X) (R : ℕ → Set (Y × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Y) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) : Prop :=
  ∀ i n (a b : RationalPathTime),
    ResidualIncidenceBound B (Icc a.toTime b.toTime) (R i) (P i n) (ν i) (m i) Γ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagContainment
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed level-containment tests for the actual finite unions in tag slots. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def activeTagLevelGraph (H : ℕ → Set (UnitAddCircle × X)) : Set (TagData × X) :=
  {q | ∃ i : Fin (q.1.1 + 1), (q.1.2.2.1 i, q.2) ∈ H (q.1.2.1 i)}

def tagLevelGraph (H : ℕ → Set (UnitAddCircle × X)) : Set (TagSlot × X) :=
  {q | match q.1 with
    | Sum.inl _ => True
    | Sum.inr t => (t, q.2) ∈ activeTagLevelGraph H}

def tagContainment (H : ℕ → Set (UnitAddCircle × X)) : Set (C(PathTime, X) × TagSlot) :=
  {q | ∀ t : PathTime, tagLeft q.2 < t → t < tagRight q.2 → (q.2, q.1 t) ∈ tagLevelGraph H}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagValidity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel tests for nonconstant active tags and excluded level tuples. -/

open Set MeasureTheory Topology
open scoped Topology Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T2Space X]

def nonconstantTagSegment : Set (C(PathTime, X) × TagSlot) :=
  {q | ∃ s t : PathTime,
    tagLeft q.2 < s ∧ s < tagRight q.2 ∧
    tagLeft q.2 < t ∧ t < tagRight q.2 ∧ q.1 s ≠ q.1 t}

def validTagShape : Set (C(PathTime, X) × TagSlot) :=
  (Prod.snd ⁻¹' Set.range (Sum.inl : Unit → TagSlot)) ∪ nonconstantTagSegment

def insertTagTuple (n : ℕ) (l : Fin (n + 1) → ℕ)
    (p : (Fin (n + 1) → UnitAddCircle) × PathTime × PathTime) : TagSlot :=
  Sum.inr ⟨n, l, p⟩

def tagTupleExcluded (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)) :
    Set TagSlot :=
  ⋃ n, ⋃ l, insertTagTuple n l '' (N n l ×ˢ (univ : Set (PathTime × PathTime)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagCodeSpace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Borel ambient codes and Borel simultaneous tag rules. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def TagRules (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) : Prop :=
  ∀ k : ℕ, (Γ.1, Γ.2 k) ∈ validTagShape ∧
    (Γ.1, Γ.2 k) ∈ tagContainment H ∧ Γ.2 k ∉ tagTupleExcluded N

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClippedPaths
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant extension of a closed path portion. Its arclength is exactly
the variation of that portion; this is used to assemble local physical lifts. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def timeClip (a b : PathTime) : C(PathTime, PathTime) where
  toFun t := max a (min b t)
  continuous_toFun := continuous_const.max (continuous_const.min continuous_id)

theorem range_timeClip {a b : PathTime} (hab : a ≤ b) : Set.range (timeClip a b) = Icc a b := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  · intro ht
    exact ⟨t, by simp [timeClip, min_eq_right ht.2, max_eq_right ht.1]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DyadicTimes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed dyadic time partitions used to assemble physical-domain length. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def dyadicReal (n i : ℕ) : ℝ := (i : ℝ) / (2 : ℝ) ^ n

theorem dyadicReal_nonneg (n i : ℕ) : 0 ≤ dyadicReal n i := by
  unfold dyadicReal
  positivity

theorem dyadicReal_le_one {n i : ℕ} (hi : i ≤ 2 ^ n) : dyadicReal n i ≤ 1 := by
  rw [dyadicReal, div_le_one (by positivity)]
  exact_mod_cast hi

theorem dyadicReal_mono (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    dyadicReal n i ≤ dyadicReal n j := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

def dyadicTime (n : ℕ) (i : Fin (2 ^ n + 1)) : PathTime :=
  ⟨dyadicReal n i.val, dyadicReal_nonneg n i.val, dyadicReal_le_one (by omega)⟩

def dyadicLeft (n : ℕ) (i : Fin (2 ^ n)) : PathTime := dyadicTime n i.castSucc

def dyadicRight (n : ℕ) (i : Fin (2 ^ n)) : PathTime := dyadicTime n i.succ

theorem dyadicLeft_le_right (n : ℕ) (i : Fin (2 ^ n)) : dyadicLeft n i ≤ dyadicRight n i :=
  dyadicReal_mono n (Nat.le_succ i.val)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalSubpaths
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical lifts of quotient paths on a compact time interval.
The quotient is inverted only where it is a homeomorphism. Constant extension
at the interval ends gives an ordinary continuous physical path. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def pathsInsideOn (U : Set X) (a b : PathTime) : Set C(PathTime, X) :=
  {γ | MapsTo γ (Icc a b) U}

def physicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) : C(PathTime, Y) where
  toFun t := (e.symm ⟨γ.val (timeClip a b t), γ.property (by
    rw [← range_timeClip hab]
    exact mem_range_self t)⟩).val
  continuous_toFun := continuous_subtype_val.comp
    (e.symm.continuous.comp ((γ.val.continuous.comp (timeClip a b).continuous).subtype_mk _))

def totalPhysicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (y₀ : Y) (γ : C(PathTime, X)) : C(PathTime, Y) := by
  classical
  exact if h : γ ∈ pathsInsideOn U a b then physicalSubpath e hab ⟨γ, h⟩
    else ContinuousMap.const _ y₀

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalDyadicLength
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel dyadic physical length and finite-stage occupation data.
Every length here uses the physical metric after inverting the quotient. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

def physicalDyadicPath (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n))
    (γ : C(PathTime, X)) : C(PathTime, Y) :=
  totalPhysicalSubpath e (dyadicLeft_le_right n i) y₀ γ

def physicalDyadicLength (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n))
    (γ : C(PathTime, X)) : ℝ≥0∞ :=
  eVariationOn (physicalDyadicPath e y₀ n i γ) univ

def physicalStageLength (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (γ : C(PathTime, X)) : ℝ≥0∞ :=
  ∑ i : Fin (2 ^ n), physicalDyadicLength e y₀ n i γ

def physicalDomainLength (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) : ℝ≥0∞ :=
  ⨆ n : ℕ, physicalStageLength e y₀ n γ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothContours
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact smooth cutoffs and regular superlevel neighborhoods

This is the first half of the common contour construction in §1 of
the Koebe manuscript's small-disks proof. The cutoff is constructed
using Mathlib's smooth Urysohn theorem and a relatively compact open
neighborhood; its existence is unconditional.

Only the regular-value choice is conditional on a published input:
Arthur Sard, *The measure of the critical values of differentiable
maps*, Bull. Amer. Math. Soc. 48 (1942), 883--890, Theorem 7.2,
pp. 889--890, DOI: 10.1090/S0002-9904-1942-07811-6. We use only its
specialization to compactly supported smooth maps from the plane to
the real line. The assumption says that their actual critical-value
image has Lebesgue outer measure zero.
Original article: https://doi.org/10.1090/S0002-9904-1942-07811-6
Readable scan: https://webhomes.maths.ed.ac.uk/~v1ranick/papers/sard.pdf

No smooth Jordan disk or finite-component decomposition is assumed.
The constructed neighborhood has compact closure in the prescribed
open set and its boundary lies in a compact regular level set.
-/

open Set Filter Function MeasureTheory
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The actual differential is nonzero at every point of the level. -/
def IsPlanarRegularValue (f : ℂ → ℝ) (t : ℝ) : Prop :=
  ∀ z, f z = t → fderiv ℝ f z ≠ 0

/-- Published input: Sard (1942), Theorem 7.2, restricted to the smooth
compactly supported scalar planar case needed for contour selection.
This is a proposition parameter, not a global axiom. -/
def SmoothPlanarSard : Prop :=
  ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    volume (f '' {z | fderiv ℝ f z = 0}) = 0

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularLevelFlow
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete smooth nonstationary trajectories on compact regular levels
of the actual defining planar scalar function. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

structure CompactRegularLevelFlow (f : ℂ → ℝ) (a : ℝ) where
  field : ℂ → ℂ
  lipschitzConstant : ℝ≥0
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  lipschitz : LipschitzWith lipschitzConstant field
  tangent : ∀ z, (fderiv ℝ f z) (field z) = 0
  trajectory : {z // f z = a} → ℝ → ℂ
  initial : ∀ z, trajectory z 0 = z.val
  equation : ∀ z t, HasDerivAt (trajectory z) (field (trajectory z t)) t
  scalar : ∀ z t, f (trajectory z t) = a
  trajectory_smooth : ∀ z, ContDiff ℝ ∞ (trajectory z)
  regular : ∀ z t, deriv (trajectory z) t ≠ 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularLevelOpenOrbit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each orbit is open in its actual regular level, as witnessed by the
nonzero derivative of its local level coordinate. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def CompactRegularLevelFlow.levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) (t : ℝ) : {z // f z = a} :=
  ⟨F.trajectory x t,F.scalar x t⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanContours
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Circle contours of compact regular levels

Two classical inputs are separated from the contour construction.

* `CompactOneManifoldClassification` is the compact boundaryless case of
  Milnor, *Topology from the Differentiable Viewpoint* (1965), Appendix
  "Classifying 1-Manifolds", theorem p. 55 (proof pp. 55--57).
  https://www.ux1.eiu.edu/~cidelman/Classes/4855%20and%205220/Supplementary%20Texts/MilnorTopDiffVpt.pdf
* `PlanarSchoenflies` is Moise, *Geometric Topology in Dimensions 2 and 3*,
  Graduate Texts in Mathematics 47 (1977), Theorem 10.4: a continuous
  injection of the unit circle into the plane extends to a homeomorphism
  of the plane. DOI: https://doi.org/10.1007/978-1-4612-9906-6

Both are explicit proposition parameters, not axioms. Neither input asserts
the manuscript's obstacle-isolating disk selection. Smooth local charts,
finite components, their planar embeddings and the contour cover are proved.
-/

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- Published input: the planar Schoenflies extension theorem in exactly its
circle-to-plane form. -/
def PlanarSchoenflies : Prop :=
  ∀ γ : Circle → ℂ, Continuous γ → Injective γ →
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle, H (z : ℂ) = γ z

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_OuterContours
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting outer Jordan contours

The disks are images of the unit disk by planar homeomorphisms. Connected
exteriors and the nesting alternative allow selection of the maximal
members of a finite family.
-/

open Set Filter Function
open scoped Topology

namespace CircleDomainRigidity

def jordanInterior (H : ℂ ≃ₜ ℂ) : Set ℂ := H '' Metric.ball (0 : ℂ) 1

theorem jordanInterior_isOpen (H : ℂ ≃ₜ ℂ) : IsOpen (jordanInterior H) :=
  H.isOpenMap _ Metric.isOpen_ball

theorem closure_jordanInterior (H : ℂ ≃ₜ ℂ) :
    closure (jordanInterior H) = H '' Metric.closedBall (0 : ℂ) 1 := by
  rw [jordanInterior, ← H.image_closure, closure_ball _ one_ne_zero]

theorem isCompact_closure_jordanInterior (H : ℂ ≃ₜ ℂ) :
    IsCompact (closure (jordanInterior H)) := by
  rw [closure_jordanInterior]
  exact (isCompact_closedBall (0 : ℂ) 1).image H.continuous

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanNeighborhoods
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smooth Jordan neighborhoods

The contour construction in Section 1 of the Koebe manuscript is derived
from the smooth cutoff and regular level, scalar Sard, compact
one-manifold classification, and planar Schoenflies. Outer selection and containment
give the finite family of Jordan neighborhoods.
-/

open Set Filter Function
open scoped Topology ContDiff Manifold

namespace CircleDomainRigidity

/-- A connected unbounded exterior cannot enter the bounded side of a
Jordan curve that it misses. This applies to physical inverse images of
quotient Jordan neighborhoods, even when their boundaries are not smooth. -/
theorem closed_jordanInterior_subset_of_unbounded_connected_compl
    (H : ℂ ≃ₜ ℂ) {V : Set ℂ}
    (hV : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ)
    (hfront : frontier (jordanInterior H) ⊆ V) :
    closure (jordanInterior H) ⊆ V := by
  have hsplit : Vᶜ ⊆ jordanInterior H ∨ Vᶜ ⊆ (closure (jordanInterior H))ᶜ := by
    apply hV.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
    · intro z hz
      by_cases hzin : z ∈ jordanInterior H
      · exact Or.inl hzin
      · right
        intro hzcl
        apply hz
        apply hfront
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hzcl, hzin⟩
  rcases hsplit with hin | hout
  · exact (hVunbounded ((isCompact_closure_jordanInterior H).isBounded.subset
      (hin.trans subset_closure))).elim
  · exact compl_subset_compl.mp hout

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The retained core and completed domain of a finite disk construction

The core is the spherical complement of all terminal and filling disks.
If the disks cover the preimage of the quotient dust, the core is a compact
subset of the original domain. Filling the second family leaves precisely
the complement of the terminal interiors. This completed compact set has
the open neighborhood consisting of the original domain and the filling
interiors. In a finite chart its bounded closed pieces are compact, even
though the entire planar exterior is unbounded.

The final statements apply the actual finite patching construction to this
open neighborhood and recover local agreement on the retained core.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

def sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i)

@[simp] theorem coe_mem_sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) (z : ℂ) :
    (z : Sphere) ∈ sphericalDiskUnion H ↔ ∃ i, z ∈ jordanInterior (H i) := by
  simp [sphericalDiskUnion, OnePoint.coe_injective.mem_set_image]

@[simp] theorem infty_not_mem_sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) :
    OnePoint.infty ∉ sphericalDiskUnion H := by
  simp [sphericalDiskUnion]

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CoreGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Keeping the selected physical core away from all terminal disks

A closed planar core extends across infinity to a compact spherical
core. Its quotient image is disjoint from the quotient dust. Thus the
terminal and filling neighborhoods can be chosen away from the entire
retained core. Compact planar tail pieces suffice for the metric step.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def sphericalCore (K : Set (ℝ × ℝ)) : Set Sphere :=
  (((↑) : ℂ → Sphere) '' (Complex.equivRealProdCLM ⁻¹' Kᶜ))ᶜ

@[simp] theorem coe_mem_sphericalCore (K : Set (ℝ × ℝ)) (z : ℂ) :
    (z : Sphere) ∈ sphericalCore K ↔ Complex.equivRealProdCLM z ∈ K := by
  simp [sphericalCore, OnePoint.coe_injective.mem_set_image]

@[simp] theorem infty_mem_sphericalCore (K : Set (ℝ × ℝ)) :
    OnePoint.infty ∈ sphericalCore K := by
  simp [sphericalCore]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_EuclideanPlaneCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The area-preserving linear coordinates connecting the physical plane
with the Euclidean-space Sobolev library. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

def euclideanPlaneCoordinates : EuclideanPlane ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp] theorem euclideanPlaneCoordinates_apply (x : EuclideanPlane) :
    euclideanPlaneCoordinates x = (x 0, x 1) := rfl

@[simp] theorem euclideanPlaneCoordinates_single_zero :
    euclideanPlaneCoordinates (EuclideanSpace.single 0 1) = (1, 0) := by
  simp [euclideanPlaneCoordinates_apply]

@[simp] theorem euclideanPlaneCoordinates_single_one :
    euclideanPlaneCoordinates (EuclideanSpace.single 1 1) = (0, 1) := by
  simp [euclideanPlaneCoordinates_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.KLS_Sobolev_WeakDerivatives
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def HasWeakPartialDeriv (i : Fin d) (g f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ φ : E → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      -∫ x in Ω, g x * φ x

def HasWeakGrad (G : E → E) (f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ i : Fin d, HasWeakPartialDeriv i (fun x => G x i) f Ω

omit [NeZero d] in

theorem HasWeakPartialDeriv.ae_eq {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {g₁ g₂ f : E → ℝ}
    (h1 : HasWeakPartialDeriv i g₁ f Ω) (h2 : HasWeakPartialDeriv i g₂ f Ω)
    (hg₁ : LocallyIntegrable g₁ (volume.restrict Ω))
    (hg₂ : LocallyIntegrable g₂ (volume.restrict Ω)) :
    g₁ =ᵐ[volume.restrict Ω] g₂ := by
  suffices h : ∀ᵐ x ∂(volume.restrict Ω), (g₁ - g₂) x = 0 by
    filter_upwards [h] with x hx
    simp [sub_eq_zero] at hx
    exact hx
  rw [ae_restrict_iff' hΩ.measurableSet]
  apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hΩ
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict (hg₁.sub hg₂)
  · intro φ hφ hφ_supp hφ_tsupport
    have eq1 := h1 φ hφ hφ_supp hφ_tsupport
    have eq2 := h2 φ hφ hφ_supp hφ_tsupport
    have h_eq : ∫ x in Ω, g₁ x * φ x = ∫ x in Ω, g₂ x * φ x := by
      linarith
    have h_zero : ∀ x, x ∉ Ω → φ x • (g₁ - g₂) x = 0 := by
      intro x hx
      have hφx : φ x = 0 := by
        by_contra h
        exact hx (hφ_tsupport (subset_tsupport _ h))
      simp [hφx]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_zero]
    simp_rw [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub]
    · simp_rw [mul_comm (φ _)]
      linarith
    ·
      have : Integrable (fun x => φ x • g₁ x) (volume.restrict Ω) :=
        hg₁.integrable_smul_left_of_hasCompactSupport hφ.continuous hφ_supp
      simpa [smul_eq_mul] using this
    ·
      have : Integrable (fun x => φ x • g₂ x) (volume.restrict Ω) :=
        hg₂.integrable_smul_left_of_hasCompactSupport hφ.continuous hφ_supp
      simpa [smul_eq_mul] using this

omit [NeZero d] in

theorem HasWeakPartialDeriv.of_contDiff {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDeriv i (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω := by
  let _ := hΩ
  intro φ hφ hφ_supp hφ_sub
  let v := EuclideanSpace.single i (1 : ℝ)
  have h_fderiv_supp : tsupport (fun x => (fderiv ℝ φ x) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφ_sub
  have hf_diff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hf_cont : Continuous f := hf_diff.continuous
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hfderiv_φ_cont : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderiv_f_cont : Continuous (fun x => (fderiv ℝ f x) v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφ_fderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) v) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) v
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_integral_of_forall_compl_eq_zero]
  ·
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hfderiv_f_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
      ((hf_cont.mul hfderiv_φ_cont).integrable_of_hasCompactSupport hφ_fderiv_supp.mul_left)
      ((hf_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
      (fun x _ => hf_diff x) (fun x _ => hφ_diff x)
  ·
    intro x hx
    have : x ∉ tsupport φ := fun h => hx (hφ_sub h)
    simp only [mul_eq_zero]
    right
    by_contra hf'
    exact this (subset_tsupport φ (mem_support.mpr hf'))
  ·
    intro x hx
    have : x ∉ tsupport (fun x => (fderiv ℝ φ x) v) := fun h => hx (h_fderiv_supp h)
    simp only [mul_eq_zero]
    right
    by_contra hf'
    exact this (subset_tsupport _ (mem_support.mpr hf'))

omit [NeZero d] in

theorem HasWeakPartialDeriv.mul_smooth {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {g f η : E → ℝ}
    (hf : HasWeakPartialDeriv i g f Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hf_int : LocallyIntegrable f (volume.restrict Ω))
    (hg_int : LocallyIntegrable g (volume.restrict Ω)) :
    HasWeakPartialDeriv i
      (fun x => η x * g x + (fderiv ℝ η x) (EuclideanSpace.single i 1) * f x)
      (fun x => η x * f x) Ω := by
  let _ := hΩ
  intro φ hφ_smooth hφ_supp hφ_sub
  have hηφ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * φ x) := hη.mul hφ_smooth
  have hηφ_supp : HasCompactSupport (fun x => η x * φ x) := hφ_supp.mul_left
  have hηφ_tsub : tsupport (fun x => η x * φ x) ⊆ Ω :=
    (tsupport_smul_subset_right η φ).trans hφ_sub
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
  let ei : E := EuclideanSpace.single i (1 : ℝ)
  have fderiv_prod : ∀ x : E, (fderiv ℝ (fun y => η y * φ y) x) ei =
      η x * (fderiv ℝ φ x) ei + φ x * (fderiv ℝ η x) ei := by
    intro x
    rw [fderiv_fun_mul hη_diff.differentiableAt hφ_diff.differentiableAt]
    simp [smul_eq_mul]
  have key :
      ∫ x in Ω, f x * (η x * (fderiv ℝ φ x) ei + φ x * (fderiv ℝ η x) ei) =
        -∫ x in Ω, g x * (η x * φ x) := by
    simpa [fderiv_prod, ei] using hf (fun x => η x * φ x) hηφ_smooth hηφ_supp hηφ_tsub
  have hη_deriv_cont : Continuous (fun x => (fderiv ℝ η x) ei) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ_deriv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
    (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ_deriv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) ei
  have int_f_φ_dη :
      Integrable (fun x => f x * (φ x * (fderiv ℝ η x) ei)) (volume.restrict Ω) := by
    have h := hf_int.integrable_smul_right_of_hasCompactSupport
      (hφ_smooth.continuous.mul hη_deriv_cont) hφ_supp.smul_right
    simpa [smul_eq_mul] using h
  have int_f_η_dφ :
      Integrable (fun x => f x * (η x * (fderiv ℝ φ x) ei)) (volume.restrict Ω) := by
    have h := hf_int.integrable_smul_right_of_hasCompactSupport
      (hη.continuous.mul hφ_deriv_cont) hφ_deriv_supp.mul_left
    simpa [smul_eq_mul] using h
  have int_g_ηφ : Integrable (fun x => g x * (η x * φ x)) (volume.restrict Ω) := by
    have h := hg_int.integrable_smul_right_of_hasCompactSupport
      (hη.continuous.mul hφ_smooth.continuous) hηφ_supp
    simpa [smul_eq_mul] using h
  have key2 :
      ∫ x in Ω, f x * (η x * (fderiv ℝ φ x) ei) + f x * (φ x * (fderiv ℝ η x) ei) =
        -∫ x in Ω, g x * (η x * φ x) := by
    simp_rw [← mul_add] at key ⊢
    exact key
  rw [integral_add int_f_η_dφ int_f_φ_dη] at key2
  show ∫ x in Ω, η x * f x * (fderiv ℝ φ x) ei =
    -∫ x in Ω, (η x * g x + (fderiv ℝ η x) ei * f x) * φ x
  have goal_rhs_conv :
      (fun x => (η x * g x + (fderiv ℝ η x) ei * f x) * φ x) =
        (fun x => g x * (η x * φ x) + f x * (φ x * (fderiv ℝ η x) ei)) := by
    ext x
    ring
  simp_rw [goal_rhs_conv]
  rw [integral_add int_g_ηφ int_f_φ_dη, neg_add]
  have goal_lhs_conv :
      (fun x => η x * f x * (fderiv ℝ φ x) ei) =
        (fun x => f x * (η x * (fderiv ℝ φ x) ei)) := by
    ext x
    ring
  simp_rw [goal_lhs_conv]
  linarith

omit [NeZero d] in
theorem HasWeakPartialDeriv.restrict {Ω Ω' : Set E}
    (hΩ' : IsOpen Ω') (h_sub : Ω' ⊆ Ω)
    {i : Fin d} {g f : E → ℝ}
    (hf : HasWeakPartialDeriv i g f Ω) :
    HasWeakPartialDeriv i g f Ω' := by
  let _ := hΩ'
  intro φ hφ_smooth hφ_compact hφ_supp
  have hφ_supp_Ω : tsupport φ ⊆ Ω := hφ_supp.trans h_sub
  have key := hf φ hφ_smooth hφ_compact hφ_supp_Ω
  have h1 : ∀ x, x ∉ Ω' → f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun h => hx (hφ_supp h)
    have hφ_eq : φ =ᶠ[𝓝 x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp
  have h2 : ∀ x, x ∉ Ω' → g x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ_supp h))]
  have h3 : ∀ x, x ∉ Ω → f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 :=
    fun x hx => h1 x (fun h => hx (h_sub h))
  have h4 : ∀ x, x ∉ Ω → g x * φ x = 0 :=
    fun x hx => h2 x (fun h => hx (h_sub h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    setIntegral_eq_integral_of_forall_compl_eq_zero h2,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero h3,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero h4,
    key]

omit [NeZero d] in
lemma tendsto_integral_mul_of_eLpNorm_tendsto_zero_p
    {μ : Measure E} {f : E → ℝ} {g : ℕ → E → ℝ} {p q : ℝ}
    (hpq : p⁻¹ + q⁻¹ = 1) (hp : 1 < p) (hq : 1 < q)
    (hf : MemLp f (ENNReal.ofReal q) μ)
    (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun n => eLpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) atTop (nhds 0) := by
  have hpqR : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, hpq⟩
  let C : ℝ := MeasureTheory.lpNorm f (ENNReal.ofReal q) μ
  have hlim' : Tendsto (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    have hlim_toReal :
        Tendsto (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun n => (hg n).eLpNorm_ne_top)).2 hlim
    have hEq :
        (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) =
          (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) := by
      funext n
      simpa using
        (MeasureTheory.toReal_eLpNorm
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) (hg n).aestronglyMeasurable)
    simpa [hEq] using hlim_toReal
  have hbound :
      ∀ n, |∫ x, f x * g n x ∂μ| ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
    intro n
    have h_int :
        |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by
      calc
        |∫ x, f x * g n x ∂μ| = ‖∫ x, f x * g n x ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖f x * g n x‖ ∂μ := by
          simpa using norm_integral_le_integral_norm (μ := μ) (f := fun x => f x * g n x)
        _ = ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by simp_rw [norm_mul]
    have h_holder :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := μ) (f := f) (g := g n) (p := q) (q := p) hpqR.symm hf (hg n)
    have hp0 : ENNReal.ofReal p ≠ 0 := by
      intro hp0'
      have : p ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hp0'
      linarith
    have hq0 : ENNReal.ofReal q ≠ 0 := by
      intro hq0'
      have : q ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hq0'
      linarith
    have h_f_lp :
        MeasureTheory.lpNorm f (ENNReal.ofReal q) μ =
          (∫ x, ‖f x‖ ^ q ∂μ) ^ q⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal q) (f := f) hq0 (by simp) hf.aestronglyMeasurable)
    have h_g_lp :
        MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ =
          (∫ x, ‖g n x‖ ^ p ∂μ) ^ p⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) hp0 (by simp) (hg n).aestronglyMeasurable)
    calc
      |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := h_int
      _ ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
        simpa [C, h_f_lp, h_g_lp, mul_comm, mul_left_comm, mul_assoc] using h_holder
  have h_upper :
      Tendsto (fun n => C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    simpa using Tendsto.const_mul C hlim'
  have h_abs :
      Tendsto (fun n => |∫ x, f x * g n x ∂μ|) atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound h_upper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs

omit [NeZero d] in

theorem HasWeakPartialDeriv.of_eLpNormApprox_p
    {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p)
    {i : Fin d} {f g : E → ℝ} {ψ : ℕ → E → ℝ} {gψ : ℕ → E → ℝ}
    (hf_memLp : MemLp f (ENNReal.ofReal p) (volume.restrict Ω))
    (hg_memLp : MemLp g (ENNReal.ofReal p) (volume.restrict Ω))
    (hψ_wd : ∀ n, HasWeakPartialDeriv i (gψ n) (ψ n) Ω)
    (hψ_fun_memLp : ∀ n, MemLp (fun x => ψ n x - f x) (ENNReal.ofReal p) (volume.restrict Ω))
    (hψ_fun :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - f x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0))
    (hψ_grad_memLp : ∀ n, MemLp (fun x => gψ n x - g x) (ENNReal.ofReal p) (volume.restrict Ω))
    (hψ_grad :
      Tendsto (fun n => eLpNorm (fun x => gψ n x - g x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0)) :
    HasWeakPartialDeriv i g f Ω := by
  let _ := hΩ
  intro φ hφ hφ_supp hφ_sub
  let μ : Measure E := volume.restrict Ω
  let dφ : E → ℝ := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  let q : ℝ := Real.conjExponent p
  have hpqR : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hpq : p⁻¹ + q⁻¹ = 1 := (Real.holderConjugate_iff.mp hpqR).2
  have hq : 1 < q := (Real.holderConjugate_iff.mp hpqR.symm).1
  let : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 :=
    ENNReal.HolderConjugate.of_toReal <| by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p),
        ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using hpqR
  have hdφ_memLp : MemLp dφ (ENNReal.ofReal q) μ := by
    have hcont : Continuous dφ := by
      simpa [dφ] using
        ((hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const)
    have hcpt : HasCompactSupport dφ := by
      simpa [dφ] using hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    exact (hcont.memLp_of_hasCompactSupport hcpt).restrict _
  have hφ_memLp : MemLp φ (ENNReal.ofReal q) μ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_supp).restrict _
  have h_fun_int :
      Tendsto (fun n => ∫ x, dφ x * (ψ n x - f x) ∂μ) atTop (nhds 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero_p hpq hp hq hdφ_memLp hψ_fun_memLp hψ_fun
  have h_grad_int :
      Tendsto (fun n => ∫ x, φ x * (gψ n x - g x) ∂μ) atTop (nhds 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero_p hpq hp hq hφ_memLp hψ_grad_memLp hψ_grad
  have h_lhs_tendsto :
      Tendsto (fun n => ∫ x in Ω, ψ n x * dφ x)
        atTop (nhds (∫ x in Ω, f x * dφ x)) := by
    have h_eq :
        (fun n => ∫ x in Ω, ψ n x * dφ x) =
          fun n => (∫ x in Ω, f x * dφ x) + ∫ x, dφ x * (ψ n x - f x) ∂μ := by
      funext n
      have hfi : Integrable (fun x => f x * dφ x) μ :=
        hf_memLp.integrable_mul hdφ_memLp
      have hdi : Integrable (fun x => dφ x * (ψ n x - f x)) μ :=
        hdφ_memLp.integrable_mul (hψ_fun_memLp n)
      calc
        ∫ x in Ω, ψ n x * dφ x
            = ∫ x, (f x * dφ x) + dφ x * (ψ n x - f x) ∂μ := by
                congr with x
                ring
        _ = (∫ x, f x * dφ x ∂μ) + ∫ x, dφ x * (ψ n x - f x) ∂μ :=
              integral_add hfi hdi
    rw [h_eq]
    simpa [μ] using Tendsto.const_add _ h_fun_int
  have h_rhs_tendsto :
      Tendsto (fun n => -∫ x in Ω, gψ n x * φ x)
        atTop (nhds (-∫ x in Ω, g x * φ x)) := by
    have h_eq :
        (fun n => -∫ x in Ω, gψ n x * φ x) =
          fun n => -(∫ x in Ω, g x * φ x) - ∫ x, φ x * (gψ n x - g x) ∂μ := by
      funext n
      have hgi : Integrable (fun x => g x * φ x) μ :=
        hg_memLp.integrable_mul hφ_memLp
      have hdi : Integrable (fun x => φ x * (gψ n x - g x)) μ :=
        hφ_memLp.integrable_mul (hψ_grad_memLp n)
      have : ∫ x, gψ n x * φ x ∂μ =
          (∫ x, g x * φ x ∂μ) + ∫ x, φ x * (gψ n x - g x) ∂μ := by
        calc
          ∫ x, gψ n x * φ x ∂μ
              = ∫ x, (g x * φ x) + φ x * (gψ n x - g x) ∂μ := by
                  congr with x
                  ring
          _ = (∫ x, g x * φ x ∂μ) + ∫ x, φ x * (gψ n x - g x) ∂μ :=
                integral_add hgi hdi
      linarith
    have h_aux :
        Tendsto
          (fun n => -(∫ x, g x * φ x ∂μ) - ∫ x, φ x * (gψ n x - g x) ∂μ)
          atTop (nhds (-(∫ x, g x * φ x ∂μ) - 0)) :=
      Tendsto.const_sub _ h_grad_int
    simpa [μ, h_eq] using h_aux
  have h_eq_n :
      ∀ n,
        ∫ x in Ω, ψ n x * dφ x = -∫ x in Ω, gψ n x * φ x := by
    intro n
    exact hψ_wd n φ hφ hφ_supp hφ_sub
  have h_eq_tendsto :
      Tendsto (fun n => ∫ x in Ω, ψ n x * dφ x)
        atTop (nhds (-∫ x in Ω, g x * φ x)) := by
    simpa [h_eq_n] using h_rhs_tendsto
  exact tendsto_nhds_unique h_lhs_tendsto h_eq_tendsto

end DeGiorgi

end

end OAI
end

section
-- module Solutions.Q146_CD.KLS_Sobolev_Witnesses
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def MemW1p (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) : Prop :=
  MemLp f p (μ.restrict Ω) ∧
  ∀ i : Fin d, ∃ g : E → ℝ,
    MemLp g p (μ.restrict Ω) ∧ HasWeakPartialDeriv i g f Ω

structure MemW1pWitness (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) where

  memLp : MemLp f p (μ.restrict Ω)

  weakGrad : E → E

  weakGrad_component_memLp : ∀ i : Fin d,
    MemLp (fun x => weakGrad x i) p (μ.restrict Ω)

  isWeakGrad : HasWeakGrad weakGrad f Ω

def MemW01p (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) : Prop :=
  MemW1p p f Ω μ ∧
  ∃ (hw : MemW1pWitness p f Ω μ) (φ : ℕ → E → ℝ),
    (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
    (∀ n, HasCompactSupport (φ n)) ∧
    (∀ n, tsupport (φ n) ⊆ Ω) ∧
    Tendsto (fun n => eLpNorm (fun x => φ n x - f x) p (μ.restrict Ω))
      atTop (nhds 0) ∧
    ∀ i : Fin d,
      Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        p (μ.restrict Ω))
        atTop (nhds 0)

noncomputable def MemW1p.someWitness
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hf : MemW1p p f Ω μ) :
    MemW1pWitness p f Ω μ := by
  rcases hf with ⟨hf_memLp, hf_grad⟩
  choose g hg_memLp hg_weak using hf_grad
  let G : E → E := fun x => WithLp.toLp 2 fun i => g i x
  exact
    { memLp := hf_memLp
      weakGrad := G
      weakGrad_component_memLp := hg_memLp
      isWeakGrad := hg_weak }

omit [NeZero d] in

theorem MemW1pWitness.memW1p
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hw : MemW1pWitness p f Ω μ) :
    MemW1p p f Ω μ := by
  refine ⟨hw.memLp, ?_⟩
  intro i
  exact ⟨fun x => hw.weakGrad x i, hw.weakGrad_component_memLp i, hw.isWeakGrad i⟩

noncomputable def MemW1pWitness.restrict
    {p : ℝ≥0∞} {Ω Ω' : Set E} {f : E → ℝ}
    (hΩ' : IsOpen Ω')
    (hsub : Ω' ⊆ Ω)
    (hw : MemW1pWitness p f Ω) :
    MemW1pWitness p f Ω' where
  memLp := hw.memLp.mono_measure (Measure.restrict_mono_set volume hsub)
  weakGrad := hw.weakGrad
  weakGrad_component_memLp := by
    intro i
    exact (hw.weakGrad_component_memLp i).mono_measure (Measure.restrict_mono_set volume hsub)
  isWeakGrad := by
    intro i
    exact HasWeakPartialDeriv.restrict hΩ' hsub (hw.isWeakGrad i)

noncomputable def MemW1pWitness.mul_smooth_bounded_p
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u η : E → ℝ} (hw : MemW1pWitness p u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    MemW1pWitness p (fun x => η x * u x) Ω where
  memLp := by
    let _ := hC₀
    let _ := hC₁
    refine MemLp.of_le_mul (g := u) (c := C₀) hw.memLp ?_ ?_
    · exact hη.continuous.aestronglyMeasurable.mul hw.memLp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        calc
          ‖η x * u x‖ = |η x| * ‖u x‖ := by
            rw [norm_mul, Real.norm_eq_abs]
          _ ≤ C₀ * ‖u x‖ := by
            gcongr
            exact hη_bound x
  weakGrad := fun x =>
    η x • hw.weakGrad x +
      (show E from WithLp.toLp 2 fun i => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)
  weakGrad_component_memLp := by
    intro i
    have hfirst : MemLp (fun x => η x * hw.weakGrad x i) p (volume.restrict Ω) := by
      refine MemLp.of_le_mul (g := fun x => hw.weakGrad x i) (c := C₀)
        (hw.weakGrad_component_memLp i) ?_ ?_
      · exact hη.continuous.aestronglyMeasurable.mul
          (hw.weakGrad_component_memLp i).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          calc
            ‖η x * hw.weakGrad x i‖ = |η x| * ‖hw.weakGrad x i‖ := by
              rw [norm_mul, Real.norm_eq_abs]
            _ ≤ C₀ * ‖hw.weakGrad x i‖ := by
              gcongr
              exact hη_bound x
    have hderiv_cont : Continuous (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) :=
      (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
    have hsecond :
        MemLp (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) p
          (volume.restrict Ω) := by
      refine MemLp.of_le_mul (g := u) (c := C₁) hw.memLp ?_ ?_
      · exact hderiv_cont.aestronglyMeasurable.mul hw.memLp.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1) * u x‖
                = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖u x‖ := by
                    rw [norm_mul]
            _ ≤ ‖fderiv ℝ η x‖ * ‖u x‖ := by
                  gcongr
                  simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                    (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ C₁ * ‖u x‖ := by
                  gcongr
                  exact hη_grad_bound x
    simpa using! hfirst.add hsecond
  isWeakGrad := by
    intro i
    simpa using HasWeakPartialDeriv.mul_smooth hΩ
      (hf := hw.isWeakGrad i) hη
      (hw.memLp.locallyIntegrable hp)
      ((hw.weakGrad_component_memLp i).locallyIntegrable hp)

omit [NeZero d] in

theorem MemW1pWitness.weakGrad_memLp
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hw : MemW1pWitness p f Ω μ) :
    MemLp hw.weakGrad p (μ.restrict Ω) := by
  refine MemLp.of_eval_piLp ?_
  intro i
  simpa using hw.weakGrad_component_memLp i

end DeGiorgi

end

end OAI
end

section
-- module Solutions.Q146_CD.KLS_Sobolev_SobolevApproximation
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
lemma exists_smooth_cutoff
    {K Ω : Set E}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ η : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ K, η x = 1) ∧
      tsupport η ⊆ Ω := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ E) (s := Metric.thickening δ K) (t := K)
      isOpen_thickening hK.isClosed (self_subset_thickening hδ_pos K) with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  refine ⟨η, contMDiff_iff_contDiff.mp hη_smooth, ?_, hη_range, ?_, ?_⟩
  · apply HasCompactSupport.intro' (K := Metric.cthickening δ K)
    · exact hK.cthickening (r := δ)
    · simpa using (isClosed_cthickening : IsClosed (Metric.cthickening δ K))
    · intro x hx
      have hxt : x ∉ tsupport η := by
        intro hxt
        have hx_closure : x ∈ closure (Metric.thickening δ K) := by
          rw [tsupport, hη_support] at hxt
          exact hxt
        exact hx ((Metric.closure_thickening_subset_cthickening δ K) hx_closure)
      exact image_eq_zero_of_notMem_tsupport hxt
  · intro x hx
    exact (hη_one_iff x).1 hx
  · rw [tsupport, hη_support]
    exact Metric.closure_thickening_subset_cthickening δ K |>.trans hδΩ

lemma memW01p_of_global_approx_supported
    {Ω : Set E} {p : ℝ≥0∞} {u : E → ℝ}
    (hw : MemW1pWitness p u Ω)
    (φ : ℕ → E → ℝ)
    (hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hφ_compact : ∀ n, HasCompactSupport (φ n))
    (hφ_sub : ∀ n, tsupport (φ n) ⊆ Ω)
    (hφ_fun :
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) p (volume.restrict Ω))
        atTop (nhds 0))
    (hφ_grad :
      ∀ i : Fin d, Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        p (volume.restrict Ω)) atTop (nhds 0)) :
    MemW01p p u Ω := by
  let _ := (inferInstance : NeZero d)
  exact ⟨hw.memW1p, hw, φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩

omit [NeZero d] in
theorem zero_outside_of_tsupport_subset
    {Ω : Set E} {f : E → ℝ}
    (hsub : tsupport f ⊆ Ω) {x : E} (hx : x ∉ Ω) :
    f x = 0 := by
  by_cases hfx : f x = 0
  · exact hfx
  · exfalso
    exact hx (hsub (subset_tsupport f (mem_support.mpr hfx)))

theorem fderiv_apply_zero_outside_of_tsupport_subset
    {Ω : Set E} {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsub : tsupport f ⊆ Ω) {x : E} (hx : x ∉ Ω) (i : Fin d) :
    (fderiv ℝ f x) (EuclideanSpace.single i 1) = 0 := by
  let _ := (inferInstance : NeZero d)
  let _ := hf
  apply zero_outside_of_tsupport_subset
    (Ω := Ω)
    (f := fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1))
  · exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i (1 : ℝ))).trans hsub
  · exact hx

noncomputable def zeroExtend_memW1pWitness_p
    {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p)
    {v : E → ℝ}
    (hv : MemW01p (ENNReal.ofReal p) v Ω)
    (hw : MemW1pWitness (ENNReal.ofReal p) v Ω) :
    MemW1pWitness (ENNReal.ofReal p) (Ω.indicator v) Set.univ := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  let hw₀ : MemW1pWitness (ENNReal.ofReal p) v Ω := Classical.choose hv.2
  let hExφ := Classical.choose_spec hv.2
  let φ : ℕ → E → ℝ := Classical.choose hExφ
  have hφspec := Classical.choose_spec hExφ
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) := hφspec.1
  have hφ_compact : ∀ n, HasCompactSupport (φ n) := hφspec.2.1
  have hφ_sub : ∀ n, tsupport (φ n) ⊆ Ω := hφspec.2.2.1
  have hφ_fun :
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - v x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0) := hφspec.2.2.2.1
  have hφ_grad :
      ∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw₀.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω))
          atTop (nhds 0) := hφspec.2.2.2.2
  let G : E → E := fun x =>
    WithLp.toLp 2 fun i => Ω.indicator (fun y => hw.weakGrad y i) x
  refine
    { memLp := ?_
      weakGrad := G
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · simpa using
      (MeasureTheory.memLp_indicator_iff_restrict
        (μ := volume) (s := Ω) (f := v) (p := ENNReal.ofReal p) hΩ_meas).2 hw.memLp
  · intro i
    simpa [G, PiLp.toLp_apply] using
      (MeasureTheory.memLp_indicator_iff_restrict
        (μ := volume) (s := Ω) (f := fun y => hw.weakGrad y i) (p := ENNReal.ofReal p) hΩ_meas).2
        (hw.weakGrad_component_memLp i)
  · intro i
    have hp_le : 1 ≤ p := le_of_lt hp
    have hcompΩ :
        (fun x => hw₀.weakGrad x i) =ᵐ[volume.restrict Ω] (fun x => hw.weakGrad x i) := by
      exact HasWeakPartialDeriv.ae_eq hΩ (hw₀.isWeakGrad i) (hw.isWeakGrad i)
        ((hw₀.weakGrad_component_memLp i).locallyIntegrable (by
          simpa using (ENNReal.ofReal_le_ofReal hp_le : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)))
        ((hw.weakGrad_component_memLp i).locallyIntegrable (by
          simpa using (ENNReal.ofReal_le_ofReal hp_le : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)))
    refine HasWeakPartialDeriv.of_eLpNormApprox_p
      (d := d) (Ω := Set.univ) (p := p) (hΩ := isOpen_univ) (hp := hp)
      (i := i) (f := Ω.indicator v) (g := fun x => G x i)
      (ψ := φ)
      (gψ := fun n x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Measure.restrict_univ]
      simpa using
        (MeasureTheory.memLp_indicator_iff_restrict
          (μ := volume) (s := Ω) (f := v) (p := ENNReal.ofReal p) hΩ_meas).2 hw.memLp
    · rw [Measure.restrict_univ]
      simpa [G, PiLp.toLp_apply] using
        (MeasureTheory.memLp_indicator_iff_restrict
          (μ := volume) (s := Ω) (f := fun y => hw.weakGrad y i) (p := ENNReal.ofReal p) hΩ_meas).2
          (hw.weakGrad_component_memLp i)
    · intro n
      simpa using
        HasWeakPartialDeriv.of_contDiff (Ω := Set.univ) (i := i) (f := φ n)
          isOpen_univ ((hφ_smooth n).of_le (by norm_cast))
    · intro n
      have hφ_memLp :
          MemLp (φ n) (ENNReal.ofReal p) (volume.restrict Ω) :=
        ((hφ_smooth n).continuous.memLp_of_hasCompactSupport (hφ_compact n)).restrict Ω
      have hEq :
          (fun x => φ n x - Ω.indicator v x) =
            Ω.indicator (fun x => φ n x - v x) := by
        ext x
        by_cases hx : x ∈ Ω
        · simp [hx]
        · have hφx : φ n x = 0 := zero_outside_of_tsupport_subset (Ω := Ω) (hφ_sub n) hx
          simp [hx, hφx]
      rw [Measure.restrict_univ, hEq,
        MeasureTheory.memLp_indicator_iff_restrict (μ := volume) (s := Ω)
          (p := ENNReal.ofReal p) hΩ_meas]
      exact hφ_memLp.sub hw.memLp
    · have hEq :
          (fun n => eLpNorm (fun x => φ n x - Ω.indicator v x) (ENNReal.ofReal p) volume) =
            fun n => eLpNorm (fun x => φ n x - v x) (ENNReal.ofReal p) (volume.restrict Ω) := by
        funext n
        have hFn :
            (fun x => φ n x - Ω.indicator v x) =
              Ω.indicator (fun x => φ n x - v x) := by
          ext x
          by_cases hx : x ∈ Ω
          · simp [hx]
          · have hφx : φ n x = 0 := zero_outside_of_tsupport_subset (Ω := Ω) (hφ_sub n) hx
            simp [hx, hφx]
        rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
          (μ := volume) (s := Ω) (p := ENNReal.ofReal p) hΩ_meas]
      rw [Measure.restrict_univ, hEq]
      simpa using hφ_fun
    · intro n
      let ei : E := EuclideanSpace.single i (1 : ℝ)
      have hderiv_smooth :
          ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ (φ n) x) ei) :=
        (hφ_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)
          |>.clm_apply contDiff_const
      have hderiv_memLp :
          MemLp (fun x => (fderiv ℝ (φ n) x) ei) (ENNReal.ofReal p) (volume.restrict Ω) :=
        (hderiv_smooth.continuous.memLp_of_hasCompactSupport
          ((hφ_compact n).fderiv_apply (𝕜 := ℝ) _)).restrict Ω
      have hEq :
          (fun x => (fderiv ℝ (φ n) x) ei - G x i) =
            Ω.indicator (fun x => (fderiv ℝ (φ n) x) ei - hw.weakGrad x i) := by
        ext x
        by_cases hx : x ∈ Ω
        · simp [G, hx]
        · have hdx :
              (fderiv ℝ (φ n) x) ei = 0 := by
            simpa [ei] using
              fderiv_apply_zero_outside_of_tsupport_subset (Ω := Ω) (hf := hφ_smooth n)
                (hsub := hφ_sub n) hx i
          simp [G, hx, hdx]
      rw [Measure.restrict_univ, hEq,
        MeasureTheory.memLp_indicator_iff_restrict (μ := volume) (s := Ω)
          (p := ENNReal.ofReal p) hΩ_meas]
      exact hderiv_memLp.sub (hw.weakGrad_component_memLp i)
    · have hEq :
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i)
              (ENNReal.ofReal p) volume) =
            fun n =>
              eLpNorm
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                (ENNReal.ofReal p) (volume.restrict Ω) := by
        funext n
        have hFn :
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i) =
              Ω.indicator
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) := by
          ext x
          by_cases hx : x ∈ Ω
          · simp [G, hx]
          · have hdx :
                (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) = 0 := by
              exact fderiv_apply_zero_outside_of_tsupport_subset (Ω := Ω) (hf := hφ_smooth n)
                (hsub := hφ_sub n) hx i
            simp [G, hx, hdx]
        rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
          (μ := volume) (s := Ω) (p := ENNReal.ofReal p) hΩ_meas]
      rw [Measure.restrict_univ, hEq]
      have hEqSeq :
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω)) =
            (fun n =>
              eLpNorm
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw₀.weakGrad x i)
                (ENNReal.ofReal p) (volume.restrict Ω)) := by
        funext n
        have hDiffAe :
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              =ᵐ[volume.restrict Ω]
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw₀.weakGrad x i) := by
          filter_upwards [hcompΩ] with x hx
          simp [hx]
        exact eLpNorm_congr_ae hDiffAe
      rw [hEqSeq]
      simpa using hφ_grad i

omit [NeZero d] in
lemma tsupport_convolution_subset_cthickening
    {κ u : E → ℝ} {r : ℝ}
    (hκ : Function.support κ ⊆ Metric.closedBall (0 : E) r)
    (hu : HasCompactSupport u) :
    tsupport (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
      ⊆ Metric.cthickening r (tsupport u) := by
  let _ := hu
  have hsupport :
      Function.support (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
        ⊆ Function.support κ + Function.support u :=
    support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
  have hsum :
      Function.support κ + Function.support u ⊆ Metric.cthickening r (tsupport u) := by
    intro x hx
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
    have ha_ball : a ∈ Metric.closedBall (0 : E) r := hκ ha
    have hb_tsupport : b ∈ tsupport u := subset_tsupport u hb
    refine Metric.mem_cthickening_of_dist_le (x := a + b) (y := b) (δ := r)
      (tsupport u) hb_tsupport ?_
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using ha_ball
  simpa [tsupport] using
    closure_minimal (hsupport.trans hsum) isClosed_cthickening

omit [NeZero d] in
lemma tsupport_normed_convolution_subset_cthickening
    (φ : ContDiffBump (0 : E)) {u : E → ℝ}
    (hu : HasCompactSupport u) :
    tsupport ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
      ⊆ Metric.cthickening φ.rOut (tsupport u) :=
  tsupport_convolution_subset_cthickening
    (r := φ.rOut)
    (fun x hx => (Metric.mem_ball.1 ((by simpa [φ.support_normed_eq] using hx))).le)
    hu

noncomputable def shrinkingBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (((n : ℝ) + 1)⁻¹) / 2
  rOut := ((n : ℝ) + 1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hr_pos : 0 < (((n : ℝ) + 1)⁻¹ : ℝ) := by positivity
    nlinarith

omit [NeZero d] in
lemma tendsto_shrinkingBump_rOut :
    Tendsto (fun n => (shrinkingBump (d := d) n).rOut) atTop (nhds 0) := by
  have h :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1) : ℝ)⁻¹) atTop (nhds (0 : ℝ)) :=
    by simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa [shrinkingBump] using h

omit [NeZero d] in
theorem eLpNorm_normedConvolution_le
    (φ : ContDiffBump (0 : E))
    {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
      (ENNReal.ofReal p) volume ≤
    eLpNorm f (ENNReal.ofReal p) volume := by
  let ψ : E → ℝ := φ.normed volume
  let ρ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (ψ y)
  let ν : Measure E := volume.withDensity ρ
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp_pos)
  have hp_toReal : (ENNReal.ofReal p).toReal = p := by
    simp [hp_pos.le]
  have hρ_meas : Measurable ρ := by
    exact φ.continuous_normed.measurable.ennreal_ofReal
  have hρ_lt_top : ∀ᵐ y ∂volume, ρ y < ∞ := by
    filter_upwards with y
    simp [ρ]
  have hρ_ne_top : ∀ᵐ y ∂volume, ρ y ≠ ∞ := by
    filter_upwards [hρ_lt_top] with y hy
    exact hy.ne
  have hν_prob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [show ν = volume.withDensity ρ by rfl, withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      φ.integrable_normed (Filter.Eventually.of_forall φ.nonneg_normed)]
    simpa [ρ, ψ] using φ.integral_normed (μ := volume)
  have hf_loc : LocallyIntegrable f volume := by
    exact hf.locallyIntegrable (by simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p))
  have hh_int : Integrable (fun x => ‖f x‖ ^ p) volume := by
    simpa [hp_toReal] using hf.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  have hψ_int : Integrable ψ volume := by
    simpa [ψ] using φ.integrable_normed
  have hψ_cont : Continuous ψ := by
    simpa [ψ] using φ.continuous_normed
  have hψ_cpt : HasCompactSupport ψ := by
    simpa [ψ] using φ.hasCompactSupport_normed (μ := volume)
  have hconv_cont :
      Continuous (((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) : E → ℝ) := by
    exact hψ_cpt.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hf_loc
  have hpointwise :
      ∀ x : E,
        ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p ≤
          (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x := by
    intro x
    have hce_f :
        ConvolutionExistsAt ψ f x (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      exact (hψ_cpt.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hf_loc) x
    have hce_h :
        ConvolutionExistsAt ψ (fun y => ‖f y‖ ^ p) x (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      exact (hψ_cpt.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hh_int.locallyIntegrable) x
    have hconv_ν :
        ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) = ∫ y, f (x - y) ∂ν := by
      rw [show ν = volume.withDensity ρ by rfl]
      rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
      rw [MeasureTheory.convolution_def]
      refine integral_congr_ae ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, φ.nonneg_normed y, mul_comm]
    have h_int_norm_vol :
        Integrable (fun y => (ρ y).toReal * ‖f (x - y)‖) volume := by
      refine hce_f.integrable.norm.congr ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, φ.nonneg_normed y]
    have h_int_norm :
        Integrable (fun y => ‖f (x - y)‖) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, φ.nonneg_normed] using h_int_norm_vol
    have h_int_rpow_vol :
        Integrable (fun y => (ρ y).toReal * ‖f (x - y)‖ ^ p) volume := by
      refine hce_h.integrable.congr ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, φ.nonneg_normed y, mul_comm]
    have h_int_rpow :
        Integrable (fun y => ‖f (x - y)‖ ^ p) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, φ.nonneg_normed] using h_int_rpow_vol
    have hnorm_le : ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ≤ ∫ y, ‖f (x - y)‖ ∂ν := by
      rw [hconv_ν]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have hJensen :
        (∫ y, ‖f (x - y)‖ ∂ν) ^ p ≤ ∫ y, ‖f (x - y)‖ ^ p ∂ν := by
      have hconv : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ p) := convexOn_rpow hp
      have hcont : ContinuousOn (fun t : ℝ => t ^ p) (Set.Ici (0 : ℝ)) := by
        exact continuousOn_id.rpow_const (by
          intro t ht
          exact Or.inr hp_pos.le)
      have hmem : ∀ᵐ y ∂ν, ‖f (x - y)‖ ∈ Set.Ici (0 : ℝ) := by
        filter_upwards with y
        exact norm_nonneg _
      exact hconv.map_integral_le hcont isClosed_Ici hmem h_int_norm h_int_rpow
    calc
      ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p
          ≤ (∫ y, ‖f (x - y)‖ ∂ν) ^ p := by
            exact Real.rpow_le_rpow (norm_nonneg _) hnorm_le hp_pos.le
      _ ≤ ∫ y, ‖f (x - y)‖ ^ p ∂ν := hJensen
      _ = ∫ y, ψ y * ‖f (x - y)‖ ^ p ∂volume := by
            rw [show ν = volume.withDensity ρ by rfl]
            rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
            refine integral_congr_ae ?_
            filter_upwards with y
            simp [ρ, ψ, φ.nonneg_normed y, mul_comm]
      _ = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x := by
            simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, mul_comm]
  have hconv_h_int :
      Integrable (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) volume := by
    exact hψ_int.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hh_int
  have hpow_int :
      Integrable (fun x =>
        ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p) volume := by
    refine Integrable.mono' hconv_h_int ?_ ?_
    · exact (hconv_cont.norm.rpow_const (by intro x; exact Or.inr hp_pos.le)).aestronglyMeasurable
    · filter_upwards with x
      have hnonneg : 0 ≤ |((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)| ^ p := by
        positivity
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hpointwise x
  have h_int_le :
      ∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p ∂volume ≤
        ∫ x, (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x ∂volume := by
    refine integral_mono_ae hpow_int hconv_h_int ?_
    filter_upwards with x
    exact hpointwise x
  have h_conv_eq :
      ∫ x, (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x ∂volume =
        ∫ x, ‖f x‖ ^ p ∂volume := by
    calc
      ∫ x, (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x ∂volume
          = (∫ x, ψ x ∂volume) * (∫ x, ‖f x‖ ^ p ∂volume) := by
              simpa [ContinuousLinearMap.lsmul_apply, mul_comm, mul_left_comm, mul_assoc] using
                (MeasureTheory.integral_convolution
                  (L := ContinuousLinearMap.lsmul ℝ ℝ)
                  (μ := volume) (ν := volume) hψ_int hh_int)
      _ = ∫ x, ‖f x‖ ^ p ∂volume := by
            simp [ψ, φ.integral_normed (μ := volume)]
  have hconv_memLp :
      MemLp ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) : E → ℝ)
        (ENNReal.ofReal p) volume := by
    exact (MeasureTheory.integrable_norm_rpow_iff
      hconv_cont.aestronglyMeasurable hp0 ENNReal.ofReal_ne_top).1 <| by
        simpa [hp_toReal] using hpow_int
  calc
    eLpNorm ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) : E → ℝ)
        (ENNReal.ofReal p) volume
      = ENNReal.ofReal ((∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p ∂volume) ^ p⁻¹) := by
          simpa [hp_toReal] using
            hconv_memLp.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ p⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          refine Real.rpow_le_rpow ?_ (h_int_le.trans_eq h_conv_eq) ?_
          · exact integral_nonneg fun _ => by positivity
          · exact inv_nonneg.mpr hp_pos.le
    _ = eLpNorm f (ENNReal.ofReal p) volume := by
          symm
          simpa [hp_toReal] using hf.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top

omit [NeZero d] in
theorem normedConvolution_sub_eq
    (φ : ContDiffBump (0 : E)) {f g : E → ℝ}
    (hf_loc : LocallyIntegrable f volume) (hg_loc : LocallyIntegrable g volume) :
    (fun x =>
      ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
        ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) =
    (fun x =>
      ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => f y - g y) x) := by
  ext x
  have hce_f := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed hf_loc
  have hce_g := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed hg_loc
  have hf_int :
      Integrable (fun t => φ.normed volume t * f (x - t)) volume := by
    exact (hce_f x).congr <| Eventually.of_forall fun t => by
      simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hg_int :
      Integrable (fun t => φ.normed volume t * g (x - t)) volume := by
    exact (hce_g x).congr <| Eventually.of_forall fun t => by
      simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub hf_int hg_int]
  congr 1
  ext t
  ring

omit [NeZero d] in
theorem eLpNorm_normedConvolution_sub_le
    (φ : ContDiffBump (0 : E))
    {p : ℝ} (hp : 1 ≤ p) {f g : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    eLpNorm
      (fun x =>
        ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
          ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
      (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) volume := by
  rw [normedConvolution_sub_eq (d := d) φ
    (hf.locallyIntegrable (by
      simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)))
    (hg.locallyIntegrable (by
      simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)))]
  exact eLpNorm_normedConvolution_le (d := d) φ hp (hf.sub hg)

omit [NeZero d] in
theorem tendsto_eLpNorm_normedConvolution_sub_of_continuous
    {p : ℝ} (hp : 1 ≤ p) {g : E → ℝ}
    (hg_cont : Continuous g) (hg_comp : HasCompactSupport g) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
              g x)
          (ENNReal.ofReal p) volume)
      atTop (nhds 0) := by
  let _ := hp
  let S : Set E := Metric.cthickening 1 (tsupport g)
  let T : Set E := Metric.cthickening (1 + 1) (tsupport g)
  have hS_comp : IsCompact S := hg_comp.isCompact.cthickening (r := 1)
  have hT_comp : IsCompact T := hg_comp.isCompact.cthickening (r := 1 + 1)
  have hS_meas : MeasurableSet S := hS_comp.measurableSet
  have hS_finite : volume S < ∞ := hS_comp.measure_lt_top
  have hS_sub_T : S ⊆ T := by
    simpa [S, T] using (cthickening_mono (show (1 : ℝ) ≤ 1 + 1 by norm_num) (tsupport g))
  have hg_support_sub : Function.support g ⊆ S := by
    intro x hx
    exact Metric.mem_cthickening_of_dist_le (x := x) (y := x) (δ := 1)
      (tsupport g) (subset_tsupport g hx) (by simp)
  have huc : UniformContinuousOn g T := hT_comp.uniformContinuousOn_of_continuous hg_cont.continuousOn
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ε hε
  by_cases hε_top : ε = ∞
  · filter_upwards with n
    simp [hε_top]
  let εr : ℝ := ε.toReal
  have hεr_pos : 0 < εr := ENNReal.toReal_pos hε.ne' hε_top
  let M : ℝ≥0∞ := volume S ^ ((1 : ℝ) / (ENNReal.ofReal p).toReal)
  have hM_top : M ≠ ∞ := by
    simp [M, hS_finite.ne]
  let C : ℝ := M.toReal + 1
  have hC_pos : 0 < C := by
    have hM_nonneg : 0 ≤ M.toReal := ENNReal.toReal_nonneg
    dsimp [C]
    linarith
  let ε0 : ℝ := εr / C
  have hε0_pos : 0 < ε0 := by
    dsimp [ε0]
    positivity
  rcases Metric.uniformContinuousOn_iff.mp huc ε0 hε0_pos with ⟨δ0, hδ0_pos, hδ0⟩
  let δ : ℝ := min δ0 1
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ0_pos zero_lt_one
  have hsmall :
      ∀ᶠ n in atTop, (shrinkingBump (d := d) n).rOut < δ := by
    exact (tendsto_order.1 tendsto_shrinkingBump_rOut).2 _ hδ_pos
  filter_upwards [hsmall] with n hn
  have hrOut_le_one : (shrinkingBump (d := d) n).rOut ≤ 1 := by
    exact le_trans hn.le (min_le_right _ _)
  have hconv_support_sub :
      Function.support
          (((shrinkingBump (d := d) n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
        ⊆ S := by
    intro x hx
    have hts :
        tsupport
            (((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g))
          ⊆ S := by
      refine (tsupport_normed_convolution_subset_cthickening (d := d) (shrinkingBump (d := d) n) hg_comp).trans ?_
      simpa [S] using cthickening_mono hrOut_le_one (tsupport g)
    exact hts (subset_tsupport _ hx)
  have hdist :
      ∀ x : E,
        dist
            (((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
            (g x) ≤ ε0 := by
    intro x
    by_cases hx : x ∈ S
    · have hxT : x ∈ T := hS_sub_T hx
      refine (shrinkingBump (d := d) n).dist_normed_convolution_le hg_cont.aestronglyMeasurable ?_
      intro y hy
      have hyT : y ∈ T := by
        have hyS :
            y ∈ Metric.cthickening 1 S := by
          refine Metric.mem_cthickening_of_dist_le (x := y) (y := x) (δ := 1) S hx ?_
          exact le_trans hy.le hrOut_le_one
        have hyT' : y ∈ Metric.cthickening 1 (Metric.cthickening 1 (tsupport g)) := by
          simpa [S] using hyS
        have hyT'' : y ∈ Metric.cthickening (1 + 1) (tsupport g) := by
          simpa [S, cthickening_cthickening (show (0 : ℝ) ≤ 1 by positivity)
            (show (0 : ℝ) ≤ 1 by positivity) (tsupport g)] using hyT'
        simpa [T] using hyT''
      exact (hδ0 y hyT x hxT (lt_of_lt_of_le hy (le_trans hn.le (min_le_left _ _)))).le
    · have hconvx :
          (((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) = 0 := by
        exact zero_outside_of_tsupport_subset
          (Ω := S)
          ((tsupport_normed_convolution_subset_cthickening (d := d) (shrinkingBump (d := d) n) hg_comp).trans
            (by simpa [S] using cthickening_mono hrOut_le_one (tsupport g)))
          hx
      have hgx : g x = 0 := zero_outside_of_tsupport_subset (Ω := S)
        (show tsupport g ⊆ S by
          intro y hy
          exact Metric.mem_cthickening_of_dist_le (x := y) (y := y) (δ := 1)
            (tsupport g) hy (by simp))
        hx
      simp [hconvx, hgx, hε0_pos.le]
  have hbound :
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ε0 * M := by
    refine eLpNorm_sub_le_of_dist_bdd
      (μ := volume) (p := ENNReal.ofReal p) (s := S) (hp := by simp)
      hS_meas hε0_pos.le hdist ?_ ?_
    · intro x hx
      exact hconv_support_sub hx
    · exact hg_support_sub
  have hfinal :
      ENNReal.ofReal ε0 * M < ε := by
    have hM_eq : M = ENNReal.ofReal (M.toReal) := by
      exact (ENNReal.ofReal_toReal hM_top).symm
    have hlt_real : ε0 * M.toReal < εr := by
      dsimp [ε0, C]
      have hfrac_lt_one : M.toReal / (M.toReal + 1) < 1 := by
        have hM_nonneg : 0 ≤ M.toReal := ENNReal.toReal_nonneg
        have hden_pos : 0 < M.toReal + 1 := by linarith
        have hnum_lt : M.toReal < M.toReal + 1 := by linarith
        exact (div_lt_one hden_pos).2 hnum_lt
      have hmul_lt : εr * (M.toReal / (M.toReal + 1)) < εr := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_lt_mul_of_pos_left hfrac_lt_one hεr_pos)
      have hcalc :
          εr / (M.toReal + 1) * M.toReal = εr * (M.toReal / (M.toReal + 1)) := by
        field_simp [show M.toReal + 1 ≠ 0 by linarith]
      simpa [hcalc] using hmul_lt
    have hlt_ofReal :
        ENNReal.ofReal ε0 * M < ENNReal.ofReal εr := by
      rw [hM_eq, ← ENNReal.ofReal_mul (show 0 ≤ ε0 by positivity),
        ENNReal.ofReal_lt_ofReal_iff hεr_pos]
      exact hlt_real
    simpa [εr, hε_top] using hlt_ofReal
  exact hbound.trans hfinal.le

omit [NeZero d] in
theorem tendsto_eLpNorm_normedConvolution_sub
    {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              f x)
          (ENNReal.ofReal p) volume)
      atTop (nhds 0) := by
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ε hε
  by_cases hε_top : ε = ∞
  · filter_upwards with n
    simp [hε_top]
  let εr : ℝ := ε.toReal
  have hεr_pos : 0 < εr := ENNReal.toReal_pos hε.ne' hε_top
  have hε3_pos : 0 < εr / 3 := by positivity
  obtain ⟨g, hg_comp, hg_smooth, hfg⟩ :=
    hf.exist_eLpNorm_sub_le (by simp) (by
      simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p))
      hε3_pos
  have hg_memLp : MemLp g (ENNReal.ofReal p) volume :=
    hg_smooth.continuous.memLp_of_hasCompactSupport hg_comp
  have hmid :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
                g x)
            (ENNReal.ofReal p) volume)
        atTop (nhds 0) :=
    tendsto_eLpNorm_normedConvolution_sub_of_continuous (d := d) hp hg_smooth.continuous hg_comp
  have hconv_diff :
      ∀ n,
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
          (ENNReal.ofReal p) volume ≤
          eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) volume := by
    intro n
    exact eLpNorm_normedConvolution_sub_le (d := d) (shrinkingBump (d := d) n) hp hf hg_memLp
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hmid (ENNReal.ofReal (εr / 3))
      (ENNReal.ofReal_pos.mpr hε3_pos)] with n hn
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hA_cont :
      Continuous
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (fun y => f y - g y)) x) := by
    exact (shrinkingBump (d := d) n).hasCompactSupport_normed.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (shrinkingBump (d := d) n).continuous_normed ((hf.sub hg_memLp).locallyIntegrable hp_enn)
  have hB_cont :
      Continuous
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) := by
    exact (shrinkingBump (d := d) n).hasCompactSupport_normed.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (shrinkingBump (d := d) n).continuous_normed (hg_memLp.locallyIntegrable hp_enn)
  have hF_cont :
      Continuous
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) := by
    exact (shrinkingBump (d := d) n).hasCompactSupport_normed.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (shrinkingBump (d := d) n).continuous_normed (hf.locallyIntegrable hp_enn)
  have hA_sm :
      AEStronglyMeasurable
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (fun y => f y - g y)) x)
        volume := hA_cont.aestronglyMeasurable
  have hFG_sm :
      AEStronglyMeasurable
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        volume := hF_cont.aestronglyMeasurable.sub hB_cont.aestronglyMeasurable
  have hB_sm :
      AEStronglyMeasurable
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x)
        volume := hB_cont.aestronglyMeasurable.sub hg_memLp.aestronglyMeasurable
  have hC_sm :
      AEStronglyMeasurable (fun x => g x - f x) volume :=
    hg_memLp.aestronglyMeasurable.sub hf.aestronglyMeasurable
  have htri :
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            f x)
        (ENNReal.ofReal p) volume ≤
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        (ENNReal.ofReal p) volume +
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x)
        (ENNReal.ofReal p) volume +
      eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
    have hdecomp :
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            f x) =
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) +
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x) +
        (fun x => g x - f x) := by
      ext x
      simp [sub_eq_add_neg, add_assoc, add_comm]
      ring
    rw [hdecomp]
    calc
      eLpNorm
          ((fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) +
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
                g x) +
            (fun x => g x - f x))
          (ENNReal.ofReal p) volume
          ≤
        eLpNorm
            ((fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
                ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) +
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
                g x))
            (ENNReal.ofReal p) volume +
          eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
          exact eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) hp_enn
      _ ≤
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
          (ENNReal.ofReal p) volume +
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
              g x)
          (ENNReal.ofReal p) volume +
        eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
          gcongr
          exact eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) hp_enn
  have houter :
      eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
          (ENNReal.ofReal p) volume +
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
              g x)
          (ENNReal.ofReal p) volume +
        eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3)) + ENNReal.ofReal (εr / 3) := by
    have hfg' : eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (εr / 3) := by
      simpa [sub_eq_add_neg, add_comm] using! hfg
    have hgf' : eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (εr / 3) := by
      have hEq :
          eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) volume =
            eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
        simpa [sub_eq_add_neg] using!
          (eLpNorm_sub_comm (fun x => f x) (fun x => g x) (ENNReal.ofReal p) volume)
      rw [← hEq]
      exact hfg'
    have hfirst_le :
        eLpNorm
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
                ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (εr / 3) := (hconv_diff n).trans hfg'
    calc
      eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
          (ENNReal.ofReal p) volume +
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
              g x)
          (ENNReal.ofReal p) volume +
        eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume
          ≤
        ENNReal.ofReal (εr / 3) +
          eLpNorm
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
                g x)
            (ENNReal.ofReal p) volume +
          eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
            gcongr
      _ ≤ ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3) +
            eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
            gcongr
      _ ≤ ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3) +
            ENNReal.ofReal (εr / 3) := by
            gcongr
      _ = (ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3)) +
            ENNReal.ofReal (εr / 3) := by ac_rfl
  calc
    eLpNorm
      (fun x =>
        ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
          f x)
      (ENNReal.ofReal p) volume
        ≤
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        (ENNReal.ofReal p) volume +
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x)
        (ENNReal.ofReal p) volume +
      eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := htri
    _ ≤ (ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3)) + ENNReal.ofReal (εr / 3) := houter
    _ ≤ ε := by
        have hsum : (εr / 3 + εr / 3) + εr / 3 = εr := by ring
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ εr / 3) (by positivity : 0 ≤ εr / 3),
          ← ENNReal.ofReal_add (by positivity : 0 ≤ εr / 3 + εr / 3) (by positivity : 0 ≤ εr / 3)]
        simp [hsum, εr, hε_top]

theorem MemW1pWitness.ae_eq
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ}
    (hw₁ hw₂ : MemW1pWitness 2 f Ω) :
    hw₁.weakGrad =ᵐ[volume.restrict Ω] hw₂.weakGrad := by
  let _ := (inferInstance : NeZero d)
  have hp2 : (1 : ENNReal) ≤ 2 := by
    norm_num
  have hcomp :
      ∀ i : Fin d,
        (fun x => hw₁.weakGrad x i) =ᵐ[volume.restrict Ω] (fun x => hw₂.weakGrad x i) := by
    intro i
    exact HasWeakPartialDeriv.ae_eq hΩ (hw₁.isWeakGrad i) (hw₂.isWeakGrad i)
      ((hw₁.weakGrad_component_memLp i).locallyIntegrable hp2)
      ((hw₂.weakGrad_component_memLp i).locallyIntegrable hp2)
  filter_upwards [ae_all_iff.2 hcomp] with x hx
  ext i
  exact hx i

omit [NeZero d] in
theorem convolution_fderiv_eq_convolution_weakPartial_univ
    {u g φ : E → ℝ} {i : Fin d}
    (hweak : HasWeakPartialDeriv i g u Set.univ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) :
    ∀ x,
      ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
        (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  intro x
  let T : Homeomorph E E := (Homeomorph.neg E).trans (Homeomorph.addLeft x)
  let ψ : E → ℝ := φ ∘ T
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
      hφ_smooth.comp (contDiff_const.add contDiff_id.neg)
  have hψ_compact : HasCompactSupport ψ := by
    simpa [ψ, T, Function.comp] using hφ_compact.comp_homeomorph T
  have key := hweak ψ hψ_smooth hψ_compact (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hderiv :
      ∀ t,
        (fderiv ℝ ψ t) (EuclideanSpace.single i 1) =
          - (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) := by
    intro t
    have hfd :
        HasFDerivAt ψ
          (((fderiv ℝ φ (x + -t)).comp ((0 : E →L[ℝ] E) - 1)) : E →L[ℝ] ℝ) t := by
      simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
        ((hφ_smooth.differentiable
            (show (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 by simp) (x + -t)).hasFDerivAt.comp t
          ((hasFDerivAt_const x t).add (hasFDerivAt_id t).neg))
    calc
      (fderiv ℝ ψ t) (EuclideanSpace.single i 1)
        = (((fderiv ℝ φ (x + -t)).comp ((0 : E →L[ℝ] E) - 1))
            (EuclideanSpace.single i 1)) := by
              rw [hfd.fderiv]
      _ = (fderiv ℝ φ (x + -t))
            (((0 : E →L[ℝ] E) - 1) (EuclideanSpace.single i 1)) := by
              rfl
      _ = (fderiv ℝ φ (x + -t)) (- EuclideanSpace.single i 1) := by
            simp
      _ = - (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) := by
            simp
  have hkey :
      ∫ t, g t * ψ t ∂volume =
        ∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
    have hkey' :
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume =
          -∫ t, g t * ψ t ∂volume := by
      simpa [Measure.restrict_univ] using key
    have hderiv_int :
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume =
          -∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
      calc
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume
          = ∫ t, -(u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1)) ∂volume := by
              refine integral_congr_ae ?_
              filter_upwards with t
              rw [hderiv t]
              ring
        _ = -∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
              rw [integral_neg]
    linarith
  calc
      ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x
      = ∫ t, u t * (fderiv ℝ φ (x - t)) (EuclideanSpace.single i 1) ∂volume := by
          simpa [smul_eq_mul, mul_comm] using
            (MeasureTheory.convolution_lsmul_swap
              (f := fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1)) (g := u) (x := x)
              (μ := volume))
    _ = ∫ t, g t * ψ t ∂volume := hkey.symm
    _ = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
          simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            smul_eq_mul, mul_comm] using
            (MeasureTheory.convolution_lsmul_swap (f := φ) (g := g) (x := x) (μ := volume)).symm

theorem exists_smooth_compactSupport_W1p_approx_univ
    {p : ℝ} (hp : 1 < p)
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u Set.univ)
    (hu_compact : HasCompactSupport u) :
    ∃ φ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n,
        tsupport (φ n) ⊆
          Metric.cthickening (shrinkingBump (d := d) n).rOut (tsupport u)) ∧
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - u x) (ENNReal.ofReal p) volume)
        atTop (nhds 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0)) := by
  let _ := (inferInstance : NeZero d)
  have hp_le : 1 ≤ p := le_of_lt hp
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_le : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hu_memLp : MemLp u (ENNReal.ofReal p) volume := by
    simpa [Measure.restrict_univ] using hw.memLp
  let φ : ℕ → E → ℝ := fun n =>
    ((shrinkingBump (d := d) n).normed volume
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (shrinkingBump (d := d) n).hasCompactSupport_normed.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((shrinkingBump (d := d) n).contDiff_normed)
      (hu_memLp.locallyIntegrable hp_enn)
  · intro n
    apply HasCompactSupport.intro'
      (K := Metric.cthickening (shrinkingBump (d := d) n).rOut (tsupport u))
      (hu_compact.isCompact.cthickening (r := (shrinkingBump (d := d) n).rOut))
      (hu_compact.isCompact.cthickening (r := (shrinkingBump (d := d) n).rOut)).isClosed
    intro x hx
    exact zero_outside_of_tsupport_subset
      (Ω := Metric.cthickening (shrinkingBump (d := d) n).rOut (tsupport u))
      (tsupport_normed_convolution_subset_cthickening
        (d := d) (shrinkingBump (d := d) n) hu_compact)
      hx
  · intro n
    exact tsupport_normed_convolution_subset_cthickening
      (d := d) (shrinkingBump (d := d) n) hu_compact
  · simpa [φ] using
      tendsto_eLpNorm_normedConvolution_sub (d := d) hp_le hu_memLp
  · intro i
    have hGi_memLp : MemLp (fun y => hw.weakGrad y i) (ENNReal.ofReal p) volume := by
      simpa [Measure.restrict_univ] using hw.weakGrad_component_memLp i
    have hEq :
        (fun n =>
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            (ENNReal.ofReal p) volume) =
          fun n =>
            eLpNorm
              (fun x =>
                ((shrinkingBump (d := d) n).normed volume
                  ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => hw.weakGrad y i)) x -
                  hw.weakGrad x i)
              (ENNReal.ofReal p) volume := by
      funext n
      refine eLpNorm_congr_ae ?_
      filter_upwards with x
      let bump : E → ℝ := (shrinkingBump (d := d) n).normed volume
      let Dbump : E → E →L[ℝ] ℝ := fderiv ℝ bump
      let ei : E := EuclideanSpace.single i 1
      have hbump1 : ContDiff ℝ 1 bump := by
        simpa [bump] using
          ((shrinkingBump (d := d) n).contDiff_normed : ContDiff ℝ 1 ((shrinkingBump (d := d) n).normed volume))
      have hfd :=
        (shrinkingBump (d := d) n).hasCompactSupport_normed.hasFDerivAt_convolution_left
          (L := ContinuousLinearMap.lsmul ℝ ℝ)
          hbump1
          (hu_memLp.locallyIntegrable hp_enn) x
      have hDbump_cont : Continuous Dbump := by
        simpa [Dbump, bump] using hbump1.continuous_fderiv one_ne_zero
      have hDbump_compact : HasCompactSupport Dbump := by
        simpa [Dbump, bump] using ((shrinkingBump (d := d) n).hasCompactSupport_normed.fderiv (𝕜 := ℝ))
      have hfd' :
          (fderiv ℝ (φ n) x) ei =
            (((Dbump ⋆[
                ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x)
                ei) := by
        simpa [φ, bump, Dbump, ei] using
          congrArg (fun A : E →L[ℝ] ℝ => A ei) hfd.fderiv
      have hconv_apply :
          (((Dbump ⋆[
              ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei) =
            (((fun y => (fderiv ℝ bump y) ei)
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) := by
        calc
          (((Dbump ⋆[
              ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei)
              =
            ((u ⋆[
              ContinuousLinearMap.precompR E (ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] Dbump) x) ei := by
                simpa [ContinuousLinearMap.precompL, Dbump] using
                  congrArg (fun F => F x ei)
                    (MeasureTheory.convolution_flip
                      (L := ContinuousLinearMap.precompR E (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                      (μ := volume) (f := u) (g := Dbump))
          _ = (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (fun y => Dbump y ei)) x := by
                simpa [Dbump, bump] using
                  (MeasureTheory.convolution_precompR_apply
                    (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                    (μ := volume) (f := u) (g := Dbump)
                    (hf := hu_memLp.locallyIntegrable hp_enn)
                    (hcg := hDbump_compact) (hg := hDbump_cont) (x₀ := x) (x := ei))
          _ = (((fun y => Dbump y ei) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) := by
                simpa [smul_eq_mul, mul_comm] using
                  congrArg (fun F => F x)
                    ((MeasureTheory.convolution_flip
                      (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                      (μ := volume) (f := u) (g := fun y => Dbump y ei)).symm)
      calc
        (fderiv ℝ (φ n) x) ei - hw.weakGrad x i
          = (((Dbump ⋆[
                ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x)
                ei) - hw.weakGrad x i := by
                  rw [hfd']
        _ = (((fun y =>
              (fderiv ℝ bump y) ei)
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) - hw.weakGrad x i := by
                  rw [hconv_apply]
        _ = ((bump)
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => hw.weakGrad y i)) x -
                hw.weakGrad x i := by
                  simpa [ei] using
                    congrArg (fun z => z - hw.weakGrad x i)
                      (convolution_fderiv_eq_convolution_weakPartial_univ
                        (d := d) (i := i) (u := u) (g := fun y => hw.weakGrad y i)
                        (φ := bump)
                        (hw.isWeakGrad i)
                        (by
                          simpa [bump] using
                            ((shrinkingBump (d := d) n).contDiff_normed :
                              ContDiff ℝ (⊤ : ℕ∞) ((shrinkingBump (d := d) n).normed volume)))
                        ((shrinkingBump (d := d) n).hasCompactSupport_normed) x)
    exact hEq ▸ tendsto_eLpNorm_normedConvolution_sub (d := d) hp_le hGi_memLp

omit [NeZero d] in
lemma fderiv_apply_eq_zero_of_eq_one_on_cthickening
    {K : Set E} {δ : ℝ} (hδ : 0 < δ)
    {η : E → ℝ}
    (hη_one : ∀ x ∈ Metric.cthickening δ K, η x = 1)
    {x : E} (hx : x ∈ K) (i : Fin d) :
    (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
  have hη_eq : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : 0 < δ / 2)) ?_
    intro y hy
    rw [Metric.mem_ball] at hy
    have hy_closed : y ∈ Metric.closedBall x (δ / 2) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt hy
    have hy_cthick_half : y ∈ Metric.cthickening (δ / 2) K :=
      Metric.closedBall_subset_cthickening hx (δ / 2) hy_closed
    have hy_cthick : y ∈ Metric.cthickening δ K :=
      Metric.cthickening_mono (by linarith : δ / 2 ≤ δ) K hy_cthick_half
    exact hη_one y hy_cthick
  rw [Filter.EventuallyEq.fderiv_eq hη_eq]
  simp

omit [NeZero d] in
theorem tsupport_mul_smooth_bounded_p_weakGrad_component_subset
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u η : E → ℝ} (hw : MemW1pWitness p u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (i : Fin d) :
    tsupport
        (fun x =>
          (MemW1pWitness.mul_smooth_bounded_p
            (d := d) (p := p) hp hΩ hw hη hC₀ hC₁ hη_bound hη_grad_bound).weakGrad x i) ⊆
      tsupport η := by
  have hfirst :
      tsupport (fun x => η x * hw.weakGrad x i) ⊆ tsupport η :=
    tsupport_mul_subset_left
  have hsecond :
      tsupport (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) ⊆ tsupport η :=
    (tsupport_mul_subset_left :
      tsupport (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) ⊆
        tsupport (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1))).trans <|
      (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans subset_rfl
  simpa [MemW1pWitness.mul_smooth_bounded_p, PiLp.toLp_apply, smul_eq_mul] using
    (tsupport_add
      (fun x => η x * hw.weakGrad x i)
      (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)).trans
      (union_subset hfirst hsecond)

theorem exists_smooth_W1p_approx_of_supportedWitness
    {Ω K : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p)
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u Ω)
    (hK_compact : IsCompact K) (hKΩ : K ⊆ Ω)
    (hu_sub : tsupport u ⊆ K)
    (hgrad_sub : ∀ i : Fin d, tsupport (fun x => hw.weakGrad x i) ⊆ K) :
    ∃ φ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ Ω) ∧
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - u x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω))
          atTop (nhds 0)) := by
  have hp_le : 1 ≤ p := le_of_lt hp
  have hK_compact_u : HasCompactSupport u := by
    apply HasCompactSupport.intro' (K := K) hK_compact hK_compact.isClosed
    intro x hx
    exact zero_outside_of_tsupport_subset (Ω := K) hu_sub hx
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hK_compact.exists_cthickening_subset_open hΩ hKΩ
  let K' : Set E := Metric.cthickening δ K
  have hK'_compact : IsCompact K' := hK_compact.cthickening (r := δ)
  have hK'_Ω : K' ⊆ Ω := hδΩ
  obtain ⟨χ, hχ_smooth, hχ_compact, _hχ_range, hχ_one, hχ_sub⟩ :=
    exists_smooth_cutoff (d := d) hK'_compact hΩ hK'_Ω
  have hu_memLp_univ : MemLp u (ENNReal.ofReal p) volume := by
    have hu_eq_ind : Ω.indicator u = u := by
      ext x
      by_cases hx : x ∈ Ω
      · simp [hx]
      · simp [hx, zero_outside_of_tsupport_subset (Ω := Ω) (hu_sub.trans hKΩ) hx]
    rw [← hu_eq_ind]
    exact (MeasureTheory.memLp_indicator_iff_restrict
      (μ := volume) (s := Ω) (f := u) (p := ENNReal.ofReal p) hΩ.measurableSet).2 hw.memLp
  have hgrad_memLp_univ :
      ∀ i : Fin d, MemLp (fun x => hw.weakGrad x i) (ENNReal.ofReal p) volume := by
    intro i
    have hgi_eq_ind : Ω.indicator (fun x => hw.weakGrad x i) = fun x => hw.weakGrad x i := by
      ext x
      by_cases hx : x ∈ Ω
      · simp [hx]
      · simp [hx, zero_outside_of_tsupport_subset (Ω := Ω) (hgrad_sub i |>.trans hKΩ) hx]
    rw [← hgi_eq_ind]
    exact (MeasureTheory.memLp_indicator_iff_restrict
      (μ := volume) (s := Ω) (f := fun x => hw.weakGrad x i) (p := ENNReal.ofReal p)
      hΩ.measurableSet).2 (hw.weakGrad_component_memLp i)
  let hwUniv : MemW1pWitness (ENNReal.ofReal p) u Set.univ := by
    refine
      { memLp := by simpa [Measure.restrict_univ] using hu_memLp_univ
        weakGrad := hw.weakGrad
        weakGrad_component_memLp := by
          intro i
          simpa [Measure.restrict_univ] using hgrad_memLp_univ i
        isWeakGrad := ?_ }
    ·
      intro i φ hφ_smooth hφ_compact _hφ_sub
      let ψ : E → ℝ := fun x => χ x * φ x
      have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hχ_smooth.mul hφ_smooth
      have hψ_compact : HasCompactSupport ψ := by
        simpa [ψ] using! hχ_compact.mul_right (f' := φ)
      have hψ_sub : tsupport ψ ⊆ Ω := (tsupport_smul_subset_left χ φ).trans hχ_sub
      have key := hw.isWeakGrad i ψ hψ_smooth hψ_compact hψ_sub
      let ei : E := EuclideanSpace.single i 1
      have hχ_deriv_zero :
          ∀ x ∈ K, (fderiv ℝ χ x) ei = 0 := by
        intro x hx
        exact fderiv_apply_eq_zero_of_eq_one_on_cthickening
          (d := d) hδ_pos hχ_one hx i
      have hleft_pt :
          ∀ x,
            u x * (fderiv ℝ ψ x) ei =
              u x * (fderiv ℝ φ x) ei := by
        intro x
        by_cases hx : x ∈ K
        · have hχx : χ x = 1 := hχ_one x (Metric.self_subset_cthickening K hx)
          have hdχx : (fderiv ℝ χ x) ei = 0 := hχ_deriv_zero x hx
          have hχ_diff : Differentiable ℝ χ := hχ_smooth.differentiable (by simp)
          have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
          rw [fderiv_fun_mul hχ_diff.differentiableAt hφ_diff.differentiableAt]
          simp [ei, smul_eq_mul, hχx, hdχx]
        · have hux : u x = 0 := zero_outside_of_tsupport_subset (Ω := K) hu_sub hx
          simp [hux]
      have hright_pt :
          ∀ x,
            hw.weakGrad x i * ψ x =
              hw.weakGrad x i * φ x := by
        intro x
        by_cases hx : x ∈ K
        · have hχx : χ x = 1 := hχ_one x (Metric.self_subset_cthickening K hx)
          simp [ψ, hχx]
        · have hgx : hw.weakGrad x i = 0 :=
            zero_outside_of_tsupport_subset (Ω := K) (hgrad_sub i) hx
          simp [ψ, hgx]
      have hψ_deriv_sub : tsupport (fun x => (fderiv ℝ ψ x) ei) ⊆ Ω :=
        (tsupport_fderiv_apply_subset ℝ ei).trans hψ_sub
      have hleft_zero : ∀ x, x ∉ Ω → u x * (fderiv ℝ ψ x) ei = 0 := by
        intro x hx
        have hderivx : (fderiv ℝ ψ x) ei = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y => (fderiv ℝ ψ y) ei) (fun h => hx (hψ_deriv_sub h))
        simp [hderivx]
      have hright_zero : ∀ x, x ∉ Ω → hw.weakGrad x i * ψ x = 0 := by
        intro x hx
        have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψ_sub h))
        simp [hψx]
      have key_global :
          ∫ x, u x * (fderiv ℝ ψ x) ei ∂volume =
            -∫ x, hw.weakGrad x i * ψ x ∂volume := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero,
          ← setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero]
        simpa [Measure.restrict_univ] using key
      have hleft_global :
          ∫ x, u x * (fderiv ℝ ψ x) ei ∂volume =
            ∫ x, u x * (fderiv ℝ φ x) ei ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact hleft_pt x
      have hright_global :
          ∫ x, hw.weakGrad x i * ψ x ∂volume =
            ∫ x, hw.weakGrad x i * φ x ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact hright_pt x
      rw [hleft_global, hright_global] at key_global
      simpa [Measure.restrict_univ] using key_global
  rcases exists_smooth_compactSupport_W1p_approx_univ (d := d) hp hwUniv hK_compact_u with
    ⟨φ, hφ_smooth, hφ_compact, hφ_sup, hφ_fun, hφ_grad⟩
  have hsmall_lt :
      ∀ᶠ n in atTop, (shrinkingBump (d := d) n).rOut < δ := by
    exact (tendsto_order.1 (tendsto_shrinkingBump_rOut (d := d))).2 _ hδ_pos
  have hsmall :
      ∀ᶠ n in atTop, (shrinkingBump (d := d) n).rOut ≤ δ := by
    exact hsmall_lt.mono fun _ hn => hn.le
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  let ψ : ℕ → E → ℝ := fun n => φ (n + N)
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hφ_smooth (n + N)
  · intro n
    exact hφ_compact (n + N)
  · intro n
    have hle : (shrinkingBump (d := d) (n + N)).rOut ≤ δ := hN (n + N) (Nat.le_add_left _ _)
    exact (hφ_sup (n + N)).trans <|
      (Metric.cthickening_subset_of_subset (shrinkingBump (d := d) (n + N)).rOut hu_sub).trans <|
        (Metric.cthickening_mono hle K).trans hδΩ
  ·
    have hψ_fun_global :
        Tendsto
          (fun n => eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) volume)
          atTop (nhds 0) := by
      simpa [ψ] using! hφ_fun.comp (tendsto_add_atTop_nat N)
    have hψ_fun_nonneg :
        ∀ n,
          (0 : ℝ≥0∞) ≤ eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) (volume.restrict Ω) :=
      fun _ => zero_le
    have hψ_fun_bound :
        ∀ n,
          eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) (volume.restrict Ω) ≤
            eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) volume :=
      fun n =>
        eLpNorm_mono_measure (f := fun x => ψ n x - u x) Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hψ_fun_global hψ_fun_nonneg hψ_fun_bound
  · intro i
    have hψ_grad_global :
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0) := by
      simpa [ψ] using! (hφ_grad i).comp (tendsto_add_atTop_nat N)
    have hψ_grad_nonneg :
        ∀ n,
          (0 : ℝ≥0∞) ≤
            eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω) :=
      fun _ => zero_le
    have hψ_grad_bound :
        ∀ n,
          eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω) ≤
            eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) volume :=
      fun n =>
        eLpNorm_mono_measure
          (f := fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hψ_grad_global hψ_grad_nonneg hψ_grad_bound

theorem memW01p_of_memW1p_of_tsupport_subset
    {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hu : MemW1p (ENNReal.ofReal p) u Ω)
    (hu_compact : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ Ω) :
    MemW01p (ENNReal.ofReal p) u Ω := by
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal (le_of_lt hp) : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  rcases hu with ⟨hu_memLp, hu_grad⟩
  choose g hg_memLp hg_weak using hu_grad
  let G : E → E := fun x => WithLp.toLp 2 fun i => g i x
  let hw : MemW1pWitness (ENNReal.ofReal p) u Ω :=
    { memLp := hu_memLp
      weakGrad := G
      weakGrad_component_memLp := hg_memLp
      isWeakGrad := hg_weak }
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hu_compact.isCompact.exists_cthickening_subset_open hΩ hu_sub
  let K : Set E := Metric.cthickening δ (tsupport u)
  have hK_compact : IsCompact K := hu_compact.isCompact.cthickening (r := δ)
  have hKΩ : K ⊆ Ω := hδΩ
  obtain ⟨η, hη_smooth, hη_compact, hη_range, hη_one, hη_sub⟩ :=
    exists_smooth_cutoff (d := d) hK_compact hΩ hKΩ
  have hη_bound : ∀ x, |η x| ≤ 1 := by
    intro x
    rcases hη_range ⟨x, rfl⟩ with ⟨hx0, hx1⟩
    rw [abs_of_nonneg hx0]
    exact hx1
  have hη_fderiv_compact : HasCompactSupport (fderiv ℝ η) := hη_compact.fderiv (𝕜 := ℝ)
  obtain ⟨Cη, hCη⟩ := hη_fderiv_compact.isCompact.exists_bound_of_continuousOn
    ((hη_smooth.continuous_fderiv (by simp)).continuousOn)
  let C₁ : ℝ := max Cη 0
  have hC₁_nonneg : 0 ≤ C₁ := le_max_right _ _
  have hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁ := by
    intro x
    by_cases hx : x ∈ tsupport (fderiv ℝ η)
    · exact (hCη x hx).trans (le_max_left _ _)
    · have hzero : fderiv ℝ η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [C₁, hzero]
  let v : E → ℝ := fun x => η x * u x
  let hwCut :=
    MemW1pWitness.mul_smooth_bounded_p
      (d := d) (p := ENNReal.ofReal p) hp_enn hΩ hw hη_smooth
      zero_le_one hC₁_nonneg hη_bound hη_grad_bound
  have hv_eq_u : v = u := by
    funext x
    by_cases hx : x ∈ tsupport u
    · have hηx : η x = 1 := hη_one x (Metric.self_subset_cthickening (tsupport u) hx)
      simp [v, hηx]
    · have hux : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [v, hux]
  have hv_sub : tsupport v ⊆ tsupport η := tsupport_smul_subset_left η u
  have hgrad_sub :
      ∀ i : Fin d, tsupport (fun x => hwCut.weakGrad x i) ⊆ tsupport η := by
    intro i
    exact tsupport_mul_smooth_bounded_p_weakGrad_component_subset
      (d := d) (p := ENNReal.ofReal p) hp_enn hΩ hw hη_smooth zero_le_one hC₁_nonneg hη_bound
      hη_grad_bound i
  rcases exists_smooth_W1p_approx_of_supportedWitness
      (d := d) (Ω := Ω) (K := tsupport η) hΩ hp hwCut
      hη_compact.isCompact hη_sub hv_sub hgrad_sub with
    ⟨φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩
  simpa [v, hv_eq_u] using
    memW01p_of_global_approx_supported hwCut φ hφ_smooth hφ_compact hφ_sub hφ_fun hφ_grad

end DeGiorgi

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveSobolevApproximation
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit positive mollification of a compactly supported planar
Sobolev function. The values and weak derivatives converge in L². -/

open Set Filter MeasureTheory
open scoped ENNReal Topology Convolution

noncomputable section

namespace CircleDomainRigidity

def planarMollification (u : EuclideanPlane → ℝ) (n : ℕ) : EuclideanPlane → ℝ :=
  ((DeGiorgi.shrinkingBump (d := 2) n).normed volume
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)

theorem planarMollification_smooth {u : EuclideanPlane → ℝ}
    (hu : LocallyIntegrable u volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (planarMollification u n) :=
  (DeGiorgi.shrinkingBump (d := 2) n).hasCompactSupport_normed.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (DeGiorgi.shrinkingBump (d := 2) n).contDiff_normed hu

theorem planarMollification_hasCompactSupport {u : EuclideanPlane → ℝ}
    (hu : HasCompactSupport u) (n : ℕ) : HasCompactSupport (planarMollification u n) := by
  exact (DeGiorgi.shrinkingBump (d := 2) n).hasCompactSupport_normed.convolution
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hu

theorem tendsto_planarMollifier_radius :
    Tendsto (fun n => (DeGiorgi.shrinkingBump (d := 2) n).rOut) atTop (𝓝 0) := by
  simpa only [DeGiorgi.shrinkingBump, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem planarMollification_derivative_of_weak {u g : EuclideanPlane → ℝ}
    (hu : LocallyIntegrable u volume) (i : Fin 2)
    (hweak : DeGiorgi.HasWeakPartialDeriv i g u univ) (n : ℕ) (x : EuclideanPlane) :
    (fderiv ℝ (planarMollification u n) x) (EuclideanSpace.single i 1) =
      ((DeGiorgi.shrinkingBump (d := 2) n).normed volume
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  let bump : EuclideanPlane → ℝ := (DeGiorgi.shrinkingBump (d := 2) n).normed volume
  let Dbump : EuclideanPlane → EuclideanPlane →L[ℝ] ℝ := fderiv ℝ bump
  let ei : EuclideanPlane := EuclideanSpace.single i 1
  have hb : ContDiff ℝ 1 bump := (DeGiorgi.shrinkingBump (d := 2) n).contDiff_normed
  have hs : HasCompactSupport bump := (DeGiorgi.shrinkingBump (d := 2) n).hasCompactSupport_normed
  have hd := hs.hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hb hu x
  have hd' : (fderiv ℝ (planarMollification u n) x) ei =
      ((Dbump ⋆[ContinuousLinearMap.precompL EuclideanPlane
        (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei := by
    simpa only [planarMollification, bump, Dbump] using
      congrArg (fun A : EuclideanPlane →L[ℝ] ℝ => A ei) hd.fderiv
  have hconv :
      ((Dbump ⋆[ContinuousLinearMap.precompL EuclideanPlane
        (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei =
      ((fun y => (fderiv ℝ bump y) ei) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := by
    calc
      _ = ((u ⋆[ContinuousLinearMap.precompR EuclideanPlane
          (ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] Dbump) x) ei := by
        simpa [ContinuousLinearMap.precompL, Dbump] using
          congrArg (fun F => F x ei) (MeasureTheory.convolution_flip
            (L := ContinuousLinearMap.precompR EuclideanPlane (ContinuousLinearMap.lsmul ℝ ℝ).flip)
            (μ := volume) (f := u) (g := Dbump))
      _ = (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (fun y => Dbump y ei)) x := by
        exact MeasureTheory.convolution_precompR_apply
          (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (μ := volume)
          (f := u) (g := Dbump) hu (hs.fderiv (𝕜 := ℝ))
          (hb.continuous_fderiv one_ne_zero) x ei
      _ = _ := by
        simpa [Dbump] using congrArg (fun F => F x)
          ((MeasureTheory.convolution_flip (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
            (μ := volume) (f := u) (g := fun y => Dbump y ei)).symm)
  exact hd'.trans (hconv.trans
    (DeGiorgi.convolution_fderiv_eq_convolution_weakPartial_univ hweak
      (DeGiorgi.shrinkingBump (d := 2) n).contDiff_normed hs x))


theorem planarMollification_derivative {u : EuclideanPlane → ℝ}
    (hw : DeGiorgi.MemW1pWitness 2 u univ) (n : ℕ) (i : Fin 2) (x : EuclideanPlane) :
    (fderiv ℝ (planarMollification u n) x) (EuclideanSpace.single i 1) =
      ((DeGiorgi.shrinkingBump (d := 2) n).normed volume
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => hw.weakGrad y i)) x := by
  have hm : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  exact planarMollification_derivative_of_weak (hm.locallyIntegrable (by norm_num))
    i (hw.isWeakGrad i) n x

theorem planarMollification_tendsto_L2 {u : EuclideanPlane → ℝ}
    (hu : MemLp u 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => planarMollification u n x - u x) 2 volume)
      atTop (𝓝 0) := by
  have hu' : MemLp u (ENNReal.ofReal (2 : ℝ)) volume := by simpa using hu
  simpa only [planarMollification, ENNReal.ofReal_ofNat] using
    DeGiorgi.tendsto_eLpNorm_normedConvolution_sub (d := 2) (p := 2) (by norm_num) hu'

theorem planarMollification_tendsto_gradient_L2 {u : EuclideanPlane → ℝ}
    (hw : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (planarMollification u n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
      2 volume) atTop (𝓝 0) := by
  have hgi : MemLp (fun x => hw.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hw.weakGrad_component_memLp i
  have h := planarMollification_tendsto_L2 hgi
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  apply eLpNorm_congr_ae
  exact Eventually.of_forall fun x => congrArg (fun z => z - hw.weakGrad x i)
    (planarMollification_derivative hw n i x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MollificationEnergy
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong mollification converges in Dirichlet energy on every measurable
source region. The limiting energy is that of the original weak field. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem planarMollification_partial_memLp
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u) (n : ℕ) (i : Fin 2) :
    MemLp (fun x => fderiv ℝ (planarMollification u n) x (EuclideanSpace.single i 1))
      2 volume := by
  have hL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  exact ((planarMollification_smooth (hL.locallyIntegrable (by norm_num)) n).continuous_fderiv
    (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
      ((planarMollification_hasCompactSupport hs n).fderiv_apply (𝕜 := ℝ) _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BasePathCodes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base-code space from the positive-law construction. The defining
relations are the actual path-hit and level incidences, with physical length,
finite deletions, optional tags, endpoint conditions and collar gates. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable (X Y : Type*) [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

structure PathCodeData where
  physicalDomain : Set Y
  quotientDomain : Set X
  domainEquiv : physicalDomain ≃ₜ quotientDomain
  basePoint : Y
  dust : Set X
  levels : ℕ → Set (UnitAddCircle × X)
  priorLaws : ℕ → Measure C(PathTime, X)
  priorDeletions : ℕ → ℕ → Finset X
  flagDeletions : ℕ → Finset X
  levelWeights : ℕ → X → ℝ≥0∞
  anchor : Set X
  target : X
  gateContours : ℕ → Set X
  gateSets : ℕ → Set X

variable {X Y}

def priorHitMass (μ : Measure C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  μ {η | (η, x) ∈ pathHitSet}

def AllowedTaggedPath (d : PathCodeData X Y) (dustMeasure : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) : Prop :=
  physicalDomainLength d.domainEquiv d.basePoint Γ.1 < ∞ ∧
  TagRules d.levels N Γ ∧
  ResidualConstraintFamily d.dust (fun _ => pathHitSet) d.priorDeletions d.priorLaws
    (fun i => priorHitMass (d.priorLaws i)) Γ ∧
  ResidualConstraintFamily d.dust d.levels (fun _ => d.flagDeletions)
    (fun _ => volume) d.levelWeights Γ ∧
  dustMeasure (residualImage d.dust Γ) = 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagDelay
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving the same tags to later slots preserves the actual residual times
and all admissibility rules. The tuple measure decreases geometrically. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

def inactiveTag : TagSlot := Sum.inl ()

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalPlaneCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite physical chart in the Euclidean coordinates used for smoothing. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

def complexPlaneCoordinates : EuclideanPlane ≃L[ℝ] ℂ :=
  euclideanPlaneCoordinates.trans Complex.equivRealProdCLM.symm

@[simp] theorem complexPlaneCoordinates_apply (x : EuclideanPlane) :
    complexPlaneCoordinates x = (⟨x 0, x 1⟩ : ℂ) := rfl

def planeSphere (x : EuclideanPlane) : Sphere := (complexPlaneCoordinates x : Sphere)

theorem continuous_planeSphere : Continuous planeSphere :=
  OnePoint.continuous_coe.comp complexPlaneCoordinates.continuous

def physicalPlaneDomain (G : Set Sphere) : Set EuclideanPlane := planeSphere ⁻¹' G

theorem isOpen_physicalPlaneDomain {G : Set Sphere} (hG : IsOpen G) :
    IsOpen (physicalPlaneDomain G) := hG.preimage continuous_planeSphere

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexSobolevTransport
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two physical complex-coordinate derivative identities give the
Euclidean-plane weak derivatives, with the same area measure. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

@[simp] theorem complexPlaneCoordinates_zero :
    complexPlaneCoordinates (EuclideanSpace.single 0 1) = 1 := by
  simp only [complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply,
    euclideanPlaneCoordinates_single_zero]
  apply Complex.ext <;> rfl

@[simp] theorem complexPlaneCoordinates_one :
    complexPlaneCoordinates (EuclideanSpace.single 1 1) = Complex.I := by
  simp only [complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply,
    euclideanPlaneCoordinates_single_one]
  apply Complex.ext <;> rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalRoundIntegrals
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of round-disk integrals and smooth partial derivatives
between the physical Euclidean plane and the complex plane. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complexPlaneCoordinates_norm (x : EuclideanPlane) :
    ‖complexPlaneCoordinates x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.real_norm_sq_eq]
  simp only [complexPlaneCoordinates_apply, Fin.sum_univ_two]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevRepresentative
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Changing an almost-everywhere representative preserves the actual weak
partial derivatives. These bridges do not require pointwise regularity. -/
open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
 theorem HasWeakPartialDeriv.congr_ae {i : Fin d} {f f' g g' : E → ℝ} {U : Set E}
    (h : HasWeakPartialDeriv i g f U)
    (hf : f =ᵐ[volume.restrict U] f') (hg : g =ᵐ[volume.restrict U] g') :
    HasWeakPartialDeriv i g' f' U := by
  intro φ hφ hs hsub
  have he := h φ hφ hs hsub
  calc
    _ = ∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = -(∫ x in U, g x * φ x) := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

 def MemW1pWitness.congr_ae {p : ℝ≥0∞} {f g : E → ℝ} {U : Set E}
    (h : MemW1pWitness p f U) (he : f =ᵐ[volume.restrict U] g) :
    MemW1pWitness p g U where
  memLp := h.memLp.ae_eq he
  weakGrad := h.weakGrad
  weakGrad_component_memLp := h.weakGrad_component_memLp
  isWeakGrad i := (h.isWeakGrad i).congr_ae he Filter.EventuallyEq.rfl

end DeGiorgi

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalRealBeltrami
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise classical real-coefficient principal Beltrami input.

Published source: Clop and Cruz, *Weighted estimates for Beltrami
equations*, Ann. Acad. Sci. Fenn. Math. 38 (2013), 91–113,
DOI 10.5186/aasfm.2013.3818, section 4, opening paragraph, p. 107.
Their theorem states existence of a principal W^{1,2}_loc plane homeomorphism
for compactly supported measurable coefficients mu, nu with
|mu|+|nu| bounded by k<1. We use only mu=0 and real nu=q.

No height, energy inequality, extremality, circle model, or limiting
assertion is included in this input. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

structure PlaneLocalWeakComplex (f : EuclideanPlane → ℂ) where
  realGradient : EuclideanPlane → EuclideanPlane
  imagGradient : EuclideanPlane → EuclideanPlane
  real_weak : DeGiorgi.HasWeakGrad realGradient (fun x => (f x).re) univ
  imag_weak : DeGiorgi.HasWeakGrad imagGradient (fun x => (f x).im) univ
  real_memLp : ∀ R i, MemLp (fun x => realGradient x i) 2
    (volume.restrict (Metric.ball 0 R))
  imag_memLp : ∀ R i, MemLp (fun x => imagGradient x i) 2
    (volume.restrict (Metric.ball 0 R))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactMollifierSampling
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform sampling control on compact sets, including exact preservation
of constant regions and smooth cutoffs equal to one near a compact set. -/

open Set Filter MeasureTheory Metric
open scoped Topology

/-- d13f23b's `exists_contDiff_support_eq_eq_one_iff` (missing in our Mathlib 0df444a), derived as there from
`exists_contMDiff_support_eq_eq_one_iff`. -/
theorem _root_.exists_contDiff_support_eq_eq_one_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ∞} {s t : Set E} (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : E → ℝ, ContDiff ℝ n f ∧ Set.range f ⊆ Set.Icc 0 1 ∧ Function.support f = s ∧
      (∀ x, x ∈ t ↔ f x = 1) := by
  simpa [contMDiff_iff_contDiff] using
    exists_contMDiff_support_eq_eq_one_iff (modelWithCornersSelf ℝ E) (n := n) hs ht h

noncomputable section

namespace CircleDomainRigidity

theorem exists_smooth_compact_cutoff_one_near
    {K Ω : Set EuclideanPlane} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ (η : EuclideanPlane → ℝ) (V : Set EuclideanPlane),
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀x, η x ∈ Icc 0 1) ∧ tsupport η ⊆ Ω ∧
      IsOpen V ∧ K ⊆ V ∧ ∀x ∈ V, η x = 1 := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hsub : cthickening (δ / 2) K ⊆ thickening δ K :=
    cthickening_subset_thickening' hδ (half_lt_self hδ) K
  obtain ⟨η, hη, hunit, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff isOpen_thickening isClosed_cthickening hsub
      (n := (⊤ : ℕ∞))
  have hs : tsupport η ⊆ cthickening δ K := by
    rw [tsupport, hsupp]
    exact closure_thickening_subset_cthickening δ K
  refine ⟨η, thickening (δ / 2) K, hη,
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure hs,
    fun x => hunit (mem_range_self x), hs.trans hδΩ, isOpen_thickening,
    self_subset_thickening (half_pos hδ) K, ?_⟩
  intro x hx
  exact (hone x).1 (thickening_subset_cthickening (δ / 2) K hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_UniformLocalMollification
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive mollification approximates a continuous branch uniformly on
a compact set strictly inside its domain of continuity. -/

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem planarMollification_uniform_on_compact
    {u : EuclideanPlane → ℝ} (hu : AEStronglyMeasurable u volume)
    {K V : Set EuclideanPlane} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hc : ContinuousOn u V) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, |planarMollification u n x - u x| < ε := by
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  have huc := (hK.cthickening (r := r)).uniformContinuousOn_of_continuous (hc.mono hrV)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
  have hrad : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < min r δ :=
    (tendsto_order.mp tendsto_planarMollifier_radius).2 _ (lt_min hr hδ)
  filter_upwards [hrad] with n hn x hx
  have hb : ∀ y ∈ ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut,
      dist (u y) (u x) ≤ ε / 2 := by
    intro y hy
    have hyx : dist y x < min r δ := (mem_ball.mp hy).trans hn
    exact (hd y (mem_cthickening_of_dist_le y x r K hx (lt_of_lt_of_le hyx (min_le_left _ _)).le)
      x (self_subset_cthickening K hx) (lt_of_lt_of_le hyx (min_le_right _ _))).le
  have he := (DeGiorgi.shrinkingBump (d := 2) n).dist_normed_convolution_le hu hb
  exact (show |planarMollification u n x - u x| ≤ ε / 2 by
    simpa only [planarMollification, Real.dist_eq] using he).trans_lt (half_lt_self hε)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactSobolevCutoff
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact cutoffs turn local planar Sobolev functions into
global Sobolev functions, to which positive mollification applies. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem memW1p_mul_compact_cutoff
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) {u η : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1p 2 u Ω) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) : DeGiorgi.MemW1p 2 (fun x => η x * u x) Ω := by
  obtain ⟨A, hA⟩ := hη.continuous.bounded_above_of_compact_support hsη
  obtain ⟨B, hB⟩ := (hη.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).bounded_above_of_compact_support
    (hsη.fderiv (𝕜 := ℝ))
  exact (hu.someWitness.mul_smooth_bounded_p (by norm_num) hΩ hη
    (le_max_right A 0) (le_max_right B 0)
    (fun x => by simpa only [Real.norm_eq_abs] using (hA x).trans (le_max_left A 0))
    (fun x => (hB x).trans (le_max_left B 0))).memW1p

theorem exists_global_compact_cutoff_witness
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) {u η : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1p 2 u Ω) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (hsub : tsupport η ⊆ Ω) :
    Nonempty (DeGiorgi.MemW1pWitness 2 (fun x => η x * u x) univ) := by
  let v : EuclideanPlane → ℝ := fun x => η x * u x
  have hv : DeGiorgi.MemW1p 2 v Ω := memW1p_mul_compact_cutoff hΩ hu hη hsη
  have hsv : HasCompactSupport v := hsη.mul_right
  have hsubv : tsupport v ⊆ Ω := (tsupport_mul_subset_left).trans hsub
  have hv' : DeGiorgi.MemW1p (ENNReal.ofReal (2 : ℝ)) v Ω := by simpa using hv
  have hzero := DeGiorgi.memW01p_of_memW1p_of_tsupport_subset
    (p := 2) hΩ (by norm_num) hv' hsv hsubv
  have hi : Ω.indicator v = v := by
    funext x
    by_cases hx : x ∈ Ω
    · exact indicator_of_mem hx v
    · rw [indicator_of_notMem hx]
      exact (DeGiorgi.zero_outside_of_tsupport_subset hsubv hx).symm
  have hw := DeGiorgi.zeroExtend_memW1pWitness_p (p := 2) hΩ (by norm_num) hzero hv'.someWitness
  rw [hi] at hw
  exact ⟨by simpa using hw⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevSmoothing
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local positive smoothing with errors relative to the original weak
gradient. Compact cutoffs are removed on a neighborhood of the core. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem weakPartial_congrOn {V : Set EuclideanPlane} (hV : IsOpen V)
    {f g G : EuclideanPlane → ℝ} {i : Fin 2}
    (hG : DeGiorgi.HasWeakPartialDeriv i G f V) (hfg : EqOn f g V) :
    DeGiorgi.HasWeakPartialDeriv i G g V := by
  intro φ hφ hsφ hsubφ
  calc
    _ = ∫x in V, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) :=
      setIntegral_congr_fun hV.measurableSet (fun x hx => by rw [hfg hx])
    _ = _ := hG φ hφ hsφ hsubφ

theorem weakGrad_eq_on_cutoff_plateau
    {Ω V : Set EuclideanPlane} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u η : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hw : DeGiorgi.MemW1pWitness 2 (fun x => η x * u x) univ)
    (hone : ∀x ∈ V, η x = 1) (i : Fin 2) :
    (fun x => hw.weakGrad x i) =ᵐ[volume.restrict V] fun x => hu.weakGrad x i := by
  let hwV := hw.restrict hV (subset_univ V)
  let huV := hu.restrict hV hVΩ
  have hG := weakPartial_congrOn hV (hwV.isWeakGrad i)
    (fun x hx => by rw [hone x hx, one_mul])
  simpa only [hwV, huV, DeGiorgi.MemW1pWitness.restrict] using
    hG.ae_eq hV (huV.isWeakGrad i)
    ((hwV.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((huV.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MobiusConformal
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Holomorphy of the explicit normalizing Möbius maps

The affine chart at infinity is the rational function z / (a + b z).
This gives a nonzero derivative there as well as in every finite chart.
-/

open Set Filter Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

@[simp] theorem finiteCoord_coe (z : ℂ) : finiteCoord (z : Sphere) = z := rfl

@[simp] theorem chart_coe_apply (p : ℂ) (q : Sphere) :
    chart (p : Sphere) q = finiteCoord q := by
  simp [chart]

@[simp] theorem chart_coe_self (p : ℂ) : chart (p : Sphere) (p : Sphere) = p := by
  simp [finiteCoord]

@[simp] theorem chart_infty_apply (q : Sphere) :
    chart OnePoint.infty q = finiteCoord (sphereInv q) := by simp [chart]

@[simp] theorem sphereInv_infty : sphereInv OnePoint.infty = ((0 : ℂ) : Sphere) := rfl

@[simp] theorem sphereInv_zero : sphereInv ((0 : ℂ) : Sphere) = OnePoint.infty := by
  simp [sphereInv]

@[simp] theorem chartSymm_coe_apply (p z : ℂ) : chartSymm (p : Sphere) z = (z : Sphere) := by
  simp [chartSymm]

@[simp] theorem affineSphere_coe (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    affineSphere a b ha (z : Sphere) = ((a * z + b : ℂ) : Sphere) := rfl

@[simp] theorem affineSphere_infty (a b : ℂ) (ha : a ≠ 0) :
    affineSphere a b ha OnePoint.infty = OnePoint.infty := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def closedTerminalCap (H : ℂ ≃ₜ ℂ) : Set Sphere :=
  ((↑) : ℂ → Sphere) '' closure (jordanInterior H)

def openCompletedRegion {I : Type*} (H : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  (⋃ i, closedTerminalCap (H i))ᶜ

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_QuasiconformalSobolev
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quasiconformal change of variables for continuous Sobolev functions.

Oliva--Prats, *Sharp bounds for composition with quasiconformal mappings
in Sobolev spaces*, J. Math. Anal. Appl. 451 (2017), 1026--1044,
DOI 10.1016/j.jmaa.2017.02.016: Definition 2.1, Theorem 2.2 (null-set
preservation and inverse regularity), and Theorem 2.7, critical case
p = n = 2, with the chain rule in its proof;
https://arxiv.org/pdf/1612.00689, sections 2.1--2.2, pp. 4--7.

We assume only inverse weak derivatives, forward preservation of null
sets, and the scalar Sobolev chain rule for continuous compactly supported
functions. The squared Frobenius bound below is stronger than the operator
norm bound in Definition 2.1. No model or extremality assertion is assumed.
-/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def physicalHomeomorph (φ : ℂ ≃ₜ ℂ) : EuclideanPlane ≃ₜ EuclideanPlane :=
  (complexPlaneCoordinates.toHomeomorph.trans φ).trans
    complexPlaneCoordinates.toHomeomorph.symm

@[simp] theorem physicalHomeomorph_apply (φ : ℂ ≃ₜ ℂ) (x : EuclideanPlane) :
    physicalHomeomorph φ x = complexPlaneCoordinates.symm (φ (complexPlaneCoordinates x)) := rfl

@[simp] theorem physicalHomeomorph_symm (φ : ℂ ≃ₜ ℂ) :
    (physicalHomeomorph φ).symm = physicalHomeomorph φ.symm := rfl

 theorem planeSphere_physicalHomeomorph (φ : ℂ ≃ₜ ℂ) (x : EuclideanPlane) :
    planeSphere (physicalHomeomorph φ x) = φ.onePointCongr (planeSphere x) := by
  simp [planeSphere]

 def PlaneLocalWeakComplex.HasBoundedDistortion {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ ∀ᵐ x ∂volume,
    (D.realGradient x 0)^2 + (D.realGradient x 1)^2 +
      (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2 ≤
        K * |D.realGradient x 0 * D.imagGradient x 1 -
          D.realGradient x 1 * D.imagGradient x 0|

 def PlaneQuasiconformalCalculus : Prop :=
  ∀ (φ : ℂ ≃ₜ ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
    D.HasBoundedDistortion →
    ∃ E : PlaneLocalWeakComplex (fun x => φ.symm (complexPlaneCoordinates x)),
      Measure.QuasiMeasurePreserving (physicalHomeomorph φ.symm) volume volume ∧
      ∀ (u : EuclideanPlane → ℝ), Continuous u → HasCompactSupport u →
        ∀ H : DeGiorgi.MemW1pWitness 2 u univ,
        ∃ V : DeGiorgi.MemW1pWitness 2 (u ∘ physicalHomeomorph φ.symm) univ,
          ∀ᵐ x ∂volume, ∀ j : Fin 2,
            V.weakGrad x j =
              H.weakGrad (physicalHomeomorph φ.symm x) 0 * E.realGradient x j +
              H.weakGrad (physicalHomeomorph φ.symm x) 1 * E.imagGradient x j

 theorem quasiconformal_compact_zero_gradient (hqc : PlaneQuasiconformalCalculus)
    (φ : ℂ ≃ₜ ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hd : D.HasBoundedDistortion) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (H : DeGiorgi.MemW1pWitness 2 u univ) (F : Set EuclideanPlane)
    (hz : ∀ j, ∀ᵐ x ∂volume, x ∈ F → H.weakGrad x j = 0) :
    ∃ V : DeGiorgi.MemW1pWitness 2 (u ∘ physicalHomeomorph φ.symm) univ,
      ∀ j, ∀ᵐ x ∂volume, x ∈ physicalHomeomorph φ '' F → V.weakGrad x j = 0 := by
  obtain ⟨E, hN, hcomp⟩ := hqc φ D hd
  obtain ⟨V, hV⟩ := hcomp u hu hs H
  refine ⟨V, fun j => ?_⟩
  filter_upwards [hV, hN.ae (hz 0), hN.ae (hz 1)] with x hx h0 h1 hxF
  have hin : physicalHomeomorph φ.symm x ∈ F := by
    obtain ⟨y, hy, rfl⟩ := hxF
    simpa only [← physicalHomeomorph_symm, Homeomorph.symm_apply_apply] using hy
  rw [hx j, h0 hin, h1 hin, zero_mul, zero_mul, add_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2ProductConvergence
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L² convergence may be paired with uniformly bounded,
almost-everywhere convergent multipliers and a fixed L² test. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem abs_integral_mul_le_eLpNorm_two
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have he : (∫ x, f x * g x ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp only [Real.inner_apply, hx, hy]
  rw [he, ← Lp.norm_toLp, ← Lp.norm_toLp]
  exact abs_real_inner_le_norm _ _

 theorem tendsto_integral_bounded_mul_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → X → ℝ} {G : X → ℝ} {h : ℕ → X → ℝ} {H φ : X → ℝ}
    (hg : ∀ n, MemLp (g n) 2 μ) (hG : MemLp G 2 μ) (hφ : MemLp φ 2 μ)
    (hl : Tendsto (fun n => eLpNorm (fun x => g n x - G x) 2 μ) atTop (𝓝 0))
    (hm : ∀ n, AEStronglyMeasurable (h n) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ ≤ C)
    (hp : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 (H x))) :
    Tendsto (fun n => ∫ x, h n x * g n x * φ x ∂μ) atTop
      (𝓝 (∫ x, H x * G x * φ x ∂μ)) := by
  have hH : AEStronglyMeasurable H μ := aestronglyMeasurable_of_tendsto_ae atTop hm hp
  have hHb : ∀ᵐ x ∂μ, ‖H x‖ ≤ C := by
    filter_upwards [hp, ae_all_iff.2 hb] with x hx hb
    exact le_of_tendsto hx.norm (Eventually.of_forall hb)
  have hprod : Integrable (fun x => G x * φ x) μ := hG.integrable_mul hφ
  have hdom : Integrable (fun x => C * ‖G x * φ x‖) μ := hprod.norm.const_mul C
  have hmain := tendsto_integral_of_dominated_convergence
    (F := fun n x => h n x * G x * φ x) (f := fun x => H x * G x * φ x)
    (fun x => C * ‖G x * φ x‖)
    (fun n => ((hm n).mul hG.aestronglyMeasurable).mul hφ.aestronglyMeasurable)
    hdom (fun n => by
      filter_upwards [hb n] with x hx
      simpa only [norm_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right hx (norm_nonneg (G x * φ x)))
    (by filter_upwards [hp] with x hx; exact (hx.mul_const _).mul_const _)
  have herr : Tendsto (fun n => ∫ x, h n x * (g n x - G x) * φ x ∂μ)
      atTop (𝓝 0) := by
    have hnorm : Tendsto (fun n => (eLpNorm (fun x => g n x - G x) 2 μ).toReal)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal (by simp)).comp hl
    apply squeeze_zero_norm' _ (by
      simpa using ((hnorm.const_mul C).mul_const (eLpNorm φ 2 μ).toReal))
    apply Eventually.of_forall
    intro n
    let D : X → ℝ := fun x => g n x - G x
    have hD : MemLp D 2 μ := (hg n).sub hG
    have hint : Integrable (fun x => ‖D x‖ * ‖φ x‖) μ := hD.norm.integrable_mul hφ.norm
    calc
      ‖∫ x, h n x * D x * φ x ∂μ‖ ≤ ∫ x, ‖h n x * D x * φ x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, C * (‖D x‖ * ‖φ x‖) ∂μ := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
          (hint.const_mul C)
        filter_upwards [hb n] with x hx
        simpa only [norm_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right hx (mul_nonneg (norm_nonneg (D x)) (norm_nonneg (φ x)))
      _ = C * ∫ x, ‖D x‖ * ‖φ x‖ ∂μ := integral_const_mul _ _
      _ ≤ C * ((eLpNorm D 2 μ).toReal * (eLpNorm φ 2 μ).toReal) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have ha := abs_integral_mul_le_eLpNorm_two hD.norm hφ.norm
        have hn : 0 ≤ ∫ x, ‖D x‖ * ‖φ x‖ ∂μ := integral_nonneg
          (fun x => mul_nonneg (norm_nonneg (D x)) (norm_nonneg (φ x)))
        rw [eLpNorm_norm _,
          eLpNorm_norm _, abs_of_nonneg hn] at ha
        exact ha
      _ = C * (eLpNorm D 2 μ).toReal * (eLpNorm φ 2 μ).toReal := by ring
  have hsum := herr.add hmain
  simp only [zero_add] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  have hfirst : Integrable (fun x => h n x * (g n x - G x) * φ x) μ := by
    apply ( ((hg n).sub hG).integrable_mul hφ).norm.const_mul C |>.mono'
      (((hm n).mul ((hg n).sub hG).aestronglyMeasurable).mul hφ.aestronglyMeasurable)
    filter_upwards [hb n] with x hx
    change ‖h n x * (g n x - G x) * φ x‖ ≤ C * ‖(g n x - G x) * φ x‖
    simpa only [norm_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg ((g n x - G x) * φ x))
  have hsecond : Integrable (fun x => h n x * G x * φ x) μ := by
    apply hdom.mono' (((hm n).mul hG.aestronglyMeasurable).mul hφ.aestronglyMeasurable)
    filter_upwards [hb n] with x hx
    change ‖h n x * G x * φ x‖ ≤ C * ‖G x * φ x‖
    simpa only [norm_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (G x * φ x))
  rw [← integral_add hfirst hsecond]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CutoffCore
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The physical core containing the entire cutoff transition

Taking the complement of the open one-plateau of the cutoff gives a
compact spherical subset of the original domain. Choosing all disk
closures off this larger core guarantees genuine staircase collars.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def realChartDomain (G : Set Sphere) : Set (ℝ × ℝ) :=
  (fun z : ℝ × ℝ => ((Complex.equivRealProdCLM.symm z : ℂ) : Sphere)) ⁻¹' G

def cutoffCore (χ : (ℝ × ℝ) → ℝ) : Set Sphere :=
  sphericalCore (interior {z | χ z = 1})ᶜ

@[simp] theorem infty_mem_cutoffCore (χ : (ℝ × ℝ) → ℝ) : OnePoint.infty ∈ cutoffCore χ :=
  infty_mem_sphericalCore _

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactClopenRefinement
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite clopen partitions subordinate to prescribed dust neighborhoods

This retains the compact pieces and their containment data, rather than only
the open cover returned by `DustCover`. They are the pieces pulled back to the
physical sphere before simultaneous smooth contour construction.
-/

open Set Function TopologicalSpace

namespace CircleDomainRigidity

theorem exists_compact_clopen_refinement
    {X : Type*} [TopologicalSpace X] [T2Space X] {B : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (V : B → Set X) (hV : ∀ b, IsOpen (V b)) (hbV : ∀ b, b.val ∈ V b) :
    ∃ (n : ℕ) (A : Fin n → Set X) (b : Fin n → B),
      (∀ i, IsCompact (A i) ∧ A i ⊆ B ∧ A i ⊆ V (b i) ∧ IsClosed (B \ A i)) ∧
      Pairwise (Disjoint on A) ∧ (⋃ i, A i) = B := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : TotallyDisconnectedSpace B := totallyDisconnectedSpace_subtype_iff.mpr hTD
  let O : B → Opens B := fun b => ⟨Subtype.val ⁻¹' V b,
    (hV b).preimage continuous_subtype_val⟩
  have hO : IsOpenCover O := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro b
    exact mem_iUnion.mpr ⟨b, hbV b⟩
  obtain ⟨n, C, hC, hcover, hdisj⟩ := hO.exists_finite_nonempty_disjoint_clopen_cover
  choose b hb using fun i => (hC i).2
  let A : Fin n → Set X := fun i => Subtype.val '' (C i : Set B)
  have hAB (i) : A i ⊆ B := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hdiff (i) : B \ A i = Subtype.val '' ((C i : Set B)ᶜ) := by
    ext x
    constructor
    · rintro ⟨hx, hxA⟩
      exact ⟨⟨x, hx⟩, fun h => hxA ⟨⟨x, hx⟩, h, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_⟩
      rintro ⟨y, hy, hyx⟩
      exact hx (Subtype.ext hyx ▸ hy)
  refine ⟨n, A, b, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(C i).isClosed.isCompact.image continuous_subtype_val, hAB i, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hb i hx
    · rw [hdiff]
      exact hB.isClosed.isClosedMap_subtype_val _ (C i).isOpen.isClosed_compl
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have hvu' : v = u := Subtype.ext hvu
    subst v
    exact Set.disjoint_left.mp (Clopens.coe_disjoint.mpr (hdisj hij)) hu hv
  · apply Set.Subset.antisymm (iUnion_subset hAB)
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ (⟨x, hx⟩ : B)))
    exact mem_iUnion.mpr ⟨i, ⟨x, hx⟩, hi, rfl⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CompletedChart
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual completed region in the finite real chart

These identifications pass the spherical disk completion to the real
coordinates used by the energy estimates, preserving the original core
and the exact open extension domain.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

@[simp] theorem realChartDomain_union (G H : Set Sphere) :
    realChartDomain (G ∪ H) = realChartDomain G ∪ realChartDomain H := rfl

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LimitSphereExtension
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extending a principally normalized limit across infinity

The uniform principal remainder does more than prevent a constant
limit: it gives continuity on the sphere and chart derivative one at
infinity. This step needs no further analytic input.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def extendAtInfinity (F : ℂ → ℂ) : Sphere → Sphere :=
  fun p => p.elim OnePoint.infty (fun z => (F z : Sphere))

@[simp] theorem extendAtInfinity_infty (F : ℂ → ℂ) :
    extendAtInfinity F OnePoint.infty = OnePoint.infty := rfl

@[simp] theorem extendAtInfinity_coe (F : ℂ → ℂ) (z : ℂ) :
    extendAtInfinity F (z : Sphere) = (F z : Sphere) := rfl

theorem principal_remainder_tendsto_zero {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0) :=
  hF.trans_tendsto (tendsto_inv₀_cobounded (α := ℂ))

theorem principal_tendsto_cobounded {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    Tendsto F (cobounded ℂ) (cobounded ℂ) := by
  apply tendsto_norm_atTop_iff_cobounded.mp
  apply tendsto_atTop.mpr
  intro A
  have hb : ∀ᶠ z in cobounded ℂ, ‖F z - z‖ ≤ 1 := by
    have hn : Tendsto (fun z => ‖F z - z‖) (cobounded ℂ) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using (principal_remainder_tendsto_zero hF).norm
    have h := hn.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact h.mono (fun _ hz => hz.le)
  filter_upwards [hb, eventually_cobounded_le_norm (E := ℂ) (A + 1)] with z hz hzn
  have hn := norm_le_norm_sub_add z (F z)
  rw [norm_sub_rev] at hn
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneQuotientRepresentative
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Descend a physical planar function through the actual domain homeomorphism. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

def sphereFromPlaneFunction (w : EuclideanPlane → ℝ) (p : Sphere) : ℝ := by
  classical
  exact if p = OnePoint.infty then 0 else w (complexPlaneCoordinates.symm (finiteCoord p))

@[simp] theorem sphereFromPlaneFunction_coe (w : EuclideanPlane → ℝ) (z : ℂ) :
    sphereFromPlaneFunction w (z : Sphere) = w (complexPlaneCoordinates.symm z) := by
  simp [sphereFromPlaneFunction, finiteCoord]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SpherePlaneContinuity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compactly supported planar smoothing descends continuously across infinity. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem sphereFromPlaneFunction_continuousAt_coe
    {w : EuclideanPlane → ℝ} {z : ℂ}
    (hw : ContinuousAt w (complexPlaneCoordinates.symm z)) :
    ContinuousAt (sphereFromPlaneFunction w) (z : Sphere) := by
  apply OnePoint.continuousAt_coe.mpr
  have he : sphereFromPlaneFunction w ∘ ((↑) : ℂ → Sphere) =
      w ∘ complexPlaneCoordinates.symm := by
    funext z
    exact sphereFromPlaneFunction_coe w z
  rw [he]
  exact hw.comp complexPlaneCoordinates.symm.continuous.continuousAt

theorem sphereFromPlaneFunction_continuousAt_infty
    {w : EuclideanPlane → ℝ} {K : Set EuclideanPlane} (hK : IsCompact K)
    (hw : ∀x ∉ K, w x = 0) :
    ContinuousAt (sphereFromPlaneFunction w) OnePoint.infty := by
  apply OnePoint.continuousAt_infty.mpr
  intro S hS
  have hK' : IsCompact (complexPlaneCoordinates '' K) := hK.image complexPlaneCoordinates.continuous
  refine ⟨complexPlaneCoordinates '' K, hK'.isClosed, hK', ?_⟩
  intro z hz
  change sphereFromPlaneFunction w (z : Sphere) ∈ S
  rw [sphereFromPlaneFunction_coe, hw _ ?_]
  · apply mem_of_mem_nhds
    simpa [sphereFromPlaneFunction] using hS
  · intro hx
    exact hz ⟨complexPlaneCoordinates.symm z, hx, complexPlaneCoordinates.apply_symm_apply z⟩

theorem sphereFromPlaneFunction_continuousOn
    {G : Set Sphere} (hG : IsOpen G) {w : EuclideanPlane → ℝ}
    (hw : ContinuousOn w (physicalPlaneDomain G))
    {K : Set EuclideanPlane} (hK : IsCompact K) (hzero : ∀x ∉ K, w x = 0) :
    ContinuousOn (sphereFromPlaneFunction w) G := by
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (sphereFromPlaneFunction_continuousAt_infty hK hzero).continuousWithinAt
  | coe z =>
    have hx : complexPlaneCoordinates.symm z ∈ physicalPlaneDomain G := by
      change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp
    exact (sphereFromPlaneFunction_continuousAt_coe
      (hw.continuousAt ((isOpen_physicalPlaneDomain hG).mem_nhds hx))).continuousWithinAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_PrincipalCoefficientLimit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first principal coefficient as a limit. Composition adds the actual
coefficients, and the published area theorem bounds each coefficient on a
fixed exterior disk. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def HasPrincipalCoefficient (F : ℂ → ℂ) (b : ℂ) : Prop :=
  Tendsto (fun z => z*(F z-z)) (cobounded ℂ) (𝓝 b)

 theorem HasPrincipalCoefficient.bigO {F : ℂ → ℂ} {b : ℂ}
    (hb : HasPrincipalCoefficient F b) :
    (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  have hB : (fun z => z*(F z-z)) =O[cobounded ℂ] (fun _ => (1 : ℂ)) :=
    isBigO_const_of_tendsto hb (by norm_num : (1 : ℂ) ≠ 0)
  have h := (isBigO_refl (fun z : ℂ => z⁻¹) (cobounded ℂ)).mul hB
  apply h.congr' _ (Eventually.of_forall (fun z => mul_one z⁻¹))
  have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    exact isCompact_singleton.compl_mem_cocompact
  filter_upwards [hn] with z hz
  simp [hz]

 theorem HasPrincipalCoefficient.comp {F P : ℂ → ℂ} {b c : ℂ}
    (hb : HasPrincipalCoefficient F b) (hc : HasPrincipalCoefficient P c) :
    HasPrincipalCoefficient (P ∘ F) (b+c) := by
  have hFt := principal_tendsto_cobounded hb.bigO
  have hF0 := principal_remainder_tendsto_zero hb.bigO
  have hP0 := (principal_remainder_tendsto_zero hc.bigO).comp hFt
  have hh := ((Filter.Tendsto.comp hc hFt).sub (hF0.mul hP0)).add hb
  simp only [zero_mul, sub_zero] at hh
  rw [add_comm b c]
  apply hh.congr'
  filter_upwards [] with z
  dsimp only [Function.comp_apply]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarModel
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar models with a globally deformed round complement. This is the
smaller class needed for coefficient extremality: it contains the actual
circle models and is closed under plane homeomorphisms. The deformation
retains every complementary component, rather than just its boundary. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 structure CompactScalarModel (G : Set Sphere) {m : ℕ}
    (u : Fin m → EuclideanPlane → ℝ) where
  function : ℂ → ℂ
  coefficient : ℂ
  coefficient_limit : HasPrincipalCoefficient function coefficient
  conformal : IsConformalEquivalence (extendAtInfinity function) G (extendAtInfinity function '' G)
  roundDomain : Set Sphere
  round_circle : IsCircleDomain roundDomain
  deformation : ℂ ≃ₜ ℂ
  image_eq : extendAtInfinity function '' G = deformation.onePointCongr '' roundDomain
  projection : Sphere → Sphere
  projection_continuous : Continuous projection
  projection_inverse : ∀ p ∈ G, projection (extendAtInfinity function p) = p
  projection_outside : ∀ p ∉ extendAtInfinity function '' G, projection p ∈ Gᶜ
  projection_component : ∀ p ∉ extendAtInfinity function '' G,
    ∀ q ∈ connectedComponentIn (extendAtInfinity function '' G)ᶜ p, projection q = projection p
  witness : ∀ i, DeGiorgi.MemW1pWitness 2
    (fun x => sphereFromPlaneFunction (u i) (projection (planeSphere x))) univ
  gradient_zero : ∀ i j, ∀ᵐ x ∂volume,
    x ∉ physicalPlaneDomain (extendAtInfinity function '' G) → (witness i).weakGrad x j = 0
  scalar_compact : ∀ i, HasCompactSupport
    (fun x => sphereFromPlaneFunction (u i) (projection (planeSphere x)))

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_continuous (M : CompactScalarModel G u)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i)) (i : Fin m) :
    Continuous (fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))) := by
  have huc : Continuous (sphereFromPlaneFunction (u i)) := continuousOn_univ.mp
    (sphereFromPlaneFunction_continuousOn isOpen_univ (hu i).continuousOn (hs i).isCompact
      (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  exact huc.comp (M.projection_continuous.comp continuous_planeSphere)

 end CompactScalarModel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ScalarModelPostcomposition
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Postcomposition of actual scalar models. The scalar witnesses and their
zero complementary gradients follow from the published chain rule and
null-set preservation. The topological data are transported explicitly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem extendAtInfinity_postcompose (φ : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    extendAtInfinity (φ ∘ f) = φ.onePointCongr ∘ extendAtInfinity f := by
  funext p
  cases p using OnePoint.rec <;> rfl

 theorem physicalPlaneDomain_homeomorph_image (φ : ℂ ≃ₜ ℂ) (Ω : Set Sphere) :
    physicalPlaneDomain (φ.onePointCongr '' Ω) =
      physicalHomeomorph φ '' physicalPlaneDomain Ω := by
  ext x
  rw [φ.onePointCongr.image_eq_preimage_symm,
    (physicalHomeomorph φ).image_eq_preimage_symm]
  change φ.onePointCongr.symm (planeSphere x) ∈ Ω ↔
    planeSphere ((physicalHomeomorph φ).symm x) ∈ Ω
  rw [physicalHomeomorph_symm, planeSphere_physicalHomeomorph]
  rfl

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def postcomposeWithScalarTransport (M : CompactScalarModel G u)
    (φ : ℂ ≃ₜ ℂ)
    (htransport : ∀ i, ∃ V : DeGiorgi.MemW1pWitness 2
      ((fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))) ∘
        physicalHomeomorph φ.symm) univ,
      ∀ j, ∀ᵐ x ∂volume,
        x ∈ physicalHomeomorph φ '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ →
          V.weakGrad x j=0)
    (c : ℂ) (hc : HasPrincipalCoefficient φ c)
    (hconf : IsConformalEquivalence φ.onePointCongr
      (extendAtInfinity M.function '' G)
      (φ.onePointCongr '' (extendAtInfinity M.function '' G))) : CompactScalarModel G u := by
  let f := φ ∘ M.function
  let Ω := extendAtInfinity M.function '' G
  let e := φ.onePointCongr
  have hf : extendAtInfinity f = e ∘ extendAtInfinity M.function :=
    extendAtInfinity_postcompose φ M.function
  have him : extendAtInfinity f '' G = e '' Ω := by rw [hf, image_comp]
  let P : Sphere → Sphere := M.projection ∘ e.symm
  have hscalar (i : Fin m) :
      (fun x => sphereFromPlaneFunction (u i) (P (planeSphere x))) =
        (fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))) ∘
          physicalHomeomorph φ.symm := by
    funext x
    rw [comp_apply, planeSphere_physicalHomeomorph]
    rfl
  have hphys : (physicalPlaneDomain (extendAtInfinity f '' G))ᶜ =
      physicalHomeomorph φ '' (physicalPlaneDomain Ω)ᶜ := by
    rw [him, physicalPlaneDomain_homeomorph_image, (physicalHomeomorph φ).image_compl]
  choose V hV using htransport
  let hV' (i : Fin m) : DeGiorgi.MemW1pWitness 2
      (fun x => sphereFromPlaneFunction (u i) (P (planeSphere x))) univ :=
    (V i).congr_ae (Eventually.of_forall (fun x => congrFun (hscalar i).symm x))
  refine {
    function := f
    coefficient := M.coefficient+c
    coefficient_limit := M.coefficient_limit.comp hc
    conformal := ?_
    roundDomain := M.roundDomain
    round_circle := M.round_circle
    deformation := M.deformation.trans φ
    image_eq := ?_
    projection := P
    projection_continuous := M.projection_continuous.comp e.symm.continuous
    projection_inverse := ?_
    projection_outside := ?_
    projection_component := ?_
    witness := hV'
    gradient_zero := ?_
    scalar_compact := ?_ }
  · rw [hf, image_comp]
    exact M.conformal.trans hconf
  · rw [him]
    change e '' (extendAtInfinity M.function '' G) = _
    rw [M.image_eq, ← image_comp]
    congr 1
    funext p
    cases p using OnePoint.rec <;> rfl
  · intro p hp
    change M.projection (e.symm (extendAtInfinity f p)) = p
    rw [hf, comp_apply, e.symm_apply_apply]
    exact M.projection_inverse p hp
  · intro p hp
    apply M.projection_outside
    intro hh
    apply hp
    rw [him]
    exact ⟨e.symm p, hh, e.apply_symm_apply p⟩
  · intro p hp q hq
    have hpold : e.symm p ∉ Ω := by
      intro hh
      apply hp
      rw [him]
      exact ⟨e.symm p, hh, e.apply_symm_apply p⟩
    have hback : e.symm '' (extendAtInfinity f '' G)ᶜ = Ωᶜ := by
      rw [him, ← e.image_compl, image_image]
      simp only [e.symm_apply_apply, image_id']
    have hqback := e.symm.continuous.continuousOn.image_connectedComponentIn_subset hp
      (mem_image_of_mem e.symm hq)
    rw [hback] at hqback
    exact M.projection_component (e.symm p) hpold (e.symm q) hqback
  · intro i j
    have he := hV i j
    rw [← hphys] at he
    exact he
  · intro i
    rw [hscalar]
    exact (M.scalar_compact i).comp_homeomorph (physicalHomeomorph φ.symm)

 def postcompose (M : CompactScalarModel G u) (hqc : PlaneQuasiconformalCalculus)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (φ : ℂ ≃ₜ ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hd : D.HasBoundedDistortion) (c : ℂ) (hc : HasPrincipalCoefficient φ c)
    (hconf : IsConformalEquivalence φ.onePointCongr
      (extendAtInfinity M.function '' G)
      (φ.onePointCongr '' (extendAtInfinity M.function '' G))) : CompactScalarModel G u := by
  exact M.postcomposeWithScalarTransport φ
    (fun i => quasiconformal_compact_zero_gradient hqc φ D hd
      (M.scalar_continuous hu hs i) (M.scalar_compact i) (M.witness i)
      (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ (M.gradient_zero i))
    c hc hconf

 @[simp] theorem postcompose_coefficient (M : CompactScalarModel G u)
    (hqc : PlaneQuasiconformalCalculus)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hd : D.HasBoundedDistortion) (c : ℂ) (hc : HasPrincipalCoefficient φ c)
    (hconf : IsConformalEquivalence φ.onePointCongr
      (extendAtInfinity M.function '' G)
      (φ.onePointCongr '' (extendAtInfinity M.function '' G))) :
    (M.postcompose hqc hu hs φ D hd c hc hconf).coefficient = M.coefficient+c := rfl

 end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_VerticalWeakConstant
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalization of a zero-error height: its only possible freedom
is an additive constant, which exterior decay then removes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def verticalLinear : EuclideanPlane →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp euclideanPlaneCoordinates.toContinuousLinearMap

 @[simp] theorem verticalLinear_apply (p : EuclideanPlane) : verticalLinear p = p 1 := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BarrierDifferentialError
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise differential comparison used by the saved barriers. The
exceptional set allows unrestricted horizontal displacement, while its
energy contribution is charged only on that set. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem composition_covector_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A H : E →L[ℝ] F) (P Q : F →L[ℝ] ℝ) :
    ‖P.comp A-Q.comp H‖ ≤ ‖P‖*‖A-H‖+‖P-Q‖*‖H‖ := by
  have he : P.comp A-Q.comp H = P.comp (A-H)+(P-Q).comp H := by
    ext x
    simp only [sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (P.opNorm_comp_le _) ((P-Q).opNorm_comp_le _))

 theorem barrier_differential_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : Type*} (S : Set X) (A H : X → F)
    (DA DH : X → E →L[ℝ] F) (Φ : F → ℝ)
    {M₁ M₂ e : ℝ} (_hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hbound : ∀ y, ‖fderiv ℝ Φ y‖ ≤ M₁)
    (hlip : ∀ y z, ‖fderiv ℝ Φ y-fderiv ℝ Φ z‖ ≤ M₂*‖y-z‖)
    (hclose : ∀ x ∉ S, ‖A x-H x‖ ≤ e) (x : X) :
    ‖(fderiv ℝ Φ (A x)).comp (DA x)-(fderiv ℝ Φ (H x)).comp (DH x)‖ ≤
      M₁*‖DA x-DH x‖+M₂*e*‖DH x‖+2*M₁*S.indicator (fun _ => ‖DH x‖) x := by
  have hbase := composition_covector_error (DA x) (DH x)
    (fderiv ℝ Φ (A x)) (fderiv ℝ Φ (H x))
  have hfirst : ‖fderiv ℝ Φ (A x)‖*‖DA x-DH x‖ ≤ M₁*‖DA x-DH x‖ :=
    mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx]
    have hd : ‖fderiv ℝ Φ (A x)-fderiv ℝ Φ (H x)‖ ≤ 2*M₁ := by
      exact (norm_sub_le _ _).trans (by linarith [hbound (A x), hbound (H x)])
    have hb := mul_le_mul_of_nonneg_right hd (norm_nonneg (DH x))
    have hz : 0 ≤ M₂*e*‖DH x‖ := mul_nonneg (mul_nonneg hM₂ he) (norm_nonneg _)
    linarith
  · rw [indicator_of_notMem hx, mul_zero, add_zero]
    have hd : ‖fderiv ℝ Φ (A x)-fderiv ℝ Φ (H x)‖ ≤ M₂*e :=
      (hlip _ _).trans (mul_le_mul_of_nonneg_left (hclose x hx) hM₂)
    have hb := mul_le_mul_of_nonneg_right hd (norm_nonneg (DH x))
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2ThreeTermBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three error terms in the barrier comparison retain their separate
L2 budgets. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem real_l2_add_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (eLpNorm (fun x => f x+g x) 2 μ).toReal ≤
      (eLpNorm f 2 μ).toReal+(eLpNorm g 2 μ).toReal := by
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable (f := f) (g := g) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  rw [show (fun x => f x+g x) = f+g from rfl]
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] at hh
  exact hh

 theorem real_l2_nonneg_scale {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (eLpNorm (fun x => a*f x) 2 μ).toReal = a*(eLpNorm f 2 μ).toReal := by
  have hh : eLpNorm (fun x => a*f x) 2 μ = ENNReal.ofReal a*eLpNorm f 2 μ := by
    change eLpNorm (a • f) 2 μ = _
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg ha] using eLpNorm_const_smul a f 2 μ
  rw [hh, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]

 theorem l2_three_term_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {F : X → E} {g h k : X → ℝ}
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hF : AEStronglyMeasurable F μ) (hg : MemLp g 2 μ)
    (hh : MemLp h 2 μ) (hk : MemLp k 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hh0 : ∀ᵐ x ∂μ, 0 ≤ h x) (hk0 : ∀ᵐ x ∂μ, 0 ≤ k x)
    (hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ a*g x+b*h x+c*k x) :
    MemLp F 2 μ ∧ (eLpNorm F 2 μ).toReal ≤
      a*(eLpNorm g 2 μ).toReal+b*(eLpNorm h 2 μ).toReal+c*(eLpNorm k 2 μ).toReal := by
  let v := fun x => a*g x+b*h x+c*k x
  have hv : MemLp v 2 μ := ((hg.const_mul a).add (hh.const_mul b)).add (hk.const_mul c)
  have hnorm : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖v x‖ := by
    filter_upwards [hbound, hg0, hh0, hk0] with x hx hxg hxh hxk
    simpa only [v, Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (add_nonneg (mul_nonneg ha hxg) (mul_nonneg hb hxh)) (mul_nonneg hc hxk))] using hx
  refine ⟨hv.of_le hF hnorm, ?_⟩
  have h₀ := ENNReal.toReal_mono hv.eLpNorm_ne_top (eLpNorm_mono_ae hnorm)
  have h₁ := real_l2_add_bound ((hg.const_mul a).add (hh.const_mul b)) (hk.const_mul c)
  have h₂ := real_l2_add_bound (hg.const_mul a) (hh.const_mul b)
  rw [real_l2_nonneg_scale μ k hc] at h₁
  rw [real_l2_nonneg_scale μ g ha, real_l2_nonneg_scale μ h hb] at h₂
  simp only [Pi.add_apply] at h₁
  exact h₀.trans (h₁.trans (add_le_add h₂ le_rfl))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BarrierL2Error
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's three-term barrier estimate, including the energy
on the altered horizontal support. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem barrier_L2_error
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace X]
    {μ : Measure X} (S : Set X) (hS : MeasurableSet S)
    (A H : X → F) (DA DH : X → E →L[ℝ] F) (Φ : F → ℝ)
    {M₁ M₂ e : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hbound : ∀ y, ‖fderiv ℝ Φ y‖ ≤ M₁)
    (hlip : ∀ y z, ‖fderiv ℝ Φ y-fderiv ℝ Φ z‖ ≤ M₂*‖y-z‖)
    (hclose : ∀ x ∉ S, ‖A x-H x‖ ≤ e)
    (hD : AEStronglyMeasurable (fun x =>
      (fderiv ℝ Φ (A x)).comp (DA x)-(fderiv ℝ Φ (H x)).comp (DH x)) μ)
    (herror : MemLp (fun x => DA x-DH x) 2 μ) (hH : MemLp DH 2 μ) :
    let D := fun x => (fderiv ℝ Φ (A x)).comp (DA x)-(fderiv ℝ Φ (H x)).comp (DH x)
    MemLp D 2 μ ∧ (eLpNorm D 2 μ).toReal ≤
      M₁*(eLpNorm (fun x => ‖DA x-DH x‖) 2 μ).toReal +
      (M₂*e)*(eLpNorm (fun x => ‖DH x‖) 2 μ).toReal +
      (2*M₁)*(eLpNorm (S.indicator (fun x => ‖DH x‖)) 2 μ).toReal := by
  apply l2_three_term_bound hM₁ (mul_nonneg hM₂ he) (mul_nonneg (by norm_num) hM₁)
    hD herror.norm hH.norm (hH.norm.indicator hS)
    (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun _ => norm_nonneg _))
  · exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · simpa only [indicator_of_mem hx] using norm_nonneg (DH x)
      · simp only [indicator_of_notMem hx, le_refl]
  · exact Eventually.of_forall fun x => by
      have h := barrier_differential_error S A H DA DH Φ hM₁ hM₂ he hbound hlip hclose x
      by_cases hx : x ∈ S
      · simpa only [indicator_of_mem hx, mul_assoc] using h
      · simpa only [indicator_of_notMem hx, mul_assoc] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevConformalTransport
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous compactly supported Sobolev functions can be transported
by the actual smooth conformal inverse. The local target witness has at
most the source energy; no smoothness of the original test is assumed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem planarMollification_tendsto_of_continuous
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (x : EuclideanPlane) :
    Tendsto (fun n => planarMollification u n x) atTop (𝓝 (u x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := planarMollification_uniform_on_compact hu.aestronglyMeasurable
    (K := {x}) isCompact_singleton isOpen_univ (subset_univ _) hu.continuousOn hε
  filter_upwards [he] with n hn
  simpa only [Real.dist_eq] using hn x (mem_singleton x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarPairCalculus
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-coordinate map and its differential, for composing
saved smooth barriers with Sobolev coordinates. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def planePair (a b : ℝ) : EuclideanPlane :=
  a • EuclideanSpace.single (0 : Fin 2) 1+b • EuclideanSpace.single (1 : Fin 2) 1

 @[simp] theorem planePair_zero (a b : ℝ) : planePair a b 0 = a := by
  simp [planePair]

 @[simp] theorem planePair_one (a b : ℝ) : planePair a b 1 = b := by
  simp [planePair]

 theorem planePair_coordinates (x : EuclideanPlane) : planePair (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> simp

 theorem planePair_covector (L : EuclideanPlane →L[ℝ] ℝ) (a b : ℝ) :
    L (planePair a b) = a*L (EuclideanSpace.single (0 : Fin 2) 1)+
      b*L (EuclideanSpace.single (1 : Fin 2) 1) := by
  simp only [planePair, map_add, map_smul, smul_eq_mul]

 theorem continuous_planePair {X : Type*} [TopologicalSpace X] {a b : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => planePair (a x) (b x)) :=
  (ha.smul continuous_const).add (hb.smul continuous_const)

 theorem contDiff_planePair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {n : WithTop ℕ∞} (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b) :
    ContDiff ℝ n (fun x => planePair (a x) (b x)) :=
  (ha.smul contDiff_const).add (hb.smul contDiff_const)

 theorem hasFDerivAt_planePair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {Da Db : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a Da x) (hb : HasFDerivAt b Db x) :
    HasFDerivAt (fun y => planePair (a y) (b y))
      (Da.smulRight (EuclideanSpace.single (0 : Fin 2) 1)+
       Db.smulRight (EuclideanSpace.single (1 : Fin 2) 1)) x :=
  (ha.smul_const _).add (hb.smul_const _)

 theorem fderiv_planePair_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {Φ : EuclideanPlane → ℝ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hΦ : DifferentiableAt ℝ Φ (planePair (a x) (b x))) (v : E) :
    fderiv ℝ (fun y => Φ (planePair (a y) (b y))) x v =
      fderiv ℝ Φ (planePair (a x) (b x)) (EuclideanSpace.single (0 : Fin 2) 1)*fderiv ℝ a x v+
      fderiv ℝ Φ (planePair (a x) (b x)) (EuclideanSpace.single (1 : Fin 2) 1)*fderiv ℝ b x v := by
  have ht := hΦ.hasFDerivAt.comp x (hasFDerivAt_planePair ha.hasFDerivAt hb.hasFDerivAt)
  change fderiv ℝ (Φ ∘ fun y => planePair (a y) (b y)) x v = _
  rw [ht.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactPairChainRule
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint smooth chain rule for the actual continuous compact source
coordinates. Positive mollification converges pointwise and in gradient
L2, so the two coefficient products pass to the weak derivative. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_pair_weak_chain
    {u v : EuclideanPlane → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v)
    (Wu : DeGiorgi.MemW1pWitness 2 u univ) (Wv : DeGiorgi.MemW1pWitness 2 v univ)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (_hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (0 : Fin 2) 1)*Wu.weakGrad x i+
        fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (1 : Fin 2) 1)*Wv.weakGrad x i)
      (fun x => Φ (planePair (u x) (v x))) univ := by
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using Wu.memLp
  have hvL : MemLp v 2 volume := by simpa only [Measure.restrict_univ] using Wv.memLp
  have hGu : MemLp (fun x => Wu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using Wu.weakGrad_component_memLp i
  have hGv : MemLp (fun x => Wv.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using Wv.weakGrad_component_memLp i
  let a := planarMollification u
  let b := planarMollification v
  let P := fun x => planePair (u x) (v x)
  let Pn := fun n x => planePair (a n x) (b n x)
  let k := fun (j : Fin 2) y => fderiv ℝ Φ y (EuclideanSpace.single j 1)
  have hkc (j : Fin 2) : Continuous (k j) :=
    (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hkb (j : Fin 2) (y : EuclideanPlane) : ‖k j y‖ ≤ C := by
    have h := (fderiv ℝ Φ y).le_opNorm (EuclideanSpace.single j 1)
    have h' : ‖k j y‖ ≤ ‖fderiv ℝ Φ y‖ := by
      simpa only [PiLp.norm_single, norm_one, mul_one] using h
    exact h'.trans (hΦd y)
  have has (n : ℕ) : ContDiff ℝ 1 (a n) :=
    (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbs (n : ℕ) : ContDiff ℝ 1 (b n) :=
    (planarMollification_smooth (hvL.locallyIntegrable (by norm_num)) n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hPs (n : ℕ) : ContDiff ℝ 1 (Pn n) := contDiff_planePair (has n) (hbs n)
  have hPt (x : EuclideanPlane) : Tendsto (fun n => Pn n x) atTop (𝓝 (P x)) :=
    ((planarMollification_tendsto_of_continuous hu x).smul tendsto_const_nhds).add
      ((planarMollification_tendsto_of_continuous hv x).smul tendsto_const_nhds)
  intro φ hφ hs hsub
  let e : EuclideanPlane := EuclideanSpace.single i 1
  have hdc : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport (fun x => fderiv ℝ φ x e) := hs.fderiv_apply (𝕜 := ℝ) e
  have hφL : MemLp φ 2 (volume : Measure EuclideanPlane) :=
    hφ.continuous.memLp_of_hasCompactSupport hs
  have hleft := tendsto_integral_of_dominated_convergence (μ := (volume : Measure EuclideanPlane))
    (F := fun n x => Φ (Pn n x)*fderiv ℝ φ x e)
    (f := fun x => Φ (P x)*fderiv ℝ φ x e)
    (fun x => B*‖fderiv ℝ φ x e‖)
    (fun n => ((hΦ.comp (hPs n)).continuous.aestronglyMeasurable).mul hdc.aestronglyMeasurable)
    ((hdc.integrable_of_hasCompactSupport hds).norm.const_mul B)
    (fun n => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hΦb _) (norm_nonneg _)))
    (Eventually.of_forall (fun x => ((hΦ.continuous.tendsto _).comp (hPt x)).mul_const _))
  have hrightu := tendsto_integral_bounded_mul_L2
    (g := fun n x => fderiv ℝ (a n) x e) (G := fun x => Wu.weakGrad x i)
    (h := fun n x => k 0 (Pn n x)) (H := fun x => k 0 (P x)) (φ := φ)
    (fun n => planarMollification_partial_memLp Wu hsu n i) hGu hφL
    (planarMollification_tendsto_gradient_L2 Wu i)
    (fun n => ((hkc 0).comp (hPs n).continuous).aestronglyMeasurable)
    hC (fun n => Eventually.of_forall (fun x => hkb 0 _))
    (Eventually.of_forall (fun x => ((hkc 0).tendsto _).comp (hPt x)))
  have hrightv := tendsto_integral_bounded_mul_L2
    (g := fun n x => fderiv ℝ (b n) x e) (G := fun x => Wv.weakGrad x i)
    (h := fun n x => k 1 (Pn n x)) (H := fun x => k 1 (P x)) (φ := φ)
    (fun n => planarMollification_partial_memLp Wv hsv n i) hGv hφL
    (planarMollification_tendsto_gradient_L2 Wv i)
    (fun n => ((hkc 1).comp (hPs n).continuous).aestronglyMeasurable)
    hC (fun n => Eventually.of_forall (fun x => hkb 1 _))
    (Eventually.of_forall (fun x => ((hkc 1).tendsto _).comp (hPt x)))
  have hI {g : EuclideanPlane → ℝ} (hg : MemLp g 2 volume)
      {t : EuclideanPlane → ℝ} (ht : AEStronglyMeasurable t volume) (htb : ∀ x, ‖t x‖ ≤ C) :
      Integrable (fun x => t x*g x*φ x) := by
    apply ((hg.integrable_mul hφL).norm.const_mul C).mono'
      ((ht.mul hg.aestronglyMeasurable).mul hφ.continuous.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change ‖t x*g x*φ x‖ ≤ C*‖g x*φ x‖
      simpa only [norm_mul, mul_assoc] using mul_le_mul_of_nonneg_right (htb x) (norm_nonneg (g x*φ x))
  have heq (n : ℕ) : (∫ x, Φ (Pn n x)*fderiv ℝ φ x e) =
      -((∫ x, k 0 (Pn n x)*fderiv ℝ (a n) x e*φ x)+
        (∫ x, k 1 (Pn n x)*fderiv ℝ (b n) x e*φ x)) := by
    have hw := DeGiorgi.HasWeakPartialDeriv.of_contDiff (i := i) isOpen_univ
      (hΦ.comp (hPs n)) φ hφ hs hsub
    simp only [Measure.restrict_univ] at hw
    have hd (x : EuclideanPlane) : fderiv ℝ (fun y => Φ (Pn n y)) x e =
        k 0 (Pn n x)*fderiv ℝ (a n) x e+k 1 (Pn n x)*fderiv ℝ (b n) x e :=
      fderiv_planePair_comp ((has n).differentiable one_ne_zero x)
        ((hbs n).differentiable one_ne_zero x) (hΦ.differentiable one_ne_zero _) e
    change (∫ x, Φ (Pn n x)*fderiv ℝ φ x e) =
      -(∫ x, fderiv ℝ (fun y => Φ (Pn n y)) x e*φ x) at hw
    simp only [hd, add_mul] at hw
    rw [integral_add (hI (t := fun x => k 0 (Pn n x)) (planarMollification_partial_memLp Wu hsu n i)
      (((hkc 0).comp (hPs n).continuous).aestronglyMeasurable) (fun x => hkb 0 _))
      (hI (t := fun x => k 1 (Pn n x)) (planarMollification_partial_memLp Wv hsv n i)
      (((hkc 1).comp (hPs n).continuous).aestronglyMeasurable) (fun x => hkb 1 _))] at hw
    exact hw
  have hPr : Continuous P := continuous_planePair hu hv
  have hsum := hrightu.add hrightv
  have hIu := hI (t := fun x => k 0 (P x)) hGu
    (((hkc 0).comp hPr).aestronglyMeasurable) (fun x => hkb 0 _)
  have hIv := hI (t := fun x => k 1 (P x)) hGv
    (((hkc 1).comp hPr).aestronglyMeasurable) (fun x => hkb 1 _)
  have hls : (∫ x, k 0 (P x)*Wu.weakGrad x i*φ x)+
      (∫ x, k 1 (P x)*Wv.weakGrad x i*φ x) =
      ∫ x, (k 0 (P x)*Wu.weakGrad x i+k 1 (P x)*Wv.weakGrad x i)*φ x := by
    rw [← integral_add hIu hIv]
    congr 1
    funext x
    ring
  rw [hls] at hsum
  simp only [Measure.restrict_univ]
  exact tendsto_nhds_unique hleft (by simpa only [heq] using hsum.neg)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalPairChainRule
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint chain rule on the actual open source domain. All temporary
global extensions are cut off strictly inside that domain, so no
extension across the removed set is assumed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_pair_weak_chain {U : Set EuclideanPlane} (hU : IsOpen U)
    {u v : EuclideanPlane → ℝ} (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (0 : Fin 2) 1)*Wu.weakGrad x i+
        fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (1 : Fin 2) 1)*Wv.weakGrad x i)
      (fun x => Φ (planePair (u x) (v x))) U := by
  intro φ hφ hs hsub
  obtain ⟨η, Z, hη, hsη, _, hηU, hZ, hKZ, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hs hU hsub
  have hZU : Z ⊆ U := by
    intro x hx
    exact hηU (subset_tsupport η (by change η x ≠ 0; rw [hone x hx]; exact one_ne_zero))
  let a := fun x => η x*u x
  let b := fun x => η x*v x
  obtain ⟨Wa⟩ := exists_global_compact_cutoff_witness hU Wu.memW1p hη hsη hηU
  obtain ⟨Wb⟩ := exists_global_compact_cutoff_witness hU Wv.memW1p hη hsη hηU
  have ha : EqOn a u Z := fun x hx => by dsimp [a]; rw [hone x hx, one_mul]
  have hb : EqOn b v Z := fun x hx => by dsimp [b]; rw [hone x hx, one_mul]
  have hGa := (ae_restrict_iff' hZ.measurableSet).mp (weakGrad_eq_on_cutoff_plateau hZ hZU Wu Wa hone i)
  have hGb := (ae_restrict_iff' hZ.measurableSet).mp (weakGrad_eq_on_cutoff_plateau hZ hZU Wv Wb hone i)
  have hdz (x : EuclideanPlane) (hx : x ∉ Z) : fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
      (fun ht => hx (hKZ (tsupport_fderiv_apply_subset ℝ _ ht)))
  have hφz (x : EuclideanPlane) (hx : x ∉ Z) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hKZ ht))
  have hchain := compact_pair_weak_chain (hη.continuous.mul hu) (hη.continuous.mul hv)
    hsη.mul_right hsη.mul_right Wa Wb hΦ hB hC hΦb hΦd i φ hφ hs (subset_univ _)
  simp only [Measure.restrict_univ] at hchain
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hdz x (fun hz => hx (hZU hz)), mul_zero])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hφz x (fun hz => hx (hZU hz)), mul_zero])]
  calc
    _ = ∫ x, Φ (planePair (a x) (b x))*fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Z
        · simp only [a, b, hone x hx, one_mul]
        · simp only [hdz x hx, mul_zero]
    _ = _ := hchain
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hGa, hGb] with x hax hbx
      by_cases hx : x ∈ Z
      · simp only [Pi.mul_apply, hone x hx, one_mul, hax hx, hbx hx]
      · simp only [hφz x hx, mul_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalPairChainWitness
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine local Sobolev witness for each smooth saved barrier
composed with the two actual source coordinates. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def localPairChainWitness {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) :
    DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (u x) (v x))) U where
  memLp := by
    let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUf
    exact MemLp.of_bound ((hΦ.continuous.comp (continuous_planePair hu hv)).aestronglyMeasurable.restrict) B
      (Eventually.of_forall (fun x => hΦb _))
  weakGrad := fun x => WithLp.toLp 2 (fun i =>
    fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (0 : Fin 2) 1)*Wu.weakGrad x i+
    fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (1 : Fin 2) 1)*Wv.weakGrad x i)
  weakGrad_component_memLp := by
    intro i
    have hcoef (j : Fin 2) : Continuous (fun x => fderiv ℝ Φ
        (planePair (u x) (v x)) (EuclideanSpace.single j 1)) :=
      ((hΦ.continuous_fderiv one_ne_zero).comp (continuous_planePair hu hv)).clm_apply continuous_const
    have hbound (j : Fin 2) (x : EuclideanPlane) :
        ‖fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single j 1)‖ ≤ C := by
      have h := (fderiv ℝ Φ (planePair (u x) (v x))).le_opNorm (EuclideanSpace.single j 1)
      have hh : ‖fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single j 1)‖ ≤
          ‖fderiv ℝ Φ (planePair (u x) (v x))‖ := by
        simpa only [PiLp.norm_single, norm_one, mul_one] using h
      exact hh.trans (hΦd _)
    have hmul (j : Fin 2) {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict U)) :
        MemLp (fun x => fderiv ℝ Φ (planePair (u x) (v x))
          (EuclideanSpace.single j 1)*g x) 2 (volume.restrict U) := by
      apply hg.of_le_mul (c := C) ((hcoef j).aestronglyMeasurable.restrict.mul hg.aestronglyMeasurable)
      exact Eventually.of_forall fun x => by
        change ‖fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single j 1)*g x‖ ≤ C*‖g x‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound j x) (norm_nonneg _)
    exact (hmul 0 (Wu.weakGrad_component_memLp i)).add (hmul 1 (Wv.weakGrad_component_memLp i))
  isWeakGrad := local_pair_weak_chain hU hu hv Wu Wv hΦ hB hC hΦb hΦd

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakPairDifferential
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint weak chain rule expressed as an actual linear differential.
Its norm is exactly the norm of the scalar weak gradient, so the
three-term barrier estimate applies to the constructed Sobolev witness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def weakPairDifferential (a b : EuclideanPlane) : EuclideanPlane →L[ℝ] EuclideanPlane :=
  (innerSL ℝ a).smulRight (EuclideanSpace.single (0 : Fin 2) 1)+
    (innerSL ℝ b).smulRight (EuclideanSpace.single (1 : Fin 2) 1)

 theorem plane_inner_basis (a : EuclideanPlane) (i : Fin 2) :
    innerSL ℝ a (EuclideanSpace.single i 1) = a i := by
  fin_cases i <;> simp [innerSL_apply_apply, PiLp.inner_apply ]

 theorem plane_covector_of_basis (L : EuclideanPlane →L[ℝ] ℝ) :
    L = innerSL ℝ (planePair (L (EuclideanSpace.single (0 : Fin 2) 1))
      (L (EuclideanSpace.single (1 : Fin 2) 1))) := by
  ext x
  rw [← planePair_coordinates x, planePair_covector, planePair_covector]
  simp only [plane_inner_basis, planePair_zero, planePair_one]

 theorem weakPairDifferential_chain (L : EuclideanPlane →L[ℝ] ℝ) (a b : EuclideanPlane) :
    L.comp (weakPairDifferential a b) =
      innerSL ℝ (L (EuclideanSpace.single (0 : Fin 2) 1) • a+
        L (EuclideanSpace.single (1 : Fin 2) 1) • b) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, weakPairDifferential, add_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    smul_apply, smul_eq_mul]
  ring

 theorem localPairChainWitness_gradient {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) (x : EuclideanPlane) :
    (localPairChainWitness hU hUf hu hv Wu Wv hΦ hB hC hΦb hΦd).weakGrad x =
      fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (0 : Fin 2) 1) • Wu.weakGrad x+
      fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (1 : Fin 2) 1) • Wv.weakGrad x := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakCovectorGradient
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion between planar scalar covectors and their two
coordinate gradients. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def planeCovectorGradient (L : EuclideanPlane →L[ℝ] ℝ) : EuclideanPlane :=
  planePair (L (EuclideanSpace.single (0 : Fin 2) 1)) (L (EuclideanSpace.single (1 : Fin 2) 1))

 theorem planeCovectorGradient_inner (a : EuclideanPlane) :
    planeCovectorGradient (innerSL ℝ a) = a := by
  simp only [planeCovectorGradient, plane_inner_basis, planePair_coordinates]

 theorem planeCovectorGradient_sub (L K : EuclideanPlane →L[ℝ] ℝ) :
    planeCovectorGradient (L-K) = planeCovectorGradient L-planeCovectorGradient K := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [planeCovectorGradient, sub_apply]

 theorem planeCovectorGradient_norm (L : EuclideanPlane →L[ℝ] ℝ) :
    ‖planeCovectorGradient L‖ = ‖L‖ := by
  have he : L = innerSL ℝ (planeCovectorGradient L) := plane_covector_of_basis L
  calc
    _ = ‖innerSL ℝ (planeCovectorGradient L)‖ := (innerSL_apply_norm ℝ (planeCovectorGradient L)).symm
    _ = ‖L‖ := congrArg norm he.symm

 theorem continuous_planeCovectorGradient : Continuous planeCovectorGradient :=
  continuous_planePair (continuous_id.clm_apply continuous_const)
    (continuous_id.clm_apply continuous_const)

 theorem localPairChainWitness_covector {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) (x : EuclideanPlane) :
    (localPairChainWitness hU hUf hu hv Wu Wv hΦ hB hC hΦb hΦd).weakGrad x =
      planeCovectorGradient ((fderiv ℝ Φ (planePair (u x) (v x))).comp
        (weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x))) := by
  rw [weakPairDifferential_chain, planeCovectorGradient_inner]
  exact localPairChainWitness_gradient hU hUf hu hv Wu Wv hΦ hB hC hΦb hΦd x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TranslatedPhysicalBarrier
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translating a physical barrier preserves its energy and derivative
bounds; the plateau and support move to the selected trace center. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 def translatedPhysicalBarrier (Φ : EuclideanPlane → ℝ) (c : EuclideanPlane) : EuclideanPlane → ℝ :=
    fun x => Φ (x-c)

 theorem translatedPhysicalBarrier_fderiv {Φ : EuclideanPlane → ℝ}
    (hΦ : Differentiable ℝ Φ) (c x : EuclideanPlane) :
    fderiv ℝ (translatedPhysicalBarrier Φ c) x = fderiv ℝ Φ (x-c) := by
  have h := (hΦ (x-c)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)
  change fderiv ℝ (fun y => Φ (y-c)) x = _
  simpa only [id_eq, Function.comp_def, ContinuousLinearMap.comp_id] using h.fderiv

 theorem translatedPhysicalBarrier_data {Φ : EuclideanPlane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ)
    {r R M₁ M₂ : ℝ} (hsR : tsupport Φ ⊆ ball 0 R)
    (hunit : ∀ x, Φ x ∈ Icc (0 : ℝ) 1) (hone : ∀ x ∈ ball 0 r, Φ x = 1)
    (hD : ∀ x, ‖fderiv ℝ Φ x‖ ≤ M₁)
    (hDD : ∀ x y, ‖fderiv ℝ Φ x-fderiv ℝ Φ y‖ ≤ M₂*‖x-y‖)
    (c : EuclideanPlane) :
    ContDiff ℝ ∞ (translatedPhysicalBarrier Φ c) ∧
      HasCompactSupport (translatedPhysicalBarrier Φ c) ∧
      tsupport (translatedPhysicalBarrier Φ c) ⊆ ball c R ∧
      (∀ x, translatedPhysicalBarrier Φ c x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball c r, translatedPhysicalBarrier Φ c x = 1) ∧
      (∀ x, ‖fderiv ℝ (translatedPhysicalBarrier Φ c) x‖ ≤ M₁) ∧
      (∀ x y, ‖fderiv ℝ (translatedPhysicalBarrier Φ c) x-
        fderiv ℝ (translatedPhysicalBarrier Φ c) y‖ ≤ M₂*‖x-y‖) := by
  have he : translatedPhysicalBarrier Φ c = Φ ∘ Homeomorph.addRight (-c) := by
    funext x
    change Φ (x-c) = Φ (x + -c)
    rw [sub_eq_add_neg]
  refine ⟨hΦ.comp (contDiff_id.sub contDiff_const), ?_, ?_, fun x => hunit _, ?_, ?_, ?_⟩
  · rw [he]
    exact hs.comp_homeomorph _
  · rw [he, tsupport_comp_eq_preimage]
    intro x hx
    have h := hsR hx
    change x + -c ∈ ball (0 : EuclideanPlane) R at h
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero] using h
  · intro x hx
    exact hone _ (by simpa only [mem_ball, dist_eq_norm, sub_zero] using hx)
  · intro x
    rw [translatedPhysicalBarrier_fderiv (hΦ.differentiable (by simp))]
    exact hD _
  · intro x y
    rw [translatedPhysicalBarrier_fderiv (hΦ.differentiable (by simp)),
      translatedPhysicalBarrier_fderiv (hΦ.differentiable (by simp))]
    simpa only [sub_sub_sub_cancel_right] using hDD (x-c) (y-c)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_HorizontalNullPair
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The companion trace pair with the ordinary horizontal coordinate.
The same proved level argument applies to the constant rotated homeomorphism. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def horizontalLinear : EuclideanPlane →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp euclideanPlaneCoordinates.toContinuousLinearMap

 @[simp] theorem horizontalLinear_apply (p : EuclideanPlane) : horizontalLinear p = p 0 := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCentering
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit disk automorphism used to move the marked endpoint to
the origin in a Jordan disk coordinate. -/

open Set Function Filter Metric
open scoped Topology ComplexConjugate

noncomputable section
namespace CircleDomainRigidity

def diskCentering (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

@[simp] theorem diskCentering_self (a : ℂ) : diskCentering a a = 0 := by
  simp only [diskCentering, sub_self, zero_div]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereJordanCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complex disk and measurable circle coordinates for a spherical
Jordan collar. -/

open Set Function Metric MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

def sphereJordanCoordinate (K : ℂ ≃ₜ ℂ) (x : Sphere) : ℂ := K.symm (finiteCoord x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundDiskReflection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spherical reflections in the assigned finite round disks. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

def roundDiskReflection (c : ℂ) (r : ℝ) (hr : 0 < r) : Sphere ≃ₜ Sphere :=
  let A := affineSphere (r:ℂ) c (by exact_mod_cast hr.ne')
  A.symm.trans (CannonSphereReflection.reflection.trans A)

lemma roundDiskReflection_involutive (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Involutive (roundDiskReflection c r hr) := by
  intro z
  dsimp [roundDiskReflection]
  rw [Homeomorph.symm_apply_apply,CannonSphereReflection.reflection_involutive,
    Homeomorph.apply_symm_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereCoefficient
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel complex coefficient fields on the concrete sphere, with an explicit
value at infinity. -/
open Set Function MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

local instance instBorelSpaceSphere_8_rffc8c3_1 : BorelSpace Sphere := ⟨rfl⟩
def sphereCoefficient (a : ℂ) (f : ℂ → ℂ) : Sphere → ℂ := fun p => p.elim a f

@[simp] lemma sphereCoefficient_coe (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    sphereCoefficient a f (z : Sphere)=f z := rfl

@[simp] lemma sphereCoefficient_infty (a : ℂ) (f : ℂ → ℂ) :
    sphereCoefficient a f ∞=a := rfl

def circleReflectionPhase (c z : ℂ) : ℂ :=
  if z=c then 1 else ((z-c)/(starRingEnd ℂ (z-c)))^2

def sphereReflectionPhase (c : ℂ) : Sphere → ℂ :=
  sphereCoefficient 1 (circleReflectionPhase c)

lemma roundDiskReflection_infty (c : ℂ) {r : ℝ} (hr : 0 < r) :
    roundDiskReflection c r hr ∞=(c : Sphere) := by
  change affineSphere (r:ℂ) c (by exact_mod_cast hr.ne')
    (CannonSphereReflection.reflection ∞)=(c : Sphere)
  rw [CannonSphereReflection.reflection_infty,affineSphere_coe]
  simp only [mul_zero,zero_add]

lemma roundDiskReflection_center (c : ℂ) {r : ℝ} (hr : 0 < r) :
    roundDiskReflection c r hr (c : Sphere)=∞ := by
  rw [←roundDiskReflection_infty c hr,roundDiskReflection_involutive c hr]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundReflectionCoefficient
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual norm-preserving coefficient transport for circular reflection. -/
open Set Function MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

local instance instBorelSpaceSphere_9_rffc8c3_1 : BorelSpace Sphere := ⟨rfl⟩
def roundReflectionCoefficient (c : ℂ) (p : Sphere) (a : ℂ) : ℂ :=
  sphereReflectionPhase c p * starRingEnd ℂ a

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalSmoothApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth principal maps whose actual densities converge strongly to a
specified compact-coefficient L2 solution. The common coefficient support
will give uniform exterior estimates for the maps. -/
open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

structure PrincipalSmoothApproximation (g : PlaneL2) (k R : ℝ) where
  coefficient : ℕ → SchwartzMap ℂ ℂ
  density : ℕ → SchwartzMap ℂ ℂ
  map : ℕ → ℂ ≃ₜ ℂ
  coefficient_compact : ∀ n, HasCompactSupport (coefficient n : ℂ → ℂ)
  coefficient_bound : ∀ n z, ‖coefficient n z‖ ≤ k
  coefficient_zero : ∀ n z, R+2 ≤ ‖z‖ → coefficient n z=0
  density_compact : ∀ n, HasCompactSupport (density n : ℂ → ℂ)
  values : ∀ n z, map n z=z+cauchyTransform (density n) z
  smooth : ∀ n, ContDiff ℝ ∞ (map n : ℂ → ℂ)
  inverse_smooth : ∀ n, ContDiff ℝ ∞ ((map n).symm : ℂ → ℂ)
  equation : ∀ n z, partialBar (map n) z=coefficient n z*partialZ (map n) z
  partials : ∀ n z, partialBar (map n) z=density n z ∧
    partialZ (map n) z=1+smoothBeurling (density n) z
  strong_density : Tendsto (fun n => (density n).toLp 2 (μ:=volume)) atTop (𝓝 g)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalWeakDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strong principal density limit supplies the actual directional weak
derivatives of the locally uniform homeomorphism limit. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

 def principalDirectionalCorrection (g : PlaneL2) (v : ℂ) : PlaneL2 :=
  v • beurling g + star v • g

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalSmoothLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the principal plane homeomorphism with the specified strong
L2 density. Retain the actual smooth approximants and both convergences
for the subsequent scalar transport application. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane

structure PrincipalMapLimit {g : PlaneL2} {k R : ℝ}
    (S : PrincipalSmoothApproximation g k R) where
  map : ℂ ≃ₜ ℂ
  index : ℕ → ℕ
  index_strict : StrictMono index
  forward : Tendsto (fun n => homeomorphMap (S.map (index n))) atTop
    (𝓝 (homeomorphMap map))
  inverse : Tendsto (fun n => homeomorphMap (S.map (index n)).symm) atTop
    (𝓝 (homeomorphMap map.symm))
  principal : Tendsto (fun z => map z-z) (Bornology.cobounded ℂ) (𝓝 0)
  weak : ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
    (∫ z, map z*fderiv ℝ (φ : ℂ → ℂ) z v) =
      -(∫ z, (v+principalDirectionalCorrection g v z)*φ z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.TwoArcs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Two points cut a Jordan curve into two arcs

Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points. This is the converse of
`IsJordanCurve.of_two_arcs`, and the harder direction.

The whole argument is carried by the loop's **parameters**; the circle never appears. Pull the
two points back to parameters `s` and `t` short of the finish — `parameter_before_finish`,
which replaces a parameter at the finish by the start, the only use the closing condition gets
— and order them, say `s < t`. Then the two pieces are what the loop makes of the parameters
*between* `s` and `t` and of the parameters *outside* them:

* the middle piece `f '' Icc s t` is a subarc, produced by `Subarc.lean`'s
  `isArcBetween_subarc`, whose injectivity hypothesis is confined to the traversed interval
  and so survives a loop;
* the outside piece `f '' Icc 0 s ∪ f '' Icc t 1` is two end intervals glued where the loop
  closes up, produced by `Concatenate.lean`'s `IsArcBetween.concatenate`.

That asymmetry — one subarc and one concatenation — is inherent to a parameter interval with
a seam in it, and is not worth fighting. It costs one case split, at `s = 0`, where the front
interval degenerates to a point that the back piece already carries at its far end.

Both halves of the conclusion are then facts about intervals of reals. Covering is the
three-way split of `[0,1]` around two parameters, which is the linearity of the order and
nothing else. Meeting is injectivity off the finish, applied on each of the three pieces; the
one case that needs the loop rather than an arc is an outside parameter *at* the finish, which
carries the same point as the start and so lands back on `s`.

## Blueprint

* `lem:jordan-circle` — "any two distinct points of `C` divide it into two simple arcs having
  exactly those points in common". `IsJordanCurve.two_arcs` is that clause, proved directly
  from the parametrisation instead of through the model curve, so it does not wait on the
  loop-to-circle bridge.
* `IsLoop.two_arcs_at_parameters` — the parameter-level form the clause is assembled from.
-/

open Set unitInterval

namespace Schoenflies

namespace IsLoop

variable {s t : ℝ}

/-! ### Parameters short of the finish

A loop is injective on `[0, 1)` only, so every statement below has to keep its parameters
away from `1`. These two lemmas are the interface to that: one says injectivity holds as soon
as neither parameter is the finish, the other says the finish can always be avoided. -/

/-! ### The three pieces of parameters

Two parameters `s < t` cut `[0, 1]` into the middle interval `[s, t]` and the two end
intervals `[0, s]` and `[t, 1]`. Each piece needs the loop to be injective on its own
parameters. On the middle and the front that is injectivity off the finish, since neither
contains it; the back piece *does* contain the finish, and there the extra argument is that
the only other parameter carrying `f 1` is the start, which lies strictly before `t`. -/

theorem front_subset_I (hs : s ∈ I) : Icc 0 s ⊆ I := Icc_subset_Icc le_rfl hs.2

theorem middle_subset_I (hs : s ∈ I) (ht : t ∈ I) : Icc s t ⊆ I := Icc_subset_Icc hs.1 ht.2

theorem back_subset_I (ht : t ∈ I) : Icc t 1 ⊆ I := Icc_subset_Icc ht.1 le_rfl

/-! ### The three pieces are arcs -/

/-! ### The outside piece

The parameters outside `[s, t]` are two intervals, glued at the point where the loop closes
up: walk from `t` to the finish, then from the start to `s`. When `s` *is* the start the front
interval degenerates to a single parameter, and the outside is the back piece alone — its far
end already carries the point the front piece would have contributed. -/

/-! ### Covering, and where the pieces meet -/

/-- The parameter interval splits three ways around any two of its points. Linearity of the
order, and nothing else — the split does not even need the two points ordered, since when they
are not the middle interval is empty and the two end intervals already overlap. -/
theorem parameters_split (hs : s ∈ I) (ht : t ∈ I) :
    I = Icc s t ∪ (Icc 0 s ∪ Icc t 1) := by
  ext x
  constructor
  · rintro ⟨h0, h1⟩
    rcases le_total x s with h | h
    · exact Or.inr (Or.inl ⟨h0, h⟩)
    · rcases le_total x t with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (Or.inr ⟨h', h1⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hs.1.trans h1, h2.trans ht.2⟩
    · exact ⟨h1, h2.trans hs.2⟩
    · exact ⟨ht.1.trans h1, h2⟩

/-! ### The two arcs, at chosen parameters -/

end IsLoop

/-! ### The theorem -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Realization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-! ## Clean pieces

The overlay of `Schoenflies/OverlayGraph.lean`, stripped of the graph. All that is wanted from
it is a finite list of segments occupying the curve whose interiors are pairwise disjoint and
none of whose ends is interior to any of them — the geometric content of `lem:polygonal-overlay`
with the combinatorics left out. -/

/-! ## The gaps between the parameters

The loop's parameters at which it visits an end of a piece form a finite subset of `[0, 1)`
containing `0`. Listed in increasing order they cut `[0, 1)` into gaps, one per piece; the last
gap runs to `1`, where the loop closes. This section is pure order theory on `ℝ`. -/

section Gaps

variable {n : ℕ} {T : Finset ℝ} (hcard : T.card = n)

/-- The `i`-th parameter, in increasing order. -/
noncomputable def par (T : Finset ℝ) (hcard : T.card = n) (i : Fin n) : ℝ :=
  T.orderEmbOfFin hcard i

/-- The right end of the `i`-th gap: the next parameter, or `1` for the last gap. -/
noncomputable def parNext (T : Finset ℝ) (hcard : T.card = n) (i : Fin n) : ℝ :=
  if h : (i : ℕ) + 1 < n then T.orderEmbOfFin hcard ⟨(i : ℕ) + 1, h⟩ else 1

theorem par_mem (i : Fin n) : par T hcard i ∈ T := T.orderEmbOfFin_mem hcard i

theorem par_lt_par {i j : Fin n} (h : i < j) : par T hcard i < par T hcard j :=
  (T.orderEmbOfFin hcard).strictMono h

theorem par_lt_iff {i j : Fin n} : par T hcard i < par T hcard j ↔ i < j :=
  (T.orderEmbOfFin hcard).lt_iff_lt

theorem par_le_par {i j : Fin n} (h : i ≤ j) : par T hcard i ≤ par T hcard j :=
  (T.orderEmbOfFin hcard).monotone h

theorem exists_par_eq {s : ℝ} (hs : s ∈ T) : ∃ i : Fin n, par T hcard i = s := by
  have := T.range_orderEmbOfFin hcard
  rw [Set.ext_iff] at this
  exact (this s).2 hs

variable (hT : ∀ s ∈ T, s ∈ Ico (0 : ℝ) 1) (h0 : (0 : ℝ) ∈ T)
include hcard hT h0

omit hT in
theorem par_card_pos : 0 < n := by
  rw [← hcard]
  exact Finset.card_pos.2 ⟨0, h0⟩

/-- The first parameter is `0`: the loop is at a vertex when it starts. -/
theorem par_zero : par T hcard ⟨0, par_card_pos hcard h0⟩ = 0 := by
  rw [par, Finset.orderEmbOfFin_zero hcard (par_card_pos hcard h0)]
  exact le_antisymm (Finset.min'_le _ _ h0)
    (Finset.le_min' _ _ _ fun s hs => (hT s hs).1)

omit h0 in
theorem parNext_le_one (i : Fin n) : parNext T hcard i ≤ 1 := by
  rw [parNext]
  split_ifs with hi
  · exact le_of_lt (hT _ (T.orderEmbOfFin_mem hcard _)).2
  · exact le_refl 1

omit h0 in
theorem par_lt_parNext (i : Fin n) : par T hcard i < parNext T hcard i := by
  rw [parNext]
  split_ifs with hi
  · exact par_lt_par hcard (by exact Fin.mk_lt_mk.2 (Nat.lt_succ_self _) : i < ⟨(i : ℕ) + 1, hi⟩)
  · exact (hT _ (par_mem hcard i)).2

omit hT h0 in
/-- No parameter lies strictly inside a gap. -/
theorem notMem_of_mem_gap {i : Fin n} {s : ℝ} (hs : s ∈ Ioo (par T hcard i) (parNext T hcard i)) :
    s ∉ T := by
  intro hsT
  obtain ⟨j, rfl⟩ := exists_par_eq hcard hsT
  have hij : i < j := (par_lt_iff hcard).1 hs.1
  rw [parNext] at hs
  split_ifs at hs with hi
  · exact absurd hs.2 (not_lt.2 (par_le_par hcard (by exact Fin.mk_le_of_le_val hij)))
  · exact absurd j.isLt (by omega)

omit hT h0 in
/-- Distinct gaps are disjoint. -/
theorem gap_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Ioo (par T hcard i) (parNext T hcard i))
      (Ioo (par T hcard j) (parNext T hcard j)) := by
  -- One of the two comes first; its right end is at most the other's left end.
  have key : ∀ a b : Fin n, a < b → parNext T hcard a ≤ par T hcard b := by
    intro a b hab
    rw [parNext]
    split_ifs with ha
    · exact par_le_par hcard (Fin.mk_le_of_le_val hab)
    · exact absurd b.isLt (by omega)
  rw [Set.disjoint_left]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact fun x hx hx' => absurd (lt_of_lt_of_le hx.2 (key i j hlt)) (not_lt.2 hx'.1.le)
  · exact fun x hx hx' => absurd (lt_of_lt_of_le hx'.2 (key j i hlt)) (not_lt.2 hx.1.le)

omit h0 in
theorem gap_subset_Ico (i : Fin n) :
    Ioo (par T hcard i) (parNext T hcard i) ⊆ Ico (0 : ℝ) 1 := fun _ hs =>
  ⟨le_of_lt (lt_of_le_of_lt (hT _ (par_mem hcard i)).1 hs.1),
    lt_of_lt_of_le hs.2 (parNext_le_one hcard hT i)⟩

omit h0 in
theorem gapClosure_subset_I (i : Fin n) :
    Icc (par T hcard i) (parNext T hcard i) ⊆ I := by
  intro s hs
  exact ⟨le_trans (hT _ (par_mem hcard i)).1 hs.1, le_trans hs.2 (parNext_le_one hcard hT i)⟩

/-- **The gaps cover `[0, 1)` minus the parameters.** The gap containing `s` starts at the
largest parameter below `s`. -/
theorem exists_mem_gap {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (hsT : s ∉ T) :
    ∃ i : Fin n, s ∈ Ioo (par T hcard i) (parNext T hcard i) := by
  classical
  have hn : 0 < n := par_card_pos hcard h0
  -- The gap containing `s` starts at the largest parameter below it.
  obtain ⟨i₀, hi₀le, hi₀max⟩ : ∃ i₀ : Fin n, par T hcard i₀ ≤ s ∧
      ∀ j : Fin n, par T hcard j ≤ s → j ≤ i₀ := by
    have hSne : (Finset.univ.filter fun i : Fin n => par T hcard i ≤ s).Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        by rw [par_zero hcard hT h0]; exact hs.1⟩⟩
    exact ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hSne)).2,
      fun j hj => Finset.le_max' _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩
  refine ⟨i₀, lt_of_le_of_ne hi₀le fun he => hsT (he ▸ par_mem hcard _), ?_⟩
  rw [parNext]
  split_ifs with hi
  · by_contra hcon
    push Not at hcon
    exact absurd (hi₀max ⟨(i₀ : ℕ) + 1, hi⟩ hcon)
      (not_le.2 (Fin.lt_def.2 (Nat.lt_succ_self _)))
  · exact hs.2

end Gaps

/-! ## From a clean presentation to a cyclic vertex list

The loop reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the loop reaches them, are the cyclic
vertex list of a `PrePolygon` whose edges are the pieces. -/

/-! ## The realization theorem -/

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

end Schoenflies
end

section
-- module Solutions.Q146_CD.Jordan
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Jordan curve theorem

The complement of a Jordan curve has exactly two regions, one bounded and one unbounded, and
both have the curve as their boundary. That is `Schoenflies.IsSeparating C` — the very
predicate `Schoenflies/CrosscutCells.lean` introduces and
`Schoenflies.ClosedPolygon.polygonal_jordan` establishes for a polygon — so every consumer of
the polygonal case applies verbatim to the general one, `inside C` and `outside C` included.

Everything here takes one hypothesis, carried explicitly through every statement
that needs it:

    harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ

which is `thm:arc-complement`, the complement of a simple arc is connected. Nothing else is
assumed; in particular no part of `thm:jordan` itself is.

## The two theorems

`lem:accessible-dense` (`Schoenflies.accessible_dense`) says the points of `C` reachable from a
fixed `x ∉ C` by a polygonal arc meeting `C` only at its endpoint are dense in `C`. Its proof
is the blueprint's: delete a small open subarc `J₀`, leaving a simple arc whose complement is
connected by `harc`; join `x` there to a point of another component of `Cᶜ`; the joining chain
must cross `C`, and it can only do so inside `J₀`.

`thm:jordan` (`Schoenflies.IsJordanCurve.isSeparating`) then needs "at most two components",
which is `Schoenflies.not_three_components`, and the boundary clause, which is
`lem:accessible-dense` again: an accessible point is a limit of the region it is accessible
from, so `C` lies in the closure of each region and, being disjoint from both, in each
frontier.

## Three places where this departs from the blueprint's route

**The first meeting is taken on a vertex list, not on a parametrisation.**
`Schoenflies.exists_first_meeting` recurses on the list: on the first segment the first hit is
the infimum of the hitting parameters, and if the first segment misses the obstacle it is
swallowed by the component of the start and the recursion moves on. It returns the *initial
chain*, so both consumers — the accessibility of the meeting point, and the third branch of a
tripod — read off the same lemma.

**The tripod is built without a graph.** The blueprint overlays the three access arcs
(`lem:polygonal-overlay`), takes a minimal connected spanning subgraph, and extracts its unique
degree-three vertex by `lem:three-leaf-tree`. `Schoenflies.exists_tripod` instead joins the
first two terminals by a crosscut (`lem:accessible-endpoints`), runs a chain from the third
terminal to that crosscut, and takes the first meeting: that meeting point *is* the branch
vertex, and cutting the crosscut there (`IsArcBetween.exists_split`) gives the other two
branches. Neither `Schoenflies.polygonal_overlay` nor `Graph.IsTree.three_leaves` is used.

**The nine terminals are chosen in nine prescribed parameter windows.** The blueprint chooses
them distinct — proving that a dense set meets a nonempty relatively open subarc infinitely
often — and then *orders* the three on each closed arc `Q_j` to find the middle one `y_j`.
`Schoenflies.exists_windows` supplies nine pairwise separated windows inside `(0,1)`, in three
blocks of three; distinctness is then disjointness of the windows, the middle terminal of a
block is always the one with row index `1`, and no order on the curve is ever constructed. The
blueprint's `Q_j` never appears: only the parameter blocks `[t 0 j, t 2 j]` do.

## Blueprint

* `Schoenflies.exists_first_meeting_segment`, `Schoenflies.exists_first_meeting`,
  `Schoenflies.exists_arc_to_first_meeting`, `Schoenflies.polyAccessible_first_meeting` — the
  first-meeting machinery `lem:accessible-dense` and `thm:jordan` both run on. General enough
  to be hoisted if a second module needs it.
* `Schoenflies.PolyAccessible.mem_closure` — an accessible point of `∂Ω` lies in `closure Ω`.
* `Schoenflies.IsLoop.compl_openArc` — `lem:jordan-circle` in the form used here: the curve
  minus an open subarc is the complementary closed arc.
* `Schoenflies.exists_polyAccessible_openArc`, `Schoenflies.accessible_dense` —
  `lem:accessible-dense`, in the parameter form the proof produces and in the closure form.
* `Schoenflies.exists_tripod` — the three internally disjoint branches of the blueprint's
  `T_i`, at the H5 step of `thm:jordan`.
* `Schoenflies.exists_windows`, `Schoenflies.uIcc_inter_uIcc_mid` — the choice of the nine
  terminals and the middle-point bookkeeping that replaces "order `p_{1j}, p_{2j}, p_{3j}`
  along `Q_j`".
* `Schoenflies.not_three_components` — the `K(3,3)` half of `thm:jordan`, through
  `Graph.IsArcK33.elim` (`cor:k33-subdivision`).
* `Schoenflies.subset_closure_of_accessible_dense`, `Schoenflies.IsJordanCurve.isSeparating` —
  `thm:jordan`.
-/

open Bornology Metric Set unitInterval

namespace Schoenflies

/-! ### The first meeting of a polygonal chain with a closed set

A chain that starts off a closed obstacle `S` and eventually hits it has a *first* hit, and
the piece of the chain before it never leaves the component of `U` its start lies in. This is
the only reason `lem:accessible-dense` produces an *accessible* point rather than merely a
point of the curve, and it is proved by structural recursion on the vertex list: on the first
segment the first hit is the infimum of the hitting parameters, and if the first segment
misses `S` the segment itself is swallowed by the component and the recursion moves on. -/

/-! ### An accessible point is a limit of the region

The half of `thm:jordan`'s boundary clause that `lem:accessible-dense` supplies: an accessible
point of the curve is in the closure of the region it is accessible from. The access chain is
connected and carries a point of the region, so the accessible point is not isolated on it. -/

/-! ### The curve with an open subarc deleted

`lem:jordan-circle`'s "two points cut the curve into two arcs" in the form
`lem:accessible-dense` consumes it: the complement *in the curve* of a relatively open subarc
is one closed arc. The proof is the parameter bookkeeping of `Schoenflies/TwoArcs.lean` — no
new topology. -/

/-! ### Density of accessible points, `lem:accessible-dense`

The blueprint's proof verbatim: shrink the given relatively open arc to one whose closure is
inside it, delete it from the curve to leave a simple arc, join `x` to a point of another
component in the (connected) complement of that arc by a polygonal chain, and take the first
meeting of the chain with the curve.

The shrinking step is done on parameters. Instead of "an open arc `J₀` with closure inside
`J`" the statement below takes the open subarc `f '' Ioo a b` with `0 < a < b < 1`, which is
already strictly inside the parameter interval; every relatively open piece of the curve
contains such a subarc (`Schoenflies.basic_piece_inside_ball` supplies one inside any ball),
and that is all the blueprint's `J₀` is for. -/

/-! ### The tripod at a component

The blueprint builds the three internally disjoint branches from `x_i` to the three terminals
by overlaying the three access arcs, taking a minimal connected spanning subgraph, and reading
off its unique degree-three vertex (`lem:three-leaf-tree`). The construction below reaches the
same object without a graph: join the first two terminals by a *crosscut* — a simple polygonal
arc meeting the curve exactly at its two endpoints (`lem:accessible-endpoints` in crosscut
form) — then run a chain from the third terminal into the region and on to a point of that
crosscut, and take its **first meeting** with the crosscut. That meeting point is the branch
vertex; cutting the crosscut there (`IsArcBetween.exists_split`) supplies the other two
branches.

The output is the same three internally disjoint arcs, with the same two properties every
later step uses: each meets the curve only at its terminal, and two of them meet only at the
branch vertex. -/

/-! ### Nine parameter windows

The blueprint chooses the nine terminals `p_{ij}` distinct and then *orders* the three on each
arc `Q_j` to find the middle one `y_j`. Choosing them in nine prescribed, pairwise separated
parameter windows does both jobs at once: distinctness is disjointness of the windows, and the
middle one is always the terminal of the middle index. No order on the curve is ever
constructed.

The windows are `((6j + 2i + 2)/24, (6j + 2i + 3)/24)`, which for `i, j < 3` are nine disjoint
intervals inside `(0, 1)`, ordered lexicographically by `(j, i)`. -/

/-- Nine parameter windows strictly inside `(0, 1)`, in blocks of three: increasing the row
index `i` within a block, or the block index `j`, moves past the end of the current window. -/
theorem exists_windows : ∃ w : Fin 3 → Fin 3 → ℝ,
    (∀ i j, 0 < w i j) ∧ (∀ i j, w i j + 1 / 24 < 1) ∧
      (∀ i j k l : Fin 3, (j = l ∧ i.val < k.val) ∨ j.val < l.val →
        w i j + 1 / 24 ≤ w k l) := by
  refine ⟨fun i j => (6 * (j.val : ℝ) + 2 * (i.val : ℝ) + 2) / 24, ?_, ?_, ?_⟩
  · intro i j
    have h1 : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    linarith
  · intro i j
    have h1 : ((j.val : ℝ)) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
    have h2 : ((i.val : ℝ)) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 i.isLt
    linarith
  · rintro i j k l (⟨rfl, hik⟩ | hjl)
    · have h : ((i.val : ℝ)) + 1 ≤ (k.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hik
      linarith
    · have h : ((j.val : ℝ)) + 1 ≤ (l.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hjl
      have h1 : ((i.val : ℝ)) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 i.isLt
      have h2 : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
      linarith

/-- Two closed intervals sharing the endpoint `m`, one on each side of it, meet only there. -/
theorem uIcc_inter_uIcc_mid {r s m : ℝ} (hr : r ≤ m) (hs : m ≤ s) :
    uIcc r m ∩ uIcc s m ⊆ {m} := by
  rw [uIcc_of_le hr, uIcc_of_ge hs]
  rintro z ⟨⟨-, h2⟩, ⟨h3, -⟩⟩
  exact le_antisymm h2 h3

/-! ### At most two components

The heart of `thm:jordan`. Three components would give three tripods, whose nine branches,
extended along the curve to the three middle terminals, are a plane `K(3,3)` subdivision —
excluded by `cor:k33-subdivision` (`Graph.IsArcK33.elim`). -/

/-! ### The Jordan curve theorem

Stated as `IsSeparating C`, the predicate `Schoenflies/CrosscutCells.lean` introduces and
`Schoenflies.ClosedPolygon.polygonal_jordan` establishes in the polygonal case. Unfolding it,
that is exactly the blueprint's statement: `inside C` and `outside C` are each a single region,
one bounded and one unbounded (`IsSeparating.isBounded_inside`,
`IsSeparating.not_isBounded_outside`), and both have `C` as boundary. Every consumer written
against the polygonal case therefore applies verbatim. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolyArcRealize
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

section SkipIdx

variable {i k : ℕ}

/-- The index map that skips over vertex `i + 1`. -/
def skipIdx (i k : ℕ) : ℕ := if k ≤ i then k else k + 1

theorem skipIdx_of_le (h : k ≤ i) : skipIdx i k = k := if_pos h

theorem skipIdx_of_lt (h : i < k) : skipIdx i k = k + 1 := if_neg (by omega)

theorem skipIdx_injective (i : ℕ) : Function.Injective (skipIdx i) := by
  intro k l h
  simp only [skipIdx] at h
  split_ifs at h <;> omega

theorem skipIdx_succ (h : k ≠ i) : skipIdx i (k + 1) = skipIdx i k + 1 := by
  simp only [skipIdx]
  split_ifs <;> omega

theorem skipIdx_ne_left (h : k ≠ i) : skipIdx i k ≠ i := by
  simp only [skipIdx]; split_ifs <;> omega

theorem skipIdx_ne_right (i k : ℕ) : skipIdx i k ≠ i + 1 := by
  simp only [skipIdx]; split_ifs <;> omega

end SkipIdx

/-! ## Arcs before normalization

`PreArc` is `PolyArc` with the `corner` field removed, exactly as `Schoenflies.PrePolygon` is
`Schoenflies.ClosedPolygon` with it removed. Realization produces one of these; normalization
turns it into a `PolyArc`. -/

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
-- module Solutions.Q146_CD.Graph_TwoConnected
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem mem_deleteVerts_singleton : y ∈ V(G.deleteVerts {x}) ↔ y ∈ V(G) ∧ y ≠ x := by
  simp

theorem mem_deleteVerts_singleton_of_ne (hy : y ∈ V(G)) (hyx : y ≠ x) :
    y ∈ V(G.deleteVerts {x}) :=
  mem_deleteVerts_singleton.2 ⟨hy, hyx⟩

/-- Deleting the same vertices from both sides of an inclusion keeps it. -/
theorem deleteVerts_mono (h : G ≤ H) (X : Set α) : G.deleteVerts X ≤ H.deleteVerts X where
  vertexSet_mono := by
    simp only [vertexSet_deleteVerts]
    exact sdiff_subset_sdiff_left h.vertexSet_mono
  isLink_mono e x y hl := by
    rw [deleteVerts_isLink] at hl ⊢
    exact ⟨h.isLink_mono hl.1, hl.2.1, hl.2.2⟩

/-! ### Walks across a vertex deletion -/

/-! ### Cut vertices -/

/-! ### At least three vertices -/

/-! ### Two-connectivity -/

/-! ### The union of two graphs -/

end Graph
end

section
-- module Solutions.Q146_CD.CombinatorialInvariance
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace Graph

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v x : α} {W : List β}

/-- Deleting a vertex commutes with an injective relabelling of the vertices. -/
theorem map_deleteVerts_singleton (hf : InjOn f V(G)) (hx : x ∈ V(G)) :
    (G.map f).deleteVerts {f x} = (G.deleteVerts {x}).map f := by
  refine Graph.ext ?_ ?_
  · rw [vertexSet_deleteVerts, vertexSet_map, vertexSet_map, vertexSet_deleteVerts]
    rw [hf.image_sdiff_subset (Set.singleton_subset_iff.2 hx), Set.image_singleton]
  · intro e a b
    rw [deleteVerts_isLink]
    simp only [map_isLink, Relation.map_apply, deleteVerts_isLink, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨p, q, hpq, rfl, rfl⟩, hp, hq⟩
      exact ⟨p, q, ⟨hpq, fun h => hp (by rw [h]), fun h => hq (by rw [h])⟩, rfl, rfl⟩
    · rintro ⟨p, q, ⟨hpq, hp, hq⟩, rfl, rfl⟩
      exact ⟨⟨p, q, hpq, rfl, rfl⟩, fun h => hp (hf hpq.left_mem hx h),
        fun h => hq (hf hpq.right_mem hx h)⟩

/-- An injective relabelling can be undone: `Function.invFunOn` inverts it on the vertex set. -/
theorem map_map_invFunOn [Nonempty α] (hf : InjOn f V(G)) :
    (G.map f).map (Function.invFunOn f V(G)) = G := by
  have key : G.map (Function.invFunOn f V(G) ∘ f) = G.map id :=
    map_eq_of_eqOn fun z hz => hf.leftInvOn_invFunOn hz
  rw [map_map, key, map_id]

/-! ### The point set of a subgraph -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_RelativeEar
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The relative ear decomposition

`lem:relative-ear`: *if `H` is a 2-connected subgraph of a finite 2-connected graph `G`, then
`G` is obtained from `H` by repeatedly adding paths whose distinct endpoints are already
present and whose internal vertices are new.*

Two things are delivered, and they are different in kind.

* `Graph.IsTwoConnected.relative_ear_exists` — the **relative** ear: the blueprint's own
  construction, through a component of `G - V(K)`, which is what makes the internal vertices
  new. `Graph.IsTwoConnected.ear_exists` in `Schoenflies/Graph/Ear.lean` finds *an* ear by a
  crossing walk, but says nothing about where the ear's interior lies — its path may run back
  and forth through the subgraph. That is enough to make the subgraph grow; it is **not**
  enough for the consumers, which need "whose internal vertices are new" verbatim (the ear's
  interior must be disjoint from the current skeleton, so that it lies in one current face).
* `Graph.IsTwoConnected.ear_decomposition` — the **iterated** form, as an induction principle.
  `Graph.IsTwoConnected.grows_by_ear` is deliberately one step; the finiteness induction the
  blueprint hides behind "finiteness terminates the process" is done here.

## Why the relative form is a different theorem

The blueprint's proof does not walk out of the subgraph and hope. It looks at a component `L`
of `G - V(H₀)`: if `L` has a vertex it has two distinct neighbours in `H₀`, since otherwise
its unique neighbour would be a cut vertex of `G`, and a shortest path through `L` between two
such neighbours is an ear. That path meets `V(H₀)` only at its two ends **by construction**,
because its interior was built inside `G - V(H₀)`.

All of that is already proved: `Graph.IsTwoConnected.exists_path_through_component` in
`Schoenflies/Graph/Component.lean` packages the component argument and the path through it.
What is left here is to feed it `S = V(K)` — the two distinct vertices of `S` it asks for are
two of the three that a 2-connected `K` has — and to read its "every edge has an end outside
`S`" as "no edge of the ear is an edge of `K`".

The degenerate branch is the blueprint's second sentence: if every vertex of `G` is already
present, a missing edge is an ear of length one, and it has no internal vertex at all. As in
`Graph.IsTwoConnected.ear_exists`, that branch — and only that branch — needs `G` to be
loopless: a loop added to a 2-connected graph leaves it 2-connected, and no ear between
*distinct* endpoints can supply it.

## The termination measure

Edges, not vertices: `(E(G) \ E(B)).ncard`, which is finite because `G` is. Every ear
contributes at least one edge that `B` did not have — in the relative form *every* edge of the
ear is new, since each has an end outside `V(B)` — so the measure strictly drops, and the
process stops exactly when `B = G`. The stopping step is `Graph.eq_of_le_of_subset_subset`: a
subgraph with all the vertices and all the edges is the graph.

Note that the measure never needs to see a vertex. It is tempting to stop when `E(B) = E(G)`
and argue that a connected `G` has no isolated vertex; that is true but needs the degree
theory, and is unnecessary: if `V(B) ≠ V(G)` the ear that the first branch produces has an
edge outside `E(B)`, so the measure was not zero after all.

## One import that looks wrong

`Schoenflies/Graph/Tree.lean` is imported for a single two-line fact, `Graph.IsPath.ne_nil` —
a path between distinct vertices has an edge — which happens to live there. Nothing else in
this file has anything to do with trees. The honest fix is for the integrator to hoist
`Graph.IsPath.ne_nil` into `Schoenflies/Graph/Walk.lean`, where it belongs, and drop the
import; it is not restated here.

## What the induction principle gives a consumer

`motive G`, from `motive K` and one step. The step is handed the ear in full — the path `D` of
`G`, its distinct ends in `V(B)`, and the freshness of its interior — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`, and must produce `motive (B.union (G.pathGraphOf a D))`.
That is exactly the shape of the induction in `lem:face-cycles` ("suppose it holds for the
current graph and add the next geometric ear") and of the finite transfer of Part II.

## Blueprint

* `Graph.IsTwoConnected.relative_ear_exists` — `lem:relative-ear`, the ear itself: "a shortest
  path through `L` between two such neighbours is an ear", plus "if all vertices are already
  present, add a missing edge as an ear of length one".
* `Graph.IsTwoConnected.relative_grows_by_ear` — the same, glued on: one step of "`G` is
  obtained from `H` by repeatedly adding paths".
* `Graph.IsTwoConnected.ear_decomposition` — `lem:relative-ear` in full, including
  "finiteness terminates the process", as an induction principle.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G K B : Graph α β} {a b x y : α} {e f : β} {D : List β}

/-! ### Two facts about a subgraph inclusion

Both are general and neither is in `Schoenflies/Graph/Walk.lean`; the integrator may want to
hoist them. -/

/-- **An edge of a subgraph has its ends in the subgraph**, even when the incidence is only
known in the big graph. This is what turns "every edge of the ear has an end outside `V(K)`"
into "no edge of the ear is an edge of `K`". -/
theorem mem_vertexSet_of_inc_of_mem_edgeSet (hKG : K ≤ G) (hf : f ∈ E(K)) (h : G.Inc f y) :
    y ∈ V(K) :=
  ((hKG.inc_congr hf).2 h).vertex_mem

/-- **A subgraph with all the vertices and all the edges is the graph.** The termination
condition of the ear process. -/
theorem eq_of_le_of_subset_subset (hKG : K ≤ G) (hV : V(G) ⊆ V(K)) (hE : E(G) ⊆ E(K)) :
    K = G :=
  le_antisymm hKG ((Compatible.of_ge hKG).le_iff.2 ⟨hV, hE⟩)

/-! ### The relative ear -/

/-! ### Reading the enlarged graph

Two unfoldings a consumer of the induction principle below needs immediately, since the step's
conclusion is about `B.union (G.pathGraphOf a D)`. Both are immediate from the simp lemmas of
`Schoenflies/Graph/TwoConnected.lean` and `Schoenflies/Graph/PathGraph.lean`; they are here
only so that no consumer has to rediscover which two to combine. -/

/-! ### Iterating: the decomposition itself -/

end Graph
end

section
-- module Solutions.Q146_CD.SquareCycle
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The subdivided boundary of a square is a cycle

`Schoenflies.SquaresTwoConnected`, the last hypothesis between this library and
`thm:jordan`, discharged.

## What has to be built

`Schoenflies.squareGraph pieces points c r` is the part of a polygonal overlay lying on the
boundary of the axis-parallel square of `ℓ^∞`-radius `r` about `c`, when the four sides of that
square are among the overlay's source segments.  It is the subdivided boundary of the square,
so it is a cycle, and `Graph.IsLongCycle.isTwoConnected` finishes.  What is missing on `main`
is the **cyclic order** of the cut points: the graph is presented as a set of edges, with
nothing saying which edge follows which.

## The route

One real-valued coordinate does the whole of it.  `Schoenflies.sqCoord c r` is the *perimeter
coordinate*: the distance travelled from the north-east corner going counterclockwise round the
boundary, a number in `[0, 8r)`.  It is affine on each side, and it is the ordering tool of
`Schoenflies/SegmentOrder.lean` — distance from the side's first corner — with an offset.

* `Graph.IsIncWalk` is a walk along which a chosen real function strictly increases.  Such a
  walk is automatically a **path** (`Graph.IsIncWalk.isPath`): the freshness clause of
  `Graph.IsPath` says the vertex a step departs from is not visited later, and a vertex visited
  later has a strictly larger value.  This is the only place where "the cut points are in
  order" is turned into a combinatorial statement, and it replaces every argument about
  distinctness of vertices.
* `Schoenflies.exists_incWalk_of_chain` is the one-dimensional heart: a finite family of
  nondegenerate segments inside one ambient segment `[a, b]`, with pairwise disjoint interiors,
  with every end of every one of them interior to none of them, and covering `[a, b]`, is a
  **chain** from `a` to `b` — an `IsIncWalk` for the coordinate `dist a ·` whose edge list is
  exactly the family.  The induction is on the number of segments, and the step is
  `Schoenflies.exists_next_piece`: the piece leaving the current point is the one covering a
  point just beyond it, "just" being measured by the least end-coordinate strictly ahead.
* The four sides are chained separately and concatenated.  The concatenation is a closed walk
  at the north-east corner, so its last edge is split off (`Graph.IsIncWalk.split_last`) and
  becomes the distinguished edge of `Graph.IsCycleThrough`.

## Blueprint

* `Schoenflies.squaresTwoConnected` — the hypothesis `Schoenflies.SquaresTwoConnected` of
  `thm:arc-complement`, discharged.  In the blueprint this is the unstated step of
  "it follows inductively from `lem:union-two-connected` that `Γ_i` is 2-connected": the
  induction starts from one subdivided square boundary, and that it is a cycle is taken for
  granted there.
* `Schoenflies.exists_isLongCycle_squareGraph` — the cycle itself, with the clause that makes
  it usable: the cycle graph **is** `squareGraph`, not merely a subgraph of it.  A consumer
  wanting the boundary cycle of a square as an object, rather than 2-connectedness, takes it
  from here.
* `Schoenflies.exists_incWalk_insideEdges` — the subdivision of one source segment of a
  polygonal overlay, as a **path**.  `Schoenflies/SquareMeshConnected.lean` names exactly this
  as the theorem missing from `main` that blocks `prop:anchored-square-mesh` from being carried
  over to `Schoenflies.squareMesh`.  Its own ground is `Schoenflies.exists_incWalk_of_chain`,
  which knows nothing about overlays either.
* `Graph.IsIncWalk` — no blueprint statement; it is the device that makes
  `lem:polygonal-overlay`'s cut points into an ordered cycle.
-/

open Metric Set
open scoped Graph

/-! ## Part 1: a walk along which a real function increases -/

namespace Graph

variable {α β : Type*} {G H : Graph α β} {f g : α → ℝ} {u v w x : α} {e : β}
  {W W₁ W₂ : List β}

/-- **A walk along which `f` strictly increases.**  The point of the definition is
`Graph.IsIncWalk.isPath`: a walk that cannot come back is a path, and no argument about the
distinctness of the vertices has to be made anywhere else. -/
inductive IsIncWalk (G : Graph α β) (f : α → ℝ) : α → List β → α → Prop
  /-- The empty walk, at a vertex of the graph. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsIncWalk f x [] x
  /-- A step to a vertex of strictly larger value, followed by an increasing walk. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hf : f u < f w)
      (hW : G.IsIncWalk f w W v) : G.IsIncWalk f u (e :: W) v

namespace IsIncWalk

theorem append (h₁ : G.IsIncWalk f u W₁ w) (h₂ : G.IsIncWalk f w W₂ v) :
    G.IsIncWalk f u (W₁ ++ W₂) v := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hl hf _ ih => exact .cons hl hf (ih h₂)

/-- Shifting the function by a constant changes nothing.  Each side of the square carries the
distance from its own first corner; the shifts are what glue the four into one coordinate. -/
theorem const_add (h : G.IsIncWalk f u W v) (t : ℝ) :
    G.IsIncWalk (fun x => t + f x) u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl hf _ ih => exact .cons hl (by linarith) ih

end IsIncWalk

end Graph

/-! ## Part 2: a tiling of one segment is a chain

Everything here happens along a single ambient segment `[a, b]`, and the coordinate is the one
`Schoenflies/SegmentOrder.lean` supplies: the distance from `a`.  A finite family of
nondegenerate pieces inside `[a, b]`, with disjoint interiors, no end interior to any of them,
and covering the part of `[a, b]` ahead of the current point, is walked through from the current
point to `b`, one piece at a time, in increasing distance from `a`. -/
end

section
-- module Solutions.Q146_CD.GeneratedStructure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- The graph `H` with the edge `e`, running from `x` to `y`, replaced by a new vertex `v` and
two new edges `e₁ : x — v`, `e₂ : v — y`.

The three guards `f ≠ e`, `f ≠ e₁`, `f ≠ e₂` on the surviving links make the three disjuncts
mutually exclusive with no hypotheses, and `hne` does the same for the last two. The freshness
hypotheses `h₁`, `h₂` are what make `edgeSet` right. -/
def subdivGraph (H : Graph γ γ) (e x y v e₁ e₂ : γ) (hne : e₁ ≠ e₂)
    (h₁ : e₁ ∉ E(H)) (h₂ : e₂ ∉ E(H)) : Graph γ γ where
  vertexSet := V(H) ∪ {z | z = v ∧ H.IsLink e x y}
  edgeSet := (E(H) \ {e}) ∪ {f | (f = e₁ ∨ f = e₂) ∧ H.IsLink e x y}
  IsLink f a b :=
    (H.IsLink f a b ∧ f ≠ e ∧ f ≠ e₁ ∧ f ≠ e₂) ∨
      (f = e₁ ∧ H.IsLink e x y ∧ s(a, b) = s(x, v)) ∨
      (f = e₂ ∧ H.IsLink e x y ∧ s(a, b) = s(v, y))
  isLink_symm _ _ :=
    { symm := by
        rintro a b (⟨hl, hf, hf₁, hf₂⟩ | ⟨rfl, hl, hs⟩ | ⟨rfl, hl, hs⟩)
        · exact Or.inl ⟨hl.symm, hf, hf₁, hf₂⟩
        · exact Or.inr (Or.inl ⟨rfl, hl, Sym2.eq_swap.trans hs⟩)
        · exact Or.inr (Or.inr ⟨rfl, hl, Sym2.eq_swap.trans hs⟩) }
  eq_or_eq_of_isLink_of_isLink := by
    rintro f a b c d h h'
    rcases h with ⟨hl, -, hf₁, hf₂⟩ | ⟨hfe, -, hs⟩ | ⟨hfe, -, hs⟩ <;>
      rcases h' with ⟨hl', -, hg₁, hg₂⟩ | ⟨hge, -, hs'⟩ | ⟨hge, -, hs'⟩
    · exact hl.left_eq_or_eq hl'
    · exact absurd hge hf₁
    · exact absurd hge hf₂
    · exact absurd hfe hg₁
    · have := Sym2.eq_iff.1 (hs.trans hs'.symm); tauto
    · exact absurd (hfe.symm.trans hge) hne
    · exact absurd hfe hg₂
    · exact absurd (hge.symm.trans hfe) hne
    · have := Sym2.eq_iff.1 (hs.trans hs'.symm); tauto
  edge_mem_iff_exists_isLink f := by
    constructor
    · rintro (⟨hf, hfe⟩ | ⟨hf, hl⟩)
      · obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet hf
        exact ⟨a, b, Or.inl ⟨hab, hfe, fun h => h₁ (h ▸ hf), fun h => h₂ (h ▸ hf)⟩⟩
      · rcases hf with rfl | rfl
        · exact ⟨x, v, Or.inr (Or.inl ⟨rfl, hl, rfl⟩)⟩
        · exact ⟨v, y, Or.inr (Or.inr ⟨rfl, hl, rfl⟩)⟩
    · rintro ⟨a, b, (⟨hl, hf, -, -⟩ | ⟨rfl, hl, -⟩ | ⟨rfl, hl, -⟩)⟩
      · exact Or.inl ⟨hl.edge_mem, hf⟩
      · exact Or.inr ⟨Or.inl rfl, hl⟩
      · exact Or.inr ⟨Or.inr rfl, hl⟩
  left_mem_of_isLink := by
    rintro f a b (⟨hl, -, -, -⟩ | ⟨rfl, hl, hs⟩ | ⟨rfl, hl, hs⟩)
    · exact Or.inl hl.left_mem
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl hl.left_mem
      · exact Or.inr ⟨rfl, hl⟩
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr ⟨rfl, hl⟩
      · exact Or.inl hl.right_mem

variable {H K : Graph γ γ} {e x y v e₁ e₂ : γ}

@[simp] theorem subdivGraph_vertexSet {hne h₁ h₂} :
    V(subdivGraph H e x y v e₁ e₂ hne h₁ h₂) = V(H) ∪ {z | z = v ∧ H.IsLink e x y} := rfl

@[simp] theorem subdivGraph_edgeSet {hne h₁ h₂} :
    E(subdivGraph H e x y v e₁ e₂ hne h₁ h₂) =
      (E(H) \ {e}) ∪ {f | (f = e₁ ∨ f = e₂) ∧ H.IsLink e x y} := rfl

theorem subdivGraph_isLink {hne h₁ h₂} {f a b : γ} :
    (subdivGraph H e x y v e₁ e₂ hne h₁ h₂).IsLink f a b ↔
      (H.IsLink f a b ∧ f ≠ e ∧ f ≠ e₁ ∧ f ≠ e₂) ∨
        (f = e₁ ∧ H.IsLink e x y ∧ s(a, b) = s(x, v)) ∨
        (f = e₂ ∧ H.IsLink e x y ∧ s(a, b) = s(v, y)) := Iff.rfl

/-- Subdividing is monotone in the graph: a subgraph carrying the subdivided edge is subdivided
along with the whole, and one that does not carry it is left alone and still fits inside. This
is what gives `CellStructure.subdivideEdge` its `outerGraph_le`. -/
theorem subdivGraph_mono (hHK : H ≤ K) {hne h₁ h₂ h₁' h₂'} :
    subdivGraph H e x y v e₁ e₂ hne h₁ h₂ ≤ subdivGraph K e x y v e₁ e₂ hne h₁' h₂' where
  vertexSet_mono := by
    rintro z (hz | ⟨rfl, hl⟩)
    · exact Or.inl (hHK.vertexSet_mono hz)
    · exact Or.inr ⟨rfl, hHK.isLink_mono hl⟩
  isLink_mono := by
    rintro f a b (⟨hl, hf, hf₁, hf₂⟩ | ⟨rfl, hl, hs⟩ | ⟨rfl, hl, hs⟩)
    · exact Or.inl ⟨hHK.isLink_mono hl, hf, hf₁, hf₂⟩
    · exact Or.inr (Or.inl ⟨rfl, hHK.isLink_mono hl, hs⟩)
    · exact Or.inr (Or.inr ⟨rfl, hHK.isLink_mono hl, hs⟩)

/-! ### The cells of an abstract structure -/

/-! ### Generated matched cell structures -/

/-! ### The geometric content of one 2-cell split

`thm:general-crosscut` is what the induction step of assertions (i) and (vii) applies at each
split. The two hypotheses it still carries on `main` — `thm:jordan` and `HasArcCollars` — are
threaded through verbatim; both are being discharged elsewhere. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.RealizeSubdiv
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- The two halves of a parameter interval cut at a point of it cover it. -/
theorem uIcc_union_uIcc (h : t ∈ uIcc a b) : uIcc a t ∪ uIcc t b = uIcc a b := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at h ⊢
    rw [uIcc_of_le h.1, uIcc_of_le h.2, Icc_union_Icc_eq_Icc h.1 h.2]
  · rw [uIcc_of_ge hab] at h ⊢
    rw [uIcc_of_ge h.2, uIcc_of_ge h.1, union_comm, Icc_union_Icc_eq_Icc h.1 h.2]

/-- …and meet exactly at the cut point. -/
theorem uIcc_inter_uIcc (h : t ∈ uIcc a b) : uIcc a t ∩ uIcc t b = {t} := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at h
    rw [uIcc_of_le h.1, uIcc_of_le h.2, Icc_inter_Icc_eq_singleton h.1 h.2]
  · rw [uIcc_of_ge hab] at h
    rw [uIcc_of_ge h.2, uIcc_of_ge h.1, inter_comm, Icc_inter_Icc_eq_singleton h.1 h.2]

/-- The far endpoint is not in the near half. -/
theorem right_notMem_uIcc_left (h : t ∈ uIcc a b) (hb : b ≠ t) : b ∉ uIcc a t := fun hmem =>
  hb (by
    have : b ∈ uIcc a t ∩ uIcc t b := ⟨hmem, right_mem_uIcc⟩
    rwa [uIcc_inter_uIcc h, mem_singleton_iff] at this)

/-- …and symmetrically. -/
theorem left_notMem_uIcc_right (h : t ∈ uIcc a b) (ha : a ≠ t) : a ∉ uIcc t b := fun hmem =>
  ha (by
    have : a ∈ uIcc a t ∩ uIcc t b := ⟨left_mem_uIcc, hmem⟩
    rwa [uIcc_inter_uIcc h, mem_singleton_iff] at this)

theorem uIcc_left_subset (h : t ∈ uIcc a b) : uIcc a t ⊆ uIcc a b :=
  uIcc_subset_uIcc left_mem_uIcc h

theorem uIcc_right_subset (h : t ∈ uIcc a b) : uIcc t b ⊆ uIcc a b :=
  uIcc_subset_uIcc h right_mem_uIcc

/-! ### The two subarcs of a cut -/

/-! ### The two halves of a drawn edge

The special case `a = 0`, `b = 1` of the previous section, in the notation a consumer holding a
`Graph.IsDrawing` writes. -/

variable {β : Type*}
  {e : β}

theorem uIcc_zero_one : uIcc (0 : ℝ) 1 = I := uIcc_of_le zero_le_one

/-! ### The orientation of the drawn subdivided edge -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_JordanCircularizationSequence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

structure FiniteJordanConfiguration (I : Type*) where
  hole : I → ℂ ≃ₜ ℂ
  disjoint : Pairwise (Disjoint on fun i => closure (jordanInterior (hole i)))

namespace FiniteJordanConfiguration
variable {I : Type*} [Finite I]

def region (C : FiniteJordanConfiguration I) : Set Sphere := openCompletedRegion C.hole

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticReflectionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual data for finite analytic uniformization by invariant Beltrami
coefficients. Conformality of the straightened comparison and roundness of
its boundary images are not fields and remain to be proved. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer CannonBeltrami
attribute [local instance] sphereMetric sphereBorel

local instance instBorelSpaceSphere_12_rffc8c3_1 : BorelSpace Sphere := ⟨rfl⟩
structure AnalyticReflectionData {I : Type*} [Finite I] (C : FiniteJordanConfiguration I) where
  comparison : ℂ ≃ₜ ℂ
  center : I → ℂ
  radius : I → ℝ
  radius_pos : ∀i,0 < radius i
  comparison_smooth : ContDiff ℝ ∞ (comparison : ℂ → ℂ)
  comparison_inverse_smooth : ContDiff ℝ ∞ (comparison.symm : ℂ → ℂ)
  cap_image : ∀i,comparison '' closure (jordanInterior (C.hole i))=closedBall (center i) (radius i)
  baseCoefficient : ℂ → ℂ
  bound : ℝ
  bound_nonneg : 0≤bound
  bound_lt_one : bound<1
  base_bound : ∀z,‖baseCoefficient z‖≤bound
  base_equation : ∀z,partialBar comparison.symm z=baseCoefficient z*partialZ comparison.symm z
  extension : Sphere → ℂ
  extension_measurable : Measurable extension
  extension_bound : ∀p,‖extension p‖≤bound
  extension_base : EqOn extension (sphereCoefficient 0 baseCoefficient) (comparison.onePointCongr '' C.region)
  extension_invariant : ∀i p,extension p=roundReflectionCoefficient (center i) p
    (extension (roundDiskReflection (center i) (radius i) (radius_pos i) p))
  density : PlaneL2
  supportRadius : ℝ
  extension_zero : ∀z : ℂ,supportRadius≤‖z‖ → extension (z : Sphere)=0
  approximation : PrincipalSmoothApproximation density bound supportRadius
  limitData : PrincipalMapLimit approximation
  density_equation : ∀ᵐz ∂volume,density z=extension (z : Sphere)*(1+beurling density z)
  coefficient_tendsto : ∀ᵐz ∂volume,Tendsto (fun n => approximation.coefficient n z)
    atTop (𝓝 (extension (z : Sphere)))

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def principal (D : AnalyticReflectionData C) : ℂ ≃ₜ ℂ := D.limitData.map

end AnalyticReflectionData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticStraighteningResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pulled-back principal approximants have antiholomorphic
error tending strongly to zero on the original analytic domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def straighteningApproximation (D : AnalyticReflectionData C) (n : ℕ) : ℂ → ℂ :=
  (D.approximation.map (D.limitData.index n)) ∘ D.comparison

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundReflectionDifferential
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Plane formula and differential of a circular reflection off its pole. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

def roundReflectionPlane (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  c+(r:ℂ)^2/(star (z-c))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_PrincipalReflectionDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mollified coefficients' reflection defects are uniformly
bounded and tend almost everywhere to zero. The smooth conjugate's exact
antiholomorphic derivative is expressed using this defect. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def reflectionDefect (D : AnalyticReflectionData C) (i : I) (n : ℕ) (z : ℂ) : ℂ :=
  circleReflectionPhase (D.center i) z *
    star (D.approximation.coefficient (D.limitData.index n)
      (roundReflectionPlane (D.center i) (D.radius i) z)) -
    D.approximation.coefficient (D.limitData.index n) z

def reflectedApproximation (D : AnalyticReflectionData C) (i : I) (n : ℕ) (z : ℂ) : ℂ :=
  star (D.approximation.map (D.limitData.index n)
    (roundReflectionPlane (D.center i) (D.radius i)
      ((D.approximation.map (D.limitData.index n)).symm z)))

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectedApproximationLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conjugated smooth reflections converge locally uniformly off
the limiting pole. This follows from both retained principal-map limits. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def reflectedLimit (D : AnalyticReflectionData C) (i : I) (z : ℂ) : ℂ :=
  star (D.principal (roundReflectionPlane (D.center i) (D.radius i) (D.principal.symm z)))

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneHomeomorphFromSphere
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restrict an actual sphere homeomorphism fixing infinity to its finite
plane chart. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def spherePlaneMap (e : Sphere ≃ₜ Sphere) (_he : e OnePoint.infty=OnePoint.infty) (z : ℂ) : ℂ :=
  finiteCoord (e (z : Sphere))

lemma spherePlaneMap_finite (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) (z : ℂ) :
    e (z : Sphere)≠OnePoint.infty := by
  intro h
  exact OnePoint.coe_ne_infty z (e.injective (h.trans he.symm))

lemma coe_spherePlaneMap (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) (z : ℂ) :
    (spherePlaneMap e he z : Sphere)=e (z : Sphere) :=
  CannonMobius.coe_coordinate (spherePlaneMap_finite e he z)

lemma spherePlaneMap_continuous (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) :
    Continuous (spherePlaneMap e he) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (CannonMobius.continuousAt_coordinate (spherePlaneMap_finite e he z)).comp_of_eq
    ((e.continuous.comp OnePoint.continuous_coe).continuousAt) rfl

lemma sphereHomeomorph_symm_infty (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) :
    e.symm OnePoint.infty=OnePoint.infty := by
  apply e.injective
  rw [e.apply_symm_apply,he]

def spherePlaneHomeomorph (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) : ℂ ≃ₜ ℂ where
  toFun := spherePlaneMap e he
  invFun := spherePlaneMap e.symm (sphereHomeomorph_symm_infty e he)
  left_inv := by
    intro z
    apply OnePoint.coe_injective
    rw [coe_spherePlaneMap,coe_spherePlaneMap,e.symm_apply_apply]
  right_inv := by
    intro z
    apply OnePoint.coe_injective
    rw [coe_spherePlaneMap,coe_spherePlaneMap,e.apply_symm_apply]
  continuous_toFun := spherePlaneMap_continuous e he
  continuous_invFun := spherePlaneMap_continuous e.symm _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectedSphereNormalization
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the pole of the actual conjugated reflection to infinity.
The result is an actual plane homeomorphism. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def reflectedSphere (D : AnalyticReflectionData C) (i : I) : Sphere ≃ₜ Sphere :=
  D.principal.onePointCongr.symm.trans
    ((roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i)).trans
      (D.principal.onePointCongr.trans Complex.conjCLE.toHomeomorph.onePointCongr))

lemma reflectedSphere_pole (D : AnalyticReflectionData C) (i : I) :
    D.reflectedSphere i (D.principal (D.center i) : Sphere)=OnePoint.infty := by
  change Complex.conjCLE.toHomeomorph.onePointCongr (D.principal.onePointCongr
    (roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i)
      (D.principal.onePointCongr.symm (D.principal (D.center i) : Sphere))))=_
  change Complex.conjCLE.toHomeomorph.onePointCongr (D.principal.onePointCongr
    (roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i)
      (D.principal.symm (D.principal (D.center i)) : Sphere)))=_
  rw [D.principal.symm_apply_apply,roundDiskReflection_center]
  rfl

def poleParameter (D : AnalyticReflectionData C) (i : I) : Sphere ≃ₜ Sphere :=
  CannonMobius.inversion.trans (affineSphere 1 (D.principal (D.center i)) one_ne_zero)

lemma poleParameter_infty (D : AnalyticReflectionData C) (i : I) :
    D.poleParameter i OnePoint.infty=(D.principal (D.center i) : Sphere) := by
  change affineSphere 1 _ one_ne_zero (CannonMobius.inversion OnePoint.infty)=_
  rw [show CannonMobius.inversion OnePoint.infty=(0:ℂ) from CannonMobius.inv_infty,affineSphere_coe]
  simp

lemma poleNormalized_fixes_infty (D : AnalyticReflectionData C) (i : I) :
    (D.poleParameter i |>.trans (D.reflectedSphere i)) OnePoint.infty=OnePoint.infty := by
  change D.reflectedSphere i (D.poleParameter i OnePoint.infty)=_
  rw [D.poleParameter_infty,D.reflectedSphere_pole]

def poleNormalized (D : AnalyticReflectionData C) (i : I) : ℂ ≃ₜ ℂ :=
  spherePlaneHomeomorph ((D.poleParameter i).trans (D.reflectedSphere i))
    (D.poleNormalized_fixes_infty i)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AppendedScalarPairs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair-nullity for the exact finite list obtained by adjoining two
scalar tests. The first two coordinates are the new tests. -/
open Set Function MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

 def appendScalarPair {X : Type*} {m : ℕ} (u : Fin m → X → ℝ) (p q : X → ℝ) :
    Fin (m+2) → X → ℝ := Fin.cases q (Fin.cases p u)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakBarrierEstimate
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative saved-barrier estimate for the actual joint
Sobolev witness, retaining the separate exceptional-support term. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_barrier_estimate {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    (S : Set EuclideanPlane) (hS : MeasurableSet S)
    (H : EuclideanPlane → EuclideanPlane) (DH : EuclideanPlane → EuclideanPlane →L[ℝ] EuclideanPlane)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ e : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hbound : ∀ y, ‖fderiv ℝ Φ y‖ ≤ M₁)
    (hlip : ∀ y z, ‖fderiv ℝ Φ y-fderiv ℝ Φ z‖ ≤ M₂*‖y-z‖)
    (hclose : ∀ x ∉ S, ‖planePair (u x) (v x)-H x‖ ≤ e)
    (hD : AEStronglyMeasurable (fun x =>
      (fderiv ℝ Φ (planePair (u x) (v x))).comp (weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x))-
      (fderiv ℝ Φ (H x)).comp (DH x)) (volume.restrict U))
    (herror : MemLp (fun x => weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x)-DH x)
      2 (volume.restrict U)) (hH : MemLp DH 2 (volume.restrict U)) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (u x) (v x))) U,
      MemLp (fun x => W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x)))
        2 (volume.restrict U) ∧
      (eLpNorm (fun x => W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x)))
        2 (volume.restrict U)).toReal ≤
      M₁*(eLpNorm (fun x => ‖weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x)-DH x‖)
        2 (volume.restrict U)).toReal +
      (M₂*e)*(eLpNorm (fun x => ‖DH x‖) 2 (volume.restrict U)).toReal +
      (2*M₁)*(eLpNorm (S.indicator (fun x => ‖DH x‖)) 2 (volume.restrict U)).toReal := by
  let W := localPairChainWitness hU hUf hu hv Wu Wv hΦ hB hM₁ hΦb hbound
  let D := fun x => (fderiv ℝ Φ (planePair (u x) (v x))).comp
    (weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x))-(fderiv ℝ Φ (H x)).comp (DH x)
  obtain ⟨hLp, hn⟩ := barrier_L2_error S hS (fun x => planePair (u x) (v x)) H
    (fun x => weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x)) DH Φ
    hM₁ hM₂ he hbound hlip hclose hD herror hH
  have hid (x : EuclideanPlane) :
      W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x)) =
        planeCovectorGradient (D x) := by
    rw [planeCovectorGradient_sub]
    rw [localPairChainWitness_covector hU hUf hu hv Wu Wv hΦ hB hM₁ hΦb hbound]
  have hnorm (x : EuclideanPlane) :
      ‖W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x))‖ = ‖D x‖ := by
    rw [hid, planeCovectorGradient_norm]
  have hgrad : MemLp (fun x => W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x)))
      2 (volume.restrict U) := by
    apply hLp.of_le
    · exact (continuous_planeCovectorGradient.comp_aestronglyMeasurable hD).congr
        (Eventually.of_forall (fun x => (hid x).symm))
    · exact Eventually.of_forall (fun x => (hnorm x).le)
  refine ⟨W,hgrad,?_⟩
  have hnorms := eLpNorm_congr_norm_ae (μ := volume.restrict U) (Eventually.of_forall hnorm) (p := 2)
  rw [hnorms]
  exact hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakPairL2
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two scalar weak-gradient errors control the actual joint linear
map, without any extra integrability assumption on that map. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPairDifferential_norm_le (a b : EuclideanPlane) :
    ‖weakPairDifferential a b‖ ≤ ‖a‖+‖b‖ := by
  have hn := norm_add_le ((innerSL ℝ a).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
    ((innerSL ℝ b).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  simpa only [weakPairDifferential, ContinuousLinearMap.norm_smulRight_apply,
    innerSL_apply_norm, PiLp.norm_single, norm_one, mul_one] using hn

 theorem weakPairDifferential_sub (a b c d : EuclideanPlane) :
    weakPairDifferential (a-c) (b-d) = weakPairDifferential a b-weakPairDifferential c d := by
  ext x
  simp only [weakPairDifferential, add_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    map_sub, sub_smul]
  abel_nf

 theorem continuous_weakPairDifferential : Continuous (fun x : EuclideanPlane × EuclideanPlane =>
    weakPairDifferential x.1 x.2) := by
  have hc (e : EuclideanPlane) : Continuous (fun a : EuclideanPlane => (innerSL ℝ a).smulRight e) :=
    ((ContinuousLinearMap.smulRightL ℝ EuclideanPlane EuclideanPlane).continuous.comp
      (innerSL ℝ).continuous).clm_apply continuous_const
  exact ((hc _).comp continuous_fst).add ((hc _).comp continuous_snd)

 theorem weakPairDifferential_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → EuclideanPlane} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    MemLp (fun x => weakPairDifferential (a x) (b x)) 2 μ ∧
      (eLpNorm (fun x => weakPairDifferential (a x) (b x)) 2 μ).toReal ≤
        (eLpNorm a 2 μ).toReal+(eLpNorm b 2 μ).toReal := by
  have hm := continuous_weakPairDifferential.comp_aestronglyMeasurable
    (ha.aestronglyMeasurable.prodMk hb.aestronglyMeasurable)
  have hz : MemLp (fun _ : X => (0 : ℝ)) 2 μ := MemLp.zero'
  have h := l2_three_term_bound (a := 1) (b := 1) (c := 0) (by norm_num) (by norm_num)
    le_rfl hm ha.norm hb.norm hz
    (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall (fun _ => le_rfl))
    (Eventually.of_forall (fun x => by simpa only [one_mul, zero_mul, add_zero] using (weakPairDifferential_norm_le (a x) (b x))))
  simpa only [eLpNorm_norm _, eLpNorm_norm _,
    one_mul, zero_mul, add_zero] using h

 theorem weakPairDifferential_error_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b c d : X → EuclideanPlane}
    (ha : MemLp (fun x => a x-c x) 2 μ) (hb : MemLp (fun x => b x-d x) 2 μ) :
    MemLp (fun x => weakPairDifferential (a x) (b x)-weakPairDifferential (c x) (d x)) 2 μ ∧
      (eLpNorm (fun x => weakPairDifferential (a x) (b x)-weakPairDifferential (c x) (d x)) 2 μ).toReal ≤
        (eLpNorm (fun x => a x-c x) 2 μ).toReal+(eLpNorm (fun x => b x-d x) 2 μ).toReal := by
  simpa only [weakPairDifferential_sub] using weakPairDifferential_memLp ha hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakBarrierMeasurability
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual barrier differential follows from the
two scalar Sobolev witnesses and the reference differential. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem continuous_plane_covector_comp : Continuous
    (fun p : (EuclideanPlane →L[ℝ] ℝ) × (EuclideanPlane →L[ℝ] EuclideanPlane) => p.1.comp p.2) :=
  ((ContinuousLinearMap.compL ℝ EuclideanPlane EuclideanPlane ℝ).continuous.comp
    continuous_fst).clm_apply continuous_snd

 theorem joint_barrier_differential_measurable {U : Set EuclideanPlane}
    {u v : EuclideanPlane → ℝ} (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {H : EuclideanPlane → EuclideanPlane} (hH : AEStronglyMeasurable H (volume.restrict U))
    {DH : EuclideanPlane → EuclideanPlane →L[ℝ] EuclideanPlane}
    (hDH : AEStronglyMeasurable DH (volume.restrict U))
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ) :
    AEStronglyMeasurable (fun x =>
      (fderiv ℝ Φ (planePair (u x) (v x))).comp
        (weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x))-
      (fderiv ℝ Φ (H x)).comp (DH x)) (volume.restrict U) := by
  have ha := ((hΦ.continuous_fderiv one_ne_zero).comp
    (continuous_planePair hu hv)).aestronglyMeasurable (μ := volume) |>.restrict (s := U)
  have hb := (hΦ.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hH
  have hd := continuous_weakPairDifferential.comp_aestronglyMeasurable
    (Wu.weakGrad_memLp.aestronglyMeasurable.prodMk Wv.weakGrad_memLp.aestronglyMeasurable)
  exact (continuous_plane_covector_comp.comp_aestronglyMeasurable (ha.prodMk hd)).sub
    (continuous_plane_covector_comp.comp_aestronglyMeasurable (hb.prodMk hDH))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalWeakBarrierBound
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local three-term barrier bound from four actual scalar Sobolev
witnesses. Measurability and joint differential integrability are derived. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_weak_barrier_bound
    {U S : Set EuclideanPlane} (hU : IsOpen U) (hUf : volume U ≠ ∞)
    (hS : MeasurableSet S) {p q x y : EuclideanPlane → ℝ}
    (hp : Continuous p) (hq : Continuous q)
    (Wp : DeGiorgi.MemW1pWitness 2 p U) (Wq : DeGiorgi.MemW1pWitness 2 q U)
    (Wx : DeGiorgi.MemW1pWitness 2 x U) (Wy : DeGiorgi.MemW1pWitness 2 y U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ e : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖)
    (hclose : ∀ z ∈ U, z ∉ S → ‖planePair (p z) (q z)-planePair (x z) (y z)‖ ≤ e) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (p z) (q z))) U,
      MemLp (fun z => W.weakGrad z-planeCovectorGradient
        ((fderiv ℝ Φ (planePair (x z) (y z))).comp
          (weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)))) 2 (volume.restrict U) ∧
      (eLpNorm (fun z => W.weakGrad z-planeCovectorGradient
        ((fderiv ℝ Φ (planePair (x z) (y z))).comp
          (weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)))) 2 (volume.restrict U)).toReal ≤
      M₁*((eLpNorm (fun z => Wp.weakGrad z-Wx.weakGrad z) 2 (volume.restrict U)).toReal+
        (eLpNorm (fun z => Wq.weakGrad z-Wy.weakGrad z) 2 (volume.restrict U)).toReal)+
      (M₂*e)*(eLpNorm (fun z => weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z))
        2 (volume.restrict U)).toReal+
      (2*M₁)*(eLpNorm (S.indicator (fun z => ‖weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)‖))
        2 (volume.restrict U)).toReal := by
  let T := S ∪ Uᶜ
  let H := fun z => planePair (x z) (y z)
  let DH := fun z => weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)
  have hH : AEStronglyMeasurable H (volume.restrict U) :=
    (continuous_planePair continuous_fst continuous_snd).comp_aestronglyMeasurable
      (Wx.memLp.aestronglyMeasurable.prodMk Wy.memLp.aestronglyMeasurable)
  have hDH := (weakPairDifferential_memLp Wx.weakGrad_memLp Wy.weakGrad_memLp).1
  have herror := weakPairDifferential_error_memLp
    (Wp.weakGrad_memLp.sub Wx.weakGrad_memLp) (Wq.weakGrad_memLp.sub Wy.weakGrad_memLp)
  have ht : ∀ z ∉ T, ‖planePair (p z) (q z)-H z‖ ≤ e := by
    intro z hz
    have hzU : z ∈ U := not_not.mp (fun h => hz (Or.inr h))
    exact hclose z hzU (fun h => hz (Or.inl h))
  obtain ⟨W,hW,hn⟩ := local_sobolev_barrier_estimate hU hUf hp hq Wp Wq T
    (hS.union hU.measurableSet.compl) H DH hΦ hB hM₁ hM₂ he hΦb hbound hlip ht
    (joint_barrier_differential_measurable hp hq Wp Wq hH hDH.aestronglyMeasurable hΦ)
    herror.1 hDH
  have hi : eLpNorm (T.indicator (fun z => ‖DH z‖)) 2 (volume.restrict U) =
      eLpNorm (S.indicator (fun z => ‖DH z‖)) 2 (volume.restrict U) := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    by_cases hs : z ∈ S
    · simp [T, hs]
    · have ht : z ∉ T := fun h => h.elim hs (fun h => h hz)
      simp only [indicator_of_notMem hs, indicator_of_notMem ht]
  rw [hi, eLpNorm_norm _,
    eLpNorm_norm _] at hn
  refine ⟨W,hW,hn.trans ?_⟩
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left herror.2 hM₁) le_rfl) le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BarrierEnergyAssembly
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn the proved reference-comparison bound into the total source
barrier energy. The reference is constructed by conformal transport. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_norm_le_error_add {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f g : X → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (eLpNorm f 2 μ).toReal ≤ (eLpNorm (fun x => f x-g x) 2 μ).toReal+(eLpNorm g 2 μ).toReal := by
  have hd := hf.sub hg
  have hz : MemLp (fun _ : X => (0 : ℝ)) 2 μ := MemLp.zero'
  have h := l2_three_term_bound (a := 1) (b := 1) (c := 0) (by norm_num) (by norm_num) le_rfl
    hf.aestronglyMeasurable hd.norm hg.norm hz
    (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun _ => le_rfl))
    (Eventually.of_forall (fun x => by
      simpa only [one_mul, zero_mul, add_zero, Pi.sub_apply] using (calc
        ‖f x‖ = ‖(f x-g x)+g x‖ := by rw [sub_add_cancel]
        _ ≤ ‖f x-g x‖+‖g x‖ := norm_add_le _ _)))
  have hdn : AEStronglyMeasurable (fun x => f x-g x) μ := hd.aestronglyMeasurable
  have h' : (eLpNorm f 2 μ).toReal ≤
      (eLpNorm (fun x => ‖f x-g x‖) 2 μ).toReal+(eLpNorm (fun x => ‖g x‖) 2 μ).toReal := by
    simpa only [one_mul, zero_mul, add_zero, Pi.sub_apply] using h.2
  rw [eLpNorm_norm _, eLpNorm_norm _] at h'
  exact h'


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AppendingPairData
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite appending construction, before choosing its inner
contours. The resulting fields concern the original source functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

structure AppendingPairData (G : Set Sphere) {m : ℕ}
    (u : Fin m → EuclideanPlane → ℝ)
    (Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)) (a δ η : ℝ) where
  old : Fin m → EuclideanPlane → ℝ
  p : EuclideanPlane → ℝ
  q : EuclideanPlane → ℝ
  old_continuous : ∀ i, Continuous (old i)
  old_compact : ∀ i, HasCompactSupport (old i)
  old_witness : ∀ i, DeGiorgi.MemW1pWitness 2 (old i) (physicalPlaneDomain G)
  old_close : ∀ i x, |old i x-u i x| < δ
  old_error : ∀ i, (eLpNorm (fun x => (old_witness i).weakGrad x-(Wold i).weakGrad x) 2
    (volume.restrict (physicalPlaneDomain G))).toReal < δ
  p_continuous : Continuous p
  q_continuous : Continuous q
  p_compact : HasCompactSupport p
  q_compact : HasCompactSupport q
  p_witness : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G)
  q_witness : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G)
  pair_null : ∀ i j : Fin (m+2), i ≠ j → volume ((fun x =>
    (sphereFromPlaneFunction (appendScalarPair old p q i) x,
      sphereFromPlaneFunction (appendScalarPair old p q j) x)) '' Gᶜ) = 0
  barrier : EuclideanPlane → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  barrier_smooth : ContDiff ℝ ∞ barrier
  barrier_compact : HasCompactSupport barrier
  barrier_support : tsupport barrier ⊆ ball 0 (4*a)
  barrier_unit : ∀ x, barrier x ∈ Icc (0 : ℝ) 1
  barrier_one : ∀ x ∈ ball 0 radius, barrier x = 1
  small_energy : ∀ c : EuclideanPlane,
    ∃ V : DeGiorgi.MemW1pWitness 2 (fun x => barrier (planePair (p x) (q x)-c))
      (physicalPlaneDomain G ∩ ball 0 (65*a)),
      (eLpNorm V.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η
  trace_bound : ∀ z ∈ Gᶜ, ‖planePair (sphereFromPlaneFunction p z) (sphereFromPlaneFunction q z)‖ ≤ 8*a
  outer_margin : ∀ x ∈ physicalPlaneDomain G, 63*a ≤ ‖x‖ → ‖x‖ ≤ 65*a →
    ∀ c : EuclideanPlane, ‖c‖ ≤ 8*a → 5*a ≤ ‖planePair (p x) (q x)-c‖

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredJordanCoordinate
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered disk coordinates for the actual spherical Jordan collars.
The continuous extension is used only to push path laws to path space. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

def centeredJordanCoordinate (K : ℂ ≃ₜ ℂ) (b x : Sphere) : ℂ :=
  diskCentering (sphereJordanCoordinate K b) (sphereJordanCoordinate K x)

@[simp] theorem centeredJordanCoordinate_self (K : ℂ ≃ₜ ℂ) (b : Sphere) :
    centeredJordanCoordinate K b b = 0 := diskCentering_self _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PointDustContourSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing subordinate contour construction on a point-complement
source, with its identity quotient made explicit. -/
open Set Function Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem continuous_sphereFromPlaneFunction {p : EuclideanPlane → ℝ}
    (hp : Continuous p) (hs : HasCompactSupport p) : Continuous (sphereFromPlaneFunction p) := by
  exact continuousOn_univ.mp (sphereFromPlaneFunction_continuousOn isOpen_univ hp.continuousOn
    hs.isCompact (fun _ hx => image_eq_zero_of_notMem_tsupport hx))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCompactTests
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite test families and the actual appending transition. The two new
coordinates occupy positions zero and one; every previous coordinate is
retained after the proved small flattening. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

structure FiniteCompactTests (G : Set Sphere) where
  count : ℕ
  test : Fin count → EuclideanPlane → ℝ
  continuous : ∀ i, Continuous (test i)
  compact : ∀ i, HasCompactSupport (test i)
  witness : ∀ i, DeGiorgi.MemW1pWitness 2 (test i) (physicalPlaneDomain G)
  pair_null : ∀ i j, i ≠ j → volume ((fun x =>
    (sphereFromPlaneFunction (test i) x,sphereFromPlaneFunction (test j) x)) '' Gᶜ) = 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SavedBarrierEnergy
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative stability of a saved barrier under changes to its two
source tests. Its Sobolev witness is retained. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem saved_barrier_energy_stability
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUf : volume U ≠ ∞)
    {p q x y : EuclideanPlane → ℝ}
    (hp : Continuous p) (hq : Continuous q) (hx : Continuous x) (hy : Continuous y)
    (Wp : DeGiorgi.MemW1pWitness 2 p U) (Wq : DeGiorgi.MemW1pWitness 2 q U)
    (Wx : DeGiorgi.MemW1pWitness 2 x U) (Wy : DeGiorgi.MemW1pWitness 2 y U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ e : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖)
    (hclose : ∀ z ∈ U, ‖planePair (p z) (q z)-planePair (x z) (y z)‖ ≤ e)
    (V : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (x z) (y z))) U) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (p z) (q z))) U,
      (eLpNorm (fun z => W.weakGrad z-V.weakGrad z) 2 (volume.restrict U)).toReal ≤
        M₁*((eLpNorm (fun z => Wp.weakGrad z-Wx.weakGrad z) 2 (volume.restrict U)).toReal+
          (eLpNorm (fun z => Wq.weakGrad z-Wy.weakGrad z) 2 (volume.restrict U)).toReal)+
        (M₂*e)*(eLpNorm (fun z => weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z))
          2 (volume.restrict U)).toReal := by
  let V' := localPairChainWitness hU hUf hx hy Wx Wy hΦ hB hM₁ hΦb hbound
  have hv := V.ae_eq hU V'
  obtain ⟨W,hW,hn⟩ := local_weak_barrier_bound (S := ∅) hU hUf MeasurableSet.empty hp hq Wp Wq Wx Wy
    hΦ hB hM₁ hM₂ he hΦb hbound hlip (fun z hz _ => hclose z hz)
  have heq : (fun z => W.weakGrad z-V.weakGrad z) =ᵐ[volume.restrict U]
      (fun z => W.weakGrad z-planeCovectorGradient
        ((fderiv ℝ Φ (planePair (x z) (y z))).comp
          (weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)))) := by
    filter_upwards [hv] with z hz
    rw [hz, localPairChainWitness_covector hU hUf hx hy Wx Wy hΦ hB hM₁ hΦb hbound]
  refine ⟨W,?_⟩
  rw [eLpNorm_congr_ae heq]
  simpa only [indicator_empty, eLpNorm_zero', ENNReal.toReal_zero, mul_zero, add_zero] using hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SavedBarrierEnergySlack
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive energy slack yields a positive perturbation tolerance for a
fixed saved barrier, by quantitative comparison. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_saved_barrier_energy_tolerance
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUf : volume U ≠ (⊤ : ℝ≥0∞))
    {x y : EuclideanPlane → ℝ} (hx : Continuous x) (hy : Continuous y)
    (Wx : DeGiorgi.MemW1pWitness 2 x U) (Wy : DeGiorgi.MemW1pWitness 2 y U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ η : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖)
    (V : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (x z) (y z))) U)
    (hV : (eLpNorm V.weakGrad 2 (volume.restrict U)).toReal < η) :
    ∃ t > 0, ∀ (p q : EuclideanPlane → ℝ), Continuous p → Continuous q →
      ∀ (Wp : DeGiorgi.MemW1pWitness 2 p U) (Wq : DeGiorgi.MemW1pWitness 2 q U),
      (∀ z ∈ U, ‖planePair (p z) (q z)-planePair (x z) (y z)‖ ≤ t) →
      (eLpNorm (fun z => Wp.weakGrad z-Wx.weakGrad z) 2 (volume.restrict U)).toReal ≤ t →
      (eLpNorm (fun z => Wq.weakGrad z-Wy.weakGrad z) 2 (volume.restrict U)).toReal ≤ t →
      ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (p z) (q z))) U,
        (eLpNorm W.weakGrad 2 (volume.restrict U)).toReal < η := by
  let N := (eLpNorm (fun z => weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z))
    2 (volume.restrict U)).toReal
  let C := 2*M₁+M₂*N+1
  have hC : 0 < C := by dsimp only [C,N] <;> positivity
  let t := (η-(eLpNorm V.weakGrad 2 (volume.restrict U)).toReal)/C
  have ht : 0 < t := div_pos (sub_pos.mpr hV) hC
  have heq : t*C = η-(eLpNorm V.weakGrad 2 (volume.restrict U)).toReal := div_mul_cancel₀ _ hC.ne'
  refine ⟨t,ht,?_⟩
  intro p q hp hq Wp Wq hclose hpE hqE
  obtain ⟨W,hW⟩ := saved_barrier_energy_stability hU hUf hp hq hx hy Wp Wq Wx Wy
    hΦ hB hM₁ hM₂ ht.le hΦb hbound hlip hclose V
  have herr : (eLpNorm (fun z => W.weakGrad z-V.weakGrad z) 2 (volume.restrict U)).toReal ≤
      M₁*(t+t)+(M₂*t)*N := hW.trans (add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hpE hqE) hM₁) le_rfl)
  have hnorm := (l2_norm_le_error_add W.weakGrad_memLp V.weakGrad_memLp).trans
    (add_le_add herr le_rfl)
  have he : M₁*(t+t)+(M₂*t)*N = t*C-t := by dsimp only [C] <;> ring
  rw [he,heq] at hnorm
  exact ⟨W,by linarith⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AppendingEnergyTolerance
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite saved family has a common positive energy tolerance. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_common_positive_fin {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ t > 0, ∀ i, t ≤ r i := by
  induction n with
  | zero => exact ⟨1,zero_lt_one,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨t,ht,hti⟩ := ih (fun i => r i.succ) (fun i => hr i.succ)
    refine ⟨min (r 0) t,lt_min (hr 0) ht,?_⟩
    intro i
    exact Fin.cases (min_le_left _ _) (fun j => (min_le_right _ _).trans (hti j)) i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveTestConstruction
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterate the constructed finite appending theorem, choosing each error
below every saved tolerance in the finite history. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

structure AppendingConstructionState (G : Set Sphere) where
  family : FiniteCompactTests G
  tolerances : List ℝ
  positive : ∀ t ∈ tolerances, 0 < t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.StableBernstein_Estimates_PuncturedSard
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Bernstein.Sard

open Set MeasureTheory Manifold
open scoped ContDiff Topology
universe u

section Strata
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sixFlatSet (U : Set E) (f : E → ℝ) : Set E :=
  {x | x ∈ U ∧ ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0}

def nonflatCriticalStratum (U : Set E) (f : E → ℝ) (k : ℕ) : Set E :=
  {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ iteratedFDeriv ℝ k f x = 0 ∧
    iteratedFDeriv ℝ (k + 1) f x ≠ 0}

end Strata

end Bernstein.Sard

open MeasureTheory Manifold Set Filter
open scoped Topology ContDiff

end

end OAI
end


