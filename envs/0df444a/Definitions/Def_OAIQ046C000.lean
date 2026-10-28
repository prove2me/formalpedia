-- Prove2me | Definitions.Def_OAIQ046C000
-- name    : OAIQ046C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:43:34.893743+00:00
-- url     : https://prove2.me/theorems/36601519-5bb3-42f8-8166-c055ec803320
-- title:
--   Definitions bundle OAIQ046C000 of the split of OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 638 declarations of OpenAI's Lean: 277 definitions, 12 inductive types or structures, 11 instances and 338 theorems. The definitions and types are `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.CannonActions.Cocompact`, `OAI.CannonActions.OrderedTriples`, `OAI.CannonActions.Proper`, `OAI.CannonActions.conjugate`, `OAI.CannonActions.triplesAction`, `OAI.CannonActions.triplesCongr`, `OAI.CannonActions.triplesHom`, `OAI.CannonActions.triplesMap`, `OAI.CannonAnnular.MacroscopicAdmissible`, `OAI.CannonAnnular.pathCellIndices`, `OAI.CannonAnnularCompactness.closedAnnulus`, `OAI.CannonApprox.Admissible`, `OAI.CannonApprox.FlowPaid`, `OAI.CannonApprox.FlowPatternSetup`, `OAI.CannonApprox.FlowSetup`, `OAI.CannonApprox.RecordData`, `OAI.CannonApprox.initial`, `OAI.CannonApprox.interiorScalar`, `OAI.CannonApprox.meshEnergy`, `OAI.CannonApprox.rawFunction`, `OAI.CannonApprox.scalar`, `OAI.CannonAtomic.atomic`, `OAI.CannonAtomic.dirac`, `OAI.CannonBands.ChartSquare`, `OAI.CannonBands.Strip`, `OAI.CannonBands.extend`, `OAI.CannonBands.height`, `OAI.CannonBands.rawExtended`, `OAI.CannonBands.stripHomeomorph`, `OAI.CannonBands.stripPath`, `OAI.CannonBeltrami.BoundedSmooth`, `OAI.CannonBeltrami.PlaneL2`, `OAI.CannonBeltrami.SmoothL2`, `OAI.CannonBeltrami.Sobolev`, `OAI.CannonBeltrami.axis`, `OAI.CannonBeltrami.barProject`, `OAI.CannonBeltrami.beurling` and 249 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/Cannon, in whole or in part: `Cannon_Actions_Height`, `Cannon_Actions_Proper`, `Cannon_Beltrami_Axis`, `Cannon_Beltrami_Beltrami`, `Cannon_Beltrami_CauchySymbol`, `Cannon_Beltrami_ContinuousMemLpRestrict`, `Cannon_Beltrami_Increment`, `Cannon_Beltrami_Mollifier`, `Cannon_Beltrami_MultiplyLp`, `Cannon_Beltrami_SideOrientation`, `Cannon_Beltrami_TwoPointNormalize`, `Cannon_Boundary_BoundaryHomeomorph`, `Cannon_Boundary_Thin`, `Cannon_Boundary_UnitCircle`, `Cannon_Boundary_WordBall`, `Cannon_CirclePacking_AngleGradient`, `Cannon_CirclePacking_OrientedArea`, `Cannon_CirclePacking_Radius`, `Cannon_Conformal_AnalyticFixInftyAffine`, `Cannon_Conformal_Center`, `Cannon_Conformal_LinearZ`, `Cannon_Conformal_Sphere`, `Cannon_Conformal_SphereMeasure`, `Cannon_Conformal_SphereTile`, `Cannon_Energy_ApproxSelfSimilar`, `Cannon_Energy_Extend`, `Cannon_Energy_Interior`, `Cannon_Energy_LiftPath`, `Cannon_Energy_MeshEnergy`, `Cannon_Energy_PathCosts`, `Cannon_Energy_Plane`, `Cannon_Energy_RawFunction`, `Cannon_Energy_RecordData`, `Cannon_Energy_Square`, `Cannon_Energy_SquareMap`, `Cannon_Energy_StripCrossing`, `Cannon_Flows_FlowPaid`, `Cannon_Flows_FlowPatternSetup`, `Cannon_Flows_FlowSetup`, `Cannon_Flows_GoodCandidates`, `Cannon_Flows_Lower`, `Cannon_Flows_Node`, `Cannon_Flows_Oscillation`, `Cannon_Flows_State`, `Cannon_Flows_Subdivision`, `Cannon_Modulus_Clip`, `Cannon_Modulus_ClosedAnnulus`, `Cannon_Modulus_Cost`, `Cannon_Modulus_PathCellIndices`, `Cannon_Modulus_Quad`, `Cannon_Modulus_Weights`, `Cannon_PlanarGraphs_ChartLabel`, `Cannon_PlanarGraphs_ClosureRegionInside`, `Cannon_PlanarGraphs_CutOrder`, `Cannon_PlanarGraphs_EdgeGraph`, `Cannon_PlanarGraphs_GraphShear`, `Cannon_PlanarGraphs_HomeomorphComponents`, `Cannon_PlanarGraphs_Next`, `Cannon_PlanarGraphs_Plane`, `Cannon_PlanarGraphs_Region`, `Cannon_PlanarGraphs_Support`, `Cannon_PlanarGraphs_TraceCard`, `Cannon_PlaneTopology_Arc`, `Cannon_PlaneTopology_CompactifiedFace`, `Cannon_PlaneTopology_Consecutive`, `Cannon_PlaneTopology_Crossing`, `Cannon_PlaneTopology_DevelopedFaces`, `Cannon_PlaneTopology_DualGraph`, `Cannon_PlaneTopology_FaceHull`, `Cannon_PlaneTopology_FiniteVertexSet`, `Cannon_PlaneTopology_Hat`, `Cannon_PlaneTopology_IncidentEdges`, `Cannon_PlaneTopology_IncidentFaces`, `Cannon_PlaneTopology_InnerFlux`, `Cannon_PlaneTopology_IntrinsicCircleData`, `Cannon_PlaneTopology_Portion`, `Cannon_PlaneTopology_RegionEdges`, `Cannon_PlaneTopology_Reverse`, `Cannon_PlaneTopology_Spans`, `Cannon_PlaneTopology_SquareSide`, `Cannon_PlaneTopology_Straight`, `Cannon_PlaneTopology_TameEdgeIncidenceLocal`, `Cannon_PlaneTopology_TameGraphFlatChart`, `Cannon_PlaneTopology_VertexLines`, `Cannon_ScalarLimits_Dirac`, `Cannon_ScalarLimits_EscapingLevelsAlong`, `Cannon_ScalarLimits_Exhaustion`, `Cannon_ScalarLimits_InteriorScalar`, `Cannon_Topology_Glue`, `Cannon_Uniformization_EventualRelativeShrink`.
--
--   **Imports.** It imports the published bundle `Def_CannonGeometricAction`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ046C002`; the statements `OAI.CannonBeltrami.normalized_smooth_beltrami_solution`, `OAI.CannonConformal.measurable_structure_integration`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.circle_packing`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.disk_disjoint_of_interior`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.univalent_triangles`, `OAI.CannonEmbeddedArc.Arc.exists_global_radius_constant`, `OAI.CannonEmbeddedArc.Arc.face_incidence_card_le`, `OAI.CannonEmbeddedArc.Arc.facialCycle_exists`, `OAI.CannonEmbeddedArc.Arc.intrinsic_developed_faces`, `OAI.CannonEmbeddedArc.Arc.proper_facial_bound`, `OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates` and `OAI.CannonPlanarEuler.triangular_counts`; the proofs of `OAI.CannonBeltrami.normalized_smooth_beltrami_solution`, `OAI.CannonConformal.measurable_structure_integration`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.circle_packing`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.univalent_triangles`, `OAI.CannonEmbeddedArc.Arc.exists_global_radius_constant`, `OAI.CannonEmbeddedArc.Arc.face_incidence_card_le`, `OAI.CannonEmbeddedArc.Arc.facialCycle_exists` and `OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates`.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/Cannon at commit adc7f12

import Mathlib
import Definitions.Def_CannonGeometricAction

section
-- module Solutions.OAIQ046_CN.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set Filter Topology
open scoped OnePoint

namespace CannonMobius
abbrev Sphere := OnePoint ℂ

def inv (p : Sphere) : Sphere :=
  p.elim ((0:ℂ):Sphere) (fun z => if z=0 then ∞ else (z⁻¹:ℂ))

@[simp] lemma inv_infty : inv ∞=((0:ℂ):Sphere) := rfl
@[simp] lemma inv_zero : inv ((0:ℂ):Sphere)=∞ := by simp [inv]
lemma inv_coe {z : ℂ} (hz : z ≠ 0) : inv (z:Sphere)=(z⁻¹:ℂ) := by simp [inv,hz]

lemma inv_involutive : Function.Involutive inv := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z=0
    · simp [hz]
    · rw [inv_coe hz,inv_coe (inv_ne_zero hz),inv_inv]

lemma continuous_inv : Continuous inv := by
  rw [OnePoint.continuous_iff]
  constructor
  · have ht : Tendsto (fun z : ℂ => ((z⁻¹:ℂ):Sphere)) (coclosedCompact ℂ)
        (𝓝 ((0:ℂ):Sphere)) := by
      apply OnePoint.continuous_coe.continuousAt.tendsto.comp
      simpa only [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded : Tendsto Inv.inv (Bornology.cobounded ℂ) (𝓝 (0:ℂ)))
    apply ht.congr'
    have hn : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
      rw [coclosedCompact_eq_cocompact]
      exact isCompact_singleton.compl_mem_cocompact
    filter_upwards [hn] with z hz
    exact (inv_coe hz).symm
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z=0
    · subst z
      have ht : Tendsto (fun z : ℂ => ((z⁻¹:ℂ):Sphere)) (𝓝[≠] (0:ℂ)) (𝓝 ∞) := by
        apply OnePoint.tendsto_coe_infty.comp
        simpa only [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact] using
          (tendsto_inv₀_nhdsNE_zero : Tendsto Inv.inv (𝓝[≠] (0:ℂ)) (Bornology.cobounded ℂ))
      have hcon : Tendsto (fun z : ℂ => inv (z:Sphere)) (𝓝[≠] (0:ℂ)) (𝓝 ∞) := ht.congr'
        (Filter.Eventually.mono self_mem_nhdsWithin (fun z hz => (inv_coe hz).symm))
      have hw : ContinuousWithinAt (fun z : ℂ => inv (z:Sphere)) (univ \ {0}) 0 := by
        simpa only [ContinuousWithinAt,compl_eq_univ_sdiff,inv_zero] using hcon
      exact (continuousWithinAt_univ _ _).mp (continuousWithinAt_sdiff_self.mp hw)
    · apply (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact inv_coe hw

def inversion : Sphere ≃ₜ Sphere where
  toFun := inv
  invFun := inv
  left_inv := inv_involutive
  right_inv := inv_involutive
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv

end CannonMobius

noncomputable section
open Set Filter Topology

namespace CannonConformal

lemma homeomorph_tendsto_cobounded (f : ℂ ≃ₜ ℂ) :
    Tendsto f (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
  simpa only [Metric.cobounded_eq_cocompact] using f.isClosedEmbedding.tendsto_cocompact

def inverted (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z⁻¹)⁻¹

lemma inverted_zero {f : ℂ → ℂ} (h0 : f 0=0) : inverted f 0=0 := by
  simp [inverted,h0]

lemma inverted_continuousAt_zero (f : ℂ ≃ₜ ℂ) (h0 : f 0=0) :
    ContinuousAt (inverted f) 0 := by
  have ht : Tendsto (inverted f) (𝓝[≠] (0:ℂ)) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp ((homeomorph_tendsto_cobounded f).comp tendsto_inv₀_nhdsNE_zero)
  have hw : ContinuousWithinAt (inverted f) (univ \ {0}) 0 := by
    simpa only [ContinuousWithinAt,compl_eq_univ_sdiff,inverted_zero h0] using ht
  exact (continuousWithinAt_univ _ _).mp (continuousWithinAt_sdiff_self.mp hw)

lemma inverted_differentiable (f : ℂ ≃ₜ ℂ) (h0 : f 0=0)
    (hf : Differentiable ℂ f) : Differentiable ℂ (inverted f) := by
  have hn (z : ℂ) (hz : z ≠ 0) : f z⁻¹ ≠ 0 := by
    intro hh
    exact (inv_ne_zero hz) (f.injective (hh.trans h0.symm))
  have hp (z : ℂ) (hz : z ≠ 0) : DifferentiableAt ℂ (inverted f) z :=
    ((hf z⁻¹).comp z (differentiableAt_id.inv hz)).inv (hn z hz)
  intro z
  by_cases hz : z=0
  · subst z
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (show ∀ᶠ z : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ (inverted f) z from
        Filter.Eventually.mono self_mem_nhdsWithin (fun z hz => hp z hz))
      (inverted_continuousAt_zero f h0)).differentiableAt
  · exact hp z hz

lemma inverted_leftInverse (f : ℂ ≃ₜ ℂ) :
    Function.LeftInverse (inverted f.symm) (inverted f) := by
  intro z
  simp [inverted]

theorem biholomorphic_fix_zero_linear (f : ℂ ≃ₜ ℂ) (h0 : f 0=0)
    (hf : Differentiable ℂ f) (hfi : Differentiable ℂ f.symm) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ z, f z=a*z := by
  let g := inverted f
  let gi := inverted f.symm
  have h0i : f.symm 0=0 := f.injective (by simp [h0])
  have hg : Differentiable ℂ g := inverted_differentiable f h0 hf
  have hgi : Differentiable ℂ gi := inverted_differentiable f.symm h0i hfi
  have hg0 : g 0=0 := inverted_zero h0
  have hcomp : gi ∘ g=id := funext (inverted_leftInverse f)
  have hd := (hgi (g 0)).hasDerivAt.comp 0 (hg 0).hasDerivAt
  have ha : deriv g 0 ≠ 0 := by
    have hh : deriv gi (g 0)*deriv g 0=1 := by
      rw [hcomp] at hd
      exact hd.unique (hasDerivAt_id 0)
    intro he
    rw [he,mul_zero] at hh
    exact zero_ne_one hh
  let a : ℂ := (deriv g 0)⁻¹
  have hds : Differentiable ℂ (dslope f 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (by simp)).mpr hf.differentiableOn)
  have ht : Tendsto (fun z : ℂ => (dslope g 0 z⁻¹)⁻¹)
      (Bornology.cobounded ℂ) (𝓝 a) := by
    have hh := (continuousAt_dslope_same.mpr (hg 0)).tendsto.comp tendsto_inv₀_cobounded
    rw [dslope_same] at hh
    exact hh.inv₀ ha
  have heq : (fun z : ℂ => (dslope g 0 z⁻¹)⁻¹) =ᶠ[Bornology.cobounded ℂ]
      dslope f 0 := by
    have hn : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 := by
      rw [Metric.cobounded_eq_cocompact]
      exact isCompact_singleton.compl_mem_cocompact
    filter_upwards [hn] with z hz
    have hfz : f z ≠ 0 := fun hh => hz (f.injective (hh.trans h0.symm))
    rw [dslope_of_ne _ (inv_ne_zero hz),dslope_of_ne _ hz]
    simp only [slope,g,inverted,inv_inv,inv_zero,h0,vsub_eq_sub,sub_zero,smul_eq_mul]
    field_simp
  have ht' : Tendsto (dslope f 0) (cocompact ℂ) (𝓝 a) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact ht.congr' heq
  refine ⟨a,inv_ne_zero ha,?_⟩
  intro z
  have hh := hds.apply_eq_of_tendsto_cocompact z ht'
  by_cases hz : z=0
  · simp [hz,h0]
  · rw [dslope_of_ne _ hz] at hh
    simp only [slope,h0,vsub_eq_sub,sub_zero,smul_eq_mul] at hh
    calc
      f z = z*(z⁻¹*f z) := by rw [← mul_assoc,mul_inv_cancel₀ hz,one_mul]
      _ = a*z := by rw [hh,mul_comm]

theorem biholomorphic_affine (f : ℂ ≃ₜ ℂ)
    (hf : Differentiable ℂ f) (hfi : Differentiable ℂ f.symm) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z=a*z+b := by
  let h := f.trans (Homeomorph.addRight (-f 0))
  have h0 : h 0=0 := by simp [h]
  have hd : Differentiable ℂ h := hf.add_const (-f 0)
  have hdi : Differentiable ℂ h.symm := by
    change Differentiable ℂ (fun z => f.symm (z + -(-f 0)))
    simpa only [neg_neg,Function.comp_def,id_eq] using
      hfi.comp (differentiable_id.add_const (f 0))
  obtain ⟨a,ha,he⟩ := biholomorphic_fix_zero_linear h h0 hd hdi
  refine ⟨a,f 0,ha,?_⟩
  intro z
  have hh := he z
  change f z + -(f 0)=a*z at hh
  linear_combination hh
end CannonConformal

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

def coordinate (p : Sphere) : ℂ := p.elim 0 id
@[simp] lemma coordinate_coe (z : ℂ) : coordinate (z:Sphere)=z := rfl
@[simp] lemma coordinate_infty : coordinate ∞=0 := rfl
lemma coe_coordinate {p : Sphere} (hp : p ≠ ∞) : (coordinate p:Sphere)=p := by
  induction p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z => rfl

lemma continuousAt_coordinate {p : Sphere} (hp : p ≠ ∞) : ContinuousAt coordinate p := by
  induction p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z => exact OnePoint.continuousAt_coe.mpr continuousAt_id

lemma coe_map_ne_infty (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) (z : ℂ) : f (z:Sphere) ≠ ∞ :=
  fun he => OnePoint.coe_ne_infty z (f.injective (he.trans hf.symm))

lemma symm_infty (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) : f.symm ∞=∞ := by
  apply f.injective
  rw [f.apply_symm_apply,hf]

def finiteRestriction (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞) : ℂ ≃ₜ ℂ where
  toFun z := coordinate (f (z:Sphere))
  invFun z := coordinate (f.symm (z:Sphere))
  left_inv z := by
    change coordinate (f.symm (coordinate (f (z:Sphere)):Sphere))=z
    rw [coe_coordinate (coe_map_ne_infty f hf z),f.symm_apply_apply,coordinate_coe]
  right_inv z := by
    change coordinate (f (coordinate (f.symm (z:Sphere)):Sphere))=z
    rw [coe_coordinate (coe_map_ne_infty f.symm (symm_infty f hf) z),f.apply_symm_apply,coordinate_coe]
  continuous_toFun := continuous_iff_continuousAt.mpr (fun z =>
    ContinuousAt.comp (f := fun w : ℂ => f (w:Sphere)) (x := z)
      (continuousAt_coordinate (coe_map_ne_infty f hf z))
      (f.continuous.comp OnePoint.continuous_coe).continuousAt)
  continuous_invFun := continuous_iff_continuousAt.mpr (fun z =>
    ContinuousAt.comp (f := fun w : ℂ => f.symm (w:Sphere)) (x := z)
      (continuousAt_coordinate (coe_map_ne_infty f.symm (symm_infty f hf) z))
      (f.symm.continuous.comp OnePoint.continuous_coe).continuousAt)

def chart : Bool → Sphere ≃ₜ Sphere
  | false => 1
  | true => inversion

lemma chart_involutive (b : Bool) (p : Sphere) : chart b (chart b p)=p := by
  cases b
  · rfl
  · exact inv_involutive p

@[simp] lemma coordinate_inv_coe (z : ℂ) : coordinate (inv (z:Sphere))=z⁻¹ := by
  by_cases hz : z=0
  · simp [hz]
  · rw [inv_coe hz,coordinate_coe]

def inChart (s t : Bool) (f : Sphere ≃ₜ Sphere) (z : ℂ) : ℂ :=
  coordinate (chart t (f (chart s (z:Sphere))))
def chartDomain (s t : Bool) (f : Sphere ≃ₜ Sphere) : Set ℂ :=
  {z | chart t (f (chart s (z:Sphere))) ≠ ∞}

lemma isOpen_chartDomain (s t : Bool) (f : Sphere ≃ₜ Sphere) : IsOpen (chartDomain s t f) :=
  isOpen_compl_singleton.preimage ((chart t).continuous.comp
    (f.continuous.comp ((chart s).continuous.comp OnePoint.continuous_coe)))

def IsAnalytic (f : Sphere ≃ₜ Sphere) : Prop :=
  ∀ s t, DifferentiableOn ℂ (inChart s t f) (chartDomain s t f)

lemma analytic_differentiableAt {f : Sphere ≃ₜ Sphere} (hf : IsAnalytic f)
    (s t : Bool) {z : ℂ} (hz : z ∈ chartDomain s t f) :
    DifferentiableAt ℂ (inChart s t f) z :=
  (hf s t z hz).differentiableAt ((isOpen_chartDomain s t f).mem_nhds hz)

lemma isAnalytic_mul {f g : Sphere ≃ₜ Sphere} (hf : IsAnalytic f) (hg : IsAnalytic g) :
    IsAnalytic (f*g) := by
  classical
  intro s t z hz
  let p := g (chart s (z:Sphere))
  let u : Bool := if p=∞ then true else false
  have hu : chart u p ≠ ∞ := by
    by_cases hp : p=∞
    · dsimp [u]
      rw [ite_eq_left hp]
      change inv p ≠ ∞
      rw [hp,inv_infty]
      exact OnePoint.coe_ne_infty 0
    · simp [u,hp,chart]
  have hgdom : z ∈ chartDomain s u g := hu
  have he : chart u (inChart s u g z : Sphere)=p := by
    change chart u (coordinate (chart u p):Sphere)=p
    rw [coe_coordinate hu,chart_involutive]
  have hfdom : inChart s u g z ∈ chartDomain u t f := by
    change chart t (f (chart u (inChart s u g z:Sphere))) ≠ ∞
    rw [he]
    exact hz
  have hd := (analytic_differentiableAt hf u t hfdom).comp z
    (analytic_differentiableAt hg s u hgdom)
  apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  have hn : ∀ᶠ w in 𝓝 z, w ∈ chartDomain s u g := (isOpen_chartDomain s u g).mem_nhds hgdom
  filter_upwards [hn] with w hw
  change coordinate (chart t (f (g (chart s (w:Sphere)))) )=
    coordinate (chart t (f (chart u (coordinate (chart u (g (chart s (w:Sphere)))):Sphere))))
  rw [coe_coordinate hw,chart_involutive]

lemma restriction_differentiable (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞)
    (ha : IsAnalytic f) : Differentiable ℂ (finiteRestriction f hf) := by
  intro z
  exact analytic_differentiableAt ha false false (coe_map_ne_infty f hf z)

theorem analytic_fix_infty_affine (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞)
    (ha : IsAnalytic f) (hi : IsAnalytic f.symm) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, f (z:Sphere)=(a*z+b:ℂ) := by
  obtain ⟨a,b,ha',he⟩ := CannonConformal.biholomorphic_affine (finiteRestriction f hf)
    (restriction_differentiable f hf ha)
    (restriction_differentiable f.symm (symm_infty f hf) hi)
  refine ⟨a,b,ha',?_⟩
  intro z
  have hh := congrArg (fun z : ℂ => (z:Sphere)) (he z)
  exact (coe_coordinate (coe_map_ne_infty f hf z)).symm.trans hh
end CannonMobius

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Next
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonCycleOrder
open Set SimpleGraph

def next {n:ℕ} (hn:0<n) (i:Fin n) : Fin n :=
  if h:i.val+1<n then ⟨i.val+1,h⟩ else ⟨0,hn⟩

def bipartite {E A:Type*} (R:E→A→Prop) : SimpleGraph (E⊕A) where
  Adj
    | .inl e,.inr a => R e a
    | .inr a,.inl e => R e a
    | _,_ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

def tag {E A:Type*} : E⊕A→ℕ | .inl _ => 0 | .inr _ => 1

end CannonCycleOrder

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_AngleGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variational angle functional for a conformal circle packing. -/

section
section
section
section
namespace CannonPackingGeometry
open Set Filter Topology MeasureTheory

noncomputable section

def angleGradient (θ : ℝ) : ℝ := Real.log (Real.sin (θ/2)) - Real.log (Real.cos (θ/2))

end
end CannonPackingGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Region
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonFaceIncidence
variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

def region (V : Set X) (π : V → D) (d : D) : Set X :=
  {x | ∃ h : x∈V, π ⟨x,h⟩=d}

def incident (V : Set X) (π : V → D) (x : X) : Set D :=
  {d | x∈closure (region V π d)}

omit [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D] in
lemma region_subset (V : Set X) (π : V → D) (d : D) : region V π d⊆V := by
  rintro x ⟨hx,_⟩
  exact hx

lemma region_isOpen {V : Set X} (hV : IsOpen V) {π : V → D} (hπ : Continuous π) (d : D) :
    IsOpen (region V π d) := by
  have he : region V π d=Subtype.val '' (π ⁻¹' {d}) := by
    ext x
    simp only [region,mem_ofPred_eq,mem_image,mem_preimage,mem_singleton_iff]
    constructor
    · rintro ⟨hx,he⟩
      exact ⟨⟨x,hx⟩,he,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.property,hx⟩
  rw [he]
  exact hV.isOpenMap_subtype_val _ (hπ.isOpen_preimage _ (isOpen_discrete _))

lemma label_on_connected {V S : Set X} {π : V → D} (hπ : Continuous π)
    (hS : IsConnected S) (hSV : S⊆V) : ∃ d : D, S⊆region V π d := by
  let _ : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS.isPreconnected
  obtain ⟨x,hx⟩ := hS.nonempty
  let f : S → D := fun y => π ⟨y.val,hSV y.property⟩
  have hf : Continuous f := hπ.comp (by fun_prop)
  refine ⟨f ⟨x,hx⟩,fun y hy => ⟨hSV hy,?_⟩⟩
  exact (IsLocallyConstant.iff_continuous f).mpr hf |>.apply_eq_of_preconnectedSpace ⟨y,hy⟩ ⟨x,hx⟩

theorem sector_incidence {V W B : Set X} (hW : IsOpen W) (hBW : B⊆W)
    {π : V → D} (hπ : Continuous π) {ι : Type*} [Finite ι]
    (S : ι → Set X) (hS : ∀ i, IsConnected (S i))
    (hcover : W∩V=⋃ i, S i) (hclose : ∀ i, B⊆closure (S i)) :
    ∃ labels : ι → D, (∀ i, S i⊆region V π (labels i)) ∧
      ∀ x∈B, incident V π x=range labels := by
  classical
  have hSV (i : ι) : S i⊆V := by
    intro x hx
    exact (hcover.symm ▸ mem_iUnion_of_mem i hx).2
  choose labels hlabels using fun i => label_on_connected hπ (hS i) (hSV i)
  refine ⟨labels,hlabels,?_⟩
  intro x hx
  ext d
  constructor
  · intro hd
    by_contra hn
    have hnone : W∩region V π d=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hyW,hyR⟩
      have hyWV : y∈W∩V := ⟨hyW,region_subset V π d hyR⟩
      rw [hcover] at hyWV
      obtain ⟨i,hi⟩ := mem_iUnion.mp hyWV
      obtain ⟨hy,he⟩ := hlabels i hi
      obtain ⟨hy',he'⟩ := hyR
      apply hn
      exact ⟨i,he.symm.trans he'⟩
    have hm : (W∩region V π d).Nonempty :=
      (mem_closure_iff_nhds.mp hd) W (hW.mem_nhds (hBW hx))
    rw [hnone] at hm
    exact not_nonempty_empty hm
  · rintro ⟨i,rfl⟩
    exact closure_mono (hlabels i) (hclose i hx)

omit [TopologicalSpace D] [DiscreteTopology D] in

theorem incident_constant_on_preconnected {V A : Set X} {π : V → D}
    (hA : IsPreconnected A)
    (hloc : ∀ x∈A, ∃ W : Set X, IsOpen W ∧ x∈W ∧
      ∀ y∈A∩W, incident V π y=incident V π x) :
    ∀ x∈A, ∀ y∈A, incident V π x=incident V π y := by
  let _ : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp hA
  let f : A → Set D := fun x => incident V π x.val
  have hf : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_eventually_eq f).mpr
    intro x
    obtain ⟨W,hW,hxW,heq⟩ := hloc x.val x.property
    filter_upwards [(continuous_subtype_val.isOpen_preimage W hW).mem_nhds hxW] with y hy
    exact heq y.val ⟨y.property,hy⟩
  intro x hx y hy
  exact hf.apply_eq_of_preconnectedSpace ⟨x,hx⟩ ⟨y,hy⟩

end CannonFaceIncidence

namespace CannonFaceIncidence
open Set Metric Topology

def openBox (r : ℝ) : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) r
def halfBox (r : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  Ioo (-r) r ×ˢ (if b then Ioo 0 r else Ioo (-r) 0)

lemma openBox_eq_ball (r : ℝ) : openBox r=ball (0,0) r := by
  rw [←ball_prod_same,Real.ball_eq_Ioo]
  simp [openBox]

lemma halfBox_connected {r : ℝ} (hr : 0 < r) (b : Bool) : IsConnected (halfBox r b) := by
  cases b
  · exact (isConnected_Ioo (by linarith : -r < r)).prod (isConnected_Ioo (neg_neg_of_pos hr))
  · exact (isConnected_Ioo (by linarith : -r < r)).prod (isConnected_Ioo hr)

lemma halfBox_closure {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ}
    (hp : p∈openBox r) (hp₂ : p.2=0) (b : Bool) : p∈closure (halfBox r b) := by
  have hrr : -r < r := by linarith
  cases b <;> simp only [halfBox,Bool.false_eq_true,↓reduceIte,closure_prod_eq]
  · rw [closure_Ioo hrr.ne,closure_Ioo (neg_neg_of_pos hr).ne]
    exact ⟨⟨hp.1.1.le,hp.1.2.le⟩,by rw [hp₂]; exact ⟨(neg_neg_of_pos hr).le,le_rfl⟩⟩
  · rw [closure_Ioo hrr.ne,closure_Ioo hr.ne]
    exact ⟨⟨hp.1.1.le,hp.1.2.le⟩,by rw [hp₂]; exact ⟨le_rfl,hr.le⟩⟩

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

theorem flat_chart_incidence {V W : Set X} {π : V → D} (hπ : Continuous π)
    (H : (ℝ × ℝ) ≃ₜ X) (hW : IsOpen W) (h₀ : H (0,0)∈W)
    (hflat : ∀ z∈W, z∈V ↔ (H.symm z).2≠0) :
    ∃ U : Set X, IsOpen U ∧ H (0,0)∈U ∧ U⊆W ∧
      ∃ labels : Bool → D, ∀ x∈U∩Vᶜ, incident V π x=range labels := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage H.continuous).mem_nhds h₀)
  let C := openBox r
  let U := H '' C
  have hCU : C⊆H ⁻¹' W := by rw [show C=openBox r from rfl,openBox_eq_ball]; exact hball
  have hUW : U⊆W := by rintro _ ⟨p,hp,rfl⟩; exact hCU hp
  have hU : IsOpen U := H.isOpenMap C (by rw [show C=openBox r from rfl,openBox_eq_ball]; exact isOpen_ball)
  have h₀U : H (0,0)∈U := ⟨(0,0),by rw [show C=openBox r from rfl,openBox_eq_ball]; exact mem_ball_self hr,rfl⟩
  let S : Bool → Set X := fun b => H '' halfBox r b
  have hSc (b : Bool) : IsConnected (S b) :=
    (halfBox_connected hr b).image H H.continuous.continuousOn
  have hcover : U∩V=⋃ b, S b := by
    ext x
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hpV⟩
      have hp₂ : p.2≠0 := by simpa using (hflat (H p) (hCU hp)).mp hpV
      rcases lt_or_gt_of_ne hp₂ with hl|hr'
      · exact mem_iUnion.mpr ⟨false,⟨p,⟨hp.1,hp.2.1,hl⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨true,⟨p,⟨hp.1,hr',hp.2.2⟩,rfl⟩⟩
    · intro hx
      obtain ⟨b,p,hp,rfl⟩ := mem_iUnion.mp hx
      have hpC : p∈C := by
        cases b
        · exact ⟨hp.1,hp.2.1,hp.2.2.trans hr⟩
        · exact ⟨hp.1,(neg_neg_of_pos hr).trans hp.2.1,hp.2.2⟩
      refine ⟨⟨p,hpC,rfl⟩,(hflat (H p) (hCU hpC)).mpr ?_⟩
      simp only [H.symm_apply_apply]
      cases b
      · exact hp.2.2.ne
      · exact hp.2.1.ne'
  have hclose (b : Bool) : U∩Vᶜ⊆closure (S b) := by
    rintro x ⟨⟨p,hp,hpx⟩,hxV⟩
    subst x
    have hp₂ : p.2=0 := by
      by_contra h
      apply hxV
      apply (hflat (H p) (hCU hp)).mpr
      simpa using h
    rw [show S b=H '' halfBox r b from rfl,←H.image_closure]
    exact ⟨p,halfBox_closure hr hp hp₂ b,rfl⟩
  obtain ⟨labels,_,hlabels⟩ := sector_incidence hU inter_subset_left hπ S hSc hcover hclose
  exact ⟨U,hU,h₀U,hUW,labels,hlabels⟩
end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_HomeomorphComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonFaceIncidence
open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def homeomorphComponents (e : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y :=
  Equiv.ofBijective e.continuous.connectedComponentsMap
    (e.isQuotientMap.isCoinducing.connectedComponentsMap_bijective (fun y => by
      have he : e ⁻¹' {y}={e.symm y} := by
        ext x
        exact ⟨fun h => by simpa using congrArg e.symm h, fun h => by
          change x=e.symm y at h
          rw [h]
          exact e.apply_symm_apply y⟩
      rw [he]
      exact isConnected_singleton))

noncomputable def componentsDeletionEquiv (V : Set X) (S : Set X)
    [DiscreteTopology (ConnectedComponents V)] :
    ConnectedComponents (V\S : Set X) ≃
      Σ d : ConnectedComponents V, ConnectedComponents (region V ConnectedComponents.mk d\S : Set X) := by
  let U (d : ConnectedComponents V) : Set (V\S : Set X) :=
    {x | x.val∈region V ConnectedComponents.mk d}
  let π : (V\S : Set X) → ConnectedComponents V := fun x => ConnectedComponents.mk ⟨x.val,x.property.1⟩
  have hπ : Continuous π := ConnectedComponents.continuous_coe.comp (continuous_subtype_val.subtype_mk _)
  have hU (d : ConnectedComponents V) : U d=π ⁻¹' {d} := by
    ext x
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨x.property.1,h⟩
  have hcl (d : ConnectedComponents V) : IsClopen (U d) := by
    rw [hU]
    exact (isClopen_discrete {d}).preimage hπ
  have hdis : Pairwise (Function.onFun Disjoint U) := by
    intro d e hde
    apply Set.disjoint_left.mpr
    intro x hd he
    exact hde (hd.2.symm.trans he.2)
  have hcover : ⋃ d,U d=univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨π x,x.property.1,rfl⟩
  let E (d : ConnectedComponents V) : U d ≃ₜ (region V ConnectedComponents.mk d\S : Set X) :=
    { toFun := fun z => ⟨z.val.val,z.property,z.val.property.2⟩
      invFun := fun z => ⟨⟨z.val,(region_subset _ _ d z.property.1),z.property.2⟩,z.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact (ConnectedComponents.equivOfIsClopen hcl hdis hcover).trans
    (Equiv.sigmaCongrRight fun d => homeomorphComponents (E d))

end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_ClosureRegionInside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonFaceIncidence
variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

lemma closure_region_inside {V : Set X} (hV : IsOpen V) {π : V → D}
    (hπ : Continuous π) {d : D} {x : X} (hx : x∈closure (region V π d))
    (hxV : x∈V) : x∈region V π d := by
  let d₀ := π ⟨x,hxV⟩
  have hR := region_isOpen hV hπ d₀
  have hxR : x∈region V π d₀ := ⟨hxV,rfl⟩
  obtain ⟨y,⟨hyV,hyd₀⟩,⟨hyV',hyd⟩⟩ :=
    (mem_closure_iff_nhds.mp hx) _ (hR.mem_nhds hxR)
  exact ⟨hxV,hyd₀.symm.trans hyd⟩

theorem region_boundary_hits {K T : Set X} (hK : IsClosed K) (hT : IsClosed T)
    (hTK : T⊆K) (hconn : IsPreconnected Tᶜ) (hne : (K\T).Nonempty)
    {π : (Kᶜ : Set X) → D} (hπ : Continuous π) (d : D)
    (hd : (region Kᶜ π d).Nonempty) :
    ∃ x∈K, x∉T ∧ d∈incident Kᶜ π x := by
  by_contra hn
  have hbound : closure (region Kᶜ π d)⊆region Kᶜ π d∪T := by
    intro x hx
    by_cases hxK : x∈K
    · right
      by_contra hxT
      exact hn ⟨x,hxK,hxT,hx⟩
    · exact Or.inl (closure_region_inside hK.isOpen_compl hπ hx hxK)
  have hclosed : IsClosed (region Kᶜ π d∪T) := by
    apply isClosed_of_closure_subset
    rw [closure_union,hT.closure_eq]
    exact union_subset hbound subset_union_right
  let _ : PreconnectedSpace (Tᶜ : Set X) := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set (Tᶜ : Set X) := Subtype.val ⁻¹' region Kᶜ π d
  have hC : IsClopen C := by
    constructor
    · have he : C=Subtype.val ⁻¹' (region Kᶜ π d∪T) := by
        ext x
        simp only [C,mem_preimage,mem_union]
        exact or_iff_left x.property |>.symm
      rw [he]
      exact hclosed.preimage continuous_subtype_val
    · exact (region_isOpen hK.isOpen_compl hπ d).preimage continuous_subtype_val
  obtain ⟨x,hx⟩ := hd
  have hxT : x∉T := fun hxT => (region_subset Kᶜ π d hx) (hTK hxT)
  have hCe : C=univ := hC.eq_univ ⟨⟨x,hxT⟩,hx⟩
  obtain ⟨y,hyK,hyT⟩ := hne
  have hyC : (⟨y,hyT⟩ : (Tᶜ : Set X))∈C := hCe.symm ▸ mem_univ _
  exact (region_subset Kᶜ π d hyC) hyK
end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Arc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embedded arcs and compatible finite subdivisions. -/

section
section
section
noncomputable section
open Set unitInterval Topology

namespace CannonEmbeddedArc

structure Arc (X : Type*) [TopologicalSpace X] where
  map : C(I, X)
  injective : Function.Injective map

variable {X : Type*} [TopologicalSpace X]
instance instCoeFunArcForallElemRealUnitInterval : CoeFun (Arc X) (fun _ => I → X) := ⟨fun a => a.map⟩

namespace Arc
lemma continuous (a : Arc X) : Continuous a := a.map.continuous
lemma compact_range (a : Arc X) : IsCompact (range a) := isCompact_range a.continuous
lemma endpoints_ne (a : Arc X) : a 0 ≠ a 1 := fun h => by
  have := a.injective h
  exact zero_ne_one this

def path (a : Arc X) : Path (a 0) (a 1) :=
  { toContinuousMap := a.map, source' := rfl, target' := rfl }

@[simp] lemma path_apply (a : Arc X) (t : I) : a.path t = a t := rfl

def subarc (a : Arc X) (u v : I) (huv : u ≠ v) : Arc X where
  map := ⟨fun t => a (Icc.convexComb u v t),
    a.continuous.comp (Icc.continuous_convexComb u v)⟩
  injective := by
    intro s t h
    have hh := congrArg Subtype.val (a.injective h)
    simp only [Icc.coe_convexComb] at hh
    apply Subtype.ext
    have hn : (u : ℝ) ≠ v := fun h => huv (Subtype.ext h)
    have : ((s : ℝ) - t) * ((v : ℝ) - u) = 0 := by nlinarith [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hn.symm))

@[simp] lemma subarc_zero (a : Arc X) (u v : I) (huv : u ≠ v) :
    a.subarc u v huv 0 = a u := by simp [subarc]
@[simp] lemma subarc_one (a : Arc X) (u v : I) (huv : u ≠ v) :
    a.subarc u v huv 1 = a v := by simp [subarc]
lemma subarc_range_subset (a : Arc X) (u v : I) (huv : u ≠ v) :
    range (a.subarc u v huv) ⊆ range a := by
  rintro _ ⟨t,rfl⟩
  exact mem_range_self _

def spliceFun (a b : Arc X) (u v : I) (t : I) : X :=
  if t ≤ u then a t else if t ≤ v then b.path.extend (((t : ℝ)-u)/((v : ℝ)-u)) else a t

lemma spliceFun_left (a b : Arc X) (u v t : I) (ht : t ≤ u) :
    spliceFun a b u v t = a t := by simp [spliceFun,ht]

lemma continuous_spliceFun (a b : Arc X) {u v : I} (huv : u < v)
    (hstart : b 0 = a u) (hend : b 1 = a v) :
    Continuous (spliceFun a b u v) := by
  have hd : (v : ℝ)-u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
  have hb : Continuous (fun t : I => b.path.extend (((t : ℝ)-u)/((v : ℝ)-u))) :=
    b.path.continuous_extend.comp (by fun_prop)
  unfold spliceFun
  apply a.continuous.if_le
    (hb.if_le a.continuous continuous_id continuous_const ?_)
    continuous_id continuous_const ?_
  · intro t ht
    change t = v at ht
    subst t
    simpa [div_self hd] using hend
  · intro t ht
    change t = u at ht
    subst t
    simp [huv.le,hstart]

def sliceParam {u v : I} (huv : u < v) (t : I) (ht : t ∈ Icc u v) : I :=
  ⟨((t : ℝ)-u)/((v : ℝ)-u), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr (show (u : ℝ) < v from huv)).le
    · apply (div_le_one (sub_pos.mpr (show (u : ℝ)<v from huv))).2
      exact sub_le_sub_right (show (t : ℝ) ≤ v from ht.2) _⟩

lemma spliceFun_middle (a b : Arc X) {u v : I} (huv : u < v)
    (hstart : b 0 = a u) (t : I) (ht : t ∈ Icc u v) :
    spliceFun a b u v t = b (sliceParam huv t ht) := by
  by_cases htu : t ≤ u
  · have he : t=u := le_antisymm htu ht.1
    subst t
    have hs : sliceParam huv u ht=0 := by ext; simp [sliceParam]
    simp [spliceFun,hs,hstart]
  · simp only [spliceFun,htu,ite_false,ht.2,ite_true]
    exact b.path.extend_apply (sliceParam huv t ht).property

lemma spliceFun_outside (a b : Arc X) {u v t : I} (ht : t ∉ Icc u v) :
    spliceFun a b u v t = a t := by
  by_cases htu : t ≤ u
  · exact spliceFun_left a b u v t htu
  · have htv : ¬t ≤ v := fun h => ht ⟨(not_le.mp htu).le,h⟩
    simp [spliceFun,htu,htv]

lemma injective_spliceFun (a b : Arc X) {u v : I} (huv : u < v)
    (hstart : b 0 = a u) (havoid : ∀ t : I, t ∉ Icc u v → a t ∉ range b) :
    Function.Injective (spliceFun a b u v) := by
  intro s t he
  by_cases hs : s ∈ Icc u v <;> by_cases ht : t ∈ Icc u v
  · rw [spliceFun_middle a b huv hstart s hs,
      spliceFun_middle a b huv hstart t ht] at he
    have h := congrArg Subtype.val (b.injective he)
    simp only [sliceParam] at h
    have hd : (v : ℝ)-u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
    have hst := (div_left_inj' hd).mp h
    apply Subtype.ext
    linarith
  · rw [spliceFun_middle a b huv hstart s hs,spliceFun_outside a b ht] at he
    exact False.elim (havoid t ht ⟨sliceParam huv s hs,he⟩)
  · rw [spliceFun_outside a b hs,spliceFun_middle a b huv hstart t ht] at he
    exact False.elim (havoid s hs ⟨sliceParam huv t ht,he.symm⟩)
  · rw [spliceFun_outside a b hs,spliceFun_outside a b ht] at he
    exact a.injective he

def splice (a b : Arc X) {u v : I} (huv : u < v)
    (hstart : b 0 = a u) (hend : b 1 = a v)
    (havoid : ∀ t : I, t ∉ Icc u v → a t ∉ range b) : Arc X :=
  ⟨⟨spliceFun a b u v,continuous_spliceFun a b huv hstart hend⟩,
    injective_spliceFun a b huv hstart havoid⟩

@[simp] lemma splice_zero (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b) :
    splice a b huv hs he ha 0 = a 0 :=
  spliceFun_left a b u v 0 (unitInterval.nonneg u)

lemma first_last [T2Space X] (a e : Arc X) (hne : (a ⁻¹' range e).Nonempty) :
    ∃ u v : I, u≤v ∧ a u ∈ range e ∧ a v ∈ range e ∧
      ∀ t : I, a t ∈ range e → t ∈ Icc u v := by
  have hc : IsCompact (a ⁻¹' range e) :=
    (e.compact_range.isClosed.preimage a.continuous).isCompact
  obtain ⟨u,hu⟩ := hc.exists_isLeast hne
  obtain ⟨v,hv⟩ := hc.exists_isGreatest hne
  exact ⟨u,v,hu.2 hv.1,hu.1,hv.1,fun t ht => ⟨hu.2 ht,hv.2 ht⟩⟩

def Compatible (e f : Arc X) : Prop :=
  (∀ s t : I, e s = f t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
  (range e ∩ range f).Subsingleton

lemma Compatible.symm {e f : Arc X} (h : Compatible e f) : Compatible f e := by
  constructor
  · intro s t he
    exact (h.1 t s he.symm).symm
  · simpa [inter_comm] using h.2

section Convex
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

def mappedSegment (e : E → X) (he : Continuous e) (hinj : Function.Injective e)
    (x y : E) (hxy : x≠y) : Arc X where
  map := ⟨fun t => e (Path.segment x y t),he.comp (Path.segment x y).continuous⟩
  injective := hinj.comp (Path.segment_injective_of_ne hxy)

@[simp] lemma mappedSegment_zero (e : E → X) (he : Continuous e)
    (hinj : Function.Injective e) (x y : E) (hxy : x≠y) :
    mappedSegment e he hinj x y hxy 0 = e x := by simp [mappedSegment]
@[simp] lemma mappedSegment_one (e : E → X) (he : Continuous e)
    (hinj : Function.Injective e) (x y : E) (hxy : x≠y) :
    mappedSegment e he hinj x y hxy 1 = e y := by simp [mappedSegment]

end Convex

end Arc
end CannonEmbeddedArc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_GraphShear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

namespace CannonPlanarCorner

def graphShear (f : C(ℝ,ℝ)) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1,p.2+f p.1)
  invFun p := (p.1,p.2-f p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma graphShear_apply (f : C(ℝ,ℝ)) (x y : ℝ) :
    graphShear f (x,y)=(x,y+f x) := rfl

def bendHeight (m n : ℝ) : C(ℝ,ℝ) :=
  ⟨fun x => m*x+(n-m)*max x 0,by fun_prop⟩

lemma bendHeight_nonpos (m n : ℝ) {x : ℝ} (hx : x≤0) :
    bendHeight m n x=m*x := by simp [bendHeight,max_eq_right hx]
lemma bendHeight_nonneg (m n : ℝ) {x : ℝ} (hx : 0≤x) :
    bendHeight m n x=n*x := by simp [bendHeight,max_eq_left hx]; ring

lemma complex_real_inner (u v : ℂ) : inner ℝ u v=(star u*v).re := by
  simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  ring

theorem separating_multiplier {u v : ℂ} (h : ¬SameRay ℝ u v) :
    ∃ c : ℂ, c≠0 ∧ (c*u).re<0 ∧ 0<(c*v).re := by
  have hu : u≠0 := fun he => h (he ▸ SameRay.zero_left v)
  have hv : v≠0 := fun he => h (he ▸ SameRay.zero_right u)
  have hnu : 0<‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0<‖v‖ := norm_pos_iff.mpr hv
  have hlt : inner ℝ u v<‖u‖*‖v‖ := by
    apply inner_lt_norm_mul_iff_real.mpr
    intro he
    exact h (sameRay_iff_norm_smul_eq.mpr he.symm)
  let w := ‖v‖⁻¹ • v-‖u‖⁻¹ • u
  have hwu : inner ℝ w u<0 := by
    simp only [w,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    rw [real_inner_comm u v]
    have hh := (div_lt_iff₀ hnv).mpr hlt
    rw [div_eq_mul_inv,mul_comm] at hh
    have he : ‖u‖⁻¹*‖u‖^2=‖u‖ := by field_simp
    rw [he]
    exact sub_neg.mpr hh
  have hwv : 0 < inner ℝ w v := by
    simp only [w,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    have hh : ‖u‖⁻¹*inner ℝ u v<‖v‖ := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_lt_iff₀ hnu).mpr (by simpa only [mul_comm] using hlt)
    have he : ‖v‖⁻¹*‖v‖^2=‖v‖ := by field_simp
    rw [he]
    exact sub_pos.mpr hh
  refine ⟨star w,?_,?_,?_⟩
  · intro hz
    have hw : w=0 := star_eq_zero.mp hz
    simp [hw] at hwu
  · simpa only [complex_real_inner] using hwu
  · simpa only [complex_real_inner] using hwv

def ray (u : ℂ) : Set ℂ := {z | ∃ t : ℝ, 0≤t ∧ z=t•u}

def horizontal : Set (ℝ × ℝ) := {p | p.2=0}

theorem flattened_bend {u v : ℂ} (hu : u.re<0) (hv : 0<v.re) :
    let H := (graphShear (bendHeight (u.im/u.re) (v.im/v.re))).trans
      Complex.equivRealProdCLM.toHomeomorph.symm
    H '' horizontal=ray u∪ray v := by
  dsimp only
  let f := bendHeight (u.im/u.re) (v.im/v.re)
  ext z
  constructor
  · rintro ⟨⟨x,y⟩,hy,rfl⟩
    change y=0 at hy
    subst y
    by_cases hx : x≤0
    · left
      refine ⟨x/u.re,div_nonneg_of_nonpos hx hu.le,?_⟩
      apply Complex.ext
      · simp [graphShear,hu.ne]
      · simp [graphShear,bendHeight_nonpos _ _ hx]
        ring
    · right
      have hx' : 0≤x := le_of_not_ge hx
      refine ⟨x/v.re,div_nonneg hx' hv.le,?_⟩
      apply Complex.ext
      · simp [graphShear,hv.ne']
      · simp [graphShear,bendHeight_nonneg _ _ hx']
        ring
  · rintro (⟨t,ht,rfl⟩|⟨t,ht,rfl⟩)
    · refine ⟨(t*u.re,0),rfl,?_⟩
      have hx : t*u.re≤0 := mul_nonpos_of_nonneg_of_nonpos ht hu.le
      apply Complex.ext
      · simp [graphShear]
      · simp [graphShear,bendHeight_nonpos _ _ hx]
        field_simp [hu.ne]
    · refine ⟨(t*v.re,0),rfl,?_⟩
      have hx : 0≤t*v.re := mul_nonneg ht hv.le
      apply Complex.ext
      · simp [graphShear]
      · simp [graphShear,bendHeight_nonneg _ _ hx]
        field_simp [hv.ne']

theorem straighten_corner {u v : ℂ} (h : ¬SameRay ℝ u v) :
    ∃ H : (ℝ × ℝ) ≃ₜ ℂ, H (0,0)=0 ∧ H '' horizontal=ray u∪ray v := by
  obtain ⟨c,hc,hu,hv⟩ := separating_multiplier h
  let L : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ c hc
  let H₀ := (graphShear (bendHeight ((c*u).im/(c*u).re) ((c*v).im/(c*v).re))).trans
    Complex.equivRealProdCLM.toHomeomorph.symm
  have hH₀ : H₀ '' horizontal=ray (c*u)∪ray (c*v) := flattened_bend hu hv
  have hL (w : ℂ) : L '' ray w=ray (c*w) := by
    ext z
    constructor
    · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
      exact ⟨t,ht,by simp [L,mul_left_comm]⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t•w,⟨t,ht,rfl⟩,by simp [L,mul_left_comm]⟩
  refine ⟨H₀.trans L.symm,?_,?_⟩
  · have hzero : H₀ (0,0)=0 := by
      apply Complex.ext <;> simp [H₀,graphShear,bendHeight]
    simp only [Homeomorph.trans_apply,hzero]
    apply L.injective
    simp [L]
  · change (L.symm ∘ H₀) '' horizontal=ray u∪ray v
    rw [Set.image_comp]
    rw [hH₀,←hL u,←hL v,←image_union,Set.image_image]
    simp

end CannonPlanarCorner

namespace CannonPlanarCorner

lemma local_ray_segment {x u z : ℂ} {r : ℝ} (hru : r≤‖u‖) (hz : z∈ball x r) :
    (∃ s : ℝ, 0 ≤ s ∧ z = x+s•u) ↔ z∈segment ℝ x (x+u) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨s,hs,rfl⟩
    have hd : s*‖u‖ < r := by
      simpa [dist_eq_norm,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs] using hz
    have hu : 0<‖u‖ := by
      have : 0 < r := (norm_nonneg (s•u)).trans_lt (by simpa [dist_eq_norm] using hz)
      exact this.trans_le hru
    have hs₁ : s≤1 := by nlinarith
    exact ⟨s,⟨hs,hs₁⟩,by simp⟩
  · rintro ⟨s,hs,he⟩
    exact ⟨s,hs.1,by simpa using he.symm⟩
end CannonPlanarCorner

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Consecutive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

namespace CannonEmbeddedArc
open Set unitInterval

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma interval_of_ordConnected [T2Space X] (a e : Arc X)
    (hc : OrdConnected (a ⁻¹' range e)) :
    (a ⁻¹' range e)=∅ ∨ ∃ u v : I, u≤v ∧ a ⁻¹' range e=Icc u v := by
  by_cases hne : (a ⁻¹' range e).Nonempty
  · obtain ⟨u,v,huv,hu,hv,hfl⟩ := first_last a e hne
    exact Or.inr ⟨u,v,huv,Subset.antisymm hfl (hc.out hu hv)⟩
  · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

theorem finite_breakpoints [T2Space X] {ι : Type*} (E : ι → Arc X)
    (S : Finset ι) (a : Arc X) (hc : ∀ i ∈ S, OrdConnected (a ⁻¹' range (E i))) :
    ∃ P : Finset I, 0∈P ∧ 1∈P ∧ P.card ≤ 2*S.card+2 ∧
      ∀ i ∈ S, (a ⁻¹' range (E i))=∅ ∨
        ∃ u∈P, ∃ v∈P, u≤v ∧ a ⁻¹' range (E i)=Icc u v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨{0,1},by simp,by simp,by simp,?_⟩
    simp
  | @insert i S hi ih =>
    obtain ⟨P,hP₀,hP₁,hcard,hP⟩ := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    rcases interval_of_ordConnected a (E i) (hc i (Finset.mem_insert_self _ _)) with he|⟨u,v,huv,he⟩
    · refine ⟨P,hP₀,hP₁,hcard.trans ?_,?_⟩
      · simp only [Finset.card_insert_of_notMem hi]
        omega
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl|hj
        · exact Or.inl he
        · exact hP j hj
    · let Q := insert u (insert v P)
      have hPQ : P ⊆ Q := Finset.subset_insert _ _ |>.trans (Finset.subset_insert _ _)
      refine ⟨Q,hPQ hP₀,hPQ hP₁,?_,?_⟩
      · have hv := Finset.card_insert_le v P
        have hu := Finset.card_insert_le u (insert v P)
        simp only [Finset.card_insert_of_notMem hi]
        change (insert u (insert v P)).card ≤ _
        omega
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl|hj
        · exact Or.inr ⟨u,Finset.mem_insert_self _ _,v,
            Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),huv,he⟩
        · rcases hP j hj with he|⟨p,hp,q,hq,hpq,he⟩
          · exact Or.inl he
          · exact Or.inr ⟨p,hPQ hp,q,hPQ hq,hpq,he⟩

def Consecutive (P : Finset I) (p q : I) : Prop :=
  p∈P ∧ q∈P ∧ p<q ∧ ∀ t∈P, p<t → t<q → False

lemma consecutive_cover (P : Finset I) (h₀ : 0∈P) (h₁ : 1∈P) (t : I) :
    ∃ p q : I, Consecutive P p q ∧ t ∈ Icc p q := by
  classical
  by_cases ht : t<1
  · let L := P.filter (· ≤ t)
    let R := P.filter (t < ·)
    have hL : L.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨h₀,unitInterval.nonneg t⟩⟩
    have hR : R.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨h₁,ht⟩⟩
    let p := L.max' hL
    let q := R.min' hR
    have hp := Finset.mem_filter.mp (Finset.max'_mem L hL)
    have hq := Finset.mem_filter.mp (Finset.min'_mem R hR)
    refine ⟨p,q,⟨hp.1,hq.1,hp.2.trans_lt hq.2,?_⟩,hp.2,hq.2.le⟩
    intro z hz hpz hzq
    rcases le_or_gt z t with hzt|htz
    · exact hpz.not_ge (Finset.le_max' L z (Finset.mem_filter.mpr ⟨hz,hzt⟩))
    · exact hzq.not_ge (Finset.min'_le R z (Finset.mem_filter.mpr ⟨hz,htz⟩))
  · have ht₁ : t=1 := le_antisymm (unitInterval.le_one t) (le_of_not_gt ht)
    subst t
    let L := P.filter (· < 1)
    have hL : L.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨h₀,zero_lt_one⟩⟩
    let p := L.max' hL
    have hp := Finset.mem_filter.mp (Finset.max'_mem L hL)
    refine ⟨p,1,⟨hp.1,h₁,hp.2,?_⟩,hp.2.le,le_rfl⟩
    intro z hz hpz hz₁
    exact hpz.not_ge (Finset.le_max' L z (Finset.mem_filter.mpr ⟨hz,hz₁⟩))

lemma convexComb_sliceParam {u v : I} (huv : u<v) (t : I) (ht : t∈Icc u v) :
    Icc.convexComb u v (sliceParam huv t ht)=t := by
  exact (Icc.eq_convexComb ht.1 ht.2).symm

lemma subarc_range_eq (a : Arc X) {p q : I} (hpq : p<q) :
    range (a.subarc p q hpq.ne) = a '' Icc p q := by
  apply Subset.antisymm
  · rintro _ ⟨t,rfl⟩
    exact ⟨Icc.convexComb p q t,⟨Icc.le_convexComb hpq.le t,Icc.convexComb_le hpq.le t⟩,rfl⟩
  · rintro _ ⟨t,ht,rfl⟩
    refine ⟨sliceParam hpq t ht,?_⟩
    change a (Icc.convexComb p q (sliceParam hpq t ht))=a t
    rw [convexComb_sliceParam]

lemma Consecutive.ordered {P : Finset I} {p q r s : I}
    (hpq : Consecutive P p q) (hrs : Consecutive P r s)
    (hne : (p,q) ≠ (r,s)) : q ≤ r ∨ s≤p := by
  rcases lt_trichotomy p r with hpr|hpr|hrp
  · exact Or.inl (le_of_not_gt (fun hrq => hpq.2.2.2 r hrs.1 hpr hrq))
  · subst r
    rcases lt_trichotomy q s with hqs|hqs|hsq
    · exact False.elim (hrs.2.2.2 q hpq.2.1 hpq.2.2.1 hqs)
    · exact False.elim (hne (by simp [hqs]))
    · exact False.elim (hpq.2.2.2 s hrs.2.1 hrs.2.2.1 hsq)
  · exact Or.inr (le_of_not_gt (fun hps => hrs.2.2.2 p hpq.1 hrp hps))

lemma ordered_subarcs_meeting (a : Arc X) {p q r s : I} (hpq : p<q) (hrs : r < s)
    (hqr : q ≤ r) (t w : I)
    (he : a.subarc p q hpq.ne t=a.subarc r s hrs.ne w) : t=1 ∧ w=0 := by
  have hc : Icc.convexComb p q t=Icc.convexComb r s w := a.injective he
  have htq : Icc.convexComb p q t=q := le_antisymm (Icc.convexComb_le hpq.le t)
    (hqr.trans ((Icc.le_convexComb hrs.le w).trans_eq hc.symm))
  have hwr : Icc.convexComb r s w=r := le_antisymm
    (hc.symm.trans_le ((Icc.convexComb_le hpq.le t).trans hqr)) (Icc.le_convexComb hrs.le w)
  constructor
  · apply (a.subarc p q hpq.ne).injective
    change a (Icc.convexComb p q t)=a (Icc.convexComb p q 1)
    rw [htq,Icc.convexComb_one]
  · apply (a.subarc r s hrs.ne).injective
    change a (Icc.convexComb r s w)=a (Icc.convexComb r s 0)
    rw [hwr,Icc.convexComb_zero]

lemma ordered_subarcs_compatible (a : Arc X) {p q r s : I}
    (hpq : p<q) (hrs : r < s) (hqr : q ≤ r) :
    Compatible (a.subarc p q hpq.ne) (a.subarc r s hrs.ne) := by
  constructor
  · intro t w he
    obtain ⟨ht,hw⟩ := ordered_subarcs_meeting a hpq hrs hqr t w he
    exact ⟨Or.inr ht,Or.inl hw⟩
  · intro x hx y hy
    obtain ⟨t,ht⟩ := hx.1
    obtain ⟨w,hw⟩ := hx.2
    obtain ⟨u,hu⟩ := hy.1
    obtain ⟨v,hv⟩ := hy.2
    have ht₁ := (ordered_subarcs_meeting a hpq hrs hqr t w (ht.trans hw.symm)).1
    have hu₁ := (ordered_subarcs_meeting a hpq hrs hqr u v (hu.trans hv.symm)).1
    exact ht.symm.trans ((congrArg (a.subarc p q hpq.ne) (ht₁.trans hu₁.symm)).trans hu)

def segments (P : Finset I) : Finset (I×I) := by
  classical
  exact (P.product P).filter (fun z => Consecutive P z.1 z.2)

lemma mem_segments (P : Finset I) (p q : I) :
    (p,q)∈segments P ↔ Consecutive P p q := by
  classical
  unfold segments
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2,fun h => ⟨Finset.mem_product.mpr ⟨h.1,h.2.1⟩,h⟩⟩

lemma segment_consecutive (P : Finset I) (z : segments P) :
    Consecutive P z.val.1 z.val.2 := (mem_segments P _ _).mp z.property

def subdivArc (a : Arc X) (P : Finset I) (z : segments P) : Arc X :=
  a.subarc z.val.1 z.val.2 (segment_consecutive P z).2.2.1.ne

@[simp] lemma subdivArc_zero (a : Arc X) (P : Finset I) (z : segments P) :
    subdivArc a P z 0=a z.val.1 := subarc_zero _ _ _ _
@[simp] lemma subdivArc_one (a : Arc X) (P : Finset I) (z : segments P) :
    subdivArc a P z 1=a z.val.2 := subarc_one _ _ _ _

lemma subdivArc_range_eq (a : Arc X) (P : Finset I) (z : segments P) :
    range (subdivArc a P z)=a '' Icc z.val.1 z.val.2 :=
  subarc_range_eq a (segment_consecutive P z).2.2.1

lemma subdivision_cover (a : Arc X) (P : Finset I) (h₀ : 0∈P) (h₁ : 1∈P) :
    range a=⋃ z : segments P, range (subdivArc a P z) := by
  apply Subset.antisymm
  · rintro _ ⟨t,rfl⟩
    obtain ⟨p,q,hpq,ht⟩ := consecutive_cover P h₀ h₁ t
    let z : segments P := ⟨(p,q),(mem_segments P p q).mpr hpq⟩
    apply mem_iUnion.mpr
    refine ⟨z,?_⟩
    rw [subdivArc_range_eq]
    exact ⟨t,ht,rfl⟩
  · intro x hx
    obtain ⟨z,hz⟩ := mem_iUnion.mp hx
    exact subarc_range_subset a _ _ _ hz

lemma subdivision_compatible (a : Arc X) (P : Finset I) :
    ∀ z w : segments P, z≠w → Compatible (subdivArc a P z) (subdivArc a P w) := by
  intro z w hzw
  have hz := segment_consecutive P z
  have hw := segment_consecutive P w
  have hne : z.val ≠ w.val := fun h => hzw (Subtype.ext h)
  rcases hz.ordered hw hne with h|h
  · exact ordered_subarcs_compatible a hz.2.2.1 hw.2.2.1 h
  · exact (ordered_subarcs_compatible a hw.2.2.1 hz.2.2.1 h).symm

lemma convexComb_injective {p q : I} (hpq : p<q) : Function.Injective (Icc.convexComb p q) := by
  intro s t h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  simp only [Icc.coe_convexComb] at hh
  have : ((s : ℝ)-t)*((q : ℝ)-p)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (ne_of_gt (sub_pos.mpr hpq)))

lemma Consecutive.marked_parameter {P : Finset I} {p q : I}
    (hpq : Consecutive P p q) (t : I) (ht : Icc.convexComb p q t∈P) : t=0 ∨ t=1 := by
  have hlo := Icc.le_convexComb hpq.2.2.1.le t
  have hhi := Icc.convexComb_le hpq.2.2.1.le t
  by_cases hl : Icc.convexComb p q t=p
  · exact Or.inl (convexComb_injective hpq.2.2.1 (hl.trans (Icc.convexComb_zero p q).symm))
  · have hr : Icc.convexComb p q t=q := by
      by_contra hr
      exact hpq.2.2.2 _ ht (lt_of_le_of_ne hlo (Ne.symm hl)) (lt_of_le_of_ne hhi hr)
    exact Or.inr (convexComb_injective hpq.2.2.1 (hr.trans (Icc.convexComb_one p q).symm))

lemma subarc_parameter_endpoint {p q t : I} (hpq : p<q)
    (ht : Icc.convexComb p q t=0 ∨ Icc.convexComb p q t=1) : t=0 ∨ t=1 := by
  have hlo := Icc.le_convexComb hpq.le t
  have hhi := Icc.convexComb_le hpq.le t
  rcases ht with ht|ht
  · have hp : p=0 := le_antisymm (ht ▸ hlo) (unitInterval.nonneg p)
    exact Or.inl (convexComb_injective hpq (ht.trans (hp.symm.trans (Icc.convexComb_zero p q).symm)))
  · have hq : q=1 := le_antisymm (unitInterval.le_one q) (ht ▸ hhi)
    exact Or.inr (convexComb_injective hpq (ht.trans (hq.symm.trans (Icc.convexComb_one p q).symm)))

lemma Compatible.subarcs {a b : Arc X} (hab : Compatible a b)
    {p q r s : I} (hpq : p<q) (hrs : r < s) :
    Compatible (a.subarc p q hpq.ne) (b.subarc r s hrs.ne) := by
  constructor
  · intro t w he
    obtain ⟨ht,hw⟩ := hab.1 (Icc.convexComb p q t) (Icc.convexComb r s w) he
    exact ⟨subarc_parameter_endpoint hpq ht,subarc_parameter_endpoint hrs hw⟩
  · exact hab.2.anti (inter_subset_inter (subarc_range_subset a p q hpq.ne)
      (subarc_range_subset b r s hrs.ne))

lemma Consecutive.interval_dichotomy {P : Finset I} {p q u v : I}
    (hpq : Consecutive P p q) (hu : u∈P) (hv : v∈P) :
    Icc p q ⊆ Icc u v ∨ ∀ t∈Icc p q ∩ Icc u v, t=p ∨ t=q := by
  by_cases hs : Icc p q ⊆ Icc u v
  · exact Or.inl hs
  · refine Or.inr (fun t ht => ?_)
    by_cases htp : t=p
    · exact Or.inl htp
    by_cases htq : t=q
    · exact Or.inr htq
    have hpt : p<t := lt_of_le_of_ne ht.1.1 (Ne.symm htp)
    have htq : t<q := lt_of_le_of_ne ht.1.2 htq
    have hup : u≤p := le_of_not_gt (fun hpu => hpq.2.2.2 u hu hpu (ht.2.1.trans_lt htq))
    have hqv : q≤v := le_of_not_gt (fun hvq => hpq.2.2.2 v hv (hpt.trans_le ht.2.2) hvq)
    exact False.elim (hs (Icc_subset_Icc hup hqv))

lemma free_segment_intersection {a e : Arc X} {P : Finset I} {p q : I}
    (hpq : Consecutive P p q)
    (he : (a ⁻¹' range e)=∅ ∨ ∃ u∈P, ∃ v∈P, u≤v ∧ a ⁻¹' range e=Icc u v)
    (hfree : ¬ range (a.subarc p q hpq.2.2.1.ne) ⊆ range e) :
    (∀ t : I, a.subarc p q hpq.2.2.1.ne t∈range e → t=0 ∨ t=1) ∧
    (range (a.subarc p q hpq.2.2.1.ne) ∩ range e).Subsingleton := by
  rcases he with he|⟨u,hu,v,hv,huv,he⟩
  · have hn (t : I) (ht : a.subarc p q hpq.2.2.1.ne t∈range e) : False := by
      have : Icc.convexComb p q t∈a ⁻¹' range e := ht
      rw [he] at this
      exact this
    exact ⟨fun t ht => (hn t ht).elim,fun x ⟨⟨t,ht⟩,hx⟩ y _ => (hn t (ht ▸ hx)).elim⟩
  · have hns : ¬ Icc p q ⊆ Icc u v := by
      intro hs
      apply hfree
      rw [subarc_range_eq a hpq.2.2.1]
      rintro x ⟨t,ht,rfl⟩
      change t∈a ⁻¹' range e
      rw [he]
      exact hs ht
    have hends := (hpq.interval_dichotomy hu hv).resolve_left hns
    have hend (t : I) (ht : a.subarc p q hpq.2.2.1.ne t∈range e) : t=0 ∨ t=1 := by
      have ht' : Icc.convexComb p q t∈Icc u v := he ▸ ht
      rcases hends _ ⟨⟨Icc.le_convexComb hpq.2.2.1.le t,Icc.convexComb_le hpq.2.2.1.le t⟩,ht'⟩ with hl|hr
      · exact Or.inl (convexComb_injective hpq.2.2.1 (hl.trans (Icc.convexComb_zero p q).symm))
      · exact Or.inr (convexComb_injective hpq.2.2.1 (hr.trans (Icc.convexComb_one p q).symm))
    refine ⟨hend,?_⟩
    have hnotboth : ¬ (a p∈range e ∧ a q∈range e) := by
      rintro ⟨hp,hq⟩
      apply hns
      have hp' : p∈Icc u v := he ▸ hp
      have hq' : q∈Icc u v := he ▸ hq
      exact Icc_subset_Icc hp'.1 hq'.2
    rintro x ⟨⟨t,rfl⟩,ht⟩ y ⟨⟨w,rfl⟩,hw⟩
    rcases hend t ht with rfl|rfl <;> rcases hend w hw with rfl|rfl
    · rfl
    · exact (hnotboth (by simpa using And.intro ht hw)).elim
    · exact (hnotboth (by simpa using And.intro hw ht)).elim
    · rfl

theorem old_breakpoints (a e : Arc X) (P : Finset I) :
    ∃ Q : Finset I, 0∈Q ∧ 1∈Q ∧ Q.card ≤ P.card+2 ∧
      ∀ t : I, e t∈a '' (P : Set I) → t∈Q := by
  classical
  let T : Set I := e ⁻¹' (a '' (P : Set I))
  have hTf : T.Finite := ((Finset.finite_toSet P).image a).preimage e.injective.injOn
  let Q := insert 0 (insert 1 hTf.toFinset)
  have hcard : hTf.toFinset.card ≤ P.card := by
    calc
      _ = T.ncard := (Set.ncard_eq_toFinset_card T hTf).symm
      _ ≤ (a '' (P : Set I)).ncard := Set.ncard_le_ncard_of_injOn e (fun _ ht => ht) e.injective.injOn ((Finset.finite_toSet P).image a)
      _ ≤ (P : Set I).ncard := Set.ncard_image_le
      _ = P.card := Set.ncard_coe_finset P
  refine ⟨Q,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),?_,?_⟩
  · have h₁ := Finset.card_insert_le 1 hTf.toFinset
    have h₀ := Finset.card_insert_le 0 (insert 1 hTf.toFinset)
    dsimp [Q]
    omega
  · intro t ht
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hTf.mem_toFinset.mpr ht))

lemma free_segment_compatible_old_subdivision {a e : Arc X} {P Q : Finset I}
    {p q r s : I} (hpq : Consecutive P p q) (hrs : Consecutive Q r s)
    (he : (a ⁻¹' range e)=∅ ∨ ∃ u∈P, ∃ v∈P, u≤v ∧ a ⁻¹' range e=Icc u v)
    (hfree : ¬ range (a.subarc p q hpq.2.2.1.ne) ⊆ range e)
    (hmark : ∀ t : I, e t∈a '' (P : Set I) → t∈Q) :
    Compatible (a.subarc p q hpq.2.2.1.ne) (e.subarc r s hrs.2.2.1.ne) := by
  obtain ⟨hend,hsub⟩ := free_segment_intersection hpq he hfree
  constructor
  · intro t w heq
    have ht := hend t ⟨Icc.convexComb r s w,heq.symm⟩
    refine ⟨ht,hrs.marked_parameter w (hmark _ ?_)⟩
    rcases ht with rfl|rfl
    · exact ⟨p,hpq.1,(subarc_zero a _ _ _).symm.trans heq⟩
    · exact ⟨q,hpq.2.1,(subarc_one a _ _ _).symm.trans heq⟩
  · exact hsub.anti (inter_subset_inter_right _ (subarc_range_subset e r s _))

end Arc
end CannonEmbeddedArc

noncomputable section
namespace CannonEmbeddedArc
open Set unitInterval

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma subdivArc_range_subset (a : Arc X) (P : Finset I) (z : segments P) :
    range (subdivArc a P z) ⊆ range a :=
  subarc_range_subset a _ _ (segment_consecutive P z).2.2.1.ne

lemma Compatible.of_disjoint {a b : Arc X} (h : Disjoint (range a) (range b)) :
    Compatible a b := by
  constructor
  · intro t w heq
    exact (Set.disjoint_left.mp h (mem_range_self t) ⟨w,heq.symm⟩).elim
  · intro x hx y _
    exact (Set.disjoint_left.mp h hx.1 hx.2).elim

def Vertex {ι : Type*} (E : ι → Arc X) (x : X) : Prop :=
  ∃ i, E i 0=x ∨ E i 1=x

variable {ι κ : Type*} (E : ι → Arc X) (A : κ → Arc X)
    (P : κ → Finset I) (Q : ι → Finset I)

def FreeSegment (i : κ) (z : segments (P i)) : Prop :=
  ∀ e, ¬range (subdivArc (A i) (P i) z) ⊆ range (E e)

def RefinementIndex := (Σ e : ι, segments (Q e)) ⊕
  (Σ i : κ, {z : segments (P i) // FreeSegment E A P i z})

instance instFintypeRefinementIndex [Fintype ι] [Fintype κ] : Fintype (RefinementIndex E A P Q) := by
  classical
  unfold RefinementIndex
  infer_instance

def refinementArc : RefinementIndex E A P Q → Arc X
  | Sum.inl ⟨e,z⟩ => subdivArc (E e) (Q e) z
  | Sum.inr ⟨i,z⟩ => subdivArc (A i) (P i) z.val

variable (hE : Pairwise (fun e f => Compatible (E e) (E f)))
    (hA : Pairwise (fun i j => Disjoint (range (A i)) (range (A j))))
    (hinterval : ∀ i e, (A i ⁻¹' range (E e))=∅ ∨
      ∃ u∈P i, ∃ v∈P i, u≤v ∧ A i ⁻¹' range (E e)=Icc u v)
    (hmark : ∀ i e t, E e t∈A i '' (P i : Set I) → t∈Q e)

include hE hA hinterval hmark in
lemma refinement_compatible : Pairwise (fun z w : RefinementIndex E A P Q =>
    Compatible (refinementArc E A P Q z) (refinementArc E A P Q w)) := by
  intro z w hzw
  rcases z with ⟨e,z⟩|⟨i,z⟩ <;> rcases w with ⟨f,w⟩|⟨j,w⟩
  · by_cases hef : e=f
    · subst f
      have hne : z≠w := fun h => hzw (by cases h; rfl)
      exact subdivision_compatible (E e) (Q e) z w hne
    · exact (hE hef).subarcs (segment_consecutive (Q e) z).2.2.1
        (segment_consecutive (Q f) w).2.2.1
  · exact (free_segment_compatible_old_subdivision
      (segment_consecutive (P j) w.val) (segment_consecutive (Q e) z)
      (hinterval j e) (w.property e) (hmark j e)).symm
  · exact free_segment_compatible_old_subdivision
      (segment_consecutive (P i) z.val) (segment_consecutive (Q f) w)
      (hinterval i f) (z.property f) (hmark i f)
  · by_cases hij : i=j
    · subst j
      have hne : z.val≠w.val := fun h => hzw (by have heq : z=w := Subtype.ext h; cases heq; rfl)
      exact subdivision_compatible (A i) (P i) z.val w.val hne
    · apply Compatible.of_disjoint
      exact (hA hij).mono (subdivArc_range_subset (A i) (P i) z.val) (subdivArc_range_subset (A j) (P j) w.val)

variable (hP₀ : ∀ i, 0∈P i) (hP₁ : ∀ i, 1∈P i)
    (hQ₀ : ∀ e, 0∈Q e) (hQ₁ : ∀ e, 1∈Q e)

include hQ₀ hQ₁ in
lemma refinement_old_subset (e : ι) : range (E e) ⊆ ⋃ z, range (refinementArc E A P Q z) := by
  rw [subdivision_cover (E e) (Q e) (hQ₀ e) (hQ₁ e)]
  intro x hx
  obtain ⟨z,hz⟩ := mem_iUnion.mp hx
  exact mem_iUnion_of_mem (Sum.inl ⟨e,z⟩) hz

include hP₀ hP₁ hQ₀ hQ₁ in
lemma refinement_cover : (⋃ e, range (E e)) ∪ (⋃ i, range (A i)) =
    ⋃ z, range (refinementArc E A P Q z) := by
  classical
  apply Subset.antisymm
  · intro x hx
    rcases hx with hx|hx
    · obtain ⟨e,he⟩ := mem_iUnion.mp hx
      exact refinement_old_subset E A P Q hQ₀ hQ₁ e he
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      rw [subdivision_cover (A i) (P i) (hP₀ i) (hP₁ i)] at hi
      obtain ⟨z,hz⟩ := mem_iUnion.mp hi
      by_cases hf : FreeSegment E A P i z
      · exact mem_iUnion_of_mem (Sum.inr ⟨i,⟨z,hf⟩⟩) hz
      · obtain ⟨e,he⟩ : ∃ e, range (subdivArc (A i) (P i) z) ⊆ range (E e) := by
          simpa only [FreeSegment,not_forall,not_not] using hf
        exact refinement_old_subset E A P Q hQ₀ hQ₁ e (he hz)
  · intro x hx
    obtain ⟨z,hz⟩ := mem_iUnion.mp hx
    rcases z with ⟨e,z⟩|⟨i,z⟩
    · exact Or.inl (mem_iUnion_of_mem e (subdivArc_range_subset (E e) (Q e) z hz))
    · exact Or.inr (mem_iUnion_of_mem i (subdivArc_range_subset (A i) (P i) z.val hz))

end Arc
end CannonEmbeddedArc

namespace CannonEmbeddedArc
open Set unitInterval
open scoped BigOperators

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma range_subset_of_interior {S : Set X} (hS : IsClosed S) (a : Arc X)
    (h : ∀ t : I, t≠0 → t≠1 → a t∈S) : range a ⊆ S := by
  have hc : closure (Ioo (0 : I) 1) ⊆ a ⁻¹' S :=
    (hS.preimage a.continuous).closure_subset_iff.mpr
      (fun t ht => h t (ne_of_gt ht.1) (ne_of_lt ht.2))
  rintro _ ⟨t,rfl⟩
  apply hc
  rw [closure_Ioo (show (0 : I)≠1 from zero_ne_one)]
  exact ⟨unitInterval.nonneg t,unitInterval.le_one t⟩

noncomputable def intersectionCount {ι : Type*} [Fintype ι] (E : ι → Arc X) (S : Set X) : ℕ := by
  classical
  exact ∑ i, if (range (E i) ∩ S).Nonempty then 1 else 0

end Arc
end CannonEmbeddedArc

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Straight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
namespace CannonEmbeddedArc
open Set unitInterval

namespace Arc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsStraight (a : Arc E) : Prop :=
  ∃ f : ℝ →ᵃ[ℝ] E, ∀ t : I, a t=f (t:ℝ)

def lineArc (a b : E) (hab : a≠b) : Arc E :=
  ⟨(Path.segment a b).toContinuousMap,Path.segment_injective_of_ne hab⟩
@[simp] lemma lineArc_zero (a b : E) (hab : a≠b) : lineArc a b hab 0=a := (Path.segment a b).source
@[simp] lemma lineArc_one (a b : E) (hab : a≠b) : lineArc a b hab 1=b := (Path.segment a b).target
lemma lineArc_straight (a b : E) (hab : a≠b) : IsStraight (lineArc a b hab) :=
  ⟨AffineMap.lineMap a b,Path.segment_apply a b⟩
lemma lineArc_range (a b : E) (hab : a≠b) :
    range (lineArc a b hab)=segment ℝ a b := Path.range_segment a b

lemma IsStraight.range_eq {a : Arc E} (ha : IsStraight a) :
    range a=segment ℝ (a 0) (a 1) := by
  obtain ⟨f,hf⟩ := ha
  have he : range a=f '' Set.Icc (0:ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨t,t.property,(hf t).symm⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,hf ⟨t,ht⟩⟩
  rw [he,←segment_eq_Icc (show (0:ℝ)≤1 by norm_num),image_segment]
  rw [hf 0,hf 1]
  rfl

lemma IsStraight.subarc {a : Arc E} (ha : IsStraight a) (u v : I) (huv : u≠v) :
    IsStraight (a.subarc u v huv) := by
  obtain ⟨f,hf⟩ := ha
  refine ⟨f.comp (AffineMap.lineMap (u:ℝ) (v:ℝ)),fun t => ?_⟩
  change a (Icc.convexComb u v t)=f (AffineMap.lineMap (u:ℝ) (v:ℝ) (t:ℝ))
  rw [hf]
  congr 1
  simp only [Icc.coe_convexComb,AffineMap.lineMap_apply_module,smul_eq_mul]

lemma IsStraight.preimage_convex {a : Arc E} (ha : IsStraight a)
    {S : Set E} (hS : Convex ℝ S) : OrdConnected (a ⁻¹' S) := by
  obtain ⟨f,hf⟩ := ha
  refine ⟨fun u hu v hv t ht => ?_⟩
  have htseg : (t:ℝ)∈segment ℝ (u:ℝ) (v:ℝ) := by
    rw [segment_eq_Icc (show (u:ℝ)≤v from ht.1.trans ht.2)]
    exact ht
  have hft : f (t:ℝ)∈segment ℝ (f u) (f v) := by
    rw [←image_segment]
    exact ⟨t,htseg,rfl⟩
  rw [←hf u,←hf v] at hft
  change a t∈S
  rw [hf]
  exact hS.segment_subset hu hv hft

theorem insert_straight_arrangement {ι : Type*} [Fintype ι]
    (F : ι → Arc E) (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (hFs : ∀ i, IsStraight (F i)) (a : Arc E) (ha : IsStraight a) :
    ∃ n : ℕ, ∃ B : Fin n → Arc E,
      Pairwise (fun i j => Compatible (B i) (B j)) ∧
      (∀ i, IsStraight (B i)) ∧ (⋃ i, range (B i))=(⋃ i, range (F i))∪range a := by
  classical
  have hc (i : ι) : OrdConnected (a ⁻¹' range (F i)) := by
    apply ha.preimage_convex
    rw [(hFs i).range_eq]
    exact convex_segment ..
  obtain ⟨P,hP₀,hP₁,_,hP⟩ := finite_breakpoints F Finset.univ a (fun i _ => hc i)
  choose Q hQ₀ hQ₁ hQc hQ using fun i => old_breakpoints a (F i) P
  let A : Unit → Arc E := fun _ => a
  let PP : Unit → Finset I := fun _ => P
  have hA : Pairwise (fun i j => Disjoint (range (A i)) (range (A j))) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hinterval : ∀ i e, (A i ⁻¹' range (F e))=∅ ∨
      ∃ u∈PP i, ∃ v∈PP i, u≤v ∧ A i ⁻¹' range (F e)=Icc u v :=
    fun _ e => hP e (Finset.mem_univ e)
  have hmark : ∀ i e t, F e t∈A i '' (PP i:Set I) → t∈Q e := fun _ e => hQ e
  let R := refinementArc F A PP Q
  have hRc : Pairwise (fun z w => Compatible (R z) (R w)) :=
    refinement_compatible F A PP Q hF hA hinterval hmark
  have hRs (z : RefinementIndex F A PP Q) : IsStraight (R z) := by
    rcases z with ⟨i,z⟩|⟨i,z⟩
    · exact (hFs i).subarc _ _ (segment_consecutive (Q i) z).2.2.1.ne
    · exact ha.subarc _ _ (segment_consecutive (PP i) z.val).2.2.1.ne
  have hcover : (⋃ z, range (R z))=(⋃ i, range (F i))∪range a := by
    have hh := (refinement_cover F A PP Q (fun _ => hP₀) (fun _ => hP₁) hQ₀ hQ₁).symm
    simpa only [A,iUnion_const] using hh
  let e := Fintype.equivFin (RefinementIndex F A PP Q)
  refine ⟨_,R ∘ e.symm,?_,fun i => hRs (e.symm i),?_⟩
  · intro i j hij
    exact hRc (fun h => hij (e.symm.injective h))
  · rw [←hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨e.symm i,hi⟩
    · intro hx
      obtain ⟨z,hz⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨e z,by simpa using hz⟩

theorem straight_arrangement (P : Finset (E×E)) (hne : ∀ p∈P, p.1≠p.2) :
    ∃ n : ℕ, ∃ F : Fin n → Arc E,
      Pairwise (fun i j => Compatible (F i) (F j)) ∧
      (∀ i, IsStraight (F i)) ∧ (⋃ i, range (F i))=⋃ p∈P, segment ℝ p.1 p.2 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨0,Fin.elim0,?_,?_,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · simp
  | @insert p P hp ih =>
    obtain ⟨n,F,hFc,hFs,hFr⟩ := ih (fun q hq => hne q (Finset.mem_insert_of_mem hq))
    have hn := hne p (Finset.mem_insert_self p P)
    obtain ⟨m,B,hBc,hBs,hBr⟩ := insert_straight_arrangement F hFc hFs
      (lineArc p.1 p.2 hn) (lineArc_straight p.1 p.2 hn)
    refine ⟨m,B,hBc,hBs,?_⟩
    rw [hBr,hFr,lineArc_range]
    simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left]
    exact union_comm ..
end Arc
end CannonEmbeddedArc

noncomputable section
open Set unitInterval

namespace CannonTame
variable {X : Type*} [TopologicalSpace X]

lemma connected_in_finite_closed_cover {ι : Type*} [Finite ι]
    (F : ι → Set X) (hF : ∀ i, IsClosed (F i))
    {C : Set X} (hC : IsConnected C) (hcov : C⊆⋃ i, F i)
    (hdisj : ∀ i j, i≠j → C∩(F i∩F j)=∅) :
    ∃ i, C⊆F i := by
  classical
  obtain ⟨x,hx⟩ := hC.nonempty
  obtain ⟨i,hxi⟩ := mem_iUnion.mp (hcov hx)
  refine ⟨i,?_⟩
  let W := ⋃ j : {j : ι // j≠i}, F j.val
  have hW : IsClosed W := isClosed_iUnion_of_finite (fun j => hF j.val)
  have hxW : x∉W := by
    intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    have hh : x∈C∩(F j.val∩F i) := ⟨hx,hj,hxi⟩
    rw [hdisj j.val i j.property] at hh
    exact hh
  intro y hy
  by_contra hyi
  have hcover : C⊆Wᶜ∪(F i)ᶜ := by
    intro z hz
    by_cases hzi : z∈F i
    · left
      intro hzW
      obtain ⟨j,hj⟩ := mem_iUnion.mp hzW
      have hh : z∈C∩(F j.val∩F i) := ⟨hz,hj,hzi⟩
      rw [hdisj j.val i j.property] at hh
      exact hh
    · exact Or.inr hzi
  obtain ⟨z,hz,hzW,hzi⟩ := hC.isPreconnected _ _ hW.isOpen_compl (hF i).isOpen_compl
    hcover ⟨x,hx,hxW⟩ ⟨y,hy,hyi⟩
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hcov hz)
  by_cases hji : j=i
  · exact hzi (hji ▸ hj)
  · exact hzW (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
end CannonTame

namespace CannonEmbeddedArc.Arc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma IsStraight.image_Icc {a : Arc E} (ha : IsStraight a) {u v : I} (huv : u≤v) :
    a '' Icc u v=segment ℝ (a u) (a v) := by
  obtain ⟨f,hf⟩ := ha
  have he : a '' Icc u v=f '' Icc (u:ℝ) (v:ℝ) := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,(hf t).symm⟩
    · rintro ⟨t,ht,rfl⟩
      let w : I := ⟨t,⟨u.property.1.trans ht.1,ht.2.trans v.property.2⟩⟩
      exact ⟨w,ht,hf w⟩
  rw [he,←segment_eq_Icc (show (u:ℝ)≤v from huv),image_segment,hf u,hf v]

lemma range_eq_segment_of_subset {a b : Arc E} (ha : IsStraight a)
    (hsub : range b⊆range a) : range b=segment ℝ (b 0) (b 1) := by
  let e := (a.continuous.isClosedEmbedding a.injective).isEmbedding.toHomeomorph
  let f : I → range a := fun t => ⟨b t,hsub (mem_range_self t)⟩
  let g : I → I := e.symm ∘ f
  have hfc : Continuous f := b.continuous.subtype_mk _
  have hgc : Continuous g := e.symm.continuous.comp hfc
  have hgf (t : I) : a (g t)=b t := by
    have hh := congrArg Subtype.val (e.apply_symm_apply (f t))
    exact hh
  have hgi : Function.Injective g := by
    intro s t hst
    apply b.injective
    rw [←hgf s,←hgf t,hst]
  have hgr : range b=a '' range g := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨g t,mem_range_self t,hgf t⟩
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      exact ⟨t,(hgf t).symm⟩
  have hc : OrdConnected (range g) := (isPreconnected_range hgc).ordConnected
  rcases hgc.strictMono_of_inj_boundedOrder' hgi with hm|hm
  · have he : range g=Icc (g 0) (g 1) := by
      apply Subset.antisymm
      · rintro _ ⟨t,rfl⟩
        exact ⟨hm.monotone (unitInterval.nonneg t),hm.monotone (unitInterval.le_one t)⟩
      · exact hc.out (mem_range_self 0) (mem_range_self 1)
    rw [hgr,he,ha.image_Icc (hm.monotone zero_le_one),hgf 0,hgf 1]
  · have he : range g=Icc (g 1) (g 0) := by
      apply Subset.antisymm
      · rintro _ ⟨t,rfl⟩
        exact ⟨hm.antitone (unitInterval.le_one t),hm.antitone (unitInterval.nonneg t)⟩
      · exact hc.out (mem_range_self 1) (mem_range_self 0)
    rw [hgr,he,ha.image_Icc (hm.antitone zero_le_one),hgf 0,hgf 1,segment_symm]

variable {X : Type*} [TopologicalSpace X] [T2Space X]

lemma subarc_in_one_edge {ι : Type*} [Finite ι] (F : ι → Arc X)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (a : Arc X) (P : Finset I) {p q : I} (hpq : Consecutive P p q)
    (hcov : ∀ t : I, t≠0 → t≠1 →
      a.subarc p q hpq.2.2.1.ne t∈⋃ i, range (F i))
    (hmark : ∀ t, Vertex F (a t) → t∈P) :
    ∃ i, range (a.subarc p q hpq.2.2.1.ne)⊆range (F i) := by
  let b := a.subarc p q hpq.2.2.1.ne
  let C := b '' Ioo (0:I) 1
  have hC : IsConnected C :=
    (isConnected_Ioo (show (0:I)<1 from zero_lt_one)).image b b.continuous.continuousOn
  have hcover : C⊆⋃ i, range (F i) := by
    rintro _ ⟨t,ht,rfl⟩
    exact hcov t (ne_of_gt ht.1) (ne_of_lt ht.2)
  have hdisj (i j : ι) (hij : i≠j) : C∩(range (F i)∩range (F j))=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨t,ht,he⟩,⟨u,hu⟩,⟨v,hv⟩⟩
    obtain ⟨hui,_⟩ := (hF hij).1 u v (hu.trans hv.symm)
    have hvtx : Vertex F (b t) := by
      refine ⟨i,?_⟩
      rcases hui with rfl|rfl
      · exact Or.inl (hu.trans he.symm)
      · exact Or.inr (hu.trans he.symm)
    have hm := hmark (Icc.convexComb p q t) hvtx
    rcases hpq.marked_parameter t hm with h|h
    · exact (ne_of_gt ht.1) h
    · exact (ne_of_lt ht.2) h
  obtain ⟨i,hi⟩ := CannonTame.connected_in_finite_closed_cover
    (fun i => range (F i)) (fun i => (F i).compact_range.isClosed) hC hcover hdisj
  refine ⟨i,range_subset_of_interior (F i).compact_range.isClosed b ?_⟩
  intro t ht₀ ht₁
  apply hi
  refine ⟨t,⟨?_,?_⟩,rfl⟩
  · exact lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht₀)
  · exact lt_of_le_of_ne (unitInterval.le_one t) ht₁
end CannonEmbeddedArc.Arc

noncomputable section
namespace CannonEmbeddedArc.Arc
open Set unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem arc_in_arrangement_subdivision {ι : Type*} [Finite ι]
    (F : ι → Arc E) (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (hFs : ∀ i, IsStraight (F i)) (T : Finset E)
    (a : Arc E) (hsub : range a⊆(⋃ i, range (F i))∪(T:Set E)) :
    ∃ P : Finset I, 0∈P ∧ 1∈P ∧
      ∀ z : segments P, range (subdivArc a P z)=
        segment ℝ (a z.val.1) (a z.val.2) := by
  classical
  let V : Set E := (range (fun i => F i 0)∪range (fun i => F i 1))∪(T:Set E)
  have hV : V.Finite := ((finite_range _).union (finite_range _)).union T.finite_toSet
  have hpre : (a ⁻¹' V).Finite := hV.preimage a.injective.injOn
  let P := insert 0 (insert 1 hpre.toFinset)
  have hmarkV (t : I) (ht : a t∈V) : t∈P :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hpre.mem_toFinset.mpr ht))
  refine ⟨P,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),?_⟩
  intro z
  have hz := segment_consecutive P z
  have havoid (t : I) (ht₀ : t≠0) (ht₁ : t≠1) :
      subdivArc a P z t∉V := by
    intro hv
    have hmem := hmarkV (Icc.convexComb z.val.1 z.val.2 t) hv
    rcases hz.marked_parameter t hmem with h|h
    · exact ht₀ h
    · exact ht₁ h
  have hcover (t : I) (ht₀ : t≠0) (ht₁ : t≠1) :
      subdivArc a P z t∈⋃ i, range (F i) := by
    rcases hsub (subdivArc_range_subset a P z (mem_range_self t)) with h|h
    · exact h
    · exact (havoid t ht₀ ht₁ (Or.inr h)).elim
  have hmark (t : I) (ht : Vertex F (a t)) : t∈P := by
    apply hmarkV
    obtain ⟨i,hi|hi⟩ := ht
    · exact Or.inl (Or.inl ⟨i,hi⟩)
    · exact Or.inl (Or.inr ⟨i,hi⟩)
  obtain ⟨i,hi⟩ := subarc_in_one_edge F hF a P hz hcover hmark
  have hh := range_eq_segment_of_subset (hFs i) hi
  change range (subdivArc a P z)=segment ℝ
    (subdivArc a P z 0) (subdivArc a P z 1) at hh
  simpa only [subdivArc_zero,subdivArc_one] using hh

theorem finite_segment_arc_subdivision (Q : Finset (E×E)) (a : Arc E)
    (hsub : range a⊆⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ P : Finset I, 0∈P ∧ 1∈P ∧
      ∀ z : segments P, range (subdivArc a P z)=
        segment ℝ (a z.val.1) (a z.val.2) := by
  classical
  let R := Q.filter (fun q => q.1≠q.2)
  obtain ⟨n,F,hFc,hFs,hFr⟩ := straight_arrangement R
    (fun p hp => (Finset.mem_filter.mp hp).2)
  let T := Q.image Prod.fst
  apply arc_in_arrangement_subdivision F hFc hFs T a
  intro x hx
  obtain ⟨q,hq,hxq⟩ := mem_iUnion₂.mp (hsub hx)
  by_cases hn : q.1=q.2
  · right
    have hxq' : x=q.1 := by simpa only [←hn,segment_same,mem_singleton_iff] using hxq
    exact hxq' ▸ Finset.mem_image_of_mem Prod.fst hq
  · left
    rw [hFr]
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hn⟩,hxq⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval

lemma consecutive_neighbors (P : Finset I) (h₀ : 0∈P) (h₁ : 1∈P)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) (ht : t∈P) :
    ∃ p q, Consecutive P p t ∧ Consecutive P t q := by
  classical
  let L := P.filter (· < t)
  let R := P.filter (t < ·)
  have hL : L.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨h₀,ht₀⟩⟩
  have hR : R.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨h₁,ht₁⟩⟩
  let p := L.max' hL
  let q := R.min' hR
  have hp := Finset.mem_filter.mp (Finset.max'_mem L hL)
  have hq := Finset.mem_filter.mp (Finset.min'_mem R hR)
  refine ⟨p,q,⟨hp.1,ht,hp.2,?_⟩,⟨ht,hq.1,hq.2,?_⟩⟩
  · intro z hz hpz hzt
    exact hpz.not_ge (Finset.le_max' L z (Finset.mem_filter.mpr ⟨hz,hzt⟩))
  · intro z hz htz hzq
    exact hzq.not_ge (Finset.min'_le R z (Finset.mem_filter.mpr ⟨hz,htz⟩))

lemma consecutive_refinement {P Q : Finset I} (h₀ : 0∈P) (h₁ : 1∈P)
    (hPQ : P⊆Q) {p q : I} (hpq : Consecutive Q p q) :
    ∃ u v, Consecutive P u v ∧ Icc p q⊆Icc u v := by
  obtain ⟨m,hpm,hmq⟩ := exists_between hpq.2.2.1
  obtain ⟨u,v,huv,hum,hmv⟩ := consecutive_cover P h₀ h₁ m
  have hup : u≤p := by
    by_contra h
    exact hpq.2.2.2 u (hPQ huv.1) (lt_of_not_ge h) (hum.trans_lt hmq)
  have hqv : q≤v := by
    by_contra h
    exact hpq.2.2.2 v (hPQ huv.2.1) (hpm.trans_le hmv) (lt_of_not_ge h)
  exact ⟨u,v,huv,fun _ h => ⟨hup.trans h.1,h.2.trans hqv⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma segment_subarc_image (a : Arc E) {p q u v : I} (hpq : p<q) (huv : u<v)
    (he : a '' Icc p q=segment ℝ (a p) (a q)) (hsub : Icc u v⊆Icc p q) :
    a '' Icc u v=segment ℝ (a u) (a v) := by
  let b := a.subarc u v huv.ne
  have hsub' : range b⊆range (lineArc (a p) (a q) (a.injective.ne hpq.ne)) := by
    rw [lineArc_range,←he]
    exact (subarc_range_eq a huv).subset.trans (image_mono hsub)
  have hh := range_eq_segment_of_subset
    (lineArc_straight (a p) (a q) (a.injective.ne hpq.ne)) hsub'
  change range (a.subarc u v huv.ne)=segment ℝ
    (a.subarc u v huv.ne 0) (a.subarc u v huv.ne 1) at hh
  rw [←subarc_range_eq a huv]
  simpa only [subarc_zero,subarc_one] using hh

lemma straight_subdivision_refines (a : Arc E) {P Q : Finset I} (h₀ : 0∈P) (h₁ : 1∈P)
    (hPQ : P⊆Q) (hP : ∀ z : segments P,
      range (subdivArc a P z)=segment ℝ (a z.val.1) (a z.val.2)) :
    ∀ z : segments Q, range (subdivArc a Q z)=segment ℝ (a z.val.1) (a z.val.2) := by
  intro z
  have hz := segment_consecutive Q z
  obtain ⟨u,v,huv,hsub⟩ := consecutive_refinement h₀ h₁ hPQ hz
  let w : segments P := ⟨(u,v),(mem_segments P u v).mpr huv⟩
  have hw := hP w
  rw [subdivArc_range_eq] at hw ⊢
  exact segment_subarc_image a huv.2.2.1 hz.2.2.1 hw hsub

lemma corner_not_sameRay (a : Arc E) {p t q : I} (hpt : p<t) (htq : t<q)
    (hleft : a '' Icc p t=segment ℝ (a p) (a t))
    (hright : a '' Icc t q=segment ℝ (a t) (a q)) :
    ¬SameRay ℝ (a p-a t) (a q-a t) := by
  intro h
  have hu : a p-a t≠0 := sub_ne_zero.mpr (a.injective.ne hpt.ne)
  have hv : a q-a t≠0 := sub_ne_zero.mpr (a.injective.ne htq.ne.symm)
  obtain ⟨r,hr,he⟩ := h.exists_pos_left hu hv
  by_cases hr₁ : r≤1
  · have hmem : a q∈segment ℝ (a t) (a p) := by
      rw [segment_eq_image']
      exact ⟨r,⟨hr.le,hr₁⟩,by dsimp only; rw [he]; abel⟩
    rw [segment_symm,←hleft] at hmem
    obtain ⟨s,hs,hse⟩ := hmem
    have hsq := a.injective hse
    subst s
    exact htq.not_ge hs.2
  · have hr₁' : 1 ≤ r := (lt_of_not_ge hr₁).le
    have hei : r⁻¹ • (a q-a t)=a p-a t := by
      rw [←he,inv_smul_smul₀ hr.ne']
    have hmem : a p∈segment ℝ (a t) (a q) := by
      rw [segment_eq_image']
      exact ⟨r⁻¹,⟨inv_nonneg.mpr hr.le,inv_le_one_of_one_le₀ hr₁'⟩,by dsimp only; rw [hei]; abel⟩
    rw [←hright] at hmem
    obtain ⟨s,hs,hse⟩ := hmem
    have hsp := a.injective hse
    subst s
    exact hpt.not_ge hs.1

theorem tame_interior_corner (Q : Finset (E×E)) (a : Arc E)
    (hsub : range a⊆⋃ q∈Q, segment ℝ q.1 q.2)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ p q : I, p<t ∧ t<q ∧
      a '' Icc p t=segment ℝ (a p) (a t) ∧
      a '' Icc t q=segment ℝ (a t) (a q) ∧
      ¬SameRay ℝ (a p-a t) (a q-a t) := by
  classical
  obtain ⟨P,hP₀,hP₁,hP⟩ := finite_segment_arc_subdivision Q a hsub
  let R := insert t P
  have hPR : P⊆R := Finset.subset_insert _ _
  obtain ⟨p,q,hpt,htq⟩ := consecutive_neighbors R (hPR hP₀) (hPR hP₁) ht₀ ht₁
    (Finset.mem_insert_self _ _)
  have hR := straight_subdivision_refines a hP₀ hP₁ hPR hP
  have hleft := hR ⟨(p,t),(mem_segments R p t).mpr hpt⟩
  have hright := hR ⟨(t,q),(mem_segments R t q).mpr htq⟩
  rw [subdivArc_range_eq] at hleft hright
  exact ⟨p,q,hpt.2.2.1,htq.2.2.1,hleft,hright,
    corner_not_sameRay a hpt.2.2.1 htq.2.2.1 hleft hright⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem isolate_edge_interior {ι : Type*} [Finite ι] (F : ι → Arc X)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (i : ι) {p t q : I} (hpt : p<t) (htq : t<q) :
    ∃ W : Set X, IsOpen W ∧ F i t∈W ∧
      ∀ z∈W, (z∈⋃ j, range (F j) ↔ z∈F i '' Icc p q) := by
  classical
  let A : Set X := ⋃ j : {j // j≠i}, range (F j.val)
  let B : Set X := F i '' (Iic p∪Ici q)
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun j => (F j.val).compact_range.isClosed)
  have hB : IsClosed B :=
    ((isClosed_Iic.union isClosed_Ici).isCompact.image (F i).continuous).isClosed
  let W := (A∪B)ᶜ
  have ht₀ : t≠0 := ne_of_gt ((unitInterval.nonneg p).trans_lt hpt)
  have ht₁ : t≠1 := ne_of_lt (htq.trans_le (unitInterval.le_one q))
  have htA : F i t∉A := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.mp hh
    obtain ⟨s,hs⟩ := hj
    have hh := (hF j.property.symm).1 t s hs.symm
    exact hh.1.elim ht₀ ht₁
  have htB : F i t∉B := by
    rintro ⟨s,hs,hst⟩
    have he := (F i).injective hst
    subst s
    exact hs.elim hpt.not_ge htq.not_ge
  refine ⟨W,(hA.union hB).isOpen_compl,fun h => h.elim htA htB,?_⟩
  intro z hz
  constructor
  · intro hzF
    obtain ⟨j,s,hs⟩ := mem_iUnion.mp hzF
    by_cases hji : j=i
    · subst j
      refine ⟨s,?_,hs⟩
      have hsB : s∉Iic p∪Ici q := fun hsB => hz (Or.inr ⟨s,hsB,hs⟩)
      constructor
      · exact (lt_of_not_ge (fun h => hsB (Or.inl h))).le
      · exact (lt_of_not_ge (fun h => hsB (Or.inr h))).le
    · exact (hz (Or.inl (mem_iUnion.mpr ⟨⟨j,hji⟩,⟨s,hs⟩⟩))).elim
  · rintro ⟨s,_,rfl⟩
    exact mem_iUnion.mpr ⟨i,mem_range_self s⟩
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TameGraphFlatChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPlanarCorner

theorem tame_graph_flat_chart {ι : Type*} [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (i : ι) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ F i t∈W ∧
      H (0,0)=F i t ∧ ∀ z∈W,
        (z∈⋃ j, range (F j) ↔ z∈H '' horizontal) := by
  obtain ⟨p,q,hpt,htq,hleft,hright,hcorner⟩ := tame_interior_corner Q (F i) (hQ i) ht₀ ht₁
  obtain ⟨W,hW,htW,hiso⟩ := isolate_edge_interior F hF i hpt htq
  let x := F i t
  let u := F i p-x
  let v := F i q-x
  have hu : u≠0 := sub_ne_zero.mpr ((F i).injective.ne hpt.ne)
  have hv : v≠0 := sub_ne_zero.mpr ((F i).injective.ne htq.ne.symm)
  let r := min ‖u‖ ‖v‖
  have hr : 0 < r := lt_min (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  obtain ⟨H₀,hH₀,hHr⟩ := straighten_corner hcorner
  let H := H₀.trans (Homeomorph.addLeft x)
  refine ⟨H,W∩ball x r,hW.inter isOpen_ball,⟨htW,mem_ball_self hr⟩,?_,?_⟩
  · simp [H,hH₀,x]
  · intro z hz
    rw [hiso z hz.1]
    have he : Icc p q=Icc p t∪Icc t q := by
      ext s
      constructor
      · intro hs
        rcases le_total s t with hst|hts
        · exact Or.inl ⟨hs.1,hst⟩
        · exact Or.inr ⟨hts,hs.2⟩
      · rintro (hs|hs)
        · exact ⟨hs.1,hs.2.trans htq.le⟩
        · exact ⟨hpt.le.trans hs.1,hs.2⟩
    rw [he,image_union,hleft,hright]
    have hHimage : H '' horizontal=(fun w : ℂ => x+w) '' (ray u∪ray v) := by
      change ((fun w : ℂ => x+w) ∘ H₀) '' horizontal=_
      rw [image_comp,hHr]
    rw [hHimage,image_union,mem_union,mem_union]
    have hxU : x+u=F i p := by dsimp [u,x]; abel
    have hxV : x+v=F i q := by dsimp [v,x]; abel
    have hmem (w : ℂ) : z∈(fun b : ℂ => x+b) '' ray w ↔
        ∃ s : ℝ, 0 ≤ s ∧ z = x+s•w := by
      constructor
      · rintro ⟨b,⟨s,hs,hb⟩,hbe⟩
        exact ⟨s,hs,by rw [hb] at hbe; exact hbe.symm⟩
      · rintro ⟨s,hs,rfl⟩
        exact ⟨s•w,⟨s,hs,rfl⟩,rfl⟩
    rw [hmem u,hmem v,local_ray_segment (min_le_left _ _) hz.2,
      local_ray_segment (min_le_right _ _) hz.2,hxU,hxV]
    rw [segment_symm (𝕜:=ℝ) (x:=F i p) (y:=x)]
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner

def reverse (a : Arc ℂ) : Arc ℂ where
  map := a.path.symm.toContinuousMap
  injective := fun _ _ h => unitInterval.symm_bijective.injective (a.injective h)
@[simp] lemma reverse_apply (a : Arc ℂ) (t : I) : a.reverse t=a (unitInterval.symm t) := rfl
@[simp] lemma reverse_zero (a : Arc ℂ) : a.reverse 0=a 1 := by simp
@[simp] lemma reverse_one (a : Arc ℂ) : a.reverse 1=a 0 := by simp
@[simp] lemma reverse_range (a : Arc ℂ) : range a.reverse=range a :=
  Path.symm_range a.path

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Portion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

def portion (a : Arc ℂ) (u v : I) : Path (a u) (a v) where
  toFun t := a (Icc.convexComb u v t)
  continuous_toFun := a.continuous.comp (Icc.continuous_convexComb u v)
  source' := by simp
  target' := by simp
@[simp] lemma portion_apply (a : Arc ℂ) (u v t : I) :
    a.portion u v t=a (Icc.convexComb u v t) := rfl
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TameEdgeIncidenceLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPlanarCorner CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma tame_edge_incidence_local (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ U : Set ℂ, IsOpen U ∧ F i t∈U ∧
      ∃ labels : Bool → D, ∀ x∈U∩(⋃ j, range (F j)),
        incident _ π x=range labels := by
  obtain ⟨H,W,hW,htW,h₀,hflat⟩ := tame_graph_flat_chart F hF Q hQ i ht₀ ht₁
  have he (z : ℂ) : z∈H '' horizontal ↔ (H.symm z).2=0 := by
    rw [H.image_eq_preimage_symm]
    rfl
  obtain ⟨U,hU,h₀U,_,labels,hlabels⟩ := flat_chart_incidence hπ H hW (h₀.symm ▸ htW)
    (fun z hz => by exact not_congr ((hflat z hz).trans (he z)))
  exact ⟨U,hU,h₀ ▸ h₀U,labels,by simpa only [compl_compl] using hlabels⟩

theorem tame_edge_incident_labels (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π) (i : ι) :
    ∃ labels : Bool → D, ∀ t : I, 0<t → t<1 →
      incident _ π (F i t)=range labels := by
  let A := F i '' Ioo (0:I) 1
  have hA : IsPreconnected A :=
    (isPreconnected_Ioo).image (F i) (F i).continuous.continuousOn
  have hloc : ∀ x∈A, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∀ y∈A∩U, incident _ π y=incident _ π x := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨U,hU,htU,labels,hlabels⟩ := tame_edge_incidence_local F hF Q hQ hπ i ht.1 ht.2
    refine ⟨U,hU,htU,?_⟩
    rintro y ⟨⟨s,hs,hsy⟩,hyU⟩
    have hsyG : y∈⋃ j, range (F j) := mem_iUnion.mpr ⟨i,⟨s,hsy⟩⟩
    exact (hlabels y ⟨hyU,hsyG⟩).trans
      (hlabels (F i t) ⟨htU,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩).symm
  let t₀ : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht₀ : 0<t₀ ∧ t₀<1 := by
    change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1
    norm_num
  obtain ⟨U,hU,htU,labels,hlabels⟩ := tame_edge_incidence_local F hF Q hQ hπ i ht₀.1 ht₀.2
  refine ⟨labels,fun t ht₁ ht₂ => ?_⟩
  exact (incident_constant_on_preconnected hA hloc (F i t) ⟨t,⟨ht₁,ht₂⟩,rfl⟩
    (F i t₀) ⟨t₀,ht₀,rfl⟩).trans
    (hlabels (F i t₀) ⟨htU,mem_iUnion.mpr ⟨i,mem_range_self t₀⟩⟩)
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FiniteVertexSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma finite_vertex_set (F : ι → Arc ℂ) : {x | Vertex F x}.Finite := by
  have he : {x | Vertex F x}=range (fun i => F i 0)∪range (fun i => F i 1) := by
    ext x
    simp only [mem_ofPred_eq,Vertex,mem_union,mem_range]
    aesop
  rw [he]
  exact (finite_range _).union (finite_range _)

omit [Finite ι] in
lemma interior_not_vertex (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (i : ι)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) : ¬Vertex F (F i t) := by
  rintro ⟨j,hj⟩
  by_cases hij : i=j
  · subst j
    rcases hj with h|h
    · exact ht₀.ne' ((F i).injective h).symm
    · exact ht₁.ne ((F i).injective h).symm
  · rcases hj with h|h
    · rcases ((hF hij).1 t 0 h.symm).1 with h|h
      · exact ht₀.ne' h
      · exact ht₁.ne h
    · rcases ((hF hij).1 t 1 h.symm).1 with h|h
      · exact ht₀.ne' h
      · exact ht₁.ne h

theorem tame_face_hits_edge [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (d : D) (hd : (region _ π d).Nonempty) :
    ∃ (i : ι) (t : I), 0<t ∧ t<1 ∧ d∈incident _ π (F i t) := by
  let K : Set ℂ := ⋃ j, range (F j)
  let T : Set ℂ := {x | Vertex F x}
  have hTK : T⊆K := by
    rintro x ⟨i,hi⟩
    apply mem_iUnion.mpr
    rcases hi with h|h
    · exact ⟨i,⟨0,h⟩⟩
    · exact ⟨i,⟨1,h⟩⟩
  have hconn : IsPreconnected Tᶜ := by
    apply (Set.Countable.isPathConnected_compl_of_one_lt_rank (E:=ℂ) ?_
      (finite_vertex_set F).countable).isConnected.isPreconnected
    rw [Complex.rank_real_complex]
    norm_num
  have hne : (K\T).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    let t : I := ⟨1/2,by constructor <;> norm_num⟩
    refine ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩,interior_not_vertex F hF i ?_ ?_⟩
    · change (0:ℝ)<1/2
      norm_num
    · change (1/2:ℝ)<1
      norm_num
  obtain ⟨x,hxK,hxT,hxd⟩ := region_boundary_hits
    (show IsClosed K from isClosed_iUnion_of_finite (fun i => (F i).compact_range.isClosed))
    (finite_vertex_set F).isClosed hTK hconn hne hπ d hd
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hxK
  have ht₀ : t≠0 := by
    intro h
    apply hxT
    exact ⟨i,Or.inl (congrArg (F i) h.symm)⟩
  have ht₁ : t≠1 := by
    intro h
    apply hxT
    exact ⟨i,Or.inr (congrArg (F i) h.symm)⟩
  exact ⟨i,t,lt_of_le_of_ne (show (0:I)≤t from t.property.1) ht₀.symm,
    lt_of_le_of_ne (show t≤(1:I) from t.property.2) ht₁,hxd⟩

theorem tame_face_labels_surjection [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (hsur : Function.Surjective π) :
    ∃ f : ι × Bool → D, Function.Surjective f := by
  choose labels hlabels using tame_edge_incident_labels F hF Q hQ hπ
  refine ⟨fun p => labels p.1 p.2,?_⟩
  intro d
  obtain ⟨z,hz⟩ := hsur d
  obtain ⟨i,t,ht₀,ht₁,hd⟩ := tame_face_hits_edge F hF hπ d ⟨z.val,z.property,hz⟩
  rw [hlabels i t ht₀ ht₁] at hd
  obtain ⟨b,hb⟩ := hd
  exact ⟨(i,b),hb⟩

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RegionEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

def regionEdges (F : ι → Arc ℂ) (π : ((⋃ j,range (F j))ᶜ : Set ℂ) → D) (d : D) : Set ι :=
  {i | ∃ t : I, 0<t ∧ t<1 ∧ d∈incident _ π (F i t)}

end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def pullChart (e : X → Y) (he : IsEmbedding e) (a : Arc Y)
    (ha : range a⊆range e) : Arc X where
  map := ⟨fun t => he.toHomeomorph.symm ⟨a t,ha (mem_range_self t)⟩,
    he.toHomeomorph.symm.continuous.comp (a.continuous.subtype_mk _)⟩
  injective := by
    intro s t h
    apply a.injective
    exact congrArg Subtype.val (he.toHomeomorph.symm.injective h)

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_VertexLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonFaceIncidence

variable {ι : Type*} [Finite ι]

def Faces (F : ι → Arc ℂ) := ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)
def face (F : ι → Arc ℂ) (d : Faces F) : Set ℂ :=
  region _ ConnectedComponents.mk d
noncomputable def faceVertices (F : ι → Arc ℂ) (d : Faces F) : Finset ℂ :=
  ((finite_vertex_set F).inter_of_left (s:={x | Vertex F x}) (t:=closure (face F d))).toFinset

lemma faces_finite [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) :
    Finite (Faces F) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  obtain ⟨f,hf⟩ := tame_face_labels_surjection F hF P hP
    ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  exact Finite.of_surjective f hf

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonPlanarEuler
open Set Topology unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {ι : Type*} [DecidableEq ι]
def vertices (F : ι → Arc ℂ) (S : Finset ι) : Finset ℂ := by
  classical
  exact S.biUnion fun i => {F i 0,F i 1}
end CannonPlanarEuler

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_UnitCircle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonCircleBoundary
open Set Topology Metric
open scoped OnePoint

abbrev UnitCircle := sphere (0 : ℂ) 1

def circleChart (a : UnitCircle) : OnePoint ℝ ≃ₜ UnitCircle := by
  have ha : ‖(a:ℂ)‖=1 := by simpa only [mem_sphere_zero_iff_norm] using a.property
  have hane : (a:ℂ)≠0 := by intro h; simp [h] at ha
  letI : Fact (Module.finrank ℝ ℂ=1+1) := ⟨by simp [Complex.finrank_real_complex]⟩
  have hdim : Module.finrank ℝ (ℝ ∙ (a:ℂ))ᗮ=1 :=
    Submodule.finrank_orthogonal_span_singleton (n:=1) hane
  let e : ℝ ≃L[ℝ] (ℝ ∙ (a:ℂ))ᗮ :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simpa using hdim.symm)).some
  exact e.toHomeomorph.onePointCongr.trans (onePointHyperplaneHomeoUnitSphere ha)

@[simp] lemma circleChart_infty (a : UnitCircle) : circleChart a ∞=a := by
  rfl

end CannonCircleBoundary

namespace CannonCircleBoundary
open Set Topology Metric

abbrev Punctured (q : ℂ) := {z : ℂ // z≠q}

def radialDirection (q : ℂ) (z : Punctured q) : UnitCircle :=
  ⟨‖(z:ℂ)-q‖⁻¹ • ((z:ℂ)-q),by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property))⟩

lemma radial_ne (q : ℂ) (u : UnitCircle) {s : ℝ} (hs : 0 < s) : q+s•(u:ℂ)≠q := by
  have hu : (u:ℂ)≠0 := by
    have hh : ‖(u:ℂ)‖=1 := mem_sphere_zero_iff_norm.mp u.property
    intro h
    simp [h] at hh
  intro he
  have h : s•(u:ℂ)=0 := add_left_cancel (he.trans (add_zero q).symm)
  exact (smul_ne_zero hs.ne' hu) h

end CannonCircleBoundary

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Spans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

def Spans (a : Arc ℂ) (x y : ℂ) : Prop :=
  (a 0=x ∧ a 1=y) ∨ (a 1=x ∧ a 0=y)
lemma Spans.symm {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : Spans a y x := by
  rcases h with h|h
  · exact Or.inr h.symm
  · exact Or.inl h.symm
lemma Spans.ne {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : x≠y := by
  rcases h with h|h
  · exact h.1 ▸ h.2 ▸ a.endpoints_ne
  · exact h.1 ▸ h.2 ▸ a.endpoints_ne.symm

abbrev GraphVertices (F : ι → Arc ℂ) := {z : ℂ // Vertex F z}
instance graphVertices_finite [Finite ι] (F : ι → Arc ℂ) : Finite (GraphVertices F) := (finite_vertex_set F).to_subtype

def edgeGraph (F : ι → Arc ℂ) (E : Set ι) : SimpleGraph (GraphVertices F) where
  Adj x y := ∃ i∈E,Spans (F i) x.val y.val
  symm := by constructor; rintro x y ⟨i,hi,h⟩; exact ⟨i,hi,h.symm⟩
  loopless := by constructor; rintro x ⟨i,_hi,h⟩; exact h.ne rfl

end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

def edgeStart (F : ι → Arc ℂ) (i : ι) : GraphVertices F := ⟨F i 0,i,Or.inl rfl⟩
def edgeEnd (F : ι → Arc ℂ) (i : ι) : GraphVertices F := ⟨F i 1,i,Or.inr rfl⟩
def edgeKey (F : ι → Arc ℂ) (i : ι) : Sym2 (GraphVertices F) := s(edgeStart F i,edgeEnd F i)

def walkCarrier (F : ι → Arc ℂ) {E : Set ι} {x y : GraphVertices F}
    (w : (edgeGraph F E).Walk x y) : Set ℂ := {z | ∃ i,edgeKey F i∈w.edges ∧ z∈range (F i)}

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_OrientedArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open ComplexConjugate

def orientedArea (a b c : ℂ) : ℝ := (conj (b-a)*(c-a)).im

@[simp] lemma orientedArea_translate (t a b c : ℂ) :
    orientedArea (a+t) (b+t) (c+t)=orientedArea a b c := by
  simp [orientedArea]

@[simp] lemma orientedArea_conj (a b c:ℂ) :
    orientedArea (conj a) (conj b) (conj c)= -orientedArea a b c := by
  simp only [orientedArea,←map_sub,Complex.conj_conj,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

end CannonPackingGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_IncidentFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
abbrev IncidentFaces (F : ι → Arc ℂ) (q : ℂ) := {d : Faces F | q∈closure (face F d)}
abbrev IncidentEdges (F : ι → Arc ℂ) (q : ℂ) := {i : ι | q∈range (F i)}
def vertexFaceGraph (F : ι → Arc ℂ) (q : ℂ) : SimpleGraph (IncidentFaces F q) where
  Adj d c := d≠c ∧ ∃ i : ι,q∈range (F i) ∧
    i∈regionEdges F ConnectedComponents.mk d.val ∧
    i∈regionEdges F ConnectedComponents.mk c.val
  symm := ⟨by rintro d c ⟨hne,i,hi,hd,hc⟩; exact ⟨hne.symm,i,hi,hc,hd⟩⟩
  loopless := ⟨fun d h=>h.1 rfl⟩

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
def vertexLink (F : ι → Arc ℂ) (q : ℂ) : SimpleGraph (IncidentEdges F q ⊕ IncidentFaces F q) where
  Adj
    | .inl i,.inr d => i.val∈regionEdges F ConnectedComponents.mk d.val
    | .inr d,.inl i => i.val∈regionEdges F ConnectedComponents.mk d.val
    | _,_ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_IntrinsicCircleData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HasIntrinsicCircleData (F : ι → Arc ℂ) [Fintype (Faces F)] (out : Faces F) : Prop := by
  classical
  exact
   let V := vertices F Finset.univ
   let A := {d : Faces F // d≠out}
   ∃ vertex : A×Fin 3 → V,
    (∀ f,Function.Injective (fun k=>vertex (f,k))) ∧
    (∀ f,range (fun k=>(vertex (f,k)).val)=(faceVertices F f.val : Set ℂ)) ∧
    ∃ θ : A×Fin 3 → ℝ,∃ r : V → ℝ,∃ q : A → ℝ,
      (∀ i,θ i∈Ioo (0:ℝ) Real.pi) ∧
      (∀ f,∑ k:Fin 3,θ (f,k)=Real.pi) ∧
      (∀ v,(∑ i : A×Fin 3,if vertex i=v then θ i else 0)=
        if v.val∈faceVertices F out then Real.pi/3 else 2*Real.pi) ∧
      (∀ v,0 < r v) ∧ (∀ f,0<q f) ∧
      ∀ i,Real.tan (θ i/2)=q i.1/r (vertex i)
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_EdgeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonGraphGauge
open Set

variable {V E D : Type*} [Fintype E] [Group D]
def edgeGraph (a b : E→V) (hneq:∀i,a i≠b i) (S:Set E) : SimpleGraph V where
  Adj x y := ∃ i∈S,(a i=x ∧ b i=y) ∨ (a i=y ∧ b i=x)
  symm := ⟨by
    rintro x y ⟨i,hi,h|h⟩
    · exact ⟨i,hi,Or.inr h⟩
    · exact ⟨i,hi,Or.inl h⟩⟩
  loopless := ⟨by rintro x ⟨i,hi,h|h⟩ <;> exact hneq i (h.1.trans h.2.symm)⟩

def goodEdges (a b:E→V) (K:E→D) (v:V→D) : Finset E := by
  classical
  exact Finset.univ.filter fun i=>K i*v (a i)=v (b i)
@[simp] lemma mem_goodEdges (a b:E→V) (K:E→D) (v:V→D) (i:E) :
    i∈goodEdges a b K v ↔ K i*v (a i)=v (b i) := by
  classical
  simp [goodEdges]

end CannonGraphGauge

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_DualGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
def dualGraph (F : ι → Arc ℂ) (E : Set ι) : SimpleGraph (Faces F) where
  Adj a b := a≠b ∧ ∃ i∈E,i∈regionEdges F ConnectedComponents.mk a ∧
    i∈regionEdges F ConnectedComponents.mk b
  symm := ⟨by rintro a b ⟨hab,i,hi,ha,hb⟩; exact ⟨hab.symm,i,hi,hb,ha⟩⟩
  loopless := ⟨fun a h=>h.1 rfl⟩

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_DevelopedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

structure DevelopedFaces (F : ι → Arc ℂ) [Fintype (Faces F)] (out : Faces F) where
  radius : ℂ → ℝ
  radius_pos : ∀ q,0 < radius q
  chart : Faces F → ℂ → ℂ
  lengths : ∀ d,∀ u∈faceVertices F d,∀ v∈faceVertices F d,u≠v →
    dist (chart d u) (chart d v)=radius u+radius v
  angle : Faces F → ℂ → ℝ
  angle_pos : ∀ d,d≠out → ∀ q∈faceVertices F d,angle d q∈Ioo (0:ℝ) Real.pi
  angle_sum : ∀ q,Vertex F q → (∑ d,angle d q)=if q∈faceVertices F out then Real.pi/3 else 2*Real.pi
  angle_zero : ∀ d q,q∉faceVertices F d → angle d q=0
  angle_out : ∀ q,angle out q=0
  cosine : ∀ d,d≠out → ∀ u∈faceVertices F d,∀ v∈faceVertices F d,∀ w∈faceVertices F d,
    u≠v → u≠w → v≠w →
    2*(radius u+radius v)*(radius u+radius w)*Real.cos (angle d u)=
      (radius u+radius v)^2+(radius u+radius w)^2-(radius v+radius w)^2
  edge_agree : ∀ i d e,d≠out → e≠out →
    i∈regionEdges F ConnectedComponents.mk d → i∈regionEdges F ConnectedComponents.mk e →
    chart d (F i 0)=chart e (F i 0) ∧ chart d (F i 1)=chart e (F i 1)
  opposite : ∀ i d e,d≠e → d≠out → e≠out →
    i∈regionEdges F ConnectedComponents.mk d → i∈regionEdges F ConnectedComponents.mk e →
    ∀ u∈faceVertices F d,u≠F i 0 → u≠F i 1 →
    ∀ v∈faceVertices F e,v≠F i 0 → v≠F i 1 →
    orientedArea (chart e (F i 0)) (chart e (F i 1)) (chart d u)*
      orientedArea (chart e (F i 0)) (chart e (F i 1)) (chart e v)<0

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

structure FacialCycle (F : ι → Arc ℂ) (d : Faces F) where
  a : ℂ
  b : ℂ
  c : ℂ
  e : ι
  f : ι
  g : ι
  ab : a≠b
  ac : a≠c
  bc : b≠c
  vertices : faceVertices F d={a,b,c}
  mem_e : e∈regionEdges F ConnectedComponents.mk d
  mem_f : f∈regionEdges F ConnectedComponents.mk d
  mem_g : g∈regionEdges F ConnectedComponents.mk d
  spans_e : Spans (F e) a b
  spans_f : Spans (F f) b c
  spans_g : Spans (F g) c a

variable {F : ι → Arc ℂ} {d : Faces F}

def FacialCycle.reverse (C : FacialCycle F d) : FacialCycle F d where
  a := C.a
  b := C.c
  c := C.b
  e := C.g
  f := C.f
  g := C.e
  ab := C.ac
  ac := C.ab
  bc := C.bc.symm
  vertices := by
    classical
    rw [C.vertices,Finset.pair_comm C.b C.c]
  mem_e := C.mem_g
  mem_f := C.mem_f
  mem_g := C.mem_e
  spans_e := C.spans_g.symm
  spans_f := C.spans_f.symm
  spans_g := C.spans_e.symm

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} {d : Faces F}

def FacialCycle.flux {R : Type*} [Zero R] (C : FacialCycle F d) (f : ℂ → ℂ → R) (i : ι) : R :=
  if i=C.e then f C.a C.b else if i=C.f then f C.b C.c else if i=C.g then f C.c C.a else 0

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_CutOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonCycleOrder

def cutOrder {n : ℕ} (hn : 0<n) (o : Fin n) (k : ℕ) : Fin n :=
  ⟨(o.val+1+k)%n,Nat.mod_lt _ hn⟩

end CannonCycleOrder

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_InnerFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

def innerFlux {R : Type*} [AddCommMonoid R]
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val) (f : ℂ → ℂ → R) (i : ι) : R :=
  ∑ d,(C d).flux f i

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FaceHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι]

def faceHull (F : ι → Arc ℂ) (z : ℂ → ℂ) (d : Faces F) : Set ℂ :=
  convexHull ℝ (z '' (faceVertices F d : Set ℂ))

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_CompactifiedFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [Nonempty ι]

variable {X : Type*} [TopologicalSpace X] [T2Space X]

def compactifiedFace (F : ι → Arc ℂ) (e : ℂ → X) (d : Faces F) : Set X :=
  closure (e '' face F d)

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereTile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}

def sphereTile (F : ι → Arc ℂ) (z : ℂ → ℂ) (out d : Faces F) : Set (OnePoint ℂ) :=
  if d=out then ((↑) '' interior (faceHull F z out))ᶜ else (↑) '' faceHull F z d

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonMobius
open Set Topology
open scoped OnePoint

@[simp] lemma inv_inv_apply (p : Sphere) : inv (inv p)=p := inv_involutive p

lemma inv_scalar_differentiable :
    DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (z:Sphere))) {z | inv (z:Sphere) ≠ ∞} := by
  intro z hz
  have hn : z ≠ 0 := by intro hh; subst z; exact hz inv_zero
  simpa only [coordinate_inv_coe] using (differentiableAt_inv hn).differentiableWithinAt

lemma isAnalytic_one : IsAnalytic 1 := by
  intro s t
  cases s <;> cases t
  · change DifferentiableOn ℂ (fun z : ℂ => z) _
    exact differentiable_id.differentiableOn
  · exact inv_scalar_differentiable
  · exact inv_scalar_differentiable
  · change DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (inv (z:Sphere)))) _
    simp_rw [inv_inv_apply,coordinate_coe]
    exact differentiable_id.differentiableOn

lemma isAnalytic_inversion : IsAnalytic inversion := by
  intro s t
  cases s <;> cases t
  · exact inv_scalar_differentiable
  · change DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (inv (z:Sphere)))) _
    simp_rw [inv_inv_apply,coordinate_coe]
    exact differentiable_id.differentiableOn
  · change DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (inv (z:Sphere)))) _
    simp_rw [inv_inv_apply,coordinate_coe]
    exact differentiable_id.differentiableOn
  · change DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (inv (inv (z:Sphere)))))
      {z | inv (inv (inv (z:Sphere))) ≠ ∞}
    simpa only [inv_inv_apply] using inv_scalar_differentiable

def affinePlane (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a*z+b
  invFun z := (z-b)/a
  left_inv z := by simp [ha]
  right_inv z := by field_simp; ring
  continuous_toFun := (continuous_const.mul continuous_id).add continuous_const
  continuous_invFun := (continuous_id.sub continuous_const).div_const a

def affine (a b : ℂ) (ha : a ≠ 0) : Sphere ≃ₜ Sphere := (affinePlane a b ha).onePointCongr
@[simp] lemma affine_infty (a b : ℂ) (ha : a ≠ 0) : affine a b ha ∞=∞ := rfl
@[simp] lemma affine_coe (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    affine a b ha (z:Sphere)=(a*z+b:ℂ) := rfl

lemma affine_symm (a b : ℂ) (ha : a ≠ 0) :
    (affine a b ha).symm=affine a⁻¹ (-b/a) (inv_ne_zero ha) := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change (((z-b)/a:ℂ):Sphere)=((a⁻¹*z+(-b/a):ℂ):Sphere)
    congr 1
    ring

lemma inChart_affine_tt (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    inChart true true (affine a b ha) z=z/(a+b*z) := by
  change coordinate (inv (affine a b ha (inv (z:Sphere))))=_
  by_cases hz : z=0
  · subst z
    rw [inv_zero,affine_infty,inv_infty,coordinate_coe]
    simp
  · rw [inv_coe hz,affine_coe,coordinate_inv_coe]
    have he : a*z⁻¹+b=(a+b*z)/z := by field_simp
    rw [he,inv_div]

lemma isAnalytic_affine (a b : ℂ) (ha : a ≠ 0) : IsAnalytic (affine a b ha) := by
  intro s t
  cases s <;> cases t
  · change DifferentiableOn ℂ (fun z : ℂ => a*z+b) _
    exact ((differentiable_const a).mul differentiable_id |>.add_const b).differentiableOn
  · intro z hz
    change inv ((a*z+b:ℂ):Sphere) ≠ ∞ at hz
    have hn : a*z+b ≠ 0 := by
      intro hh
      rw [hh,inv_zero] at hz
      exact hz rfl
    change DifferentiableWithinAt ℂ (fun z : ℂ => coordinate (inv ((a*z+b:ℂ):Sphere))) _ z
    simp_rw [coordinate_inv_coe]
    exact (((differentiable_const a).mul differentiable_id |>.add_const b) z).inv hn |>.differentiableWithinAt
  · intro z hz
    have hn : z ≠ 0 := by
      intro hh
      subst z
      change affine a b ha (inv ((0:ℂ):Sphere)) ≠ ∞ at hz
      rw [inv_zero,affine_infty] at hz
      exact hz rfl
    have hd : DifferentiableAt ℂ (fun z : ℂ => a*z⁻¹+b) z :=
      ((differentiableAt_const a).mul (differentiableAt_inv hn)).add_const b
    apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [eventually_ne_nhds hn] with w hw
    change coordinate (affine a b ha (inv (w:Sphere)))=a*w⁻¹+b
    rw [inv_coe hw,affine_coe,coordinate_coe]
  · intro z hz
    have hn : a+b*z ≠ 0 := by
      intro hh
      by_cases hz0 : z=0
      · exact ha (by simpa [hz0] using hh)
      · have he : a*z⁻¹+b=0 := by
          have he' : a*z⁻¹+b=(a+b*z)/z := by field_simp
          rw [he',hh,zero_div]
        change inv (affine a b ha (inv (z:Sphere))) ≠ ∞ at hz
        rw [inv_coe hz0,affine_coe,he,inv_zero] at hz
        exact hz rfl
    have hd : DifferentiableAt ℂ (fun z : ℂ => z/(a+b*z)) z :=
      differentiableAt_id.div ((differentiableAt_const a).add
        ((differentiableAt_const b).mul differentiableAt_id)) hn
    rw [show inChart true true (affine a b ha)=(fun z : ℂ => z/(a+b*z)) from funext (inChart_affine_tt a b ha)]
    exact hd.differentiableWithinAt

def biholomorphic : Subgroup (Sphere ≃ₜ Sphere) where
  carrier := {f | IsAnalytic f ∧ IsAnalytic f.symm}
  one_mem' := ⟨isAnalytic_one,isAnalytic_one⟩
  mul_mem' := by
    intro f g hf hg
    exact ⟨isAnalytic_mul hf.1 hg.1,isAnalytic_mul hg.2 hf.2⟩
  inv_mem' := by intro f hf; exact ⟨hf.2,hf.1⟩

lemma affine_biholomorphic (a b : ℂ) (ha : a ≠ 0) : affine a b ha ∈ biholomorphic := by
  refine ⟨isAnalytic_affine a b ha,?_⟩
  rw [affine_symm]
  exact isAnalytic_affine _ _ _

lemma inversion_biholomorphic : inversion ∈ biholomorphic :=
  ⟨isAnalytic_inversion,isAnalytic_inversion⟩
end CannonMobius

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

abbrev Triple := {t : Fin 3 → Sphere // Function.Injective t}
def tripleMap (f : Sphere ≃ₜ Sphere) (t : Triple) : Triple := ⟨f ∘ t.val,f.injective.comp t.property⟩
@[simp] lemma tripleMap_mul (f g : Sphere ≃ₜ Sphere) (t : Triple) :
    tripleMap (f*g) t=tripleMap f (tripleMap g t) := rfl

end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_AnalyticFixInftyAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonMobius
open Set
open scoped OnePoint

lemma analytic_fix_infty_eq_affine (f : Sphere ≃ₜ Sphere) (hInfinity : f ∞=∞)
    (hf : f ∈ biholomorphic) : ∃ a b : ℂ, ∃ ha : a ≠ 0, f=affine a b ha := by
  obtain ⟨a,b,ha,he⟩ := analytic_fix_infty_affine f hInfinity hf.1 hf.2
  refine ⟨a,b,ha,?_⟩
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => exact hInfinity
  | coe z => exact he z

theorem biholomorphic_normal_form (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic) :
    (∃ a b : ℂ, ∃ ha : a ≠ 0, f=affine a b ha) ∨
    (∃ p a b : ℂ, ∃ ha : a ≠ 0,
      f=affine 1 p one_ne_zero*inversion*affine a b ha) := by
  by_cases hInfinity : f ∞=∞
  · exact Or.inl (analytic_fix_infty_eq_affine f hInfinity hf)
  · have hp : ∃ p : ℂ, f ∞=(p:Sphere) := by
      induction h : f ∞ using OnePoint.rec with
      | infty => exact (hInfinity h).elim
      | coe p => exact ⟨p,rfl⟩
    obtain ⟨p,hp⟩ := hp
    let N : Sphere ≃ₜ Sphere := inversion*affine 1 (-p) one_ne_zero
    have hNg : N ∈ biholomorphic := biholomorphic.mul_mem inversion_biholomorphic
      (affine_biholomorphic 1 (-p) one_ne_zero)
    have hNf : (N*f) ∞=∞ := by
      change inv (affine 1 (-p) one_ne_zero (f ∞))=∞
      rw [hp,affine_coe]
      simp only [one_mul,add_neg_cancel,inv_zero]
    obtain ⟨a,b,ha,he⟩ := analytic_fix_infty_eq_affine (N*f) hNf (biholomorphic.mul_mem hNg hf)
    have hNi : N⁻¹=affine 1 p one_ne_zero*inversion := by
      rw [show N=inversion*affine 1 (-p) one_ne_zero from rfl,mul_inv_rev]
      change (affine 1 (-p) one_ne_zero).symm*inversion=affine 1 p one_ne_zero*inversion
      rw [affine_symm]
      simp only [inv_one,neg_neg,div_one]
    refine Or.inr ⟨p,a,b,ha,?_⟩
    calc
      f=N⁻¹*(N*f) := by rw [← mul_assoc,inv_mul_cancel,one_mul]
      _=affine 1 p one_ne_zero*inversion*affine a b ha := by rw [hNi,he]

theorem biholomorphic_mem_of_generators (S : Subgroup (Sphere ≃ₜ Sphere))
    (ha : ∀ a b : ℂ, ∀ h : a ≠ 0, affine a b h ∈ S) (hi : inversion ∈ S)
    {f : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic) : f ∈ S := by
  rcases biholomorphic_normal_form f hf with ⟨a,b,h,rfl⟩ | ⟨p,a,b,h,rfl⟩
  · exact ha a b h
  · exact S.mul_mem (S.mul_mem (ha 1 p one_ne_zero) hi) (ha a b h)
end CannonMobius

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Actions_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
noncomputable section
namespace CannonH3
open CannonRelease Set Topology

abbrev Height := {t : ℝ // 0 < t}
abbrev Half := ℂ × Height

def coords : HyperbolicThree ≃ₜ Half where
  toFun x := ⟨⟨x.val 0,x.val 1⟩,⟨x.val 2,x.property⟩⟩
  invFun p := ⟨![p.1.re,p.1.im,p.2.val],p.2.property⟩
  left_inv x := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · have hc : Continuous (fun x : HyperbolicThree => (x.val 0:ℂ)+(x.val 1:ℂ)*Complex.I) :=
        (Complex.continuous_ofReal.comp ((continuous_apply 0).comp continuous_subtype_val)).add
          ((Complex.continuous_ofReal.comp ((continuous_apply 1).comp continuous_subtype_val)).mul continuous_const)
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      exact (Complex.re_add_im _).symm
    · exact ((continuous_apply 2).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact Complex.continuous_re.comp continuous_fst
    · exact Complex.continuous_im.comp continuous_fst
    · exact continuous_subtype_val.comp continuous_snd

def distArg (x y : Half) : ℝ :=
  1+(‖x.1-y.1‖^2+(x.2.val-y.2.val)^2)/(2*x.2.val*y.2.val)

def heightScale (s : ℝ) (hs : 0 < s) : Height ≃ₜ Height where
  toFun t := ⟨s*t.val,mul_pos hs t.property⟩
  invFun t := ⟨t.val/s,div_pos t.property hs⟩
  left_inv t := by ext; exact mul_div_cancel_left₀ t.val hs.ne'
  right_inv t := by ext; exact mul_div_cancel₀ t.val hs.ne'
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.div_const s).subtype_mk _

def complexAffine (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a*z+b
  invFun z := (z-b)/a
  left_inv z := by simp [ha]
  right_inv z := by field_simp; ring
  continuous_toFun := (continuous_const.mul continuous_id).add continuous_const
  continuous_invFun := (continuous_id.sub continuous_const).div_const a

def affine (a b : ℂ) (ha : a ≠ 0) : Half ≃ₜ Half :=
  (complexAffine a b ha).prodCongr (heightScale ‖a‖ (norm_pos_iff.mpr ha))

lemma affine_preserves (a b : ℂ) (ha : a ≠ 0) (x y : Half) :
    distArg (affine a b ha x) (affine a b ha y)=distArg x y := by
  have he : a*x.1+b-(a*y.1+b)=a*(x.1-y.1) := by ring
  change 1+(‖a*x.1+b-(a*y.1+b)‖^2+(‖a‖*x.2.val-‖a‖*y.2.val)^2)/
    (2*(‖a‖*x.2.val)*(‖a‖*y.2.val))=distArg x y
  rw [he,norm_mul]
  unfold distArg
  have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  field_simp

def q (x : Half) : ℝ := ‖x.1‖^2+x.2.val^2
lemma q_pos (x : Half) : 0 < q x := by
  have hh := x.2.property
  unfold q
  nlinarith [sq_nonneg ‖x.1‖]

def inversionFun (x : Half) : Half :=
  ⟨star x.1 / (q x:ℂ),⟨x.2.val/q x,div_pos x.2.property (q_pos x)⟩⟩

lemma inversion_q (x : Half) : q (inversionFun x)=(q x)⁻¹ := by
  change ‖star x.1/(q x:ℂ)‖^2+(x.2.val/q x)^2=(q x)⁻¹
  rw [norm_div,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (q_pos x)]
  unfold q
  have hq := (q_pos x).ne'
  change ‖x.1‖^2+x.2.val^2 ≠ 0 at hq
  field_simp

lemma inversion_involutive : Function.Involutive inversionFun := by
  intro x
  apply Prod.ext
  · change star (star x.1/(q x:ℂ))/((q (inversionFun x)):ℂ)=x.1
    rw [inversion_q]
    simp [Complex.conj_ofReal,Complex.ofReal_inv,(q_pos x).ne']
  · apply Subtype.ext
    change (x.2.val/q x)/q (inversionFun x)=x.2.val
    rw [inversion_q]
    field_simp [(q_pos x).ne']

lemma continuous_q : Continuous q := by
  unfold q
  fun_prop

lemma continuous_inversion : Continuous inversionFun := by
  apply Continuous.prodMk
  · exact (continuous_star.comp continuous_fst).div
      (Complex.continuous_ofReal.comp continuous_q) (fun x => by exact_mod_cast (q_pos x).ne')
  · exact ((continuous_subtype_val.comp continuous_snd).div continuous_q (fun x => (q_pos x).ne')).subtype_mk _

def inversion : Half ≃ₜ Half where
  toFun := inversionFun
  invFun := inversionFun
  left_inv := inversion_involutive
  right_inv := inversion_involutive
  continuous_toFun := continuous_inversion
  continuous_invFun := continuous_inversion
end CannonH3

namespace CannonH3
lemma inversion_preserves (x y : Half) :
    distArg (inversion x) (inversion y)=distArg x y := by
  have hxq : q x ≠ 0 := (q_pos x).ne'
  have hyq : q y ≠ 0 := (q_pos y).ne'
  have hxt : x.2.val ≠ 0 := x.2.property.ne'
  have hyt : y.2.val ≠ 0 := y.2.property.ne'
  have heq : ‖(inversion x).1-(inversion y).1‖^2 =
    (x.1.re/q x-y.1.re/q y)^2+(-x.1.im/q x-(-y.1.im)/q y)^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    change ((star x.1/(q x:ℂ)).re-(star y.1/(q y:ℂ)).re)*
      ((star x.1/(q x:ℂ)).re-(star y.1/(q y:ℂ)).re)+
      ((star x.1/(q x:ℂ)).im-(star y.1/(q y:ℂ)).im)*
      ((star x.1/(q x:ℂ)).im-(star y.1/(q y:ℂ)).im)=_
    simp only [Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring
  unfold distArg
  rw [heq,Complex.sq_norm]
  change 1+(_+(x.2.val/q x-y.2.val/q y)^2)/(2*(x.2.val/q x)*(y.2.val/q y))=
    1+(Complex.normSq (x.1-y.1)+(x.2.val-y.2.val)^2)/(2*x.2.val*y.2.val)
  apply congrArg (fun t : ℝ => 1+t)
  apply (div_eq_div_iff (by positivity : 2*(x.2.val/q x)*(y.2.val/q y) ≠ 0)
    (by positivity : 2*x.2.val*y.2.val ≠ 0)).mpr
  field_simp
  unfold q
  rw [Complex.sq_norm,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

end CannonH3

noncomputable section
open Set Filter Topology
open scoped OnePoint

namespace CannonH3
open Set Topology
open scoped OnePoint

abbrev Boundary := OnePoint ℂ

def potential (x : Half) (p : Boundary) : ℝ :=
  p.elim (1/x.2.val) (fun z => (‖x.1-z‖^2+x.2.val^2)/(x.2.val*(1+‖z‖^2)))

@[simp] lemma potential_infty (x : Half) : potential x ∞=1/x.2.val := rfl
@[simp] lemma potential_coe (x : Half) (z : ℂ) :
  potential x (z:Boundary)=(‖x.1-z‖^2+x.2.val^2)/(x.2.val*(1+‖z‖^2)) := rfl

lemma potential_pos (x : Half) (p : Boundary) : 0 < potential x p := by
  induction p using OnePoint.rec with
  | infty => exact one_div_pos.mpr x.2.property
  | coe z =>
    apply div_pos
    · nlinarith [sq_nonneg ‖x.1-z‖,x.2.property]
    · exact mul_pos x.2.property (by nlinarith [sq_nonneg ‖z‖])

def Compatible (f : Boundary ≃ₜ Boundary) (F : Half ≃ₜ Half) : Prop :=
  ∀ x y p, potential (F x) (f p)*potential y p=
    potential x p*potential (F y) (f p)

def quadratic (x : Half) (p : ℂ) : ℝ := ‖x.1-p‖^2+x.2.val^2
lemma quadratic_pos (x : Half) (p : ℂ) : 0 < quadratic x p := by
  unfold quadratic
  nlinarith [sq_nonneg ‖x.1-p‖,x.2.property]

lemma height_relation {F : Half ≃ₜ Half} (hF : Compatible 1 F) (x y : Half) :
    (F x).2.val*y.2.val=x.2.val*(F y).2.val := by
  have he := hF x y ∞
  change (1/(F x).2.val)*(1/y.2.val)=(1/x.2.val)*(1/(F y).2.val) at he
  have hxt := x.2.property.ne'
  have hyt := y.2.property.ne'
  have hfxt := (F x).2.property.ne'
  have hfyt := (F y).2.property.ne'
  field_simp at he
  nlinarith [he]

lemma quadratic_relation {F : Half ≃ₜ Half} (hF : Compatible 1 F) (x y : Half) (p : ℂ) :
    quadratic (F x) p*quadratic y p=quadratic x p*quadratic (F y) p := by
  have he := hF x y (p:Boundary)
  change (quadratic (F x) p/((F x).2.val*(1+‖p‖^2)))*
      (quadratic y p/(y.2.val*(1+‖p‖^2)))=
    (quadratic x p/(x.2.val*(1+‖p‖^2)))*
      (quadratic (F y) p/((F y).2.val*(1+‖p‖^2))) at he
  rw [div_mul_div_comm,div_mul_div_comm] at he
  have hd : (F x).2.val*(1+‖p‖^2)*(y.2.val*(1+‖p‖^2))=
      x.2.val*(1+‖p‖^2)*((F y).2.val*(1+‖p‖^2)) := by
    calc
      _ = ((F x).2.val*y.2.val)*(1+‖p‖^2)^2 := by ring
      _ = (x.2.val*(F y).2.val)*(1+‖p‖^2)^2 := by rw [height_relation hF x y]
      _ = _ := by ring
  rw [hd] at he
  exact (div_left_inj' (mul_ne_zero
    (mul_ne_zero x.2.property.ne' (by nlinarith [sq_nonneg ‖p‖]))
    (mul_ne_zero (F y).2.property.ne' (by nlinarith [sq_nonneg ‖p‖])))).mp he

lemma quadratic_re (x : Half) (r : ℝ) :
    quadratic x (r:ℂ)=r^2-2*x.1.re*r+q x := by
  unfold quadratic q
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,sub_zero]
  ring

lemma quadratic_im (x : Half) (r : ℝ) :
    quadratic x ((r:ℂ)*Complex.I)=r^2-2*x.1.im*r+q x := by
  unfold quadratic q
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,sub_zero]
  ring

lemma product_quadratic_coefficients (a A b B c C : ℝ)
    (h : ∀ r : ℝ, (r^2-2*a*r+A)*(r^2+1)=
      (r^2-2*b*r+B)*(r^2-2*c*r+C)) :
    A=B*C ∧ a=b+c ∧ A+1=B+C+4*b*c ∧ a=b*C+c*B := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,sub_zero,zero_add] at h0
  norm_num at h0
  refine ⟨h0,?_,?_,?_⟩
  · nlinarith [h1,hm1,h2,hm2]
  · nlinarith [h0,h1,hm1]
  · nlinarith [h1,hm1,h2,hm2]

def basepoint : Half := ⟨0,⟨1,by norm_num⟩⟩

lemma basepoint_fixed {F : Half ≃ₜ Half} (hF : Compatible 1 F) : F basepoint=basepoint := by
  let xr : Half := ⟨1,⟨1,by norm_num⟩⟩
  let xi : Half := ⟨Complex.I,⟨1,by norm_num⟩⟩
  have hr : ∀ r : ℝ, (r^2-2*(F xr).1.re*r+q (F xr))*(r^2+1)=
      (r^2-2*1*r+2)*(r^2-2*(F basepoint).1.re*r+q (F basepoint)) := by
    intro r
    have he := quadratic_relation hF xr basepoint (r:ℂ)
    rw [quadratic_re,quadratic_re,quadratic_re,quadratic_re] at he
    simpa [xr,basepoint,q,show (1:ℝ)+1=2 by norm_num] using he
  obtain ⟨hA,ha,hB,hb⟩ := product_quadratic_coefficients _ _ _ _ _ _ hr
  have hre : (F basepoint).1.re=0 := by nlinarith
  have hq : q (F basepoint)=1 := by nlinarith
  have hi : ∀ r : ℝ, (r^2-2*(F xi).1.im*r+q (F xi))*(r^2+1)=
      (r^2-2*1*r+2)*(r^2-2*(F basepoint).1.im*r+q (F basepoint)) := by
    intro r
    have he := quadratic_relation hF xi basepoint ((r:ℂ)*Complex.I)
    rw [quadratic_im,quadratic_im,quadratic_im,quadratic_im] at he
    simpa [xi,basepoint,q,show (1:ℝ)+1=2 by norm_num] using he
  obtain ⟨hA',ha',hB',hb'⟩ := product_quadratic_coefficients _ _ _ _ _ _ hi
  have him : (F basepoint).1.im=0 := by nlinarith
  have hz : (F basepoint).1=0 := Complex.ext hre him
  apply Prod.ext hz
  apply Subtype.ext
  change (F basepoint).2.val=1
  unfold q at hq
  rw [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add] at hq
  nlinarith [(F basepoint).2.property]

lemma compatible_identity_unique {F : Half ≃ₜ Half} (hF : Compatible 1 F) : F=1 := by
  have h0 := basepoint_fixed hF
  apply Homeomorph.ext
  intro x
  have hquad (p : ℂ) : quadratic (F x) p=quadratic x p := by
    have he := quadratic_relation hF x basepoint p
    rw [h0] at he
    exact mul_right_cancel₀ (quadratic_pos basepoint p).ne' he
  have hq : q (F x)=q x := by simpa [quadratic,q] using hquad 0
  have hre : (F x).1.re=x.1.re := by
    have he := hquad 1
    have e1 := quadratic_re (F x) 1
    have e2 := quadratic_re x 1
    norm_num at e1 e2
    rw [e1,e2] at he
    linarith
  have him : (F x).1.im=x.1.im := by
    have he := hquad Complex.I
    have e1 := quadratic_im (F x) 1
    have e2 := quadratic_im x 1
    norm_num at e1 e2
    rw [e1,e2] at he
    linarith
  have hz : (F x).1=x.1 := Complex.ext hre him
  apply Prod.ext hz
  apply Subtype.ext
  change (F x).2.val=x.2.val
  unfold q at hq
  rw [hz] at hq
  nlinarith [(F x).2.property,x.2.property]
end CannonH3

namespace CannonH3
open Set

lemma compatible_one : Compatible 1 1 := by intro x y p; rfl
lemma compatible_mul {f g : Boundary ≃ₜ Boundary} {F G : Half ≃ₜ Half}
    (hf : Compatible f F) (hg : Compatible g G) : Compatible (f*g) (F*G) := by
  intro x y p
  change potential (F (G x)) (f (g p))*potential y p=
    potential x p*potential (F (G y)) (f (g p))
  apply mul_right_cancel₀ (potential_pos (G y) (g p)).ne'
  have h1 := hf (G x) (G y) (g p)
  have h2 := hg x y p
  linear_combination potential y p*h1+potential (F (G y)) (f (g p))*h2

lemma compatible_inv {f : Boundary ≃ₜ Boundary} {F : Half ≃ₜ Half}
    (hf : Compatible f F) : Compatible f⁻¹ F⁻¹ := by
  intro x y p
  simpa only [Homeomorph.inv_apply,Homeomorph.apply_symm_apply] using
    (hf (F.symm x) (F.symm y) (f.symm p)).symm

def paired : Subgroup ((Boundary ≃ₜ Boundary) × (Half ≃ₜ Half)) where
  carrier := {u | Compatible u.1 u.2 ∧ ∀ x y, distArg (u.2 x) (u.2 y)=distArg x y}
  one_mem' := ⟨compatible_one,by intro x y; rfl⟩
  mul_mem' := by
    rintro ⟨f,F⟩ ⟨g,G⟩ ⟨hf,hF⟩ ⟨hg,hG⟩
    refine ⟨compatible_mul hf hg,?_⟩
    intro x y
    exact (hF (G x) (G y)).trans (hG x y)
  inv_mem' := by
    rintro ⟨f,F⟩ ⟨hf,hF⟩
    refine ⟨compatible_inv hf,?_⟩
    intro x y
    change distArg (F.symm x) (F.symm y)=distArg x y
    simpa only [Homeomorph.apply_symm_apply] using (hF (F.symm x) (F.symm y)).symm

def boundaryProjection : paired →* (Boundary ≃ₜ Boundary) where
  toFun u := u.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

lemma boundaryProjection_injective : Function.Injective boundaryProjection := by
  apply (injective_iff_map_eq_one boundaryProjection).mpr
  intro u hu
  apply Subtype.ext
  apply Prod.ext hu
  apply compatible_identity_unique
  have hh := u.property.1
  change u.val.1=1 at hu
  rwa [hu] at hh

def boundaryGroup : Subgroup (Boundary ≃ₜ Boundary) := boundaryProjection.range

end CannonH3

namespace CannonH3
open Set
open scoped OnePoint

def boundaryAffine (a b : ℂ) (ha : a ≠ 0) : Boundary ≃ₜ Boundary :=
  (complexAffine a b ha).onePointCongr

lemma affine_potential (a b : ℂ) (ha : a ≠ 0) (x : Half) (p : ℂ) :
    potential (affine a b ha x) (boundaryAffine a b ha p)=
      (‖a‖*(1+‖p‖^2)/(1+‖a*p+b‖^2))*potential x p := by
  change (‖a*x.1+b-(a*p+b)‖^2+(‖a‖*x.2.val)^2)/
    ((‖a‖*x.2.val)*(1+‖a*p+b‖^2))=_
  have he : a*x.1+b-(a*p+b)=a*(x.1-p) := by ring
  rw [he,norm_mul,potential_coe]
  have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hp : 1+‖p‖^2 ≠ 0 := by nlinarith [sq_nonneg ‖p‖]
  have hap : 1+‖a*p+b‖^2 ≠ 0 := by nlinarith [sq_nonneg ‖a*p+b‖]
  field_simp

lemma affine_compatible (a b : ℂ) (ha : a ≠ 0) :
    Compatible (boundaryAffine a b ha) (affine a b ha) := by
  intro x y p
  induction p using OnePoint.rec with
  | infty =>
    change (1/(‖a‖*x.2.val))*(1/y.2.val)=(1/x.2.val)*(1/(‖a‖*y.2.val))
    ring
  | coe p => rw [affine_potential,affine_potential]; ring

lemma inversion_potential (x : Half) (p : Boundary) :
    potential (inversion x) (CannonMobius.inversion p)=potential x p := by
  have hq : q x ≠ 0 := (q_pos x).ne'
  have ht : x.2.val ≠ 0 := x.2.property.ne'
  induction p using OnePoint.rec with
  | infty =>
    change potential (inversion x) ((0:ℂ):Boundary)=potential x ∞
    rw [potential_coe,potential_infty,sub_zero]
    change q (inversionFun x)/((x.2.val/q x)*(1+‖(0:ℂ)‖^2))=1/x.2.val
    rw [inversion_q]
    simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,mul_one]
    field_simp
  | coe p =>
    by_cases hp : p=0
    · subst p
      change potential (inversion x) (CannonMobius.inv ((0:ℂ):Boundary))=potential x ((0:ℂ):Boundary)
      rw [CannonMobius.inv_zero,potential_infty,potential_coe]
      change 1/(x.2.val/q x)=(‖x.1-0‖^2+x.2.val^2)/(x.2.val*(1+‖(0:ℂ)‖^2))
      simp only [sub_zero,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,mul_one]
      unfold q
      field_simp
    · have hp' : ‖p‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hp)
      change potential (inversion x) (CannonMobius.inv (p:Boundary))=potential x p
      rw [CannonMobius.inv_coe hp,potential_coe,potential_coe]
      have he : ‖(inversion x).1-p⁻¹‖^2=
        (‖x.1-p‖^2+x.2.val^2)/(q x*‖p‖^2)-(x.2.val/q x)^2 := by
        change ‖star x.1/(q x:ℂ)-p⁻¹‖^2=_
        simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
          Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.star_def,Complex.conj_re,
          Complex.conj_im,Complex.inv_re,Complex.inv_im]
        have hn : Complex.normSq p ≠ 0 := (Complex.normSq_pos.mpr hp).ne'
        have hn' : p.re*p.re+p.im*p.im ≠ 0 := hn
        unfold q
        rw [Complex.sq_norm]
        simp only [Complex.normSq_apply]
        simp only [sq]
        have hn2 : p.re^2+p.im^2 ≠ 0 := by simpa only [sq] using hn'
        field_simp [hn', hn2, Complex.normSq_apply]
        ring_nf
      rw [he,norm_inv]
      change (_+(x.2.val/q x)^2)/((x.2.val/q x)*(1+(‖p‖⁻¹)^2))=_
      have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
      have hs : 1+‖p‖^2 ≠ 0 := by nlinarith [sq_nonneg ‖p‖]
      field_simp
      ring

lemma inversion_compatible : Compatible CannonMobius.inversion inversion := by
  intro x y p
  rw [inversion_potential,inversion_potential]

end CannonH3

noncomputable section
open Set Filter Topology

namespace CannonH3
open scoped OnePoint

lemma affine_mem_boundaryGroup (a b : ℂ) (ha : a ≠ 0) :
    CannonMobius.affine a b ha ∈ boundaryGroup := by
  have he : boundaryAffine a b ha=CannonMobius.affine a b ha := by
    apply Homeomorph.ext
    intro p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe z => rfl
  refine ⟨⟨(boundaryAffine a b ha,affine a b ha),affine_compatible a b ha,
    affine_preserves a b ha⟩,he⟩

lemma inversion_mem_boundaryGroup : CannonMobius.inversion ∈ boundaryGroup :=
  ⟨⟨(CannonMobius.inversion,inversion),inversion_compatible,inversion_preserves⟩,rfl⟩

lemma biholomorphic_mem_boundaryGroup {f : Boundary ≃ₜ Boundary}
    (hf : f ∈ CannonMobius.biholomorphic) : f ∈ boundaryGroup :=
  CannonMobius.biholomorphic_mem_of_generators boundaryGroup
    affine_mem_boundaryGroup inversion_mem_boundaryGroup hf

def reflection : Half ≃ₜ Half :=
  Complex.conjCLE.toHomeomorph.prodCongr (Homeomorph.refl Height)
def boundaryReflection : Boundary ≃ₜ Boundary := Complex.conjCLE.toHomeomorph.onePointCongr

lemma reflection_potential (x : Half) (p : Boundary) :
    potential (reflection x) (boundaryReflection p)=potential x p := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe p =>
    change (‖star x.1-star p‖^2+x.2.val^2)/(x.2.val*(1+‖star p‖^2))=_
    rw [← star_sub,norm_star,norm_star]
    rfl
lemma reflection_compatible : Compatible boundaryReflection reflection := by
  intro x y p
  rw [reflection_potential,reflection_potential]
lemma reflection_distArg (x y : Half) : distArg (reflection x) (reflection y)=distArg x y := by
  change 1+(‖star x.1-star y.1‖^2+(x.2.val-y.2.val)^2)/(2*x.2.val*y.2.val)=_
  rw [← star_sub,norm_star]
  rfl
lemma reflection_mem_boundaryGroup : boundaryReflection ∈ boundaryGroup :=
  ⟨⟨(boundaryReflection,reflection),reflection_compatible,reflection_distArg⟩,rfl⟩

lemma boundaryReflection_sq : boundaryReflection*boundaryReflection=1 := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe p => exact congrArg (fun z : ℂ => (z:Boundary)) (star_star p)

theorem conformal_or_anticonformal_mem {f : Boundary ≃ₜ Boundary}
    (hf : f ∈ CannonMobius.biholomorphic ∨ boundaryReflection*f ∈ CannonMobius.biholomorphic) :
    f ∈ boundaryGroup := by
  rcases hf with hf|hf
  · exact biholomorphic_mem_boundaryGroup hf
  · have h := boundaryGroup.mul_mem reflection_mem_boundaryGroup
      (biholomorphic_mem_boundaryGroup hf)
    simpa only [← mul_assoc,boundaryReflection_sq,one_mul] using h

end CannonH3

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Actions_Proper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Properness and cocompactness transferred through equivariant maps. -/

section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonActions
open Set

variable {Γ X Y : Type*} [Group Γ] [TopologicalSpace X] [TopologicalSpace Y]

def Proper (A : Γ →* (X ≃ₜ X)) : Prop :=
  ∀ K : Set X, IsCompact K → {g : Γ | ∃ x ∈ K, A g x ∈ K}.Finite

def Cocompact (A : Γ →* (X ≃ₜ X)) : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : Γ, ∃ y ∈ K, A g y=x

def conjugate (ψ : X ≃ₜ Y) (A : Γ →* (X ≃ₜ X)) : Γ →* (Y ≃ₜ Y) where
  toFun g := (ψ.symm.trans (A g)).trans ψ
  map_one' := by
    ext y
    simp only [map_one,Homeomorph.trans_apply,Homeomorph.one_apply,Homeomorph.apply_symm_apply]
  map_mul' g h := by
    ext y
    simp only [map_mul,Homeomorph.trans_apply,Homeomorph.mul_apply,Homeomorph.symm_apply_apply]

end CannonActions

namespace CannonActions
open Set

variable {X Y Z Γ : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [Group Γ]
abbrev OrderedTriples (X : Type*) := {t : Fin 3 → X // Function.Injective t}
def triplesMap (f : X ≃ₜ Y) (t : OrderedTriples X) : OrderedTriples Y :=
  ⟨f ∘ t.val,f.injective.comp t.property⟩
lemma continuous_triplesMap (f : X ≃ₜ Y) : Continuous (triplesMap f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact f.continuous.comp ((continuous_apply i).comp continuous_subtype_val)
def triplesCongr (f : X ≃ₜ Y) : OrderedTriples X ≃ₜ OrderedTriples Y where
  toFun := triplesMap f
  invFun := triplesMap f.symm
  left_inv t := by apply Subtype.ext; funext i; exact f.symm_apply_apply _
  right_inv t := by apply Subtype.ext; funext i; exact f.apply_symm_apply _
  continuous_toFun := continuous_triplesMap f
  continuous_invFun := continuous_triplesMap f.symm

def triplesHom : (X ≃ₜ X) →* (OrderedTriples X ≃ₜ OrderedTriples X) where
  toFun := triplesCongr
  map_one' := by apply Homeomorph.ext; intro t; rfl
  map_mul' f g := by apply Homeomorph.ext; intro t; rfl

def triplesAction (A : Γ →* (X ≃ₜ X)) : Γ →* (OrderedTriples X ≃ₜ OrderedTriples X) := triplesHom.comp A

end CannonActions

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_MultiplyLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CannonBeltrami

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma memLp_multiply (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    MemLp (fun x => m x*f x) 2 ν := by
  apply (Lp.memLp f).of_le_mul (c:=k) (hm.mul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖m x*f x‖ ≤ k*‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def multiplyLp (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) : Lp ℂ 2 ν :=
  (memLp_multiply m hm hb f).toLp

lemma multiplyLp_ae (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    multiplyLp m hm hb f =ᵐ[ν] fun x => m x*f x :=
  MemLp.coeFn_toLp _

lemma multiplyLp_add (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f g : Lp ℂ 2 ν) :
    multiplyLp m hm hb (f+g)=multiplyLp m hm hb f+multiplyLp m hm hb g := by
  apply Lp.ext
  filter_upwards [multiplyLp_ae m hm hb (f+g),multiplyLp_ae m hm hb f,
    multiplyLp_ae m hm hb g,Lp.coeFn_add f g,
    Lp.coeFn_add (multiplyLp m hm hb f) (multiplyLp m hm hb g)] with x h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1,h5,h2,h3,h4,mul_add]

lemma multiplyLp_smul (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (c : ℂ) (f : Lp ℂ 2 ν) :
    multiplyLp m hm hb (c • f)=c • multiplyLp m hm hb f := by
  apply Lp.ext
  filter_upwards [multiplyLp_ae m hm hb (c • f),multiplyLp_ae m hm hb f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (multiplyLp m hm hb f)] with x h1 h2 h3 h4
  simp only [Pi.smul_apply,smul_eq_mul] at h3 h4
  rw [h1,h4,h2,h3]
  exact mul_left_comm _ _ _

lemma norm_multiplyLp_le (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (_hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    ‖multiplyLp m hm hb f‖ ≤ k*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplyLp_ae m hm hb f,hb] with x hx hx'
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right hx' (norm_nonneg _)

def multiplier (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  LinearMap.mkContinuous
    { toFun := multiplyLp m hm hb
      map_add' := multiplyLp_add m hm hb
      map_smul' := multiplyLp_smul m hm hb }
    k (norm_multiplyLp_le m hm hk hb)

abbrev PlaneL2 := Lp (α:=ℂ) ℂ 2 volume

def beurlingSymbol (z : ℂ) : ℂ := if z=0 then 1 else star z/z

lemma measurable_beurlingSymbol : Measurable beurlingSymbol := by
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (continuous_star.measurable.div measurable_id)

lemma norm_beurlingSymbol (z : ℂ) : ‖beurlingSymbol z‖=1 := by
  by_cases hz : z=0
  · simp [beurlingSymbol,hz]
  · simp [beurlingSymbol,hz,norm_ne_zero_iff.mpr hz]

def symbolMultiplier : PlaneL2 →L[ℂ] PlaneL2 :=
  multiplier beurlingSymbol measurable_beurlingSymbol.aestronglyMeasurable zero_le_one
    (.of_forall (fun z => (norm_beurlingSymbol z).le))

def planeFourier : PlaneL2 ≃ₗᵢ[ℂ] PlaneL2 := Lp.fourierTransformₗᵢ ℂ ℂ

def beurling : PlaneL2 →L[ℂ] PlaneL2 :=
  planeFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (symbolMultiplier.comp planeFourier.toContinuousLinearEquiv.toContinuousLinearMap)

open FourierTransform

def translateL2 (a : ℂ) : PlaneL2 →ₗᵢ[ℂ] PlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℂ => z+a) (measurePreserving_add_right volume a)

def translationPhase (a z : ℂ) : ℂ := Real.fourierChar (inner ℝ a z)

lemma continuous_translationPhase (a : ℂ) : Continuous (translationPhase a) := by
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id))

lemma norm_translationPhase (a z : ℂ) : ‖translationPhase a z‖=1 := Circle.norm_coe _

def phaseMultiplier (a : ℂ) : PlaneL2 →L[ℂ] PlaneL2 :=
  multiplier (translationPhase a) (continuous_translationPhase a).aestronglyMeasurable
    zero_le_one (.of_forall fun z => (norm_translationPhase a z).le)

def directionSymbol (v z : ℂ) : ℂ := 2*Real.pi*Complex.I*(inner ℝ v z : ℝ)

open scoped ENNReal

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_Axis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CannonBeltrami

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

open FourierTransform
open scoped ENNReal

def axis (b : Bool) : ℂ := if b then Complex.I else 1

def Sobolev : ℕ → PlaneL2 → Prop
  | 0, _ => True
  | n+1, f => Sobolev n f ∧ ∀ b : Bool, ∃ df : PlaneL2,
      HasDerivAt (fun t : ℝ => translateL2 (t • axis b) f) df 0 ∧ Sobolev n df

def BoundedSmooth : ℕ → (ℂ → ℂ) → Prop
  | 0, μ => AEStronglyMeasurable μ volume ∧ ∃ K : NNReal, ∀ z, ‖μ z‖ ≤ K
  | n+1, μ => BoundedSmooth n μ ∧ ∃ L : NNReal, LipschitzWith L μ ∧
      ∀ b : Bool, ∃ d : ℂ → ℂ, BoundedSmooth n d ∧
        ∀ z, HasDerivAt (fun t : ℝ => μ (z+t • axis b)) (d z) 0

open scoped SchwartzMap LineDeriv FourierTransform

def SmoothL2 (f : PlaneL2) : Prop := ∀ n : ℕ, Sobolev n f

open scoped ContDiff

def smoothRepresentative (f : PlaneL2) : ℂ → ℂ := 𝓕⁻ (planeFourier f : ℂ → ℂ)

end CannonBeltrami

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Plane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

namespace CannonFiniteFaces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Plane := EuclideanSpace ℝ (Fin 2)

end CannonFiniteFaces

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_Thin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Thin geodesic triangles and fellow travelling in the Cayley graph. -/

section
section
section
section
section
section
noncomputable section
namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def Thin (G : SimpleGraph V) (δ : ℕ) : Prop :=
  ∀ x y z : V, ∀ p : G.Walk x y, ∀ q : G.Walk y z, ∀ r : G.Walk z x,
    p.length = G.dist x y → q.length = G.dist y z → r.length = G.dist z x →
    ∀ a ∈ p.support, ∃ b ∈ q.support ++ r.support, G.dist a b ≤ δ

lemma start_getVert_dist (hG : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) {k : ℕ} (hk : k ≤ p.length) :
    G.dist x (p.getVert k) = k := by
  have ht := G.dist_le (p.take k)
  have hd := G.dist_le (p.drop k)
  have htri := @Connected.dist_triangle _ G x (p.getVert k) y hG
  rw [Walk.take_length, min_eq_left hk] at ht
  rw [Walk.drop_length] at hd
  omega

lemma getVert_end_dist (hG : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) {k : ℕ} (hk : k ≤ p.length) :
    G.dist (p.getVert k) y = p.length - k := by
  have ht := start_getVert_dist hG p hp hk
  have hd := G.dist_le (p.drop k)
  have htri := @Connected.dist_triangle _ G x (p.getVert k) y hG
  rw [Walk.drop_length] at hd
  omega

lemma getVert_dist_le {x y : V} (p : G.Walk x y) {i j : ℕ} (hij : i ≤ j) :
    G.dist (p.getVert i) (p.getVert j) ≤ j-i := by
  have h := G.dist_le ((p.drop i).take (j-i))
  rw [Walk.take_length, Walk.drop_getVert, Nat.add_sub_of_le hij] at h
  exact h.trans (min_le_left _ _)

lemma of_mem_geodesic (hG : G.Connected) {x y b : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) (hb : b ∈ p.support) :
    G.dist x b + G.dist b y = G.dist x y := by
  classical
  have h₁ := G.dist_le (p.takeUntil b hb)
  have h₂ := G.dist_le (p.dropUntil b hb)
  have h₃ := @Connected.dist_triangle _ G x b y hG
  have he : (p.takeUntil b hb).length + (p.dropUntil b hb).length = p.length := by
    rw [← Walk.length_append]; congr 1; exact p.take_spec hb
  omega

lemma opposite_side_bound (hG : G.Connected) {o x y a b : V}
    (q : G.Walk x y) (hq : q.length = G.dist x y) (hb : b ∈ q.support) :
    G.dist o x + G.dist o y ≤ 2 * G.dist o a + 2 * G.dist a b + G.dist x y := by
  have h₁ := @Connected.dist_triangle _ G o a b hG
  have h₂ := @Connected.dist_triangle _ G o b x hG
  have h₃ := @Connected.dist_triangle _ G o b y hG
  have hb' := of_mem_geodesic hG q hq hb
  rw [SimpleGraph.dist_comm (u := b) (v := x)] at h₂
  omega

lemma synchronous_of_near (hG : G.Connected) {o x y : V}
    (p : G.Walk o x) (q : G.Walk o y)
    (hp : p.length = G.dist o x) (hq : q.length = G.dist o y)
    {k δ : ℕ} (hkp : k ≤ p.length) (_hkq : k ≤ q.length)
    {b : V} (hb : b ∈ q.support) (hab : G.dist (p.getVert k) b ≤ δ) :
    G.dist (p.getVert k) (q.getVert k) ≤ 2*δ := by
  obtain ⟨j,hjb,hj⟩ := Walk.mem_support_iff_exists_getVert.mp hb
  subst b
  have hpk := start_getVert_dist hG p hp hkp
  have hqj := start_getVert_dist hG q hq hj
  have h₁ := @Connected.dist_triangle _ G o (p.getVert k) (q.getVert j) hG
  have h₂ := @Connected.dist_triangle _ G o (q.getVert j) (p.getVert k) hG
  rw [SimpleGraph.dist_comm (u := q.getVert j) (v := p.getVert k)] at h₂
  have hd : G.dist (q.getVert j) (q.getVert k) ≤ δ := by
    rcases le_total j k with hjk | hkj
    · have h := getVert_dist_le q hjk
      omega
    · have h := getVert_dist_le q hkj
      rw [SimpleGraph.dist_comm (u := q.getVert k) (v := q.getVert j)] at h
      omega
  have h₃ := @Connected.dist_triangle _ G (p.getVert k) (q.getVert j) (q.getVert k) hG
  omega

lemma fellow_travel_below_product (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {o x y : V} (p : G.Walk o x) (q : G.Walk o y)
    (hp : p.length = G.dist o x) (hq : q.length = G.dist o y)
    {k : ℕ} (hkp : k ≤ p.length) (hkq : k ≤ q.length)
    (hprod : 2*k + 2*δ + G.dist x y < G.dist o x + G.dist o y) :
    G.dist (p.getVert k) (q.getVert k) ≤ 2*δ := by
  obtain ⟨s,hs⟩ := hG.exists_walk_length_eq_dist x y
  have hqr : q.reverse.length = G.dist y o := by simpa [SimpleGraph.dist_comm] using hq
  obtain ⟨b,hb,hab⟩ := hthin o x y p s q.reverse hp hs hqr
    (p.getVert k) (p.getVert_mem_support k)
  rcases List.mem_append.mp hb with hb | hb
  · have hh := opposite_side_bound hG s hs hb (a := p.getVert k) (o := o)
    rw [start_getVert_dist hG p hp hkp] at hh
    omega
  · apply synchronous_of_near hG p q hp hq hkp hkq _ hab
    simpa using hb

def raySegment (r : ℕ → V) (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j) :
    (n : ℕ) → G.Walk (r 0) (r n)
  | 0 => .nil
  | n+1 => (raySegment r hr n).concat (dist_eq_one_iff_adj.mp (by rw [hr]; simp [Nat.dist]))

@[simp] lemma raySegment_length (r : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j) (n : ℕ) :
    (raySegment r hr n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [raySegment, ih]

lemma raySegment_getVert (r : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j) {n k : ℕ} (hk : k ≤ n) :
    (raySegment r hr n).getVert k = r k := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases hkn : k ≤ n
    · simp only [raySegment, Walk.concat_eq_append, Walk.getVert_append',
        raySegment_length, ite_eq_left hkn]
      exact ih hkn
    · have : k = n+1 := by omega
      subst k
      have h := (raySegment r hr (n+1)).getVert_length
      simpa using h

theorem asymptotic_rays_uniform (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (r s : ℕ → V) (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (hs : ∀ i j, G.dist (s i) (s j) = Nat.dist i j) (h₀ : r 0 = s 0)
    (hbounded : ∃ C : ℕ, ∀ n, G.dist (r n) (s n) ≤ C) :
    ∀ n, G.dist (r n) (s n) ≤ 2*δ := by
  obtain ⟨C,hC⟩ := hbounded
  intro n
  let N := n+δ+C+1
  let p := raySegment r hr N
  let q := (raySegment s hs N).copy h₀.symm rfl
  have hp : p.length = G.dist (r 0) (r N) := by simp [p,hr,Nat.dist]
  have hq : q.length = G.dist (r 0) (s N) := by simp [q,h₀,hs,Nat.dist]
  have hnp : n ≤ p.length := by simp only [p,raySegment_length]; dsimp [N]; omega
  have hnq : n ≤ q.length := by simp only [q,Walk.length_copy,raySegment_length]; dsimp [N]; omega
  have hprod : 2*n+2*δ+G.dist (r N) (s N) < G.dist (r 0) (r N)+G.dist (r 0) (s N) := by
    rw [hr, h₀, hs]
    simp only [Nat.dist_zero_left]
    have := hC N
    dsimp [N] at *
    omega
  have h := fellow_travel_below_product hG hthin p q hp hq hnp hnq hprod
  simpa only [p,q,Walk.getVert_copy, raySegment_getVert r hr (show n ≤ N by dsimp [N]; omega),
    raySegment_getVert s hs (show n ≤ N by dsimp [N]; omega)] using h

end CannonGraph

namespace CannonGraph
open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

lemma finite_short_walk_ends (hfin : ∀ v, (G.neighborSet v).Finite) (o : V) (n : ℕ) :
    {v | ∃ p : G.Walk o v, p.length ≤ n}.Finite := by
  induction n with
  | zero =>
    apply (Set.finite_singleton o).subset
    rintro v ⟨p,hp⟩
    exact Set.mem_singleton_iff.mpr (Walk.eq_of_length_eq_zero (p := p) (by omega)).symm
  | succ n ih =>
    apply ((Set.finite_singleton o).union (ih.biUnion (fun v _ => hfin v))).subset
    rintro v ⟨p,hp⟩
    by_cases hz : p.length = 0
    · exact Or.inl (Walk.eq_of_length_eq_zero hz).symm
    · right
      refine Set.mem_iUnion₂.mpr ⟨p.penultimate, ?_, p.adj_penultimate (by simpa only [← Walk.length_eq_zero_iff] using hz)⟩
      refine ⟨p.dropLast, ?_⟩
      rw [Walk.length_dropLast]
      omega

lemma finite_graph_ball (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite)
    (o : V) (n : ℕ) : {v | G.dist o v ≤ n}.Finite := by
  apply (finite_short_walk_ends hfin o n).subset
  intro v hv
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist o v
  exact ⟨p, hp ▸ hv⟩

lemma finite_cayley_neighbors {M : Type*} [Group M] (S : Finset M) (v : M) :
    ((SimpleGraph.mulCayley (S : Set M)).neighborSet v).Finite := by
  apply ((S.finite_toSet.image (v * ·)).union (S.finite_toSet.image (fun g => v * g⁻¹))).subset
  intro w hw
  obtain ⟨_,g,hg,he⟩ := (SimpleGraph.mulCayley_adj' (S : Set M) v w).mp hw
  rcases he with he | he
  · exact Or.inl ⟨g,hg,he⟩
  · exact Or.inr ⟨g,hg,by rw [he]; simp⟩

theorem compact_ray_space [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite) (o : V) :
    IsCompact {r : ℕ → V | r 0 = o ∧ ∀ i j, G.dist (r i) (r j) = Nat.dist i j} := by
  let A : Set (ℕ → V) := {r | r 0 = o ∧ ∀ i j, G.dist (r i) (r j) = Nat.dist i j}
  have hA : IsClosed A := by
    refine (isClosed_eq (continuous_apply 0) continuous_const).inter ?_
    change IsClosed {r : ℕ → V | ∀ i j, G.dist (r i) (r j) = Nat.dist i j}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    have hp : Continuous (fun r : ℕ → V => (r i, r j)) :=
      (continuous_apply i).prodMk (continuous_apply j)
    exact isClosed_eq ((continuous_of_discreteTopology : Continuous (fun p : V × V => G.dist p.1 p.2)).comp hp) continuous_const
  have hpi : IsCompact {r : ℕ → V | ∀ n, G.dist o (r n) ≤ n} :=
    isCompact_pi_infinite (fun n => (finite_graph_ball hG hfin o n).isCompact)
  apply hpi.of_isClosed_subset hA
  intro r hr n
  rw [← hr.1, hr.2, Nat.dist_zero_left]

end CannonGraph

namespace CannonGraph
open SimpleGraph Set Filter
open scoped Topology

variable {V : Type*} {G : SimpleGraph V}

lemma geodesic_getVert_dist (hG : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = Nat.dist i j := by
  have hai := start_getVert_dist hG p hp hi
  have haj := start_getVert_dist hG p hp hj
  rcases le_total i j with hij | hji
  · have hu := getVert_dist_le p hij
    have hl := @Connected.dist_triangle _ G x (p.getVert i) (p.getVert j) hG
    simp only [Nat.dist_eq_sub_of_le hij]
    omega
  · have hu := getVert_dist_le p hji
    have hl := @Connected.dist_triangle _ G x (p.getVert j) (p.getVert i) hG
    rw [SimpleGraph.dist_comm (u := p.getVert j) (v := p.getVert i)] at hu hl
    simp only [Nat.dist_eq_sub_of_le_right hji]
    omega

lemma different_bases_same_endpoint (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {o b w : V} (p : G.Walk o w) (q : G.Walk b w)
    (hp : p.length = G.dist o w) (hq : q.length = G.dist b w)
    {k : ℕ} (hkp : k ≤ p.length) (hkq : k ≤ q.length) :
    G.dist (p.getVert k) (q.getVert k) ≤ 3 * G.dist o b + 2*δ := by
  obtain ⟨s,hs⟩ := hG.exists_walk_length_eq_dist b o
  have hqr : q.reverse.length = G.dist w b := by simpa [SimpleGraph.dist_comm] using hq
  obtain ⟨z,hz,haz⟩ := hthin o w b p q.reverse s hp hqr hs
    (p.getVert k) (p.getVert_mem_support k)
  have hpk := start_getVert_dist hG p hp hkp
  have hqk := start_getVert_dist hG q hq hkq
  rcases List.mem_append.mp hz with hz | hz
  · have hzq : z ∈ q.support := by simpa using hz
    obtain ⟨j,hjz,hj⟩ := Walk.mem_support_iff_exists_getVert.mp hzq
    subst z
    have hqj := start_getVert_dist hG q hq hj
    have h₁ := @Connected.dist_triangle _ G o b (q.getVert j) hG
    have h₂ := @Connected.dist_triangle _ G o (q.getVert j) (p.getVert k) hG
    have h₃ := @Connected.dist_triangle _ G b o (p.getVert k) hG
    have h₄ := @Connected.dist_triangle _ G b (p.getVert k) (q.getVert j) hG
    rw [SimpleGraph.dist_comm (u := q.getVert j) (v := p.getVert k)] at h₂
    rw [SimpleGraph.dist_comm (u := b) (v := o)] at h₃
    have hd : G.dist (q.getVert j) (q.getVert k) ≤ G.dist o b + δ := by
      rcases le_total j k with hjk | hkj
      · have hh := getVert_dist_le q hjk
        omega
      · have hh := getVert_dist_le q hkj
        rw [SimpleGraph.dist_comm (u := q.getVert k) (v := q.getVert j)] at hh
        omega
    have hh := @Connected.dist_triangle _ G (p.getVert k) (q.getVert j) (q.getVert k) hG
    omega
  · have hz' := of_mem_geodesic hG s hs hz
    have h₁ := @Connected.dist_triangle _ G o z (p.getVert k) hG
    rw [SimpleGraph.dist_comm (u := z) (v := p.getVert k),
      SimpleGraph.dist_comm (u := o) (v := z)] at h₁
    rw [SimpleGraph.dist_comm (u := b) (v := o)] at hz'
    have h₂ := @Connected.dist_triangle _ G (p.getVert k) o b hG
    have h₃ := @Connected.dist_triangle _ G (p.getVert k) b (q.getVert k) hG
    rw [SimpleGraph.dist_comm (u := p.getVert k) (v := o)] at h₂
    omega

theorem exists_rebased_ray [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite)
    {δ : ℕ} (hthin : Thin G δ) (r : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j) (o : V) :
    ∃ s : ℕ → V, s 0 = o ∧
      (∀ i j, G.dist (s i) (s j) = Nat.dist i j) ∧
      ∀ n, G.dist (s n) (r n) ≤ 3 * G.dist o (r 0) + 2*δ := by
  choose p hp using fun n => hG.exists_walk_length_eq_dist o (r n)
  let f : ℕ → ℕ → V := fun N k => (p N).getVert k
  have hfball : ∀ N, f N ∈ {s : ℕ → V | ∀ n, G.dist o (s n) ≤ n} := by
    intro N n
    have hh := G.dist_le ((p N).take n)
    rw [Walk.take_length] at hh
    exact hh.trans (min_le_left _ _)
  have hbox : IsCompact {s : ℕ → V | ∀ n, G.dist o (s n) ≤ n} :=
    isCompact_pi_infinite (fun n => (finite_graph_ball hG hfin o n).isCompact)
  obtain ⟨s,hs,φ,hφ,ht⟩ := hbox.tendsto_subseq hfball
  have hlength : ∀ N k, k + G.dist o (r 0) ≤ N → k ≤ (p N).length := by
    intro N k hNk
    have hh := @Connected.dist_triangle _ G (r 0) o (r N) hG
    rw [hr, Nat.dist_zero_left, SimpleGraph.dist_comm (u := r 0) (v := o), ← hp N] at hh
    omega
  have hstart : s 0 = o := by
    have hclosed : IsClosed {s : ℕ → V | s 0 = o} :=
      isClosed_eq (continuous_apply 0) continuous_const
    apply hclosed.mem_of_tendsto ht
    exact Filter.Eventually.of_forall (fun n => by simp [f])
  refine ⟨s,hstart,?_,?_⟩
  · intro i j
    have hclosed : IsClosed {s : ℕ → V | G.dist (s i) (s j) = Nat.dist i j} := by
      exact (isClosed_discrete {n : ℕ | n = Nat.dist i j}).preimage
        ((continuous_of_discreteTopology : Continuous (fun p : V × V => G.dist p.1 p.2)).comp
          ((continuous_apply i : Continuous (fun s : ℕ → V => s i)).prodMk
            (continuous_apply j : Continuous (fun s : ℕ → V => s j))))
    apply hclosed.mem_of_tendsto ht
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop (max i j + G.dist o (r 0))] with N hN
    exact geodesic_getVert_dist hG (p (φ N)) (hp (φ N))
      (hlength _ _ (by omega)) (hlength _ _ (by omega))
  · intro k
    have hclosed : IsClosed {s : ℕ → V | G.dist (s k) (r k) ≤ 3 * G.dist o (r 0) + 2*δ} := by
      exact (isClosed_discrete {n : ℕ | n ≤ 3 * G.dist o (r 0) + 2*δ}).preimage
        ((continuous_of_discreteTopology : Continuous (fun v : V => G.dist v (r k))).comp
          (continuous_apply k))
    apply hclosed.mem_of_tendsto ht
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop (k + G.dist o (r 0))] with N hN
    have hNk : k ≤ φ N := by omega
    have hh := different_bases_same_endpoint hG hthin (p (φ N)) (raySegment r hr (φ N))
      (hp (φ N)) (by simp [hr, Nat.dist]) (hlength _ _ hN)
      (by simpa only [raySegment_length] using hNk)
    simpa only [Function.comp_apply, f, raySegment_getVert r hr hNk] using hh

end CannonGraph

noncomputable section
open Set Topology

namespace CannonBoundary

lemma quotient_closedMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (s : Setoid X) (hs : IsClosed {p : X × X | s.r p.1 p.2}) :
    IsClosedMap (@Quotient.mk' X s) := by
  intro F hF
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  have h := isClosedMap_fst_of_compactSpace (X := X) (Y := X)
    _ (hs.inter (isClosed_univ.prod hF))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · rintro ⟨y,hy,hxy⟩
    refine ⟨(x,y),⟨?_,⟨trivial,hy⟩⟩,rfl⟩
    exact s.symm (Quotient.exact hxy)
  · rintro ⟨⟨x',y⟩,⟨hxy,_,hy⟩,rfl⟩
    exact ⟨y,hy,Quotient.sound (s.symm hxy)⟩

theorem quotient_t2_of_closed {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (s : Setoid X) (hs : IsClosed {p : X × X | s.r p.1 p.2}) :
    T2Space (Quotient s) := by
  have hcont : Continuous (@Quotient.mk' X s) := continuous_quotient_mk'
  have hcl := quotient_closedMap s hs
  have hfib : ∀ y : Quotient s, IsCompact ((@Quotient.mk' X s) ⁻¹' {y}) := by
    intro y
    induction y using Quotient.inductionOn with
    | h x =>
      have h : IsClosed {z : X | s.r x z} := hs.preimage (continuous_const.prodMk continuous_id)
      convert h.isCompact using 1
      all_goals try with_reducible_and_instances rfl
      ext z
      simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
      exact ⟨fun hz => s.symm (Quotient.exact hz), fun hz => Quotient.sound (s.symm hz)⟩
  have hproper := isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hcont,hcl,hfib⟩
  apply t2_iff_isClosed_diagonal.mpr
  have hh := hproper.prodMap hproper
  have he : Set.diagonal (Quotient s) =
      Prod.map (@Quotient.mk' X s) (@Quotient.mk' X s) '' {p : X × X | s.r p.1 p.2} := by
    ext p
    constructor
    · intro hp
      obtain ⟨x,hx⟩ := Quotient.mk'_surjective p.1
      refine ⟨(x,x),s.refl x,?_⟩
      apply Prod.ext
      · exact hx
      · exact hx.trans (Set.mem_diagonal_iff.mp hp)
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact Quotient.sound hxy
  rw [he]
  exact hh.isClosedMap _ hs

end CannonBoundary

noncomputable section

namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma iso_dist (hG : G.Connected) (e : G ≃g G) (x y : V) :
    G.dist (e x) (e y) = G.dist x y := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist x y
    simpa [hp] using G.dist_le (p.map e.toHom)
  · obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist (e x) (e y)
    simpa [hp] using G.dist_le (p.map e.symm.toHom)

theorem asymptotic_rays_different_bases_uniform
    [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite)
    {δ : ℕ} (hthin : Thin G δ) (r s : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (hs : ∀ i j, G.dist (s i) (s j) = Nat.dist i j)
    (hbounded : ∃ C : ℕ, ∀ n, G.dist (r n) (s n) ≤ C) :
    ∀ n, G.dist (r n) (s n) ≤ 3 * G.dist (r 0) (s 0) + 4*δ := by
  obtain ⟨t,ht₀,ht,hts⟩ := exists_rebased_ray hG hfin hthin s hs (r 0)
  obtain ⟨C,hC⟩ := hbounded
  have hrt : ∃ C : ℕ, ∀ n, G.dist (r n) (t n) ≤ C := by
    refine ⟨C + (3 * G.dist (r 0) (s 0) + 2*δ), fun n => ?_⟩
    have h := @Connected.dist_triangle _ G (r n) (s n) (t n) hG
    rw [SimpleGraph.dist_comm (u := s n) (v := t n)] at h
    exact h.trans (Nat.add_le_add (hC n) (hts n))
  have hrt' := asymptotic_rays_uniform hG hthin r t hr ht ht₀.symm hrt
  intro n
  have h := @Connected.dist_triangle _ G (r n) (t n) (s n) hG
  have := hrt' n
  have := hts n
  omega
end CannonGraph

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryHomeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def product2 (o x y : V) : ℕ := G.dist o x + G.dist o y - G.dist x y

lemma product2_add_dist (hG : G.Connected) (o x y : V) :
    product2 (G := G) o x y + G.dist x y = G.dist o x + G.dist o y := by
  apply Nat.sub_add_cancel
  have := @Connected.dist_triangle _ G x o y hG
  rwa [SimpleGraph.dist_comm (u := x) (v := o)] at this

lemma product2_le_twice_left (hG : G.Connected) (o x y : V) :
    product2 (G := G) o x y ≤ 2*G.dist o x := by
  have h := product2_add_dist hG o x y
  have h' := @Connected.dist_triangle _ G o x y hG
  omega

lemma product2_comm (o x y : V) : product2 (G := G) o x y = product2 (G := G) o y x := by
  simp only [product2, SimpleGraph.dist_comm (u := x) (v := y), Nat.add_comm]

lemma product2_le_twice_right (hG : G.Connected) (o x y : V) :
    product2 (G := G) o x y ≤ 2*G.dist o y := by
  rw [product2_comm]
  exact product2_le_twice_left hG o y x

theorem product2_hyperbolic (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (o x y z : V) :
    min (product2 (G := G) o x y) (product2 (G := G) o y z) ≤
      product2 (G := G) o x z + 8*δ+6 := by
  let m := min (product2 (G := G) o x y) (product2 (G := G) o y z)
  by_cases hm : m ≤ 2*δ+2
  · change m ≤ _
    omega
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist o x
  obtain ⟨q,hq⟩ := hG.exists_walk_length_eq_dist o y
  obtain ⟨r,hr⟩ := hG.exists_walk_length_eq_dist o z
  let k := m/2-δ-1
  have hm₁ : m ≤ product2 (G := G) o x y := min_le_left _ _
  have hm₂ : m ≤ product2 (G := G) o y z := min_le_right _ _
  have hk : 2*k+2*δ < m := by dsimp [k]; omega
  have hkp : k ≤ p.length := by
    have := product2_le_twice_left hG o x y
    dsimp [k]; omega
  have hkq : k ≤ q.length := by
    have := product2_le_twice_right hG o x y
    dsimp [k]; omega
  have hkr : k ≤ r.length := by
    have := product2_le_twice_right hG o y z
    dsimp [k]; omega
  have hxy := product2_add_dist hG o x y
  have hyz := product2_add_dist hG o y z
  have h₁ := fellow_travel_below_product hG hthin p q hp hq hkp hkq (by omega)
  have h₂ := fellow_travel_below_product hG hthin q r hq hr hkq hkr (by omega)
  have hpx := getVert_end_dist hG p hp hkp
  have hrz := getVert_end_dist hG r hr hkr
  have h₃ := @Connected.dist_triangle _ G (p.getVert k) (q.getVert k) (r.getVert k) hG
  have h₄ := @Connected.dist_triangle _ G x (p.getVert k) (r.getVert k) hG
  have h₅ := @Connected.dist_triangle _ G x (r.getVert k) z hG
  rw [SimpleGraph.dist_comm (u := x) (v := p.getVert k)] at h₄
  have hxz := product2_add_dist hG o x z
  change m ≤ _
  dsimp [k] at *
  omega

lemma product2_ray_mono (hG : G.Connected) (r s : ℕ → V)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (hs : ∀ i j, G.dist (s i) (s j) = Nat.dist i j) (h₀ : r 0 = s 0) :
    Monotone (fun n => product2 (G := G) (r 0) (r n) (s n)) := by
  intro i j hij
  have h₁ := @Connected.dist_triangle _ G (r j) (r i) (s i) hG
  have h₂ := @Connected.dist_triangle _ G (r j) (s i) (s j) hG
  rw [hr] at h₁
  rw [hs] at h₂
  have hi := product2_add_dist hG (r 0) (r i) (s i)
  have hj := product2_add_dist hG (r 0) (r j) (s j)
  have hi₀ : G.dist (r 0) (s i) = i := by
    simpa only [h₀, Nat.dist_zero_left] using hs 0 i
  have hj₀ : G.dist (r 0) (s j) = j := by
    simpa only [h₀, Nat.dist_zero_left] using hs 0 j
  rw [hr, hi₀] at hi
  rw [hr, hj₀] at hj
  simp only [Nat.dist_zero_left, Nat.dist_eq_sub_of_le hij,
    Nat.dist_eq_sub_of_le_right hij] at *
  omega

end CannonGraph

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_WordBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
noncomputable section

noncomputable section
open Set Topology

noncomputable section

namespace CannonGraph
open SimpleGraph

variable {M : Type*} [Group M]

noncomputable def wordBall (S : Finset M) : ℕ → Finset M := by
  classical
  exact fun n => Nat.rec {1} (fun _ t => t.biUnion (fun x => (insert 1 S).image (x*·))) n

end CannonGraph

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_IncidentEdges
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonEmbeddedArc
open Set Metric unitInterval
open scoped BigOperators

namespace Arc
variable {X : Type*} [MetricSpace X]

noncomputable def incidentEdges {ι : Type*} [Fintype ι] (E : ι → Arc X) (a : Arc X) : Finset ι := by
  classical
  exact Finset.univ.filter (fun e => (range a ∩ range (E e)).Nonempty)

def stageBound (M : ℕ) : ℕ := M*(2*M+4)^2+(2*M+2)^2

end Arc
end CannonEmbeddedArc

namespace CannonEmbeddedArc
namespace Arc
open Set Metric

variable {X : Type*} [MetricSpace X]

def colorBound : ℕ → ℕ
  | 0 => 0
  | n+1 => stageBound (colorBound n)

end Arc
end CannonEmbeddedArc

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_Glue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonClosedGluing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {κ : Type*} [Finite κ]

def glue (S : κ → Set X) (hS : ∀ i, IsClosed (S i)) (hcover : ⋃ i, S i=univ)
    (f : ∀ i, C(S i,Y))
    (heq : ∀ i j x (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩) : C(X,Y) :=
  ⟨Set.liftCover S (fun i => f i) heq hcover,
    (locallyFinite_of_finite S).continuous hcover hS (fun i => by
      rw [continuousOn_iff_continuous_domRestrict]
      simpa +unfoldPartialApp only [Set.domRestrict,Set.liftCover_coe] using (f i).continuous)⟩

@[simp] lemma glue_apply (S : κ → Set X) (hS : ∀ i, IsClosed (S i)) (hcover : ⋃ i, S i=univ)
    (f : ∀ i, C(S i,Y))
    (heq : ∀ i j x (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩)
    (i : κ) (x : S i) : glue S hS hcover f heq x = f i x :=
  by
    change Set.liftCover S (fun i => f i) heq hcover x=f i x
    exact Set.liftCover_coe x

end CannonClosedGluing

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_SquareSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section

namespace CannonGrid
open Set Metric Topology unitInterval

variable {X : Type*} [TopologicalSpace X]

def point (n : ℕ) (hn : 0<n) (i : Fin (n+1)) : I :=
  ⟨(i:ℝ)/n,div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩

def strip (n : ℕ) (i : Fin n) : Set (I×I) :=
  {z | (i:ℝ)≤n*(z.2:ℝ) ∧ n*(z.2:ℝ)≤(i:ℝ)+1}

lemma strip_closed (n : ℕ) (i : Fin n) : IsClosed (strip n i) := by
  change IsClosed ({z : I×I | (i:ℝ)≤n*(z.2:ℝ)} ∩ {z : I×I | n*(z.2:ℝ)≤(i:ℝ)+1})
  exact (isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le (by fun_prop) continuous_const)

lemma strip_cover (n : ℕ) (hn : 0<n) : ⋃ i, strip n i=univ := by
  ext z
  simp only [mem_iUnion,mem_univ,iff_true]
  have ht : 0≤(n:ℝ)*(z.2:ℝ) := mul_nonneg (Nat.cast_nonneg _) z.2.property.1
  let i := min ⌊(n:ℝ)*(z.2:ℝ)⌋₊ (n-1)
  have hi : i<n := (min_le_right ..).trans_lt (by omega)
  refine ⟨⟨i,hi⟩,?_,?_⟩
  · exact (Nat.cast_le.mpr (min_le_left ..)).trans (Nat.floor_le ht)
  · by_cases h : ⌊(n:ℝ)*(z.2:ℝ)⌋₊≤n-1
    · simpa [i,min_eq_left h] using (Nat.lt_floor_add_one ((n:ℝ)*(z.2:ℝ))).le
    · have hin : i=n-1 := min_eq_right (le_of_not_ge h)
      have hn' : ((n-1:ℕ):ℝ)+1=n := by norm_cast; omega
      change (n:ℝ)*(z.2:ℝ)≤(i:ℝ)+1
      rw [hin,hn']
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) z.2.property.2

def coordinate (n : ℕ) (i : Fin n) : C(strip n i,I) :=
  ⟨fun z => ⟨n*(z.val.2:ℝ)-(i:ℝ),by
      have h := z.property
      exact ⟨sub_nonneg.mpr h.1,by linarith [h.2]⟩⟩,by fun_prop⟩

def patch (n : ℕ) (i : Fin n) (F : C(I×I,X)) : C(strip n i,X) :=
  F.comp ⟨fun z => (z.val.1,coordinate n i z),by fun_prop⟩

lemma strip_overlap {n : ℕ} {i j : Fin n} (hij : i<j) {z : I×I}
    (hi : z∈strip n i) (hj : z∈strip n j) :
    (i:ℕ)+1=(j:ℕ) ∧ (n:ℝ)*(z.2:ℝ)=(j:ℝ) := by
  have hij' : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast hij
  have heq : (i:ℝ)+1=(j:ℝ) := le_antisymm hij' (hj.1.trans hi.2)
  constructor
  · exact_mod_cast heq
  · exact le_antisymm (hi.2.trans heq.le) hj.1

lemma patch_agree (n : ℕ) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0)) :
    ∀ i j z (hi : z∈strip n i) (hj : z∈strip n j),
      patch n i (F i) ⟨z,hi⟩=patch n j (F j) ⟨z,hj⟩ := by
  intro i j z hi hj
  rcases lt_trichotomy i j with hij|rfl|hji
  · obtain ⟨hij',hz⟩ := strip_overlap hij hi hj
    have hci : coordinate n i ⟨z,hi⟩=1 := by
      apply Subtype.ext
      change (n:ℝ)*(z.2:ℝ)-(i:ℝ)=1
      rw [hz]; have hcast : (i:ℝ)+1=(j:ℝ) := by exact_mod_cast hij'
      linarith
    have hcj : coordinate n j ⟨z,hj⟩=0 := by
      apply Subtype.ext; change (n:ℝ)*(z.2:ℝ)-(j:ℝ)=0; rw [hz,sub_self]
    simpa only [patch,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hci,hcj] using hF i j hij' z.1
  · rfl
  · obtain ⟨hji',hz⟩ := strip_overlap hji hj hi
    have hcj : coordinate n j ⟨z,hj⟩=1 := by
      apply Subtype.ext
      change (n:ℝ)*(z.2:ℝ)-(j:ℝ)=1
      rw [hz]; have hcast : (j:ℝ)+1=(i:ℝ) := by exact_mod_cast hji'
      linarith
    have hci : coordinate n i ⟨z,hi⟩=0 := by
      apply Subtype.ext; change (n:ℝ)*(z.2:ℝ)-(i:ℝ)=0; rw [hz,sub_self]
    simpa only [patch,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hci,hcj] using (hF j i hji' z.1).symm

def glue (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0)) : C(I×I,X) :=
  CannonClosedGluing.glue (strip n) (strip_closed n) (strip_cover n hn)
    (fun i => patch n i (F i)) (patch_agree n F hF)

def parameter (n : ℕ) (hn : 0<n) (i : Fin n) : C(I,I) :=
  ⟨fun t => ⟨((i:ℝ)+(t:ℝ))/n,div_nonneg (add_nonneg (Nat.cast_nonneg _) t.property.1) (Nat.cast_nonneg _),
      (div_le_one (by exact_mod_cast hn)).mpr (by
        have hi : (i:ℝ)+1≤n := by exact_mod_cast i.isLt
        linarith [t.property.2])⟩,by fun_prop⟩

@[simp] lemma parameter_zero (n : ℕ) (hn : 0<n) (i : Fin n) :
    parameter n hn i 0=point n hn i.castSucc := by ext; simp [parameter,point]
@[simp] lemma parameter_one (n : ℕ) (hn : 0<n) (i : Fin n) :
    parameter n hn i 1=point n hn i.succ := by ext; simp [parameter,point]

end CannonGrid

namespace CannonGrid
open Set Metric Topology unitInterval

variable {X : Type*} [TopologicalSpace X]

@[simp] lemma point_zero (n : ℕ) (hn : 0<n) : point n hn 0=0 := by ext; simp [point]
@[simp] lemma point_last (n : ℕ) (hn : 0<n) : point n hn (Fin.last n)=1 := by
  ext; simp [point,ne_of_gt hn]

end CannonGrid

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_ChartLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonFaceIncidence
open Set Topology

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]
variable {Y : Type*} [TopologicalSpace Y]
def chartLabel (e : Y → X) {V : Set X} (π : V → D) : (e ⁻¹' V) → D :=
  fun x => π ⟨e x.val,x.property⟩

end CannonFaceIncidence

namespace CannonFaceIncidence
open Set Topology

variable {X Y D : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace D] [DiscreteTopology D]

def labelPull (e : Y → X) {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V)
    (π : V → D) : W → D := chartLabel e π ∘ (Homeomorph.setCongr hW)

end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_TraceCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

namespace CannonIncidence
open Set Metric

variable {X ι : Type*} [MetricSpace X] [Fintype ι]

noncomputable def traceCard (E : ι → Set X) (S : Set X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => (E i∩S).Nonempty)).card

end CannonIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Weights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
open scoped InnerProductSpace
open Set

namespace CannonDuality

variable {ι : Type*} [Fintype ι]
abbrev Weights (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

def Nonnegative (w : Weights ι) : Prop := ∀ i, 0 ≤ w i

def Admissible (V : Set (Weights ι)) (w : Weights ι) : Prop :=
  Nonnegative w ∧ ∀ v ∈ V, 1 ≤ ⟪w, v⟫_ℝ

def Modulus (V : Set (Weights ι)) : ℝ :=
  sInf {e : ℝ | ∃ w : Weights ι, Admissible V w ∧ e = ‖w‖ ^ 2}

end CannonDuality

namespace CannonCells
open Set CannonDuality
open scoped InnerProductSpace

variable {X ι : Type*} [Fintype ι]

noncomputable def indices (C : ι → Set X) (A : Set X) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (A ∩ C i).Nonempty)

noncomputable def weight (s : Finset ι) : Weights ι := by
  classical
  exact WithLp.toLp 2 (fun i => if i ∈ s then (1:ℝ) else 0)

noncomputable def incidence (C : ι → Set X) (A : Set X) : Weights ι :=
  weight (indices C A)

noncomputable def familyVectors (C : ι → Set X) (F : Set (Set X)) : Finset (Weights ι) :=
  ((Set.toFinite (indices C '' F)).toFinset).image weight

lemma mem_indices (C : ι → Set X) (A : Set X) (i : ι) :
    i ∈ indices C A ↔ (A ∩ C i).Nonempty := by
  classical
  simp [indices]

noncomputable def modulus (C : ι → Set X) (F : Set (Set X)) : ℝ :=
  Modulus (familyVectors C F : Set (Weights ι))

end CannonCells
end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Quad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonGeneralizedDisk
open Set Metric
open scoped ComplexConjugate OnePoint

structure Quad where
  A : ℝ
  b : ℂ
  C : ℝ

def Quad.value (q : Quad) (z : ℂ) : ℝ :=
  q.A*Complex.normSq z-2*(conj q.b*z).re+q.C

def Quad.discr (q : Quad) : ℝ := Complex.normSq q.b-q.A*q.C

def Quad.region (q : Quad) : Set (OnePoint ℂ) :=
  {p | p.elim (q.A<0) (fun z=>q.value z<0)}

@[simp] lemma Quad.mem_region_coe (q : Quad) (z : ℂ) :
    (z : OnePoint ℂ)∈q.region ↔ q.value z<0 := Iff.rfl
@[simp] lemma Quad.mem_region_infty (q : Quad) :
    ∞∈q.region ↔ q.A<0 := Iff.rfl

def Quad.affine (q : Quad) (a b : ℂ) : Quad :=
  ⟨q.A,(q.A:ℂ)*b+a*q.b,
    q.A*Complex.normSq b+2*(conj (a*q.b)*b).re+q.C*Complex.normSq a⟩

def Quad.inv (q : Quad) : Quad := ⟨q.C,conj q.b,q.A⟩

def disk (a : ℂ) (r : ℝ) : Quad := ⟨1,a,Complex.normSq a-r^2⟩

end CannonGeneralizedDisk

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Clip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
section
section

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

def clip (a b x : ℝ) : ℝ := max a (min b x)

end CannonCapacity

end

section

section

open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonAnnular

theorem radial_subinterval (g : I → ℝ) (hg : Continuous g)
    (r s : ℝ) (hrs : r < s) (hzero : g 0 ≤ r) (hone : s ≤ g 1) :
    ∃ a b : I, a < b ∧ g a = r ∧ g b = s ∧
      ∀ t ∈ Icc a b, g t ∈ Icc r s := by
  have hnon : (g ⁻¹' {s}).Nonempty := by
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (show (0:I) ≤ 1 from zero_le)
      hg.continuousOn ⟨hzero.trans hrs.le, hone⟩
    exact ⟨t, ht⟩
  have hc : IsCompact (g ⁻¹' {s}) := (isClosed_singleton.preimage hg).isCompact
  obtain ⟨b, hb, hbmin⟩ := hc.exists_isMinOn hnon continuous_id.continuousOn
  have hgb : g b = s := hb
  have hnonr : (Icc (0:I) b ∩ g ⁻¹' {r}).Nonempty := by
    obtain ⟨t, ht, htr⟩ := intermediate_value_Icc (show (0:I) ≤ b from zero_le) hg.continuousOn
      ⟨hzero, hgb ▸ hrs.le⟩
    exact ⟨t, ht, htr⟩
  have hcr : IsCompact (Icc (0:I) b ∩ g ⁻¹' {r}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hg)
  obtain ⟨a, ha, hamax⟩ := hcr.exists_isMaxOn hnonr continuous_id.continuousOn
  have hga : g a = r := ha.2
  have hab : a < b := lt_of_le_of_ne ha.1.2 (by intro he; rw [he, hgb] at hga; exact hrs.ne hga.symm)
  refine ⟨a, b, hab, hga, hgb, ?_⟩
  intro t ht
  constructor
  · by_contra hn
    have hlt : g t < r := lt_of_not_ge hn
    obtain ⟨z, hz, hzr⟩ := intermediate_value_Icc ht.2 hg.continuousOn
      ⟨hlt.le, hgb ▸ hrs.le⟩
    have hza : z ≤ a := hamax ⟨⟨zero_le, hz.2⟩, hzr⟩
    have htz : t < z := lt_of_le_of_ne hz.1 (by intro he; rw [← he] at hzr; exact hlt.ne hzr)
    exact (not_lt_of_ge (hza.trans ht.1)) htz
  · by_contra hn
    have hlt : s < g t := lt_of_not_ge hn
    obtain ⟨z, hz, hzs⟩ := intermediate_value_Icc (show (0:I) ≤ t from zero_le) hg.continuousOn
      ⟨hzero.trans hrs.le, hlt.le⟩
    have hbz : b ≤ z := hbmin hzs
    have hzt : z < t := lt_of_le_of_ne hz.2 (by intro he; rw [he] at hzs; exact hlt.ne' hzs)
    exact (not_lt_of_ge (ht.2.trans hbz)) hzt

end CannonAnnular

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace

namespace CannonCells

open Set

variable {X ι : Type*} [Fintype ι]

noncomputable def cost (C : ι → Set X) (w : ι → ℝ) (A : Set X) : ℝ :=
  ∑ i ∈ indices C A, w i

lemma cost_nonneg (C : ι → Set X) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (A : Set X) :
    0 ≤ cost C w A := Finset.sum_nonneg (fun i _ => hw i)

lemma indices_mono (C : ι → Set X) {A B : Set X} (h : A ⊆ B) : indices C A ⊆ indices C B := by
  intro i hi
  obtain ⟨x,hx,hxi⟩ := (mem_indices C A i).mp hi
  exact (mem_indices C B i).mpr ⟨x,h hx,hxi⟩

lemma cost_mono (C : ι → Set X) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {A B : Set X} (h : A ⊆ B) : cost C w A ≤ cost C w B := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (indices_mono C h) (fun i _ _ => hw i)

lemma indices_union [DecidableEq ι] (C : ι → Set X) (A B : Set X) :
    indices C (A ∪ B) = indices C A ∪ indices C B := by
  classical
  ext i
  simp only [mem_indices,Finset.mem_union,union_inter_distrib_right,union_nonempty]

lemma cost_union_le (C : ι → Set X) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (A B : Set X) :
    cost C w (A ∪ B) ≤ cost C w A + cost C w B := by
  classical
  unfold cost
  rw [indices_union]
  have h := Finset.sum_union_inter (s₁ := indices C A) (s₂ := indices C B) (f := w)
  have hn : 0 ≤ ∑ i ∈ indices C A ∩ indices C B, w i :=
    Finset.sum_nonneg (fun i _ => hw i)
  linarith

end CannonCells

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_PathCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace

namespace CannonPotential

open Set CannonCells

variable {X ι : Type*} [TopologicalSpace X] [PathConnectedSpace X] [Fintype ι]

variable (C : ι → Set X) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)

def pathCosts (A : Set X) (x : X) : Set ℝ :=
  {c | ∃ a ∈ A, ∃ p : Path a x, cost C w (range p) = c}

noncomputable def distanceFrom (A : Set X) (x : X) : ℝ := sInf (pathCosts C w A x)

lemma pathCosts_nonempty {A : Set X} (hA : A.Nonempty) (x : X) :
    (pathCosts C w A x).Nonempty := by
  obtain ⟨a,ha⟩ := hA
  let p := PathConnectedSpace.somePath a x
  exact ⟨cost C w (range p),a,ha,p,rfl⟩

include hw

omit [PathConnectedSpace X] in
lemma pathCosts_bddBelow (A : Set X) (x : X) : BddBelow (pathCosts C w A x) := by
  refine ⟨0,?_⟩
  rintro c ⟨a,ha,p,rfl⟩
  exact cost_nonneg C hw _

lemma distanceFrom_nonneg {A : Set X} (hA : A.Nonempty) (x : X) :
    0 ≤ distanceFrom C w A x := by
  apply le_csInf (pathCosts_nonempty C w hA x)
  rintro c ⟨a,ha,p,rfl⟩
  exact cost_nonneg C hw _

omit [PathConnectedSpace X] in
lemma distanceFrom_le_path {A : Set X} {a x : X} (ha : a ∈ A) (p : Path a x) :
    distanceFrom C w A x ≤ cost C w (range p) :=
  csInf_le (pathCosts_bddBelow C w hw A x) ⟨a,ha,p,rfl⟩

lemma distanceFrom_triangle {A : Set X} (hA : A.Nonempty) {x y : X} (p : Path x y) :
    distanceFrom C w A y ≤ distanceFrom C w A x + cost C w (range p) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  have hc : distanceFrom C w A x < b - cost C w (range p) := by linarith
  obtain ⟨c,⟨a,ha,q,rfl⟩,hc⟩ :=
    (csInf_lt_iff (pathCosts_bddBelow C w hw A x) (pathCosts_nonempty C w hA x)).mp hc
  have h₁ := distanceFrom_le_path C w hw ha (q.trans p)
  rw [Path.trans_range] at h₁
  have h₂ := cost_union_le C hw (range q) (range p)
  linarith

noncomputable def raw (A : Set X) (x : X) : ℝ := by
  classical
  exact if x ∈ A then 0 else min 1 (distanceFrom C w A x)

omit hw [PathConnectedSpace X] in
lemma raw_on_top {A : Set X} {x : X} (hx : x ∈ A) : raw C w A x = 0 := by
  classical
  simp [raw,hx]

lemma raw_bounds {A : Set X} (hA : A.Nonempty) (x : X) : raw C w A x ∈ Icc 0 1 := by
  classical
  by_cases hx : x ∈ A
  · simp [raw,hx]
  · simp only [raw,ite_eq_right hx,mem_Icc]
    exact ⟨le_min zero_le_one (distanceFrom_nonneg C w hw hA x),min_le_left _ _⟩

lemma raw_le_add_cost {A : Set X} (hA : A.Nonempty) {x y : X} (p : Path x y) :
    raw C w A y ≤ raw C w A x + cost C w (range p) := by
  classical
  have hn := cost_nonneg C hw (range p)
  by_cases hy : y ∈ A
  · rw [raw_on_top C w hy]
    exact add_nonneg (raw_bounds C w hw hA x).1 hn
  by_cases hx : x ∈ A
  · rw [raw_on_top C w hx,zero_add]
    simp only [raw,ite_eq_right hy]
    exact (min_le_right _ _).trans (distanceFrom_le_path C w hw hx p)
  simp only [raw,ite_eq_right hx,ite_eq_right hy]
  have ht := distanceFrom_triangle C w hw hA p
  by_cases hb : distanceFrom C w A x ≤ 1
  · rw [min_eq_right hb]
    exact (min_le_right _ _).trans ht
  · rw [min_eq_left (le_of_not_ge hb)]
    exact (min_le_left _ _).trans (by linarith)

theorem raw_path_variation {A : Set X} (hA : A.Nonempty) {x y : X} (p : Path x y) :
    |raw C w A x - raw C w A y| ≤ cost C w (range p) := by
  have h₁ := raw_le_add_cost C w hw hA p
  have h₂ := raw_le_add_cost C w hw hA p.symm
  rw [Path.symm_range] at h₂
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

omit hw in
lemma raw_on_bottom {A B : Set X} (hA : A.Nonempty) (hAB : Disjoint A B)
    (hadm : ∀ a ∈ A, ∀ b ∈ B, ∀ p : Path a b, 1 ≤ cost C w (range p))
    {b : X} (hb : b ∈ B) : raw C w A b = 1 := by
  classical
  have hba : b ∉ A := fun ha => Set.disjoint_left.mp hAB ha hb
  simp only [raw,ite_eq_right hba]
  apply min_eq_left
  apply le_csInf (pathCosts_nonempty C w hA b)
  rintro c ⟨a,ha,p,rfl⟩
  exact hadm a ha b hb p

end CannonPotential

open Set unitInterval

namespace CannonBands

open Set unitInterval

variable {X : Type*} [TopologicalSpace X]

lemma last_level_suffix (g : I → ℝ) (hg : Continuous g) (a : ℝ)
    (hne : ∃ t, g t = a) (hone : a ≤ g 1) :
    ∃ s : I, g s = a ∧ ∀ t, s ≤ t → a ≤ g t := by
  have hK : IsCompact (g ⁻¹' {a}) := (isClosed_singleton.preimage hg).isCompact
  obtain ⟨s,hs,hmax⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
  refine ⟨s,hs,?_⟩
  intro t ht
  by_contra hn
  have hlt := lt_of_not_ge hn
  obtain ⟨z,hz,hza⟩ := intermediate_value_Icc (show t ≤ (1:I) from t.property.2)
    hg.continuousOn ⟨hlt.le,hone⟩
  have hzs : z ≤ s := hmax hza
  have hst : s < t := lt_of_le_of_ne ht (by intro he; rw [← he,hs] at hlt; exact lt_irrefl _ hlt)
  exact (not_lt_of_ge hzs) (hst.trans_le hz.1)

lemma value_le_cost_of_top
    (g : X → ℝ) (hg : Continuous g) (a b : ℝ)
    (f : X → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hTop : ∀ x, g x ≤ a → f x = 0)
    (c : Set X → ℝ) (hc0 : ∀ S, 0 ≤ c S)
    (hcmono : ∀ S T, S ⊆ T → c S ≤ c T)
    (hcore : ∀ u v : X, ∀ p : Path u v,
      (∀ t, g (p t) ∈ Icc a b) → |f u-f v| ≤ c (range p))
    {u v : X} (p : Path u v) (hup : ∀ t, g (p t) ≤ b)
    (htop : ∃ t, g (p t) ≤ a) (t : I) : f (p t) ≤ c (range p) := by
  by_cases ht : g (p t) ≤ a
  · rw [hTop _ ht]
    exact hc0 _
  obtain ⟨s,hs⟩ := htop
  let q := p.subpath s t
  have hstart : g (q 0) ≤ a := by simpa [q] using hs
  have hend : a ≤ g (q 1) := by simpa [q] using le_of_not_ge ht
  have hne : ∃ z, g (q z) = a := by
    obtain ⟨z,_,hz⟩ := intermediate_value_Icc (show (0:I) ≤ 1 from zero_le)
      (hg.comp q.continuous).continuousOn ⟨hstart,hend⟩
    exact ⟨z,hz⟩
  obtain ⟨s',hs',hafter⟩ := last_level_suffix (fun z => g (q z))
    (hg.comp q.continuous) a hne hend
  have hqr : range q ⊆ range p := by
    rw [show range q = p '' uIcc s t from Path.range_subpath p s t]
    exact image_subset_range _ _
  have hq'r : range (q.subpath s' 1) ⊆ range q := by
    rw [Path.range_subpath]
    exact image_subset_range _ _
  have hq := hcore (q s') (q 1) (q.subpath s' 1) (by
    intro z
    have hz : (q.subpath s' 1) z ∈ range (q.subpath s' 1) := mem_range_self z
    rw [Path.range_subpath_of_le _ _ _ (show s' ≤ (1:I) from s'.property.2)] at hz
    obtain ⟨w,hw,hwz⟩ := hz
    rw [← hwz]
    refine ⟨hafter w hw.1,?_⟩
    obtain ⟨z,hz⟩ := hqr (mem_range_self w)
    rw [← hz]
    exact hup z)
  rw [hTop _ hs'.le,zero_sub,abs_neg,abs_of_nonneg (hf0 _)] at hq
  have hh := hq.trans (hcmono _ _ (hq'r.trans hqr))
  simpa [q] using hh

theorem extended_path_variation
    (g : X → ℝ) (hg : Continuous g) (a b : ℝ) (hab : a < b)
    (f : X → ℝ) (hf : ∀ x, f x ∈ Icc 0 1)
    (hTop : ∀ x, g x ≤ a → f x = 0) (hBot : ∀ x, b ≤ g x → f x = 1)
    (c : Set X → ℝ) (hc0 : ∀ S, 0 ≤ c S)
    (hcmono : ∀ S T, S ⊆ T → c S ≤ c T)
    (hcore : ∀ u v : X, ∀ p : Path u v,
      (∀ t, g (p t) ∈ Icc a b) → |f u-f v| ≤ c (range p))
    {u v : X} (p : Path u v) : |f u-f v| ≤ c (range p) := by
  by_cases hT : ∃ t, g (p t) ≤ a
  · by_cases hB : ∃ t, b ≤ g (p t)
    · obtain ⟨s,hs⟩ := hT
      obtain ⟨t,ht⟩ := hB
      let q := p.subpath s t
      obtain ⟨v₀,v₁,hv,hv₀,hv₁,hbetween⟩ := CannonAnnular.radial_subinterval
        (fun z => g (q z)) (hg.comp q.continuous) a b hab
        (by simpa [q] using hs) (by simpa [q] using ht)
      have hsq : range (q.subpath v₀ v₁) ⊆ range q := by
        rw [Path.range_subpath]
        exact image_subset_range _ _
      have hsp : range q ⊆ range p := by
        rw [show range q = p '' uIcc s t from Path.range_subpath p s t]
        exact image_subset_range _ _
      have hc := hcore (q v₀) (q v₁) (q.subpath v₀ v₁) (by
        intro z
        have hz : (q.subpath v₀ v₁) z ∈ range (q.subpath v₀ v₁) := mem_range_self z
        rw [Path.range_subpath_of_le _ _ _ hv.le] at hz
        obtain ⟨w,hw,hwz⟩ := hz
        rw [← hwz]
        exact hbetween w hw)
      rw [hTop _ hv₀.le,hBot _ hv₁.ge] at hc
      norm_num only [zero_sub,abs_neg,abs_one] at hc
      have hc' := hc.trans (hcmono _ _ (hsq.trans hsp))
      apply le_trans _ hc'
      exact abs_sub_le_iff.mpr ⟨by linarith [(hf u).2,(hf v).1],by linarith [(hf v).2,(hf u).1]⟩
    · have hup : ∀ t, g (p t) ≤ b := by
        intro t
        exact (lt_of_not_ge (fun ht => hB ⟨t,ht⟩)).le
      have hval := value_le_cost_of_top g hg a b f (fun x => (hf x).1) hTop
        c hc0 hcmono hcore p hup hT
      have hu : f u ≤ c (range p) := by simpa using hval 0
      have hv : f v ≤ c (range p) := by simpa using hval 1
      exact abs_sub_le_iff.mpr ⟨by linarith [(hf v).1],by linarith [(hf u).1]⟩
  · by_cases hB : ∃ t, b ≤ g (p t)
    · have hcore' : ∀ u v : X, ∀ p : Path u v,
          (∀ t, -g (p t) ∈ Icc (-b) (-a)) →
          |(1-f u)-(1-f v)| ≤ c (range p) := by
        intro u v p hp
        have hh := hcore u v p (fun t => ⟨by linarith [(hp t).2],by linarith [(hp t).1]⟩)
        simpa only [sub_sub_sub_cancel_left,abs_sub_comm] using hh
      have hval := value_le_cost_of_top (fun x => -g x) hg.neg (-b) (-a)
        (fun x => 1-f x) (fun x => by linarith [(hf x).2])
        (fun x hx => by rw [hBot x (by linarith)]; ring)
        c hc0 hcmono hcore' p (fun t => by
          have ht : a < g (p t) := lt_of_not_ge (fun ht => hT ⟨t,ht⟩)
          linarith) (by obtain ⟨t,ht⟩ := hB; exact ⟨t,by linarith⟩)
      have hu : 1-f u ≤ c (range p) := by simpa using hval 0
      have hv : 1-f v ≤ c (range p) := by simpa using hval 1
      exact abs_sub_le_iff.mpr ⟨by linarith [(hf u).2],by linarith [(hf v).2]⟩
    · apply hcore u v p
      intro t
      exact ⟨(lt_of_not_ge (fun ht => hT ⟨t,ht⟩)).le,
        (lt_of_not_ge (fun ht => hB ⟨t,ht⟩)).le⟩

end CannonBands

namespace CannonBands

open Set CannonCells CannonPotential

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

abbrev Strip (g : X → ℝ) (a b : ℝ) := {x : X // g x ∈ Icc a b}

def extend (g : X → ℝ) (a b : ℝ) (f : Strip g a b → ℝ) (x : X) : ℝ := by
  classical
  exact if hx : g x ∈ Icc a b then f ⟨x,hx⟩ else if g x ≤ a then 0 else 1

omit [TopologicalSpace X] in
lemma extend_on_strip (g : X → ℝ) (a b : ℝ) (f : Strip g a b → ℝ) (x : X)
    (hx : g x ∈ Icc a b) : extend g a b f x = f ⟨x,hx⟩ := by
  simp [extend,hx]

omit [TopologicalSpace X] in
lemma extend_bounds (g : X → ℝ) (a b : ℝ) (f : Strip g a b → ℝ)
    (hf : ∀ x, f x ∈ Icc 0 1) (x : X) : extend g a b f x ∈ Icc 0 1 := by
  classical
  unfold extend
  split
  · exact hf _
  · split <;> norm_num

omit [TopologicalSpace X] in
lemma extend_top (g : X → ℝ) (a b : ℝ) (f : Strip g a b → ℝ)
    (hf : ∀ x, g x.val = a → f x = 0) (x : X) (hx : g x ≤ a) :
    extend g a b f x = 0 := by
  classical
  unfold extend
  split
  · exact hf _ (le_antisymm hx ‹g x ∈ Icc a b›.1)
  · simp

omit [TopologicalSpace X] in
lemma extend_bottom (g : X → ℝ) (a b : ℝ) (hab : a < b) (f : Strip g a b → ℝ)
    (hf : ∀ x, g x.val = b → f x = 1) (x : X) (hx : b ≤ g x) :
    extend g a b f x = 1 := by
  classical
  unfold extend
  split
  · exact hf _ (le_antisymm ‹g x ∈ Icc a b›.2 hx)
  · simp [show ¬g x ≤ a by linarith]

omit [TopologicalSpace X] in
lemma cost_preimage_image {Y : Type*} (e : Y → X) (C : ι → Set X) (w : ι → ℝ)
    (A : Set Y) : cost (fun i => e ⁻¹' C i) w A = cost C w (e '' A) := by
  unfold cost
  congr 1
  ext i
  rw [mem_indices,mem_indices]
  constructor
  · rintro ⟨x,hx,hc⟩
    exact ⟨e x,⟨x,hx,rfl⟩,hc⟩
  · rintro ⟨z,⟨x,hx,rfl⟩,hc⟩
    exact ⟨x,hx,hc⟩

def stripPath (g : X → ℝ) (a b : ℝ) {u v : X} (p : Path u v)
    (hp : ∀ t, g (p t) ∈ Icc a b) :
    Path (⟨u,by simpa using hp 0⟩ : Strip g a b) ⟨v,by simpa using hp 1⟩ where
  toFun := fun t => ⟨p t,hp t⟩
  continuous_toFun := p.continuous.subtype_mk hp
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

lemma stripPath_image_range (g : X → ℝ) (a b : ℝ) {u v : X} (p : Path u v)
    (hp : ∀ t, g (p t) ∈ Icc a b) :
    Subtype.val '' range (stripPath g a b p hp) = range p := by
  rw [← range_comp]
  rfl

def rawExtended (g : X → ℝ) (a b : ℝ) (C : ι → Set X) (w : ι → ℝ)
    [PathConnectedSpace (Strip g a b)] : X → ℝ :=
  extend g a b (raw (fun i => Subtype.val ⁻¹' C i) w {x : Strip g a b | g x.val = a})

theorem rawExtended_properties
    (g : X → ℝ) (hg : Continuous g) (a b : ℝ) (hab : a < b)
    (C : ι → Set X) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    [PathConnectedSpace (Strip g a b)]
    (hTop : ({x : Strip g a b | g x.val = a} : Set (Strip g a b)).Nonempty)
    (hcross : ∀ u : Strip g a b, g u.val = a → ∀ v : Strip g a b, g v.val = b →
      ∀ p : Path u v, 1 ≤ cost (fun i => Subtype.val ⁻¹' C i) w (range p)) :
    (∀ x, rawExtended g a b C w x ∈ Icc 0 1) ∧
    (∀ x, g x ≤ a → rawExtended g a b C w x = 0) ∧
    (∀ x, b ≤ g x → rawExtended g a b C w x = 1) ∧
    (∀ u v : X, ∀ p : Path u v,
      |rawExtended g a b C w u-rawExtended g a b C w v| ≤ cost C w (range p)) := by
  let C' : ι → Set (Strip g a b) := fun i => Subtype.val ⁻¹' C i
  let A : Set (Strip g a b) := {x | g x.val = a}
  let B : Set (Strip g a b) := {x | g x.val = b}
  have hbare : ∀ x, raw C' w A x ∈ Icc 0 1 := raw_bounds C' w hw hTop
  have hA : ∀ x : Strip g a b, g x.val = a → raw C' w A x = 0 := by
    intro x hx
    exact raw_on_top C' w hx
  have hB : ∀ x : Strip g a b, g x.val = b → raw C' w A x = 1 := by
    intro x hx
    apply raw_on_bottom C' w hTop (B := B) _ hcross hx
    rw [Set.disjoint_left]
    intro z hzA hzB
    exact hab.ne (hzA.symm.trans hzB)
  have hbnd : ∀ x, rawExtended g a b C w x ∈ Icc 0 1 :=
    extend_bounds g a b _ hbare
  have htop : ∀ x, g x ≤ a → rawExtended g a b C w x = 0 :=
    extend_top g a b _ hA
  have hbot : ∀ x, b ≤ g x → rawExtended g a b C w x = 1 :=
    extend_bottom g a b hab _ hB
  refine ⟨hbnd,htop,hbot,?_⟩
  intro u v p
  apply extended_path_variation g hg a b hab _ hbnd htop hbot (cost C w)
    (cost_nonneg C hw) (fun _ _ h => cost_mono C hw h) _ p
  intro u v q hq
  let q' := stripPath g a b q hq
  have hh := raw_path_variation C' w hw hTop q'
  have hu : g u ∈ Icc a b := by simpa using hq 0
  have hv : g v ∈ Icc a b := by simpa using hq 1
  change |extend g a b (raw C' w A) u-extend g a b (raw C' w A) v| ≤ _
  rw [extend_on_strip g a b _ u hu,extend_on_strip g a b _ v hv]
  apply hh.trans
  change cost (fun i => Subtype.val ⁻¹' C i) w (range (stripPath g a b q hq)) ≤ _
  rw [cost_preimage_image,stripPath_image_range]

end CannonBands

namespace CannonBands

open Set unitInterval

abbrev ChartSquare := I × I

def height (z : ChartSquare) : ℝ := z.2

def stripHomeomorph (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    Strip height a b ≃ₜ I × Icc a b where
  toFun := fun z => (z.val.1,⟨z.val.2,z.property⟩)
  invFun := fun z => ⟨(z.1,⟨z.2.val,⟨ha.trans z.2.property.1,z.2.property.2.trans hb⟩⟩),
    z.2.property⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma strip_pathConnected (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    PathConnectedSpace (Strip height a b) := by
  let : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0,by norm_num⟩)
  let : PathConnectedSpace (Icc a b) := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc a b).isPathConnected ⟨a,le_rfl,hab⟩)
  exact (stripHomeomorph a b ha hb).symm.surjective.pathConnectedSpace
    (stripHomeomorph a b ha hb).symm.continuous

lemma strip_top_nonempty (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    ({x : Strip height a b | height x.val = a} : Set (Strip height a b)).Nonempty := by
  exact ⟨⟨(0,⟨a,ha,hab.trans hb⟩),le_rfl,hab⟩,rfl⟩

end CannonBands

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_Square
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonPlanar

abbrev Square := I × I

instance instLocallyPathConnectedSpaceElemRealUnitInterval_solutions : LocallyPathConnectedSpace I :=
  (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).locallyPathConnectedSpace

end CannonPlanar

namespace CannonRegularization

variable {X : Type*} [TopologicalSpace X]

def FloodThresholds (f : X → ℝ) (A : Set X) (x : X) : Set ℝ :=
  {c | ∃ y ∈ A, ∃ p : Path x y, ∀ t, f (p t) ≤ c}

def flood (f : X → ℝ) (A : Set X) (x : X) : ℝ :=
  sInf (FloodThresholds f A x)

lemma floodThresholds_bddBelow (f : X → ℝ) (A : Set X) (x : X) :
    BddBelow (FloodThresholds f A x) := by
  refine ⟨f x, ?_⟩
  rintro c ⟨y, hy, p, hp⟩
  simpa using hp 0

lemma floodThresholds_nonempty [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) (x : X) :
    (FloodThresholds f A x).Nonempty := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨B, y, hy, PathConnectedSpace.somePath x y, fun t => hf _⟩

lemma le_flood [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) (x : X) : f x ≤ flood f A x := by
  apply le_csInf (floodThresholds_nonempty hA hf x)
  rintro c ⟨y, hy, p, hp⟩
  simpa using hp 0

lemma flood_le_of_path {f : X → ℝ} {A : Set X} {x y : X}
    (hy : y ∈ A) (p : Path x y) {B : ℝ} (hp : ∀ t, f (p t) ≤ B) :
    flood f A x ≤ B :=
  csInf_le (floodThresholds_bddBelow f A x) ⟨y, hy, p, hp⟩

lemma flood_eq_on_band [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) {x : X} (hx : x ∈ A) : flood f A x = f x := by
  apply le_antisymm _ (le_flood hA hf x)
  exact flood_le_of_path hx (Path.refl x) (by simp)

lemma flood_le_upper [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) (x : X) : flood f A x ≤ B := by
  obtain ⟨y, hy⟩ := hA
  exact flood_le_of_path hy (PathConnectedSpace.somePath x y) (fun t => hf _)

lemma flood_le_max [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) {x y : X} (p : Path x y) {M : ℝ}
    (hp : ∀ t, f (p t) ≤ M) : flood f A x ≤ max M (flood f A y) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  have hcy : flood f A y < c := (le_max_right _ _).trans_lt hc
  obtain ⟨d, hd, hdc⟩ := (csInf_lt_iff (floodThresholds_bddBelow f A y)
    (floodThresholds_nonempty hA hf y)).mp hcy
  obtain ⟨z, hz, q, hq⟩ := hd
  apply flood_le_of_path hz (p.trans q)
  intro t
  have ht : (p.trans q) t ∈ range p ∪ range q := by
    rw [← Path.trans_range]
    exact mem_range_self t
  rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]
    exact (hp s).trans ((le_max_left _ _).trans hc.le)
  · rw [← hs]
    exact (hq s).trans hdc.le

theorem flood_path_variation [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) {x y : X} (p : Path x y) {m M : ℝ}
    (hp : ∀ t, f (p t) ∈ Icc m M) :
    |flood f A x - flood f A y| ≤ M - m := by
  have hxy := flood_le_max hA hf p (fun t => (hp t).2)
  have hyx := flood_le_max hA hf p.symm (fun t => (hp (unitInterval.symm t)).2)
  have hx : m ≤ flood f A x := by
    have : m ≤ f x := by simpa using (hp 0).1
    exact this.trans (le_flood hA hf x)
  have hy : m ≤ flood f A y := by
    have : m ≤ f y := by simpa using (hp 1).1
    exact this.trans (le_flood hA hf y)
  have hmM : m ≤ M := (hp 0).1.trans (hp 0).2
  rw [abs_le]
  constructor
  · rcases le_max_iff.mp hyx with h | h <;> linarith
  · rcases le_max_iff.mp hxy with h | h <;> linarith

theorem continuous_flood [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : Continuous f) (hfB : ∀ x, f x ≤ B) : Continuous (flood f A) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hfn : {y | dist (f y) (f x) < ε / 4} ∈ 𝓝 x :=
    (Metric.tendsto_nhds.mp hf.continuousAt) (ε / 4) (by positivity)
  obtain ⟨S, ⟨hSn, hSc⟩, hSf⟩ := (path_connected_basis x).mem_iff.mp hfn
  filter_upwards [hSn] with y hy
  obtain ⟨p, hp⟩ := hSc.joinedIn x (mem_of_mem_nhds hSn) y hy
  have hosc := flood_path_variation hA hfB p (m := f x - ε / 4)
    (M := f x + ε / 4) (fun t => ?_)
  · rw [Real.dist_eq, abs_sub_comm]
    exact hosc.trans_lt (by linarith)
  · have hft := hSf (hp t)
    change dist (f (p t)) (f x) < ε / 4 at hft
    rw [Real.dist_eq, abs_sub_lt_iff] at hft
    constructor <;> linarith [hft.1, hft.2]

def drain (f : X → ℝ) (A : Set X) (x : X) : ℝ :=
  -flood (fun z => -f z) A x

lemma drain_le [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, B ≤ f x) (x : X) : drain f A x ≤ f x := by
  have := le_flood (f := fun z => -f z) hA (B := -B) (by intro z; linarith [hf z]) x
  dsimp [drain]
  linarith

lemma drain_eq_on_band [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, B ≤ f x) {x : X} (hx : x ∈ A) : drain f A x = f x := by
  dsimp [drain]
  rw [flood_eq_on_band hA (B := -B) (by intro z; linarith [hf z]) hx]
  simp

lemma drain_lower [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, B ≤ f x) (x : X) : B ≤ drain f A x := by
  have := flood_le_upper (f := fun z => -f z) hA (B := -B) (by intro z; linarith [hf z]) x
  dsimp [drain]
  linarith

theorem continuous_drain [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : Continuous f) (hfB : ∀ x, B ≤ f x) : Continuous (drain f A) :=
  (continuous_flood hA (B := -B) hf.neg (by intro x; change -f x ≤ -B; linarith [hfB x])).neg

end CannonRegularization

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_LiftPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonChart

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def liftPath (e : X → Y) (he : IsEmbedding e) {a b : X}
    (p : Path (e a) (e b)) (hp : ∀ t, p t ∈ range e) : Path a b where
  toFun := fun t => he.toHomeomorph.symm ⟨p t,hp t⟩
  continuous_toFun := he.toHomeomorph.symm.continuous.comp (p.continuous.subtype_mk hp)
  source' := by
    apply he.toHomeomorph.injective
    simp
  target' := by
    apply he.toHomeomorph.injective
    simp

end CannonChart

namespace CannonLevel

open CannonPlanar CannonRegularization

instance instPathConnectedSpaceSquare : PathConnectedSpace Square :=
  pathConnectedSpace_iff_connectedSpace.mpr inferInstance

theorem regularized_values {f : Square → ℝ} {A B : Set Square}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (hAf : ∀ z ∈ A, f z = 0) (hBf : ∀ z ∈ B, f z = 1) :
    (∀ z, drain (flood f A) B z ∈ Icc (0 : ℝ) 1) ∧
    (∀ z ∈ A, drain (flood f A) B z = 0) ∧
    (∀ z ∈ B, drain (flood f A) B z = 1) := by
  have hF0 : ∀ z, 0 ≤ flood f A z := fun z => (hf0 z).trans (le_flood hA hf1 z)
  have hF1 := flood_le_upper hA hf1
  have hH0 := drain_lower hB hF0
  have hHF := drain_le hB hF0
  refine ⟨fun z => ⟨hH0 z, (hHF z).trans (hF1 z)⟩, ?_, ?_⟩
  · intro z hz
    apply le_antisymm _ (hH0 z)
    simpa [flood_eq_on_band hA hf1 hz, hAf z hz] using hHF z
  · intro z hz
    rw [drain_eq_on_band hB hF0 hz]
    apply le_antisymm (hF1 z)
    simpa [hBf z hz] using le_flood hA hf1 z

lemma slab_pathConnected {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IsPathConnected {z : Square | a ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ b} := by
  let e : Square → ℝ × ℝ := Prod.map Subtype.val Subtype.val
  have he : Topology.IsInducing e := Topology.IsInducing.subtypeVal.prodMap
    Topology.IsInducing.subtypeVal
  rw [he.isPathConnected_iff]
  have himage : e '' {z : Square | a ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ b} =
      Icc ((0 : ℝ),a) (1,b) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨⟨w.1.property.1,hw.1⟩,⟨w.1.property.2,hw.2⟩⟩
    · intro hz
      refine ⟨(⟨z.1,hz.1.1,hz.2.1⟩,⟨z.2,ha.trans hz.1.2,hz.2.2.trans hb⟩), ?_, rfl⟩
      exact ⟨hz.1.2,hz.2.2⟩
  rw [himage]
  exact (convex_Icc _ _).isPathConnected ⟨(0,a),⟨le_rfl,⟨zero_le_one,hab⟩⟩⟩

def topBand : Set Square := {z | (z.2 : ℝ) ≤ 1 / 3}

def bottomBand : Set Square := {z | 2 / 3 ≤ (z.2 : ℝ)}

def centralRectangle : Set Square := {z | (z.2 : ℝ) ∈ Icc (1 / 3) (2 / 3)}

lemma topBand_pathConnected : IsPathConnected topBand := by
  convert slab_pathConnected (a := 0) (b := 1 / 3) (by norm_num) (by norm_num) (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  exact ⟨fun hz => ⟨z.2.property.1,hz⟩,fun hz => hz.2⟩

lemma bottomBand_pathConnected : IsPathConnected bottomBand := by
  convert slab_pathConnected (a := 2 / 3) (b := 1) (by norm_num) (by norm_num) (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  exact ⟨fun hz => ⟨hz,z.2.property.2⟩,fun hz => hz.1⟩

end CannonLevel

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Hat
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonGrid

def hat (x y : ℝ) : ℝ := max 0 (1 - max |x| (max |y| |x-y|))

lemma hat_nonneg (x y : ℝ) : 0 ≤ hat x y := le_max_left ..

lemma continuous_hat : Continuous (fun p : ℝ × ℝ => hat p.1 p.2) := by
  exact continuous_const.max (continuous_const.sub
    (continuous_fst.abs.max (continuous_snd.abs.max (continuous_fst.sub continuous_snd).abs)))

lemma hat_ne_zero {x y : ℝ} (h : hat x y ≠ 0) : |x| < 1 ∧ |y| < 1 := by
  have hh : 0 < hat x y := lt_of_le_of_ne (hat_nonneg x y) h.symm
  rw [hat, lt_max_iff] at hh
  have ht : max |x| (max |y| |x-y|) < 1 := by rcases hh with hh | hh <;> linarith
  exact ⟨(le_max_left ..).trans_lt ht, ((le_max_left ..).trans (le_max_right ..)).trans_lt ht⟩

lemma hat_neg (x y : ℝ) : hat (-x) (-y) = hat x y := by
  simp only [hat, abs_neg]
  congr 3
  rw [show -x - -y = -(x-y) by ring, abs_neg]

lemma hat_on_square {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat x y = 1-max x y := by
  have ha : |x-y| ≤ max x y := abs_le.mpr ⟨by
    have := le_max_right x y
    linarith [hx.1], by
    have := le_max_left x y
    linarith [hy.1]⟩
  have he : max |x| (max |y| |x-y|) = max x y := by
    rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1]
    apply le_antisymm
    · exact max_le (le_max_left ..) (max_le (le_max_right ..) ha)
    · exact max_le (le_max_left ..) ((le_max_left ..).trans (le_max_right ..))
  rw [hat, he, max_eq_right]
  exact sub_nonneg.mpr (max_le hx.2 hy.2)

lemma hat_on_square_right {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat (x-1) y = max 0 (x-y) := by
  have hx' : x-1 ≤ 0 := by linarith [hx.2]
  have hxy : x-1-y ≤ 0 := by linarith [hx.2,hy.1]
  have hm : max (-(x-1)) (max y (-(x-1-y))) = -(x-1-y) := by
    have h₁ : y ≤ -(x-1-y) := by linarith [hx.2]
    rw [max_eq_right h₁, max_eq_right (by linarith [hy.1])]
  simp only [hat, abs_of_nonpos hx', abs_of_nonneg hy.1, abs_of_nonpos hxy, hm]
  congr 1
  ring

lemma hat_comm (x y : ℝ) : hat x y = hat y x := by
  unfold hat
  rw [abs_sub_comm x y, max_left_comm |x| |y|]

lemma hat_on_square_top {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat x (y-1) = max 0 (y-x) := by
  rw [hat_comm]
  exact hat_on_square_right hy hx

lemma hat_on_square_diag {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat (x-1) (y-1) = min x y := by
  rw [show x-1 = -(1-x) by ring, show y-1 = -(1-y) by ring, hat_neg]
  rw [hat_on_square ⟨by linarith [hx.2],by linarith [hx.1]⟩
    ⟨by linarith [hy.2],by linarith [hy.1]⟩]
  by_cases h : x ≤ y
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · have hh := le_of_not_ge h
    rw [min_eq_right hh, max_eq_right (by linarith)]
    ring

lemma four_hats {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat x y + hat x (y-1) + (hat (x-1) y + hat (x-1) (y-1)) = 1 := by
  rw [hat_on_square hx hy, hat_on_square_right hx hy,
    hat_on_square_top hx hy, hat_on_square_diag hx hy]
  by_cases h : x ≤ y
  · rw [max_eq_right h, min_eq_left h, max_eq_right (by linarith : 0 ≤ y-x),
      max_eq_left (by linarith : x-y ≤ 0)]
    ring
  · have hh := le_of_not_ge h
    rw [max_eq_left hh, min_eq_right hh, max_eq_left (by linarith : y-x ≤ 0),
      max_eq_right (by linarith : 0 ≤ x-y)]
    ring

lemma grid_cell {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Icc 0 (N:ℝ)) :
    ∃ k : ℕ, k < N ∧ (k:ℝ) ≤ x ∧ x ≤ k+1 := by
  by_cases h : x < N
  · exact ⟨Nat.floor x, (Nat.floor_lt hx.1).mpr h, Nat.floor_le hx.1,
      (Nat.lt_floor_add_one x).le⟩
  · have hxN : x = N := le_antisymm hx.2 (le_of_not_gt h)
    refine ⟨N-1, by omega, ?_, ?_⟩
    all_goals rw [hxN, Nat.cast_sub (by omega : 1 ≤ N)]; norm_num

lemma nat_eq_or_succ_of_abs_lt {k i : ℕ} {x : ℝ}
    (hx : (k:ℝ) ≤ x ∧ x ≤ k+1) (hi : |x-i| < 1) : i = k ∨ i = k+1 := by
  have hi' := abs_lt.mp hi
  by_contra h
  push Not at h
  have hcases : i+1 ≤ k ∨ k+2 ≤ i := by omega
  rcases hcases with h | h
  · have hh : (i:ℝ)+1 ≤ k := by exact_mod_cast h
    linarith [hx.1,hi'.2]
  · have hh : (k:ℝ)+2 ≤ i := by exact_mod_cast h
    linarith [hx.2,hi'.1]

lemma sum_two {ι : Type*} [Fintype ι] (f : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → f k = 0) : (∑ k, f k) = f i + f j := by
  classical
  have he : ∑ k ∈ ({i,j} : Finset ι), f k = ∑ k, f k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    exact h k (fun he => hk (by simp [he])) (fun he => hk (by simp [he]))
  rw [← he]
  simp [hij]

theorem grid_partition {N : ℕ} (hN : 0 < N) {x y : ℝ}
    (hx : x ∈ Icc 0 (N:ℝ)) (hy : y ∈ Icc 0 (N:ℝ)) :
    (∑ i : Fin (N+1), ∑ j : Fin (N+1), hat (x-i) (y-j)) = 1 := by
  obtain ⟨k,hk,hkx⟩ := grid_cell hN hx
  obtain ⟨l,hl,hly⟩ := grid_cell hN hy
  let k₀ : Fin (N+1) := ⟨k,by omega⟩
  let k₁ : Fin (N+1) := ⟨k+1,by omega⟩
  let l₀ : Fin (N+1) := ⟨l,by omega⟩
  let l₁ : Fin (N+1) := ⟨l+1,by omega⟩
  have hkne : k₀ ≠ k₁ := by intro h; have := congrArg Fin.val h; dsimp [k₀,k₁] at this; omega
  have hlne : l₀ ≠ l₁ := by intro h; have := congrArg Fin.val h; dsimp [l₀,l₁] at this; omega
  have hrow : ∀ i : Fin (N+1), i ≠ k₀ → i ≠ k₁ → ∀ j : Fin (N+1),
      hat (x-i) (y-j) = 0 := by
    intro i hi₀ hi₁ j
    by_contra hh
    rcases nat_eq_or_succ_of_abs_lt hkx (hat_ne_zero hh).1 with hh | hh
    · exact hi₀ (Fin.ext hh)
    · exact hi₁ (Fin.ext hh)
  have hcol : ∀ j : Fin (N+1), j ≠ l₀ → j ≠ l₁ → ∀ i : Fin (N+1),
      hat (x-i) (y-j) = 0 := by
    intro j hj₀ hj₁ i
    by_contra hh
    rcases nat_eq_or_succ_of_abs_lt hly (hat_ne_zero hh).2 with hh | hh
    · exact hj₀ (Fin.ext hh)
    · exact hj₁ (Fin.ext hh)
  rw [sum_two _ k₀ k₁ hkne (by intro i hi₀ hi₁; simp [hrow i hi₀ hi₁])]
  rw [sum_two _ l₀ l₁ hlne (by intro j hj₀ hj₁; exact hcol j hj₀ hj₁ k₀)]
  rw [sum_two _ l₀ l₁ hlne (by intro j hj₀ hj₁; exact hcol j hj₀ hj₁ k₁)]
  change hat (x-(k:ℝ)) (y-(l:ℝ)) + hat (x-k) (y-(l+1:ℕ)) +
    (hat (x-(k+1:ℕ)) (y-l) + hat (x-(k+1:ℕ)) (y-(l+1:ℕ))) = 1
  simp only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub]
  exact four_hats ⟨by linarith [hkx.1],by linarith [hkx.2]⟩
    ⟨by linarith [hly.1],by linarith [hly.2]⟩

end CannonGrid

namespace CannonGrid

open unitInterval

abbrev Square := I × I

abbrev Index (N : ℕ) := Fin (N+1) × Fin (N+1)

def vertex (N : ℕ) (hN : 0 < N) (i : Index N) : Square :=
  (⟨(i.1:ℝ)/N, ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast Nat.le_of_lt_succ i.1.isLt)⟩⟩,
   ⟨(i.2:ℝ)/N, ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast Nat.le_of_lt_succ i.2.isLt)⟩⟩)

def weight (N : ℕ) (z : Square) (i : Index N) : ℝ :=
  hat (N*(z.1:ℝ)-i.1) (N*(z.2:ℝ)-i.2)

def interpolate (N : ℕ) (hN : 0 < N) (f : Square → ℝ) (z : Square) : ℝ :=
  ∑ i : Index N, weight N z i * f (vertex N hN i)

lemma weight_nonneg (N : ℕ) (z : Square) (i : Index N) : 0 ≤ weight N z i :=
  hat_nonneg ..

lemma weight_partition (N : ℕ) (hN : 0 < N) (z : Square) :
    (∑ i : Index N, weight N z i) = 1 := by
  rw [Fintype.sum_prod_type]
  apply grid_partition hN
  · exact ⟨mul_nonneg (Nat.cast_nonneg _) z.1.property.1,
      by simpa using mul_le_mul_of_nonneg_left z.1.property.2 (Nat.cast_nonneg N : (0:ℝ) ≤ N)⟩
  · exact ⟨mul_nonneg (Nat.cast_nonneg _) z.2.property.1,
      by simpa using mul_le_mul_of_nonneg_left z.2.property.2 (Nat.cast_nonneg N : (0:ℝ) ≤ N)⟩

lemma continuous_weight (N : ℕ) (i : Index N) : Continuous (fun z : Square => weight N z i) := by
  unfold weight
  exact continuous_hat.comp (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
      continuous_const).prodMk
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const))

theorem continuous_interpolate (N : ℕ) (hN : 0 < N) (f : Square → ℝ) :
    Continuous (interpolate N hN f) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_weight N i).mul continuous_const

lemma interpolate_bounds_of_support (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (z : Square) (a b : ℝ)
    (hf : ∀ i, weight N z i ≠ 0 → f (vertex N hN i) ∈ Icc a b) :
    interpolate N hN f z ∈ Icc a b := by
  constructor
  · calc
      a = (∑ i : Index N, weight N z i)*a := by rw [weight_partition N hN z,one_mul]
      _ = ∑ i : Index N, weight N z i*a := Finset.sum_mul ..
      _ ≤ interpolate N hN f z := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : weight N z i = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_left (hf i hi).1 (weight_nonneg ..)
  · calc
      interpolate N hN f z ≤ ∑ i : Index N, weight N z i*b := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : weight N z i = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_left (hf i hi).2 (weight_nonneg ..)
      _ = (∑ i : Index N, weight N z i)*b := (Finset.sum_mul ..).symm
      _ = b := by rw [weight_partition N hN z,one_mul]

lemma interpolate_bounds (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (hf : ∀ z, f z ∈ Icc 0 1) (z : Square) :
    interpolate N hN f z ∈ Icc 0 1 :=
  interpolate_bounds_of_support N hN f z 0 1 (fun _ _ => hf _)

lemma interpolate_eq_of_support (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (z : Square) (c : ℝ) (hf : ∀ i, weight N z i ≠ 0 → f (vertex N hN i) = c) :
    interpolate N hN f z = c := by
  have hh := interpolate_bounds_of_support N hN f z c c (by intro i hi; simp [hf i hi])
  exact le_antisymm hh.2 hh.1

lemma support_below {N : ℕ} {z : Square} {i : Index N} {k : ℕ}
    (hz : N*(z.2:ℝ) ≤ k) (hi : weight N z i ≠ 0) : i.2.val ≤ k := by
  have hh := (abs_lt.mp (hat_ne_zero hi).2).1
  have hr : (i.2.val:ℝ) < (k:ℝ)+1 := by linarith
  have hn : i.2.val < k+1 := by exact_mod_cast hr
  omega

lemma support_above {N : ℕ} {z : Square} {i : Index N} {k : ℕ}
    (hz : (k:ℝ) ≤ N*(z.2:ℝ)) (hi : weight N z i ≠ 0) : k ≤ i.2.val := by
  have hh := (abs_lt.mp (hat_ne_zero hi).2).2
  have hr : (k:ℝ) < (i.2.val:ℝ)+1 := by linarith
  have hn : k < i.2.val+1 := by exact_mod_cast hr
  omega

theorem interpolate_const_below (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (c : ℝ) (k : ℕ) (hf : ∀ i, i.2.val ≤ k → f (vertex N hN i) = c)
    (z : Square) (hz : N*(z.2:ℝ) ≤ k) : interpolate N hN f z = c := by
  apply interpolate_eq_of_support
  intro i hi
  exact hf i (support_below hz hi)

theorem interpolate_const_above (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (c : ℝ) (k : ℕ) (hf : ∀ i, k ≤ i.2.val → f (vertex N hN i) = c)
    (z : Square) (hz : (k:ℝ) ≤ N*(z.2:ℝ)) : interpolate N hN f z = c := by
  apply interpolate_eq_of_support
  intro i hi
  exact hf i (support_above hz hi)

theorem interpolate_preserves_bands (n : ℕ) (hn : 0 < n) (f : Square → ℝ)
    (hT : ∀ z, (z.2:ℝ) ≤ 1/3 → f z = 0)
    (hB : ∀ z, 2/3 ≤ (z.2:ℝ) → f z = 1) :
    (∀ z : Square, (z.2:ℝ) ≤ 1/3 → interpolate (3*n) (by omega) f z = 0) ∧
    (∀ z : Square, 2/3 ≤ (z.2:ℝ) → interpolate (3*n) (by omega) f z = 1) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hden : (0:ℝ) < (3*n:ℕ) := by positivity
  constructor
  · intro z hz
    apply interpolate_const_below (3*n) (by omega) f 0 n
    · intro i hi
      apply hT
      change (i.2.val:ℝ)/(3*n:ℕ) ≤ 1/3
      apply (div_le_iff₀ hden).mpr
      have hh : (i.2.val:ℝ) ≤ n := by exact_mod_cast hi
      push_cast
      nlinarith
    · push_cast
      nlinarith
  · intro z hz
    apply interpolate_const_above (3*n) (by omega) f 1 (2*n)
    · intro i hi
      apply hB
      change 2/3 ≤ (i.2.val:ℝ)/(3*n:ℕ)
      apply (le_div_iff₀ hden).mpr
      have hh : ((2*n:ℕ):ℝ) ≤ i.2.val := by exact_mod_cast hi
      push_cast at hh ⊢
      nlinarith
    · push_cast
      nlinarith

end CannonGrid

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_RawFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonApprox

open CannonGrid CannonRegularization CannonLevel CannonCells CannonBands

variable {ι : Type*} [Fintype ι]

local instance instPathConnectedSpaceStripChartSquareHeightHDivRealOfNat : PathConnectedSpace (Strip height (1 / 3) (2 / 3)) :=
  strip_pathConnected _ _ (by norm_num) (by norm_num) (by norm_num)

def rawFunction (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ) : CannonGrid.Square → ℝ :=
  rawExtended height (1/3) (2/3) C ρ

def Admissible (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ) : Prop :=
  ∀ u : Strip height (1/3) (2/3), height u.val = 1/3 →
    ∀ v : Strip height (1/3) (2/3), height v.val = 2/3 →
      ∀ p : Path u v, 1 ≤ cost (fun i => Subtype.val ⁻¹' C i) ρ (range p)

theorem rawFunction_properties (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hcross : Admissible C ρ) :
    (∀ z, rawFunction C ρ z ∈ Icc 0 1) ∧
    (∀ z ∈ topBand, rawFunction C ρ z = 0) ∧
    (∀ z ∈ bottomBand, rawFunction C ρ z = 1) ∧
    (∀ u v, ∀ p : Path u v, |rawFunction C ρ u-rawFunction C ρ v| ≤ cost C ρ (range p)) := by
  exact rawExtended_properties height (by unfold height; fun_prop) (1/3) (2/3) (by norm_num) C ρ hρ
    (strip_top_nonempty _ _ (by norm_num) (by norm_num) (by norm_num)) hcross

def initial (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ) (n : ℕ) (hn : 0 < n) :
    CannonGrid.Square → ℝ := interpolate (3*n) (by omega) (rawFunction C ρ)

def scalar (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ) (n : ℕ) (hn : 0 < n) :
    CannonGrid.Square → ℝ := drain (flood (initial C ρ n hn) topBand) bottomBand

lemma initial_properties (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hcross : Admissible C ρ) (n : ℕ) (hn : 0 < n) :
    Continuous (initial C ρ n hn) ∧ (∀ z, initial C ρ n hn z ∈ Icc 0 1) ∧
    (∀ z ∈ topBand, initial C ρ n hn z = 0) ∧
    (∀ z ∈ bottomBand, initial C ρ n hn z = 1) := by
  obtain ⟨hrange,htop,hbottom,_⟩ := rawFunction_properties C ρ hρ hcross
  have hbands := interpolate_preserves_bands n hn (rawFunction C ρ) htop hbottom
  exact ⟨continuous_interpolate _ _ _, interpolate_bounds _ _ _ hrange,hbands⟩

theorem scalar_properties (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hcross : Admissible C ρ) (n : ℕ) (hn : 0 < n) :
    Continuous (scalar C ρ n hn) ∧ (∀ z, scalar C ρ n hn z ∈ Icc 0 1) ∧
    (∀ z ∈ topBand, scalar C ρ n hn z = 0) ∧
    (∀ z ∈ bottomBand, scalar C ρ n hn z = 1) := by
  obtain ⟨hf,hfI,hT,hB⟩ := initial_properties C ρ hρ hcross n hn
  have hF := continuous_flood topBand_pathConnected.nonempty hf (fun z => (hfI z).2)
  have hFk : ∀ z, 0 ≤ flood (initial C ρ n hn) topBand z := fun z =>
    (hfI z).1.trans (le_flood topBand_pathConnected.nonempty (fun w => (hfI w).2) z)
  exact ⟨continuous_drain bottomBand_pathConnected.nonempty hF hFk,
    regularized_values topBand_pathConnected.nonempty bottomBand_pathConnected.nonempty
      (fun z => (hfI z).1) (fun z => (hfI z).2) hT hB⟩

end CannonApprox

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_Plane
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology

namespace CannonCharts

abbrev Plane := ℝ × ℝ

abbrev SphereTwo := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def box (r : ℝ) : Set Plane := closedBall 0 r

def openBox (r : ℝ) : Set Plane := ball 0 r

end CannonCharts

open Set Topology unitInterval

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_SideOrientation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCharts

open unitInterval

def sideOrientation : Fin 4 → Plane ≃ₜ Plane :=
  ![Homeomorph.refl Plane,
    (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ),
    Homeomorph.prodComm ℝ ℝ,
    (Homeomorph.prodComm ℝ ℝ).trans
      ((Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ))]

end CannonCharts

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_StripCrossing
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCharts

open unitInterval

def StripCrossing (q : I → Plane) : Prop :=
  Continuous q ∧ (q 0).1 = 1 ∧ (q 1).1 = 2 ∧
    ∀ t, (q t).1 ∈ Icc 1 2 ∧ |(q t).2| ≤ 2

def stripFamily {X : Type*} (e : Plane → X) : Set (Set X) :=
  {A | ∃ q : I → Plane, StripCrossing q ∧ A = range (e ∘ q)}

def macroFamily {X : Type*} [MetricSpace X] (d : ℝ) : Set (Set X) :=
  {A | ∃ p : I → X, Continuous p ∧ A = range p ∧ d ≤ diam A}

end CannonCharts

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_SquareMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCharts

def squareMap (z : CannonGrid.Square) : Plane := (1+(z.1:ℝ),12*(z.2:ℝ)-6)

lemma continuous_squareMap : Continuous squareMap := by
  unfold squareMap
  fun_prop

lemma squareMap_injective : Function.Injective squareMap := by
  intro z w h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext
  · apply Subtype.ext
    dsimp [squareMap] at hx
    linarith
  · apply Subtype.ext
    dsimp [squareMap] at hy
    linarith

lemma squareMap_embedding : IsEmbedding squareMap :=
  (continuous_squareMap.isClosedEmbedding squareMap_injective).isEmbedding

end CannonCharts

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_PathCellIndices
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonAnnular

open Metric

noncomputable def pathCellIndices {Y β : Type*} [PseudoMetricSpace Y] [Fintype β]
    (ξ : β → Y) (s : ℝ) {u v : Y} (p : Path u v) : Finset β := by
  classical
  exact Finset.univ.filter (fun j => ∃ t, dist (p t) (ξ j) < 2*s)

def MacroscopicAdmissible {Y β : Type*} [PseudoMetricSpace Y] [Fintype β]
    (ξ : β → Y) (s d₀ : ℝ) (ω : β → ℝ) : Prop :=
  (∀ j, 0 ≤ ω j) ∧ ∀ (u v : Y) (p : Path u v),
    d₀ ≤ diam (Set.range p) → 1 ≤ ∑ j ∈ pathCellIndices ξ s p, ω j

end CannonAnnular

open Set Metric

end

end

end

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_Extend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology

namespace CannonChart

open Set Topology Metric

variable {X Y : Type*}

def extend (e : X → Y) (f : X → ℝ) : Y → ℝ := Function.extend e f (fun _ => 0)

lemma extend_apply (e : X → Y) (he : Function.Injective e) (f : X → ℝ) (x : X) :
    extend e f (e x) = f x := he.extend_apply f (fun _ => 0) x

lemma continuousOn_extend [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y) (he : IsEmbedding e) (f : X → ℝ)
    (hf : Continuous f) : ContinuousOn (extend e f) (range e) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := hf.comp he.toHomeomorph.symm.continuous
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  obtain ⟨x,hx⟩ := y.property
  have hy : y = he.toHomeomorph x := Subtype.ext hx.symm
  subst y
  simp only [Set.domRestrict, Function.comp_apply, Homeomorph.symm_apply_apply]
  exact extend_apply e he.injective f x

end CannonChart

open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_Interior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonChart

def onInterior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X → Y) (he : IsEmbedding e) (f : C(X,ℝ)) : C(interior (range e),ℝ) :=
  ⟨fun z => extend e f z.val,
    (continuousOn_extend e he f f.continuous).comp_continuous
      continuous_subtype_val (fun z => interior_subset z.property)⟩

end CannonChart

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_Radius
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
open Filter Topology

namespace CannonNode

def radius (ell : ℝ) (k : ℕ) : ℝ := Real.exp (-ell*k)

end CannonNode

end

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_Lower
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
open Set Metric

namespace CannonNode

def lower {X : Type*} [MetricSpace X] (f : X → ℝ) (y : X) (r : ℝ) : ℝ :=
  sInf (f '' closedBall y r)

def upper {X : Type*} [MetricSpace X] (f : X → ℝ) (y : X) (r : ℝ) : ℝ :=
  sSup (f '' closedBall y r)

end CannonNode

end

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_GoodCandidates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section

namespace CannonNode

open Set Metric Finset CannonCapacity

attribute [local instance] Classical.propDecidable

def GoodCandidates {ι : Type*} (li ui lo uo : ι → ℝ) (a b κ : ℝ) : Prop :=
  ∃ i j,
    κ*(b-a) ≤ clip a (a+(b-a)/4) (ui i)-clip a (a+(b-a)/4) (li i) ∧
    κ*(b-a) ≤ clip (a+3*(b-a)/4) b (ui j)-clip (a+3*(b-a)/4) b (li j) ∧
    uo i+(b-a)/4 ≤ lo j

end CannonNode

end

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_Node
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
namespace CannonNode

open Set Metric

structure SourceNode {X : Type*} [MetricSpace X] (f : X → ℝ) (x₀ : X)
    (ε ell c₀ B : ℝ) (kmin : ℕ) where
  center : X
  depth : ℕ
  lowerDepth : kmin ≤ depth
  a : ℝ
  b : ℝ
  apos : 0 < a
  ab : a < b
  bone : b < 1
  straddle : lower f center (c₀*radius ell depth) ≤ a ∧
    b ≤ upper f center (c₀*radius ell depth)
  reserve : dist center x₀+2*B*radius ell depth ≤ ε

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ B : ℝ} {kmin : ℕ}

namespace SourceNode

def length (v : SourceNode f x₀ ε ell c₀ B kmin) : ℝ := v.b-v.a

end SourceNode

end CannonNode

end

section

open Set Metric

namespace CannonMagnification

def Expansion {X : Type*} [MetricSpace X] (h : X ≃ₜ X) (x : X)
    (r C L : ℝ) : Prop :=
  ∀ y z,
    dist (h y) (h z) * max r (dist x y) * max r (dist x z) ≤ C*r*dist y z ∧
    r*dist y z ≤ L*dist (h y) (h z) * max r (dist x y) * max r (dist x z)

end CannonMagnification

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonAnnular CannonMagnification

attribute [local instance] Classical.propDecidable

def LiteralGood {X : Type*} [MetricSpace X] (f : X → ℝ) (Y : Finset X)
    (c₀ r a b κ : ℝ) : Prop :=
  GoodCandidates (fun y : Y => lower f y (2*r)) (fun y : Y => upper f y (2*r))
    (fun y : Y => lower f y (c₀*r)) (fun y : Y => upper f y (c₀*r)) a b κ

end CannonNode

end

section

section

open Set Filter Finset

namespace CannonFlow

structure FiniteFlow where
  size : ℕ → ℕ
  parent : (n : ℕ) → Fin (size (n+1)) → Fin (size n)
  weight : (n : ℕ) → Fin (size n) → ℝ
  nonneg : ∀ n v, 0 ≤ weight n v
  root_mass : ∑ v, weight 0 v = 1
  conserves : ∀ n v, weight n v = ∑ w, if parent n w = v then weight (n+1) w else 0
  good : (n : ℕ) → Fin (size n) → Prop

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

def badCount : (n : ℕ) → Fin (T.size n) → ℕ
  | 0, _ => 0
  | n+1, v => badCount n (T.parent n v) + if T.good n (T.parent n v) then 0 else 1

def expectedBad (n : ℕ) : ℝ := ∑ v, T.weight n v * (T.badCount n v : ℝ)

def badMass (n : ℕ) : ℝ := ∑ v, T.weight n v * if T.good n v then 0 else 1

def goodMass (n : ℕ) : ℝ := ∑ v, T.weight n v * if T.good n v then 1 else 0

end FiniteFlow

end CannonFlow

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_Subdivision
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
open Set Filter Finset

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

structure Subdivision (X : Type*) where
  degree : X → ℕ
  child : (x : X) → Fin (degree x) → X
  prob : (x : X) → Fin (degree x) → ℝ
  prob_pos : ∀ x i, 0 < prob x i
  prob_sum : ∀ x, ∑ i, prob x i = 1

structure Population (X : Type*) where
  size : ℕ
  state : Fin size → X

namespace Subdivision

variable {X : Type*} (R : Subdivision X)

def Offspring (P : Population X) := Σ v : Fin P.size, Fin (R.degree (P.state v))

instance instFintypeOffspring (P : Population X) : Fintype (R.Offspring P) := inferInstanceAs (Fintype (Σ v : Fin P.size, Fin (R.degree (P.state v))))

def next (P : Population X) : Population X where
  size := Fintype.card (R.Offspring P)
  state i := R.child (P.state ((Fintype.equivFin (R.Offspring P)).symm i).1)
    ((Fintype.equivFin (R.Offspring P)).symm i).2

def parentOf (P : Population X) : Fin (R.next P).size → Fin P.size :=
  fun i => ((Fintype.equivFin (R.Offspring P)).symm i).1

def probOf (P : Population X) : Fin (R.next P).size → ℝ := fun i =>
  R.prob (P.state ((Fintype.equivFin (R.Offspring P)).symm i).1)
    ((Fintype.equivFin (R.Offspring P)).symm i).2

lemma fiber_sum (P : Population X) (w : Fin P.size → ℝ) (v : Fin P.size) :
    ∑ i, (if R.parentOf P i = v then R.probOf P i*w (R.parentOf P i) else 0) = w v := by
  classical
  let e := Fintype.equivFin (R.Offspring P)
  have heq : ∑ i, (if R.parentOf P i = v then R.probOf P i*w (R.parentOf P i) else 0) =
      ∑ p : R.Offspring P, if p.1=v then R.prob (P.state p.1) p.2*w p.1 else 0 := by
    apply Fintype.sum_equiv e.symm
    intro i
    rfl
  rw [heq]
  change (∑ p : (Σ u : Fin P.size, Fin (R.degree (P.state u))),
    if p.1=v then R.prob (P.state p.1) p.2*w p.1 else 0) = w v
  rw [Fintype.sum_sigma]
  simp_rw [sum_ite_irrel,← sum_mul,R.prob_sum,one_mul,sum_const_zero]
  simp

def generation (x : X) : ℕ → Population X
  | 0 => ⟨1,fun _ => x⟩
  | n+1 => R.next (generation x n)

def weights (x : X) : (n : ℕ) → Fin (R.generation x n).size → ℝ
  | 0, _ => 1
  | n+1, i => R.probOf (R.generation x n) i *
      weights x n (R.parentOf (R.generation x n) i)

lemma weights_pos (x : X) : ∀ n i, 0 < R.weights x n i := by
  intro n
  induction n with
  | zero => intro i; exact zero_lt_one
  | succ n ih =>
    intro i
    exact mul_pos (R.prob_pos _ _) (ih _)

def flow (x : X) (good : X → Prop) : FiniteFlow where
  size n := (R.generation x n).size
  parent n := R.parentOf (R.generation x n)
  weight := R.weights x
  nonneg n i := (R.weights_pos x n i).le
  root_mass := by
    change (∑ _ : Fin 1, (1:ℝ)) = 1
    simp
  conserves n v := (R.fiber_sum (R.generation x n) (R.weights x n) v).symm
  good n v := good ((R.generation x n).state v)

end Subdivision

namespace FiniteFlow

variable (T : FiniteFlow)

def ancestor (n : ℕ) : (m : ℕ) → Fin (T.size (n+m)) → Fin (T.size n)
  | 0, v => v
  | m+1, v => ancestor n m (T.parent (n+m) v)

end FiniteFlow

end CannonFlow

end

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonAnnular CannonMagnification CannonFlow

attribute [local instance] Classical.propDecidable

structure SourceConstruction {X : Type*} [MetricSpace X] (f : X → ℝ) (x₀ : X)
    (ε ell c₀ A B H ρ : ℝ) (qdim n : ℕ) where
  kmin : ℕ
  small : ∀ k ≥ kmin, radius ell k ≤ ρ
  root : SourceNode f x₀ ε ell c₀ (B+1) kmin
  root_depth : root.depth=kmin
  pattern_small : c₀*radius ell (160*(qdim+1)*n) ≤ 1
  κ : ℝ
  κpos : 0 < κ
  Y : SourceNode f x₀ ε ell c₀ (B+1) kmin → Finset X
  Yloc : ∀ v, ∀ y ∈ Y v, (A-1)*radius ell v.depth ≤ dist y v.center ∧
    dist y v.center ≤ (B+1)*radius ell v.depth
  Ysep : ∀ v, ∀ y ∈ Y v, ∀ z ∈ Y v, y ≠ z →
    radius ell (v.depth+160*(qdim+1)*n) ≤ dist y z
  Ynet : ∀ v w, (A-1)*radius ell v.depth ≤ dist w v.center →
    dist w v.center ≤ (B+1)*radius ell v.depth →
    ∃ y ∈ Y v, dist w y ≤ radius ell (v.depth+160*(qdim+1)*n)
  rule : Subdivision (SourceNode f x₀ ε ell c₀ (B+1) kmin)
  child_depth : ∀ v i, (rule.child v i).depth=v.depth+160*(qdim+1)*n
  child_move : ∀ v i, dist (rule.child v i).center v.center ≤ (B+1)*radius ell v.depth
  child_sep : ∀ v i j, i ≠ j → H*radius ell (v.depth+160*(qdim+1)*n) <
    dist (rule.child v i).center (rule.child v j).center
  child_linear : ∀ v i, rule.prob v i*v.length ≤ Real.exp (-ell*n)*(rule.child v i).length
  child_quadratic : ∀ v i, rule.prob v i*v.length^2 ≤
    (if LiteralGood f (Y v) c₀ (radius ell (v.depth+160*(qdim+1)*n)) v.a v.b κ
      then Real.exp (8*(qdim+1)*ell*n) else Real.exp (-((80*(qdim+1):ℝ)*ell*n)))*
        (rule.child v i).length^2
  child_length_le : ∀ v i, (rule.child v i).length ≤ v.length

end CannonNode

end

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_State
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section

namespace CannonNode.SourceConstruction

open Set Metric Finset Filter Topology CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

abbrev state (g : ℕ) := (S.rule.generation S.root g).state

abbrev good (v : SourceNode f x₀ ε ell c₀ (B+1) S.kmin) :=
  LiteralGood f (S.Y v) c₀ (radius ell (v.depth+160*(qdim+1)*n)) v.a v.b S.κ

noncomputable def flow := S.rule.flow S.root S.good

abbrev center (g : ℕ) (i : Fin (S.flow.size g)) := (S.state g i).center

abbrev len (g : ℕ) (i : Fin (S.flow.size g)) := (S.state g i).length

abbrev scale (g : ℕ) := radius ell (S.kmin+160*(qdim+1)*n*g)

end CannonNode.SourceConstruction

end

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_Oscillation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section

section

open Set MeasureTheory
open scoped BigOperators

namespace CannonCrossEnergy

variable {X : Type*} [TopologicalSpace X]

def oscillation (f : X → ℝ) (A : Set X) : ℝ :=
  sSup (f '' A) - sInf (f '' A)

def rangeInterval (f : X → ℝ) (A : Set X) : Set ℝ :=
  Icc (sInf (f '' A)) (sSup (f '' A))

end CannonCrossEnergy

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Dirac
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal

namespace CannonAtomic

attribute [local instance] Classical.propDecidable

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

def dirac (p : X) : FiniteMeasure X := ⟨Measure.dirac p,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def atomic (p : ι → X) (w : ι → ℝ) (M : ℝ) (_hM : 0 ≤ M) : FiniteMeasure X :=
  ∑ i, Real.toNNReal (M*(w i)^2) • dirac (p i)

end CannonAtomic

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ClosedAnnulus
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal

open Set Filter Metric Topology

namespace CannonAnnularCompactness

variable {X : Type*} [PseudoMetricSpace X]

def closedAnnulus (x : X) (R : ℝ) : Set X :=
  {y | R/4 ≤ dist y x ∧ dist y x ≤ 4*R}

end CannonAnnularCompactness

open Set Filter Topology

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_InteriorScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonApprox

open CannonGrid CannonChart CannonCharts CannonAnnular
open Set Metric Filter Topology

def interiorScalar {X ι : Type*} [MetricSpace X] [Fintype ι]
    (e : Square → X) (he : IsEmbedding e) (p : ι → X) (r : ℝ)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hadm : Admissible (fun i => e ⁻¹' ball (p i) (2*r)) ρ) (m : ℕ) (hm : 0 < m) :
    C(interior (range e),ℝ) :=
  onInterior e he ⟨scalar (fun i => e ⁻¹' ball (p i) (2*r)) ρ m hm,
    (scalar_properties _ ρ hρ hadm m hm).1⟩

end CannonApprox

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_MeshEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators

namespace CannonApprox

open Set Metric CannonCrossEnergy

def meshEnergy {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (F : X → ℝ) (K : Set X) : ℝ := by
  classical
  exact ∑ i : {i : ι // (ball (p i) (2*r) ∩ K).Nonempty},
    (oscillation F (closedBall (p i.val) (J*r)))^2

end CannonApprox

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Exhaustion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonDiagonal

open Set Metric Filter Topology CannonApprox

def exhaustion {X : Type*} [MetricSpace X] (b : X) (j : ℕ) : Set X :=
  {x | 1/((j:ℝ)+1) ≤ dist x b}

end CannonDiagonal

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_EscapingLevelsAlong
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonComparison

open Set Metric Filter Topology CannonApprox

def EscapingLevelsAlong {X : Type*} [MetricSpace X]
    (f : ℕ → X → ℝ) (W : X → ℝ) (b : X) : Prop :=
  ∀ v w : X, ∀ γ : Path v w, ∀ a d ρ : ℝ,
    range γ ⊆ ({b}ᶜ : Set X) → W v < a → a < d → d < W w → 0 < ρ →
    ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∃ D : Set X,
      IsCompact D ∧ IsConnected D ∧ (D ∩ range γ).Nonempty ∧
      (∀ x ∈ D, f n x = t) ∧ ∃ z ∈ D, dist z b < ρ

end CannonComparison

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_RecordData
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
namespace CannonApprox

open CannonMagnification CannonCrossEnergy Set Metric Filter Topology MeasureTheory

structure RecordData {X Γ : Type*} [MetricSpace X] [MeasurableSpace X]
    (action : Γ → X ≃ₜ X) (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (p : ∀ n, ι n → X) (r : ℕ → ℝ) where
  Ω : Set X
  isOpen : IsOpen Ω
  f : X → ℝ
  continuous : ContinuousOn f Ω
  unit : ∀ x ∈ Ω, f x ∈ Icc (0:ℝ) 1
  x₀ : X
  x₀mem : x₀ ∈ Ω
  variation : ∀ s : ℝ, 0 < s → ∃ y ∈ ball x₀ s, f y ≠ f x₀
  z₀ : X
  z₀not : z₀ ∉ Ω
  ν : FiniteMeasure X
  E : ℝ
  E_nonneg : 0 ≤ E
  Cμ : ℝ
  Cμ_pos : 0 < Cμ
  measure_bound : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ s₀ : ℝ, 0 < s₀ ∧
    ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ x ∈ K,
      closedBall x s ⊆ Ω ∧ (CannonCrossEnergy.oscillation f (closedBall x s))^2 ≤
        E*(ν (closedBall x (Cμ*s)) : ℝ)
  level : ℝ → Set X
  diameter : ℝ
  diameter_pos : 0 < diameter
  level_properties : ∀ t ∈ Ioo (0:ℝ) 1,
    IsCompact (level t) ∧ IsConnected (level t) ∧ diameter ≤ diam (level t) ∧
      ∀ y ∈ level t, y ∈ Ω → f y=t
  level_hits : ∀ t ∈ Ioo (0:ℝ) 1, ∀ u v, ∀ γ : Path u v, range γ ⊆ Ω →
    f u < t → t < f v → (level t ∩ range γ).Nonempty
  H : ℕ → X → ℝ
  H_unit : ∀ n x, H n x ∈ Icc (0:ℝ) 1
  H_continuous : ∀ n, ContinuousOn (H n) Ω
  H_limit : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H f atTop K
  H_diameter : ℝ
  H_diameter_pos : 0 < H_diameter
  H_level : ∀ n t, t ∈ Ioo (0:ℝ) 1 → ∃ K : Set X,
    IsCompact K ∧ IsConnected K ∧ H_diameter ≤ diam K ∧ (∀ y ∈ K, H n y=t) ∧
    ∀ u v, ∀ γ : Path u v, range γ ⊆ Ω → H n u < t → t < H n v →
      (K ∩ range γ).Nonempty
  energy : ∀ g : Γ, ∀ K : Set X, IsCompact K → K ⊆ action g '' Ω →
    ∀ J : ℝ, 0 < J → Tendsto (fun n => meshEnergy (p n) (r n) J
      (H n ∘ (action g).symm) K) atTop (𝓝 0)

end CannonApprox

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_FlowSetup
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
namespace CannonApprox

open Set Metric Filter Topology MeasureTheory CannonNode CannonMagnification CannonAnnular

structure FlowSetup {X Γ : Type*} [MetricSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ} (R : RecordData action ι p r)
    (ell L CE LE : ℝ) (Q : ℕ) where
  ε : ℝ
  εpos : 0 < ε
  local_domain : closedBall R.x₀ (2*ε) ⊆ R.Ω
  c₀ : ℝ
  A : ℝ
  B : ℝ
  cPat : ℝ
  H : ℝ
  core : 2*L+2 < c₀
  inner : A=4*L*c₀+20
  outer : B=A+10
  pattern : cPat=2*CE*(2*L)/(A-2)^2
  pattern_pos : 0 < cPat
  margin : 12*cPat*(B+2)^2*LE < c₀
  separation : max (4*(B+1)) (max (4*R.Cμ*c₀) 2) < H
  ρ : ℝ
  ρpos : 0 < ρ
  small : (B+2)*ρ ≤ ε
  cutoff : ρ ≤ ε/2
  n : ℕ
  npos : 0 < n
  decay : radius ell (160*(Q+1)*n) < 1/4
  S : SourceConstruction R.f R.x₀ ε ell c₀ A B H ρ Q n
  energy : ∀ g, ∑ i, (S.len g i)^2 ≤ R.E * (R.ν univ : ℝ)
  good : ∀ N : ℕ, ∃ g ≥ N, (1/2:ℝ) ≤ S.flow.goodMass g

end CannonApprox

end

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_FlowPatternSetup
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section

namespace CannonApprox

open Set Metric CannonNode CannonMagnification

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

structure FlowPatternSetup (T : RecordData action ι p r) {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q)
    (h : ∀ g, Fin (F.S.flow.size g) → X ≃ₜ X) where
  net : Finset X
  net_nonempty : net.Nonempty
  pat : ∀ g, Fin (F.S.flow.size g) → Bool → net
  data : ∀ g i, F.S.good (F.S.state g i) →
    ∃ v₀ v₁ : Bool → X, ∃ γ : ∀ s, Path (v₀ s) (v₁ s),
      (∀ s, range (γ s) ⊆ closedBall ((pat g i s : net) : X)
        (3*F.cPat*radius ell (160*(Q+1)*F.n))) ∧
      (∀ s, F.S.κ*F.S.len g i ≤ T.f ((h g i).symm (v₁ s))-T.f ((h g i).symm (v₀ s))) ∧
      (∀ s, (h g i).symm '' closedBall ((pat g i s : net) : X)
        (3*F.cPat*radius ell (160*(Q+1)*F.n)) ⊆ closedBall (F.S.center g i) ((F.B+2)*F.S.scale g)) ∧
      ∀ z ∈ closedBall ((pat g i false : net) : X) (3*F.cPat*radius ell (160*(Q+1)*F.n)),
        ∀ w ∈ closedBall ((pat g i true : net) : X) (3*F.cPat*radius ell (160*(Q+1)*F.n)),
          T.f ((h g i).symm z)+F.S.len g i/4 ≤ T.f ((h g i).symm w)

end CannonApprox

end

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_FlowPaid
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
namespace CannonApprox

open Set Metric Filter Topology MeasureTheory CannonNode CannonMagnification Finset

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

def FlowPaid {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (gi : ∀ g, Fin (F.S.flow.size g) → Γ)
    (c Cs Ci d : ℝ) (g : ℕ) (i j : Fin (F.S.flow.size g)) : Prop :=
  ∃ B : Set X, MeasurableSet B ∧ c*(F.S.len g i)^2 ≤ (T.ν B:ℝ) ∧
    B ⊆ closedBall (F.S.center g i) (Cs*F.S.scale g/d) ∧
    action (gi g i) '' B ⊆ closedBall (action (gi g j) T.z₀) (Ci*F.S.scale g)

end CannonApprox

end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_ApproxSelfSimilar
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonGeometry
open Set Metric

variable (X : Type*) [MetricSpace X]

def ApproxSelfSimilar : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ diam (univ : Set X) →
    ∃ f : X ≃ₜ X, ∀ y ∈ ball x r, ∀ z ∈ ball x r,
      dist (f y) (f z)*r ≤ C*dist y z ∧ dist y z ≤ C*dist (f y) (f z)*r

end CannonGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_EventualRelativeShrink
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
namespace CannonDistortion
open Set
open scoped NNReal

def maxIso {A B : Type*} [LinearOrder A] [LinearOrder B]
    (f g : A ≃o B) : A ≃o B :=
  StrictMono.orderIsoOfSurjective (fun x => max (f x) (g x))
    (fun a b hab => max_lt_iff.mpr ⟨(f.strictMono hab).trans_le (le_max_left _ _),
      (g.strictMono hab).trans_le (le_max_right _ _)⟩) (by
    intro y
    rcases le_total (f.symm y) (g.symm y) with h|h
    · refine ⟨f.symm y,?_⟩
      change max (f (f.symm y)) (g (f.symm y))=y
      rw [f.apply_symm_apply]
      exact max_eq_left ((g.monotone h).trans_eq (g.apply_symm_apply y))
    · refine ⟨g.symm y,?_⟩
      change max (f (g.symm y)) (g (g.symm y))=y
      rw [g.apply_symm_apply]
      exact max_eq_right ((f.monotone h).trans_eq (f.apply_symm_apply y)))

@[simp] lemma maxIso_apply {A B : Type*} [LinearOrder A] [LinearOrder B]
    (f g : A ≃o B) (x : A) : maxIso f g x=max (f x) (g x) := rfl

def powerGauge (α β t : ℝ) : ℝ := max (t^α) (t^β)

def powerIso (C : ℝ≥0) (hC : 0<C) (α β : ℝ) (hα : 0<α) (hβ : 0<β) : ℝ≥0 ≃o ℝ≥0 :=
  (maxIso (NNReal.orderIsoRpow α hα) (NNReal.orderIsoRpow β hβ)).trans (OrderIso.mulLeft₀ C hC)

end CannonDistortion

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
noncomputable section

noncomputable section
namespace CannonConformal
open Set Topology Metric

abbrev Form := Fin 3 → ℝ
def determinant (q : Form) : ℝ := q 0*q 2-(q 1)^2
def evaluate (q : Form) (x y : ℝ) : ℝ := q 0*x^2+2*q 1*x*y+q 2*y^2
def Positive (q : Form) : Prop := 0 < q 0 ∧ 0 < determinant q
def LowerBound (ε : ℝ) (q : Form) : Prop := ∀ x y : ℝ, ε*(x^2+y^2) ≤ evaluate q x y
def UpperBound (K : ℝ) (q : Form) : Prop := ∀ x y : ℝ, evaluate q x y ≤ K*(x^2+y^2)

end CannonConformal

end
end
end
end
section
noncomputable section
namespace CannonConformal
open Set MeasureTheory

variable {Γ X : Type*} [Group Γ] [MeasurableSpace X]

def orbitCore (A : Γ →* Equiv.Perm X) (S : Set X) : Set X :=
  {x | ∀ g : Γ, A g x ∈ S}

end CannonConformal

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_CauchySymbol
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

namespace CannonBeltrami

def cauchySymbol (z : ℂ) : ℂ := (Real.pi*Complex.I*z)⁻¹

def cauchyTransform (f : SchwartzMap ℂ ℂ) : ℂ → ℂ :=
  𝓕⁻ (fun z => cauchySymbol z*(𝓕 f) z)

end CannonBeltrami

namespace CannonBeltrami
open scoped RealInnerProductSpace

def smoothBeurling (f : SchwartzMap ℂ ℂ) : ℂ → ℂ :=
  smoothRepresentative (beurling (f.toLp 2))

def partialZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1-Complex.I*fderiv ℝ f z Complex.I)/2

def partialBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1+Complex.I*fderiv ℝ f z Complex.I)/2

end CannonBeltrami

namespace CannonBeltrami

lemma contDiff_partials {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialZ f) ∧ ContDiff ℝ ∞ (partialBar f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hx : ContDiff ℝ ∞ (fun z => fderiv ℝ f z 1) := hd.clm_apply contDiff_const
  have hy : ContDiff ℝ ∞ (fun z => fderiv ℝ f z Complex.I) := hd.clm_apply contDiff_const
  exact ⟨(hx.sub (contDiff_const.mul hy)).div_const 2,
    (hx.add (contDiff_const.mul hy)).div_const 2⟩

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_Beltrami
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

def beltrami (q : Form) : ℂ :=
  (⟨q 0-q 2,2*q 1⟩ : ℂ) / ((q 0+q 2+2*Real.sqrt (determinant q) : ℝ) : ℂ)

def coefficientForm (μ : ℂ) : Form :=
  ![(1+μ.re)^2+μ.im^2,2*μ.im,(1-μ.re)^2+μ.im^2]

end CannonConformal

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_TwoPointNormalize
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonBeltrami

def twoPointNormalize (F : ℂ ≃ₜ ℂ) : ℂ ≃ₜ ℂ where
  toFun z := (F z-F 0)/(F 1-F 0)
  invFun w := F.symm ((F 1-F 0)*w+F 0)
  left_inv z := by
    have hc : F 1-F 0 ≠ 0 := sub_ne_zero.mpr (fun h => one_ne_zero (F.injective h))
    simp [mul_div_cancel₀ _ hc]
  right_inv w := by
    have hc : F 1-F 0 ≠ 0 := sub_ne_zero.mpr (fun h => one_ne_zero (F.injective h))
    simp [hc]
  continuous_toFun := (F.continuous.sub continuous_const).div_const _
  continuous_invFun := F.symm.continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

@[simp] lemma twoPointNormalize_apply (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    twoPointNormalize F z=(F z-F 0)/(F 1-F 0) := rfl
@[simp] lemma twoPointNormalize_symm_apply (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    (twoPointNormalize F).symm z=F.symm ((F 1-F 0)*z+F 0) := rfl

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_ContinuousMemLpRestrict
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set Filter Topology Metric

namespace CannonBeltrami
open MeasureTheory Set Metric

lemma continuous_memLp_restrict_compact {f : ℂ → ℂ} (hf : Continuous f)
    {S : Set ℂ} (hS : IsCompact S) : MemLp f 2 (volume.restrict S) := by
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨B,hB⟩ := isBounded_iff_forall_norm_le.mp (hS.image hf).isBounded
  apply MemLp.of_bound hf.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
  exact hB _ ⟨z,hz,rfl⟩

end CannonBeltrami

noncomputable section
open Set Filter Topology

open MeasureTheory
open scoped ENNReal

namespace CannonHilbert
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma bounded_mul_memLp {μ ψ : X → ℂ} (hm : AEStronglyMeasurable μ ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖μ x‖ ≤ k) (hψ : MemLp ψ 2 ν) :
    MemLp (fun x => μ x*ψ x) 2 ν := by
  apply hψ.of_le_mul (c:=k) (hm.mul hψ.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖μ x*ψ x‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

end CannonHilbert

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_Mollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set Filter Topology Metric

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

namespace CannonBeltrami

def mollifier (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ)+1)
  rOut := 2 / ((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply (div_lt_div_iff_of_pos_right (by positivity)).mpr; norm_num

def mollify (μ : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  (mollifier n).normed volume ⋆[lsmul ℝ ℝ, volume] μ

end CannonBeltrami

namespace CannonBeltrami

def globalCutoff (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (n:ℝ)+1
  rOut := (n:ℝ)+2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_Increment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

namespace CannonBeltrami
open ContinuousLinearMap

def barProject : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1/2:ℂ) • ((apply ℝ ℂ (1:ℂ)) + Complex.I • (apply ℝ ℂ Complex.I))

end CannonBeltrami

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.StdSimplexCompat
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance instSubsingleton [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by
    intro a b
    ext m
    simp

variable [IsStrictOrderedRing R]

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => s.weights_nonneg i) (Finsupp.mem_support_iff.mpr hm)

instance instInhabited [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance instNonempty [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

end Semiring

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']

/-- The bijection between the one dimensional standard simplex and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, s.weights_nonneg 1, s.weights_apply_le_one 1⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · have := s.total_fin_two
      simp
      exact (eq_sub_of_add_eq this).symm
    · simp
  right_inv t := by
    ext
    simp [Finsupp.single_apply]

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by
  ext
  simp

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

section ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {I : Type*}

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  ext : 1
  simp [weights_iConvexComb, Finsupp.smul_single_one, Finsupp.sum_single]

end ConvexSpace

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, Finset.sum_filter]
  simp only [this]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- The topology on `StdSimplex R M`: the supremum of the coinduced topologies for the maps
`StdSimplex.map f : StdSimplex R ι → StdSimplex R M` with `ι` finite. When `M` is finite it is the
topology induced by the embedding `StdSimplex R M → (M → R)`. -/
noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

namespace StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, the barycenter of a nonempty finite subset `S`. -/
@[simps -isSimp]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m (S.card : K)⁻¹)
  nonneg := Finset.sum_nonneg (fun m _ => by
    classical
    intro i
    rw [Finsupp.single_apply]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hS).ne')

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Center
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

def center (S : Set Form) : Form :=
  Classical.epsilon (fun q => q ∈ closedConvexHull ℝ S ∧
    IsMaxOn determinant (closedConvexHull ℝ S) q)

abbrev PlaneLinear := Fin 4 → ℝ

def planeDet (A : PlaneLinear) : ℝ := A 0*A 3-A 1*A 2

def adjugate (A : PlaneLinear) : PlaneLinear := ![A 3,-A 1,-A 2,A 0]

def pullForm (A : PlaneLinear) : Form →ₗ[ℝ] Form where
  toFun q := ![q 0*(A 0)^2+2*q 1*A 0*A 2+q 2*(A 2)^2,
    q 0*A 0*A 1+q 1*(A 0*A 3+A 1*A 2)+q 2*A 2*A 3,
    q 0*(A 1)^2+2*q 1*A 1*A 3+q 2*(A 3)^2]
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c q := by
    ext i
    fin_cases i <;> simp <;> ring

lemma planeDet_adjugate (A : PlaneLinear) : planeDet (adjugate A)=planeDet A := by
  simp [planeDet,adjugate]
  ring

lemma adjugate_adjugate (A : PlaneLinear) : adjugate (adjugate A)=A := by
  ext i
  fin_cases i <;> simp [adjugate]

lemma pullForm_adjugate (A : PlaneLinear) (q : Form) :
    pullForm (adjugate A) (pullForm A q)=(planeDet A)^2 • q := by
  ext i
  fin_cases i <;> simp [pullForm,adjugate,planeDet] <;> ring

def normalizedPull (A : PlaneLinear) : Form →ₗ[ℝ] Form :=
  |planeDet A|⁻¹ • pullForm A

lemma normalizedPull_apply (A : PlaneLinear) (q : Form) :
    normalizedPull A q=|planeDet A|⁻¹ • pullForm A q := rfl

lemma normalizedPull_adjugate (A : PlaneLinear) (hA : planeDet A ≠ 0) (q : Form) :
    normalizedPull (adjugate A) (normalizedPull A q)=q := by
  rw [normalizedPull_apply,normalizedPull_apply,map_smul,pullForm_adjugate,planeDet_adjugate]
  simp only [smul_smul]
  have ha : |planeDet A| ≠ 0 := abs_ne_zero.mpr hA
  have he : |planeDet A|⁻¹*(|planeDet A|⁻¹*(planeDet A)^2)=1 := by
    rw [← sq_abs (planeDet A)]
    field_simp
  rw [he,one_smul]

def pullbackEquiv (A : PlaneLinear) (hA : planeDet A ≠ 0) : Form ≃L[ℝ] Form :=
  LinearEquiv.toContinuousLinearEquiv
    { normalizedPull A with
      invFun := normalizedPull (adjugate A)
      left_inv := normalizedPull_adjugate A hA
      right_inv := by
        intro q
        change normalizedPull A (normalizedPull (adjugate A) q)=q
        simpa only [adjugate_adjugate] using
          normalizedPull_adjugate (adjugate A) (by simpa only [planeDet_adjugate] using hA) q }

def planeMul (A B : PlaneLinear) : PlaneLinear :=
  ![A 0*B 0+A 1*B 2,A 0*B 1+A 1*B 3,A 2*B 0+A 3*B 2,A 2*B 1+A 3*B 3]

end CannonConformal

end
end
noncomputable section
namespace CannonConformal

def roundForm : Form := ![1,0,1]

end CannonConformal

end
end
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def combination (q : ι → Form) : (ι → ℝ) →ₗ[ℝ] Form :=
  ∑ i, (LinearMap.proj i).smulRight (q i)

abbrev FiniteForms (ε : ℝ) (ι : Type*) := {q : ι → Form | ∀ i, LowerBound ε (q i)}

end Finite

open Filter

def orbitPrefix (q : ℕ → Form) (n : ℕ) : Set Form := range (fun i : Fin (n+1) => q i.val)

open MeasureTheory

end CannonConformal

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_LinearZ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
namespace CannonConformal
open Complex

def linearZ (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1-Complex.I*A Complex.I)/2
def linearBar (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1+Complex.I*A Complex.I)/2

end CannonConformal

end
end

end
end
end
end
end
end

end OAI
end


