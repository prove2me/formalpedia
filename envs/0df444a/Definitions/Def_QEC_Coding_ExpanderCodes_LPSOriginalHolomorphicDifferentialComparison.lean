-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:52:26.492711+00:00
-- url     : https://prove2.me/theorems/260b181c-1f14-4136-b92d-d596fbadc436
-- title:
--   LPSOriginal Holomorphic Differential Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Holomorphic Differential Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_lifts_eventually_smul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspChange_translation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferentialLinearMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferential_projection_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_dense
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_openEmbedding
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_projection_contMDiff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_deriv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwo_slash_deriv
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
abbrev LPSOriginalHolomorphicCovectorSections (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  letI := lpsOriginalFilledTopology N
  letI := lpsOriginalFilledChartedSpace N hN
  letI := lpsOriginalFilled_isManifold N hN
  ContMDiffSection 𝓘(ℂ) (ℂ→L[ℂ]ℂ) ω
    (fun x : LPSOriginalFilledCurve N =>
      TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ x)
abbrev lpsOriginalHolomorphicCovectorProjection (N : ℕ) : ℍ → LPSOriginalFilledCurve N :=
  fun τ => Sum.inl (Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ)
lemma lpsOriginalHolomorphicCovectorProjection_contMDiff
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (lpsOriginalHolomorphicCovectorProjection N) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro τ
  exact lpsOriginalFilled_projection_contMDiff N hN τ
def lpsOriginalHolomorphicCovectorPullback (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) : ℍ → ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun τ => sectionForm (lpsOriginalHolomorphicCovectorProjection N τ)
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) τ (1:ℂ))
def lpsOriginalHolomorphicCovectorPullbackLinearMap
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ] (ℍ → ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  refine { toFun := lpsOriginalHolomorphicCovectorPullback N hN
           map_add' := ?_
           map_smul' := ?_ }
  · intro sectionForm ξ
    funext τ
    rfl
  · intro c sectionForm
    funext τ
    rfl
lemma lpsOriginalCovector_localInverse_deriv_ne_zero
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (σ τ : ℍ)
    (hs : Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ ∈
      ((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ).source) :
    let e := (lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ
    let proj := Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    deriv (fun z : ℂ => (e (proj (UpperHalfPlane.ofComplex z)) : ℂ)) τ ≠ 0 := by
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  let e := hf.localInverseAt σ
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let u : ℂ → ℍ := UpperHalfPlane.ofComplex
  let v : ℂ → ℍ := fun z => e (proj (u z))
  have hu : ContinuousAt u (τ : ℂ) :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) τ.im_pos).continuousAt
  have hproj : Continuous proj := continuous_quot_mk
  have ht : proj (u τ) = proj τ := by simp [u]
  have hv : ContinuousAt v (τ : ℂ) := by
    apply (e.continuousAt (by simpa only [ht] using hs)).comp
    exact hproj.continuousAt.comp hu
  have he : (fun z => proj (v z)) =ᶠ[𝓝 (τ : ℂ)] (fun z => proj (u z)) := by
    have hsrc : ∀ᶠ z in 𝓝 (τ : ℂ), proj (u z) ∈ e.source := by
      apply hproj.continuousAt.comp hu
      change e.source ∈ 𝓝 (proj (u τ))
      exact e.open_source.mem_nhds (by simpa only [ht] using hs)
    filter_upwards [hsrc] with z hz
    exact hf.apply_localInverseAt_of_mem hz
  obtain ⟨γ, hγ⟩ := lpsGamma0_lifts_eventually_smul N hN u v τ hu hv he
  have hec : (fun z => (v z : ℂ)) =ᶠ[𝓝 (τ : ℂ)]
      (fun z => (γ.val • UpperHalfPlane.ofComplex z : ℍ)) := by
    filter_upwards [hγ] with z hz
    exact congrArg UpperHalfPlane.coe hz
  have hdet : γ.val.val.det = 1 := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg Units.val (Subgroup.HasDetOne.det_eq γ.property)
  change deriv (fun z => (v z : ℂ)) τ ≠ 0
  rw [hec.deriv_eq]
  exact UpperHalfPlane.deriv_smul_ne_zero (by rw [hdet]; norm_num) τ
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constant unit tangent vector is an analytic section on the upper half-plane. -/
lemma lpsOriginalCovector_unitTangent_contMDiff :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω
      (fun τ : ℍ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ)) τ (show TangentSpace 𝓘(ℂ) τ from (1 : ℂ))) := by
  intro τ
  apply (Bundle.contMDiffAt_section (F := ℂ) (E := TangentSpace (M := ℍ) 𝓘(ℂ)) τ).mpr
  have he : (fun σ : ℍ =>
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) τ
        (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ)) σ (show TangentSpace 𝓘(ℂ) σ from (1 : ℂ)))).2) =
      fun _ => (1 : ℂ) := by
    funext σ
    exact (tangentBundleCore 𝓘(ℂ) ℍ).coordChange_self
      (achart ℂ σ) σ (mem_achart_source ℂ σ) (1 : ℂ)
  rw [he]
  exact contMDiffAt_const
lemma lpsOriginalHolomorphicCovectorPullback_contMDiff
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (lpsOriginalHolomorphicCovectorPullback N hN sectionForm) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  have hp := lpsOriginalHolomorphicCovectorProjection_contMDiff N hN
  have ht := hp.contMDiff_tangentMap (m := ω) (by simp)
  have hv := ht.comp lpsOriginalCovector_unitTangent_contMDiff
  have hsectionForm := sectionForm.contMDiff.comp hp
  have hh := hsectionForm.clm_bundle_apply hv
  intro τ
  exact ((Bundle.contMDiffAt_totalSpace.mp (hh τ)).2 : _)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The manifold derivative of a positive-determinant Mobius action is its ordinary derivative. -/
lemma lpsOriginalCovector_Mobius_mfderiv
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (τ : ℍ) (v : ℂ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun σ : ℍ => g • σ) τ v =
      deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ → ℂ) τ * v := by
  have hm := UpperHalfPlane.mdifferentiable_smul hg τ
  rw [mfderiv, if_pos hm]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  change (fderiv ℂ (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ → ℂ) τ) v = _
  exact fderiv_eq_deriv_mul
lemma lpsOriginalHolomorphicCovectorProjection_Gamma0
    (N : ℕ) (g : GL (Fin 2) ℝ)
    (hg : g ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    lpsOriginalHolomorphicCovectorProjection N ∘ (fun τ : ℍ => g • τ) =
      lpsOriginalHolomorphicCovectorProjection N := by
  funext τ
  apply congrArg Sum.inl
  apply Quotient.eq.mpr
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨⟨g, hg⟩, rfl⟩
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback of an arbitrary analytic covector satisfies the genuine weight-two slash law. -/
lemma lpsOriginalHolomorphicCovectorPullback_slash
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN)
    (g : GL (Fin 2) ℝ)
    (hg : g ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (lpsOriginalHolomorphicCovectorPullback N hN sectionForm ∣[(2 : ℤ)] g) =
      lpsOriginalHolomorphicCovectorPullback N hN sectionForm := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  have hdet : g.val.det = 1 := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg Units.val (Subgroup.HasDetOne.det_eq hg)
  have hpos : 0 < g.val.det := by rw [hdet]; norm_num
  have hp := lpsOriginalHolomorphicCovectorProjection_contMDiff N hN
  have he := lpsOriginalHolomorphicCovectorProjection_Gamma0 N g hg
  funext τ
  rw [lpsWeightTwo_slash_deriv _ g hpos τ]
  have hd := mfderiv_comp_apply τ ((hp (g • τ)).mdifferentiableAt (by decide))
    (UpperHalfPlane.mdifferentiable_smul hpos τ) (1 : ℂ)
  rw [he, lpsOriginalCovector_Mobius_mfderiv _ hpos, mul_one] at hd
  have heτ := congrFun he τ
  change lpsOriginalHolomorphicCovectorProjection N (g • τ) =
    lpsOriginalHolomorphicCovectorProjection N τ at heτ
  let d : ℂ := deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ → ℂ) τ
  have hscalar : mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N)
      (g • τ) d = d • mfderiv 𝓘(ℂ) 𝓘(ℂ)
        (lpsOriginalHolomorphicCovectorProjection N) (g • τ) (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N)
        (g • τ)).map_smul d (1 : ℂ)
  change mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) τ (1 : ℂ) =
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) (g • τ) d at hd
  rw [hscalar] at hd
  have hv := congrArg (fun v : ℂ => sectionForm
    (lpsOriginalHolomorphicCovectorProjection N (g • τ)) v) hd.symm
  rw [map_smul] at hv
  have heval := congrArg (fun x : LPSOriginalFilledCurve N => sectionForm x
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) τ (1 : ℂ))) heτ
  simpa only [lpsOriginalHolomorphicCovectorPullback, d, smul_eq_mul, mul_comm] using
    hv.trans heval
lemma lpsOriginalCovector_qParam_add (w : ℝ) (z u : ℂ) :
    Function.Periodic.qParam w (z + u) =
      Function.Periodic.qParam w u * Function.Periodic.qParam w z := by
  simp only [Function.Periodic.qParam, mul_add, add_div, Complex.exp_add]
  exact mul_comm _ _
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any integral cusp representative gives the preferred filled cusp chart up to nonzero phase. -/
lemma lpsOriginalCovector_cusp_phase
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    letI := lpsOriginalFilledTopology N
    let c := lpsOriginalCuspOrbit N ρ
    let r := lpsOriginalCuspRepresentative N c
    let w := (lpsOriginalCuspGroup N r).strictWidthInfty
    ∃ α : ℂ, α ≠ 0 ∧ ∀ σ : {τ : ℍ // 1 < τ.im},
      Sum.inl (lpsOriginalCuspProjection N ρ σ) =
        (lpsOriginalFilledCuspChart N c).symm
          (α * Function.Periodic.qParam w (σ.val : ℂ)) := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  obtain ⟨g,hg,x,hx⟩ := lpsOriginalCuspChange_translation N r ρ
    (lpsOriginalCuspRepresentative_orbit N c)
  let d := (Matrix.SpecialLinearGroup.mapGL ℝ r)⁻¹ * g *
    Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let α := Function.Periodic.qParam w (x : ℂ)
  refine ⟨α,Function.Periodic.qParam_ne_zero _,?_⟩
  intro σ
  have hi : 1 < (d • σ.val).im := by
    rw [lpsSignedTranslation_im d x hx]
    exact σ.property
  let τ : {τ : ℍ // 1 < τ.im} := ⟨d • σ.val,hi⟩
  have hp : lpsOriginalCuspProjection N r τ =
      lpsOriginalCuspProjection N ρ σ := by
    apply Quotient.eq.mpr
    rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
    refine ⟨⟨g,hg⟩,?_⟩
    change g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ • σ.val) =
      Matrix.SpecialLinearGroup.mapGL ℝ r • (d • σ.val)
    simp only [d,mul_smul,smul_inv_smul]
  have ht : (τ.val : ℂ) = (σ.val : ℂ)+(x : ℂ) := by
    change ((d • σ.val : ℍ) : ℂ) = _
    dsimp only [d]
    rcases hx with hplus | hminus
    · rw [hplus,lpsUpperRight_smul_coe]
    · rw [hminus,UpperHalfPlane.neg_smul,lpsUpperRight_smul_coe]
  let e := lpsOriginalFilledCuspChart N c
  have hs : Sum.inl (lpsOriginalCuspProjection N r τ) ∈ e.source := ⟨τ,rfl⟩
  have hq : e (Sum.inl (lpsOriginalCuspProjection N r τ)) =
      α * Function.Periodic.qParam w (σ.val : ℂ) := by
    change lpsOriginalFilledCuspPartialEquiv N r
      (Sum.inl (lpsOriginalCuspProjection N r τ)) = _
    rw [lpsOriginalFilledCuspPartialEquiv_projection,ht,
      lpsOriginalCovector_qParam_add]
  rw [←hp,← e.left_inv hs,hq]
def lpsOriginalHolomorphicCovectorChartCoefficient
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN)
    (x : LPSOriginalFilledCurve N) : ℂ → ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun z => ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
    (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ)
    x ((chartAt ℂ x).symm z) x ((chartAt ℂ x).symm z)
    (sectionForm ((chartAt ℂ x).symm z)) (1 : ℂ)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A native analytic covector has analytic coefficient at the center of any actual chart. -/
lemma lpsOriginalHolomorphicCovectorChartCoefficient_analytic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN)
    (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    AnalyticAt ℂ (lpsOriginalHolomorphicCovectorChartCoefficient N hN sectionForm x)
      (chartAt ℂ x x) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let K : LPSOriginalFilledCurve N → ℂ := fun y =>
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y (sectionForm y) (1 : ℂ)
  have hcoord := (contMDiffAt_hom_bundle _).mp (sectionForm.contMDiff x)
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω K x :=
    hcoord.2.clm_apply (contMDiffAt_const (c := (1 : ℂ)))
  have hx : chartAt ℂ x x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hi := (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := x)).contMDiffAt
    ((chartAt ℂ x).open_target.mem_nhds hx)
  have hg' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω K ((chartAt ℂ x).symm (chartAt ℂ x x)) := by
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    exact hg
  have hh := hg'.comp (chartAt ℂ x x) hi
  exact (contMDiffAt_iff_contDiffAt.mp hh).analyticAt
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation of a native analytic covector agrees with its coefficient times the chart derivative. -/
lemma lpsOriginalHolomorphicCovectorChart_evaluate
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN)
    (x y : LPSOriginalFilledCurve N) (v : ℂ)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    sectionForm y v = lpsOriginalHolomorphicCovectorChartCoefficient N hN sectionForm x
      (chartAt ℂ x y) • (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y v : ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let P : ℂ →L[ℂ] ℂ := ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
    (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y (sectionForm y)
  let e := trivializationAt ℂ (TangentSpace (M := LPSOriginalFilledCurve N) 𝓘(ℂ)) x
  have he : e.continuousLinearMapAt ℂ y = mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hy]
    exact TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy
  have hv : P (e.continuousLinearMapAt ℂ y v) = sectionForm y v := by
    dsimp only [P]
    have ht : (trivializationAt ℂ (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x).continuousLinearMapAt ℂ y = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ _ ℂ y
    rw [ContinuousLinearMap.inCoordinates, ht, ContinuousLinearMap.id_comp]
    change sectionForm y (e.symmL ℂ y (e.continuousLinearMapAt ℂ y v)) = _
    rw [e.symmL_continuousLinearMapAt hy]
  have hscalar : P (e.continuousLinearMapAt ℂ y v) =
      P (1 : ℂ) • (e.continuousLinearMapAt ℂ y v : ℂ) := by
    let z : ℂ := e.continuousLinearMapAt ℂ y v
    have hz := P.map_smul z (1 : ℂ)
    change P (z * 1) = z * P (1 : ℂ) at hz
    rw [mul_one, mul_comm] at hz
    exact hz
  rw [← hv, hscalar, he]
  congr 1
  unfold lpsOriginalHolomorphicCovectorChartCoefficient
  rw [(chartAt ℂ x).left_inv hy]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback through an analytic map agrees with the actual chart coefficient and chain derivative. -/
lemma lpsOriginalHolomorphicCovectorChart_pullback
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN)
    (x : LPSOriginalFilledCurve N) (f : ℍ → LPSOriginalFilledCurve N) (τ : ℍ)
    (hf : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      letI := lpsOriginalFilled_isManifold N hN
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f τ)
    (hx : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      f τ ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    sectionForm (f τ) (mfderiv 𝓘(ℂ) 𝓘(ℂ) f τ (1 : ℂ)) =
      lpsOriginalHolomorphicCovectorChartCoefficient N hN sectionForm x (chartAt ℂ x (f τ)) •
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) ((chartAt ℂ x) ∘ f) τ (1 : ℂ) : ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  rw [mfderiv_comp_apply τ ((mdifferentiable_chart x).mdifferentiableAt hx)
    (hf.mdifferentiableAt (by decide))]
  exact lpsOriginalHolomorphicCovectorChart_evaluate N hN sectionForm x (f τ)
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) f τ (1 : ℂ)) hx
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive-determinant slash transforms are actual covector pullbacks through the Mobius action. -/
lemma lpsOriginalHolomorphicCovectorPullback_positive_slash
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN)
    (g : GL (Fin 2) ℝ) (hpos : 0 < g.val.det) (τ : ℍ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    (lpsOriginalHolomorphicCovectorPullback N hN sectionForm ∣[(2 : ℤ)] g) τ =
      sectionForm (lpsOriginalHolomorphicCovectorProjection N (g • τ))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ)
          (lpsOriginalHolomorphicCovectorProjection N ∘ (fun σ : ℍ => g • σ)) τ (1 : ℂ)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  rw [lpsWeightTwo_slash_deriv _ g hpos τ]
  have hp := lpsOriginalHolomorphicCovectorProjection_contMDiff N hN
  have hd := mfderiv_comp_apply τ ((hp (g • τ)).mdifferentiableAt (by decide))
    (UpperHalfPlane.mdifferentiable_smul hpos τ) (1 : ℂ)
  rw [lpsOriginalCovector_Mobius_mfderiv _ hpos, mul_one] at hd
  let d : ℂ := deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ → ℂ) τ
  have hscalar : mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N)
      (g • τ) d = d • mfderiv 𝓘(ℂ) 𝓘(ℂ)
        (lpsOriginalHolomorphicCovectorProjection N) (g • τ) (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N)
        (g • τ)).map_smul d (1 : ℂ)
  change mfderiv 𝓘(ℂ) 𝓘(ℂ)
      (lpsOriginalHolomorphicCovectorProjection N ∘ (fun σ : ℍ => g • σ)) τ (1 : ℂ) =
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) (g • τ) d at hd
  rw [hscalar] at hd
  have hv := congrArg (fun v : ℂ => sectionForm
    (lpsOriginalHolomorphicCovectorProjection N (g • τ)) v) hd
  rw [map_smul] at hv
  simpa only [lpsOriginalHolomorphicCovectorPullback, d, smul_eq_mul, mul_comm] using hv.symm
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual manifold derivative of a phased cusp parameter is the usual q-parameter derivative. -/
lemma lpsOriginalHolomorphicCovector_qParam_mfderiv
    (w : ℝ) (α : ℂ) (τ : ℍ) :
    id (α := ℂ) (mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun σ : ℍ => α * Function.Periodic.qParam w (σ : ℂ))
      τ (1 : ℂ)) = α * ((((2 : ℂ) * (Real.pi : ℂ) * I) / (w : ℂ)) *
        Function.Periodic.qParam w (τ : ℂ)) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ => α * Function.Periodic.qParam w z) :=
    by
    have hc' := ContDiff.const_smul α (Function.Periodic.contDiff_qParam (h := w) ω)
    simpa only [smul_eq_mul] using hc'.contMDiff
  have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun σ : ℍ => α * Function.Periodic.qParam w (σ : ℂ)) τ :=
    ((hc.comp UpperHalfPlane.contMDiff_coe) τ).mdifferentiableAt (by decide)
  simp only [id_eq]
  rw [mfderiv, if_pos hm]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  change (fderiv ℂ (fun z : ℂ => α * Function.Periodic.qParam w
    (UpperHalfPlane.ofComplex z : ℂ)) (τ : ℂ)) (1 : ℂ) = _
  have he : (fun z : ℂ => α * Function.Periodic.qParam w (UpperHalfPlane.ofComplex z : ℂ))
      =ᶠ[𝓝 (τ : ℂ)] (fun z : ℂ => α * Function.Periodic.qParam w z) := by
    filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
    rw [Function.comp_apply, id_eq] at hz
    rw [hz]
  rw [he.fderiv_eq, fderiv_eq_deriv_mul, mul_one]
  have hd := (Function.Periodic.differentiable_qParam (h := w) (τ : ℂ)).hasDerivAt.const_mul α
  rw [lpsQParam_deriv] at hd
  exact hd.deriv
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At every integral cusp, pullback has an analytic coefficient times the vanishing q-parameter. -/
lemma lpsOriginalHolomorphicCovector_cusp_formula
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) (ρ : SL(2,ℤ)) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    let c := lpsOriginalCuspOrbit N ρ
    let r := lpsOriginalCuspRepresentative N c
    let w := (lpsOriginalCuspGroup N r).strictWidthInfty
    ∃ α : ℂ, α ≠ 0 ∧ ∀ᶠ τ in UpperHalfPlane.atImInfty,
      (lpsOriginalHolomorphicCovectorPullback N hN sectionForm ∣[(2 : ℤ)]
        Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ =
      lpsOriginalHolomorphicCovectorChartCoefficient N hN sectionForm (Sum.inr c)
        (α * Function.Periodic.qParam w (τ : ℂ)) *
        (α * ((((2 : ℂ) * (Real.pi : ℂ) * I) / (w : ℂ)) *
          Function.Periodic.qParam w (τ : ℂ))) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  let x : LPSOriginalFilledCurve N := Sum.inr c
  let e := chartAt ℂ x
  let g := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let F : ℍ → LPSOriginalFilledCurve N :=
    lpsOriginalHolomorphicCovectorProjection N ∘ (fun τ : ℍ => g • τ)
  obtain ⟨α, hα, hphase⟩ := lpsOriginalCovector_cusp_phase N ρ
  refine ⟨α, hα, ?_⟩
  let qfun : ℍ → ℂ := fun τ => α * Function.Periodic.qParam w (τ : ℂ)
  have hb : ∀ τ : ℍ, 1 < τ.im → F τ = e.symm (qfun τ) := by
    intro τ ht
    exact hphase ⟨τ, ht⟩
  have hw : 0 < w := lpsOriginalCuspGroup_width_positive N r
  have hq : Tendsto qfun UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (UpperHalfPlane.qParam_tendsto_atImInfty hw)
  have h0 : (0 : ℂ) ∈ e.target := by
    have hz := (lpsOriginalFilledCuspChart N c).map_source
      (lpsOriginalFilledCuspChart_mem_cusp N c)
    rw [lpsOriginalFilledCuspChart_cusp] at hz
    exact hz
  have htarget : ∀ᶠ τ in UpperHalfPlane.atImInfty, qfun τ ∈ e.target :=
    hq (e.open_target.mem_nhds h0)
  have him : ∀ᶠ τ in UpperHalfPlane.atImInfty, 1 < τ.im := by
    change {τ : ℍ | 1 < τ.im} ∈ UpperHalfPlane.atImInfty
    rw [UpperHalfPlane.atImInfty_mem]
    refine ⟨2, ?_⟩
    intro τ ht
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ht
  have hpos : 0 < g.val.det := by
    simp only [g, ← Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.det_mapGL, Units.val_one, zero_lt_one]
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F :=
    (lpsOriginalHolomorphicCovectorProjection_contMDiff N hN).comp
      (UpperHalfPlane.contMDiff_smul hpos)
  have hqcont : Continuous qfun :=
    continuous_const.mul ((Function.Periodic.continuous_qParam (h := w)).comp
      UpperHalfPlane.continuous_coe)
  filter_upwards [him, htarget] with τ hτ hqt
  have heτ : e (F τ) = qfun τ := by
    rw [hb τ hτ, e.right_inv hqt]
  have hsource : F τ ∈ e.source := by
    rw [hb τ hτ]
    exact e.map_target hqt
  have he : e ∘ F =ᶠ[𝓝 τ] qfun := by
    have hi : ∀ᶠ σ in 𝓝 τ, 1 < σ.im :=
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds hτ
    have ht : ∀ᶠ σ in 𝓝 τ, qfun σ ∈ e.target :=
      hqcont.continuousAt (e.open_target.mem_nhds hqt)
    filter_upwards [hi, ht] with σ hσ hqσ
    rw [Function.comp_apply, hb σ hσ, e.right_inv hqσ]
  have hd := lpsOriginalHolomorphicCovector_qParam_mfderiv w α τ
  rw [lpsOriginalHolomorphicCovectorPullback_positive_slash N hN sectionForm g hpos τ]
  change sectionForm (F τ) (mfderiv 𝓘(ℂ) 𝓘(ℂ) F τ (1 : ℂ)) = _
  rw [lpsOriginalHolomorphicCovectorChart_pullback N hN sectionForm x F τ (hF τ) hsource]
  rw [heτ, he.mfderiv_eq]
  change lpsOriginalHolomorphicCovectorChartCoefficient N hN sectionForm x (qfun τ) *
      id (α := ℂ) (mfderiv 𝓘(ℂ) 𝓘(ℂ) qfun τ (1 : ℂ)) =
    lpsOriginalHolomorphicCovectorChartCoefficient N hN sectionForm x (qfun τ) *
      (α * ((((2 : ℂ) * (Real.pi : ℂ) * I) / (w : ℂ)) *
        Function.Periodic.qParam w (τ : ℂ)))
  exact congrArg
    (fun z : ℂ => lpsOriginalHolomorphicCovectorChartCoefficient N hN sectionForm x
      (qfun τ) * z) hd
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every integral cusp transform of the arbitrary covector pullback tends to zero. -/
lemma lpsOriginalHolomorphicCovector_cusp_vanishing
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) (ρ : SL(2,ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty
      (lpsOriginalHolomorphicCovectorPullback N hN sectionForm ∣[(2 : ℤ)]
        Matrix.SpecialLinearGroup.mapGL ℝ ρ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  let G := lpsOriginalHolomorphicCovectorChartCoefficient N hN sectionForm (Sum.inr c)
  obtain ⟨α, hα, hformula⟩ := lpsOriginalHolomorphicCovector_cusp_formula N hN sectionForm ρ
  have ha := lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN sectionForm (Sum.inr c)
  change AnalyticAt ℂ G (lpsOriginalFilledCuspChart N c (Sum.inr c)) at ha
  rw [lpsOriginalFilledCuspChart_cusp] at ha
  have hw : 0 < w := lpsOriginalCuspGroup_width_positive N r
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam w (τ : ℂ))
      UpperHalfPlane.atImInfty (𝓝 0) := UpperHalfPlane.qParam_tendsto_atImInfty hw
  have hqα : Tendsto (fun τ : ℍ => α * Function.Periodic.qParam w (τ : ℂ))
      UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hq
  have hG := ha.continuousAt.tendsto.comp hqα
  have hD : Tendsto (fun τ : ℍ => α * ((((2 : ℂ) * (Real.pi : ℂ) * I) / (w : ℂ)) *
        Function.Periodic.qParam w (τ : ℂ))) UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.mul hq)
  have ht : Tendsto (fun τ : ℍ => G (α * Function.Periodic.qParam w (τ : ℂ)) *
      (α * ((((2 : ℂ) * (Real.pi : ℂ) * I) / (w : ℂ)) *
        Function.Periodic.qParam w (τ : ℂ)))) UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using hG.mul hD
  have he : (lpsOriginalHolomorphicCovectorPullback N hN sectionForm ∣[(2 : ℤ)]
      Matrix.SpecialLinearGroup.mapGL ℝ ρ) =ᶠ[UpperHalfPlane.atImInfty]
      (fun τ : ℍ => G (α * Function.Periodic.qParam w (τ : ℂ)) *
        (α * ((((2 : ℂ) * (Real.pi : ℂ) * I) / (w : ℂ)) *
          Function.Periodic.qParam w (τ : ℂ)))) := hformula
  exact ht.congr' he.symm
lemma lpsOriginalHolomorphicCovector_zero_at_cusps
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN)
    {c : OnePoint ℝ}
    (hc : IsCusp c (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    c.IsZeroAt (lpsOriginalHolomorphicCovectorPullback N hN sectionForm) (2 : ℤ) := by
  have hΓ : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
    intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨γ, _, rfl⟩
    exact ⟨γ, rfl⟩
  have hcSL := IsCusp.mono hΓ hc
  obtain ⟨ρ, hρ⟩ := isCusp_SL2Z_iff'.mp hcSL
  apply (OnePoint.isZeroAt_iff_exists_SL2Z hcSL).mpr
  exact ⟨ρ, hρ.symm, lpsOriginalHolomorphicCovector_cusp_vanishing N hN sectionForm ρ⟩
def lpsOriginalHolomorphicCovectorCuspForm
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsOriginalHolomorphicCovectorPullbackLinearMap N hN sectionForm
  slash_action_eq' g hg := lpsOriginalHolomorphicCovectorPullback_slash N hN sectionForm g hg
  holo' := (lpsOriginalHolomorphicCovectorPullback_contMDiff N hN sectionForm).mdifferentiable (by decide)
  zero_at_cusps' hc := lpsOriginalHolomorphicCovector_zero_at_cusps N hN sectionForm hc
lemma lpsOriginalHolomorphicCovectorCuspForm_apply
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) (τ : ℍ) :
    lpsOriginalHolomorphicCovectorCuspForm N hN sectionForm τ =
      lpsOriginalHolomorphicCovectorPullback N hN sectionForm τ := rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every interior chart of the original filled curve has nonzero derivative along the projection. -/
lemma lpsOriginalHolomorphicCovector_InteriorChart_deriv_ne_zero
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (τ : ℍ)
    (hs : letI := lpsOriginalFilledTopology N
      Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        (lpsOriginalFilledInteriorChart N hN x).source) :
    letI := lpsOriginalFilledTopology N
    deriv (fun z : ℂ => lpsOriginalFilledInteriorChart N hN x
      (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))) τ ≠ 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective proj := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  change Sum.inl (proj τ) ∈ Sum.inl '' (chartAt ℂ x).source at hs
  obtain ⟨a, ha, he⟩ := hs
  have hm : proj τ ∈ (chartAt ℂ x).source := by
    have he' := Sum.inl.inj he
    rwa [he'] at ha
  change proj τ ∈ ((hf.localInverseAt (r x)).trans UpperHalfPlane.ofComplex.symm).source at hm
  have hd := lpsOriginalCovector_localInverse_deriv_ne_zero N hN (r x) τ hm.1
  have heq : (fun z : ℂ => lpsOriginalFilledInteriorChart N hN x
      (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))) =
      (fun z : ℂ => ((hf.localInverseAt (r x)) (proj (UpperHalfPlane.ofComplex z)) : ℂ)) := by
    funext z
    change ((chartAt ℂ x).lift_openEmbedding (lpsOriginalFilledTopology_interior_openEmbedding N))
      (Sum.inl (proj (UpperHalfPlane.ofComplex z))) = _
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  rw [heq]
  exact hd
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine orbit projection has nonzero tangent derivative at every upper half-plane point. -/
lemma lpsOriginalHolomorphicCovectorProjection_mfderiv_ne_zero
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (τ : ℍ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) τ (1 : ℂ) ≠ 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  have hm := (lpsOriginalHolomorphicCovectorProjection_contMDiff N hN τ).mdifferentiableAt (by decide)
  rw [mfderiv, if_pos hm]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  change (fderiv ℂ (fun z : ℂ => lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ)
    (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))) (τ : ℂ)) (1 : ℂ) ≠ 0
  rw [fderiv_eq_deriv_mul, mul_one]
  exact lpsOriginalHolomorphicCovector_InteriorChart_deriv_ne_zero N hN (Quotient.mk _ τ) τ
    (lpsOriginalFilledInteriorChart_mem N hN (Quotient.mk _ τ))
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Filling the recovered cusp form gives the original arbitrary covector on the whole interior. -/
lemma lpsOriginalHolomorphicCovectorCuspForm_filled_interior
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) (τ : ℍ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    lpsOriginalFilledDifferential N hN (lpsOriginalHolomorphicCovectorCuspForm N hN sectionForm)
      (lpsOriginalHolomorphicCovectorProjection N τ) =
        sectionForm (lpsOriginalHolomorphicCovectorProjection N τ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let d : ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) τ (1 : ℂ)
  have hd : d ≠ 0 := lpsOriginalHolomorphicCovectorProjection_mfderiv_ne_zero N hN τ
  have hval : lpsOriginalFilledDifferential N hN
      (lpsOriginalHolomorphicCovectorCuspForm N hN sectionForm)
      (lpsOriginalHolomorphicCovectorProjection N τ) d =
        sectionForm (lpsOriginalHolomorphicCovectorProjection N τ) d := by
    rw [lpsOriginalFilledDifferential_projection_pullback]
    simp only [lpsCuspDifferential_apply, mul_one, lpsOriginalHolomorphicCovectorCuspForm_apply]
    rfl
  apply ContinuousLinearMap.ext
  intro v
  let vC : ℂ := v
  let A : ℂ →L[ℂ] ℂ := lpsOriginalFilledDifferential N hN
    (lpsOriginalHolomorphicCovectorCuspForm N hN sectionForm)
    (lpsOriginalHolomorphicCovectorProjection N τ)
  let B : ℂ →L[ℂ] ℂ := sectionForm (lpsOriginalHolomorphicCovectorProjection N τ)
  change A d = B d at hval
  change A vC = B vC
  calc
    A vC = A ((vC / d) • d) := by rw [smul_eq_mul, div_mul_cancel₀ _ hd]
    _ = (vC / d) • A d := A.map_smul _ _
    _ = (vC / d) • B d := congrArg (fun z : ℂ => (vC / d) • z) hval
    _ = B ((vC / d) • d) := (B.map_smul _ _).symm
    _ = B vC := by rw [smul_eq_mul, div_mul_cancel₀ _ hd]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual tangent and trivial-line coordinates at their own base point are the identity. -/
lemma lpsOriginalHolomorphicCovector_inCoordinates_self
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x x x x (sectionForm x) = sectionForm x := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  have ht : (trivializationAt ℂ (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x).continuousLinearMapAt ℂ x = ContinuousLinearMap.id ℂ ℂ :=
    Bundle.Trivial.continuousLinearMapAt_trivialization ℂ _ ℂ x
  have hs : (trivializationAt ℂ (TangentSpace (M := LPSOriginalFilledCurve N) 𝓘(ℂ)) x).symmL ℂ x = ContinuousLinearMap.id ℂ ℂ := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source ℂ x)]
    apply ContinuousLinearMap.ext
    intro v
    exact (tangentBundleCore 𝓘(ℂ) (LPSOriginalFilledCurve N)).coordChange_self
      (achart ℂ x) x (mem_achart_source ℂ x) v
  rw [ContinuousLinearMap.inCoordinates, ht, hs,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Analytic covector sections are determined by the dense original interior, including the cusps. -/
lemma lpsOriginalHolomorphicCovector_ext_interior
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (section1 section2 : LPSOriginalHolomorphicCovectorSections N hN)
    (h : ∀ q : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      section1 (Sum.inl q) = section2 (Sum.inl q)) : section1 = section2 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply DFunLike.ext
  intro x
  let K1 : LPSOriginalFilledCurve N → ℂ := fun y =>
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y (section1 y) (1 : ℂ)
  let K2 : LPSOriginalFilledCurve N → ℂ := fun y =>
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y (section2 y) (1 : ℂ)
  let H : LPSOriginalFilledCurve N → ℂ := fun y => K1 y - K2 y
  have h1 : ContinuousAt K1 x :=
    ((contMDiffAt_hom_bundle _).mp (section1.contMDiff x)).2.clm_apply
      (contMDiffAt_const (c := (1 : ℂ))) |>.continuousAt
  have h2 : ContinuousAt K2 x :=
    ((contMDiffAt_hom_bundle _).mp (section2.contMDiff x)).2.clm_apply
      (contMDiffAt_const (c := (1 : ℂ))) |>.continuousAt
  have hH : ContinuousAt H x := h1.sub h2
  have hzero : H '' Set.range (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N)
      ⊆ {(0 : ℂ)} := by
    rintro z ⟨y, ⟨q, rfl⟩, rfl⟩
    change K1 (Sum.inl q) - K2 (Sum.inl q) = 0
    dsimp only [K1, K2]
    rw [h q, sub_self]
  have hc := mem_closure_image hH (lpsOriginalFilledTopology_interior_dense N x)
  have hz : H x = 0 := (closure_minimal hzero isClosed_singleton) hc
  dsimp only [H, K1, K2] at hz
  rw [lpsOriginalHolomorphicCovector_inCoordinates_self,
    lpsOriginalHolomorphicCovector_inCoordinates_self] at hz
  have heval := sub_eq_zero.mp hz
  apply ContinuousLinearMap.ext
  intro v
  let vC : ℂ := v
  let A : ℂ →L[ℂ] ℂ := section1 x
  let B : ℂ →L[ℂ] ℂ := section2 x
  change A (1 : ℂ) = B (1 : ℂ) at heval
  change A vC = B vC
  have ha := A.map_smul vC (1 : ℂ)
  have hb := B.map_smul vC (1 : ℂ)
  simpa only [smul_eq_mul, mul_one] using
    ha.trans ((congrArg (fun z : ℂ => vC • z) heval).trans hb.symm)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Filling the recovered cusp form recovers every native analytic covector section globally. -/
lemma lpsOriginalHolomorphicCovectorCuspForm_filled
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) :
    lpsOriginalFilledHolomorphicDifferential N hN
      (lpsOriginalHolomorphicCovectorCuspForm N hN sectionForm) = sectionForm := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply lpsOriginalHolomorphicCovector_ext_interior N hN
  intro q
  refine Quotient.inductionOn q ?_
  intro τ
  exact lpsOriginalHolomorphicCovectorCuspForm_filled_interior N hN sectionForm τ
lemma lpsOriginalFilledDifferentialLinearMap_surjective
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    Function.Surjective (lpsOriginalFilledDifferentialLinearMap N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro sectionForm
  refine ⟨lpsOriginalHolomorphicCovectorCuspForm N hN sectionForm, ?_⟩
  exact lpsOriginalHolomorphicCovectorCuspForm_filled N hN sectionForm
def lpsOriginalFilledDifferentialLinearEquiv
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 ≃ₗ[ℂ]
      LPSOriginalHolomorphicCovectorSections N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact LinearEquiv.ofBijective (lpsOriginalFilledDifferentialLinearMap N hN)
    ⟨lpsOriginalFilledDifferentialLinearMap_injective N hN,
      lpsOriginalFilledDifferentialLinearMap_surjective N hN⟩
end
end QEC.Coding.TannerLiftedProduct


