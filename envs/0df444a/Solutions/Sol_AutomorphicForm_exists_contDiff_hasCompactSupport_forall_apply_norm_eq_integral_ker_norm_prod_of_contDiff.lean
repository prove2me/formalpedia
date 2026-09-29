-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/598d6996-7346-50ed-bdc4-17fbef5c6b3b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped ENNReal Classical

namespace C3Inst

open NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in
theorem secondCountableTopology_infiniteAdeleRing' (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem secondCountableTopology_E : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K) :=
  haveI := secondCountableTopology_infiniteAdeleRing' L
  (AutomorphicForm.archIdentHomeomorph K L).secondCountableTopology

theorem secondCountableTopology_unitsE : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ˣ := by
  haveI := secondCountableTopology_E K L
  haveI : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_unitsE : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem continuous_includeRight :
    Continuous ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) :
      InfiniteAdeleRing K → L ⊗[K] InfiniteAdeleRing K) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have h : ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) :
      InfiniteAdeleRing K → L ⊗[K] InfiniteAdeleRing K) = fun x => x • (1 : L ⊗[K] InfiniteAdeleRing K) := by
    funext x
    rw [AutomorphicForm.rightActions_smul_eq, mul_one]
    rfl
  rw [h]
  exact Continuous.smul (M := InfiniteAdeleRing K) (X := L ⊗[K] InfiniteAdeleRing K) continuous_id continuous_const

theorem continuous_algebraNorm :
    Continuous (Algebra.norm (InfiniteAdeleRing K) : L ⊗[K] InfiniteAdeleRing K → InfiniteAdeleRing K) := by
  classical
  haveI hTR := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI : ContinuousAdd (L ⊗[K] InfiniteAdeleRing K) := hTR.toContinuousAdd
  let b := Module.Free.chooseBasis (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have : (Algebra.norm (InfiniteAdeleRing K) : L ⊗[K] InfiniteAdeleRing K → InfiniteAdeleRing K) =
      fun s => (Algebra.leftMulMatrix b s).det := funext (Algebra.norm_eq_matrix_det b)
  rw [this]
  refine Continuous.matrix_det ?_
  exact IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap

theorem continuous_iotaL :
    Continuous (fun z : L ⊗[K] InfiniteAdeleRing K =>
      NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)) :=
  (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L).continuous.comp
    (AutomorphicForm.archIdentHomeomorph K L).continuous

theorem continuous_iotaK :
    Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K → mixedEmbedding.mixedSpace K) :=
  (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K).continuous

end C3Inst

namespace FibreSmooth

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def iotaL (z : L ⊗[K] InfiniteAdeleRing K) : NumberField.mixedEmbedding.mixedSpace L :=
  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)

noncomputable def iotaK (x : InfiniteAdeleRing K) : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x

noncomputable def normPt (ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) :
    Fin 2 → NumberField.mixedEmbedding.mixedSpace K :=
  ![iotaK K (Algebra.norm (InfiniteAdeleRing K) ((ab.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
    iotaK K (Algebra.norm (InfiniteAdeleRing K) ((ab.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))]

end FibreSmooth

namespace P4mg

open NumberField

variable (K : Type) [Field K] [NumberField K]

noncomputable def mroot (n : ℕ) (p : mixedEmbedding.mixedSpace K) : mixedEmbedding.mixedSpace K :=
  (fun w => (p.1 w) ^ ((n : ℝ)⁻¹), fun w => (p.2 w) ^ ((n : ℂ)⁻¹))

noncomputable def mrootInv (n : ℕ) (p : mixedEmbedding.mixedSpace K) : mixedEmbedding.mixedSpace K :=
  (fun w => (p.1 w) ^ (-(n : ℝ)⁻¹), fun w => (p.2 w) ^ (-(n : ℂ)⁻¹))

def good : Set (mixedEmbedding.mixedSpace K) :=
  {p | (∀ w, 0 < p.1 w) ∧ ∀ w, p.2 w ∈ Complex.slitPlane}

theorem isOpen_good : IsOpen (good K) := by
  have h1 : IsOpen {p : mixedEmbedding.mixedSpace K | ∀ w, 0 < p.1 w} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_lt continuous_const ((continuous_apply w).comp continuous_fst)
  have h2 : IsOpen {p : mixedEmbedding.mixedSpace K | ∀ w, p.2 w ∈ Complex.slitPlane} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w =>
      Complex.isOpen_slitPlane.preimage ((continuous_apply w).comp continuous_snd)
  exact h1.inter h2

theorem one_mem_good : (1 : mixedEmbedding.mixedSpace K) ∈ good K :=
  ⟨fun _ => by simp, fun _ => by simp [Complex.slitPlane, Complex.one_re]⟩

theorem mroot_pow {n : ℕ} (hn : n ≠ 0) {p : mixedEmbedding.mixedSpace K} (hp : p ∈ good K) :
    mroot K n p ^ n = p := by
  ext w
  · simp only [mroot, Prod.pow_fst, Pi.pow_apply]
    exact Real.rpow_inv_natCast_pow (hp.1 w).le hn
  · simp only [mroot, Prod.pow_snd, Pi.pow_apply]
    exact Complex.cpow_nat_inv_pow _ hn

theorem mroot_one (n : ℕ) : mroot K n 1 = 1 := by
  ext w
  · simp [mroot]
  · simp [mroot]

theorem mroot_mul_mrootInv {n : ℕ} {p : mixedEmbedding.mixedSpace K} (hp : p ∈ good K) :
    mroot K n p * mrootInv K n p = 1 := by
  ext w
  · simp only [mroot, mrootInv, Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply]
    rw [Real.rpow_neg (hp.1 w).le, mul_inv_cancel₀]
    exact (Real.rpow_pos_of_pos (hp.1 w) _).ne'
  · simp only [mroot, mrootInv, Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply]
    rw [Complex.cpow_neg, mul_inv_cancel₀]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero (hp.2 w)))

theorem continuousOn_mroot (n : ℕ) : ContinuousOn (mroot K n) (good K) := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun w => ?_
    exact ((Real.continuous_rpow_const (by positivity)).comp
      ((continuous_apply w).comp continuous_fst)).continuousOn
  · refine continuousOn_pi.2 fun w => ?_
    intro p hp
    have hc : Continuous fun q : mixedEmbedding.mixedSpace K => q.2 w := (continuous_apply w).comp continuous_snd
    exact (hc.continuousAt.cpow continuousAt_const (hp.2 w)).continuousWithinAt

theorem continuousOn_mrootInv (n : ℕ) : ContinuousOn (mrootInv K n) (good K) := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun w => ?_
    intro p hp
    have hc : Continuous fun q : mixedEmbedding.mixedSpace K => q.1 w := (continuous_apply w).comp continuous_fst
    exact (hc.continuousAt.rpow_const (Or.inl (hp.1 w).ne')).continuousWithinAt
  · refine continuousOn_pi.2 fun w => ?_
    intro p hp
    have hc : Continuous fun q : mixedEmbedding.mixedSpace K => q.2 w := (continuous_apply w).comp continuous_snd
    exact (hc.continuousAt.cpow continuousAt_const (hp.2 w)).continuousWithinAt

theorem contDiffAt_mroot (n : ℕ) {p : mixedEmbedding.mixedSpace K} (hp : p ∈ good K) :
    ContDiffAt ℝ (⊤ : ℕ∞) (mroot K n) p := by
  refine ContDiffAt.prodMk ?_ ?_
  · refine contDiffAt_pi.2 fun w => ?_
    have hc : ContDiff ℝ (⊤ : ℕ∞) fun q : mixedEmbedding.mixedSpace K => q.1 w :=
      (contDiff_apply ℝ ℝ w).comp contDiff_fst
    exact (Real.contDiffAt_rpow_const_of_ne (p := (n : ℝ)⁻¹) (hp.1 w).ne').comp p hc.contDiffAt
  · refine contDiffAt_pi.2 fun w => ?_
    have hc : ContDiff ℝ (⊤ : ℕ∞) fun q : mixedEmbedding.mixedSpace K => q.2 w :=
      (contDiff_apply ℝ ℂ w).comp contDiff_snd
    have ha : AnalyticAt ℂ (fun z : ℂ => z ^ ((n : ℂ)⁻¹)) (p.2 w) :=
      analyticAt_id.cpow analyticAt_const (hp.2 w)
    have hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => z ^ ((n : ℂ)⁻¹)) (p.2 w) :=
      ((ha.contDiffAt (n := ⊤)).restrict_scalars ℝ).of_le le_top
    exact hr.comp p hc.contDiffAt

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :
      mixedEmbedding.mixedSpace K → InfiniteAdeleRing K) := by
  have hh := NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K
  have e : ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm : mixedEmbedding.mixedSpace K → InfiniteAdeleRing K) =
      (hh.homeomorph _).symm := by
    funext y
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [RingEquiv.apply_symm_apply]
    exact ((hh.homeomorph _).apply_symm_apply y).symm
  rw [e]; exact (hh.homeomorph _).symm.continuous

theorem exists_rootUnit (n : ℕ) :
    ∃ ρ : mixedEmbedding.mixedSpace K → (InfiniteAdeleRing K)ˣ,
      (∀ t ∈ good K, ((ρ t : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mroot K n t)) ∧
      (∀ t ∈ good K, (((ρ t)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mrootInv K n t)) ∧
      ContinuousOn ρ (good K) := by
  classical
  set ι := InfiniteAdeleRing.ringEquiv_mixedSpace K with hι
  have h01 : ∀ t ∈ good K, ι.symm (mroot K n t) * ι.symm (mrootInv K n t) = 1 := by
    intro t ht
    rw [← map_mul, mroot_mul_mrootInv K ht, map_one]
  refine ⟨fun t => if h : t ∈ good K then ⟨ι.symm (mroot K n t), ι.symm (mrootInv K n t), h01 t h,
    by rw [mul_comm]; exact h01 t h⟩ else 1, ?_, ?_, ?_⟩
  · intro t ht; simp only [dif_pos ht]
  · intro t ht; simp only [dif_pos ht]; rfl
  · have hsc := continuous_ringEquiv_mixedSpace_symm K
    have h1 : ContinuousOn (fun t => ι.symm (mroot K n t)) (good K) :=
      hsc.comp_continuousOn (continuousOn_mroot K n)
    have h2 : ContinuousOn (fun t => ι.symm (mrootInv K n t)) (good K) :=
      hsc.comp_continuousOn (continuousOn_mrootInv K n)
    rw [Units.isInducing_embedProduct.continuousOn_iff]
    refine ContinuousOn.prodMk ?_ ?_
    · exact h1.congr (fun t ht => by simp only [Function.comp_apply, Units.embedProduct_apply, dif_pos ht])
    · refine (MulOpposite.continuous_op.comp_continuousOn h2).congr (fun t ht => ?_)
      simp only [Function.comp_apply, Units.embedProduct_apply, dif_pos ht]
      rfl

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

noncomputable def iotaLHom : L ⊗[K] InfiniteAdeleRing K →+* mixedEmbedding.mixedSpace L :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace L).toRingHom.comp (AutomorphicForm.archIdent K L)

theorem iotaLHom_apply (z : L ⊗[K] InfiniteAdeleRing K) :
    iotaLHom K L z = InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z) := rfl

noncomputable def Jmap : mixedEmbedding.mixedSpace K →L[ℝ] mixedEmbedding.mixedSpace L :=
  AddMonoidHom.toRealLinearMap
    (((iotaLHom K L).comp
          ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom)).toAddMonoidHom)
    (by
      haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
      have h1 := continuous_ringEquiv_mixedSpace_symm K
      have h2 : Continuous ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) :
          InfiniteAdeleRing K → L ⊗[K] InfiniteAdeleRing K) := by
        have h := IsModuleTopology.continuous_of_linearMap
          (Algebra.linearMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K))
        exact h
      have h3 : Continuous (AutomorphicForm.archIdent K L) := (AutomorphicForm.archIdentHomeomorph K L).continuous
      have h4 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace L) :=
        (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L).continuous
      exact h4.comp (h3.comp (h2.comp h1)))

theorem Jmap_apply (y : mixedEmbedding.mixedSpace K) :
    Jmap K L y = iotaLHom K L
      (Algebra.TensorProduct.includeRight (R := K) (A := L) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y)) := rfl

noncomputable def PhiFun
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker)
    (G : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ)
    (ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) : ℂ :=
  ∫ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
      ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
    G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
          ((ab.1 * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
        NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
          ((ab.2 * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))]
    ∂(θ.prod θ)

end P4mg

set_option maxHeartbeats 1600000 in
theorem P4_aux
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (G : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ)) (hCc : IsCompact C)
    (hCG : ∀ p ∈ tsupport G, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))))
    (q : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) :
    ∃ H : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ, ContDiff ℝ (⊤ : ℕ∞) H ∧
      ∀ᶠ y in nhds (FibreSmooth.normPt K L q), ∃ ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        FibreSmooth.normPt K L ab = y ∧ H y = P4mg.PhiFun K L θ G ab := by
  classical

  haveI hTR := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI := C3Inst.secondCountableTopology_E K L
  haveI := C3Inst.secondCountableTopology_unitsE K L
  haveI := C3Inst.locallyCompactSpace_unitsE K L
  haveI : IsTopologicalGroup (L ⊗[K] InfiniteAdeleRing K)ˣ := inferInstance
  have hNc : Continuous (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) :=
    Continuous.units_map _ (C3Inst.continuous_algebraNorm K L)
  have hU1closed : IsClosed ((Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker : Set (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hNc
  haveI : SecondCountableTopology ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := hU1closed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : BorelSpace (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) := Prod.borelSpace
  haveI : SigmaFinite θ := Measure.IsHaarMeasure.sigmaFinite θ
  haveI : (θ.prod θ).IsHaarMeasure := inferInstance

  set ιK := NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K with hιK
  set ιL : (L ⊗[K] InfiniteAdeleRing K) →+* NumberField.mixedEmbedding.mixedSpace L := P4mg.iotaLHom K L with hιL
  have hιL_apply : ∀ z : (L ⊗[K] InfiniteAdeleRing K), ιL z = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z) :=
    fun z => rfl
  have hιinj : Function.Injective (fun z : (L ⊗[K] InfiniteAdeleRing K) =>
      NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)) :=
    (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).injective.comp (AutomorphicForm.archIdentEquiv K L).injective
  have hιLc : Continuous ιL := C3Inst.continuous_iotaL K L
  set cmap : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L := fun u =>
    (ιL ((u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)), ιL ((u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) with hcmap
  have hcmapc : Continuous cmap :=
    (hιLc.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst))).prodMk
      (hιLc.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)))
  set incl : InfiniteAdeleRing K →+* (L ⊗[K] InfiniteAdeleRing K) :=
    (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom with hincl
  have hincl_alg : ∀ r : InfiniteAdeleRing K, incl r = algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) r := fun r => rfl
  set m : ℕ := Module.finrank (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) with hm
  have hnorm_incl : ∀ r : InfiniteAdeleRing K, Algebra.norm (InfiniteAdeleRing K) (incl r) = r ^ m := by
    intro r; rw [hincl_alg, Algebra.norm_algebraMap]
  have hm0 : m ≠ 0 := by
    intro h0
    have h := hnorm_incl 0
    rw [map_zero, h0, pow_zero, Algebra.norm_zero] at h
    exact zero_ne_one h
  set a₀ : (InfiniteAdeleRing K)ˣ := Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) q.1 with ha₀
  set b₀ : (InfiniteAdeleRing K)ˣ := Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) q.2 with hb₀
  set x₀ : Fin 2 → NumberField.mixedEmbedding.mixedSpace K := FibreSmooth.normPt K L q with hx₀
  have hx₀0 : x₀ 0 = ιK (a₀ : InfiniteAdeleRing K) := by
    simp only [hx₀, FibreSmooth.normPt, FibreSmooth.iotaK, Matrix.cons_val_zero, ha₀, Units.coe_map, MonoidHom.coe_coe, hιK]
  have hx₀1 : x₀ 1 = ιK (b₀ : InfiniteAdeleRing K) := by
    simp only [hx₀, FibreSmooth.normPt, FibreSmooth.iotaK, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, hb₀, Units.coe_map,
      MonoidHom.coe_coe, hιK]

  set t₁ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → NumberField.mixedEmbedding.mixedSpace K := fun y => ιK ((a₀⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * y 0 with ht₁
  set t₂ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → NumberField.mixedEmbedding.mixedSpace K := fun y => ιK ((b₀⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * y 1 with ht₂
  have ht₁s : ContDiff ℝ (⊤ : ℕ∞) t₁ := contDiff_const.mul (contDiff_apply ℝ (NumberField.mixedEmbedding.mixedSpace K) 0)
  have ht₂s : ContDiff ℝ (⊤ : ℕ∞) t₂ := contDiff_const.mul (contDiff_apply ℝ (NumberField.mixedEmbedding.mixedSpace K) 1)
  have ht₁x₀ : t₁ x₀ = 1 := by
    simp only [ht₁]; rw [hx₀0, ← map_mul, Units.inv_mul, map_one]
  have ht₂x₀ : t₂ x₀ = 1 := by
    simp only [ht₂]; rw [hx₀1, ← map_mul, Units.inv_mul, map_one]
  set V : Set (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) := {y | t₁ y ∈ P4mg.good K ∧ t₂ y ∈ P4mg.good K} with hV
  have hVo : IsOpen V :=
    ((P4mg.isOpen_good K).preimage ht₁s.continuous).inter ((P4mg.isOpen_good K).preimage ht₂s.continuous)
  have hx₀V : x₀ ∈ V := by
    refine ⟨?_, ?_⟩
    · show t₁ x₀ ∈ P4mg.good K; rw [ht₁x₀]; exact P4mg.one_mem_good K
    · show t₂ x₀ ∈ P4mg.good K; rw [ht₂x₀]; exact P4mg.one_mem_good K

  obtain ⟨ρ, hρval, hρinv, hρc⟩ := P4mg.exists_rootUnit K m
  set R₁ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → NumberField.mixedEmbedding.mixedSpace K := fun y => P4mg.mroot K m (t₁ y) with hR₁
  set R₂ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → NumberField.mixedEmbedding.mixedSpace K := fun y => P4mg.mroot K m (t₂ y) with hR₂
  have hR₁s : ∀ y ∈ V, ContDiffAt ℝ (⊤ : ℕ∞) R₁ y := fun y hy =>
    (P4mg.contDiffAt_mroot K m hy.1).comp y ht₁s.contDiffAt
  have hR₂s : ∀ y ∈ V, ContDiffAt ℝ (⊤ : ℕ∞) R₂ y := fun y hy =>
    (P4mg.contDiffAt_mroot K m hy.2).comp y ht₂s.contDiffAt

  set α : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → (L ⊗[K] InfiniteAdeleRing K)ˣ := fun y => q.1 * Units.map (incl : InfiniteAdeleRing K →* (L ⊗[K] InfiniteAdeleRing K)) (ρ (t₁ y)) with hα
  set β : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → (L ⊗[K] InfiniteAdeleRing K)ˣ := fun y => q.2 * Units.map (incl : InfiniteAdeleRing K →* (L ⊗[K] InfiniteAdeleRing K)) (ρ (t₂ y)) with hβ
  have hαval : ∀ y ∈ V, ((α y : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = (q.1 : (L ⊗[K] InfiniteAdeleRing K)) * incl (ιK.symm (R₁ y)) := by
    intro y hy
    simp only [hα, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, hρval _ hy.1, hR₁, hιK]
  have hβval : ∀ y ∈ V, ((β y : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = (q.2 : (L ⊗[K] InfiniteAdeleRing K)) * incl (ιK.symm (R₂ y)) := by
    intro y hy
    simp only [hβ, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, hρval _ hy.2, hR₂, hιK]
  have hαc : ContinuousOn α V := by
    have h1 : ContinuousOn (fun y => ρ (t₁ y)) V := hρc.comp ht₁s.continuous.continuousOn (fun y hy => hy.1)
    have hinclc : Continuous (incl : InfiniteAdeleRing K → (L ⊗[K] InfiniteAdeleRing K)) := C3Inst.continuous_includeRight K L
    exact continuousOn_const.mul ((Continuous.units_map (incl : InfiniteAdeleRing K →* (L ⊗[K] InfiniteAdeleRing K)) hinclc).comp_continuousOn h1)
  have hβc : ContinuousOn β V := by
    have h1 : ContinuousOn (fun y => ρ (t₂ y)) V := hρc.comp ht₂s.continuous.continuousOn (fun y hy => hy.2)
    have hinclc : Continuous (incl : InfiniteAdeleRing K → (L ⊗[K] InfiniteAdeleRing K)) := C3Inst.continuous_includeRight K L
    exact continuousOn_const.mul ((Continuous.units_map (incl : InfiniteAdeleRing K →* (L ⊗[K] InfiniteAdeleRing K)) hinclc).comp_continuousOn h1)

  have hNα : ∀ y ∈ V, ιK (Algebra.norm (InfiniteAdeleRing K) ((α y : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) = y 0 := by
    intro y hy
    rw [hαval y hy, map_mul, hnorm_incl, ← map_pow]
    show ιK (Algebra.norm (InfiniteAdeleRing K) (q.1 : (L ⊗[K] InfiniteAdeleRing K)) * ιK.symm (P4mg.mroot K m (t₁ y) ^ m)) = y 0
    rw [P4mg.mroot_pow K hm0 hy.1, map_mul, RingEquiv.apply_symm_apply]
    simp only [ht₁]
    rw [← mul_assoc, ← map_mul]
    have : Algebra.norm (InfiniteAdeleRing K) (q.1 : (L ⊗[K] InfiniteAdeleRing K)) * ((a₀⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := by
      have h := a₀.mul_inv
      rw [show ((a₀ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = Algebra.norm (InfiniteAdeleRing K) (q.1 : (L ⊗[K] InfiniteAdeleRing K)) from rfl] at h
      exact h
    rw [this, map_one, one_mul]
  have hNβ : ∀ y ∈ V, ιK (Algebra.norm (InfiniteAdeleRing K) ((β y : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) = y 1 := by
    intro y hy
    rw [hβval y hy, map_mul, hnorm_incl, ← map_pow]
    show ιK (Algebra.norm (InfiniteAdeleRing K) (q.2 : (L ⊗[K] InfiniteAdeleRing K)) * ιK.symm (P4mg.mroot K m (t₂ y) ^ m)) = y 1
    rw [P4mg.mroot_pow K hm0 hy.2, map_mul, RingEquiv.apply_symm_apply]
    simp only [ht₂]
    rw [← mul_assoc, ← map_mul]
    have : Algebra.norm (InfiniteAdeleRing K) (q.2 : (L ⊗[K] InfiniteAdeleRing K)) * ((b₀⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := by
      have h := b₀.mul_inv
      rw [show ((b₀ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = Algebra.norm (InfiniteAdeleRing K) (q.2 : (L ⊗[K] InfiniteAdeleRing K)) from rfl] at h
      exact h
    rw [this, map_one, one_mul]
  have hnormPt : ∀ y ∈ V, FibreSmooth.normPt K L (α y, β y) = y := by
    intro y hy
    funext i
    fin_cases i
    · simp only [FibreSmooth.normPt, FibreSmooth.iotaK, Matrix.cons_val_zero]; exact hNα y hy
    · simp only [FibreSmooth.normPt, FibreSmooth.iotaK, Matrix.cons_val_one, Matrix.head_cons]; exact hNβ y hy

  set J := P4mg.Jmap K L with hJ
  have hJR₁ : ∀ y ∈ V, J (R₁ y) = ιL (incl (ιK.symm (R₁ y))) := fun y hy => rfl
  set Θ : (NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) × (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) := fun mp =>
    ![ιL (q.1 : (L ⊗[K] InfiniteAdeleRing K)) * J (R₁ mp.2) * mp.1.1, ιL (q.2 : (L ⊗[K] InfiniteAdeleRing K)) * J (R₂ mp.2) * mp.1.2] with hΘ
  have hΘs : ∀ mp : (NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) × (Fin 2 → NumberField.mixedEmbedding.mixedSpace K), mp.2 ∈ V → ContDiffAt ℝ (⊤ : ℕ∞) Θ mp := by
    intro mp hmp
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun mp : (NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) × (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) => J (R₁ mp.2)) mp :=
      (J.contDiff.contDiffAt).comp mp ((hR₁s mp.2 hmp).comp mp contDiff_snd.contDiffAt)
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun mp : (NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) × (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) => J (R₂ mp.2)) mp :=
      (J.contDiff.contDiffAt).comp mp ((hR₂s mp.2 hmp).comp mp contDiff_snd.contDiffAt)
    have hm1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun mp : (NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) × (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) => mp.1.1) mp :=
      (contDiff_fst.comp contDiff_fst).contDiffAt
    have hm2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun mp : (NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) × (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) => mp.1.2) mp :=
      (contDiff_snd.comp contDiff_fst).contDiffAt
    refine contDiffAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [hΘ] using (contDiffAt_const.mul h1).mul hm1
    · simpa [hΘ] using (contDiffAt_const.mul h2).mul hm2
  have hΘval : ∀ y ∈ V, ∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
      Θ (cmap u, y) =
        ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
            (((α y * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
            (((β y * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] := by
    intro y hy u
    rw [← hιL_apply, ← hιL_apply, Units.val_mul (α y), Units.val_mul (β y), hαval y hy, hβval y hy,
      map_mul, map_mul, map_mul, map_mul]
    simp only [hΘ, hcmap]
    rfl

  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVo x₀ hx₀V
  set χ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩ with hχ
  have hχV : tsupport (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ) ⊆ V := by
    rw [χ.tsupport_eq]
    show Metric.closedBall x₀ (ε / 2) ⊆ V
    exact (Metric.closedBall_subset_ball (by linarith)).trans hεV
  have hχ1 : ∀ y ∈ Metric.ball x₀ (ε / 4), (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ) y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  set Y : Set (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) := Metric.closedBall x₀ (ε / 2) with hY
  have hYc : IsCompact Y := isCompact_closedBall _ _
  have hYV : Y ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hεV

  set S_E : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) := (fun p : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) × ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) => ((α p.1)⁻¹ * p.2.1, (β p.1)⁻¹ * p.2.2)) '' (Y ×ˢ C)
    with hS_E
  have hS_Ec : IsCompact S_E := by
    refine (hYc.prod hCc).image_of_continuousOn ?_
    refine ContinuousOn.prodMk ?_ ?_
    · exact (((hαc.mono hYV).comp continuous_fst.continuousOn (fun p hp => hp.1)).inv).mul
        (continuous_fst.comp continuous_snd).continuousOn
    · exact (((hβc.mono hYV).comp continuous_fst.continuousOn (fun p hp => hp.1)).inv).mul
        (continuous_snd.comp continuous_snd).continuousOn
  have hce : Topology.IsClosedEmbedding (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker => ((u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))) :=
    hU1closed.isClosedEmbedding_subtypeVal.prodMap hU1closed.isClosedEmbedding_subtypeVal
  set S_u : Set (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) := (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker => ((u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))) ⁻¹' S_E with hS_u
  have hS_uc : IsCompact S_u := hce.isCompact_preimage hS_Ec

  obtain ⟨wf, hw1, -, hwc, -⟩ := exists_continuous_one_zero_of_isCompact hS_uc isClosed_empty (Set.disjoint_empty _)

  have hS_Mc : IsCompact (cmap '' S_u) := hS_uc.image hcmapc
  obtain ⟨Rb, hRb⟩ := hS_Mc.isBounded.subset_closedBall (0 : NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L)
  set ψ : ContDiffBump (0 : NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) := ⟨|Rb| + 1, |Rb| + 2, by positivity, by linarith⟩ with hψ
  have hψ1 : ∀ mm ∈ cmap '' S_u, (ψ : NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L → ℝ) mm = 1 := by
    intro mm hmm
    apply ψ.one_of_mem_closedBall
    have h := hRb hmm
    rw [Metric.mem_closedBall] at h ⊢
    show dist mm 0 ≤ |Rb| + 1
    linarith [le_abs_self Rb]

  set Ψ : (NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) × (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ := fun mp =>
    (((χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ) mp.2 * (ψ : NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L → ℝ) mp.1 : ℝ) : ℂ) * G (Θ mp) with hΨ
  have hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    refine contDiff_iff_contDiffAt.mpr fun mp => ?_
    by_cases hmp : mp.2 ∈ tsupport (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ)
    · have hV' : mp.2 ∈ V := hχV hmp
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun mp : (NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L) × (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) =>
          (((χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ) mp.2 * (ψ : NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L → ℝ) mp.1 : ℝ) : ℂ)) mp := by
        refine (Complex.ofRealCLM.contDiff.contDiffAt).comp mp ?_
        exact (χ.contDiff.contDiffAt.comp mp contDiff_snd.contDiffAt).mul
          (ψ.contDiff.contDiffAt.comp mp contDiff_fst.contDiffAt)
      simp only [hΨ]
      exact h1.mul (hG.contDiffAt.comp mp (hΘs mp hV'))
    ·
      have hzero : ∀ᶠ mp' in nhds mp, Ψ mp' = 0 := by
        have ho : IsOpen ((tsupport (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ))ᶜ) := (isClosed_tsupport _).isOpen_compl
        have hmem : mp ∈ Prod.snd ⁻¹' (tsupport (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ))ᶜ := hmp
        filter_upwards [(ho.preimage continuous_snd).mem_nhds hmem] with mp' hmp'
        have : (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ) mp'.2 = 0 := image_eq_zero_of_notMem_tsupport hmp'
        simp only [hΨ, this, zero_mul, Complex.ofReal_zero]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hzero
  have hΨc : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro ((ψ.hasCompactSupport).prod (χ.hasCompactSupport)) ?_
    intro mp hmp
    rw [Set.mem_prod, not_and_or] at hmp
    rcases hmp with h | h
    · have : (ψ : NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L → ℝ) mp.1 = 0 := image_eq_zero_of_notMem_tsupport h
      simp only [hΨ, this, mul_zero, Complex.ofReal_zero, zero_mul]
    · have : (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ) mp.2 = 0 := image_eq_zero_of_notMem_tsupport h
      simp only [hΨ, this, zero_mul, Complex.ofReal_zero]

  set H : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ := fun y => ∫ u, wf u • Ψ (cmap u, y) ∂(θ.prod θ) with hH
  have hHs : ContDiff ℝ (⊤ : ℕ∞) H :=
    MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport (θ.prod θ)
      cmap hcmapc wf wf.continuous hwc Ψ hΨs hΨc
  refine ⟨H, hHs, ?_⟩

  have hball : Metric.ball x₀ (ε / 4) ∈ nhds x₀ := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with y hy
  have hyY : y ∈ Y := Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hy)
  have hyV : y ∈ V := hYV hyY
  refine ⟨(α y, β y), hnormPt y hyV, ?_⟩
  simp only [hH, P4mg.PhiFun]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)

  dsimp only
  have hΘu := hΘval y hyV u
  by_cases hGz : G (Θ (cmap u, y)) = 0
  · rw [← hΘu, hGz]
    simp only [hΨ]
    rw [hGz, mul_zero, smul_zero]
  ·
    have hsup : Θ (cmap u, y) ∈ tsupport G := subset_tsupport G hGz
    obtain ⟨q', hq'C, hq'0, hq'1⟩ := hCG _ hsup
    rw [hΘu] at hq'0 hq'1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hq'0 hq'1
    have e1 : α y * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = q'.1 := Units.ext (hιinj hq'0)
    have e2 : β y * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = q'.2 := Units.ext (hιinj hq'1)
    have huS : u ∈ S_u := by
      show ((u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) ∈ S_E
      refine ⟨(y, q'), ⟨hyY, hq'C⟩, ?_⟩
      show ((α y)⁻¹ * q'.1, (β y)⁻¹ * q'.2) = ((u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))
      rw [← e1, ← e2, inv_mul_cancel_left, inv_mul_cancel_left]
    have hw : wf u = 1 := hw1 huS
    have hψu : (ψ : NumberField.mixedEmbedding.mixedSpace L × NumberField.mixedEmbedding.mixedSpace L → ℝ) (cmap u) = 1 := hψ1 _ ⟨u, huS, rfl⟩
    have hχy : (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ) y = 1 := hχ1 y hy
    rw [← hΘu]
    simp only [hΨ]
    rw [hw, one_smul, hχy, hψu, one_mul, Complex.ofReal_one, one_mul]

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (G : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G)
    (hGu : ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport G, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) :
    ∃ F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport F, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
          G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))]) (θ.prod θ) ∧
        F ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (Algebra.norm (InfiniteAdeleRing K) ((α : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
            NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (Algebra.norm (InfiniteAdeleRing K) ((β : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] =
          ∫ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
            G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] ∂(θ.prod θ) := by
  classical
  set Φ : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ → ℂ := fun ab =>
    ∫ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
        ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
      G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
            ((ab.1 * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
            ((ab.2 * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))]
      ∂(θ.prod θ) with hΦ
  set F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ := fun y =>
    if h : ∃ ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, FibreSmooth.normPt K L ab = y
    then Φ (Classical.choose h) else 0 with hF
  obtain ⟨C, hCc, hCG⟩ := hGu
  set KC : Set (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) := FibreSmooth.normPt K L '' C with hKC

  haveI hTR := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI := C3Inst.secondCountableTopology_E K L
  haveI := C3Inst.secondCountableTopology_unitsE K L
  haveI := C3Inst.locallyCompactSpace_unitsE K L
  haveI : IsTopologicalGroup (L ⊗[K] InfiniteAdeleRing K)ˣ := inferInstance
  have hNc : Continuous (Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) :=
    Continuous.units_map _ (C3Inst.continuous_algebraNorm K L)
  have hU1closed : IsClosed ((Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker : Set (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hNc
  haveI : SecondCountableTopology ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker :=
    hU1closed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : BorelSpace (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
      ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :=
    Prod.borelSpace
  haveI : SigmaFinite θ := Measure.IsHaarMeasure.sigmaFinite θ

  have hιinj : Function.Injective (fun z : L ⊗[K] InfiniteAdeleRing K =>
      NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)) :=
    (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).injective.comp (AutomorphicForm.archIdentEquiv K L).injective
  have key0 : ∀ (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ)
      (u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
        ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
      G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
            ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
            ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] ≠ 0 →
      ∃ q ∈ C, α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = q.1 ∧ β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = q.2 := by
    intro α β u hne
    obtain ⟨q, hqC, hq0, hq1⟩ := hCG _ (subset_tsupport _ (Function.mem_support.mpr hne))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hq0 hq1
    exact ⟨q, hqC, Units.ext (hιinj hq0), Units.ext (hιinj hq1)⟩
  have hnormU : ∀ (a : (L ⊗[K] InfiniteAdeleRing K)ˣ)
      (u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
      Algebra.norm (InfiniteAdeleRing K) ((a * (u : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
          (L ⊗[K] InfiniteAdeleRing K)) =
        Algebra.norm (InfiniteAdeleRing K) (a : (L ⊗[K] InfiniteAdeleRing K)) := by
    intro a u
    have hu : Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)
        (u : (L ⊗[K] InfiniteAdeleRing K)ˣ) = 1 := u.2
    have hu' : Algebra.norm (InfiniteAdeleRing K) (((u : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)) = 1 := by
      have := congrArg Units.val hu
      simpa [Units.coe_map] using this
    rw [Units.val_mul, map_mul, hu', mul_one]
  have hnormPt_cont : Continuous (FibreSmooth.normPt K L) := by
    have h0 : Continuous fun ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ =>
        FibreSmooth.iotaK K (Algebra.norm (InfiniteAdeleRing K) ((ab.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) :=
      (C3Inst.continuous_iotaK K).comp ((C3Inst.continuous_algebraNorm K L).comp
        (Units.continuous_val.comp continuous_fst))
    have h1 : Continuous fun ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ =>
        FibreSmooth.iotaK K (Algebra.norm (InfiniteAdeleRing K) ((ab.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) :=
      (C3Inst.continuous_iotaK K).comp ((C3Inst.continuous_algebraNorm K L).comp
        (Units.continuous_val.comp continuous_snd))
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [FibreSmooth.normPt] using h0
    · simpa [FibreSmooth.normPt] using h1

  have P2a : ∀ (ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
        ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
      Φ (ab.1 * (v.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), ab.2 * (v.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) = Φ ab := by
    intro ab v
    simp only [hΦ]
    have := integral_mul_left_eq_self (μ := θ.prod θ)
      (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
        G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              ((ab.1 * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
            NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              ((ab.2 * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))]) v
    refine Eq.trans ?_ this
    congr 1
    funext u
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_assoc]
  have P2b : ∀ ab ab' : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      FibreSmooth.normPt K L ab = FibreSmooth.normPt K L ab' → Φ ab = Φ ab' := by
    intro ab ab' h
    have h1 : Algebra.norm (InfiniteAdeleRing K) ((ab.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) =
        Algebra.norm (InfiniteAdeleRing K) ((ab'.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) := by
      have := congrFun h 0
      simp only [FibreSmooth.normPt, FibreSmooth.iotaK, Matrix.cons_val_zero] at this
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).injective this
    have h2 : Algebra.norm (InfiniteAdeleRing K) ((ab.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) =
        Algebra.norm (InfiniteAdeleRing K) ((ab'.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) := by
      have := congrFun h 1
      simp only [FibreSmooth.normPt, FibreSmooth.iotaK, Matrix.cons_val_one, Matrix.head_cons] at this
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).injective this
    have hmem : ∀ (a b : (L ⊗[K] InfiniteAdeleRing K)ˣ),
        Algebra.norm (InfiniteAdeleRing K) (a : (L ⊗[K] InfiniteAdeleRing K)) =
          Algebra.norm (InfiniteAdeleRing K) (b : (L ⊗[K] InfiniteAdeleRing K)) →
        a⁻¹ * b ∈ (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := by
      intro a b hab
      have hu : Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) a =
          Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) b :=
        Units.ext (by simpa [Units.coe_map] using hab)
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel]
    have key := P2a ab (⟨ab.1⁻¹ * ab'.1, hmem _ _ h1⟩, ⟨ab.2⁻¹ * ab'.2, hmem _ _ h2⟩)
    simp only [mul_inv_cancel_left] at key
    rw [← key]
  have P2c : ∀ ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      F (FibreSmooth.normPt K L ab) = Φ ab := by
    intro ab
    have h : ∃ ab' : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        FibreSmooth.normPt K L ab' = FibreSmooth.normPt K L ab := ⟨ab, rfl⟩
    simp only [hF, dif_pos h]
    exact P2b _ _ (Classical.choose_spec h)

  have P3a : IsCompact KC := hCc.image hnormPt_cont
  have P3b : ∀ y, y ∉ KC → F y = 0 := by
    intro y hy
    simp only [hF]
    by_cases h : ∃ ab : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, FibreSmooth.normPt K L ab = y
    · rw [dif_pos h]
      set ab := Classical.choose h with hab
      have hab' : FibreSmooth.normPt K L ab = y := Classical.choose_spec h
      simp only [hΦ]
      have : ∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
          G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              ((ab.1 * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
            NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              ((ab.2 * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] = 0 := by
        intro u
        by_contra hne
        obtain ⟨q, hqC, hq1, hq2⟩ := key0 ab.1 ab.2 u hne
        apply hy
        refine ⟨q, hqC, ?_⟩
        rw [← hab']
        simp only [FibreSmooth.normPt, ← hq1, ← hq2, hnormU]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall this)
    · rw [dif_neg h]
  have P3c : ∀ y, y ∉ KC → ∀ᶠ y' in nhds y, F y' = 0 := by
    intro y hy
    have hopen : IsOpen KCᶜ := P3a.isClosed.isOpen_compl
    filter_upwards [hopen.mem_nhds hy] with y' hy'
    exact P3b y' hy'

  have P4 : ∀ q ∈ C, ∃ H : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) H ∧ ∀ᶠ y in nhds (FibreSmooth.normPt K L q), F y = H y := by
    intro q hq
    obtain ⟨H, hH, hev⟩ := P4_aux K L θ G hG hGc C hCc hCG q
    refine ⟨H, hH, hev.mono fun y hy => ?_⟩
    obtain ⟨ab, hab, hHy⟩ := hy
    have hFy : F y = Φ ab := by rw [← hab]; exact P2c ab
    rw [hFy, hHy]
    simp only [hΦ, P4mg.PhiFun]

  have P5 : ∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
      Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
        G ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
            NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))])
        (θ.prod θ) := by
    intro α β
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have hc1 : Continuous fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
            ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) :=
        (C3Inst.continuous_iotaL K L).comp (Units.continuous_val.comp
          ((continuous_const.mul (continuous_subtype_val.comp continuous_fst))))
      have hc2 : Continuous fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
            ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) :=
        (C3Inst.continuous_iotaL K L).comp (Units.continuous_val.comp
          ((continuous_const.mul (continuous_subtype_val.comp continuous_snd))))
      refine hG.continuous.comp (continuous_pi fun i => ?_)
      fin_cases i
      · simpa using hc1
      · simpa using hc2
    ·
      have hce : Topology.IsClosedEmbedding (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
          (α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))) := by
        have h1 : Topology.IsClosedEmbedding (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
            ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
            ((u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))) :=
          hU1closed.isClosedEmbedding_subtypeVal.prodMap hU1closed.isClosedEmbedding_subtypeVal
        have h2 : Topology.IsClosedEmbedding (fun p : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ => (α * p.1, β * p.2)) :=
          (Homeomorph.mulLeft (α, β)).isClosedEmbedding
        exact h2.comp h1
      refine HasCompactSupport.intro (hce.isCompact_preimage hCc) ?_
      intro u hu
      by_contra hne
      obtain ⟨q, hqC, hq1, hq2⟩ := key0 α β u hne
      exact hu (by simp only [Set.mem_preimage, hq1, hq2]; exact hqC)

  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun y => ?_
    by_cases hy : y ∈ KC
    · obtain ⟨q, hq, rfl⟩ := hy
      obtain ⟨H, hH, hFH⟩ := P4 q hq
      exact (hH.contDiffAt).congr_of_eventuallyEq hFH
    · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (P3c y hy)
  · exact HasCompactSupport.intro P3a P3b
  · refine ⟨(fun q : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ =>
        (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) q.1,
         Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) q.2)) '' C,
      ?_, ?_⟩
    · exact hCc.image ((hNc.comp continuous_fst).prodMk (hNc.comp continuous_snd))
    · intro p hp
      have hp' : p ∈ KC := by
        have hsub : Function.support F ⊆ KC := fun x hx => by
          by_contra hxK; exact hx (P3b x hxK)
        exact (P3a.isClosed.closure_subset_iff.mpr hsub) hp
      obtain ⟨q, hq, rfl⟩ := hp'
      exact ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  · intro α β
    exact ⟨P5 α β, P2c (α, β)⟩

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff (solution)
