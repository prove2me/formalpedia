-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_finsum_sub_indicator_highSet_constantTerm_finsum_borel_le_of_subset_centreCutSiegelSet_translates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/74b6e352-ecf3-509b-88be-6c15ad7af923

import Theorems.Thm_AutomorphicForm_exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
import Theorems.Thm_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_finsum_sub_indicator_highSet_constantTerm_finsum_borel_le_of_subset_centreCutSiegelSet_translates
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

namespace R4CellBound

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal
open NumberField.AdelicLevel NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Function Set
open scoped ENNReal NNReal Topology Pointwise

section Instances

variable (L : Type) [Field L] [NumberField L]

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

end Instances

section Algebra

variable (L : Type) [Field L] [NumberField L]

theorem coe_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((centralScalar (𝓞 L) L z : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; simpa [Matrix.scalar_apply] using continuous_id'
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * g = g * centralScalar (𝓞 L) L z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_centralScalar]
  exact (Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 L) L) (fun r' => Commute.all _ r') _).eq

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z) = z ^ 2 := by
  have h : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      z ^ Fintype.card (Fin 2) := Matrix.GeneralLinearGroup.det_scalar z
  rw [Fintype.card_fin] at h
  exact h

theorem det_unipotentGL2 (t : AdeleRing (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 t : AdelicGL2 (𝓞 L) L) = 1 := by
  refine Units.ext ?_
  show ((unipotentGL2 t : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).det = 1
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

theorem ideleNorm_one : ideleNorm L 1 = 1 := by
  have h := ideleNorm_mul (F := L) 1 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (ideleNorm_pos (F := L) 1).ne' (h.symm.trans (mul_one _).symm)

theorem ideleNorm_inv (u : (AdeleRing (𝓞 L) L)ˣ) : ideleNorm L u⁻¹ = (ideleNorm L u)⁻¹ := by
  have h := ideleNorm_mul (F := L) u u⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem ideleNorm_pow_two (u : (AdeleRing (𝓞 L) L)ˣ) : ideleNorm L (u ^ 2) = ideleNorm L u ^ 2 := by
  rw [pow_two, pow_two, ideleNorm_mul]

private theorem _root_.R4CellBound.continuous_ideleNorm_det :
    Continuous fun g : AdelicGL2 (𝓞 L) L => ideleNorm L (Matrix.GeneralLinearGroup.det g) :=
  NumberField.TateGlobal.continuous_ideleNorm_det L

p2m_export "R4CellBound" "continuous_ideleNorm_det"

theorem ideleNorm_det_karg (θ : AdelicGL2 (𝓞 L) L →* AdelicGL2 (𝓞 L) L)
    (hθ : ∀ g, ideleNorm L (Matrix.GeneralLinearGroup.det (θ g)) = ideleNorm L (Matrix.GeneralLinearGroup.det g))
    (x w : AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (Matrix.GeneralLinearGroup.det
        (x⁻¹ * globalPoints (𝓞 L) L δ * θ (w * (centralScalar (𝓞 L) L z * x)))) =
      ideleNorm L (Matrix.GeneralLinearGroup.det w) * ideleNorm L z ^ 2 := by
  rw [map_mul, map_mul, map_inv, ideleNorm_mul, ideleNorm_mul, ideleNorm_inv,
    AutomorphicForm.ideleNorm_det_globalPoints, hθ, map_mul, map_mul, det_centralScalar,
    ideleNorm_mul, ideleNorm_mul, ideleNorm_pow_two, mul_one]
  have hx : ideleNorm L (Matrix.GeneralLinearGroup.det x) ≠ 0 := (ideleNorm_pos (F := L) _).ne'
  field_simp

end Algebra

section Modulus

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem ideleNorm_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) =
      ideleNorm L z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph
  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne
  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* _) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b
  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl
  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    convert Set.image_id s
    exact θ.apply_symm_apply _
  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1
  have hcancel : distribHaarChar (AdeleRing (𝓞 L) L) w = distribHaarChar (AdeleRing (𝓞 L) L) z := by
    have := congrArg (fun t => t / μ s) h1
    beta_reduce at this
    rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this
  unfold NumberField.TateGlobal.ideleNorm
  rw [hw] at hcancel
  exact_mod_cast congrArg (fun t : ℝ≥0 => (t : ℝ)) hcancel

theorem ideleNorm_det_sigmaAdelicAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) :
    ideleNorm L (Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L D σ g)) =
      ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
  unfold sigmaAdelicAct
  rw [Matrix.GeneralLinearGroup.map_det]
  exact ideleNorm_unitsMap_act K L D σ _

end Modulus

section Lift

variable (L : Type) [Field L] [NumberField L]

theorem mem_Icc_sqrt_of_sq_mem_Icc {t m₀ M₀ : ℝ} (ht : 0 ≤ t) (h : t ^ 2 ∈ Set.Icc m₀ M₀) :
    t ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) :=
  ⟨by rw [← Real.sqrt_sq ht]; exact Real.sqrt_le_sqrt h.1,
    (Real.le_sqrt ht (le_trans (sq_nonneg t) h.2)).mpr h.2⟩

theorem exists_isCompact_forall_mem_exists_princ_mul {m₁ M₁ : ℝ} (hm₁ : 0 < m₁) :
    ∃ C : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact C ∧
      ∀ z : (AdeleRing (𝓞 L) L)ˣ, ideleNorm L z ∈ Set.Icc m₁ M₁ →
        ∃ (a : Lˣ) (c : (AdeleRing (𝓞 L) L)ˣ), c ∈ C ∧
          z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a * c := by
  obtain ⟨C₁, hC₁c, -, hC₁⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L
  obtain ⟨s, hs_cont, hs_norm, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L
  set S₁ : Set ℝ≥0ˣ := {r | ((r : ℝ≥0) : ℝ) ∈ Set.Icc m₁ M₁} with hS₁
  have hS₁c : IsCompact S₁ := by
    set a₀ : ℝ≥0 := ⟨m₁, hm₁.le⟩ with ha₀
    set b₀ : ℝ≥0 := Real.toNNReal M₁ with hb₀
    have ha₀pos : 0 < a₀ := hm₁
    have hpre : IsCompact (Units.embedProduct ℝ≥0 ⁻¹'
        (Set.Icc a₀ b₀ ×ˢ (MulOpposite.op '' Set.Icc b₀⁻¹ a₀⁻¹))) :=
      Units.isClosedEmbedding_embedProduct.isCompact_preimage
        (isCompact_Icc.prod (isCompact_Icc.image MulOpposite.continuous_op))
    refine hpre.of_isClosed_subset (isClosed_Icc.preimage (NNReal.continuous_coe.comp Units.continuous_val)) ?_
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have hrpos : 0 < (r : ℝ≥0) := lt_of_lt_of_le ha₀pos hr1
    have h1 : a₀ ≤ (r : ℝ≥0) := hr1
    have h2 : (r : ℝ≥0) ≤ b₀ := (Real.le_toNNReal_iff_coe_le (le_trans (le_trans hm₁.le hr1) hr2)).mpr hr2
    show ((r : ℝ≥0), MulOpposite.op ((r⁻¹ : ℝ≥0ˣ) : ℝ≥0)) ∈
      Set.Icc a₀ b₀ ×ˢ (MulOpposite.op '' Set.Icc b₀⁻¹ a₀⁻¹)
    refine Set.mk_mem_prod ⟨h1, h2⟩ ⟨(r : ℝ≥0)⁻¹, ⟨inv_anti₀ hrpos h2, inv_anti₀ ha₀pos h1⟩, ?_⟩
    rw [Units.val_inv_eq_inv_val]
  refine ⟨C₁ * s '' S₁, hC₁c.mul (hS₁c.image hs_cont), fun z hz => ?_⟩
  have hzpos : 0 < ideleNorm L z := ideleNorm_pos (F := L) z
  set r : ℝ≥0ˣ := Units.mk0 (⟨ideleNorm L z, hzpos.le⟩ : ℝ≥0)
    (fun h => hzpos.ne' (congrArg Subtype.val h)) with hr
  have hrS : r ∈ S₁ := hz
  have hsr : ideleNorm L (s r) = ideleNorm L z := hs_norm r
  have hz₁ : z * (s r)⁻¹ ∈ normOneIdeles L := by
    rw [mem_normOneIdeles_iff, ideleNorm_mul, ideleNorm_inv, hsr, mul_inv_cancel₀ hzpos.ne']
  obtain ⟨η, κ, hκ, hzκ⟩ := hC₁ _ hz₁
  refine ⟨η, κ * s r, Set.mul_mem_mul hκ ⟨r, hrS, rfl⟩, ?_⟩
  rw [← mul_assoc]
  exact mul_inv_eq_iff_eq_mul.mp hzκ

end Lift

section Kernel

variable (L : Type) [Field L] [NumberField L]

theorem finite_karg_mem {C : Set (AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) (x y : AdelicGL2 (𝓞 L) L) :
    {γ : GL (Fin 2) L | x⁻¹ * globalPoints (𝓞 L) L γ * y ∈ C}.Finite :=
  AutomorphicForm.adelicKernelLocalFiniteness L C hC x y

theorem finite_karg_mem_of_isCompact {P : Type*} [TopologicalSpace P] {a b : P → AdelicGL2 (𝓞 L) L}
    (ha : Continuous a) (hb : Continuous b) {N : Set P} (hN : IsCompact N)
    {C : Set (AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) :
    {γ : GL (Fin 2) L | ∃ p ∈ N, (a p)⁻¹ * globalPoints (𝓞 L) L γ * b p ∈ C}.Finite := by
  set ψ : P × AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L := fun q => a q.1 * q.2 * (b q.1)⁻¹ with hψ
  have hψc : Continuous ψ :=
    ((ha.comp continuous_fst).mul continuous_snd).mul (hb.comp continuous_fst).inv
  have hC' : IsCompact (ψ '' (N ×ˢ C)) := (hN.prod hC).image hψc
  refine (finite_karg_mem L hC' 1 1).subset ?_
  rintro γ ⟨p, hp, hmem⟩
  simp only [Set.mem_setOf_eq, inv_one, one_mul, mul_one]
  refine ⟨(p, (a p)⁻¹ * globalPoints (𝓞 L) L γ * b p), ⟨hp, hmem⟩, ?_⟩
  simp only [hψ]
  group

theorem continuous_kernelAlong {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P]
    {a b : P → AdelicGL2 (𝓞 L) L} (ha : Continuous a) (hb : Continuous b)
    {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous fun p : P => ∑ᶠ γ : GL (Fin 2) L, φ ((a p)⁻¹ * globalPoints (𝓞 L) L γ * b p) := by
  classical
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨N, hN, hNp⟩ := exists_compact_mem_nhds p₀
  have hfin := finite_karg_mem_of_isCompact L ha hb hN hφc.isCompact
  set T : Finset (GL (Fin 2) L) := hfin.toFinset with hTdef
  have heq : Set.EqOn
      (fun p : P => ∑ γ ∈ T, φ ((a p)⁻¹ * globalPoints (𝓞 L) L γ * b p))
      (fun p : P => ∑ᶠ γ : GL (Fin 2) L, φ ((a p)⁻¹ * globalPoints (𝓞 L) L γ * b p)) N := by
    intro p hp
    refine (finsum_eq_sum_of_support_subset _ fun γ hγ => ?_).symm
    rw [Finset.mem_coe, hTdef, Set.Finite.mem_toFinset]
    exact ⟨p, hp, subset_tsupport _ hγ⟩
  have hcont : Continuous fun p : P => ∑ γ ∈ T, φ ((a p)⁻¹ * globalPoints (𝓞 L) L γ * b p) :=
    continuous_finsetSum _ fun γ _ => hφ.comp ((ha.inv.mul continuous_const).mul hb)
  exact hcont.continuousAt.congr_of_eventuallyEq
    ((Filter.eventuallyEq_of_mem hNp heq).symm)

theorem kernel_eq_zero_of_forall {x y : AdelicGL2 (𝓞 L) L} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (h : ∀ γ : GL (Fin 2) L, φ (x⁻¹ * globalPoints (𝓞 L) L γ * y) = 0) :
    ∑ᶠ γ : GL (Fin 2) L, φ (x⁻¹ * globalPoints (𝓞 L) L γ * y) = 0 :=
  finsum_eq_zero_of_forall_eq_zero h

end Kernel

section Galois

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

abbrev actU (σ : L ≃ₐ[K] L) : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : R)).map f : Matrix (Fin 2) (Fin 2) S) =
    Matrix.scalar (Fin 2) (f (a : R))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

theorem globalPoints_scalar (a : Lˣ) :
    globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = centralScalar (𝓞 L) L (princ L a) :=
  map_scalar (algebraMap L (AdeleRing (𝓞 L) L)) a

theorem sigmaAdelicAct_centralScalar (σ : L ≃ₐ[K] L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L w) = centralScalar (𝓞 L) L (actU K L D σ w) :=
  map_scalar (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom w

theorem actU_princ (σ : L ≃ₐ[K] L) (a : Lˣ) :
    actU K L D σ (princ L a) = princ L (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a) := by
  refine Units.ext ?_
  exact D.compat σ (a : L)

theorem sigmaAdelicAct_globalPoints' (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) :=
  sigmaAdelicAct_globalPoints K L D σ γ

theorem actU_symm_apply (σ : L ≃ₐ[K] L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    actU K L D σ.symm (actU K L D σ w) = w := by
  refine Units.ext ?_
  show (D.act σ.symm : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (w : AdeleRing (𝓞 L) L))
    = (w : AdeleRing (𝓞 L) L)
  have h : (D.act σ.symm : RingAut (AdeleRing (𝓞 L) L)) * D.act σ = 1 := by
    rw [← map_mul, show σ.symm * σ = 1 from ?_, map_one]
    ext y
    exact σ.symm_apply_apply y
  have := congrArg (fun f : RingAut (AdeleRing (𝓞 L) L) => f (w : AdeleRing (𝓞 L) L)) h
  simpa using this

theorem actU_apply_symm (σ : L ≃ₐ[K] L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    actU K L D σ (actU K L D σ.symm w) = w := by
  simpa using actU_symm_apply K L D σ.symm w

theorem ideleNorm_actU (σ : L ≃ₐ[K] L) (w : (AdeleRing (𝓞 L) L)ˣ) : ideleNorm L (actU K L D σ w) = ideleNorm L w :=
  ideleNorm_unitsMap_act K L D σ w

end Galois

section Heights

variable (L : Type) [Field L] [NumberField L]

theorem finLocalHeight_scalar_mul {k : Type*} [NormedField k] {a : k} (ha : a ≠ 0)
    (s g : GL (Fin 2) k)
    (h00 : (s : Matrix (Fin 2) (Fin 2) k) 0 0 = a) (h01 : (s : Matrix (Fin 2) (Fin 2) k) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) k) 1 1 = a) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hcoe : ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (s : Matrix (Fin 2) (Fin 2) k) * (g : Matrix (Fin 2) (Fin 2) k) := rfl
  have hs : (s : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  have hmul : ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = a • (g : Matrix (Fin 2) (Fin 2) k) := by
    rw [hcoe, hs, smul_mul_assoc, one_mul]
  have hdet : ‖((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det‖ =
      ‖a‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) k).det‖ := by
    rw [hmul, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow]
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ‖a‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) k) := by
    unfold rowMaxNorm
    rw [hmul, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, norm_mul, norm_mul,
      mul_max_of_nonneg _ _ (norm_nonneg a)]
  have ha' : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hr : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) k) := rowMaxNorm_pos g
  unfold finLocalHeight
  rw [hdet, hrow, mul_pow]
  field_simp

theorem idele_arch_ne_zero (z : (AdeleRing (𝓞 L) L)ˣ) (v : InfinitePlace L) :
    (z : AdeleRing (𝓞 L) L).1 v ≠ 0 :=
  (Units.map ((archEval L v).comp (adeleArch (𝓞 L) L)).toMonoidHom z).ne_zero

theorem idele_fin_ne_zero (z : (AdeleRing (𝓞 L) L)ˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    (z : AdeleRing (𝓞 L) L).2 v ≠ 0 :=
  (Units.map ((finAdeleEval (𝓞 L) L v).comp (adeleFin (𝓞 L) L)).toMonoidHom z).ne_zero

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    adelicHeight L (centralScalar (𝓞 L) L z * g) = adelicHeight L g := by
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · refine archHeight_scalar_entries_mul L (z := (z : AdeleRing (𝓞 L) L).1)
      (idele_arch_ne_zero L z) ?_ ?_ ?_ ?_ _
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_mul (a := (z : AdeleRing (𝓞 L) L).2 v) (idele_fin_ne_zero L z v)
      _ _ ?_ ?_ ?_ ?_
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl

theorem archHeight_unipotentGL2_mul (t : AdeleRing (𝓞 L) L) (x : AdelicGL2 (𝓞 L) L) :
    archHeight L (glArch (𝓞 L) L (unipotentGL2 t * x)) = archHeight L (glArch (𝓞 L) L x) := by
  rw [map_mul]
  unfold archHeight
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_mul]
  congr 1
  have h00 : (archComponent L v (glArch (𝓞 L) L (unipotentGL2 t)) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 0 = 1 := rfl
  have h10 : (archComponent L v (glArch (𝓞 L) L (unipotentGL2 t)) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 0 = 0 := rfl
  have h11 : (archComponent L v (glArch (𝓞 L) L (unipotentGL2 t)) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 1 = 1 := rfl
  have h := SiegelCoordinates.localHeight_upper_entries_mul one_ne_zero h00 h10 h11
    (archComponent L v (glArch (𝓞 L) L x))
  simpa using h

theorem glFin_unipotentGL2_mem {t : AdeleRing (𝓞 L) L} (ht : t ∈ AdelicBox.adelicBox L) :
    glFin (𝓞 L) L (unipotentGL2 t) ∈ finiteIntegralGL2 (𝓞 L) L := by
  have h2 : t.2 ∈ integralFiniteAdeles (𝓞 L) L := ht.2
  have hneg : (-t).2 ∈ integralFiniteAdeles (𝓞 L) L := by
    have := sub_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles h2
    simp at this
    exact this
  rw [mem_finiteIntegralGL2_iff, ← map_inv]
  have e00 : (glFin (𝓞 L) L (unipotentGL2 t) :
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)) 0 0 = 1 := rfl
  have e01 : (glFin (𝓞 L) L (unipotentGL2 t) :
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)) 0 1 = t.2 := rfl
  have e10 : (glFin (𝓞 L) L (unipotentGL2 t) :
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)) 1 0 = 0 := rfl
  have e11 : (glFin (𝓞 L) L (unipotentGL2 t) :
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)) 1 1 = 1 := rfl
  have hinv : (((unipotentGL2 t)⁻¹ : AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = !![1, -t; 0, 1] := rfl
  have hM : (glFin (𝓞 L) L (unipotentGL2 t)⁻¹ :
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)) = !![1, (-t).2; 0, 1] := by
    ext i j
    rw [glFin_apply, hinv]
    fin_cases i <;> fin_cases j <;> rfl
  refine ⟨?_, ?_⟩
  swap
  · rw [hM]
    intro i j
    fin_cases i <;> fin_cases j
    · exact one_mem_integralFiniteAdeles
    · exact hneg
    · exact zero_mem_integralFiniteAdeles
    · exact one_mem_integralFiniteAdeles
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [e00] using (one_mem_integralFiniteAdeles :
        (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) ∈ integralFiniteAdeles (𝓞 L) L)
    · simpa [e01] using h2
    · simpa [e10] using (zero_mem_integralFiniteAdeles :
        (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) ∈ integralFiniteAdeles (𝓞 L) L)
    · simpa [e11] using (one_mem_integralFiniteAdeles :
        (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) ∈ integralFiniteAdeles (𝓞 L) L)

end Heights

section KernelAlgebra

variable (L : Type) [Field L] [NumberField L]

theorem adelicKernel_def (φ : AdelicGL2 (𝓞 L) L → ℂ) (a b : AdelicGL2 (𝓞 L) L) :
    adelicKernel L φ a b = ∑ᶠ γ : GL (Fin 2) L, φ (a⁻¹ * globalPoints (𝓞 L) L γ * b) := rfl

theorem centralScalar_mul_globalPoints_mul (w : (AdeleRing (𝓞 L) L)ˣ) (γ : GL (Fin 2) L) (h : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * (globalPoints (𝓞 L) L γ * h) = globalPoints (𝓞 L) L γ * (centralScalar (𝓞 L) L w * h) := by
  rw [← mul_assoc, centralScalar_comm L w (globalPoints (𝓞 L) L γ), mul_assoc]

theorem adelicKernel_globalPoints_centralScalar_mul (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (γ₁ γ₂ : GL (Fin 2) L) (v₁ v₂ : (AdeleRing (𝓞 L) L)ˣ) (a b : AdelicGL2 (𝓞 L) L) :
    adelicKernel L φ (globalPoints (𝓞 L) L γ₁ * centralScalar (𝓞 L) L v₁ * a)
        (globalPoints (𝓞 L) L γ₂ * centralScalar (𝓞 L) L v₂ * b) =
      adelicKernel L φ a (centralScalar (𝓞 L) L (v₁⁻¹ * v₂) * b) := by
  unfold adelicKernel
  refine finsum_eq_of_bijective (fun γ => γ₁⁻¹ * γ * γ₂)
    ((Group.mulRight_bijective γ₂).comp (Group.mulLeft_bijective γ₁⁻¹)) fun γ => ?_
  congr 1
  simp only [map_mul, mul_inv_rev, ← map_inv, mul_assoc, centralScalar_mul_globalPoints_mul]

theorem adelicKernel_globalPoints_mul_left (φ : AdelicGL2 (𝓞 L) L → ℂ) (γ₁ : GL (Fin 2) L)
    (a b : AdelicGL2 (𝓞 L) L) :
    adelicKernel L φ (globalPoints (𝓞 L) L γ₁ * a) b = adelicKernel L φ a b := by
  have h := adelicKernel_globalPoints_centralScalar_mul L φ γ₁ 1 1 1 a b
  simpa using h

theorem adelicKernel_globalPoints_mul_right (φ : AdelicGL2 (𝓞 L) L → ℂ) (γ₂ : GL (Fin 2) L)
    (a b : AdelicGL2 (𝓞 L) L) :
    adelicKernel L φ a (globalPoints (𝓞 L) L γ₂ * b) = adelicKernel L φ a b := by
  have h := adelicKernel_globalPoints_centralScalar_mul L φ 1 γ₂ 1 1 a b
  simpa using h

theorem continuous_adelicKernel₂ {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L => adelicKernel L φ p.1 p.2 :=
  continuous_kernelAlong L continuous_fst continuous_snd hφ hφc

end KernelAlgebra

section Pieces

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (φ : AdelicGL2 (𝓞 L) L → ℂ)

def Afun (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  adelicKernel L φ x (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))

def AIfun (I : Set (GL (Fin 2) L)) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ∑ᶠ γ ∈ I, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))

def BA (A : Set L) : Set (GL (Fin 2) L) :=
  {γ | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A}

def BiAfun (A : Set L) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) (t : AdeleRing (𝓞 L) L) : ℂ :=
  ∑ᶠ γ ∈ BA L A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 t * (centralScalar (𝓞 L) L z * x)))

theorem sigmaAdelicAct_centralScalar_princ (a : Lˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (princ L a)) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a)) := by
  rw [sigmaAdelicAct_centralScalar, actU_princ, globalPoints_scalar]

theorem Afun_princ_mul (x : AdelicGL2 (𝓞 L) L) (a : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    Afun K L D σ φ x (princ L a * z) = Afun K L D σ φ x z := by
  unfold Afun
  rw [map_mul (centralScalar (𝓞 L) L), mul_assoc, map_mul (sigmaAdelicAct K L D σ),
    sigmaAdelicAct_centralScalar_princ, adelicKernel_globalPoints_mul_right]

theorem finsum_mem_globalPoints_scalar_mul {I : Set (GL (Fin 2) L)}
    (hI : ∀ γ ∈ I, ∀ a : Lˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ I) (s : Lˣ)
    (F : AdelicGL2 (𝓞 L) L → ℂ) (x W : AdelicGL2 (𝓞 L) L) :
    ∑ᶠ γ ∈ I, F (x⁻¹ * globalPoints (𝓞 L) L γ *
        (globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) s) * W)) =
      ∑ᶠ γ ∈ I, F (x⁻¹ * globalPoints (𝓞 L) L γ * W) := by
  refine finsum_mem_eq_of_bijOn (fun γ => γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) ⟨?_, ?_, ?_⟩ ?_
  · intro γ hγ; exact hI γ hγ s
  · intro γ _ γ' _ h; exact mul_right_cancel h
  · intro γ hγ
    refine ⟨γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹, hI γ hγ s⁻¹, ?_⟩
    show γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) s = γ
    rw [map_inv, inv_mul_cancel_right]
  · intro γ _
    show F (x⁻¹ * globalPoints (𝓞 L) L γ * (globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) s) * W)) =
      F (x⁻¹ * globalPoints (𝓞 L) L (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) * W)
    rw [map_mul]; simp only [mul_assoc]

omit [NumberField L] in

theorem mul_scalar_mem_BA (A : Set L) : ∀ γ ∈ BA L A, ∀ a : Lˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ BA L A := by
  intro γ hγ a
  obtain ⟨h10, hr⟩ := hγ
  have hcoe : ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      (a : L) • (γ : Matrix (Fin 2) (Fin 2) L) := by
    rw [Units.val_mul]
    change (γ : Matrix (Fin 2) (Fin 2) L) * Matrix.scalar (Fin 2) (a : L) = _
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · show ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
    rw [hcoe, Matrix.smul_apply, h10, smul_zero]
  · show ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 /
        ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A
    rw [hcoe, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_mul_left _ _ a.ne_zero]
    exact hr

theorem AIfun_princ_mul {I : Set (GL (Fin 2) L)}
    (hI : ∀ γ ∈ I, ∀ a : Lˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ I)
    (x : AdelicGL2 (𝓞 L) L) (a : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    AIfun K L D σ φ I x (princ L a * z) = AIfun K L D σ φ I x z := by
  unfold AIfun
  rw [map_mul (centralScalar (𝓞 L) L), mul_assoc, map_mul (sigmaAdelicAct K L D σ),
    sigmaAdelicAct_centralScalar_princ]
  exact finsum_mem_globalPoints_scalar_mul L hI _ φ x _

theorem BiAfun_princ_mul (A : Set L) (x : AdelicGL2 (𝓞 L) L) (a : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) (t : AdeleRing (𝓞 L) L) :
    BiAfun K L D σ φ A x (princ L a * z) t = BiAfun K L D σ φ A x z t := by
  unfold BiAfun
  rw [map_mul (centralScalar (𝓞 L) L), mul_assoc, ← mul_assoc (unipotentGL2 t), ← centralScalar_comm L, mul_assoc,
    map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_centralScalar_princ]
  exact finsum_mem_globalPoints_scalar_mul L (mul_scalar_mem_BA L A) _ φ x _

theorem continuous_Afun (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Afun K L D σ φ p.1 p.2 := by
  unfold Afun adelicKernel
  exact continuous_kernelAlong L continuous_fst ((continuous_sigmaAdelicAct K L D σ).comp
    (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst)) hφ hφc

theorem sq_ideleNorm_mem_of_ne_zero (x w : AdelicGL2 (𝓞 L) L) (γ : GL (Fin 2) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (hw : ideleNorm L (Matrix.GeneralLinearGroup.det w) = 1)
    (hne : φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (w * (centralScalar (𝓞 L) L z * x))) ≠ 0) :
    ideleNorm L z ^ 2 ∈ (fun g : AdelicGL2 (𝓞 L) L => ideleNorm L (Matrix.GeneralLinearGroup.det g)) '' tsupport φ := by
  refine ⟨_, subset_tsupport _ hne, ?_⟩
  show ideleNorm L (Matrix.GeneralLinearGroup.det _) = _
  rw [ideleNorm_det_karg L (sigmaAdelicAct K L D σ) (ideleNorm_det_sigmaAdelicAct K L D σ), hw, one_mul]

theorem Afun_eq_zero_of_not_mem {x : AdelicGL2 (𝓞 L) L} {z : (AdeleRing (𝓞 L) L)ˣ}
    (hz : ideleNorm L z ^ 2 ∉ (fun g : AdelicGL2 (𝓞 L) L => ideleNorm L (Matrix.GeneralLinearGroup.det g)) '' tsupport φ) :
    Afun K L D σ φ x z = 0 := by
  unfold Afun adelicKernel
  refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
  by_contra hne
  have h1 : φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (1 * (centralScalar (𝓞 L) L z * x))) ≠ 0 := by
    rwa [one_mul]
  exact hz (sq_ideleNorm_mem_of_ne_zero K L D σ φ x 1 γ z (by rw [map_one, ideleNorm_one]) h1)

theorem AIfun_eq_zero_of_not_mem (I : Set (GL (Fin 2) L)) {x : AdelicGL2 (𝓞 L) L} {z : (AdeleRing (𝓞 L) L)ˣ}
    (hz : ideleNorm L z ^ 2 ∉ (fun g : AdelicGL2 (𝓞 L) L => ideleNorm L (Matrix.GeneralLinearGroup.det g)) '' tsupport φ) :
    AIfun K L D σ φ I x z = 0 := by
  unfold AIfun
  refine finsum_mem_eq_zero_of_forall_eq_zero fun γ _ => ?_
  by_contra hne
  have h1 : φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (1 * (centralScalar (𝓞 L) L z * x))) ≠ 0 := by
    rwa [one_mul]
  exact hz (sq_ideleNorm_mem_of_ne_zero K L D σ φ x 1 γ z (by rw [map_one, ideleNorm_one]) h1)

theorem BiAfun_eq_zero_of_not_mem (A : Set L) {x : AdelicGL2 (𝓞 L) L} {z : (AdeleRing (𝓞 L) L)ˣ} (t : AdeleRing (𝓞 L) L)
    (hz : ideleNorm L z ^ 2 ∉ (fun g : AdelicGL2 (𝓞 L) L => ideleNorm L (Matrix.GeneralLinearGroup.det g)) '' tsupport φ) :
    BiAfun K L D σ φ A x z t = 0 := by
  unfold BiAfun
  refine finsum_mem_eq_zero_of_forall_eq_zero fun γ _ => ?_
  by_contra hne
  exact hz (sq_ideleNorm_mem_of_ne_zero K L D σ φ x (unipotentGL2 t) γ z (by rw [det_unipotentGL2, ideleNorm_one]) hne)

omit [NumberField L] in

theorem finsum_mem_eq_of_forall_ne_zero_iff {ι : Type*} {s t : Set ι} {h : ι → ℂ}
    (H : ∀ i, h i ≠ 0 → (i ∈ s ↔ i ∈ t)) : ∑ᶠ i ∈ s, h i = ∑ᶠ i ∈ t, h i := by
  classical
  rw [finsum_mem_def, finsum_mem_def]
  refine finsum_congr fun i => ?_
  by_cases hi : h i = 0
  · simp [Set.indicator_apply, hi]
  · by_cases his : i ∈ s
    · rw [Set.indicator_of_mem his, Set.indicator_of_mem ((H i hi).mp his)]
    · rw [Set.indicator_of_notMem his, Set.indicator_of_notMem (fun hit => his ((H i hi).mpr hit))]

omit [NumberField L] in

theorem norm_finsum_mem_le_norm_finsum_norm {ι : Type*} (s : Set ι) {h : ι → ℂ} (hh : (Function.support h).Finite) :
    ‖∑ᶠ i ∈ s, h i‖ ≤ ‖∑ᶠ i, ((‖h i‖ : ℝ) : ℂ)‖ := by
  classical
  have hs : (s ∩ Function.support h).Finite := hh.subset Set.inter_subset_right
  rw [finsum_mem_eq_sum _ hs]
  have hsupp : (Function.support fun i => ((‖h i‖ : ℝ) : ℂ)) ⊆ hh.toFinset := by
    intro i hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    apply hi
    simp [h0]
  rw [finsum_eq_sum_of_support_subset _ hsupp, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  calc ‖∑ i ∈ hs.toFinset, h i‖ ≤ ∑ i ∈ hs.toFinset, ‖h i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ hh.toFinset, ‖h i‖ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => norm_nonneg _
        intro i hi
        rw [Set.Finite.mem_toFinset] at hi ⊢
        exact hi.2

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel in

theorem constantTerm_eq_integral_BiAfun (μ : Measure (AdeleRing (𝓞 L) L)) (A : Set L) (x : AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    constantTerm μ (fun t => unipotentGL2 t)
        (fun y => ∑ᶠ γ ∈ BA L A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y))
        (centralScalar (𝓞 L) L z * x) = ∫ t, BiAfun K L D σ φ A x z t ∂μ := by
  unfold constantTerm constantTermIntegrand BiAfun
  rfl

theorem norm_AIfun_le (hφc : HasCompactSupport φ) (I : Set (GL (Fin 2) L)) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ‖AIfun K L D σ φ I x z‖ ≤ ‖Afun K L D σ (fun g => ((‖φ g‖ : ℝ) : ℂ)) x z‖ := by
  unfold AIfun Afun adelicKernel
  refine norm_finsum_mem_le_norm_finsum_norm I ?_
  exact (finite_karg_mem L hφc.isCompact x _).subset fun γ hγ => subset_tsupport _ hγ

end Pieces

section Bulk

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem centralScalar_mul_mul (w : (AdeleRing (𝓞 L) L)ˣ) (g h : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * (g * h) = g * (centralScalar (𝓞 L) L w * h) := by
  rw [← mul_assoc, centralScalar_comm L w g, mul_assoc]

theorem Afun_eq_of_cover (φ : AdelicGL2 (𝓞 L) L → ℂ) {s k y : AdelicGL2 (𝓞 L) L} {γ₁ : GL (Fin 2) L}
    {z' : (AdeleRing (𝓞 L) L)ˣ} (hk : globalPoints (𝓞 L) L γ₁ * s * centralScalar (𝓞 L) L z' = k)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    Afun K L D σ φ (s * y) z =
      Afun K L D σ φ (k * y) (actU K L D σ.symm (z' * (actU K L D σ z * (actU K L D σ z')⁻¹))) := by
  have hs : s = (globalPoints (𝓞 L) L γ₁)⁻¹ * k * (centralScalar (𝓞 L) L z')⁻¹ := by
    rw [← hk]; group
  unfold Afun
  have h1 : s * y = globalPoints (𝓞 L) L γ₁⁻¹ * centralScalar (𝓞 L) L z'⁻¹ * (k * y) := by
    rw [hs]
    simp only [← map_inv, mul_assoc, centralScalar_mul_mul]
  have h2 : sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (s * y)) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ₁⁻¹) *
        centralScalar (𝓞 L) L (actU K L D σ z * actU K L D σ z'⁻¹) * sigmaAdelicAct K L D σ (k * y) := by
    rw [h1]
    simp only [map_mul, sigmaAdelicAct_centralScalar, sigmaAdelicAct_globalPoints', mul_assoc,
      centralScalar_mul_globalPoints_mul]
  have h3 : sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L
        (actU K L D σ.symm (z' * (actU K L D σ z * (actU K L D σ z')⁻¹))) * (k * y)) =
      centralScalar (𝓞 L) L ((z'⁻¹)⁻¹ * (actU K L D σ z * actU K L D σ z'⁻¹)) * sigmaAdelicAct K L D σ (k * y) := by
    rw [map_mul, sigmaAdelicAct_centralScalar, actU_apply_symm, inv_inv, map_inv]
  rw [h2, h1, h3]
  exact adelicKernel_globalPoints_centralScalar_mul L φ _ _ _ _ _ _

theorem exists_bound_Afun_of_adelicHeight_le
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AdelicGL2 (𝓞 L) L)) (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet L c u d₁ d₂)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {a b : ℝ} (ha : 0 < a) (Tcap : ℝ) :
    ∃ C₁ : ℝ, ∀ x ∈ S, adelicHeight L x ≤ Tcap → ∀ z : (AdeleRing (𝓞 L) L)ˣ, ideleNorm L z ∈ Set.Icc a b →
      ‖Afun K L D σ φ x z‖ ≤ C₁ := by

  obtain ⟨κ, Kup, hκ, hdist⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact L Tc hTc

  set n : ℕ := ∑ w : InfinitePlace L, w.mult with hn
  have hcn : 0 < c ^ n := pow_pos hc n
  obtain ⟨Kc, hKc, hcov⟩ := WindowedSiegel.exists_isCompact_cover_of_archHeight_le L (c ^ n) u (Tcap / κ) hcn

  obtain ⟨W₀, hW₀c, hW₀⟩ := exists_isCompact_forall_mem_exists_princ_mul L (M₁ := b) ha

  have hcont : Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Afun K L D σ φ p.1 p.2 :=
    continuous_Afun K L D σ φ hφ hφc
  obtain ⟨C₁, hC₁⟩ := ((hKc.mul hTc).prod hW₀c).exists_bound_of_continuousOn (f := fun p => Afun K L D σ φ p.1 p.2)
    hcont.continuousOn
  refine ⟨C₁, fun x hx hxT z hz => ?_⟩

  obtain ⟨y, hy, s, hs, rfl⟩ : ∃ y ∈ Tc, ∃ s ∈ centreCutSiegelSet L c u d₁ d₂, s * y = x := by
    have := hS hx
    simp only [Set.mem_iUnion, Set.mem_image] at this
    obtain ⟨y, hy, s, hs, hsx⟩ := this
    exact ⟨y, hy, s, hs, hsx⟩

  have hsint : glFin (𝓞 L) L s ∈ finiteIntegralGL2 (𝓞 L) L := hs.1
  have hsw : s ∈ integralWindowedSiegelSet L (c ^ n) u :=
    centreCutSiegelSet_subset_integralWindowedSiegelSet hc.le hs
  have hHs : archHeight L (glArch (𝓞 L) L s) ≤ Tcap / κ := by
    rw [← adelicHeight_eq_archHeight_of_mem hsint, le_div_iff₀ hκ, mul_comm]
    exact ((hdist s y hy).1).trans hxT
  obtain ⟨γ₁, z', -, hk⟩ := hcov s hsw hHs
  set k := globalPoints (𝓞 L) L γ₁ * s * centralScalar (𝓞 L) L z' with hkdef

  set w : (AdeleRing (𝓞 L) L)ˣ := z' * (actU K L D σ z * (actU K L D σ z')⁻¹) with hw
  set ζ : (AdeleRing (𝓞 L) L)ˣ := actU K L D σ.symm w with hζ
  have hζn : ideleNorm L ζ ∈ Set.Icc a b := by
    have hzn : ideleNorm L z' ≠ 0 := (ideleNorm_pos (F := L) z').ne'
    have : ideleNorm L ζ = ideleNorm L z := by
      rw [hζ, ideleNorm_actU, hw, ideleNorm_mul, ideleNorm_mul, ideleNorm_inv, ideleNorm_actU, ideleNorm_actU]
      field_simp
    rw [this]; exact hz
  obtain ⟨a₀, ζ₀, hζ₀, hζeq⟩ := hW₀ ζ hζn
  have hA : Afun K L D σ φ (s * y) z = Afun K L D σ φ (k * y) ζ₀ := by
    rw [Afun_eq_of_cover K L D σ φ rfl z, ← hkdef, ← hw, ← hζ, hζeq, Afun_princ_mul]
  rw [hA]
  exact hC₁ (k * y, ζ₀) ⟨Set.mul_mem_mul hk hy, hζ₀⟩

end Bulk

section Support

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem karg_rearrange (s y w : AdelicGL2 (𝓞 L) L) (γ : GL (Fin 2) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (s * y)⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (w * (centralScalar (𝓞 L) L z * (s * y))) =
      y⁻¹ * (s⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (w * s)) *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y) := by
  simp only [map_mul, mul_inv_rev, sigmaAdelicAct_centralScalar, mul_assoc, centralScalar_mul_mul]

theorem exists_forall_apply_one_zero_eq_zero
    (c u d₁ d₂ : ℝ)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AdelicGL2 (𝓞 L) L)) (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet L c u d₁ d₂)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ)
    (Z₀ : Set (AdeleRing (𝓞 L) L)ˣ) (hZ₀ : IsCompact Z₀) :
    ∃ T₂ : ℝ, ∀ x ∈ S, T₂ < adelicHeight L x → ∀ z ∈ Z₀, ∀ γ : GL (Fin 2) L,
      φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x)) ≠ 0 →
        (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by

  obtain ⟨κ, Kup, hκ, hdist⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact L Tc hTc

  set F : (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L) × ((AdeleRing (𝓞 L) L)ˣ × AdelicGL2 (𝓞 L) L) →
      AdelicGL2 (𝓞 L) L := fun q => q.1.1 * q.1.2 * (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L q.2.1 * q.2.2))⁻¹
    with hF
  have hFc : Continuous F :=
    ((continuous_fst.comp continuous_fst).mul (continuous_snd.comp continuous_fst)).mul
      ((continuous_sigmaAdelicAct K L D σ).comp (((continuous_centralScalar L).comp
        (continuous_fst.comp continuous_snd)).mul (continuous_snd.comp continuous_snd))).inv
  set Cbig : Set (AdelicGL2 (𝓞 L) L) := F '' ((Tc ×ˢ tsupport φ) ×ˢ (Z₀ ×ˢ Tc)) with hCbig
  have hCbigc : IsCompact Cbig := ((hTc.prod hφc.isCompact).prod (hZ₀.prod hTc)).image hFc
  obtain ⟨T₉, hT₉⟩ := WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem L hCbigc
  refine ⟨Kup * max T₉ 0, fun x hx hxT z hz => ?_⟩

  obtain ⟨y, hy, s, hs, rfl⟩ : ∃ y ∈ Tc, ∃ s ∈ centreCutSiegelSet L c u d₁ d₂, s * y = x := by
    have := hS hx
    simp only [Set.mem_iUnion, Set.mem_image] at this
    obtain ⟨y, hy, s, hs, hsx⟩ := this
    exact ⟨y, hy, s, hs, hsx⟩
  have hsint : glFin (𝓞 L) L s ∈ finiteIntegralGL2 (𝓞 L) L := hs.1

  have hHs : T₉ < archHeight L (glArch (𝓞 L) L s) := by
    rw [← adelicHeight_eq_archHeight_of_mem hsint]
    have h1 : adelicHeight L (s * y) ≤ Kup * adelicHeight L s := (hdist s y hy).2
    have hpos : 0 < adelicHeight L (s * y) := adelicHeight_pos _
    have hspos : 0 < adelicHeight L s := adelicHeight_pos _
    by_cases hK : Kup ≤ 0
    · exact absurd (h1.trans (mul_nonpos_of_nonpos_of_nonneg hK hspos.le)) (not_le.mpr hpos)
    · replace hK : 0 < Kup := not_le.mp hK
      have h2 : Kup * max T₉ 0 < Kup * adelicHeight L s := hxT.trans_le h1
      exact (le_max_left _ _).trans_lt (lt_of_mul_lt_mul_left h2 hK.le)

  intro γ hne
  have hσ := AutomorphicForm.archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
    K L D σ (1 * s)
  refine hT₉ s (sigmaAdelicAct K L D σ (1 * s)) hsint (hσ.2 ?_) hHs ?_ γ ?_
  · rw [map_mul, map_one]; exact Subgroup.mul_mem _ (Subgroup.one_mem _) hsint
  · rw [hσ.1, one_mul]; exact hHs
  · have hne' : φ ((s * y)⁻¹ * globalPoints (𝓞 L) L γ *
        sigmaAdelicAct K L D σ (1 * (centralScalar (𝓞 L) L z * (s * y)))) ≠ 0 := by rwa [one_mul]
    rw [karg_rearrange] at hne'
    have hmem : y⁻¹ * (s⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (1 * s)) *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y) ∈ tsupport φ := subset_tsupport _ hne'
    refine ⟨((y, _), (z, y)), ⟨⟨hy, hmem⟩, hz, hy⟩, ?_⟩
    simp only [hF]
    group

end Support

section Main

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem mainC (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AdelicGL2 (𝓞 L) L)) (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet L c u d₁ d₂)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφf : IsFactorizableTestFn L φ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ C : ℝ,
      ∀ (A : Set L) (I : Set (GL (Fin 2) L)),
        (∀ γ ∈ I, ∀ a : Lˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ I) →
        (∀ γ : GL (Fin 2) L, (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 →
            (γ ∈ I ↔ (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A)) →
        ∀ x ∈ S, ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ‖AIfun K L D σ φ I x z -
              Set.indicator (highSet (adelicHeight L) T)
                (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (AdelicBox.adelicBox L))
                  (fun t => unipotentGL2 t)
                  (fun y => ∑ᶠ γ ∈ BA L A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y)))
                (centralScalar (𝓞 L) L z * x)‖ ≤ C := by
  obtain ⟨hφ, hφc⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hφf
  set μb : Measure (AdeleRing (𝓞 L) L) := ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (AdelicBox.adelicBox L)
    with hμb

  set ψ : AdelicGL2 (𝓞 L) L → ℂ := fun g => ((‖φ g‖ : ℝ) : ℂ) with hψ
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp hφ.norm
  have hψs : HasCompactSupport ψ := (hφc.norm).comp_left Complex.ofReal_zero

  set Dn : Set ℝ := (fun g : AdelicGL2 (𝓞 L) L => ideleNorm L (Matrix.GeneralLinearGroup.det g)) '' tsupport φ with hDn
  have hDnc : IsCompact Dn := hφc.isCompact.image (continuous_ideleNorm_det L)

  have hval : ∀ (T : ℝ) (A : Set L) (I : Set (GL (Fin 2) L)) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      AIfun K L D σ φ I x z -
          Set.indicator (highSet (adelicHeight L) T)
            (constantTerm μb (fun t => unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ BA L A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y)))
            (centralScalar (𝓞 L) L z * x) =
        AIfun K L D σ φ I x z - if T < adelicHeight L x then ∫ t, BiAfun K L D σ φ A x z t ∂μb else 0 := by
    intro T A I x z
    have h2 := constantTerm_eq_integral_BiAfun K L D σ φ μb A x z
    congr 1
    by_cases hT : T < adelicHeight L x
    · rw [if_pos hT, Set.indicator_of_mem, h2]
      show T < adelicHeight L (centralScalar (𝓞 L) L z * x)
      rwa [adelicHeight_centralScalar_mul]
    · rw [if_neg hT, Set.indicator_of_notMem]
      show ¬ (T < adelicHeight L (centralScalar (𝓞 L) L z * x))
      rwa [adelicHeight_centralScalar_mul]

  rcases Dn.eq_empty_or_nonempty with hDe | hDne
  · refine ⟨0, fun T _ => ⟨0, fun A I _ _ x _ z => ?_⟩⟩
    have hz : ideleNorm L z ^ 2 ∉ Dn := by rw [hDe]; exact Set.notMem_empty _
    rw [hval, AIfun_eq_zero_of_not_mem K L D σ φ I hz]
    have hB : (fun t => BiAfun K L D σ φ A x z t) = fun _ => 0 := by
      funext t; exact BiAfun_eq_zero_of_not_mem K L D σ φ A t hz
    rw [hB, integral_zero]
    simp

  set a : ℝ := Real.sqrt (sInf Dn) with ha
  set b : ℝ := Real.sqrt (sSup Dn) with hb
  have hDpos : ∀ d ∈ Dn, 0 < d := by
    rintro _ ⟨g, _, rfl⟩; exact ideleNorm_pos (F := L) _
  have ha0 : 0 < a := Real.sqrt_pos.mpr (hDpos _ (hDnc.sInf_mem hDne))
  have hband : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ideleNorm L z ^ 2 ∈ Dn → ideleNorm L z ∈ Set.Icc a b := fun z hz =>
    mem_Icc_sqrt_of_sq_mem_Icc (ideleNorm_pos (F := L) z).le ⟨csInf_le hDnc.bddBelow hz, le_csSup hDnc.bddAbove hz⟩
  obtain ⟨Z₀, hZ₀c, hZ₀⟩ := exists_isCompact_forall_mem_exists_princ_mul L (M₁ := b) ha0

  obtain ⟨T₁, hT₁⟩ :=
    AutomorphicForm.exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
      K L D σ c u d₁ d₂ hc Tc hTc S hS φ hφf
  obtain ⟨C₂, hC₂⟩ := hT₁ 0
  obtain ⟨T₂, hT₂⟩ := exists_forall_apply_one_zero_eq_zero K L D σ c u d₁ d₂ Tc hTc S hS φ hφc Z₀ hZ₀c
  refine ⟨max T₁ T₂, fun T hT => ?_⟩

  obtain ⟨C₁, hC₁⟩ := exists_bound_Afun_of_adelicHeight_le K L D σ c u d₁ d₂ hc Tc hTc S hS ψ hψc hψs (b := b) ha0 T
  refine ⟨max (max C₁ C₂) 0, fun A I hIZ hIB x hx z => ?_⟩
  rw [hval]
  by_cases hzD : ideleNorm L z ^ 2 ∈ Dn
  swap
  ·
    rw [AIfun_eq_zero_of_not_mem K L D σ φ I hzD]
    have hB : (fun t => BiAfun K L D σ φ A x z t) = fun _ => 0 := by
      funext t; exact BiAfun_eq_zero_of_not_mem K L D σ φ A t hzD
    rw [hB, integral_zero]
    simp
  by_cases hTx : T < adelicHeight L x
  swap
  ·
    rw [if_neg hTx, sub_zero]
    exact ((norm_AIfun_le K L D σ φ hφc I x z).trans (hC₁ x hx (not_lt.mp hTx) z (hband z hzD))).trans
      ((le_max_left _ _).trans (le_max_left _ _))

  rw [if_pos hTx]
  obtain ⟨a₀, z₀, hz₀, rfl⟩ := hZ₀ _ (hband _ hzD)
  have hxT₂ : T₂ < adelicHeight L x := ((le_max_right _ _).trans hT).trans_lt hTx
  have hxT₁ : T₁ < adelicHeight L x := ((le_max_left _ _).trans hT).trans_lt hTx
  have hkey := hT₂ x hx hxT₂ z₀ hz₀
  have hAI : AIfun K L D σ φ I x z₀ =
      ∑ᶠ γ ∈ BA L A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z₀ * x)) := by
    unfold AIfun
    refine finsum_mem_eq_of_forall_ne_zero_iff fun γ hγ => ?_
    have h10 := hkey γ hγ
    rw [hIB γ h10]
    exact ⟨fun h => ⟨h10, h⟩, fun h => h.2⟩
  have hper : AIfun K L D σ φ I x (princ L a₀ * z₀) - ∫ t, BiAfun K L D σ φ A x (princ L a₀ * z₀) t ∂μb =
      (∑ᶠ γ ∈ BA L A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z₀ * x))) -
        constantTerm μb (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ BA L A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y))
          (centralScalar (𝓞 L) L z₀ * x) := by
    have hB : ∀ t, BiAfun K L D σ φ A x (princ L a₀ * z₀) t = BiAfun K L D σ φ A x z₀ t :=
      fun t => BiAfun_princ_mul K L D σ φ A x a₀ z₀ t
    simp only [hB]
    rw [AIfun_princ_mul K L D σ φ hIZ, hAI, constantTerm_eq_integral_BiAfun]
  rw [hper]
  have h := hC₂ A x hx hxT₁ z₀
  simp only [pow_zero, mul_one] at h
  exact h.trans ((le_max_right _ _).trans (le_max_left _ _))

end Main

end R4CellBound

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφf : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ C : ℝ,
      ∀ (A : Set L) (I : Set (Matrix.GeneralLinearGroup (Fin 2) L)),
        (∀ γ ∈ I, ∀ a : Lˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ I) →
        (∀ γ : Matrix.GeneralLinearGroup (Fin 2) L, (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 →
            (γ ∈ I ↔ (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A)) →
        ∀ x ∈ S, ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ‖(∑ᶠ γ ∈ I,
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) T)
                (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                      (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)‖ ≤ C :=
  R4CellBound.mainC K L D σ c u d₁ d₂ hc Tc hTc S hS φ hφf

end

end S_AutomorphicForm_exists_forall_norm_finsum_sub_indicator_highSet_constantTerm_finsum_borel_le_of_subset_centreCutSiegelSet_translates
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_finsum_sub_indicator_highSet_constantTerm_finsum_borel_le_of_subset_centreCutSiegelSet_translates (solution)
