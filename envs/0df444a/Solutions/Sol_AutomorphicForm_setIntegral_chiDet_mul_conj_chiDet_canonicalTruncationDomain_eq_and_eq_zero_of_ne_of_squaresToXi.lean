-- Prove2me | solution 1 for AutomorphicForm.setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b192596c-7023-5938-b119-6ddc2e050aeb

import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm
open scoped ENNReal NNReal

noncomputable section

namespace OrthRes

section Algebra

variable {L : Type} [Field L] [NumberField L]

theorem det_diagOne {A : Type*} [CommRing A] (z : Aˣ) :
    Matrix.GeneralLinearGroup.det (AdelicLevel.diagOne z) = z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    show ((AdelicLevel.diagOne z : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![(z : A), 1] from rfl,
    Matrix.det_diagonal]
  simp

def swap (A : Type*) [CommRing A] : GL (Fin 2) A where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diagOne_mul_diagOne {A : Type*} [CommRing A] (z : Aˣ) :
    AdelicLevel.diagOne z * AdelicLevel.diagOne z =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z *
        (AdelicLevel.diagOne z * swap A * (AdelicLevel.diagOne z)⁻¹ * (swap A)⁻¹) := by
  have hinv : ((AdelicLevel.diagOne z)⁻¹ : GL (Fin 2) A) = AdelicLevel.diagOne z⁻¹ := (map_inv _ _).symm
  rw [hinv]
  refine Units.ext ?_
  simp only [Units.val_mul]
  rw [show ((AdelicLevel.diagOne z : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![(z : A), 1] from rfl,
    show ((AdelicLevel.diagOne z⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.diagonal ![((z⁻¹ : Aˣ) : A), 1] from rfl,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    show ((swap A : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0] from rfl,
    show (((swap A)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {K : Type} [Field K] [Algebra K L]

def uAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)

theorem uAct_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    uAct D σ z = Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
      AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z := rfl

theorem coe_uAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((uAct D σ z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) z := rfl

theorem uAct_mul (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ τ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    uAct D (σ * τ) z = uAct D σ (uAct D τ z) := by
  apply Units.ext
  rw [coe_uAct, coe_uAct, coe_uAct, map_mul]
  rfl

theorem uAct_one (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    uAct D 1 z = z := by
  apply Units.ext
  rw [coe_uAct, map_one]
  rfl

theorem uAct_pow (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    ∀ (k : ℕ) (z : (AdeleRing (𝓞 L) L)ˣ), uAct D (σ ^ k) z = (uAct D σ)^[k] z
  | 0, z => by rw [pow_zero, uAct_one, Function.iterate_zero, id]
  | k + 1, z => by rw [pow_succ', uAct_mul, uAct_pow D σ k z, Function.iterate_succ_apply']

theorem uAct_principal (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (u : Lˣ) :
    uAct D σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (σ : L →* L) u) := by
  apply Units.ext
  rw [coe_uAct]
  exact D.compat σ u

theorem det_sigmaAdelicAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L D σ g) = uAct D σ (Matrix.GeneralLinearGroup.det g) :=
  Matrix.GeneralLinearGroup.map_det _ _

theorem ideleNorm_uAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (uAct D σ z) = NumberField.TateGlobal.ideleNorm L z := by
  have h := AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D σ (AdelicLevel.diagOne z)
  rwa [det_sigmaAdelicAct, det_diagOne] at h

theorem chiDet_apply (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (g : AdelicGL2 (𝓞 L) L) :
    chiDet (𝓞 L) L χ g = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := rfl

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (1 : (AdeleRing (𝓞 L) L)ˣ) 1
  rw [mul_one] at h
  exact (mul_eq_left₀ (NumberField.TateGlobal.ideleNorm_pos (1 : (AdeleRing (𝓞 L) L)ˣ)).ne').mp h.symm

theorem ideleNorm_inv (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L z⁻¹ = (NumberField.TateGlobal.ideleNorm L z)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul z z⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem ideleNorm_pow (z : (AdeleRing (𝓞 L) L)ˣ) : ∀ n : ℕ,
    NumberField.TateGlobal.ideleNorm L (z ^ n) = NumberField.TateGlobal.ideleNorm L z ^ n
  | 0 => by rw [pow_zero, pow_zero, ideleNorm_one]
  | n + 1 => by rw [pow_succ, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_pow z n, pow_succ]

end Algebra

section Scaling

variable {L : Type} [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

attribute [local instance] isHaar

theorem regular_adelicGLHaar : (adelicGLHaar (Fin 2) (𝓞 L) L).Regular := by
  dsimp only [adelicGLHaar, Measure.haar]
  infer_instance

attribute [local instance] regular_adelicGLHaar

variable (L) in

def cR (g : AdelicGL2 (𝓞 L) L) : ℝ≥0 :=
  Measure.haarScalarFactor (Measure.map (· * g) (adelicGLHaar (Fin 2) (𝓞 L) L)) (adelicGLHaar (Fin 2) (𝓞 L) L)

theorem map_mul_right_eq (g : AdelicGL2 (𝓞 L) L) :
    Measure.map (· * g) (adelicGLHaar (Fin 2) (𝓞 L) L) = (cR L g : ℝ≥0∞) • adelicGLHaar (Fin 2) (𝓞 L) L := by
  haveI : (Measure.map (· * g) (adelicGLHaar (Fin 2) (𝓞 L) L)).Regular :=
    Measure.Regular.map (Homeomorph.mulRight g)
  exact Measure.isMulLeftInvariant_eq_smul_of_regular _ _

theorem cR_pos (g : AdelicGL2 (𝓞 L) L) : 0 < cR L g :=
  Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

theorem cR_ne_zero (g : AdelicGL2 (𝓞 L) L) : cR L g ≠ 0 := (cR_pos g).ne'

theorem smul_injective {a b : ℝ≥0}
    (h : (a : ℝ≥0∞) • adelicGLHaar (Fin 2) (𝓞 L) L = (b : ℝ≥0∞) • adelicGLHaar (Fin 2) (𝓞 L) L) : a = b := by
  set ν := adelicGLHaar (Fin 2) (𝓞 L) L with hν
  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 L) L)
  have hs0 : ν s ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν ⟨1, mem_interior_iff_mem_nhds.mpr hs_mem⟩).ne'
  have hstop : ν s ≠ ∞ := hs_compact.measure_lt_top.ne
  have h' := congrArg (fun m : Measure (AdelicGL2 (𝓞 L) L) => m s) h
  simp only [Measure.smul_apply, smul_eq_mul] at h'
  exact_mod_cast (ENNReal.mul_left_inj hs0 hstop).1 h'

theorem cR_one : cR L 1 = 1 := by
  apply smul_injective (L := L)
  rw [← map_mul_right_eq, ENNReal.coe_one, one_smul]
  simp only [mul_one]
  exact Measure.map_id

theorem cR_mul (g h : AdelicGL2 (𝓞 L) L) : cR L (g * h) = cR L g * cR L h := by
  apply smul_injective (L := L)
  rw [← map_mul_right_eq]
  have hcomp : (fun x : AdelicGL2 (𝓞 L) L => x * (g * h)) = (fun x => x * h) ∘ (fun x => x * g) := by
    funext x; simp only [Function.comp_apply, mul_assoc]
  rw [hcomp, ← Measure.map_map (measurable_mul_const h) (measurable_mul_const g), map_mul_right_eq,
    Measure.map_smul, map_mul_right_eq, smul_smul, ENNReal.coe_mul, mul_comm]

theorem cR_inv (g : AdelicGL2 (𝓞 L) L) : cR L g⁻¹ = (cR L g)⁻¹ := by
  have h := cR_mul g g⁻¹
  rw [mul_inv_cancel, cR_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem cR_comm (a b : AdelicGL2 (𝓞 L) L) : cR L (a * b * a⁻¹ * b⁻¹) = 1 := by
  rw [cR_mul, cR_mul, cR_mul, cR_inv, cR_inv]
  field_simp [cR_ne_zero a, cR_ne_zero b]

theorem cR_scalar (z : (AdeleRing (𝓞 L) L)ˣ) : cR L (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1 := by
  apply smul_injective (L := L)
  rw [← map_mul_right_eq, ENNReal.coe_one, one_smul]
  have hcomm : (fun x : AdelicGL2 (𝓞 L) L => x * Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      fun x => Matrix.GeneralLinearGroup.scalar (Fin 2) z * x := by
    funext x
    have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) z) x := by
      refine Commute.units_of_val ?_
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.scalar_apply]
      exact Matrix.scalar_commute _ (fun r' => Commute.all _ r') _
    exact hc.eq.symm
  rw [hcomm]
  exact MeasureTheory.map_mul_left_eq_self _ _

theorem cR_diagOne (z : (AdeleRing (𝓞 L) L)ˣ) : cR L (AdelicLevel.diagOne z) = 1 := by
  have h2 : cR L (AdelicLevel.diagOne z) ^ 2 = 1 := by
    rw [sq, ← cR_mul, diagOne_mul_diagOne, cR_mul, cR_scalar, cR_comm, one_mul]
  exact (pow_eq_one_iff_of_nonneg (cR_pos _).le two_ne_zero).mp h2

theorem measurePreserving_mul_diagOne (z : (AdeleRing (𝓞 L) L)ˣ) :
    MeasurePreserving (· * AdelicLevel.diagOne z) (adelicGLHaar (Fin 2) (𝓞 L) L) (adelicGLHaar (Fin 2) (𝓞 L) L) := by
  refine ⟨measurable_mul_const _, ?_⟩
  rw [map_mul_right_eq, cR_diagOne, ENNReal.coe_one, one_smul]

end Scaling

section Slab

variable {L : Type} [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel isHaar

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_gl2 : Countable (GL (Fin 2) L) := by
  haveI := countable_numberField (L := L)
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

scoped instance countable_range : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_gl2 (L := L)
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L))

def slab (L : Type) [Field L] [NumberField L] (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) :=
  measurableSet_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * x ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

scoped instance smulInvariantMeasure_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨g, γ₀, rfl⟩ := γ
  have hpre : (fun x : AdelicGL2 (𝓞 L) L =>
      (⟨globalPoints (𝓞 L) L γ₀, γ₀, rfl⟩ : (globalPoints (𝓞 L) L).range) • x) ⁻¹' s =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s := rfl
  rw [hpre, Measure.restrict_apply ((measurable_const_mul _) hs), Measure.restrict_apply hs]
  have hset : (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s ∩ slab L α β =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' (s ∩ slab L α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

theorem mul_mem_slab_iff {α β : ℝ} {g : AdelicGL2 (𝓞 L) L}
    (hg : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) = 1) (x : AdelicGL2 (𝓞 L) L) :
    x * g ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul, hg, mul_one]

theorem isFundamentalDomain_mul_diagOne {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (z₀ : (AdeleRing (𝓞 L) L)ˣ) (hz₀ : NumberField.TateGlobal.ideleNorm L z₀ = 1) :
    IsFundamentalDomain (globalPoints (𝓞 L) L).range ((· * AdelicLevel.diagOne z₀) '' Φ)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  set g₀ := AdelicLevel.diagOne z₀ with hg₀
  have hdet : ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z = 1 →
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (AdelicLevel.diagOne z)) = 1 := by
    intro z hz; rwa [det_diagOne]

  have hz₀' : NumberField.TateGlobal.ideleNorm L z₀⁻¹ = 1 := by rw [ideleNorm_inv, hz₀, inv_one]
  have hmp : MeasurePreserving (· * AdelicLevel.diagOne z₀⁻¹)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
    have h := (measurePreserving_mul_diagOne (L := L) z₀⁻¹).restrict_preimage (measurableSet_slab α β)
    have hpre : (· * AdelicLevel.diagOne z₀⁻¹) ⁻¹' slab L α β = slab L α β :=
      Set.ext fun x => mul_mem_slab_iff (hdet _ hz₀') x
    rwa [hpre] at h
  have himg : (· * AdelicLevel.diagOne z₀) '' Φ = (Equiv.mulRight g₀) '' Φ := rfl
  rw [himg]
  refine hΦ.image_of_equiv (Equiv.mulRight g₀) ?_ (Equiv.refl _) fun γ x => ?_
  · have hsymm : ((Equiv.mulRight g₀).symm : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) =
        (· * AdelicLevel.diagOne z₀⁻¹) := by
      funext x
      rw [Equiv.mulRight_symm, hg₀, ← map_inv]
      rfl
    rw [hsymm]
    exact hmp.quasiMeasurePreserving
  · show (γ • x) * g₀ = γ • (x * g₀)
    obtain ⟨g, γ₁, rfl⟩ := γ
    exact mul_assoc _ _ _

end Slab

section Orth

variable {L : Type} [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel isHaar

theorem setIntegral_chiDet_eq_zero {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦs : Φ ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (ρ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hρt : ∀ u : Lˣ, ρ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) = 1)
    (z₀ : (AdeleRing (𝓞 L) L)ˣ) (hz₀ : NumberField.TateGlobal.ideleNorm L z₀ = 1) (hρ : ρ z₀ ≠ 1) :
    ∫ x in Φ, chiDet (𝓞 L) L ρ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set g₀ := AdelicLevel.diagOne z₀ with hg₀
  set F : AdelicGL2 (𝓞 L) L → ℂ := chiDet (𝓞 L) L ρ with hF
  set Φ₁ := (· * g₀) '' Φ with hΦ₁
  have hΦ₁s : Φ₁ ⊆ slab L α β := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mul_mem_slab_iff (by rw [hg₀, det_diagOne, hz₀]) x).2 (hΦs hx)
  have hΦ₁fd := isFundamentalDomain_mul_diagOne hΦ z₀ hz₀

  have hFinv : ∀ (γ : (globalPoints (𝓞 L) L).range) (x : AdelicGL2 (𝓞 L) L), F (γ • x) = F x := by
    rintro ⟨g, γ, rfl⟩ x
    show F (globalPoints (𝓞 L) L γ * x) = F x
    simp only [hF, chiDet_apply, map_mul, Units.val_mul]
    have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L γ) =
        Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Matrix.GeneralLinearGroup.det γ) :=
      Matrix.GeneralLinearGroup.map_det _ γ
    rw [hdet, hρt, Units.val_one, one_mul]

  have h1 : ∫ x in Φ, F x ∂μ = ∫ x in Φ₁, F x ∂μ := by
    have e := hΦ.setIntegral_eq hΦ₁fd (f := F) hFinv
    rwa [Measure.restrict_restrict_of_subset hΦs, Measure.restrict_restrict_of_subset hΦ₁s] at e

  have h2 : ∫ x in Φ₁, F x ∂μ = ∫ x in Φ, F (x * g₀) ∂μ :=
    (measurePreserving_mul_diagOne (L := L) z₀).setIntegral_image_emb
      (MeasurableEquiv.mulRight g₀).measurableEmbedding F Φ

  have h3 : ∫ x in Φ, F (x * g₀) ∂μ = (∫ x in Φ, F x ∂μ) * ((ρ z₀ : ℂˣ) : ℂ) := by
    rw [← integral_mul_const]
    congr 1
    funext x
    simp only [hF, chiDet_apply, map_mul, Units.val_mul, hg₀, det_diagOne]
  have key : (∫ x in Φ, F x ∂μ) * (1 - ((ρ z₀ : ℂˣ) : ℂ)) = 0 := by
    rw [mul_sub, mul_one, ← h3, ← h2, ← h1, sub_self]
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd (Units.val_eq_one.mp (sub_eq_zero.mp h).symm) hρ

end Orth

section Rigidity

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField L] in

theorem exists_norm_eq (u : InfinitePlace L) {t : ℝ} (ht : 0 < t) :
    ∃ y : (u.Completion)ˣ, ‖(y : u.Completion)‖ = t := by
  by_cases hu : u.IsReal
  · set e := InfinitePlace.Completion.ringEquivRealOfIsReal hu with he
    have hn : ‖e.symm t‖ = t := by
      rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hu).norm_map_of_map_zero (map_zero _),
        ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hu, RingEquiv.apply_symm_apply, Real.norm_eq_abs,
        abs_of_pos ht]
    have h0 : e.symm t ≠ 0 := fun h => by rw [h, norm_zero] at hn; exact ht.ne' hn.symm.symm.symm
    exact ⟨Units.mk0 _ h0, hn⟩
  · have hu' : u.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hu
    set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hu' with he
    have hn : ‖e.symm (t : ℂ)‖ = t := by
      rw [← (InfinitePlace.Completion.isometry_extensionEmbedding u).norm_map_of_map_zero (map_zero _),
        ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hu', RingEquiv.apply_symm_apply,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have h0 : e.symm (t : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hn; exact ht.ne' hn.symm.symm.symm
    exact ⟨Units.mk0 _ h0, hn⟩

theorem ideleNorm_archUnitHom (u : InfinitePlace L) (y : (u.Completion)ˣ) :
    NumberField.TateGlobal.ideleNorm L (NumberField.TateGlobal.archUnitHom u y) = ‖(y : u.Completion)‖ ^ u.mult := by
  classical
  unfold NumberField.TateGlobal.ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm L]
  have h1 : ∏ w : InfinitePlace L,
      ‖((NumberField.TateGlobal.archUnitHom u y : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 w‖ ^ w.mult =
        ‖(y : u.Completion)‖ ^ u.mult := by
    rw [Finset.prod_eq_single u]
    · rw [show ((NumberField.TateGlobal.archUnitHom u y : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 u = y from
        NumberField.AdelicVolume.archCentralUnit_fst_self u y]
    · intro w _ hw
      rw [show ((NumberField.TateGlobal.archUnitHom u y : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 w = 1 from
        NumberField.AdelicVolume.archCentralUnit_fst_of_ne u y hw, norm_one, one_pow]
    · intro h; exact absurd (Finset.mem_univ u) h
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 L),
      ‖((NumberField.TateGlobal.archUnitHom u y : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [show ((NumberField.TateGlobal.archUnitHom u y : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 = 1 from
      NumberField.AdelicVolume.archCentralUnit_snd u y, AdelicLevel.coe_one_apply, norm_one]
  rw [h1, h2, mul_one]

theorem exists_ideleNorm_pow_eq {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    ∃ a : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L (a ^ m) = r := by
  obtain ⟨u⟩ := (inferInstance : Nonempty (InfinitePlace L))
  set e : ℕ := u.mult * m with he
  have he0 : e ≠ 0 := Nat.mul_ne_zero (by have := u.mult_pos; omega) hm.ne'
  set t : ℝ := r ^ ((e : ℝ)⁻¹) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hr _
  obtain ⟨y, hy⟩ := exists_norm_eq u htpos
  refine ⟨NumberField.TateGlobal.archUnitHom u y, ?_⟩
  rw [ideleNorm_pow, ideleNorm_archUnitHom, hy, ← pow_mul, ← he, ht, Real.rpow_inv_natCast_pow hr.le he0]

theorem forall_apply_uAct_eq (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (h1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z = 1 → χ (uAct D σ z) = χ z) :
    ∀ z : (AdeleRing (𝓞 L) L)ˣ, χ (uAct D σ z) = χ z := by

  set ρ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := (χ.comp (uAct D σ)) * χ⁻¹ with hρ
  have hρ_apply : ∀ z, ρ z = χ (uAct D σ z) * (χ z)⁻¹ := fun z => rfl
  have hρ1 : ∀ z, NumberField.TateGlobal.ideleNorm L z = 1 → ρ z = 1 := by
    intro z hz
    rw [hρ_apply, h1 z hz, mul_inv_cancel]

  have hρσ : ∀ z, ρ (uAct D σ z) = ρ z := by
    intro z
    have hw : NumberField.TateGlobal.ideleNorm L (uAct D σ z * z⁻¹) = 1 := by
      rw [NumberField.TateGlobal.ideleNorm_mul, ideleNorm_uAct, ideleNorm_inv,
        mul_inv_cancel₀ (NumberField.TateGlobal.ideleNorm_pos z).ne']
    have h := hρ1 _ hw
    rw [map_mul, map_inv, mul_inv_eq_one] at h
    exact h
  have hρσk : ∀ (k : ℕ) (z), ρ ((uAct D σ)^[k] z) = ρ z := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih => intro z; rw [Function.iterate_succ_apply', hρσ, ih]

  have hiter : ∀ (k : ℕ) (z), χ ((uAct D σ)^[k] z) = ρ z ^ k * χ z := by
    intro k
    induction k with
    | zero => intro z; rw [Function.iterate_zero, id, pow_zero, one_mul]
    | succ k ih =>
      intro z
      have e1 : χ (uAct D σ ((uAct D σ)^[k] z)) = ρ ((uAct D σ)^[k] z) * χ ((uAct D σ)^[k] z) := by
        rw [hρ_apply, inv_mul_cancel_right]
      rw [Function.iterate_succ_apply', e1, hρσk, ih, pow_succ]
      group

  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  set m : ℕ := orderOf σ with hm
  have hmpos : 0 < m := orderOf_pos σ
  have hρm : ∀ z, ρ z ^ m = 1 := by
    intro z
    have h := hiter m z
    rw [← uAct_pow, hm, pow_orderOf_eq_one, uAct_one] at h
    exact (mul_eq_right.mp h.symm)

  intro z
  suffices hz : ρ z = 1 by
    have := hρ_apply z
    rw [hz] at this
    exact ((eq_mul_inv_iff_mul_eq.mp this).symm.trans (one_mul _))
  obtain ⟨a, ha⟩ := exists_ideleNorm_pow_eq (L := L) hmpos (NumberField.TateGlobal.ideleNorm_pos z)
  have hw : NumberField.TateGlobal.ideleNorm L (z * (a ^ m)⁻¹) = 1 := by
    rw [NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv, ha, mul_inv_cancel₀ (NumberField.TateGlobal.ideleNorm_pos z).ne']
  have hz : z = z * (a ^ m)⁻¹ * a ^ m := by rw [inv_mul_cancel_right]
  rw [hz, map_mul, hρ1 _ hw, one_mul, map_pow, hρm]

end Rigidity

end OrthRes
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi.OrthRes"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (χ χ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (_hχ : SquaresToXi (𝓞 K) K ⊤ ξK χ) (_hχ' : SquaresToXi (𝓞 K) K ⊤ ξK χ')
    (_hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (_hχ'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ' z : ℂˣ) : ℂ))
    (_hχu : ∀ z, ‖((χ z : ℂˣ) : ℂ)‖ = 1) (_hχ'u : ∀ z, ‖((χ' z : ℂˣ) : ℂ)‖ = 1)
    (_hχt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1)
    (_hχ't : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ' z = 1) :
    (χ = χ' → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        chiDet (𝓞 K) K χ g * conj (chiDet (𝓞 K) K χ' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ)) ∧
    (χ ≠ χ' → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        chiDet (𝓞 K) K χ g * conj (chiDet (𝓞 K) K χ' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) := by
  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ

  have hconj : ∀ g : AdelicGL2 (𝓞 K) K, conj (chiDet (𝓞 K) K χ' g) = ((χ' (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂ) := by
    intro g
    exact (Complex.inv_eq_conj (_hχ'u _)).symm
  constructor
  · intro h
    subst h
    have h1 : ∀ g : AdelicGL2 (𝓞 K) K, chiDet (𝓞 K) K χ g * conj (chiDet (𝓞 K) K χ g) = 1 := by
      intro g
      rw [hconj]
      exact mul_inv_cancel₀ (Units.ne_zero _)
    simp_rw [h1]
    rw [setIntegral_const, Complex.real_smul, mul_one]
    rfl
  · intro hne
    set η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := χ * χ'⁻¹ with hη
    have hint : ∀ g : AdelicGL2 (𝓞 K) K, chiDet (𝓞 K) K χ g * conj (chiDet (𝓞 K) K χ' g) = chiDet (𝓞 K) K η g := by
      intro g
      rw [hconj]
      show _ = (((χ * χ'⁻¹) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
      rfl
    simp_rw [hint]

    have hηt : ∀ u : Kˣ, η (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 1 := by
      intro u
      rw [hη, MonoidHom.mul_apply, MonoidHom.inv_apply, _hχt _ ⟨u, rfl⟩, _hχ't _ ⟨u, rfl⟩, inv_one, mul_one]

    have hne' : ∃ z, η z ≠ 1 := by
      by_contra h
      simp only [not_exists, not_not] at h
      apply hne
      ext z
      have := h z
      rw [hη, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
      rw [this]
    obtain ⟨z, hz⟩ := hne'

    have hsq : ∀ w, η w ^ 2 = 1 := by
      intro w
      have h1 := _hχ ⟨w, Subgroup.mem_top w⟩
      have h2 := _hχ' ⟨w, Subgroup.mem_top w⟩
      rw [hη, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow]
      change χ w ^ 2 * (χ' w ^ 2)⁻¹ = 1
      rw [h1, h2, mul_inv_cancel]

    obtain ⟨w, hw⟩ := OrthRes.exists_ideleNorm_pow_eq (L := K) (m := 2) two_pos (NumberField.TateGlobal.ideleNorm_pos z)
    set z₀ := z * (w ^ 2)⁻¹ with hz₀
    have hz₀n : NumberField.TateGlobal.ideleNorm K z₀ = 1 := by
      rw [hz₀, NumberField.TateGlobal.ideleNorm_mul, OrthRes.ideleNorm_inv, hw,
        mul_inv_cancel₀ (NumberField.TateGlobal.ideleNorm_pos z).ne']
    have hz₀η : η z₀ ≠ 1 := by
      rw [hz₀, map_mul, map_inv, map_pow, hsq, inv_one, mul_one]; exact hz
    exact OrthRes.setIntegral_chiDet_eq_zero hΦs hΦ η hηt z₀ hz₀n hz₀η

end
end S_AutomorphicForm_setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi (solution)
