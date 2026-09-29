-- Prove2me | solution 1 for AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/831fa4b8-582a-5fcd-8c8d-c75c3a08562f

import Theorems.Thm_AutomorphicForm_integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization
import Theorems.Thm_AutomorphicForm_setIntegral_chiDet_sigmaAdelicAct_mul_chiDet_inv_eq_zero_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm AdelicDock
open scoped ComplexConjugate TensorProduct TensorProduct.RightActions NumberField.PlaceTransport Pointwise

namespace R4ResSigma

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def emb (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    GL (Fin 2) (w.adicCompletion L) →* AdelicGL2 (𝓞 L) L :=
  (finEmbed (𝓞 L) L).comp (localEmbed (𝓞 L) L w)

theorem glArch_emb (w : HeightOneSpectrum (𝓞 L)) (y : GL (Fin 2) (w.adicCompletion L)) :
    glArch (𝓞 L) L (emb L w y) = 1 := glArch_finEmbed _ _ _

theorem glFin_emb (w : HeightOneSpectrum (𝓞 L)) (y : GL (Fin 2) (w.adicCompletion L)) :
    glFin (𝓞 L) L (emb L w y) = localEmbed (𝓞 L) L w y := glFin_finEmbed _ _ _

def idl (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w t)

def idlHom (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    (w.adicCompletion L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  (Units.map (finIncl (𝓞 L) L : FiniteAdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)).comp (localUnit (𝓞 L) L w)

theorem idlHom_apply (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) : idlHom L w t = idl L w t := rfl

theorem idl_fst (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    ((idl L w t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem idl_snd_self (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    ((idl L w t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w = t := by
  show ((localUnit (𝓞 L) L w t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w = t
  exact localUnit_apply_self (𝓞 L) L w t

theorem idl_snd_of_ne (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) {w' : HeightOneSpectrum (𝓞 L)}
    (hw : w' ≠ w) : ((idl L w t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w' = 1 := by
  show ((localUnit (𝓞 L) L w t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w' = 1
  exact localUnit_apply_of_ne (𝓞 L) L w t hw

theorem localChar_eq_idl (η : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 L))
    (t : (w.adicCompletion L)ˣ) : TateGlobal.localChar η w t = η (idl L w t) := rfl

theorem uniformizerIdele_eq_idl (w : HeightOneSpectrum (𝓞 L)) :
    uniformizerIdele L w = idl L w (uniformizerUnit L w) := rfl

theorem det_heckeGen (w : HeightOneSpectrum (𝓞 L)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w) = idl L w (uniformizerUnit L w) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![((idl L w (uniformizerUnit L w) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1]).det = _
  rw [Matrix.det_diagonal]
  simp

theorem emb_apply_fst (w : HeightOneSpectrum (𝓞 L)) (y : GL (Fin 2) (w.adicCompletion L)) (i j : Fin 2) :
    (((emb L w y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j := by
  rw [← glArch_apply, glArch_emb, Units.val_one]

theorem emb_apply_snd_self (w : HeightOneSpectrum (𝓞 L)) (y : GL (Fin 2) (w.adicCompletion L)) (i j : Fin 2) :
    (((emb L w y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 w =
      (y : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j := by
  show (finComponent (𝓞 L) L w (glFin (𝓞 L) L (emb L w y)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j = _
  rw [glFin_emb, finComponent_localEmbed_self]

theorem emb_apply_snd_of_ne (w : HeightOneSpectrum (𝓞 L)) (y : GL (Fin 2) (w.adicCompletion L)) (i j : Fin 2)
    {w' : HeightOneSpectrum (𝓞 L)} (hw : w' ≠ w) :
    (((emb L w y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 w' =
      (1 : Matrix (Fin 2) (Fin 2) (w'.adicCompletion L)) i j := by
  show (finComponent (𝓞 L) L w' (glFin (𝓞 L) L (emb L w y)) : Matrix (Fin 2) (Fin 2) (w'.adicCompletion L)) i j = _
  rw [glFin_emb, finComponent_localEmbed_of_ne (𝓞 L) L w y hw, Units.val_one]

theorem det_emb (w : HeightOneSpectrum (𝓞 L)) (y : GL (Fin 2) (w.adicCompletion L)) :
    Matrix.GeneralLinearGroup.det (emb L w y) = idl L w (Matrix.GeneralLinearGroup.det y) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  set M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) :=
    ((emb L w y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) with hM
  refine Prod.ext ?_ ?_
  · rw [idl_fst]
    have h1 : (M.det).1 = ((adeleArch (𝓞 L) L).mapMatrix M).det := by
      rw [← RingHom.map_det]; rfl
    have h2 : (adeleArch (𝓞 L) L).mapMatrix M = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]
      exact emb_apply_fst w y i j
    rw [h1, h2, Matrix.det_one]
  · refine FiniteAdeleRing.ext L fun w' => ?_
    have h1 : (M.det).2 w' = (((finAdeleEval (𝓞 L) L w').comp (adeleFin (𝓞 L) L)).mapMatrix M).det := by
      rw [← RingHom.map_det]; rfl
    rw [h1]
    by_cases hw : w' = w
    · subst hw
      rw [idl_snd_self, Matrix.GeneralLinearGroup.val_det_apply]
      congr 1
      ext i j : 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      exact emb_apply_snd_self w' y i j
    · rw [idl_snd_of_ne w _ hw]
      have h2 : ((finAdeleEval (𝓞 L) L w').comp (adeleFin (𝓞 L) L)).mapMatrix M = 1 := by
        ext i j : 1
        rw [RingHom.mapMatrix_apply, Matrix.map_apply]
        exact emb_apply_snd_of_ne w y i j hw
      rw [h2, Matrix.det_one]

theorem chiDet_apply (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (g : AdelicGL2 (𝓞 L) L) :
    chiDet (𝓞 L) L χ g = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := rfl

theorem chiDet_emb (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 L))
    (y : GL (Fin 2) (w.adicCompletion L)) :
    chiDet (𝓞 L) L χ (emb L w y) = ((TateGlobal.localChar χ w (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) := by
  rw [chiDet, det_emb, localChar_eq_idl]

theorem chiDet_mul (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (x y : AdelicGL2 (𝓞 L) L) :
    chiDet (𝓞 L) L χ (x * y) = chiDet (𝓞 L) L χ x * chiDet (𝓞 L) L χ y := by
  simp only [chiDet, map_mul, Units.val_mul]

theorem chiDet_ne_zero (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (x : AdelicGL2 (𝓞 L) L) :
    chiDet (𝓞 L) L χ x ≠ 0 := Units.ne_zero _

theorem chiDet_mul_chiDet_inv (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (x : AdelicGL2 (𝓞 L) L) :
    chiDet (𝓞 L) L χ x * chiDet (𝓞 L) L χ⁻¹ x = 1 := by
  simp only [chiDet, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact mul_inv_cancel₀ (Units.ne_zero _)

theorem continuous_chiDet {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ}
    (hχ : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)) :
    Continuous (chiDet (𝓞 L) L χ) :=
  hχ.comp (Matrix.GeneralLinearGroup.continuous_det)

def chiHat (w : HeightOneSpectrum (𝓞 L)) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) : ℂ :=
  ((χ (uniformizerIdele L w) : ℂˣ) : ℂ)

theorem chiHat_ne_zero (w : HeightOneSpectrum (𝓞 L)) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) : chiHat w χ ≠ 0 :=
  Units.ne_zero _

section SemiLocal

variable (K L)
variable (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v (semiLocalEval K L v a) w = a w.1 := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => finAdeleEval (𝓞 L) L w.1 a)) w = a w.1
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem semiLocalEval_mem_semiLocalIntegers_iff (a : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v a ∈ semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), a w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  refine forall_congr' fun w => ?_
  rw [semiLocalHomeomorph_semiLocalEval, SetLike.mem_coe]

theorem semiLocalComponent_mem_iff (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v ↔
      ∀ w : v.Extension (𝓞 L), finComponent (𝓞 L) L w.1 h ∈ localIntegralSet L w.1 := by
  rw [semiLocalIntegralSet, mem_integralUnitsSet]
  have e : ∀ (g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2),
      (semiLocalComponent K L v g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
        semiLocalEval K L v ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) := fun _ _ _ => rfl
  simp only [← map_inv, e, semiLocalEval_mem_semiLocalIntegers_iff, mem_localIntegralSet, finComponent_apply]
  constructor
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w⟩
  · intro hw
    exact ⟨fun i j w => (hw w).1 i j, fun i j w => (hw w).2 i j⟩

theorem semiLocalComponent_localEmbed_of_ne (w : HeightOneSpectrum (𝓞 L))
    (hw : HeightOneSpectrum.under (𝓞 K) w ≠ v) (x : GL (Fin 2) (w.adicCompletion L)) :
    semiLocalComponent K L v (localEmbed (𝓞 L) L w x) = 1 := by
  rw [← map_one (semiLocalComponent K L v)]
  refine Units.ext (Matrix.ext fun i j => ?_)
  show semiLocalEval K L v (localMat (𝓞 L) L w (x : Matrix _ _ _) i j) =
    semiLocalEval K L v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)
  simp only [semiLocalEval, RingHom.coe_comp, Function.comp_apply]
  congr 1
  funext w''
  simp only [RingHom.pi_apply, finAdeleEval_apply]
  have hne : w''.1 ≠ w := fun h => hw (by rw [← h]; exact w''.2)
  rw [localMat_apply_of_ne (𝓞 L) L w _ i j hne, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

variable {K L v}

theorem mul_mem_localIntegralSet {w : HeightOneSpectrum (𝓞 L)} {g h : GL (Fin 2) (w.adicCompletion L)}
    (hg : g ∈ localIntegralSet L w) (hh : h ∈ localIntegralSet L w) : g * h ∈ localIntegralSet L w := by
  rw [mem_localIntegralSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hh.2 i k) (hg.2 k j)

theorem inv_mem_localIntegralSet {w : HeightOneSpectrum (𝓞 L)} {g : GL (Fin 2) (w.adicCompletion L)}
    (hg : g ∈ localIntegralSet L w) : g⁻¹ ∈ localIntegralSet L w := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mul_mem_localIntegralSet_iff_left {w : HeightOneSpectrum (𝓞 L)} {g h : GL (Fin 2) (w.adicCompletion L)}
    (hg : g ∈ localIntegralSet L w) : g * h ∈ localIntegralSet L w ↔ h ∈ localIntegralSet L w := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet hg hh⟩
  have := mul_mem_localIntegralSet (inv_mem_localIntegralSet hg) hgh
  rwa [inv_mul_cancel_left] at this

theorem one_mem_localIntegralSet' (w : HeightOneSpectrum (𝓞 L)) : (1 : GL (Fin 2) (w.adicCompletion L)) ∈ localIntegralSet L w := by
  rw [mem_localIntegralSet, inv_one, Units.val_one]
  have h : ∀ i j : Fin 2, (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  exact ⟨h, h⟩

theorem semiLocalComponent_localEmbed_mem {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
(_hwv : HeightOneSpectrum.under (𝓞 K) w = v) {u : GL (Fin 2) (w.adicCompletion L)} (hu : u ∈ localIntegralSet L w) :
    semiLocalComponent K L v (localEmbed (𝓞 L) L w u) ∈ semiLocalIntegralSet K L v := by
  rw [semiLocalComponent_mem_iff]
  intro w'
  by_cases hw : w'.1 = w
  · rw [hw, finComponent_localEmbed_self]
    exact hu
  · rw [finComponent_localEmbed_of_ne (𝓞 L) L w u hw]
    exact one_mem_localIntegralSet' _

theorem mul_mem_semiLocalIntegralSet_iff_left {v : HeightOneSpectrum (𝓞 K)} {g h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hg : semiLocalComponent K L v g ∈ semiLocalIntegralSet K L v) :
    semiLocalComponent K L v (g * h) ∈ semiLocalIntegralSet K L v ↔
      semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v := by
  rw [semiLocalComponent_mem_iff] at hg
  rw [semiLocalComponent_mem_iff, semiLocalComponent_mem_iff]
  refine forall_congr' fun w => ?_
  rw [map_mul]
  exact mul_mem_localIntegralSet_iff_left (hg w)

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
  (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
  (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

def phi0 : AdelicGL2 (𝓞 L) L → ℂ := fun g =>
  {g : AdelicGL2 (𝓞 L) L | ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v}.indicator
    (fun g => φa (glArch (𝓞 L) L g) * ∏ v ∈ S, φS v (semiLocalComponent K L v (glFin (𝓞 L) L g))) g

variable {S φa φS}

theorem phi0_emb_mul {w : HeightOneSpectrum (𝓞 L)} (hw : HeightOneSpectrum.under (𝓞 K) w ∉ S)
    {u : GL (Fin 2) (w.adicCompletion L)} (hu : u ∈ localIntegralSet L w) (g : AdelicGL2 (𝓞 L) L) :
    phi0 S φa φS (emb L w u * g) = phi0 S φa φS g := by
  set v₀ := HeightOneSpectrum.under (𝓞 K) w with hv₀
  have hglA : glArch (𝓞 L) L (emb L w u * g) = glArch (𝓞 L) L g := by
    rw [map_mul, glArch_emb, one_mul]
  have hglF : glFin (𝓞 L) L (emb L w u * g) = localEmbed (𝓞 L) L w u * glFin (𝓞 L) L g := by
    rw [map_mul, glFin_emb]
  have hother : ∀ v, v ≠ v₀ → semiLocalComponent K L v (localEmbed (𝓞 L) L w u * glFin (𝓞 L) L g) =
      semiLocalComponent K L v (glFin (𝓞 L) L g) := by
    intro v hv
    rw [map_mul, semiLocalComponent_localEmbed_of_ne K L v w (fun h => hv (h ▸ hv₀)), one_mul]
  have hself : semiLocalComponent K L v₀ (localEmbed (𝓞 L) L w u * glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v₀ ↔
      semiLocalComponent K L v₀ (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v₀ :=
    mul_mem_semiLocalIntegralSet_iff_left (semiLocalComponent_localEmbed_mem hv₀.symm hu)
  have hcond : (∀ v ∉ S, semiLocalComponent K L v (localEmbed (𝓞 L) L w u * glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v) ↔
      ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v := by
    refine forall₂_congr fun v _ => ?_
    by_cases hv : v = v₀
    · subst hv; exact hself
    · rw [hother v hv]
  have hprod : ∏ v ∈ S, φS v (semiLocalComponent K L v (localEmbed (𝓞 L) L w u * glFin (𝓞 L) L g)) =
      ∏ v ∈ S, φS v (semiLocalComponent K L v (glFin (𝓞 L) L g)) :=
    Finset.prod_congr rfl fun v hv => by rw [hother v (fun h => hw (h ▸ hv))]
  simp only [phi0]
  by_cases hc : ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v
  · have hc' : ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L (emb L w u * g)) ∈ semiLocalIntegralSet K L v := by
      rw [hglF]; exact hcond.mpr hc
    rw [Set.indicator_of_mem (show emb L w u * g ∈ {g : AdelicGL2 (𝓞 L) L | ∀ v ∉ S,
        semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v} from hc'),
      Set.indicator_of_mem (show g ∈ {g : AdelicGL2 (𝓞 L) L | ∀ v ∉ S,
        semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v} from hc)]
    show φa (glArch (𝓞 L) L (emb L w u * g)) * ∏ v ∈ S, φS v (semiLocalComponent K L v (glFin (𝓞 L) L (emb L w u * g))) =
      φa (glArch (𝓞 L) L g) * ∏ v ∈ S, φS v (semiLocalComponent K L v (glFin (𝓞 L) L g))
    rw [hglA, hglF, hprod]
  · have hc' : ¬ ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L (emb L w u * g)) ∈ semiLocalIntegralSet K L v := by
      rw [hglF]; exact fun h => hc (hcond.mp h)
    rw [Set.indicator_of_notMem (show emb L w u * g ∉ {g : AdelicGL2 (𝓞 L) L | ∀ v ∉ S,
        semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v} from hc'),
      Set.indicator_of_notMem (show g ∉ {g : AdelicGL2 (𝓞 L) L | ∀ v ∉ S,
        semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v} from hc)]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem diagOne_mem_localIntegralSet {w : HeightOneSpectrum (𝓞 L)} {t : (w.adicCompletion L)ˣ}
    (ht : (t : w.adicCompletion L) ∈ w.adicCompletionIntegers L)
    (ht' : ((t⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈ w.adicCompletionIntegers L) :
    AdelicLevel.diagOne t ∈ localIntegralSet L w := by
  have ht'' : ((t : w.adicCompletion L))⁻¹ ∈ w.adicCompletionIntegers L := by
    rwa [← Units.val_inv_eq_inv_val]
  refine (mem_localIntegralSet L w).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [AdelicLevel.diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [ht, zero_mem, one_mem]
  · rw [← map_inv, AdelicLevel.diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [ht'', zero_mem, one_mem]

theorem det_diagOne {A : Type*} [CommRing A] (z : Aˣ) :
    Matrix.GeneralLinearGroup.det (AdelicLevel.diagOne z) = z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    show ((AdelicLevel.diagOne z : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![(z : A), 1] from rfl,
    Matrix.det_diagonal]
  simp

theorem integral_mul_chiDet_eq_zero_of_invariant (F : AdelicGL2 (𝓞 L) L → ℂ) (η : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (e : AdelicGL2 (𝓞 L) L) (hF : ∀ g, F (e * g) = F g) (he : chiDet (𝓞 L) L η e ≠ 1) :
    ∫ g, F g * chiDet (𝓞 L) L η g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  set I := ∫ g, F g * chiDet (𝓞 L) L η g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) with hI
  have h1 : ∫ g, F (e * g) * chiDet (𝓞 L) L η (e * g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = I :=
    integral_mul_left_eq_self (fun g => F g * chiDet (𝓞 L) L η g) e
  have h2 : ∫ g, F (e * g) * chiDet (𝓞 L) L η (e * g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      chiDet (𝓞 L) L η e * I := by
    rw [hI, ← integral_const_mul]
    congr 1
    funext g
    rw [hF, chiDet_mul]
    ring
  have h3 : (chiDet (𝓞 L) L η e - 1) * I = 0 := by rw [sub_mul, one_mul, ← h2, h1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) he
  · exact h

theorem exists_diagOne_of_not_isUnramifiedCharAt {η : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ} {w : HeightOneSpectrum (𝓞 L)}
    (hram : ¬ TateGlobal.IsUnramifiedCharAt η w) :
    ∃ t : (w.adicCompletion L)ˣ, (t : w.adicCompletion L) ∈ w.adicCompletionIntegers L ∧
      ((t⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈ w.adicCompletionIntegers L ∧
      chiDet (𝓞 L) L η (emb L w (AdelicLevel.diagOne t)) ≠ 1 := by
  simp only [TateGlobal.IsUnramifiedCharAt, not_forall] at hram
  obtain ⟨t, ht, ht', hne⟩ := hram
  refine ⟨t, ht, ht', ?_⟩
  rw [chiDet_emb, det_diagOne]
  exact fun h => hne (Units.val_eq_one.mp h)

theorem integral_phi0_mul_chiDet_eq_zero {w : HeightOneSpectrum (𝓞 L)} (hw : HeightOneSpectrum.under (𝓞 K) w ∉ S)
    (η : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hram : ¬ TateGlobal.IsUnramifiedCharAt η w) :
    ∫ g, phi0 S φa φS g * chiDet (𝓞 L) L η g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by
  obtain ⟨t, ht, ht', hne⟩ := exists_diagOne_of_not_isUnramifiedCharAt hram
  exact integral_mul_chiDet_eq_zero_of_invariant _ η _
    (fun g => phi0_emb_mul hw (diagOne_mem_localIntegralSet ht ht') g) hne

theorem emb_diagOne_mem_levelOne (N : Ideal (𝓞 L)) {w : HeightOneSpectrum (𝓞 L)} {t : (w.adicCompletion L)ˣ}
    (ht : (t : w.adicCompletion L) ∈ w.adicCompletionIntegers L)
    (ht' : ((t⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈ w.adicCompletionIntegers L) :
    emb L w (AdelicLevel.diagOne t) ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, glFin_emb, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff, ← map_inv]
    have key : ∀ (s : (w.adicCompletion L)ˣ), (s : w.adicCompletion L) ∈ w.adicCompletionIntegers L →
        IsLocalLevelOne (𝓞 L) L w N ((AdelicLevel.diagOne s : GL (Fin 2) (w.adicCompletion L)) : Matrix _ _ _) := by
      intro s hs
      refine ⟨fun i j => ?_, ?_, ?_⟩
      · rw [AdelicLevel.diagOne_coe_apply]
        fin_cases i <;> fin_cases j <;> simp [hs, zero_mem, one_mem]
      · rw [AdelicLevel.diagOne_coe_apply]
        simp
      · rw [AdelicLevel.diagOne_coe_apply]
        simp
    exact ⟨key t ht, key t⁻¹ ht'⟩
  · rw [mem_finiteAdelicGL2Subgroup_iff]
    exact glArch_emb w _

theorem integral_mul_chiDet_eq_zero_of_isBiInvariantUnder {N : Ideal (𝓞 L)} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (η : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) {w : HeightOneSpectrum (𝓞 L)} (hram : ¬ TateGlobal.IsUnramifiedCharAt η w) :
    ∫ g, φ g * chiDet (𝓞 L) L η g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by
  obtain ⟨t, ht, ht', hne⟩ := exists_diagOne_of_not_isUnramifiedCharAt hram
  exact integral_mul_chiDet_eq_zero_of_invariant φ η _
    (fun g => (hbi _ (emb_diagOne_mem_levelOne N ht ht') g).1) hne

end SemiLocal

section Tables

variable [DecidableEq (HeightOneSpectrum (𝓞 L))] (SL : Finset (HeightOneSpectrum (𝓞 L)))

def tab (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) : HeightOneSpectrum (𝓞 L) → ℂ × ℂ :=
  fun w => if w ∈ SL then 0
    else ((((Ideal.absNorm w.asIdeal : ℕ) : ℂ) + 1) * chiHat w χ, HeckeEigensystem.cNorm w * chiHat w χ ^ 2)

variable {SL}

theorem tab_of_not_mem (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ SL) :
    tab SL χ w = ((((Ideal.absNorm w.asIdeal : ℕ) : ℂ) + 1) * chiHat w χ, HeckeEigensystem.cNorm w * chiHat w χ ^ 2) := by
  simp only [tab, if_neg hw]

theorem tab_of_mem (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ SL) :
    tab SL χ w = 0 := by
  simp only [tab, if_pos hw]

theorem tab_monomial (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ SL) (k j : ℕ) :
    (tab SL χ w).1 ^ k * ((HeckeEigensystem.cNorm w)⁻¹ * (tab SL χ w).2) ^ j =
      ((((Ideal.absNorm w.asIdeal : ℕ) : ℂ) + 1) * chiHat w χ) ^ k * (chiHat w χ ^ 2) ^ j := by
  rw [tab_of_not_mem χ hw, ← mul_assoc, inv_mul_cancel₀ (HeckeEigensystem.cNorm_ne_zero w), one_mul]

omit [DecidableEq (HeightOneSpectrum (𝓞 L))] in

theorem xi_det_heckeGen_eq {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ}
    (hsq : SquaresToXi (𝓞 L) L ⊤ ξL χ) (w : HeightOneSpectrum (𝓞 L)) :
    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = chiHat w χ ^ 2 := by
  rw [← hsq ⟨_, Subgroup.mem_top _⟩, Units.val_pow_eq_pow_val, chiHat, uniformizerIdele_eq_idl, ← det_heckeGen]

theorem tab_mem_box {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ}
    (hsq : SquaresToXi (𝓞 L) L ⊤ ξL χ) :
    tab SL χ ∈ {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} := by
  refine ⟨fun w hw => tab_of_mem χ hw, fun w hw => ?_⟩
  rw [tab_of_not_mem χ hw, xi_det_heckeGen_eq hsq]
  set c : ℂ := chiHat w χ with hc
  have hc0 : c ≠ 0 := chiHat_ne_zero w χ
  set N : ℕ := Ideal.absNorm w.asIdeal with hN
  have hN0 : (N : ℂ) ≠ 0 := by
    rw [hN]; exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot)
  refine ⟨rfl, ?_, ?_⟩
  · simp only
    have hn : ‖((N : ℂ) + 1)‖ = (N : ℝ) + 1 := by
      rw [show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast
      ring
    rw [norm_mul, norm_pow, Real.sqrt_sq (norm_nonneg _), hn]
  · simp only
    have hnorm : (((‖HeckeEigensystem.cNorm w * c ^ 2‖ : ℝ)) : ℂ) = (N : ℂ) * (conj c * c) := by
      rw [Complex.conj_mul', HeckeEigensystem.cNorm, ← hN, norm_mul, norm_pow, Complex.norm_natCast]
      push_cast
      ring
    rw [hnorm, HeckeEigensystem.cNorm, ← hN, map_mul, map_mul, map_pow, map_add, map_one, Complex.conj_natCast]
    have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc0
    field_simp

theorem defaultTab_mem_box (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) :
    (fun w => if w ∈ SL then (0 : ℂ × ℂ) else (0, HeckeEigensystem.cNorm w *
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ∈
      {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} := by
  refine ⟨fun w hw => by simp only [if_pos hw], fun w hw => ?_⟩
  simp only [if_neg hw, norm_zero, map_zero, mul_zero, and_true, true_and]
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

omit [DecidableEq (HeightOneSpectrum (𝓞 L))] in

def nrmInv (L : Type) [Field L] [NumberField L] : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ where
  toFun x := Units.mk0 (((TateGlobal.ideleNorm L x : ℝ) : ℂ))⁻¹
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr (TateGlobal.ideleNorm_pos x).ne'))
  map_one' := Units.ext (by
    rw [Units.val_mk0, Units.val_one]
    have h := TateGlobal.ideleNorm_mul (1 : (AdeleRing (𝓞 L) L)ˣ) 1
    rw [mul_one] at h
    have h1 : TateGlobal.ideleNorm L 1 = 1 :=
      (mul_eq_left₀ (TateGlobal.ideleNorm_pos (1 : (AdeleRing (𝓞 L) L)ˣ)).ne').mp h.symm
    rw [h1, Complex.ofReal_one, inv_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, TateGlobal.ideleNorm_mul, Complex.ofReal_mul,
      mul_inv])

omit [DecidableEq (HeightOneSpectrum (𝓞 L))] in
theorem nrmInv_apply (x : (AdeleRing (𝓞 L) L)ˣ) :
    ((nrmInv L x : ℂˣ) : ℂ) = (((TateGlobal.ideleNorm L x : ℝ) : ℂ))⁻¹ := rfl

omit [DecidableEq (HeightOneSpectrum (𝓞 L))] in
theorem continuous_nrmInv : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((nrmInv L z : ℂˣ) : ℂ) := by
  simp_rw [nrmInv_apply]
  exact (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm L)).inv₀
    fun z => Complex.ofReal_ne_zero.mpr (TateGlobal.ideleNorm_pos z).ne'

omit [DecidableEq (HeightOneSpectrum (𝓞 L))] in

theorem nrmInv_principal (u : Lˣ) :
    nrmInv L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) = 1 := by
  apply Units.ext
  rw [nrmInv_apply, Units.val_one]
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L (AdelicLevel.diagOne u)) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u := by
    rw [show globalPoints (𝓞 L) L (AdelicLevel.diagOne u) =
      Matrix.GeneralLinearGroup.map (algebraMap L (AdeleRing (𝓞 L) L)) (AdelicLevel.diagOne u) from rfl,
      Matrix.GeneralLinearGroup.map_det, det_diagOne]
  rw [← hdet, AutomorphicForm.ideleNorm_det_globalPoints, Complex.ofReal_one, inv_one]

omit [DecidableEq (HeightOneSpectrum (𝓞 L))] in
theorem nrmInv_uniformizerIdele (w : HeightOneSpectrum (𝓞 L)) :
    ((nrmInv L (uniformizerIdele L w) : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) := by
  rw [nrmInv_apply, NumberField.TateGlobal.ideleNorm_uniformizerIdele]
  push_cast
  rw [inv_inv]

theorem tab_eq_eisensteinTableOf (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (M : Ideal (𝓞 L)) (hM : M ≠ ⊥)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ SL) :
    tab SL χ w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM (χ * nrmInv L) χ).a w,
      (LanglandsTunnell.Converse.eisensteinTableOf L M hM (χ * nrmInv L) χ).b w) := by
  rw [tab_of_not_mem χ hw]
  simp only [LanglandsTunnell.Converse.eisensteinTableOf, MonoidHom.mul_apply, Units.val_mul, nrmInv_uniformizerIdele,
    HeckeEigensystem.cNorm, chiHat]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

end Tables

section Genuine

def uAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)

omit [NumberField K] in
theorem coe_uAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((uAct D σ z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) z := rfl

omit [NumberField K] in
theorem continuous_uAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) : Continuous (uAct D σ) :=
  Continuous.units_map _ (D.continuous_act σ)

omit [NumberField K] in
theorem uAct_principal (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (u : Lˣ) :
    uAct D σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (σ : L →* L) u) := by
  apply Units.ext
  rw [coe_uAct]
  exact D.compat σ u

omit [NumberField K] in
theorem det_sigmaAdelicAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L D σ g) = uAct D σ (Matrix.GeneralLinearGroup.det g) :=
  Matrix.GeneralLinearGroup.map_det _ _

abbrev Dg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L :=
  M4aHerbrand.GenuineDescent.genuineDescentDatum K L

theorem uAct_idl (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w') (t : (w.adicCompletion L)ˣ) :
    uAct (Dg K L) σ (idl L w t) = idl L w' (NumberField.PlaceTransport.transportUnits σ h t) := by
  refine Units.ext (Prod.ext (funext fun u' => ?_) ?_)
  · have hu : σ • (σ⁻¹ • u') = u' := smul_inv_smul σ u'
    rw [coe_uAct, M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ hu, idl_fst, idl_fst]
    exact map_one _
  · refine FiniteAdeleRing.ext L fun v' => ?_
    by_cases hv : v' = w'
    · subst hv
      rw [coe_uAct, M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ h, idl_snd_self, idl_snd_self]
      rfl
    · have hv' : σ • (σ⁻¹ • v') = v' := smul_inv_smul σ v'
      have hne : σ⁻¹ • v' ≠ w := by
        intro he; apply hv; rw [← hv', he, h]
      rw [coe_uAct, M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ hv', idl_snd_of_ne w _ hne,
        idl_snd_of_ne w' _ hv]
      exact map_one _

theorem chiHat_smul (σ : L ≃ₐ[K] L) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hχσ : ∀ z, χ (uAct (Dg K L) σ z) = χ z) (w : HeightOneSpectrum (𝓞 L))
    (hunr : TateGlobal.IsUnramifiedCharAt χ (σ • w)) : chiHat (σ • w) χ = chiHat w χ := by
  set t₁ : ((σ • w).adicCompletion L)ˣ := NumberField.PlaceTransport.transportUnits σ rfl (uniformizerUnit L w) with ht₁
  set t₂ : ((σ • w).adicCompletion L)ˣ := uniformizerUnit L (σ • w) with ht₂
  have h1 : chiHat w χ = ((χ (idl L (σ • w) t₁) : ℂˣ) : ℂ) := by
    rw [chiHat, uniformizerIdele_eq_idl, ← hχσ, uAct_idl σ rfl]
  have h2 : chiHat (σ • w) χ = ((χ (idl L (σ • w) t₂) : ℂˣ) : ℂ) := by
    rw [chiHat, uniformizerIdele_eq_idl]

  have hv1 : Valued.v (t₁ : (σ • w).adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    show Valued.v (NumberField.PlaceTransport.transport σ rfl (uniformizerUnit L w : w.adicCompletion L)) = _
    rw [NumberField.PlaceTransport.valued_transport, valued_uniformizerUnit]
  have hv2 : Valued.v (t₂ : (σ • w).adicCompletion L) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit L (σ • w)
  set s : ((σ • w).adicCompletion L)ˣ := t₁ * t₂⁻¹ with hs
  have hvs : Valued.v (s : (σ • w).adicCompletion L) = 1 := by
    rw [hs, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv1, hv2,
      mul_inv_cancel₀ (WithZero.exp_ne_zero)]
  have hsi : (s : (σ • w).adicCompletion L) ∈ (σ • w).adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvs]
  have hsi' : ((s⁻¹ : ((σ • w).adicCompletion L)ˣ) : (σ • w).adicCompletion L) ∈ (σ • w).adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hvs, inv_one]
  have hloc : TateGlobal.localChar χ (σ • w) s = 1 := hunr s hsi hsi'
  rw [localChar_eq_idl] at hloc
  have hidl : idl L (σ • w) t₁ = idl L (σ • w) s * idl L (σ • w) t₂ := by
    rw [← idlHom_apply, ← idlHom_apply, ← idlHom_apply, ← map_mul, hs, inv_mul_cancel_right]
  rw [h1, h2, hidl, map_mul, hloc, one_mul]

omit [NumberField K] [NumberField L] in

theorem under_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum.under (𝓞 K) (σ • w) = HeightOneSpectrum.under (𝓞 K) w := by
  refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • algebraMap (𝓞 K) (𝓞 L) a = algebraMap (𝓞 K) (𝓞 L) a := by
    refine RingOfIntegers.ext ?_
    show σ⁻¹ (algebraMap K L (a : K)) = algebraMap K L (a : K)
    exact (σ⁻¹).commutes _
  rw [this]

omit [NumberField K] in

theorem absNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (σ • w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal _
    (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ) rfl).toEquiv).symm

omit [NumberField K] [NumberField L] in

theorem smul_asIdeal_eq_pointwise (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal = σ • w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.pointwise_smul_def]
  rfl

theorem exists_smul_eq [IsGalois K L] (w w' : HeightOneSpectrum (𝓞 L))
    (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') : ∃ τ : L ≃ₐ[K] L, τ • w = w' := by
  haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w).asIdeal := ⟨rfl⟩
  haveI : w'.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w).asIdeal := ⟨by rw [h]; rfl⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal w'.asIdeal
    (L ≃ₐ[K] L)
  exact ⟨τ, HeightOneSpectrum.ext (by rw [smul_asIdeal_eq_pointwise]; exact hτ)⟩

theorem fibre_constant [IsGalois K L] {X : Type*} (F : HeightOneSpectrum (𝓞 L) → X)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hstep : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → F (σ • w) = F w)
    (w w' : HeightOneSpectrum (𝓞 L)) (hw : w ∉ SL)
    (hww' : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') : F w = F w' := by
  let H : Subgroup (L ≃ₐ[K] L) :=
    { carrier := {τ | ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → F (τ • w) = F w}
      one_mem' := fun w _ => by rw [one_smul]
      mul_mem' := fun {τ τ'} hτ hτ' w hw => by
        have hw' : τ' • w ∉ SL := fun h => hw ((hSsat _ _ (under_smul τ' w)).mp h)
        rw [mul_smul, hτ _ hw', hτ' _ hw]
      inv_mem' := fun {τ} hτ w hw => by
        have hw' : τ⁻¹ • w ∉ SL := fun h => hw ((hSsat _ _ (under_smul τ⁻¹ w)).mp h)
        have := hτ _ hw'
        rw [smul_inv_smul] at this
        exact this.symm }
  have hσ : σ ∈ H := fun w hw => hstep w hw
  have hall : ∀ τ : L ≃ₐ[K] L, τ ∈ H := fun τ => (Subgroup.zpowers_le.mpr hσ) (hgen τ)
  obtain ⟨τ, rfl⟩ := exists_smul_eq w w' hww'
  exact (hall τ w hw).symm

end Genuine

section Analytic

theorem det_unipotentGL2 {R : Type*} [CommRing R] (x : R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of, Units.val_one]
  ring

theorem chiDet_unipotentGL2_mul (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (x : AdeleRing (𝓞 L) L) (g : AdelicGL2 (𝓞 L) L) :
    chiDet (𝓞 L) L χ (unipotentGL2 x * g) = chiDet (𝓞 L) L χ g := by
  rw [chiDet_mul, chiDet, det_unipotentGL2, map_one, Units.val_one, one_mul]

theorem lambdaT_eq_ite {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G] (μ : Measure Q) [IsProbabilityMeasure μ]
    (u : Q → G) (H : G → ℝ) (T : ℝ) (φ : G → ℂ) (hφ : ∀ q g, φ (u q * g) = φ g) (g : G) :
    lambdaT μ u H T φ g = if H g ≤ T then φ g else 0 := by
  have hct : constantTerm μ u φ g = φ g := by
    simp [constantTerm, constantTermIntegrand, hφ]
  by_cases hg : H g ≤ T
  · rw [if_pos hg, lambdaT_apply_of_le _ _ hg]
  · rw [if_neg hg, lambdaT_apply_of_lt _ _ (lt_of_not_ge hg), hct, sub_self]

theorem lambdaT_kernel_eq {mQ : MeasurableSpace (AdeleRing (𝓞 L) L)} (ν : Measure (AdeleRing (𝓞 L) L))
    [IsProbabilityMeasure ν] (H : AdelicGL2 (𝓞 L) L → ℝ) (T : ℝ) (c : ℂ)
    (A : Set ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ)) (G : ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) → AdelicGL2 (𝓞 L) L → ℂ)
    (x : AdelicGL2 (𝓞 L) L) :
    lambdaT ν (fun t => unipotentGL2 t) H T
        (fun y => c * ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ A), G χ x * chiDet (𝓞 L) L χ⁻¹ y) x =
      if H x ≤ T then c * ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ A), G χ x * chiDet (𝓞 L) L χ⁻¹ x else 0 := by
  rw [lambdaT_eq_ite]
  intro q y
  simp_rw [chiDet_unipotentGL2_mul]

attribute [local instance] NumberField.AdelicHaar.glBorel

omit [NumberField K] in

theorem twistedConvOp_chiDet (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (x : AdelicGL2 (𝓞 L) L) :
    twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x =
      chiDet (𝓞 L) L (χ.comp (uAct D σ)) x *
        ∫ z, φ z * chiDet (𝓞 L) L (χ.comp (uAct D σ)) z ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  rw [twistedConvOp_apply, rightConv_apply]
  show ∫ y, chiDet (𝓞 L) L χ (sigmaAdelicAct K L D σ (x * y)) * φ y ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = _
  have hcomp : ∀ g, chiDet (𝓞 L) L χ (sigmaAdelicAct K L D σ g) = chiDet (𝓞 L) L (χ.comp (uAct D σ)) g := by
    intro g
    rw [chiDet_apply, chiDet_apply, det_sigmaAdelicAct]
    rfl
  have h : ∀ y, chiDet (𝓞 L) L χ (sigmaAdelicAct K L D σ (x * y)) * φ y =
      chiDet (𝓞 L) L (χ.comp (uAct D σ)) x * (φ y * chiDet (𝓞 L) L (χ.comp (uAct D σ)) y) := by
    intro y
    rw [hcomp, chiDet_mul]
    ring
  simp_rw [h]
  exact integral_const_mul _ _

theorem integrableOn_and_tendsto_setIntegral_ite_of_integrableOn {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (Φ : Set G) (H : G → ℝ) (hH : Measurable H) (F : G → ℂ) (hF : IntegrableOn F Φ μ) :
    (∀ R : ℝ, IntegrableOn (fun x => if H x ≤ Real.exp R then F x else 0) Φ μ) ∧
    Filter.Tendsto (fun R : ℝ => ∫ x in Φ, (if H x ≤ Real.exp R then F x else 0) ∂μ) Filter.atTop
      (nhds (∫ x in Φ, F x ∂μ)) := by
  set s : ℝ → Set G := fun R => {x | H x ≤ Real.exp R} with hs
  have hsm : ∀ R, MeasurableSet (s R) := fun R => hH measurableSet_Iic
  have hfun : ∀ R, (fun x => if H x ≤ Real.exp R then F x else 0) = (s R).indicator F := by
    intro R
    funext x
    simp only [hs, Set.indicator_apply, Set.mem_setOf_eq]
  refine ⟨fun R => ?_, ?_⟩
  · rw [hfun R]
    exact hF.indicator (hsm R)
  · have hint : ∀ R, ∫ x in Φ, (if H x ≤ Real.exp R then F x else 0) ∂μ = ∫ x in s R, F x ∂(μ.restrict Φ) := by
      intro R
      rw [hfun R, integral_indicator (hsm R)]
    simp_rw [hint]
    have hmono : Monotone s := by
      intro R R' hRR' x hx
      exact le_trans (show H x ≤ Real.exp R from hx) (Real.exp_le_exp.mpr hRR')
    have hU : (⋃ R, s R) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, hs, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨H x, by linarith [Real.add_one_le_exp (H x)]⟩
    have hfi : IntegrableOn F (⋃ R, s R) (μ.restrict Φ) := by
      rw [hU]
      exact hF.integrableOn
    have h := tendsto_setIntegral_of_monotone (μ := μ.restrict Φ) hsm hmono hfi
    rwa [hU, Measure.restrict_univ] at h

end Analytic

end R4ResSigma

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm AdelicDock
open scoped ComplexConjugate TensorProduct TensorProduct.RightActions NumberField.PlaceTransport Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option maxHeartbeats 6400000 in
open R4ResSigma in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
      ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₂ z = 1) ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
            (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
        (∀ R : ℝ, IntegrableOn (fun x =>
            (@AutomorphicForm.lambdaT _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                    (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                        SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                            χ z = 1) ∧
                        Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
              x))
            Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
        Summable (fun n : ℕ => cs n * g ⟨tabs n, htabs n⟩) ∧
        Filter.Tendsto (fun R : ℝ =>
          ∫ x in Φ₀,
            (@AutomorphicForm.lambdaT _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                    (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                        SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                            χ z = 1) ∧
                        Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
              x)
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
          Filter.atTop (nhds (∑' n, cs n * g ⟨tabs n, htabs n⟩)) := by
  classical
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  letI mA : MeasurableSpace (AdeleRing (𝓞 L) L) := adeleBorel (𝓞 L) L

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = Dg K L := Subsingleton.elim _ _

  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set A : Set ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) := {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
      SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range → χ z = 1) ∧
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)} with hA
  set bC : ℂ := ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) with hbC
  set VC : ℂ := ((μ Φ₀).toReal : ℂ) with hVC
  have hκ : ∃ κ : ℂ, κ = bC / VC * VC := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ := hκ

  set tw : ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) := fun χ => χ.comp (uAct (Dg K L) σ) with htw
  have htw_apply : ∀ χ z, tw χ z = χ (uAct (Dg K L) σ z) := fun χ z => rfl
  have htw_cont : ∀ χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ, (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)) →
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((tw χ z : ℂˣ) : ℂ) :=
    fun χ hχ => hχ.comp (continuous_uAct (Dg K L) σ)

  set I0 : ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) → ℂ := fun η => ∫ g, phi0 S φa φS g * chiDet (𝓞 L) L η g ∂μ with hI0
  have hA₀ : ∃ A₀ : Set ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ), A₀ = {χ | χ ∈ A ∧ I0 (tw χ) ≠ 0} := ⟨_, rfl⟩
  obtain ⟨A₀, hA₀⟩ := hA₀

  have hVfin : μ Φ₀ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain L α β
      hα hαβ Φ₀ hΦ₀
    rwa [Set.inter_eq_left.mpr hΦ₀s] at h
  have hHm : Measurable (NumberField.AdelicHeight.adelicHeight L) :=
    (NumberField.AdelicHeight.continuous_adelicHeight L).measurable
  haveI hν : IsProbabilityMeasure ((productionPinsOf L ΦL
      (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν) :=
    isProbabilityMeasure_productionPinsOf_ν L _ _ _ _ (adelicAddHaar_adelicBox_pos L).ne'
      (adelicAddHaar_adelicBox_lt_top L).ne

  obtain ⟨x₀, hx₀X⟩ : ∃ x₀ : HeightOneSpectrum (𝓞 L) → ℂ × ℂ, x₀ ∈ X := ⟨_, hX (defaultTab_mem_box ξL)⟩
  have htabX : ∀ χ ∈ A, tab SL χ ∈ X := fun χ hχ => hX (tab_mem_box hχ.1)

  set P : ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) → Prop := fun χ => tw χ = χ ∧ ∀ w, TateGlobal.IsUnramifiedCharAt χ w with hP

  have hfc : ∀ χ, P χ → ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tab SL χ w = tab SL χ w' := by
    intro χ hPχ w w' hw hww'
    refine fibre_constant (K := K) (tab SL χ) SL hSL σ hgen (fun w₁ hw₁ => ?_) w w' hw hww'
    have hw₁' : σ • w₁ ∉ SL := fun h => hw₁ ((hSL _ _ (under_smul σ w₁)).mp h)
    have hχσ : ∀ z, χ (uAct (Dg K L) σ z) = χ z := fun z => by rw [← htw_apply, hPχ.1]
    rw [tab_of_not_mem χ hw₁, tab_of_not_mem χ hw₁', chiHat_smul σ χ hχσ w₁ (hPχ.2 _), absNorm_smul,
      HeckeEigensystem.cNorm, HeckeEigensystem.cNorm, absNorm_smul]

  set Aval : Finset (HeightOneSpectrum (𝓞 K)) → (∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)) →
      (HeightOneSpectrum (𝓞 K) → ℕ) → (HeightOneSpectrum (𝓞 K) → ℕ) → ℂ :=
    fun T ws ks js => if hfin : A₀.Finite then
      κ * ∑ χ ∈ hfin.toFinset.filter P, (∏ v ∈ T,
        ((((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℂ) + 1) * chiHat (ws v).1 χ) ^ ks v * (chiHat (ws v).1 χ ^ 2) ^ js v) * I0 χ
      else 0 with hAval

  obtain ⟨tabs, htabs, cs, hsum, hatoms, hfinsupp, hlim⟩ :
      ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
      (Summable fun n => ‖cs n‖) ∧
      (∀ n, cs n ≠ 0 →
        (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
        ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₂ z = 1) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
              (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∧
      (∃ s : Finset ℕ, ∀ m ∉ s, cs m = 0) ∧
      ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
        (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
        ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)) (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) → ∀ ks js : HeightOneSpectrum (𝓞 K) → ℕ,
        ∑' n, cs n * (∏ v ∈ T, (tabs n (w' v)).1 ^ ks v * ((HeckeEigensystem.cNorm (w' v))⁻¹ * (tabs n (w' v)).2) ^ js v) =
          Aval T ws ks js := by
    by_cases hfin : A₀.Finite
    · set sχ := hfin.toFinset with hsχ
      set s₁ := sχ.filter P with hs₁
      set m : ℕ := s₁.card with hm
      set e := s₁.equivFin with he
      have hmem : ∀ y : s₁, ((y : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)) ∈ A ∧ P (y : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) := by
        intro y
        have h := Finset.mem_filter.mp y.2
        have h' := hfin.mem_toFinset.mp h.1
        rw [hA₀] at h'
        exact ⟨h'.1, h.2⟩
      refine ⟨fun n => if h : n < m then tab SL ((e.symm ⟨n, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) else x₀,
        fun n => ?_, fun n => if h : n < m then κ * I0 ((e.symm ⟨n, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) else 0,
        ?_, fun n hn => ?_, ⟨Finset.range m, fun k hk => ?_⟩, fun T hTSL ws w' hw' ks js => ?_⟩
      · by_cases h : n < m
        · simp only [dif_pos h]
          exact htabX _ (hmem _).1
        · simp only [dif_neg h]
          exact hx₀X
      · refine summable_of_ne_finset_zero (s := Finset.range m) fun n hn => ?_
        rw [Finset.mem_range] at hn
        simp only [dif_neg hn, norm_zero]
      · by_cases h : n < m
        swap
        · simp only [dif_neg h] at hn
          exact absurd rfl hn
        set χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ((e.symm ⟨n, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) with hχdef
        obtain ⟨⟨hsq, htriv, hcont⟩, hPχ⟩ := hmem (e.symm ⟨n, h⟩)
        refine ⟨fun w w' hw _ hww' => ?_, ⊤, top_ne_bot, χ * nrmInv L, χ, ?_, ?_, hcont, htriv, fun w hw => ?_⟩
        · simp only [dif_pos h]
          exact hfc χ hPχ w w' hw hww'
        · have : (fun z : (AdeleRing (𝓞 L) L)ˣ => (((χ * nrmInv L) z : ℂˣ) : ℂ)) =
              fun z => ((χ z : ℂˣ) : ℂ) * ((nrmInv L z : ℂˣ) : ℂ) := by
            funext z; rw [MonoidHom.mul_apply, Units.val_mul]
          rw [this]
          exact hcont.mul continuous_nrmInv
        · rintro z ⟨u', rfl⟩
          rw [MonoidHom.mul_apply, htriv _ ⟨u', rfl⟩, nrmInv_principal, one_mul]
        · simp only [dif_pos h]
          exact tab_eq_eisensteinTableOf χ ⊤ top_ne_bot hw
      · rw [Finset.mem_range] at hk
        simp only [dif_neg hk]
      ·
        simp only [hAval, dif_pos hfin]
        have hcs : ∀ b ∉ Finset.range m, (fun n => (if h : n < m then
            κ * I0 ((e.symm ⟨n, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) else 0) *
              (∏ v ∈ T, ((if h : n < m then tab SL ((e.symm ⟨n, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) else x₀) (w' v)).1 ^ ks v *
                ((HeckeEigensystem.cNorm (w' v))⁻¹ *
                  ((if h : n < m then tab SL ((e.symm ⟨n, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) else x₀) (w' v)).2) ^ js v))
            b = 0 := by
          intro b hb
          rw [Finset.mem_range] at hb
          simp only [dif_neg hb, zero_mul]
        rw [tsum_eq_sum hcs, ← Fin.sum_univ_eq_sum_range]

        have hmono : ∀ χ, P χ → χ ∈ A →
            (∏ v ∈ T, (tab SL χ (w' v)).1 ^ ks v * ((HeckeEigensystem.cNorm (w' v))⁻¹ * (tab SL χ (w' v)).2) ^ js v) =
            ∏ v ∈ T, ((((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℂ) + 1) * chiHat (ws v).1 χ) ^ ks v *
              (chiHat (ws v).1 χ ^ 2) ^ js v := by
          intro χ hPχ _
          refine Finset.prod_congr rfl fun v hv => ?_

          have hw'v : w' v = σ⁻¹ • (ws v).1 := by
            refine HeightOneSpectrum.ext ?_
            rw [hw' v hv, smul_asIdeal_eq_pointwise, AlgEquiv.aut_inv]
          have hunder : HeightOneSpectrum.under (𝓞 K) (w' v) = HeightOneSpectrum.under (𝓞 K) (ws v).1 := by
            rw [hw'v, under_smul]
          have hw'S : w' v ∉ SL := hTSL v hv _ (by rw [hunder]; exact (ws v).2)
          have hwsS : (ws v).1 ∉ SL := hTSL v hv _ (ws v).2
          have htab : tab SL χ (w' v) = tab SL χ (ws v).1 := hfc χ hPχ _ _ hw'S hunder
          have hN : HeckeEigensystem.cNorm (w' v) = HeckeEigensystem.cNorm (ws v).1 := by
            rw [HeckeEigensystem.cNorm, HeckeEigensystem.cNorm, hw'v, absNorm_smul]
          rw [htab, hN, tab_monomial χ hwsS]
        have h1 : ∀ i : Fin m, (if h : (i : ℕ) < m then
            κ * I0 ((e.symm ⟨i, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) else 0) *
              (∏ v ∈ T, ((if h : (i : ℕ) < m then tab SL ((e.symm ⟨i, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) else x₀) (w' v)).1 ^ ks v *
                ((HeckeEigensystem.cNorm (w' v))⁻¹ *
                  ((if h : (i : ℕ) < m then tab SL ((e.symm ⟨i, h⟩ : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) else x₀) (w' v)).2) ^ js v) =
            κ * ((∏ v ∈ T, ((((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℂ) + 1) * chiHat (ws v).1 ((e.symm i : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)) ^ ks v *
              (chiHat (ws v).1 ((e.symm i : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) ^ 2) ^ js v) *
              I0 ((e.symm i : s₁) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)) := by
          intro i
          simp only [dif_pos i.2, Fin.eta]
          rw [hmono _ (hmem _).2 (hmem _).1]
          ring
        simp_rw [h1]
        rw [← Finset.mul_sum]
        congr 1
        rw [Equiv.sum_comp e.symm (fun y : s₁ => (∏ v ∈ T, ((((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℂ) + 1) *
            chiHat (ws v).1 (y : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)) ^ ks v * (chiHat (ws v).1 (y : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) ^ 2) ^ js v) *
            I0 (y : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)),
          Finset.sum_coe_sort s₁ (fun χ => (∏ v ∈ T, ((((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℂ) + 1) *
            chiHat (ws v).1 χ) ^ ks v * (chiHat (ws v).1 χ ^ 2) ^ js v) * I0 χ)]
    · refine ⟨fun _ => x₀, fun _ => hx₀X, fun _ => 0, ?_, fun n hn => absurd rfl hn, ⟨∅, fun _ _ => rfl⟩,
        fun T hTSL ws w' hw' ks js => ?_⟩
      · simp only [norm_zero]
        exact summable_zero
      · simp only [zero_mul, tsum_zero, hAval, dif_neg hfin]
  refine ⟨tabs, htabs, cs, hsum, hatoms, ?_⟩
  intro T hTd hT2 hTSL ws w' hw' ϖs hirr hϖs0 ns rTs hcos zs hzs ks js φ hφ hφc φf hfact hbi harch g hg

  set monoW : ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) → ℂ := fun η => ∏ v ∈ T,
      ((((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℂ) + 1) * chiHat (ws v).1 η) ^ ks v * (chiHat (ws v).1 η ^ 2) ^ js v with hmonoW
  have hmonoW_ne : ∀ η, monoW η ≠ 0 := by
    intro η
    refine Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ (chiHat_ne_zero _ η)))
      (pow_ne_zero _ (pow_ne_zero _ (chiHat_ne_zero _ η)))
    exact Nat.cast_add_one_ne_zero _
  have hI0_eq : ∀ η, I0 η = ∫ g, {g : AdelicGL2 (𝓞 L) L |
        ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v}.indicator
      (fun g => φa (glArch (𝓞 L) L g) * ∏ v ∈ S, φS v (semiLocalComponent K L v (glFin (𝓞 L) L g))) g *
        chiDet (𝓞 L) L η g ∂μ := fun η => rfl

  have hI0_unr : ∀ η, I0 η ≠ 0 → ∀ w, HeightOneSpectrum.under (𝓞 K) w ∉ S → TateGlobal.IsUnramifiedCharAt η w :=
    fun η hη w hw => by_contra fun hram => hη (integral_phi0_mul_chiDet_eq_zero hw η hram)
  have hT_notS : ∀ v ∈ T, HeightOneSpectrum.under (𝓞 K) (ws v).1 ∉ S := by
    intro v hv
    rw [(ws v).2]
    exact fun hvS => Finset.disjoint_left.mp hTd hv hvS
  have hW : ∀ η : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ, (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((η z : ℂˣ) : ℂ)) →
      ∫ x, φ x * chiDet (𝓞 L) L η x ∂μ = monoW η * I0 η := by
    intro η hη
    have hraw := AutomorphicForm.integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization K L S T
      hTd ws ns rTs zs ks js φa φS φ hφ hφc φf hfact η hη
    rw [hraw, ← hI0_eq]
    by_cases hunr : ∀ v ∈ T, TateGlobal.IsUnramifiedCharAt η (ws v).1
    · congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      exact NumberField.TateGlobal.sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt L (ws v).1 η
        (hunr v hv) (ϖs v) (hirr v hv) (hϖs0 v hv) (ns v) (rTs v) (hcos v hv) (zs v) (hzs v hv) (ks v) (js v)
    · push Not at hunr
      obtain ⟨v, hv, hram⟩ := hunr
      have h0 : I0 η = 0 := by_contra fun h => hram (hI0_unr η h _ (hT_notS v hv))
      rw [h0, mul_zero, mul_zero]

  set ψ : ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) → AdelicGL2 (𝓞 L) L → ℂ :=
    fun χ x => chiDet (𝓞 L) L (tw χ) x * chiDet (𝓞 L) L χ⁻¹ x with hψ
  have hψ_ne : ∀ χ x, ψ χ x ≠ 0 := fun χ x => mul_ne_zero (chiDet_ne_zero _ _) (chiDet_ne_zero _ _)
  have hGψ : ∀ χ ∈ A, ∀ x, twistedConvOp K L (Dg K L) σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ x =
      (monoW (tw χ) * I0 (tw χ)) * ψ χ x := by
    intro χ hχ x
    simp only [hψ]
    rw [twistedConvOp_chiDet, hW _ (htw_cont χ hχ.2.2)]
    ring
  have hLam : ∀ (R : ℝ) (x : AdelicGL2 (𝓞 L) L),
      @AutomorphicForm.lambdaT _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
        (fun y => bC / VC *
          ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ A),
            twistedConvOp K L (Dg K L) σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
        x = if NumberField.AdelicHeight.adelicHeight L x ≤ Real.exp R then
          bC / VC * ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ A), (monoW (tw χ) * I0 (tw χ)) * ψ χ x else 0 := by
    intro R x
    rw [lambdaT_kernel_eq _ (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) (bC / VC) A
      (fun χ x => twistedConvOp K L (Dg K L) σ φ (chiDet (𝓞 L) L χ) x) x]
    simp only [finsum_mem_congr rfl (fun χ hχ => hGψ χ hχ x)]
  simp_rw [hLam]

  have hg' : ∀ n, g ⟨tabs n, htabs n⟩ = ∏ v ∈ T, (tabs n (w' v)).1 ^ ks v *
      ((HeckeEigensystem.cNorm (w' v))⁻¹ * (tabs n (w' v)).2) ^ js v := fun n => hg ⟨tabs n, htabs n⟩
  have hsumg : Summable (fun n : ℕ => cs n * g ⟨tabs n, htabs n⟩) := by
    obtain ⟨sf, hsf⟩ := hfinsupp
    exact summable_of_ne_finset_zero (s := sf) fun n hn => by rw [hsf n hn, zero_mul]
  have hval0 : (∑' n, cs n * g ⟨tabs n, htabs n⟩) = Aval T ws ks js := by
    simp_rw [hg']
    exact hlim T hTSL ws w' hw' ks js

  by_cases hfin : A₀.Finite
  swap
  ·
    have h0 : ∀ x, ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ A), (monoW (tw χ) * I0 (tw χ)) * ψ χ x = 0 := by
      intro x
      rw [finsum_mem_def, finsum_of_infinite_support]
      rw [hA₀] at hfin
      refine Set.Infinite.mono (fun χ hχ => ?_) hfin
      rw [Function.mem_support, Set.indicator_of_mem hχ.1]
      exact mul_ne_zero (mul_ne_zero (hmonoW_ne _) hχ.2) (hψ_ne χ x)
    simp_rw [h0, mul_zero, ite_self]
    refine ⟨fun R => integrableOn_zero, hsumg, ?_⟩
    rw [hval0]
    simp only [hAval, dif_neg hfin, integral_zero]
    exact tendsto_const_nhds

  set sχ := hfin.toFinset with hsχ
  have hsχA : ∀ χ ∈ sχ, χ ∈ A ∧ I0 (tw χ) ≠ 0 := by
    intro χ hχ
    have h := hfin.mem_toFinset.mp hχ
    rwa [hA₀] at h
  have hsupp : ∀ x, Function.support (A.indicator fun χ => (monoW (tw χ) * I0 (tw χ)) * ψ χ x) ⊆ (sχ : Set _) := by
    intro x χ hχ
    rw [Function.mem_support] at hχ
    have hχA : χ ∈ A := Set.mem_of_indicator_ne_zero hχ
    rw [Set.indicator_of_mem hχA] at hχ
    rw [hsχ, Set.Finite.coe_toFinset, hA₀]
    exact ⟨hχA, right_ne_zero_of_mul (left_ne_zero_of_mul hχ)⟩
  set F : AdelicGL2 (𝓞 L) L → ℂ := fun x => bC / VC * ∑ χ ∈ sχ, (monoW (tw χ) * I0 (tw χ)) * ψ χ x with hF
  have hFx : ∀ x, bC / VC * ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ A), (monoW (tw χ) * I0 (tw χ)) * ψ χ x = F x := by
    intro x
    simp only [hF]
    congr 1
    rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (hsupp x)]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Set.indicator_of_mem (hsχA χ hχ).1]
  simp_rw [hFx]

  have hcont_inv : ∀ χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ, (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)) →
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ⁻¹ z : ℂˣ) : ℂ) := by
    intro χ hχ
    have : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ⁻¹ z : ℂˣ) : ℂ)) = fun z => (((χ z : ℂˣ) : ℂ))⁻¹ := by
      funext z; rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    rw [this]
    exact hχ.inv₀ fun z => Units.ne_zero _
  have hψc : ∀ χ ∈ sχ, Continuous (ψ χ) := fun χ hχ =>
    (continuous_chiDet (htw_cont χ (hsχA χ hχ).1.2.2)).mul (continuous_chiDet (hcont_inv χ (hsχA χ hχ).1.2.2))
  have hΦ₀sub : Φ₀ ⊆ {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∩
      ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂ := fun x hx => ⟨hΦ₀s hx, hΦ₀S hx⟩
  have hψb : ∀ χ ∈ sχ, ∃ M : ℝ, ∀ x ∈ Φ₀, ‖ψ χ x‖ ≤ M := by
    intro χ hχ
    obtain ⟨M₁, hM₁⟩ := AutomorphicForm.exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
      L (tw χ) (htw_cont χ (hsχA χ hχ).1.2.2) α β hα c u d₁ d₂ Tc hTc
    obtain ⟨M₂, hM₂⟩ := AutomorphicForm.exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
      L χ⁻¹ (hcont_inv χ (hsχA χ hχ).1.2.2) α β hα c u d₁ d₂ Tc hTc
    refine ⟨M₁ * M₂, fun x hx => ?_⟩
    simp only [hψ]
    rw [norm_mul]
    exact mul_le_mul (hM₁ x (hΦ₀sub hx)) (hM₂ x (hΦ₀sub hx)) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ x (hΦ₀sub hx)))

  have hnull : NullMeasurableSet Φ₀ (μ.restrict {g : AdelicGL2 (𝓞 L) L |
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := hΦ₀.nullMeasurableSet
  have hintb : ∀ (f : AdelicGL2 (𝓞 L) L → ℂ), Continuous f → (∃ M : ℝ, ∀ x ∈ Φ₀, ‖f x‖ ≤ M) → IntegrableOn f Φ₀ μ := by
    intro f hf hb
    obtain ⟨M, hM⟩ := hb
    set μ' := μ.restrict {g : AdelicGL2 (𝓞 L) L |
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hμ'
    have hfin' : μ' Φ₀ ≠ ⊤ := ne_top_of_le_ne_top hVfin.ne (Measure.restrict_le_self _)
    have h : IntegrableOn f Φ₀ μ' :=
      Measure.integrableOn_of_bounded hfin' hf.aestronglyMeasurable
        ((ae_restrict_iff'₀ hnull).mpr (Filter.Eventually.of_forall fun x hx => hM x hx))
    have h' : Integrable f (μ'.restrict Φ₀) := h
    rwa [hμ', Measure.restrict_restrict_of_subset hΦ₀s] at h'
  have hψint : ∀ χ ∈ sχ, IntegrableOn (ψ χ) Φ₀ μ := fun χ hχ => hintb _ (hψc χ hχ) (hψb χ hχ)
  have hFc : Continuous F := continuous_const.mul (continuous_finsetSum sχ fun χ hχ => continuous_const.mul (hψc χ hχ))
  have hFb : ∃ M : ℝ, ∀ x ∈ Φ₀, ‖F x‖ ≤ M := by
    choose! Mχ hMχ using hψb
    refine ⟨‖bC / VC‖ * ∑ χ ∈ sχ, ‖monoW (tw χ) * I0 (tw χ)‖ * Mχ χ, fun x hx => ?_⟩
    simp only [hF]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ hχ => ?_)) (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMχ χ hχ x hx) (norm_nonneg _)
  have hFint : IntegrableOn F Φ₀ μ := hintb F hFc hFb
  obtain ⟨hint, htend⟩ := integrableOn_and_tendsto_setIntegral_ite_of_integrableOn μ Φ₀
    (NumberField.AdelicHeight.adelicHeight L) hHm F hFint
  refine ⟨hint, hsumg, ?_⟩

  have hJ : ∀ χ ∈ sχ, ∫ x in Φ₀, ψ χ x ∂μ = if tw χ = χ then VC else 0 := by
    intro χ hχ
    obtain ⟨⟨-, hχt, hχc⟩, -⟩ := hsχA χ hχ
    by_cases hst : tw χ = χ
    · rw [if_pos hst]
      have h1 : ∀ x, ψ χ x = 1 := by
        intro x
        simp only [hψ]
        rw [hst, chiDet_mul_chiDet_inv]
      simp_rw [h1]
      rw [setIntegral_const, Complex.real_smul, mul_one, measureReal_def]
    · rw [if_neg hst]
      have hne : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
          χ (Units.map (((Dg K L).act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
              AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z) ≠ χ z := by
        by_contra hall
        push Not at hall
        exact hst (MonoidHom.ext hall)
      have h := AutomorphicForm.setIntegral_chiDet_sigmaAdelicAct_mul_chiDet_inv_eq_zero_of_isFundamentalDomain_slab K L
        (Dg K L) σ α β Φ₀ hΦ₀s hΦ₀ χ hχt hne
      have hfun : (fun x => ψ χ x) = fun x => chiDet (𝓞 L) L χ (sigmaAdelicAct K L (Dg K L) σ x) * chiDet (𝓞 L) L χ⁻¹ x := by
        funext x
        simp only [hψ]
        rw [chiDet_apply χ, det_sigmaAdelicAct]
        rfl
      rw [show (∫ x in Φ₀, ψ χ x ∂μ) = ∫ x in Φ₀, (fun x => ψ χ x) x ∂μ from rfl, hfun]
      exact h

  have hzero : ∀ χ ∈ sχ, tw χ = χ → ¬ P χ → monoW χ * I0 χ = 0 := by
    intro χ hχ hst hPχ
    have hχc := (hsχA χ hχ).1.2.2
    simp only [hP, not_and, not_forall] at hPχ
    obtain ⟨w, hw⟩ := hPχ hst
    rw [← hW χ hχc]
    exact integral_mul_chiDet_eq_zero_of_isBiInvariantUnder hbi χ hw
  have hval : ∫ x in Φ₀, F x ∂μ = Aval T ws ks js := by
    have h1 : ∫ x in Φ₀, F x ∂μ = bC / VC * ∑ χ ∈ sχ, (monoW (tw χ) * I0 (tw χ)) * ∫ x in Φ₀, ψ χ x ∂μ := by
      simp only [hF]
      rw [integral_const_mul, integral_finsetSum _ (fun χ hχ => (hψint χ hχ).const_mul _)]
      congr 1
      exact Finset.sum_congr rfl fun χ hχ => integral_const_mul _ _
    rw [h1, Finset.sum_congr rfl (fun χ hχ => by rw [hJ χ hχ]), ← Finset.sum_filter_add_sum_filter_not sχ (fun χ => tw χ = χ)]
    have h2 : ∑ χ ∈ sχ.filter (fun χ => ¬ tw χ = χ), (monoW (tw χ) * I0 (tw χ)) * (if tw χ = χ then VC else 0) = 0 :=
      Finset.sum_eq_zero fun χ hχ => by rw [if_neg (Finset.mem_filter.mp hχ).2, mul_zero]
    have h3 : ∑ χ ∈ sχ.filter (fun χ => tw χ = χ), (monoW (tw χ) * I0 (tw χ)) * (if tw χ = χ then VC else 0) =
        ∑ χ ∈ sχ.filter (fun χ => tw χ = χ), monoW χ * I0 χ * VC :=
      Finset.sum_congr rfl fun χ hχ => by
        have hst := (Finset.mem_filter.mp hχ).2
        rw [if_pos hst, hst]
    have h4 : ∑ χ ∈ sχ.filter (fun χ => tw χ = χ), monoW χ * I0 χ * VC = ∑ χ ∈ sχ.filter P, monoW χ * I0 χ * VC := by
      symm
      refine Finset.sum_subset (fun χ hχ => ?_) (fun χ hχ hχ' => ?_)
      · rw [Finset.mem_filter] at hχ ⊢
        exact ⟨hχ.1, hχ.2.1⟩
      · rw [Finset.mem_filter] at hχ
        have hnP : ¬ P χ := fun h => hχ' (Finset.mem_filter.mpr ⟨hχ.1, h⟩)
        rw [hzero χ hχ.1 hχ.2 hnP, zero_mul]
    rw [h2, add_zero, h3, h4]
    simp only [hAval, dif_pos hfin, hκ, ← hsχ, hmonoW]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [hval0, ← hval]
  exact htend

end S_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv
end P2MW
export P2MW.S_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv (solution)
