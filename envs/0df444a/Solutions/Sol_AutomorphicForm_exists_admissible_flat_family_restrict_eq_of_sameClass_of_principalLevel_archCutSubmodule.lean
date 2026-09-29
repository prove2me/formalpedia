-- Prove2me | solution 1 for AutomorphicForm.exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c7b2e118-9257-5746-9e40-372ed5c862f3

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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

import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

namespace Ws31
namespace SectionExt

open AutomorphicForm

variable {K : Type} [Field K] [NumberField K]

theorem norm_diag_eq_one_of_isRowIsometry {L : Type*} [NormedField L] (k : GL (Fin 2) L)
    (hk : AutomorphicForm.WindowedSiegel.IsRowIsometry k) (h10 : (k : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ‖(k : Matrix (Fin 2) (Fin 2) L) 0 0‖ = 1 ∧ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
  obtain ⟨hdet, hrow⟩ := hk
  have h11 : ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
    have := hrow 0 1
    rw [h10] at this
    simp only [zero_mul, one_mul, zero_add, mul_zero, norm_zero, norm_one] at this
    have h0 : 0 ≤ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ := norm_nonneg _
    nlinarith
  refine ⟨?_, h11⟩
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, h11, mul_one] at hdet
  exact hdet

theorem norm_eq_one_of_mul_eq_one (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K)
    (hxy : x * y = 1) (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) : ‖x‖ = 1 := by
  apply le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr hx)
  apply Valued.toNormedField.one_le_norm_iff.mpr
  have h := congrArg Valued.v hxy
  rw [map_mul, map_one] at h
  by_contra hlt
  push_neg at hlt
  have : Valued.v x * Valued.v y < 1 := mul_lt_one_of_lt_of_le hlt hy
  rw [h] at this
  exact lt_irrefl _ this

theorem distribHaarChar_borelDiag_eq_one (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K)
    (hβK : β ∈ adelicMaximalCompact K) :
    ((distribHaarChar (AdeleRing (𝓞 K) K) (borelDiagFst ⟨β, hβ⟩) : ℝ≥0) : ℝ) = 1 ∧
    ((distribHaarChar (AdeleRing (𝓞 K) K) (borelDiagSnd ⟨β, hβ⟩) : ℝ≥0) : ℝ) = 1 := by
  have h10 : (β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hβ

  have harch : ∀ w : InfinitePlace K,
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w‖ = 1 ∧
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w‖ = 1 := by
    intro w
    have hk := hβK.2 w
    have h := norm_diag_eq_one_of_isRowIsometry (archComponent K w (glArch (𝓞 K) K β)) hk (by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 w = 0
      rw [NumberField.AdelicLevel.glArch_apply, h10]; rfl)
    have e0 : ((archComponent K w (glArch (𝓞 K) K β) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w := by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 w = _
      rw [NumberField.AdelicLevel.glArch_apply]
    have e1 : ((archComponent K w (glArch (𝓞 K) K β) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w := by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 w = _
      rw [NumberField.AdelicLevel.glArch_apply]
    rw [e0, e1] at h
    exact h

  have hfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (i : Fin 2),
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v‖ = 1 := by
    intro v i
    have hle := AutomorphicForm.valued_finComponent_apply_le_one hβK v i i

    have ex : ((finComponent (𝓞 K) K v (glFin (𝓞 K) K β) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v := by
      rw [NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply]
    have ey : (((finComponent (𝓞 K) K v (glFin (𝓞 K) K β))⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i =
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v := by
      rw [← map_inv, ← map_inv, NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply]
    rw [ex] at hle; rw [ey] at hle

    have hprod : ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i) *
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i) = 1 := by
      fin_cases i
      · exact congrArg Units.val (mul_inv_cancel (borelDiagFst (⟨β, hβ⟩ : ↥(adelicBorel (𝓞 K) K))))
      · exact congrArg Units.val (mul_inv_cancel (borelDiagSnd (⟨β, hβ⟩ : ↥(adelicBorel (𝓞 K) K))))
    have hprodv : ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v *
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v = 1 := by
      have := congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) hprod
      simp at this ⊢
      exact this
    exact norm_eq_one_of_mul_eq_one v _ _ hprodv hle.1 hle.2
  constructor
  · rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
    show (∏ w : InfinitePlace K, ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).2 v‖ = 1
    rw [Finset.prod_eq_one fun w _ => by rw [(harch w).1, one_pow], finprod_eq_one_of_forall_eq_one fun v => hfin v 0, one_mul]
  · rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
    show (∏ w : InfinitePlace K, ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v‖ = 1
    rw [Finset.prod_eq_one fun w _ => by rw [(harch w).2, one_pow], finprod_eq_one_of_forall_eq_one fun v => hfin v 1, one_mul]

end Ws31.SectionExt

namespace Ws31
namespace SectionExt

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

noncomputable def bPart (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K :=
  (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose

noncomputable def kPart (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K :=
  (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose

theorem bPart_mem (g : AdelicGL2 (𝓞 K) K) : bPart K g ∈ adelicBorel (𝓞 K) K :=
  (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose_spec.1

theorem kPart_mem (g : AdelicGL2 (𝓞 K) K) : kPart K g ∈ adelicMaximalCompact K :=
  ⟨(AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose_spec.2.1,
   (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose_spec.2.2.1⟩

theorem bPart_mul_kPart (g : AdelicGL2 (𝓞 K) K) : bPart K g * kPart K g = g :=
  (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose_spec.2.2.2.symm

noncomputable def bchar (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) : ℂ :=
  ((χ₁ (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ) * ((χ₂ (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ)

theorem bchar_mul (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (b b' : AdelicGL2 (𝓞 K) K)
    (hb : b ∈ adelicBorel (𝓞 K) K) (hb' : b' ∈ adelicBorel (𝓞 K) K) :
    bchar K χ₁ χ₂ (b * b') (mul_mem hb hb') = bchar K χ₁ χ₂ b hb * bchar K χ₁ χ₂ b' hb' := by
  unfold bchar
  have h1 : (⟨b * b', mul_mem hb hb'⟩ : ↥(adelicBorel (𝓞 K) K)) = ⟨b, hb⟩ * ⟨b', hb'⟩ := rfl
  rw [h1, map_mul, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul]; ring

theorem bchar_one (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : bchar K χ₁ χ₂ 1 (one_mem _) = 1 := by
  unfold bchar
  have h1 : (⟨1, one_mem _⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := rfl
  rw [h1, map_one, map_one, map_one, map_one, Units.val_one, mul_one]

theorem bchar_ne_zero (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) :
    bchar K χ₁ χ₂ b hb ≠ 0 := mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)

theorem isInducedSection_iff (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (f : AdelicGL2 (𝓞 K) K → ℂ) :
    IsInducedSection (𝓞 K) K χ₁ χ₂ f ↔ ∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
      f (b * g) = bchar K χ₁ χ₂ b hb * f g := Iff.rfl

private noncomputable def _root_.Ws31.SectionExt.ext (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) where
  toFun f := fun g => bchar K χ₁ χ₂ (bPart K g) (bPart_mem K g) * f (kPart K g)
  map_add' f₁ f₂ := by funext g; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext g; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

p2m_export "Ws31.SectionExt" "ext"
theorem ext_apply (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (f : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    ext K χ₁ χ₂ f g = bchar K χ₁ χ₂ (bPart K g) (bPart_mem K g) * f (kPart K g) := rfl

variable {K}

theorem ext_apply_mul (χ₁ χ₂ χ₁' χ₂' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hagree : ∀ (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K), β ∈ adelicMaximalCompact K →
      bchar K χ₁ χ₂ β hβ = bchar K χ₁' χ₂' β hβ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsInducedSection (𝓞 K) K χ₁' χ₂' f)
    (b k : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K) :
    ext K χ₁ χ₂ f (b * k) = bchar K χ₁ χ₂ b hb * f k := by
  rw [ext_apply]
  set b₀ := bPart K (b * k) with hb₀
  set k₀ := kPart K (b * k) with hk₀
  have hdec : b₀ * k₀ = b * k := bPart_mul_kPart K (b * k)

  have hβB : b⁻¹ * b₀ ∈ adelicBorel (𝓞 K) K := mul_mem (inv_mem hb) (bPart_mem K (b * k))
  have hβeq : b⁻¹ * b₀ = k * k₀⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, hdec, ← mul_assoc, inv_mul_cancel, one_mul]
  have hβK : b⁻¹ * b₀ ∈ adelicMaximalCompact K := by rw [hβeq]; exact mul_mem hk (inv_mem (kPart_mem K (b * k)))
  have hb₀eq : b₀ = b * (b⁻¹ * b₀) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hkeq : k = (b⁻¹ * b₀) * k₀ := by rw [hβeq, mul_assoc, inv_mul_cancel, mul_one]
  have h1 : bchar K χ₁ χ₂ b₀ (bPart_mem K (b * k)) = bchar K χ₁ χ₂ b hb * bchar K χ₁ χ₂ (b⁻¹ * b₀) hβB := by
    have := bchar_mul K χ₁ χ₂ b (b⁻¹ * b₀) hb hβB
    rw [← this]
    congr 1
  have hf' := (isInducedSection_iff K χ₁' χ₂' f).mp hf
  rw [h1, hagree _ hβB hβK, mul_assoc, ← hf' (b⁻¹ * b₀) hβB k₀, ← hkeq]

theorem ext_isInducedSection (χ₁ χ₂ χ₁' χ₂' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hagree : ∀ (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K), β ∈ adelicMaximalCompact K →
      bchar K χ₁ χ₂ β hβ = bchar K χ₁' χ₂' β hβ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsInducedSection (𝓞 K) K χ₁' χ₂' f) :
    IsInducedSection (𝓞 K) K χ₁ χ₂ (ext K χ₁ χ₂ f) := by
  intro b hb g
  show ext K χ₁ χ₂ f (b * g) = bchar K χ₁ χ₂ b hb * ext K χ₁ χ₂ f g
  conv_lhs => rw [← bPart_mul_kPart K g, ← mul_assoc]
  rw [ext_apply_mul χ₁ χ₂ χ₁' χ₂' hagree f hf _ _ (mul_mem hb (bPart_mem K g)) (kPart_mem K g), bchar_mul, mul_assoc, ext_apply]

theorem ext_apply_of_mem (χ₁ χ₂ χ₁' χ₂' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hagree : ∀ (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K), β ∈ adelicMaximalCompact K →
      bchar K χ₁ χ₂ β hβ = bchar K χ₁' χ₂' β hβ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsInducedSection (𝓞 K) K χ₁' χ₂' f)
    (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K) : ext K χ₁ χ₂ f k = f k := by
  have := ext_apply_mul χ₁ χ₂ χ₁' χ₂' hagree f hf 1 k (one_mem _) hk
  rwa [one_mul, bchar_one, one_mul] at this

theorem ext_apply_mul_right (χ₁ χ₂ χ₁' χ₂' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hagree : ∀ (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K), β ∈ adelicMaximalCompact K →
      bchar K χ₁ χ₂ β hβ = bchar K χ₁' χ₂' β hβ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsInducedSection (𝓞 K) K χ₁' χ₂' f)
    (x : AdelicGL2 (𝓞 K) K) (hx : x ∈ adelicMaximalCompact K) (g : AdelicGL2 (𝓞 K) K) :
    ext K χ₁ χ₂ f (g * x) = ext K χ₁ χ₂ (fun h => f (h * x)) g := by
  have hf' : IsInducedSection (𝓞 K) K χ₁' χ₂' (fun h => f (h * x)) := fun b hb h => by
    show f (b * h * x) = _ * f (h * x); rw [mul_assoc]; exact hf b hb (h * x)
  conv_lhs => rw [← bPart_mul_kPart K g, mul_assoc]
  rw [ext_apply_mul χ₁ χ₂ χ₁' χ₂' hagree f hf _ _ (bPart_mem K g) (mul_mem (kPart_mem K g) hx)]
  conv_rhs => rw [← bPart_mul_kPart K g]
  rw [ext_apply_mul χ₁ χ₂ χ₁' χ₂' hagree _ hf' _ _ (bPart_mem K g) (kPart_mem K g)]

end Ws31.SectionExt

namespace Ws31
namespace SectionExt

open AutomorphicForm

variable {K : Type} [Field K] [NumberField K]

theorem level_mem_maximalCompact (N : Ideal (𝓞 K)) (u : AdelicGL2 (𝓞 K) K)
    (hu : u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) : u ∈ adelicMaximalCompact K := by
  rw [AutomorphicForm.mem_adelicMaximalCompact_iff]
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
  have h1 := NumberField.AdelicLevel.mem_levelOne_iff.mp (NumberField.AdelicLevel.principalLevel_le_levelOne _ _ N hu1)
  rw [NumberField.AdelicLevel.mem_finiteLevelOne_iff] at h1
  refine ⟨NumberField.AdelicLevel.mem_finiteIntegralGL2_iff.mpr ⟨h1.1.integral, h1.2.integral⟩, fun w => ?_⟩
  rw [(mem_finiteAdelicGL2Subgroup_iff K u).mp hu2, map_one]
  exact AutomorphicForm.WindowedSiegel.isRowIsometry_one

theorem archRow_mem_maximalCompact (w : InfinitePlace K) (x : ↥(archRowIsometrySubgroup K w)) :
    (x : AdelicGL2 (𝓞 K) K) ∈ adelicMaximalCompact K := by
  obtain ⟨r, hr, hx⟩ := Subgroup.mem_map.mp x.2
  rw [AutomorphicForm.mem_adelicMaximalCompact_iff, ← hx]
  refine ⟨?_, fun w' => ?_⟩
  · show glFin (𝓞 K) K ((adelicArchGLIncl K) (archGLIncl K w r)) ∈ _
    rw [glFin_adelicArchGLIncl]; exact one_mem _
  · show AutomorphicForm.WindowedSiegel.IsRowIsometry (archComponent K w' (glArch (𝓞 K) K ((adelicArchGLIncl K) (archGLIncl K w r))))
    rw [glArch_adelicArchGLIncl]
    by_cases h : w' = w
    · subst h; rw [archComponent_archGLIncl_self]; exact AutomorphicForm.WindowedSiegel.mem_rowIsometrySubgroup_iff.mp hr
    · rw [archComponent_archGLIncl_of_ne K h]; exact AutomorphicForm.WindowedSiegel.isRowIsometry_one

theorem rowIsometryInclAt₀_mem_maximalCompact (w : InfinitePlace K) (h : ↥(rowIsometrySubgroup₀ w.Completion)) :
    rowIsometryInclAt₀ K w h ∈ adelicMaximalCompact K := by
  have hmem : rowIsometryInclAt₀ K w h ∈ archRowIsometrySubgroup K w := by
    refine Subgroup.mem_map.mpr ⟨(h : GL (Fin 2) w.Completion), ?_, rfl⟩
    exact rowIsometrySubgroup₀_le _ h.2
  exact archRow_mem_maximalCompact w ⟨_, hmem⟩

theorem rowIsometryInclAt₀_injective (w : InfinitePlace K) : Function.Injective (rowIsometryInclAt₀ K w) := by
  intro a b hab
  apply Subtype.ext
  have := congrArg (fun g => archComponent K w (glArch (𝓞 K) K g)) hab
  change archComponent K w (glArch (𝓞 K) K ((adelicArchGLIncl K) (archGLIncl K w (a : GL (Fin 2) w.Completion)))) =
    archComponent K w (glArch (𝓞 K) K ((adelicArchGLIncl K) (archGLIncl K w (b : GL (Fin 2) w.Completion)))) at this
  rwa [glArch_adelicArchGLIncl, glArch_adelicArchGLIncl, archComponent_archGLIncl_self, archComponent_archGLIncl_self] at this

end Ws31.SectionExt

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    let Adm : (∀ x, 0 < ((αm x : ℝˣ) : ℝ)) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) →
        (ℂ → AdelicGL2 (𝓞 K) K → ℂ) → Prop := fun hαm μ ν ψf =>
      IsUnitaryChar (𝓞 K) K μ ∧ IsUnitaryChar (𝓞 K) K ν ∧
      IsIdeleClassChar (𝓞 K) K μ ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)) ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s)) ∧
      (∀ s, IsArchKFinite K (ψf s)) ∧
      (∀ s, IsKfSmooth K (ψf s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => ψf s g)) ∧
      (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
      (∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g) ∧
      (∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
    let SameClass : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) →
        ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → Prop := fun μ' ν' μ ν =>
      ∀ (g : AdelicGL2 (𝓞 K) K) (hg : g ∈ adelicBorel (𝓞 K) K), g ∈ adelicMaximalCompact K →
        ((μ (borelDiagFst ⟨g, hg⟩) : ℂˣ) : ℂ) * ((ν (borelDiagSnd ⟨g, hg⟩) : ℂˣ) : ℂ) =
          ((μ' (borelDiagFst ⟨g, hg⟩) : ℂˣ) : ℂ) * ((ν' (borelDiagSnd ⟨g, hg⟩) : ℂˣ) : ℂ)
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (ψf' : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hadm : Adm hαm μ' ν' ψf')
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (_hclass : SameClass μ' ν' μ ν),
    ∃ φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ, Adm hαm μ ν φ ∧
      ∀ (s : ℂ) (k : adelicMaximalCompact K), φ s (k : AdelicGL2 (𝓞 K) K) = ψf' 0 (k : AdelicGL2 (𝓞 K) K) := by
  intro αm Adm SameClass hαm μ' ν' ψf' hadm μ ν hμ hν hμic hνic hμc hνc hμν hclass
  obtain ⟨hμ', hν', hμic', hνic', hμc', hνc', hμν', hψf, hψfK, hψff, hψfjc, hψfhol, hψfKu, hψfflat, hψflev, hψfty⟩ := hadm
  have hαI : ∀ x : (AdeleRing (𝓞 K) K)ˣ, ((αm x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm K x := fun _ => rfl

  have hagree : ∀ (s : ℂ) (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K), β ∈ adelicMaximalCompact K →
      Ws31.SectionExt.bchar K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) β hβ =
        Ws31.SectionExt.bchar K (etaFst μ' αm hαm 0) (etaSnd ν' αm hαm 0) β hβ := by
    intro s β hβ hβK
    obtain ⟨h1, h2⟩ := Ws31.SectionExt.distribHaarChar_borelDiag_eq_one β hβ hβK
    unfold Ws31.SectionExt.bchar
    rw [etaFst_apply, etaSnd_apply, etaFst_apply, etaSnd_apply]
    simp only [Units.val_mul, cpowChar_apply_val]
    rw [show (((αm (borelDiagFst ⟨β, hβ⟩) : ℝˣ) : ℝ) : ℂ) = 1 by rw [hαI]; unfold NumberField.TateGlobal.ideleNorm; exact_mod_cast h1,
      show (((αm (borelDiagSnd ⟨β, hβ⟩) : ℝˣ) : ℝ) : ℂ) = 1 by rw [hαI]; unfold NumberField.TateGlobal.ideleNorm; exact_mod_cast h2]
    simp only [Complex.one_cpow, mul_one]
    exact hclass β hβ hβK

  set E₀ := Ws31.SectionExt.ext K (etaFst μ αm hαm 0) (etaSnd ν αm hαm 0) with hE₀
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : AdelicGL2 (𝓞 K) K → ℂ, φ₀ = E₀ (ψf' 0) := ⟨_, rfl⟩
  have hφ₀sec : IsInducedSection (𝓞 K) K (etaFst μ αm hαm 0) (etaSnd ν αm hαm 0) φ₀ := by
    rw [hφ₀]; exact Ws31.SectionExt.ext_isInducedSection _ _ _ _ (hagree 0) (ψf' 0) (hψf 0)
  have hφ₀res : ∀ k : adelicMaximalCompact K, φ₀ (k : AdelicGL2 (𝓞 K) K) = ψf' 0 (k : AdelicGL2 (𝓞 K) K) := by
    intro k; rw [hφ₀]; exact Ws31.SectionExt.ext_apply_of_mem _ _ _ _ (hagree 0) (ψf' 0) (hψf 0) k k.2
  have hφ₀right : ∀ (x : AdelicGL2 (𝓞 K) K), x ∈ adelicMaximalCompact K → ∀ g,
      φ₀ (g * x) = E₀ (fun h => ψf' 0 (h * x)) g := by
    intro x hx g; rw [hφ₀]; exact Ws31.SectionExt.ext_apply_mul_right _ _ _ _ (hagree 0) (ψf' 0) (hψf 0) x hx g
  have hφ₀lev : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g := by
    intro g u hu
    rw [hφ₀right u (Ws31.SectionExt.level_mem_maximalCompact N u hu) g]
    have : (fun h => ψf' 0 (h * u)) = ψf' 0 := funext fun h => hψflev 0 h u hu
    rw [this, hφ₀]

  have hψ0c : Continuous (ψf' 0) := hψfjc.comp (continuous_const.prodMk continuous_id)
  have hcharc : ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) (r : ℂ),
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ * cpowChar αm hαm r) z : ℂˣ) : ℂ) := by
    intro χ hχc r
    have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ * cpowChar αm hαm r) z : ℂˣ) : ℂ)) =
        fun z => ((χ z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z : ℝ) : ℂ) ^ r) := by
      funext z; rw [MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val, hαI]
    rw [this]
    refine hχc.mul ((Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm K)).cpow continuous_const ?_)
    intro z
    exact Complex.ofReal_mem_slitPlane.mpr (NumberField.TateGlobal.ideleNorm_pos z)
  have hφ₀c : Continuous φ₀ := by
    have key := AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact K (X := Unit) Set.univ isOpen_univ
      (fun _ => etaFst μ αm hαm 0) (fun _ => etaSnd ν αm hαm 0)
      (((hcharc μ hμc _).comp continuous_snd).continuousOn) (((hcharc ν hνc _).comp continuous_snd).continuousOn)
      (fun _ => φ₀) (fun _ _ => hφ₀sec) (by
        refine ((hψ0c.comp continuous_snd).continuousOn).congr fun p hp => ?_
        exact hφ₀res ⟨p.2, hp.2⟩)
    rw [Set.univ_prod_univ, continuousOn_univ] at key
    have hι : Continuous fun g : AdelicGL2 (𝓞 K) K => (((), g) : Unit × AdelicGL2 (𝓞 K) K) :=
      continuous_const.prodMk continuous_id
    exact key.comp hι

  have hφ₀K : IsArchKFinite K φ₀ := by
    intro w
    obtain ⟨s, hs⟩ := hψfK 0 w
    classical
    refine ⟨s.image E₀, fun k hk => ?_⟩
    have hk' : k ∈ adelicMaximalCompact K := Ws31.SectionExt.archRow_mem_maximalCompact w ⟨k, hk⟩
    have hfun : (fun x => φ₀ (x * k)) = E₀ (fun x => ψf' 0 (x * k)) := funext fun x => hφ₀right k hk' x
    rw [hfun, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem (hs k hk)

  have hφ₀f : IsKfSmooth K φ₀ := by
    rw [isKfSmooth_iff] at ⊢
    have hψ := (FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup).mp ((isKfSmooth_iff K (ψf' 0)).mp (hψff 0))
    obtain ⟨U, hUo, hU⟩ := hψ
    refine (FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup).mpr
      ⟨U ⊓ (levelZero (𝓞 K) K (⊤ : Ideal (𝓞 K))).comap (finiteAdelicGL2Subgroup K).subtype, ?_, ?_⟩
    · rw [Subgroup.coe_inf, Subgroup.coe_comap]
      exact hUo.inter ((NumberField.AdelicLevel.isOpen_levelZero (𝓞 K) K (N := ⊤) top_ne_bot).preimage continuous_subtype_val)
    · intro u hu
      obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
      have huK : (u : AdelicGL2 (𝓞 K) K) ∈ adelicMaximalCompact K := by
        rw [AutomorphicForm.mem_adelicMaximalCompact_iff]
        refine ⟨NumberField.AdelicLevel.mem_levelZero_iff.mp (Subgroup.mem_comap.mp hu2), fun w => ?_⟩
        rw [(mem_finiteAdelicGL2Subgroup_iff K _).mp u.2, map_one]; exact AutomorphicForm.WindowedSiegel.isRowIsometry_one
      have hfix : ∀ x, ψf' 0 (x * (u : AdelicGL2 (𝓞 K) K)) = ψf' 0 x := fun x => by
        have := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) (hU u hu1)
        simpa [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul] using this
      apply FLT.SmoothVectors.RightTranslationFn.ext
      intro x
      rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul]
      show φ₀ (x * (u : AdelicGL2 (𝓞 K) K)) = φ₀ x
      rw [hφ₀right _ huK x]
      have : (fun h => ψf' 0 (h * (u : AdelicGL2 (𝓞 K) K))) = ψf' 0 := funext hfix
      rw [this, hφ₀]

  obtain ⟨φ, hφ0, hφsec, hφK, hφf, hφjc, hφhol, hφflat⟩ :=
    AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection K hαm μ ν 0 φ₀ hφ₀sec hφ₀K hφ₀f hφ₀c

  have S5 : ∀ (s : ℂ) (k : adelicMaximalCompact K), φ s (k : AdelicGL2 (𝓞 K) K) = ψf' 0 (k : AdelicGL2 (𝓞 K) K) := by
    intro s k
    rw [hφflat s 0 (k : AdelicGL2 (𝓞 K) K) k.2.1 k.2.2, hφ0, hφ₀res k]
  have S5' : ∀ (s : ℂ) (k : adelicMaximalCompact K), φ s (k : AdelicGL2 (𝓞 K) K) = φ 0 (k : AdelicGL2 (𝓞 K) K) := by
    intro s k; rw [S5 s k, S5 0 k]

  have hφE : ∀ s : ℂ, φ s = Ws31.SectionExt.ext K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf' 0) := by
    intro s
    funext g
    obtain ⟨b, k, hb, hkf, hka, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
    have hk : k ∈ adelicMaximalCompact K := ⟨hkf, hka⟩
    rw [Ws31.SectionExt.ext_apply_mul _ _ _ _ (hagree s) (ψf' 0) (hψf 0) b k hb hk,
      (Ws31.SectionExt.isInducedSection_iff K _ _ _).mp (hφsec s) b hb k, S5 s ⟨k, hk⟩]

  have S6 : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ s (g * u) = φ s g := by
    intro s g u hu
    rw [hφE s, Ws31.SectionExt.ext_apply_mul_right _ _ _ _ (hagree s) (ψf' 0) (hψf 0) u
      (Ws31.SectionExt.level_mem_maximalCompact N u hu) g]
    have : (fun h => ψf' 0 (h * u)) = ψf' 0 := funext fun h => hψflev 0 h u hu
    rw [this]

  have S7 : ∀ s : ℂ, φ s ∈ archCutSubmodule K tysK := by
    intro s
    rw [hφE s]
    show _ ∈ ⨅ w, ⨆ i, archTypeSubmoduleAt K w (tysK.rep w i)
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    have hut : ψf' 0 ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K w) (tysK.rep w i).ρ :=
      (Submodule.mem_iInf _).mp (hψfty 0) w
    let C := inducedSectionSubmodule (R := 𝓞 K) (K := K) (etaFst μ' αm hαm 0) (etaSnd ν' αm hαm 0)
    have hC : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (u : AdelicGL2 (𝓞 K) K → ℂ), u ∈ C →
        (fun κ => u (κ * rowIsometryInclAt₀ K w k)) ∈ C := fun k u hu => IsInducedSection.rightTranslate hu _
    let A : ↥C →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
      (Ws31.SectionExt.ext K (etaFst μ αm hαm s) (etaSnd ν αm hαm s)).comp C.subtype
    have hA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (u : ↥C) (x : AdelicGL2 (𝓞 K) K),
        A ⟨fun κ => (u : AdelicGL2 (𝓞 K) K → ℂ) (κ * rowIsometryInclAt₀ K w k), hC k u u.2⟩ x =
          A u (x * rowIsometryInclAt₀ K w k) := by
      intro k u x
      show Ws31.SectionExt.ext K _ _ (fun κ => (u : AdelicGL2 (𝓞 K) K → ℂ) (κ * rowIsometryInclAt₀ K w k)) x =
        Ws31.SectionExt.ext K _ _ (u : AdelicGL2 (𝓞 K) K → ℂ) (x * rowIsometryInclAt₀ K w k)
      rw [Ws31.SectionExt.ext_apply_mul_right _ _ _ _ (hagree s) _ u.2 _
        (Ws31.SectionExt.rowIsometryInclAt₀_mem_maximalCompact w k) x]
    have key := AutomorphicForm.apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
      (rowIsometryInclAt₀ K w) (rowIsometryInclAt₀ K w) (Ws31.SectionExt.rowIsometryInclAt₀_injective w)
      C hC A hA (fun i => (tysK.rep w i).ρ) (ψf' 0) (hψf 0) hut
    exact key

  have S8 : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        (fun k : ↥(archRowIsometrySubgroup K v) => φ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W := by
    intro v
    obtain ⟨W, hW, hmem⟩ := hψfKu v
    refine ⟨W, hW, fun s g => ?_⟩
    obtain ⟨b, k, hb, hkf, hka, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
    have hfun : (fun x : ↥(archRowIsometrySubgroup K v) => φ s (b * k * (x : AdelicGL2 (𝓞 K) K))) =
        ((((etaFst μ αm hαm s) (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ) * (((etaSnd ν αm hαm s) (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ)) •
          (fun x : ↥(archRowIsometrySubgroup K v) => ψf' 0 (k * (x : AdelicGL2 (𝓞 K) K))) := by
      funext x
      have hkx : k * (x : AdelicGL2 (𝓞 K) K) ∈ adelicMaximalCompact K :=
        mul_mem ⟨hkf, hka⟩ (Ws31.SectionExt.archRow_mem_maximalCompact v x)
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc, hφsec s b hb, S5 s ⟨k * (x : AdelicGL2 (𝓞 K) K), hkx⟩]
    rw [hfun]
    exact W.smul_mem _ (hmem 0 k)
  exact ⟨φ, ⟨hμ, hν, hμic, hνic, hμc, hνc, hμν, hφsec, hφK, hφf, hφjc, hφhol, S8, S5', S6, S7⟩, S5⟩

end S_AutomorphicForm_exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule (solution)
