-- Prove2me | solution 1 for AutomorphicForm.isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ebbbb488-73ce-5f4b-8749-99701b7f595a

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LocalGL2_iwasawa_decomposition
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm AdelicDock LocalGL2
open scoped NNReal

namespace PSUnram

variable {K : Type} [Field K] [NumberField K]

def locAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    AdelicGL2 (𝓞 K) K →* GL (Fin 2) (v.adicCompletion K) :=
  (finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)

def emb (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (v.adicCompletion K) →* AdelicGL2 (𝓞 K) K :=
  (finEmbed (𝓞 K) K).comp (localEmbed (𝓞 K) K v)

theorem locAt_def (v : HeightOneSpectrum (𝓞 K)) (h : AdelicGL2 (𝓞 K) K) :
    locAt K v h = finComponent (𝓞 K) K v (glFin (𝓞 K) K h) := rfl

theorem eq_of_glArch_eq_of_glFin_eq {x y : AdelicGL2 (𝓞 K) K}
    (h₁ : glArch (𝓞 K) K x = glArch (𝓞 K) K y) (h₂ : glFin (𝓞 K) K x = glFin (𝓞 K) K y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem eq_of_forall_finComponent_eq (a b : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    (h : ∀ w : HeightOneSpectrum (𝓞 K), finComponent (𝓞 K) K w a = finComponent (𝓞 K) K w b) :
    a = b := by
  apply Units.ext
  ext i j w
  exact congrArg
    (fun m : GL (Fin 2) (w.adicCompletion K) => (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) (h w)

theorem glArch_emb (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) :
    glArch (𝓞 K) K (emb K v y) = 1 := glArch_finEmbed _ _ _

theorem glFin_emb (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) :
    glFin (𝓞 K) K (emb K v y) = localEmbed (𝓞 K) K v y := glFin_finEmbed _ _ _

theorem locAt_emb_self (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) :
    locAt K v (emb K v y) = y := by
  rw [locAt_def, glFin_emb, finComponent_localEmbed_self]

theorem emb_mul_comm {v : HeightOneSpectrum (𝓞 K)} {h : AdelicGL2 (𝓞 K) K}
    (hv : locAt K v h = 1) (y : GL (Fin 2) (v.adicCompletion K)) :
    emb K v y * h = h * emb K v y := by
  rw [locAt_def] at hv
  apply eq_of_glArch_eq_of_glFin_eq
  · simp only [map_mul, glArch_emb, one_mul, mul_one]
  · simp only [map_mul, glFin_emb]
    apply eq_of_forall_finComponent_eq
    intro w
    by_cases hw : w = v
    · subst hw
      simp only [map_mul, finComponent_localEmbed_self, hv, one_mul, mul_one]
    · simp only [map_mul, finComponent_localEmbed_of_ne (𝓞 K) K v y hw, one_mul, mul_one]

def away (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K :=
  (emb K v (locAt K v g))⁻¹ * g

theorem emb_locAt_mul_away (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) :
    emb K v (locAt K v g) * away v g = g :=
  mul_inv_cancel_left _ _

theorem locAt_away (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) :
    locAt K v (away v g) = 1 := by
  rw [away, map_mul, map_inv, locAt_emb_self, inv_mul_cancel]

theorem emb_apply_fst (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) (i j : Fin 2) :
    (((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  rw [← glArch_apply, glArch_emb, Units.val_one]

theorem emb_apply_snd_self (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) (i j : Fin 2) :
    (((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v =
      (y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  show (finComponent (𝓞 K) K v (glFin (𝓞 K) K (emb K v y)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j = _
  rw [glFin_emb, finComponent_localEmbed_self]

theorem emb_apply_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) (i j : Fin 2)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    (((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 w =
      (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  show (finComponent (𝓞 K) K w (glFin (𝓞 K) K (emb K v y)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j = _
  rw [glFin_emb, finComponent_localEmbed_of_ne (𝓞 K) K v y hw, Units.val_one]

def idl (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)

theorem idl_fst (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem idl_snd_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = t := by
  show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = t
  exact localUnit_apply_self (𝓞 K) K v t

theorem idl_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ≠ v) : ((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1
  exact localUnit_apply_of_ne (𝓞 K) K v t hw

theorem localChar_eq_idl (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : TateGlobal.localChar χ v t = χ (idl K v t) := rfl

theorem idl_one (v : HeightOneSpectrum (𝓞 K)) : idl K v 1 = 1 := by
  rw [idl, map_one, map_one]

theorem distribHaarChar_idl_of_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = 1) :
    ((distribHaarChar (AdeleRing (𝓞 K) K) (idl K v t) : ℝ≥0) : ℝ) = 1 := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm K (idl K v t)]
  have h1 : ∏ w : InfinitePlace K,
      ‖((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [idl_fst, show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  have h2 : ∏ᶠ u : HeightOneSpectrum (𝓞 K),
      ‖((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 u‖ = ‖(t : v.adicCompletion K)‖ := by
    rw [finprod_eq_single _ v fun u hu => by rw [idl_snd_of_ne v t hu, norm_one], idl_snd_self]
  rw [h1, one_mul, h2, NumberField.FinitePlace.norm_def, ht, map_one, NNReal.coe_one]

theorem emb_mem_adelicBorel (v : HeightOneSpectrum (𝓞 K)) {y : GL (Fin 2) (v.adicCompletion K)}
    (hy : y ∈ borelSubgroup (v.adicCompletion K)) : emb K v y ∈ adelicBorel (𝓞 K) K := by
  rw [mem_borelSubgroup_iff] at hy
  show ((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
  refine Prod.ext ?_ ?_
  · rw [emb_apply_fst, Matrix.one_apply_ne (by decide)]
    rfl
  · refine FiniteAdeleRing.ext K fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [emb_apply_snd_self, hy]
      rfl
    · rw [emb_apply_snd_of_ne v y 1 0 hw, Matrix.one_apply_ne (by decide)]
      rfl

theorem borelDiagFst_emb (v : HeightOneSpectrum (𝓞 K)) {y : GL (Fin 2) (v.adicCompletion K)}
    (hy : y ∈ borelSubgroup (v.adicCompletion K)) (hmem : emb K v y ∈ adelicBorel (𝓞 K) K) :
    borelDiagFst (⟨emb K v y, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) =
      idl K v (borelDiagFst (⟨y, hy⟩ : ↥(borelSubgroup (v.adicCompletion K)))) := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = _
  refine Prod.ext ?_ ?_
  · rw [emb_apply_fst, Matrix.one_apply_eq, idl_fst]
  · refine FiniteAdeleRing.ext K fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [emb_apply_snd_self, idl_snd_self, borelDiagFst_apply_val]
    · rw [emb_apply_snd_of_ne v y 0 0 hw, Matrix.one_apply_eq, idl_snd_of_ne v _ hw]

theorem borelDiagSnd_emb (v : HeightOneSpectrum (𝓞 K)) {y : GL (Fin 2) (v.adicCompletion K)}
    (hy : y ∈ borelSubgroup (v.adicCompletion K)) (hmem : emb K v y ∈ adelicBorel (𝓞 K) K) :
    borelDiagSnd (⟨emb K v y, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) =
      idl K v (borelDiagSnd (⟨y, hy⟩ : ↥(borelSubgroup (v.adicCompletion K)))) := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = _
  refine Prod.ext ?_ ?_
  · rw [emb_apply_fst, Matrix.one_apply_eq, idl_fst]
  · refine FiniteAdeleRing.ext K fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [emb_apply_snd_self, idl_snd_self, borelDiagSnd_apply_val]
    · rw [emb_apply_snd_of_ne v y 1 1 hw, Matrix.one_apply_eq, idl_snd_of_ne v _ hw]

theorem isInducedSection_emb_mul {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (v : HeightOneSpectrum (𝓞 K))
    {y : GL (Fin 2) (v.adicCompletion K)} (hy : y ∈ borelSubgroup (v.adicCompletion K))
    (g : AdelicGL2 (𝓞 K) K) :
    φ (emb K v y * g) =
      ((χ₁ (idl K v (borelDiagFst (⟨y, hy⟩ : ↥(borelSubgroup (v.adicCompletion K))))) : ℂˣ) : ℂ) *
        ((χ₂ (idl K v (borelDiagSnd (⟨y, hy⟩ : ↥(borelSubgroup (v.adicCompletion K))))) : ℂˣ) : ℂ) *
          φ g := by
  rw [hφ (emb K v y) (emb_mem_adelicBorel v hy) g, borelDiagFst_emb v hy, borelDiagSnd_emb v hy]

section Torus

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

def oneDiag {A : Type*} [CommRing A] (a : Aˣ) : GL (Fin 2) A where
  val := Matrix.diagonal ![1, (a : A)]
  inv := Matrix.diagonal ![1, ((a⁻¹ : Aˣ) : A)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem oneDiag_coe_apply {A : Type*} [CommRing A] (a : Aˣ) (i j : Fin 2) :
    (oneDiag a : Matrix (Fin 2) (Fin 2) A) i j = Matrix.diagonal ![1, (a : A)] i j := rfl

theorem diagOne_mem_borel (t : (Kv)ˣ) : (diagOne t : GL (Fin 2) Kv) ∈ borelSubgroup Kv := by
  rw [mem_borelSubgroup_iff, diagOne_coe_apply]
  simp

theorem oneDiag_mem_borel (t : (Kv)ˣ) : (oneDiag t : GL (Fin 2) Kv) ∈ borelSubgroup Kv := by
  rw [mem_borelSubgroup_iff, oneDiag_coe_apply]
  simp

theorem borelDiagFst_diagOne (t : (Kv)ˣ) :
    borelDiagFst (⟨diagOne t, diagOne_mem_borel v t⟩ : ↥(borelSubgroup Kv)) = t := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show (diagOne t : Matrix (Fin 2) (Fin 2) Kv) 0 0 = t
  rw [diagOne_coe_apply]
  simp

theorem borelDiagSnd_diagOne (t : (Kv)ˣ) :
    borelDiagSnd (⟨diagOne t, diagOne_mem_borel v t⟩ : ↥(borelSubgroup Kv)) = 1 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show (diagOne t : Matrix (Fin 2) (Fin 2) Kv) 1 1 = 1
  rw [diagOne_coe_apply]
  simp

theorem borelDiagFst_oneDiag (t : (Kv)ˣ) :
    borelDiagFst (⟨oneDiag t, oneDiag_mem_borel v t⟩ : ↥(borelSubgroup Kv)) = 1 := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show (oneDiag t : Matrix (Fin 2) (Fin 2) Kv) 0 0 = 1
  rw [oneDiag_coe_apply]
  simp

theorem borelDiagSnd_oneDiag (t : (Kv)ˣ) :
    borelDiagSnd (⟨oneDiag t, oneDiag_mem_borel v t⟩ : ↥(borelSubgroup Kv)) = t := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show (oneDiag t : Matrix (Fin 2) (Fin 2) Kv) 1 1 = t
  rw [oneDiag_coe_apply]
  simp

def unitOf (t : (Kv)ˣ) (ht : (t : Kv) ∈ v.adicCompletionIntegers K)
    (hti : ((t⁻¹ : (Kv)ˣ) : Kv) ∈ v.adicCompletionIntegers K) : (𝓞v)ˣ where
  val := ⟨t, ht⟩
  inv := ⟨((t⁻¹ : (Kv)ˣ) : Kv), hti⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

theorem diagOne_mem_integralSubgroup (t : (Kv)ˣ) (ht : (t : Kv) ∈ v.adicCompletionIntegers K)
    (hti : ((t⁻¹ : (Kv)ˣ) : Kv) ∈ v.adicCompletionIntegers K) :
    (diagOne t : GL (Fin 2) Kv) ∈ integralSubgroup (𝓞v) Kv := by
  refine ⟨diagOne (unitOf v t ht hti), ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [unitOf]

theorem oneDiag_mem_integralSubgroup (t : (Kv)ˣ) (ht : (t : Kv) ∈ v.adicCompletionIntegers K)
    (hti : ((t⁻¹ : (Kv)ˣ) : Kv) ∈ v.adicCompletionIntegers K) :
    (oneDiag t : GL (Fin 2) Kv) ∈ integralSubgroup (𝓞v) Kv := by
  refine ⟨oneDiag (unitOf v t ht hti), ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, oneDiag_coe_apply, oneDiag_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [unitOf]

theorem valued_eq_one_of_mem_of_inv_mem (t : (Kv)ˣ) (ht : (t : Kv) ∈ v.adicCompletionIntegers K)
    (hti : ((t⁻¹ : (Kv)ˣ) : Kv) ∈ v.adicCompletionIntegers K) :
    Valued.v (t : Kv) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht hti
  have ht0 : Valued.v (t : Kv) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  rw [Units.val_inv_eq_inv_val, map_inv₀] at hti
  have h1 : 1 ≤ Valued.v (t : Kv) := by
    have := mul_le_mul_left hti (Valued.v (t : Kv))
    rwa [inv_mul_cancel₀ ht0, one_mul] at this
  exact le_antisymm ht h1

end Torus

section Level

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem entries_integral_of_mem_integralSubgroup {u : GL (Fin 2) Kv} (hu : u ∈ integralSubgroup (𝓞v) Kv) :
    (∀ i j, (u : Matrix (Fin 2) (Fin 2) Kv) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((u⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) i j ∈ v.adicCompletionIntegers K := by
  obtain ⟨y, rfl⟩ := hu
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.GeneralLinearGroup.map_apply]
    exact SetLike.coe_mem _
  · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]
    exact SetLike.coe_mem _

theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 K)} (hNv : idealBound (𝓞 K) N v = 1)
    {m : Matrix (Fin 2) (Fin 2) Kv} (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers K) :
    IsLocalLevelOne (𝓞 K) K v N m := by
  refine ⟨hm, ?_, ?_⟩
  · rw [hNv]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  · rw [hNv]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (sub_mem (hm 1 1) (one_mem _))

theorem localEmbed_mem_finiteLevelOne {N : Ideal (𝓞 K)} (hNv : idealBound (𝓞 K) N v = 1)
    {u : GL (Fin 2) Kv} (hu : u ∈ integralSubgroup (𝓞v) Kv) :
    localEmbed (𝓞 K) K v u ∈ finiteLevelOne (𝓞 K) K N := by
  rw [localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
  obtain ⟨h1, h2⟩ := entries_integral_of_mem_integralSubgroup v hu
  exact ⟨isLocalLevelOne_of_integral v hNv h1, isLocalLevelOne_of_integral v hNv h2⟩

theorem finComponent_glFin_weyl :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K (weyl (𝓞 K) K)) = weylInt (𝓞v) Kv := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_apply, glFin_apply, coe_weylInt]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_weyl_conj_emb (u : GL (Fin 2) Kv) :
    glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * emb K v u * weyl (𝓞 K) K) =
      localEmbed (𝓞 K) K v ((weylInt (𝓞v) Kv)⁻¹ * u * weylInt (𝓞v) Kv) := by
  rw [map_mul, map_mul, map_inv, glFin_emb]
  apply eq_of_forall_finComponent_eq
  intro w
  by_cases hw : w = v
  · subst hw
    rw [map_mul, map_mul, map_inv, finComponent_localEmbed_self, finComponent_localEmbed_self,
      finComponent_glFin_weyl]
  · rw [map_mul, map_mul, map_inv, finComponent_localEmbed_of_ne (𝓞 K) K v u hw,
      finComponent_localEmbed_of_ne (𝓞 K) K v _ hw, mul_one, inv_mul_cancel]

theorem emb_mem_principalLevel_inf {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N)
    {u : GL (Fin 2) Kv} (hu : u ∈ integralSubgroup (𝓞v) Kv) :
    emb K v u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  have hNv : idealBound (𝓞 K) N v = 1 := idealBound_eq_one_of_not_dvd hN hv

  have h1 : emb K v u ∈ levelOne (𝓞 K) K N := by
    rw [mem_levelOne_iff, glFin_emb]
    exact localEmbed_mem_finiteLevelOne v hNv hu

  have h2 : emb K v u ∈ (levelOne (𝓞 K) K N).map (MulAut.conj (weyl (𝓞 K) K)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨(weyl (𝓞 K) K)⁻¹ * emb K v u * weyl (𝓞 K) K, ?_, ?_⟩
    · rw [mem_levelOne_iff, glFin_weyl_conj_emb]
      exact localEmbed_mem_finiteLevelOne v hNv
        (mul_mem (mul_mem (inv_mem weylInt_mem) hu) weylInt_mem)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

  have h3 : emb K v u ∈ finiteAdelicGL2Subgroup K := by
    rw [mem_finiteAdelicGL2Subgroup_iff]
    exact glArch_emb v u
  exact Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 K) K N).mpr ⟨h1, h2⟩, h3⟩

end Level

section Main

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem exists_ne_zero_locAt_mem {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (hφ0 : φ ≠ 0) :
    ∃ (k : GL (Fin 2) Kv) (g' : AdelicGL2 (𝓞 K) K),
      k ∈ integralSubgroup (𝓞v) Kv ∧ locAt K v g' = 1 ∧ φ (emb K v k * g') ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hφ0
  obtain ⟨b, k, hk, hb, hbk⟩ := LocalGL2.iwasawa_decomposition (𝓞v) Kv (locAt K v g₀)
  have hbB : b ∈ borelSubgroup Kv := (mem_borelSubgroup_iff _).mpr hb
  refine ⟨k, away v g₀, hk, locAt_away v g₀, ?_⟩
  have hg : g₀ = emb K v b * (emb K v k * away v g₀) := by
    rw [← mul_assoc, ← map_mul, ← hbk, emb_locAt_mul_away]
  have h := isInducedSection_emb_mul hφ v hbB (emb K v k * away v g₀)
  rw [← hg] at h
  intro h0
  rw [h0, mul_zero] at h
  exact hg₀ h

theorem emb_mul_emb_mul_eq (d k : GL (Fin 2) Kv) {g' : AdelicGL2 (𝓞 K) K} (hg' : locAt K v g' = 1) :
    emb K v d * (emb K v k * g') = (emb K v k * g') * emb K v (k⁻¹ * d * k) := by
  symm
  calc emb K v k * g' * emb K v (k⁻¹ * d * k)
      = emb K v k * (emb K v (k⁻¹ * d * k) * g') := by rw [mul_assoc, ← emb_mul_comm hg']
    _ = (emb K v k * emb K v (k⁻¹ * d * k)) * g' := (mul_assoc _ _ _).symm
    _ = emb K v (k * (k⁻¹ * d * k)) * g' := by rw [← map_mul]
    _ = emb K v (d * k) * g' := by
        congr 2
        group
    _ = emb K v d * (emb K v k * g') := by rw [map_mul, mul_assoc]

end Main

end PSUnram

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm PSUnram LocalGL2 AdelicDock
open scoped ComplexConjugate NNReal

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
      (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφ0 : φ ≠ 0)
      (_hφlev : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g)
      (v : HeightOneSpectrum (𝓞 K)) (_hv : ¬ v.asIdeal ∣ N),
    NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt ν v := by
  intro αm hαm μ ν s φ hφ hφ0 hφlev v hv

  have hN : N ≠ ⊥ := by
    rintro rfl
    exact hv (dvd_zero _)

  have hαI : ∀ x : (AdeleRing (𝓞 K) K)ˣ,
      ((αm x : ℝˣ) : ℝ) = ((distribHaarChar (AdeleRing (𝓞 K) K) x : ℝ≥0) : ℝ) := fun _ => rfl

  obtain ⟨k, g', hk, hg', hne⟩ := exists_ne_zero_locAt_mem v hφ hφ0

  have hmod : ∀ (t : (v.adicCompletion K)ˣ), (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ∀ r : ℂ, ((cpowChar αm hαm r (idl K v t) : ℂˣ) : ℂ) = 1 := by
    intro t ht hti r
    rw [cpowChar_apply_val, hαI, distribHaarChar_idl_of_valued_eq_one v t
      (valued_eq_one_of_mem_of_inv_mem v t ht hti), Complex.ofReal_one, Complex.one_cpow]

  have hlev : ∀ d : GL (Fin 2) (v.adicCompletion K),
      d ∈ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) →
      φ (emb K v d * (emb K v k * g')) = φ (emb K v k * g') := by
    intro d hd
    rw [emb_mul_emb_mul_eq v d k hg']
    exact hφlev _ _ (emb_mem_principalLevel_inf v hN hv (mul_mem (mul_mem (inv_mem hk) hd) hk))
  refine ⟨fun t ht hti => ?_, fun t ht hti => ?_⟩
  ·
    have h1 := isInducedSection_emb_mul hφ v (diagOne_mem_borel v t) (emb K v k * g')
    rw [borelDiagFst_diagOne, borelDiagSnd_diagOne, idl_one, map_one, Units.val_one, mul_one,
      etaFst_apply, Units.val_mul, hmod t ht hti, mul_one,
      hlev _ (diagOne_mem_integralSubgroup v t ht hti)] at h1
    have h2 : ((μ (idl K v t) : ℂˣ) : ℂ) = 1 := by
      have h3 := mul_right_cancel₀ hne (h1.symm.trans (one_mul _).symm)
      exact h3
    rw [localChar_eq_idl]
    exact Units.val_eq_one.mp h2
  ·
    have h1 := isInducedSection_emb_mul hφ v (oneDiag_mem_borel v t) (emb K v k * g')
    rw [borelDiagFst_oneDiag, borelDiagSnd_oneDiag, idl_one, map_one, Units.val_one, one_mul,
      etaSnd_apply, Units.val_mul, hmod t ht hti, mul_one,
      hlev _ (oneDiag_mem_integralSubgroup v t ht hti)] at h1
    have h2 : ((ν (idl K v t) : ℂˣ) : ℂ) = 1 := by
      have h3 := mul_right_cancel₀ hne (h1.symm.trans (one_mul _).symm)
      exact h3
    rw [localChar_eq_idl]
    exact Units.val_eq_one.mp h2

end S_AutomorphicForm_isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
end P2MW
export P2MW.S_AutomorphicForm_isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel (solution)
