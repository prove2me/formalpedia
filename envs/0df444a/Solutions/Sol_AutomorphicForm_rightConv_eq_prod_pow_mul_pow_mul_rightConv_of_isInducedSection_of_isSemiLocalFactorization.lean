-- Prove2me | solution 1 for AutomorphicForm.rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e207b181-c4f1-5df9-9a8c-9bfce766cfc8

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LocalGL2_iwasawa_decomposition
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm AdelicDock LocalGL2

namespace InducedHeckeWordSL

variable {K : Type} [Field K] [NumberField K]

def emb (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (v.adicCompletion K) →* AdelicGL2 (𝓞 K) K :=
  (finEmbed (𝓞 K) K).comp (localEmbed (𝓞 K) K v)

theorem emb_apply (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) :
    emb K v y = finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v y) := rfl

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

theorem localAt_def (v : HeightOneSpectrum (𝓞 K)) (h : AdelicGL2 (𝓞 K) K) :
    localAt K v h = finComponent (𝓞 K) K v (glFin (𝓞 K) K h) := rfl

theorem glArch_emb (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) :
    glArch (𝓞 K) K (emb K v y) = 1 := glArch_finEmbed _ _ _

theorem glFin_emb (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) :
    glFin (𝓞 K) K (emb K v y) = localEmbed (𝓞 K) K v y := glFin_finEmbed _ _ _

theorem localAt_emb_self (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (v.adicCompletion K)) :
    localAt K v (emb K v y) = y := by
  rw [localAt_def, glFin_emb, finComponent_localEmbed_self]

theorem localAt_emb_of_ne {v w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v)
    (y : GL (Fin 2) (v.adicCompletion K)) : localAt K w (emb K v y) = 1 := by
  rw [localAt_def, glFin_emb, finComponent_localEmbed_of_ne (𝓞 K) K v y hw]

theorem emb_mul_comm {v : HeightOneSpectrum (𝓞 K)} {h : AdelicGL2 (𝓞 K) K}
    (hv : localAt K v h = 1) (y : GL (Fin 2) (v.adicCompletion K)) :
    emb K v y * h = h * emb K v y := by
  rw [localAt_def] at hv
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
  (emb K v (localAt K v g))⁻¹ * g

theorem emb_localAt_mul_away (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) :
    emb K v (localAt K v g) * away v g = g :=
  mul_inv_cancel_left _ _

theorem localAt_away (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) :
    localAt K v (away v g) = 1 := by
  rw [away, map_mul, map_inv, localAt_emb_self, inv_mul_cancel]

theorem away_mul_emb_localAt (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) :
    away v g * emb K v (localAt K v g) = g := by
  rw [← emb_mul_comm (localAt_away v g), emb_localAt_mul_away]

theorem localAt_emb_mul_of_ne {v w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v)
    (y : GL (Fin 2) (v.adicCompletion K)) (h : AdelicGL2 (𝓞 K) K) :
    localAt K w (emb K v y * h) = localAt K w h := by
  rw [map_mul, localAt_emb_of_ne hw, one_mul]

theorem mem_localIntegralSet_of_mem_integralSubgroup {v : HeightOneSpectrum (𝓞 K)}
    {u : GL (Fin 2) (v.adicCompletion K)}
    (hu : u ∈ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    u ∈ localIntegralSet K v := by
  obtain ⟨y, rfl⟩ := hu
  refine (mem_localIntegralSet K v).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.GeneralLinearGroup.map_apply]
    exact SetLike.coe_mem _
  · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]
    exact SetLike.coe_mem _

theorem emb_mem_maximalCompactAway {SK : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ SK) {u : GL (Fin 2) (v.adicCompletion K)} (hu : u ∈ localIntegralSet K v) :
    emb K v u ∈ maximalCompactAway K SK := by
  rw [mem_maximalCompactAway_iff]
  refine ⟨?_, glArch_emb v u, fun w hw => ?_⟩
  · rw [mem_adelicMaximalCompact_iff]
    refine ⟨?_, fun w => ?_⟩
    · rw [glFin_emb, ← SetLike.mem_coe, ← unitFinSet_eq_finiteIntegralGL2]
      intro w
      by_cases hw : w = v
      · subst hw
        rw [finComponent_localEmbed_self]
        exact hu
      · rw [finComponent_localEmbed_of_ne (𝓞 K) K v u hw]
        exact one_mem_localIntegralSet K w
    · rw [glArch_emb, map_one]
      exact WindowedSiegel.isRowIsometry_one
  · have hwv : w ≠ v := fun h => hv (h ▸ hw)
    rw [glFin_emb, finComponent_localEmbed_of_ne (𝓞 K) K v u hwv]

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

section CosetSystem

variable {G : Type*} [Group G] {U : Subgroup G} {g₀ : G}

theorem cosetSum_eq_of_isHeckeCosetSystem {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    {reps₀ : ι₀ → G} {reps₁ : ι₁ → G}
    (h₀ : HeckeIntegralSeam.IsHeckeCosetSystem U g₀ reps₀) (h₁ : HeckeIntegralSeam.IsHeckeCosetSystem U g₀ reps₁)
    (F : G → ℂ) (hFU : ∀ y : G, ∀ u ∈ U, F (y * u) = F y) :
    ∑ i, F (reps₀ i) = ∑ j, F (reps₁ j) := by
  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (reps₀ i) : G ⧸ U) = QuotientGroup.mk (reps₁ j) :=
    fun i => h₁.covers (reps₀ i) (h₀.mem_doubleCoset i)
  choose e he using hcov
  have hinj : Function.Injective e := by
    intro i i' hii'
    apply h₀.mk_injective
    simp only
    rw [he i, he i', hii']
  have hsurj : Function.Surjective e := by
    intro j
    obtain ⟨i, hi⟩ := h₀.covers (reps₁ j) (h₁.mem_doubleCoset j)
    refine ⟨i, h₁.mk_injective ?_⟩
    simp only
    rw [← he i, hi]
  refine Fintype.sum_bijective e ⟨hinj, hsurj⟩ _ _ fun i => ?_
  have hu : (reps₀ i)⁻¹ * reps₁ (e i) ∈ U := QuotientGroup.eq.1 (he i)
  have eq : reps₁ (e i) = reps₀ i * ((reps₀ i)⁻¹ * reps₁ (e i)) := by group
  rw [eq, hFU _ _ hu]

theorem isHeckeCosetSystem_mul_left {ι : Type*} {reps : ι → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g₀ reps) {k : G} (hk : k ∈ U) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g₀ (fun i => k * reps i) := by
  constructor
  · intro i
    exact HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hk
  · intro x hx
    obtain ⟨i, hi⟩ := hsys.covers (k⁻¹ * x) (HeckePair.mul_mem_doubleCoset hx (U.inv_mem hk))
    have h : x⁻¹ * (k * reps i) ∈ U := by
      rw [show x⁻¹ * (k * reps i) = (k⁻¹ * x)⁻¹ * reps i by group]
      exact QuotientGroup.eq.mp hi
    exact ⟨i, QuotientGroup.eq.mpr h⟩
  · intro i j hij
    have h : (QuotientGroup.mk (k * reps i) : G ⧸ U) = QuotientGroup.mk (k * reps j) := hij
    have h' : (reps i)⁻¹ * reps j ∈ U := by
      rw [show (reps i)⁻¹ * reps j = (k * reps i)⁻¹ * (k * reps j) by group]
      exact QuotientGroup.eq.mp h
    exact hsys.mk_injective (QuotientGroup.eq.mpr h')

end CosetSystem

section Explicit

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

def explicitRep (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) : Option (𝓞 K ⧸ v.asIdeal) → GL (Fin 2) (Kv)
  | none => localRepInf ϖ hϖ0
  | some c => localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (𝓞v) (Quotient.out c))

theorem algebraMap_mem_maximalIdeal_iff (a : 𝓞 K) :
    algebraMap (𝓞 K) (𝓞v) a ∈ IsLocalRing.maximalIdeal (𝓞v) ↔ a ∈ v.asIdeal := by
  rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v]
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_lt_one_iff_mem v a

variable {v}

theorem sub_mem_maximalIdeal_of_mk_eq {a b : 𝓞 K}
    (h : (Ideal.Quotient.mk v.asIdeal a) = Ideal.Quotient.mk v.asIdeal b) :
    algebraMap (𝓞 K) (𝓞v) a - algebraMap (𝓞 K) (𝓞v) b ∈ IsLocalRing.maximalIdeal (𝓞v) := by
  rw [← map_sub, algebraMap_mem_maximalIdeal_iff]
  exact Ideal.Quotient.eq.1 h

theorem isHeckeCosetSystem_explicitRep (ϖ : 𝓞v) (hirr : Irreducible ϖ)
    (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) :
    HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0)
      (explicitRep v ϖ hϖ0) := by
  have hmax : IsLocalRing.maximalIdeal (𝓞v) = Ideal.span {ϖ} := hirr.maximalIdeal_eq
  constructor
  · rintro (_ | c)
    · exact HeckePair.mem_doubleCoset_iff.mpr ⟨weylInt (𝓞v) (Kv), weylInt_mem, weylInt (𝓞v) (Kv),
        weylInt_mem, rfl⟩
    · exact HeckePair.mem_doubleCoset_iff.mpr ⟨unipotentInt (Kv) _, unipotentInt_mem _, 1, one_mem _,
        by rw [mul_one]; rfl⟩
  · intro x hx
    obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have hxu : (QuotientGroup.mk (u * diagPi ϖ hϖ0 * u') : GL (Fin 2) (Kv) ⧸ integralSubgroup (𝓞v) (Kv)) =
        QuotientGroup.mk (u * diagPi ϖ hϖ0) := by
      rw [QuotientGroup.eq]
      rw [show (u * diagPi ϖ hϖ0 * u')⁻¹ * (u * diagPi ϖ hϖ0) = u'⁻¹ by group]
      exact inv_mem hu'
    rw [hxu]
    have hmem : u * diagPi ϖ hϖ0 ∈ heckeMulSet ϖ hϖ0 := (mem_heckeMulSet_iff ϖ hϖ0).mpr ⟨u, hu, rfl⟩
    rcases exists_rep_of_mem_heckeMulSet ϖ hϖ0 hirr hmem with ⟨b, hb⟩ | hinf
    ·
      obtain ⟨a, ha⟩ := NumberField.AdelicHaar.exists_valued_algebraMap_sub_lt_one (𝓞 K) K v b
      refine ⟨some (Ideal.Quotient.mk v.asIdeal a), ?_⟩
      show _ = QuotientGroup.mk (localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (𝓞v)
        (Quotient.out (Ideal.Quotient.mk v.asIdeal a))))
      rw [← hb]
      refine mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 ?_
      rw [← Ideal.mem_span_singleton, ← hmax]
      have h1 : algebraMap (𝓞 K) (𝓞v) (Quotient.out (Ideal.Quotient.mk v.asIdeal a)) -
          algebraMap (𝓞 K) (𝓞v) a ∈ IsLocalRing.maximalIdeal (𝓞v) :=
        sub_mem_maximalIdeal_of_mk_eq (Ideal.Quotient.mk_out _)
      have h2 : algebraMap (𝓞 K) (𝓞v) a - b ∈ IsLocalRing.maximalIdeal (𝓞v) := by
        rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v]
        simp at ha ⊢
        exact ha
      have := add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
    · exact ⟨none, hinf.symm⟩
  · rintro (_ | c) (_ | c') h
    · rfl
    · exact absurd h.symm (mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hirr.not_isUnit _)
    · exact absurd h (mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hirr.not_isUnit _)
    · have hd := dvd_sub_of_mk_localRepSome_eq ϖ hϖ0 h
      rw [← Ideal.mem_span_singleton, ← hmax, ← map_sub, algebraMap_mem_maximalIdeal_iff,
        ← Ideal.Quotient.eq, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at hd
      rw [hd]

theorem localRepSome_mem_borel (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) (β : 𝓞v) :
    localRepSome ϖ hϖ0 β ∈ borelSubgroup (Kv) := by
  rw [mem_borelSubgroup_iff, coe_localRepSome]
  rfl

theorem localRepInf_mem_borel (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) :
    localRepInf ϖ hϖ0 ∈ borelSubgroup (Kv) := by
  rw [mem_borelSubgroup_iff, coe_localRepInf]
  rfl

def piUnit (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) : (Kv)ˣ := Units.mk0 _ hϖ0

theorem borelDiagFst_localRepSome (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) (β : 𝓞v) :
    borelDiagFst (⟨localRepSome ϖ hϖ0 β, localRepSome_mem_borel ϖ hϖ0 β⟩ : ↥(borelSubgroup (Kv))) =
      piUnit ϖ hϖ0 := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show (localRepSome ϖ hϖ0 β : Matrix (Fin 2) (Fin 2) (Kv)) 0 0 = algebraMap (𝓞v) (Kv) ϖ
  rw [coe_localRepSome]
  rfl

theorem borelDiagSnd_localRepSome (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) (β : 𝓞v) :
    borelDiagSnd (⟨localRepSome ϖ hϖ0 β, localRepSome_mem_borel ϖ hϖ0 β⟩ : ↥(borelSubgroup (Kv))) = 1 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show (localRepSome ϖ hϖ0 β : Matrix (Fin 2) (Fin 2) (Kv)) 1 1 = 1
  rw [coe_localRepSome]
  rfl

theorem borelDiagFst_localRepInf (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) :
    borelDiagFst (⟨localRepInf ϖ hϖ0, localRepInf_mem_borel ϖ hϖ0⟩ : ↥(borelSubgroup (Kv))) = 1 := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) (Kv)) 0 0 = 1
  rw [coe_localRepInf]
  rfl

theorem borelDiagSnd_localRepInf (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) :
    borelDiagSnd (⟨localRepInf ϖ hϖ0, localRepInf_mem_borel ϖ hϖ0⟩ : ↥(borelSubgroup (Kv))) =
      piUnit ϖ hϖ0 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) (Kv)) 1 1 = algebraMap (𝓞v) (Kv) ϖ
  rw [coe_localRepInf]
  rfl

theorem card_quotient_eq_absNorm [Fintype (𝓞 K ⧸ v.asIdeal)] :
    Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem valued_eq_exp_neg_one_of_irreducible {ϖ : 𝓞v} (hirr : Irreducible ϖ) :
    Valued.v (ϖ : Kv) = WithZero.exp (-1 : ℤ) := by
  have hmax : IsLocalRing.maximalIdeal (𝓞v) = Ideal.span {ϖ} := hirr.maximalIdeal_eq

  have hlt : Valued.v (ϖ : Kv) < 1 := by
    rw [← NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v]
    exact (IsLocalRing.mem_maximalIdeal _).2 hirr.not_isUnit

  set π₀ : 𝓞v := ⟨(uniformizerUnit K v : Kv),
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [valued_uniformizerUnit]; exact le_of_lt (by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)))⟩ with hπ₀
  have hπ₀v : Valued.v (π₀ : Kv) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v
  have hπ₀mem : π₀ ∈ IsLocalRing.maximalIdeal (𝓞v) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v, hπ₀v, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 (by norm_num)
  rw [hmax, Ideal.mem_span_singleton'] at hπ₀mem
  obtain ⟨c, hc⟩ := hπ₀mem
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Kv) := by
    rw [← hπ₀v, ← hc]
    show Valued.v ((c : Kv) * (ϖ : Kv)) ≤ _
    rw [Valuation.map_mul]
    exact mul_le_of_le_one_left' c.2
  have hne : Valued.v (ϖ : Kv) ≠ 0 := by
    intro h0
    rw [h0] at hle
    exact WithZero.exp_ne_zero (le_antisymm hle zero_le')
  rw [← WithZero.exp_log hne] at hlt hle ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hle
  congr 1
  omega

theorem distribHaarChar_idl_of_valued_eq (t : (Kv)ˣ) (ht : Valued.v (t : Kv) = WithZero.exp (-1 : ℤ)) :
    ((distribHaarChar (AdeleRing (𝓞 K) K) (idl K v t) : NNReal) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm K (idl K v t)]
  have h1 : ∏ w : InfinitePlace K,
      ‖((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [idl_fst, show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  have h2 : ∏ᶠ u : HeightOneSpectrum (𝓞 K),
      ‖((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 u‖ = ‖(t : Kv)‖ := by
    rw [finprod_eq_single _ v fun u hu => by rw [idl_snd_of_ne v t hu, norm_one], idl_snd_self]
  rw [h1, one_mul, h2, NumberField.FinitePlace.norm_def, ht,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv,
    NNReal.coe_natCast]

theorem apply_idl_eq_of_isUnramifiedCharAt {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hχ : TateGlobal.IsUnramifiedCharAt χ v) {t t' : (Kv)ˣ}
    (h : Valued.v (t : Kv) = Valued.v (t' : Kv)) : χ (idl K v t) = χ (idl K v t') := by
  have ht0 : Valued.v (t : Kv) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  have hu : Valued.v ((t⁻¹ * t' : (Kv)ˣ) : Kv) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Valuation.map_mul, map_inv₀, ← h, inv_mul_cancel₀ ht0]
  have hu' : Valued.v (((t⁻¹ * t')⁻¹ : (Kv)ˣ) : Kv) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have key := hχ (t⁻¹ * t') ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le)
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu'.le)
  rw [localChar_eq_idl] at key
  calc χ (idl K v t) = χ (idl K v t) * χ (idl K v (t⁻¹ * t')) := by rw [key, mul_one]
    _ = χ (idl K v t') := by rw [← map_mul, idl, idl, idl, ← map_mul, ← map_mul, mul_inv_cancel_left]

theorem det_heckeGen : Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) = idl K v (uniformizerUnit K v) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![((idl K v (uniformizerUnit K v) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1]).det = _
  rw [Matrix.det_diagonal]
  simp

end Explicit

section Table

def chiGen (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)

def aEis (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
    (chiGen μ v * (HeckeEigensystem.cNorm v) ^ (-s) + chiGen ν v * (HeckeEigensystem.cNorm v) ^ s)

def cEis (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (HeckeEigensystem.cNorm v)⁻¹ * ((HeckeEigensystem.cNorm v) * chiGen μ v * chiGen ν v)

theorem cEis_eq (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    cEis μ ν v = chiGen μ v * chiGen ν v := by
  rw [cEis, mul_assoc, inv_mul_cancel_left₀ (HeckeEigensystem.cNorm_ne_zero v)]

theorem table_algebra (N : ℕ) (hN : N ≠ 0) (m n s : ℂ) :
    n * ((N : ℂ)⁻¹) ^ (-(s + 1 / 2)) + (N : ℂ) * (m * ((N : ℂ)⁻¹) ^ (s + 1 / 2)) =
      (N : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * (m * (N : ℂ) ^ (-s) + n * (N : ℂ) ^ s) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have harg : (N : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  have h12 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  rw [h12, Complex.inv_cpow _ _ harg, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, ← Complex.cpow_neg,
    neg_neg]
  have hhalf : (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (1 / 2 : ℂ) = N := by
    rw [← Complex.cpow_add _ _ hN']
    norm_num
  have h1 : (N : ℂ) ^ (s + 1 / 2) = (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ s := by
    rw [← Complex.cpow_add _ _ hN', add_comm]
  have h2 : (N : ℂ) * (N : ℂ) ^ (-(s + 1 / 2)) = (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-s) := by
    have : (N : ℂ) ^ (-(s + 1 / 2)) = (N : ℂ) ^ (-s) * (N : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [← Complex.cpow_add _ _ hN']
      congr 1
      ring
    have h3 : (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
      rw [← Complex.cpow_add _ _ hN', add_neg_cancel, Complex.cpow_zero]
    calc (N : ℂ) * (N : ℂ) ^ (-(s + 1 / 2))
        = ((N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (1 / 2 : ℂ)) * ((N : ℂ) ^ (-s) * (N : ℂ) ^ (-(1 / 2 : ℂ))) := by
          rw [hhalf, this]
      _ = (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-s) * ((N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-(1 / 2 : ℂ))) := by
          ring
      _ = (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-s) := by rw [h3, mul_one]
  calc n * (N : ℂ) ^ (s + 1 / 2) + (N : ℂ) * (m * (N : ℂ) ^ (-(s + 1 / 2)))
      = n * (N : ℂ) ^ (s + 1 / 2) + m * ((N : ℂ) * (N : ℂ) ^ (-(s + 1 / 2))) := by ring
    _ = _ := by rw [h1, h2]; ring

end Table

section Eigen

variable {SK : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem heckeEigen (hv : v ∉ SK) (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0)
    {n : ℕ} {r : Fin n → GL (Fin 2) (Kv)}
    (hcos : HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0) r)
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαv : ((α (idl K v (piUnit ϖ hϖ0)) : ℝˣ) : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹)
    {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hμ : TateGlobal.IsUnramifiedCharAt μ v) (hν : TateGlobal.IsUnramifiedCharAt ν v) (s : ℂ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφsph : ∀ k ∈ maximalCompactAway K SK, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g)
    (g : AdelicGL2 (𝓞 K) K) :
    ∑ i, φ (g * emb K v (r i)) = aEis μ ν s v * φ g := by
  classical
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _

  set gv := localAt K v g with hgv_def
  set g' := away v g with hg'_def
  have hg'v : localAt K v g' = 1 := localAt_away v g
  have hgd : g = emb K v gv * g' := (emb_localAt_mul_away v g).symm

  set F : GL (Fin 2) (Kv) → ℂ := fun y => φ (emb K v y * g') with hF_def
  have hFU : ∀ y : GL (Fin 2) (Kv), ∀ u ∈ integralSubgroup (𝓞v) (Kv), F (y * u) = F y := by
    intro y u hu
    simp only [hF_def]
    rw [map_mul, mul_assoc, emb_mul_comm hg'v u, ← mul_assoc,
      hφsph _ (emb_mem_maximalCompactAway hv (mem_localIntegralSet_of_mem_integralSubgroup hu))]

  have hsum : ∑ i, φ (g * emb K v (r i)) = ∑ i, F (gv * r i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hF_def]
    rw [hgd, mul_assoc, ← emb_mul_comm hg'v (r i), ← mul_assoc, ← map_mul]

  obtain ⟨b, k, hk, hb, hbk⟩ := LocalGL2.iwasawa_decomposition (𝓞v) (Kv) gv
  have hbB : b ∈ borelSubgroup (Kv) := (mem_borelSubgroup_iff _).mpr hb
  have hB := hφ (emb K v b) (emb_mem_adelicBorel v hbB)
  set cb : ℂ := ((etaFst μ α hα s (borelDiagFst (⟨emb K v b, emb_mem_adelicBorel v hbB⟩ :
      ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
    ((etaSnd ν α hα s (borelDiagSnd (⟨emb K v b, emb_mem_adelicBorel v hbB⟩ :
      ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) with hcb
  have hFb : ∀ y, F (b * y) = cb * F y := by
    intro y
    simp only [hF_def]
    rw [map_mul, mul_assoc, hB]

  have hstep1 : ∑ i, F (gv * r i) = cb * ∑ i, F (k * r i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbk, mul_assoc, hFb]
  have hstep2 : ∑ i, F (k * r i) = ∑ o, F (explicitRep v ϖ hϖ0 o) :=
    cosetSum_eq_of_isHeckeCosetSystem (isHeckeCosetSystem_mul_left hcos hk)
      (isHeckeCosetSystem_explicitRep ϖ hirr hϖ0) F hFU

  have hvalϖ : Valued.v ((piUnit ϖ hϖ0 : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) :=
    valued_eq_exp_neg_one_of_irreducible hirr
  have hval0 : Valued.v ((uniformizerUnit K v : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v
  have hμϖ : ((μ (idl K v (piUnit ϖ hϖ0)) : ℂˣ) : ℂ) = chiGen μ v := by
    rw [chiGen, det_heckeGen, apply_idl_eq_of_isUnramifiedCharAt hμ (hvalϖ.trans hval0.symm)]
  have hνϖ : ((ν (idl K v (piUnit ϖ hϖ0)) : ℂˣ) : ℂ) = chiGen ν v := by
    rw [chiGen, det_heckeGen, apply_idl_eq_of_isUnramifiedCharAt hν (hvalϖ.trans hval0.symm)]
  set N : ℕ := Ideal.absNorm v.asIdeal with hN_def
  have hN0 : N ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hαC : (((α (idl K v (piUnit ϖ hϖ0)) : ℝˣ) : ℝ) : ℂ) = ((N : ℂ))⁻¹ := by
    rw [hαv]; push_cast; rfl
  have hE1 : ((etaFst μ α hα s (idl K v (piUnit ϖ hϖ0)) : ℂˣ) : ℂ) =
      chiGen μ v * ((N : ℂ)⁻¹) ^ (s + 1 / 2) := by
    rw [etaFst_apply, Units.val_mul, cpowChar_apply_val, hμϖ, hαC]
  have hE2 : ((etaSnd ν α hα s (idl K v (piUnit ϖ hϖ0)) : ℂˣ) : ℂ) =
      chiGen ν v * ((N : ℂ)⁻¹) ^ (-(s + 1 / 2)) := by
    rw [etaSnd_apply, Units.val_mul, cpowChar_apply_val, hνϖ, hαC]
  have hF1 : F 1 = φ g' := by
    simp only [hF_def]
    rw [map_one, one_mul]
  have hsome : ∀ c : 𝓞 K ⧸ v.asIdeal, F (explicitRep v ϖ hϖ0 (some c)) =
      chiGen μ v * ((N : ℂ)⁻¹) ^ (s + 1 / 2) * φ g' := by
    intro c
    have h := isInducedSection_emb_mul hφ v (localRepSome_mem_borel ϖ hϖ0
      (algebraMap (𝓞 K) (𝓞v) (Quotient.out c))) g'
    rw [borelDiagFst_localRepSome, borelDiagSnd_localRepSome, idl_one, map_one, Units.val_one, mul_one,
      hE1] at h
    exact h
  have hnone : F (explicitRep v ϖ hϖ0 none) = chiGen ν v * ((N : ℂ)⁻¹) ^ (-(s + 1 / 2)) * φ g' := by
    have h := isInducedSection_emb_mul hφ v (localRepInf_mem_borel ϖ hϖ0) g'
    rw [borelDiagFst_localRepInf, borelDiagSnd_localRepInf, idl_one, map_one, Units.val_one, one_mul,
      hE2] at h
    exact h
  have hstep3 : ∑ o, F (explicitRep v ϖ hϖ0 o) = aEis μ ν s v * φ g' := by
    rw [Fintype.sum_option, hnone, Finset.sum_congr rfl fun c _ => hsome c, Finset.sum_const, Finset.card_univ,
      card_quotient_eq_absNorm, nsmul_eq_mul, ← hN_def]
    rw [aEis, HeckeEigensystem.cNorm, ← hN_def, ← table_algebra N hN0 (chiGen μ v) (chiGen ν v) s]
    ring

  have hFgv : F gv = cb * φ g' := by
    have : F gv = F (b * (1 * k)) := by rw [one_mul, hbk]
    rw [this, hFb, hFU 1 k hk, hF1]
  have hφg : φ g = F gv := by
    simp only [hF_def]
    rw [← hgd]
  rw [hsum, hstep1, hstep2, hstep3, hφg, hFgv]
  ring

theorem central (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0)
    (z : GL (Fin 2) (Kv))
    (hz : (z : Matrix (Fin 2) (Fin 2) (Kv)) = algebraMap (𝓞v) (Kv) ϖ • (1 : Matrix (Fin 2) (Fin 2) (Kv)))
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hμ : TateGlobal.IsUnramifiedCharAt μ v) (hν : TateGlobal.IsUnramifiedCharAt ν v) (s : ℂ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (g : AdelicGL2 (𝓞 K) K) :
    φ (g * emb K v z) = cEis μ ν v * φ g := by
  have hzB : z ∈ borelSubgroup (Kv) := by
    rw [mem_borelSubgroup_iff, hz, Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero]
  have hzFst : borelDiagFst (⟨z, hzB⟩ : ↥(borelSubgroup (Kv))) = piUnit ϖ hϖ0 := by
    apply Units.ext
    rw [borelDiagFst_apply_val]
    show (z : Matrix (Fin 2) (Fin 2) (Kv)) 0 0 = algebraMap (𝓞v) (Kv) ϖ
    rw [hz, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hzSnd : borelDiagSnd (⟨z, hzB⟩ : ↥(borelSubgroup (Kv))) = piUnit ϖ hϖ0 := by
    apply Units.ext
    rw [borelDiagSnd_apply_val]
    show (z : Matrix (Fin 2) (Fin 2) (Kv)) 1 1 = algebraMap (𝓞v) (Kv) ϖ
    rw [hz, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]

  have hcomm : g * emb K v z = emb K v z * g := by
    apply eq_of_glArch_eq_of_glFin_eq
    · simp only [map_mul, glArch_emb, one_mul, mul_one]
    · simp only [map_mul, glFin_emb]
      apply eq_of_forall_finComponent_eq
      intro w
      by_cases hw : w = v
      · subst hw
        simp only [map_mul, finComponent_localEmbed_self]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
      · simp only [map_mul, finComponent_localEmbed_of_ne (𝓞 K) K v z hw, one_mul, mul_one]
  have hvalϖ : Valued.v ((piUnit ϖ hϖ0 : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) :=
    valued_eq_exp_neg_one_of_irreducible hirr
  have hval0 : Valued.v ((uniformizerUnit K v : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v
  rw [hcomm, isInducedSection_emb_mul hφ v hzB g, hzFst, hzSnd, ← Units.val_mul, etaFst_mul_etaSnd,
    Units.val_mul, cEis_eq, chiGen, chiGen, det_heckeGen,
    apply_idl_eq_of_isUnramifiedCharAt hμ (hvalϖ.trans hval0.symm),
    apply_idl_eq_of_isUnramifiedCharAt hν (hvalϖ.trans hval0.symm)]

theorem word (hv : v ∉ SK) (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0)
    {n : ℕ} {r : Fin n → GL (Fin 2) (Kv)}
    (hcos : HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0) r)
    (z : GL (Fin 2) (Kv))
    (hz : (z : Matrix (Fin 2) (Fin 2) (Kv)) = algebraMap (𝓞v) (Kv) ϖ • (1 : Matrix (Fin 2) (Fin 2) (Kv)))
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαv : ((α (idl K v (piUnit ϖ hϖ0)) : ℝˣ) : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹)
    {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hμ : TateGlobal.IsUnramifiedCharAt μ v) (hν : TateGlobal.IsUnramifiedCharAt ν v) (s : ℂ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφsph : ∀ k ∈ maximalCompactAway K SK, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g)
    (k j : ℕ) (g : AdelicGL2 (𝓞 K) K) :
    ∑ ι : Fin k → Fin n, φ (g * emb K v ((List.ofFn fun m => r (ι m)).prod * z ^ j)) =
      aEis μ ν s v ^ k * cEis μ ν v ^ j * φ g := by
  have hzj : ∀ (j : ℕ) (g : AdelicGL2 (𝓞 K) K), φ (g * emb K v (z ^ j)) = cEis μ ν v ^ j * φ g := by
    intro j
    induction j with
    | zero => intro g; rw [pow_zero, map_one, mul_one, pow_zero, one_mul]
    | succ j ih =>
      intro g
      rw [pow_succ, map_mul, ← mul_assoc, central ϖ hirr hϖ0 z hz α hα hμ hν s hφ, ih, pow_succ]
      ring
  induction k generalizing g with
  | zero =>
    rw [Fintype.sum_unique, List.ofFn_zero, List.prod_nil, one_mul, hzj, pow_zero, one_mul]
  | succ k ih =>
    have hcons : ∀ p : Fin n × (Fin k → Fin n),
        (List.ofFn fun m => r ((Fin.consEquiv fun _ => Fin n) p m)).prod =
          r p.1 * (List.ofFn fun m => r (p.2 m)).prod := by
      intro p
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    have hin : ∀ i : Fin n, ∑ ι' : Fin k → Fin n,
        φ (g * emb K v ((List.ofFn fun m => r ((Fin.consEquiv fun _ => Fin n) (i, ι') m)).prod * z ^ j)) =
          aEis μ ν s v ^ k * cEis μ ν v ^ j * φ (g * emb K v (r i)) := by
      intro i
      rw [← ih (g * emb K v (r i))]
      refine Finset.sum_congr rfl fun ι' _ => ?_
      rw [hcons, mul_assoc (r i), map_mul, ← mul_assoc]
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ => Fin n), Fintype.sum_prod_type,
      Finset.sum_congr rfl fun i _ => hin i, ← Finset.mul_sum,
      heckeEigen hv ϖ hirr hϖ0 hcos α hα hαv hμ hν s hφ hφsph g, pow_succ]
    ring

end Eigen

section Conv

attribute [local instance] NumberField.AdelicHaar.glBorel

def transSum (v : HeightOneSpectrum (𝓞 K)) {J : Type} [Fintype J] (w : J → GL (Fin 2) (v.adicCompletion K))
    (F : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => ∑ j, F ((emb K v (w j))⁻¹ * y)

theorem transSum_apply (v : HeightOneSpectrum (𝓞 K)) {J : Type} [Fintype J] (w : J → GL (Fin 2) (v.adicCompletion K))
    (F : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) :
    transSum v w F y = ∑ j, F ((emb K v (w j))⁻¹ * y) := rfl

theorem continuous_transSum (v : HeightOneSpectrum (𝓞 K)) {J : Type} [Fintype J]
    (w : J → GL (Fin 2) (v.adicCompletion K)) {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : Continuous F) :
    Continuous (transSum v w F) :=
  continuous_finsetSum _ fun j _ => hF.comp (continuous_const_mul _)

theorem hasCompactSupport_transSum (v : HeightOneSpectrum (𝓞 K)) {J : Type} [Fintype J]
    (w : J → GL (Fin 2) (v.adicCompletion K)) {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : HasCompactSupport F) :
    HasCompactSupport (transSum v w F) := by
  have h : transSum v w F = ∑ j, fun y => F ((emb K v (w j))⁻¹ * y) := by
    funext y
    rw [transSum_apply, Finset.sum_apply]
  rw [h]
  exact HasCompactSupport.finset_sum fun j _ => hF.comp_homeomorph (Homeomorph.mulLeft ((emb K v (w j))⁻¹))

theorem rightConv_transSum {SK : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ SK) {J : Type} [Fintype J] (w : J → GL (Fin 2) (v.adicCompletion K)) (lam : ℂ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφc : Continuous φ)
    (hφsph : ∀ k ∈ maximalCompactAway K SK, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g)
    (heig : ∀ g : AdelicGL2 (𝓞 K) K, ∑ j, φ (g * emb K v (w j)) = lam * φ g)
    {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFv : ∀ y, F y ≠ 0 → localAt K v y ∈ localIntegralSet K v) (x : AdelicGL2 (𝓞 K) K) :
    rightConv K φ (transSum v w F) x = lam * rightConv K φ F x := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  have hpt : ∀ y, ∑ j, φ (x * emb K v (w j) * y) * F y = lam * (φ (x * y) * F y) := by
    intro y
    by_cases hy : F y = 0
    · simp [hy]
    · have hyv := hFv y hy
      have hy'v := localAt_away v y
      have hk : emb K v (localAt K v y) ∈ maximalCompactAway K SK := emb_mem_maximalCompactAway hv hyv
      rw [← Finset.sum_mul, ← mul_assoc]
      congr 1
      calc ∑ j, φ (x * emb K v (w j) * y) = ∑ j, φ (x * away v y * emb K v (w j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            calc φ (x * emb K v (w j) * y)
                = φ (x * emb K v (w j) * (away v y * emb K v (localAt K v y))) := by rw [away_mul_emb_localAt]
              _ = φ (x * emb K v (w j) * away v y) := by rw [← mul_assoc, hφsph _ hk]
              _ = φ (x * away v y * emb K v (w j)) := by rw [mul_assoc x, emb_mul_comm hy'v, ← mul_assoc]
        _ = lam * φ (x * away v y) := heig _
        _ = lam * φ (x * away v y * emb K v (localAt K v y)) := by rw [hφsph _ hk]
        _ = lam * φ (x * y) := by rw [mul_assoc, away_mul_emb_localAt]

  have hint1 : ∀ j, Integrable (fun y => φ (x * y) * F ((emb K v (w j))⁻¹ * y))
      (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro j
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hφc.comp (continuous_const_mul x)).mul (hF.comp (continuous_const_mul _))
    · exact (hFc.comp_homeomorph (Homeomorph.mulLeft ((emb K v (w j))⁻¹))).mul_left
  have hint2 : ∀ j, Integrable (fun y => φ (x * emb K v (w j) * y) * F y) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro j
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hφc.comp (continuous_const_mul _)).mul hF
    · exact hFc.mul_left
  calc rightConv K φ (transSum v w F) x
      = ∫ y, ∑ j, φ (x * y) * F ((emb K v (w j))⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [rightConv_apply]
        show ∫ y, φ (x * y) * transSum v w F y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = _
        congr 1
        funext y
        rw [transSum_apply, Finset.mul_sum]
    _ = ∑ j, ∫ y, φ (x * y) * F ((emb K v (w j))⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        integral_finsetSum _ fun j _ => hint1 j
    _ = ∑ j, rightConv K φ (fun y => F ((emb K v (w j))⁻¹ * y)) x := rfl
    _ = ∑ j, rightConv K φ F (x * emb K v (w j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
    _ = ∑ j, ∫ y, φ (x * emb K v (w j) * y) * F y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := rfl
    _ = ∫ y, ∑ j, φ (x * emb K v (w j) * y) * F y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        (integral_finsetSum _ fun j _ => hint2 j).symm
    _ = ∫ y, lam * (φ (x * y) * F y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1
        funext y
        exact hpt y
    _ = lam * rightConv K φ F x := by
        rw [integral_const_mul]
        rfl

def iter {J : HeightOneSpectrum (𝓞 K) → Type} [∀ v, Fintype (J v)]
    (w : ∀ v : HeightOneSpectrum (𝓞 K), J v → GL (Fin 2) (v.adicCompletion K)) :
    List (HeightOneSpectrum (𝓞 K)) → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ)
  | [], F => F
  | a :: l, F => transSum a (w a) (iter w l F)

variable {J : HeightOneSpectrum (𝓞 K) → Type} [∀ v, Fintype (J v)]
  (w : ∀ v : HeightOneSpectrum (𝓞 K), J v → GL (Fin 2) (v.adicCompletion K))

theorem iter_nil (F : AdelicGL2 (𝓞 K) K → ℂ) : iter w [] F = F := rfl

theorem iter_cons (a : HeightOneSpectrum (𝓞 K)) (l : List (HeightOneSpectrum (𝓞 K)))
    (F : AdelicGL2 (𝓞 K) K → ℂ) : iter w (a :: l) F = transSum a (w a) (iter w l F) := rfl

theorem continuous_iter {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : Continuous F) :
    ∀ l : List (HeightOneSpectrum (𝓞 K)), Continuous (iter w l F)
  | [] => hF
  | a :: l => by rw [iter_cons]; exact continuous_transSum a (w a) (continuous_iter hF l)

theorem hasCompactSupport_iter {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : HasCompactSupport F) :
    ∀ l : List (HeightOneSpectrum (𝓞 K)), HasCompactSupport (iter w l F)
  | [] => hF
  | a :: l => by rw [iter_cons]; exact hasCompactSupport_transSum a (w a) (hasCompactSupport_iter hF l)

theorem iter_local {F : AdelicGL2 (𝓞 K) K → ℂ} (a : HeightOneSpectrum (𝓞 K))
    (hFa : ∀ y, F y ≠ 0 → localAt K a y ∈ localIntegralSet K a) :
    ∀ l : List (HeightOneSpectrum (𝓞 K)), a ∉ l → ∀ y, iter w l F y ≠ 0 → localAt K a y ∈ localIntegralSet K a
  | [], _ => hFa
  | b :: l, hab => by
    intro y hy
    rw [List.mem_cons, not_or] at hab
    rw [iter_cons, transSum_apply] at hy
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have := iter_local a hFa l hab.2 _ hj
    rwa [map_mul, map_inv, localAt_emb_of_ne hab.1, inv_one, one_mul] at this

theorem rightConv_iter {SK T' : Finset (HeightOneSpectrum (𝓞 K))} (hT' : ∀ a ∈ T', a ∉ SK)
    (lam : HeightOneSpectrum (𝓞 K) → ℂ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφc : Continuous φ)
    (hφsph : ∀ k ∈ maximalCompactAway K SK, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g)
    (heig : ∀ a ∈ T', ∀ g : AdelicGL2 (𝓞 K) K, ∑ j, φ (g * emb K a (w a j)) = lam a * φ g)
    {F₀ : AdelicGL2 (𝓞 K) K → ℂ} (hF₀ : Continuous F₀) (hF₀c : HasCompactSupport F₀)
    (hloc : ∀ a ∈ T', ∀ y, F₀ y ≠ 0 → localAt K a y ∈ localIntegralSet K a) :
    ∀ l : List (HeightOneSpectrum (𝓞 K)), l.Nodup → (∀ a ∈ l, a ∈ T') → ∀ x,
      rightConv K φ (iter w l F₀) x = (l.map lam).prod * rightConv K φ F₀ x
  | [], _, _ => fun x => by rw [iter_nil, List.map_nil, List.prod_nil, one_mul]
  | a :: l, hnd, hsub => by
    intro x
    rw [List.nodup_cons] at hnd
    have haT : a ∈ T' := hsub a List.mem_cons_self
    have hsub' : ∀ b ∈ l, b ∈ T' := fun b hb => hsub b (List.mem_cons_of_mem a hb)
    rw [iter_cons, rightConv_transSum (hT' a haT) (w a) (lam a) hφc hφsph (heig a haT)
      (continuous_iter w hF₀ l) (hasCompactSupport_iter w hF₀c l) (iter_local w a (hloc a haT) l hnd.1) x,
      rightConv_iter hT' lam hφc hφsph heig hF₀ hF₀c hloc l hnd.2 hsub' x, List.map_cons, List.prod_cons,
      mul_assoc]

def iterSL {F₀ : Type} [Field F₀] [NumberField F₀] [Algebra F₀ K]
    (ws : ∀ a : HeightOneSpectrum (𝓞 F₀), a.Extension (𝓞 K))
    {J : HeightOneSpectrum (𝓞 F₀) → Type} [∀ a, Fintype (J a)]
    (w : ∀ a : HeightOneSpectrum (𝓞 F₀), J a → GL (Fin 2) ((ws a).1.adicCompletion K)) :
    List (HeightOneSpectrum (𝓞 F₀)) → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ)
  | [], F => F
  | a :: l, F => transSum (ws a).1 (w a) (iterSL ws w l F)

section IterSL

variable {F₀ : Type} [Field F₀] [NumberField F₀] [Algebra F₀ K]
  (ws : ∀ a : HeightOneSpectrum (𝓞 F₀), a.Extension (𝓞 K))
  {J : HeightOneSpectrum (𝓞 F₀) → Type} [∀ a, Fintype (J a)]
  (w : ∀ a : HeightOneSpectrum (𝓞 F₀), J a → GL (Fin 2) ((ws a).1.adicCompletion K))

theorem iterSL_nil (F : AdelicGL2 (𝓞 K) K → ℂ) : iterSL ws w [] F = F := rfl

theorem iterSL_cons (a : HeightOneSpectrum (𝓞 F₀)) (l : List (HeightOneSpectrum (𝓞 F₀)))
    (F : AdelicGL2 (𝓞 K) K → ℂ) : iterSL ws w (a :: l) F = transSum (ws a).1 (w a) (iterSL ws w l F) := rfl

theorem continuous_iterSL {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : Continuous F) :
    ∀ l : List (HeightOneSpectrum (𝓞 F₀)), Continuous (iterSL ws w l F)
  | [] => hF
  | a :: l => by rw [iterSL_cons]; exact continuous_transSum _ (w a) (continuous_iterSL hF l)

theorem hasCompactSupport_iterSL {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : HasCompactSupport F) :
    ∀ l : List (HeightOneSpectrum (𝓞 F₀)), HasCompactSupport (iterSL ws w l F)
  | [] => hF
  | a :: l => by rw [iterSL_cons]; exact hasCompactSupport_transSum _ (w a) (hasCompactSupport_iterSL hF l)

theorem ws_ne_of_ne {a b : HeightOneSpectrum (𝓞 F₀)} (hab : b ≠ a) : (ws b).1 ≠ (ws a).1 := by
  intro h
  apply hab
  have hb : HeightOneSpectrum.under (𝓞 F₀) (ws b).1 = b := (ws b).2
  have ha : HeightOneSpectrum.under (𝓞 F₀) (ws a).1 = a := (ws a).2
  rw [h] at hb
  exact hb.symm.trans ha

theorem iterSL_local {F : AdelicGL2 (𝓞 K) K → ℂ} (a : HeightOneSpectrum (𝓞 F₀))
    (hFa : ∀ y, F y ≠ 0 → localAt K (ws a).1 y ∈ localIntegralSet K (ws a).1) :
    ∀ l : List (HeightOneSpectrum (𝓞 F₀)), a ∉ l → ∀ y, iterSL ws w l F y ≠ 0 →
      localAt K (ws a).1 y ∈ localIntegralSet K (ws a).1
  | [], _ => hFa
  | b :: l, hab => by
    intro y hy
    rw [List.mem_cons, not_or] at hab
    rw [iterSL_cons, transSum_apply] at hy
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have := iterSL_local a hFa l hab.2 _ hj
    have hne : (ws a).1 ≠ (ws b).1 := ws_ne_of_ne ws hab.1
    rwa [map_mul, map_inv, localAt_emb_of_ne hne, inv_one, one_mul] at this

theorem rightConv_iterSL {SK : Finset (HeightOneSpectrum (𝓞 K))} {T' : Finset (HeightOneSpectrum (𝓞 F₀))}
    (hT' : ∀ a ∈ T', (ws a).1 ∉ SK)
    (lam : HeightOneSpectrum (𝓞 F₀) → ℂ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφc : Continuous φ)
    (hφsph : ∀ k ∈ maximalCompactAway K SK, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g)
    (heig : ∀ a ∈ T', ∀ g : AdelicGL2 (𝓞 K) K, ∑ j, φ (g * emb K (ws a).1 (w a j)) = lam a * φ g)
    {G₀ : AdelicGL2 (𝓞 K) K → ℂ} (hG₀ : Continuous G₀) (hG₀c : HasCompactSupport G₀)
    (hloc : ∀ a ∈ T', ∀ y, G₀ y ≠ 0 → localAt K (ws a).1 y ∈ localIntegralSet K (ws a).1) :
    ∀ l : List (HeightOneSpectrum (𝓞 F₀)), l.Nodup → (∀ a ∈ l, a ∈ T') → ∀ x,
      rightConv K φ (iterSL ws w l G₀) x = (l.map lam).prod * rightConv K φ G₀ x
  | [], _, _ => fun x => by rw [iterSL_nil, List.map_nil, List.prod_nil, one_mul]
  | a :: l, hnd, hsub => by
    intro x
    rw [List.nodup_cons] at hnd
    have haT : a ∈ T' := hsub a List.mem_cons_self
    have hsub' : ∀ b ∈ l, b ∈ T' := fun b hb => hsub b (List.mem_cons_of_mem a hb)
    rw [iterSL_cons, rightConv_transSum (hT' a haT) (w a) (lam a) hφc hφsph (heig a haT)
      (continuous_iterSL ws w hG₀ l) (hasCompactSupport_iterSL ws w hG₀c l)
      (iterSL_local ws w a (hloc a haT) l hnd.1) x,
      rightConv_iterSL hT' lam hφc hφsph heig hG₀ hG₀c hloc l hnd.2 hsub' x, List.map_cons, List.prod_cons,
      mul_assoc]

end IterSL

end Conv

end InducedHeckeWordSL

namespace InducedHeckeWordSL

open scoped TensorProduct TensorProduct.RightActions

section SemiLocal

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem semiLocalHomeomorph_semiLocalEval (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L)
    (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v (semiLocalEval K L v a) w = a w.1 := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a)) w = a w.1
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem semiLocalEval_mem_semiLocalIntegers_iff (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v a ∈ semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), a w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  refine forall_congr' fun w => ?_
  rw [semiLocalHomeomorph_semiLocalEval, SetLike.mem_coe]

theorem semiLocalComponent_apply (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (i j : Fin 2) :
    (semiLocalComponent K L v h : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
      semiLocalEval K L v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) :=
  rfl

theorem semiLocalComponent_mem_iff (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v ↔
      ∀ w : v.Extension (𝓞 L), finComponent (𝓞 L) L w.1 h ∈ localIntegralSet L w.1 := by
  rw [semiLocalIntegralSet, mem_integralUnitsSet]
  simp only [← map_inv, semiLocalComponent_apply, semiLocalEval_mem_semiLocalIntegers_iff,
    mem_localIntegralSet, finComponent_apply]
  constructor
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w⟩
  · intro hw
    exact ⟨fun i j w => (hw w).1 i j, fun i j w => (hw w).2 i j⟩

theorem semiLocalComponent_localEmbed_of_forall_ne (v' : HeightOneSpectrum (𝓞 K)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : ∀ w' : v'.Extension (𝓞 L), w'.1 ≠ w) (y : GL (Fin 2) (w.adicCompletion L)) :
    semiLocalComponent K L v' (localEmbed (𝓞 L) L w y) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  apply (semiLocalHomeomorph K L v').injective
  funext w'
  rw [semiLocalComponent_apply, semiLocalHomeomorph_semiLocalEval, coe_localEmbed,
    localMat_apply_of_ne (𝓞 L) L w _ i j (hw w'), Units.val_one]
  show (1 : Matrix (Fin 2) (Fin 2) (w'.1.adicCompletion L)) i j =
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v'
      ((1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v'.adicCompletion K)) i j) w'
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
    rfl

theorem semiLocalComponent_localEmbed_inv_mul_of_ne {v v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v)
    (w : v.Extension (𝓞 L)) (x : GL (Fin 2) (w.1.adicCompletion L)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v' ((localEmbed (𝓞 L) L w.1 x)⁻¹ * h) = semiLocalComponent K L v' h := by
  have hw : ∀ w' : v'.Extension (𝓞 L), w'.1 ≠ w.1 := by
    intro w' heq
    apply hv
    have h1 : HeightOneSpectrum.under (𝓞 K) w'.1 = v' := w'.2
    have h2 : HeightOneSpectrum.under (𝓞 K) w.1 = v := w.2
    rw [heq] at h1
    exact h1.symm.trans h2
  rw [map_mul, map_inv, semiLocalComponent_localEmbed_of_forall_ne v' hw, inv_one, one_mul]

theorem semiLocalComponent_localEmbed_inv_mul_self {v : HeightOneSpectrum (𝓞 K)}
    (w : v.Extension (𝓞 L)) (x : GL (Fin 2) (w.1.adicCompletion L)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v ((localEmbed (𝓞 L) L w.1 x)⁻¹ * h) =
      (semiLocalComponent K L v (localEmbed (𝓞 L) L w.1 x))⁻¹ * semiLocalComponent K L v h := by
  rw [map_mul, map_inv]

end SemiLocal

section Tracking

attribute [local instance] NumberField.AdelicHaar.glBorel

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def IsFormulaSL (S : Finset (HeightOneSpectrum (𝓞 K))) (F : AdelicGL2 (𝓞 L) L → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) : Prop :=
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
    (∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) →
      φf h = ∏ v ∈ S, gS v (semiLocalComponent K L v h)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
    (∃ v ∉ S, semiLocalComponent K L v h ∉ semiLocalIntegralSet K L v) → φf h = 0) ∧
  ∀ g, F g = φa (glArch (𝓞 L) L g) * φf (glFin (𝓞 L) L g)

theorem isFormulaSL_of_isSemiLocalFactorization {S : Finset (HeightOneSpectrum (𝓞 K))}
    {F : AdelicGL2 (𝓞 L) L → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : IsSemiLocalFactorization K L S F φa φf gS) : IsFormulaSL S F φa φf gS :=
  ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem eq_of_isFormulaSL {S : Finset (HeightOneSpectrum (𝓞 K))} {F F' : AdelicGL2 (𝓞 L) L → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {φf φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {gS gS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : IsFormulaSL S F φa φf gS) (h' : IsFormulaSL S F' φa φf' gS') (heq : ∀ v ∈ S, gS v = gS' v) :
    F = F' := by
  funext g
  rw [h.2.2 g, h'.2.2 g]
  congr 1
  by_cases hint : ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v
  · rw [h.1 _ hint, h'.1 _ hint]
    exact Finset.prod_congr rfl fun v hv => by rw [heq v hv]
  · push Not at hint
    rw [h.2.1 _ hint, h'.2.1 _ hint]

theorem isFormulaSL_transSum [DecidableEq (HeightOneSpectrum (𝓞 K))] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {F : AdelicGL2 (𝓞 L) L → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hF : IsFormulaSL S F φa φf gS) {a : HeightOneSpectrum (𝓞 K)} (ha : a ∈ S) (wa : a.Extension (𝓞 L))
    {Ja : Type} [Fintype Ja] (xa : Ja → GL (Fin 2) (wa.1.adicCompletion L)) :
    IsFormulaSL S (transSum wa.1 xa F) φa (fun h => ∑ j, φf ((localEmbed (𝓞 L) L wa.1 (xa j))⁻¹ * h))
      (Function.update gS a
        (fun x => ∑ j, gS a ((semiLocalComponent K L a (localEmbed (𝓞 L) L wa.1 (xa j)))⁻¹ * x))) := by
  refine ⟨fun h hint => ?_, fun h hbad => ?_, fun g => ?_⟩
  ·
    have hint' : ∀ j, ∀ v ∉ S,
        semiLocalComponent K L v ((localEmbed (𝓞 L) L wa.1 (xa j))⁻¹ * h) ∈ semiLocalIntegralSet K L v := by
      intro j v hv
      have hva : v ≠ a := fun e => hv (e ▸ ha)
      rw [semiLocalComponent_localEmbed_inv_mul_of_ne hva]
      exact hint v hv
    have hR : ∏ v ∈ S, Function.update gS a
          (fun x => ∑ j, gS a ((semiLocalComponent K L a (localEmbed (𝓞 L) L wa.1 (xa j)))⁻¹ * x)) v
          (semiLocalComponent K L v h) =
        (∑ j, gS a ((semiLocalComponent K L a (localEmbed (𝓞 L) L wa.1 (xa j)))⁻¹ * semiLocalComponent K L a h)) *
          ∏ v ∈ S.erase a, gS v (semiLocalComponent K L v h) := by
      rw [← Finset.mul_prod_erase S _ ha, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
    rw [hR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF.1 _ (hint' j), ← Finset.mul_prod_erase S _ ha, semiLocalComponent_localEmbed_inv_mul_self]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [semiLocalComponent_localEmbed_inv_mul_of_ne (Finset.ne_of_mem_erase hv)]
  ·
    obtain ⟨v, hv, hbad⟩ := hbad
    have hva : v ≠ a := fun e => hv (e ▸ ha)
    refine Finset.sum_eq_zero fun j _ => hF.2.1 _ ⟨v, hv, ?_⟩
    rwa [semiLocalComponent_localEmbed_inv_mul_of_ne hva]
  ·
    rw [transSum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF.2.2, map_mul, map_inv, glArch_emb, inv_one, one_mul, map_mul, map_inv, glFin_emb]

variable (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
  {J : HeightOneSpectrum (𝓞 K) → Type} [∀ v, Fintype (J v)]
  (w : ∀ v : HeightOneSpectrum (𝓞 K), J v → GL (Fin 2) ((ws v).1.adicCompletion L))

def gIterSL [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (l : List (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ :=
  if v ∈ l then fun x => ∑ j, gS v ((semiLocalComponent K L v (localEmbed (𝓞 L) L (ws v).1 (w v j)))⁻¹ * x)
  else gS v

theorem exists_isFormulaSL_iterSL [DecidableEq (HeightOneSpectrum (𝓞 K))] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {F₀ : AdelicGL2 (𝓞 L) L → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {φf₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h₀ : IsFormulaSL S F₀ φa φf₀ gS) :
    ∀ l : List (HeightOneSpectrum (𝓞 K)), l.Nodup → (∀ a ∈ l, a ∈ S) →
      ∃ φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ, IsFormulaSL S (iterSL ws w l F₀) φa φf (gIterSL ws w gS l)
  | [], _, _ => ⟨φf₀, by
      have : gIterSL ws w gS [] = gS := by
        funext v
        simp [gIterSL]
      rw [iterSL_nil, this]
      exact h₀⟩
  | a :: l, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have haS : a ∈ S := hsub a List.mem_cons_self
    obtain ⟨φf, hφf⟩ := exists_isFormulaSL_iterSL h₀ l hnd.2 fun b hb => hsub b (List.mem_cons_of_mem a hb)
    have key := isFormulaSL_transSum hφf haS (ws a) (w a)
    have heq : Function.update (gIterSL ws w gS l) a
        (fun x => ∑ j, gIterSL ws w gS l a
          ((semiLocalComponent K L a (localEmbed (𝓞 L) L (ws a).1 (w a j)))⁻¹ * x)) =
        gIterSL ws w gS (a :: l) := by
      funext v
      by_cases hva : v = a
      · subst hva
        rw [Function.update_self]
        simp [gIterSL, hnd.1]
      · rw [Function.update_of_ne hva]
        simp [gIterSL, hva]
    rw [heq] at key
    exact ⟨_, key⟩

end Tracking

end InducedHeckeWordSL

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm AdelicDock LocalGL2
open scoped TensorProduct

open InducedHeckeWordSL in
attribute [local instance] NumberField.AdelicHaar.glBorel in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTd : Disjoint T S)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hTSL : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
    (hirr : ∀ v ∈ T, Irreducible (ϖs v))
    (hϖs0 : ∀ v ∈ T,
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hcos : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfact : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))
    (φ₀ : AdelicGL2 (𝓞 L) L → ℂ) (hφ₀ : Continuous φ₀) (hφ₀c : HasCompactSupport φ₀)
    (φf₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfact₀ : IsSemiLocalFactorization K L (S ∪ T) φ₀ φa φf₀
      (fun v => if v ∈ T then (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) else φS v)) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμν : ∀ v ∈ T, NumberField.TateGlobal.IsUnramifiedCharAt μ (ws v).1 ∧
        NumberField.TateGlobal.IsUnramifiedCharAt ν (ws v).1)
      (s : ℂ) (ψ : AdelicGL2 (𝓞 L) L → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 L) L
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) ψ)
      (_hψc : Continuous ψ)
      (_hψsph : ∀ k ∈ AutomorphicForm.maximalCompactAway L SL, ∀ g : AdelicGL2 (𝓞 L) L, ψ (g * k) = ψ g)
      (x : AdelicGL2 (𝓞 L) L),
    AutomorphicForm.rightConv L ψ φ x =
      (∏ v ∈ T,
        ((HeckeEigensystem.cNorm (ws v).1) ^ ((1 / 2 : ℝ) : ℂ) *
            (((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ (-s) +
              ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ s)) ^ ks v *
          ((HeckeEigensystem.cNorm (ws v).1)⁻¹ *
            ((HeckeEigensystem.cNorm (ws v).1) *
              ((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
              ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ))) ^ js v) *
        AutomorphicForm.rightConv L ψ φ₀ x := by
  intro αm hαm μ ν hμν s ψ hψ hψc hψsph x

  let J : HeightOneSpectrum (𝓞 K) → Type := fun v => Fin (ks v) → Fin (ns v)
  let w : ∀ v : HeightOneSpectrum (𝓞 K), J v → GL (Fin 2) ((ws v).1.adicCompletion L) :=
    fun v ι => (List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v

  let gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ :=
    fun v => if v ∈ T then (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) else φS v
  have h₀ : IsFormulaSL (S ∪ T) φ₀ φa φf₀ gS := isFormulaSL_of_isSemiLocalFactorization hfact₀
  have hT : ∀ a ∈ T, (ws a).1 ∉ SL := fun a ha => hTSL a ha (ws a).1 (ws a).2

  set l₀ := T.toList with hl₀
  have hl₀nd : l₀.Nodup := Finset.nodup_toList T
  have hl₀T : ∀ a ∈ l₀, a ∈ T := fun a ha => Finset.mem_toList.mp ha
  have hl₀S : ∀ a ∈ l₀, a ∈ S ∪ T := fun a ha => Finset.mem_union_right _ (hl₀T a ha)

  obtain ⟨φf', hφf'⟩ := exists_isFormulaSL_iterSL ws w h₀ l₀ hl₀nd hl₀S
  have hf' : IsFormulaSL (S ∪ T) φ φa φf _ := isFormulaSL_of_isSemiLocalFactorization hfact
  have hfeq : φ = iterSL ws w l₀ φ₀ := by
    refine eq_of_isFormulaSL hf' hφf' fun v _ => ?_
    have hvl : v ∈ l₀ ↔ v ∈ T := Finset.mem_toList
    by_cases hvT : v ∈ T
    · simp only [gIterSL, hvT, hvl, if_true, gS]
      rfl
    · simp only [gIterSL, hvT, hvl, if_false, gS]

  have hαm_val : ∀ y : (AdeleRing (𝓞 L) L)ˣ,
      ((αm y : ℝˣ) : ℝ) = ((distribHaarChar (AdeleRing (𝓞 L) L) y : NNReal) : ℝ) := fun y => rfl
  have heig : ∀ a ∈ T, ∀ g : AdelicGL2 (𝓞 L) L,
      ∑ ι, ψ (g * emb L (ws a).1 (w a ι)) = (aEis μ ν s (ws a).1 ^ ks a * cEis μ ν (ws a).1 ^ js a) * ψ g := by
    intro a ha g
    have hαv : ((αm (idl L (ws a).1 (piUnit (ϖs a) (hϖs0 a ha))) : ℝˣ) : ℝ) =
        ((Ideal.absNorm (ws a).1.asIdeal : ℕ) : ℝ)⁻¹ := by
      rw [hαm_val]
      exact distribHaarChar_idl_of_valued_eq _ (valued_eq_exp_neg_one_of_irreducible (hirr a ha))
    exact word (hT a ha) (ϖs a) (hirr a ha) (hϖs0 a ha) (hcos a ha) (zs a) (hzs a ha) αm hαm hαv
      (hμν a ha).1 (hμν a ha).2 s hψ hψsph (ks a) (js a) g

  have hloc : ∀ a ∈ T, ∀ y, φ₀ y ≠ 0 → localAt L (ws a).1 y ∈ localIntegralSet L (ws a).1 := by
    intro a ha y hy
    have haS : a ∈ S ∪ T := Finset.mem_union_right _ ha
    rw [h₀.2.2 y] at hy
    have hff : φf₀ (glFin (𝓞 L) L y) ≠ 0 := right_ne_zero_of_mul hy
    have hint : ∀ v ∉ S ∪ T, semiLocalComponent K L v (glFin (𝓞 L) L y) ∈ semiLocalIntegralSet K L v := by
      by_contra hcon
      push Not at hcon
      exact hff (h₀.2.1 _ hcon)
    rw [h₀.1 _ hint] at hff
    have ha' := Finset.prod_ne_zero_iff.mp hff a haS
    simp only [gS, ha, if_true] at ha'
    have hmem : semiLocalComponent K L a (glFin (𝓞 L) L y) ∈ semiLocalIntegralSet K L a := by
      by_contra hnot
      exact ha' (Set.indicator_of_notMem hnot _)
    exact (semiLocalComponent_mem_iff a _).mp hmem (ws a)
  have hmain := rightConv_iterSL ws w hT (fun a => aEis μ ν s (ws a).1 ^ ks a * cEis μ ν (ws a).1 ^ js a)
    hψc hψsph heig hφ₀ hφ₀c hloc l₀ hl₀nd hl₀T x
  rw [Finset.prod_map_toList] at hmain
  rw [hfeq]
  exact hmain

end S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization
end P2MW
export P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization (solution)
