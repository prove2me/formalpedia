-- Prove2me | solution 1 for AutomorphicForm.integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/77ff19e0-1bef-580e-ab07-972a01c466bd

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

open AutomorphicForm AdelicDock LocalGL2

namespace RowH

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
  ext i j w : 2
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
        first | exact ha | simpa using ha
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

def piUnit (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) : (Kv)ˣ := Units.mk0 _ hϖ0

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

section Conv

attribute [local instance] NumberField.AdelicHaar.glBorel

def transSum (v : HeightOneSpectrum (𝓞 K)) {J : Type} [Fintype J] (w : J → GL (Fin 2) (v.adicCompletion K))
    (F : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => ∑ j, F ((emb K v (w j))⁻¹ * y)

theorem transSum_apply (v : HeightOneSpectrum (𝓞 K)) {J : Type} [Fintype J] (w : J → GL (Fin 2) (v.adicCompletion K))
    (F : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) :
    transSum v w F y = ∑ j, F ((emb K v (w j))⁻¹ * y) := rfl

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

def IsFormula (S : Finset (HeightOneSpectrum (𝓞 K))) (F : AdelicGL2 (𝓞 K) K → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
    (∀ v ∉ S, finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
      ff h = ∏ v ∈ S, gS v (finComponent (𝓞 K) K v h)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
    (∃ v ∉ S, finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0) ∧
  ∀ g, F g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)

theorem isFormula_of_isUnitFactorization {S : Finset (HeightOneSpectrum (𝓞 K))} {F : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ}
    (h : IsUnitFactorization K S F fa ff gS) : IsFormula S F fa ff gS :=
  ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem eq_of_isFormula {S : Finset (HeightOneSpectrum (𝓞 K))} {F F' : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff ff' : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {gS gS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ}
    (h : IsFormula S F fa ff gS) (h' : IsFormula S F' fa ff' gS') (heq : ∀ v ∈ S, gS v = gS' v) : F = F' := by
  funext g
  rw [h.2.2 g, h'.2.2 g]
  congr 1
  by_cases hint : ∀ v ∉ S, finComponent (𝓞 K) K v (glFin (𝓞 K) K g) ∈ localIntegralSet K v
  · rw [h.1 _ hint, h'.1 _ hint]
    exact Finset.prod_congr rfl fun v hv => by rw [heq v hv]
  · push Not at hint
    rw [h.2.1 _ hint, h'.2.1 _ hint]

theorem finComponent_localEmbed_inv_mul_of_ne {a v : HeightOneSpectrum (𝓞 K)} (hva : v ≠ a)
    (x : GL (Fin 2) (a.adicCompletion K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    finComponent (𝓞 K) K v ((localEmbed (𝓞 K) K a x)⁻¹ * h) = finComponent (𝓞 K) K v h := by
  rw [map_mul, map_inv, finComponent_localEmbed_of_ne (𝓞 K) K a x hva, inv_one, one_mul]

theorem finComponent_localEmbed_inv_mul_self {a : HeightOneSpectrum (𝓞 K)}
    (x : GL (Fin 2) (a.adicCompletion K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    finComponent (𝓞 K) K a ((localEmbed (𝓞 K) K a x)⁻¹ * h) = x⁻¹ * finComponent (𝓞 K) K a h := by
  rw [map_mul, map_inv, finComponent_localEmbed_self]

theorem isFormula_transSum [DecidableEq (HeightOneSpectrum (𝓞 K))] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {F : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ}
    (hF : IsFormula S F fa ff gS) {a : HeightOneSpectrum (𝓞 K)} (ha : a ∈ S) {Ja : Type} [Fintype Ja]
    (wa : Ja → GL (Fin 2) (a.adicCompletion K)) :
    IsFormula S (transSum a wa F) fa (fun h => ∑ j, ff ((localEmbed (𝓞 K) K a (wa j))⁻¹ * h))
      (Function.update gS a (fun x => ∑ j, gS a ((wa j)⁻¹ * x))) := by
  refine ⟨fun h hint => ?_, fun h hbad => ?_, fun g => ?_⟩
  ·
    have hint' : ∀ j, ∀ v ∉ S,
        finComponent (𝓞 K) K v ((localEmbed (𝓞 K) K a (wa j))⁻¹ * h) ∈ localIntegralSet K v := by
      intro j v hv
      have hva : v ≠ a := fun e => hv (e ▸ ha)
      rw [finComponent_localEmbed_inv_mul_of_ne hva]
      exact hint v hv
    have hR : ∏ v ∈ S, Function.update gS a (fun x => ∑ j, gS a ((wa j)⁻¹ * x)) v (finComponent (𝓞 K) K v h) =
        (∑ j, gS a ((wa j)⁻¹ * finComponent (𝓞 K) K a h)) *
          ∏ v ∈ S.erase a, gS v (finComponent (𝓞 K) K v h) := by
      rw [← Finset.mul_prod_erase S _ ha, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
    rw [hR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF.1 _ (hint' j), ← Finset.mul_prod_erase S _ ha, finComponent_localEmbed_inv_mul_self]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [finComponent_localEmbed_inv_mul_of_ne (Finset.ne_of_mem_erase hv)]
  ·
    obtain ⟨v, hv, hbad⟩ := hbad
    have hva : v ≠ a := fun e => hv (e ▸ ha)
    refine Finset.sum_eq_zero fun j _ => hF.2.1 _ ⟨v, hv, ?_⟩
    rwa [finComponent_localEmbed_inv_mul_of_ne hva]
  ·
    rw [transSum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF.2.2, map_mul, map_inv, glArch_emb, inv_one, one_mul, map_mul, map_inv, glFin_emb]

def gIter [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (l : List (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) : GL (Fin 2) (v.adicCompletion K) → ℂ :=
  if v ∈ l then fun x => ∑ j, gS v ((w v j)⁻¹ * x) else gS v

theorem exists_isFormula_iter [DecidableEq (HeightOneSpectrum (𝓞 K))] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {F₀ : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ}
    (h₀ : IsFormula S F₀ fa ff₀ gS) :
    ∀ l : List (HeightOneSpectrum (𝓞 K)), l.Nodup → (∀ a ∈ l, a ∈ S) →
      ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ, IsFormula S (iter w l F₀) fa ff (gIter w gS l)
  | [], _, _ => ⟨ff₀, by
      have : gIter w gS [] = gS := by
        funext v
        simp [gIter]
      rw [iter_nil, this]
      exact h₀⟩
  | a :: l, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have haS : a ∈ S := hsub a List.mem_cons_self
    obtain ⟨ff, hff⟩ := exists_isFormula_iter h₀ l hnd.2 fun b hb => hsub b (List.mem_cons_of_mem a hb)
    have key := isFormula_transSum hff haS (w a)
    have heq : Function.update (gIter w gS l) a (fun x => ∑ j, gIter w gS l a ((w a j)⁻¹ * x)) =
        gIter w gS (a :: l) := by
      funext v
      by_cases hva : v = a
      · subst hva
        rw [Function.update_self]
        simp [gIter, hnd.1]
      · rw [Function.update_of_ne hva]
        simp [gIter, hva]
    rw [heq] at key
    exact ⟨_, key⟩

end Conv

section Card

variable {G : Type*} [Group G] {U : Subgroup G} {g₀ : G}

theorem card_eq_of_isHeckeCosetSystem {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    {reps₀ : ι₀ → G} {reps₁ : ι₁ → G}
    (h₀ : HeckeIntegralSeam.IsHeckeCosetSystem U g₀ reps₀) (h₁ : HeckeIntegralSeam.IsHeckeCosetSystem U g₀ reps₁) :
    Fintype.card ι₀ = Fintype.card ι₁ := by
  have h := cosetSum_eq_of_isHeckeCosetSystem h₀ h₁ (fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

end Card

section Det

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem det_emb (y : GL (Fin 2) (Kv)) :
    Matrix.GeneralLinearGroup.det (emb K v y) = idl K v (Matrix.GeneralLinearGroup.det y) := by
  apply Units.ext
  refine Prod.ext ?_ ?_
  · rw [idl_fst, Matrix.GeneralLinearGroup.val_det_apply]
    show adeleArch (𝓞 K) K (((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) = 1
    rw [RingHom.map_det]
    have h1 : (adeleArch (𝓞 K) K).mapMatrix
        ((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, emb_apply_fst]
    rw [h1, Matrix.det_one]
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    ext w : 1
    show finAdeleEval (𝓞 K) K w (adeleFin (𝓞 K) K
      (((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det)) = _
    rw [← RingHom.comp_apply, RingHom.map_det]
    by_cases hw : w = v
    · subst hw
      rw [idl_snd_self, Matrix.GeneralLinearGroup.val_det_apply]
      congr 1
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply, adeleFin_apply,
        finAdeleEval_apply, emb_apply_snd_self]
    · rw [idl_snd_of_ne v _ hw]
      have h1 : ((finAdeleEval (𝓞 K) K w).comp (adeleFin (𝓞 K) K)).mapMatrix
          ((emb K v y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = 1 := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply, adeleFin_apply,
          finAdeleEval_apply, emb_apply_snd_of_ne v y i j hw]
      rw [h1, Matrix.det_one]

theorem valued_algebraMap_units (u : (𝓞v)ˣ) : Valued.v (algebraMap (𝓞v) (Kv) (u : 𝓞v)) = 1 := by
  have h1 : Valued.v (algebraMap (𝓞v) (Kv) (u : 𝓞v)) ≤ 1 := (u : 𝓞v).2
  have h2 : Valued.v (algebraMap (𝓞v) (Kv) ((u⁻¹ : (𝓞v)ˣ) : 𝓞v)) ≤ 1 := ((u⁻¹ : (𝓞v)ˣ) : 𝓞v).2
  have h3 : Valued.v (algebraMap (𝓞v) (Kv) (u : 𝓞v)) * Valued.v (algebraMap (𝓞v) (Kv) ((u⁻¹ : (𝓞v)ˣ) : 𝓞v))
      = 1 := by
    rw [← Valuation.map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
      Valuation.map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ * _ := h3.symm
    _ ≤ Valued.v (algebraMap (𝓞v) (Kv) (u : 𝓞v)) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem valued_det_of_mem_integralSubgroup {u : GL (Fin 2) (Kv)} (hu : u ∈ integralSubgroup (𝓞v) (Kv)) :
    Valued.v ((Matrix.GeneralLinearGroup.det u : (Kv)ˣ) : Kv) = 1 := by
  obtain ⟨y, rfl⟩ := hu
  have h : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap (𝓞v) (Kv)) y) : (Kv)ˣ) : Kv)
      = algebraMap (𝓞v) (Kv) ((Matrix.GeneralLinearGroup.det y : (𝓞v)ˣ) : 𝓞v) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  rw [h]
  exact valued_algebraMap_units v _

variable {v}

theorem valued_det_of_mem_doubleCoset (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) {r : GL (Fin 2) (Kv)}
    (hr : r ∈ HeckePair.doubleCoset (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0)) :
    Valued.v ((Matrix.GeneralLinearGroup.det r : (Kv)ˣ) : Kv) = Valued.v ((piUnit ϖ hϖ0 : (Kv)ˣ) : Kv) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hr
  have hd : ((Matrix.GeneralLinearGroup.det (diagPi ϖ hϖ0) : (Kv)ˣ) : Kv) = algebraMap (𝓞v) (Kv) ϖ := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagPi, Matrix.det_fin_two_of]
    ring
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Valuation.map_mul, Valuation.map_mul,
    valued_det_of_mem_integralSubgroup v hu, valued_det_of_mem_integralSubgroup v hu', one_mul, mul_one, hd]
  rfl

theorem det_eq_piUnit_sq (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) {z : GL (Fin 2) (Kv)}
    (hz : (z : Matrix (Fin 2) (Fin 2) (Kv)) = algebraMap (𝓞v) (Kv) ϖ • (1 : Matrix (Fin 2) (Fin 2) (Kv))) :
    Matrix.GeneralLinearGroup.det z = piUnit ϖ hϖ0 ^ 2 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hz, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    Units.val_pow_eq_pow_val]
  rfl

theorem chiDet_emb_of_mem_doubleCoset {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : TateGlobal.IsUnramifiedCharAt χ v)
    (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) {r : GL (Fin 2) (Kv)}
    (hr : r ∈ HeckePair.doubleCoset (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0)) :
    chiDet (𝓞 K) K χ (emb K v r) = ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) := by
  have hvalϖ : Valued.v ((piUnit ϖ hϖ0 : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) :=
    valued_eq_exp_neg_one_of_irreducible hirr
  have hval0 : Valued.v ((uniformizerUnit K v : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v
  show ((χ (Matrix.GeneralLinearGroup.det (emb K v r)) : ℂˣ) : ℂ) = _
  rw [det_emb, det_heckeGen, apply_idl_eq_of_isUnramifiedCharAt hχ
    ((valued_det_of_mem_doubleCoset ϖ hϖ0 hr).trans (hvalϖ.trans hval0.symm))]

theorem chiDet_emb_central {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : TateGlobal.IsUnramifiedCharAt χ v)
    (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) {z : GL (Fin 2) (Kv)}
    (hz : (z : Matrix (Fin 2) (Fin 2) (Kv)) = algebraMap (𝓞v) (Kv) ϖ • (1 : Matrix (Fin 2) (Fin 2) (Kv))) :
    chiDet (𝓞 K) K χ (emb K v z) = ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) ^ 2 := by
  have hvalϖ : Valued.v ((piUnit ϖ hϖ0 : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) :=
    valued_eq_exp_neg_one_of_irreducible hirr
  have hval0 : Valued.v ((uniformizerUnit K v : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v
  show ((χ (Matrix.GeneralLinearGroup.det (emb K v z)) : ℂˣ) : ℂ) = _
  rw [det_emb, det_eq_piUnit_sq ϖ hϖ0 hz, idl, map_pow, map_pow, map_pow, Units.val_pow_eq_pow_val, ← idl,
    det_heckeGen, apply_idl_eq_of_isUnramifiedCharAt hχ (hvalϖ.trans hval0.symm)]

end Det

section WordSum

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem chiDet_mul (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x y : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K χ (x * y) = chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ y := by
  simp [chiDet, map_mul]

theorem chiDet_one (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : chiDet (𝓞 K) K χ 1 = 1 := by
  simp [chiDet, map_one]

def chiDetEmb (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : GL (Fin 2) (Kv) →* ℂ where
  toFun y := chiDet (𝓞 K) K χ (emb K v y)
  map_one' := by rw [map_one, chiDet_one]
  map_mul' x y := by rw [map_mul, chiDet_mul]

theorem chiDetEmb_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (y : GL (Fin 2) (Kv)) :
    chiDetEmb v χ y = chiDet (𝓞 K) K χ (emb K v y) := rfl

theorem wordSum_eq {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : TateGlobal.IsUnramifiedCharAt χ v)
    (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0)
    {n : ℕ} {r : Fin n → GL (Fin 2) (Kv)}
    (hcos : HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0) r)
    {z : GL (Fin 2) (Kv)}
    (hz : (z : Matrix (Fin 2) (Fin 2) (Kv)) = algebraMap (𝓞v) (Kv) ϖ • (1 : Matrix (Fin 2) (Fin 2) (Kv)))
    (k j : ℕ) :
    ∑ ι : Fin k → Fin n, chiDet (𝓞 K) K χ (emb K v ((List.ofFn fun m => r (ι m)).prod * z ^ j)) =
      ((HeckeEigensystem.cNorm v + 1) *
          ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) ^ k *
        ((HeckeEigensystem.cNorm v)⁻¹ * (HeckeEigensystem.cNorm v *
          ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) ^ 2)) ^ j := by
  classical
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  set c : ℂ := ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) with hc
  have hri : ∀ i, chiDetEmb v χ (r i) = c := fun i =>
    chiDet_emb_of_mem_doubleCoset hχ ϖ hirr hϖ0 (hcos.mem_doubleCoset i)
  have hzv : chiDetEmb v χ z = c ^ 2 := chiDet_emb_central hχ ϖ hirr hϖ0 hz
  have hterm : ∀ ι : Fin k → Fin n,
      chiDet (𝓞 K) K χ (emb K v ((List.ofFn fun m => r (ι m)).prod * z ^ j)) = c ^ k * (c ^ 2) ^ j := by
    intro ι
    rw [← chiDetEmb_apply, map_mul, map_pow, hzv, map_list_prod, List.map_ofFn, List.prod_ofFn]
    simp only [Function.comp_apply, hri, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hn : n = Ideal.absNorm v.asIdeal + 1 := by
    have h := card_eq_of_isHeckeCosetSystem hcos (isHeckeCosetSystem_explicitRep ϖ hirr hϖ0)
    rw [Fintype.card_fin, Fintype.card_option, card_quotient_eq_absNorm] at h
    exact h
  have hN0 : HeckeEigensystem.cNorm v ≠ 0 := HeckeEigensystem.cNorm_ne_zero v
  rw [Finset.sum_congr rfl fun ι _ => hterm ι, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, inv_mul_cancel_left₀ hN0, mul_pow, hn, HeckeEigensystem.cNorm]
  push_cast
  ring

end WordSum

section Integral

variable (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

def HasTranslates (a : HeightOneSpectrum (𝓞 K)) {J : Type} [Fintype J] (wa : J → GL (Fin 2) (a.adicCompletion K))
    (F : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∃ D : AdelicGL2 (𝓞 K) K → ℂ, ∀ j g,
    F ((emb K a (wa j))⁻¹ * g) =
      D g * (localIntegralSet K a).indicator (fun _ => (1 : ℂ)) ((wa j)⁻¹ * localAt K a g)

theorem integral_transSum_mul_chiDet (a : HeightOneSpectrum (𝓞 K)) {J : Type} [Fintype J]
    (wa : J → GL (Fin 2) (a.adicCompletion K)) {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : HasTranslates a wa F) :
    ∫ g, transSum a wa F g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (∑ j, chiDet (𝓞 K) K χ (emb K a (wa j))) *
        ∫ g, F g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  classical
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g => F g * chiDet (𝓞 K) K χ g with hΦ
  set e : J → AdelicGL2 (𝓞 K) K := fun j => emb K a (wa j) with he
  have hterm : ∀ j g, F ((e j)⁻¹ * g) * chiDet (𝓞 K) K χ g = chiDet (𝓞 K) K χ (e j) * Φ ((e j)⁻¹ * g) := by
    intro j g
    simp only [hΦ]
    rw [mul_left_comm, ← chiDet_mul, mul_inv_cancel_left]
  have hsum : ∀ g, transSum a wa F g * chiDet (𝓞 K) K χ g = ∑ j, chiDet (𝓞 K) K χ (e j) * Φ ((e j)⁻¹ * g) := by
    intro g
    rw [transSum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hterm j g
  have hint_term : ∀ j, ∫ g, chiDet (𝓞 K) K χ (e j) * Φ ((e j)⁻¹ * g) ∂μ =
      chiDet (𝓞 K) K χ (e j) * ∫ g, Φ g ∂μ := by
    intro j
    rw [integral_const_mul, integral_mul_left_eq_self (fun g => Φ g) (e j)⁻¹]
  simp_rw [hsum]
  by_cases hI : Integrable Φ μ
  · rw [integral_finset_sum _ fun j _ => ((hI.comp_mul_left (e j)⁻¹).const_mul _), Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hint_term j
  · rw [integral_undef hI, mul_zero]
    by_cases hJ : Nonempty J
    swap
    · rw [not_nonempty_iff] at hJ
      simp [Finset.univ_eq_empty]
    obtain ⟨j₀⟩ := hJ
    apply integral_undef
    intro hΨ
    apply hI
    obtain ⟨D, hD⟩ := hF
    set A : J → Set (AdelicGL2 (𝓞 K) K) := fun j =>
      (fun g => (wa j)⁻¹ * localAt K a g) ⁻¹' localIntegralSet K a with hA
    have hAm : ∀ j, MeasurableSet (A j) := fun j =>
      ((isOpen_localIntegralSet K a).preimage ((continuous_const_mul _).comp (continuous_localAt K a))).measurableSet
    set cnt : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ j, (A j).indicator (fun _ => (1 : ℂ)) g with hcnt
    set m : AdelicGL2 (𝓞 K) K → ℂ := fun g => (A j₀).indicator (fun g => (cnt g)⁻¹) g with hm
    have hind : ∀ j g, (localIntegralSet K a).indicator (fun _ => (1 : ℂ)) ((wa j)⁻¹ * localAt K a g)
        = (A j).indicator (fun _ => (1 : ℂ)) g := by
      intro j g
      simp only [hA, Set.indicator_apply, Set.mem_preimage]
    have hΨ_eq : ∀ g, ∑ j, chiDet (𝓞 K) K χ (e j) * Φ ((e j)⁻¹ * g) = D g * chiDet (𝓞 K) K χ g * cnt g := by
      intro g
      simp only [hcnt]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hterm, hD, hind]
      ring
    have hcnt_eq : ∀ g, cnt g = ((Finset.univ.filter fun j => g ∈ A j).card : ℂ) := by
      intro g
      simp only [hcnt, Set.indicator_apply]
      rw [Finset.sum_boole]
    have hkey : ∀ g, chiDet (𝓞 K) K χ (e j₀) * Φ ((e j₀)⁻¹ * g)
        = (∑ j, chiDet (𝓞 K) K χ (e j) * Φ ((e j)⁻¹ * g)) * m g := by
      intro g
      rw [hΨ_eq, ← hterm, hD, hind]
      by_cases hg : g ∈ A j₀
      · have hc0 : cnt g ≠ 0 := by
          rw [hcnt_eq, Nat.cast_ne_zero]
          exact Finset.card_ne_zero.mpr ⟨j₀, by simp [hg]⟩
        simp only [hm, Set.indicator_of_mem hg]
        field_simp
      · simp [hm, Set.indicator_of_notMem hg]
    have hm_meas : Measurable m := by
      have hc : Measurable cnt := by
        simp only [hcnt]
        exact Finset.measurable_sum _ fun j _ => measurable_const.indicator (hAm j)
      simp only [hm]
      exact hc.inv.indicator (hAm j₀)
    have hm_bdd : ∀ g, ‖m g‖ ≤ 1 := by
      intro g
      simp only [hm, Set.indicator_apply]
      split_ifs with hg
      · rw [hcnt_eq, norm_inv, Complex.norm_natCast]
        have h1 : (1 : ℝ) ≤ ((Finset.univ.filter fun j => g ∈ A j).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr ⟨j₀, by simp [hg]⟩
        exact inv_le_one_of_one_le₀ h1
      · simp

    have hT : Integrable (fun g => chiDet (𝓞 K) K χ (e j₀) * Φ ((e j₀)⁻¹ * g)) μ := by
      have hΨm := hΨ.aestronglyMeasurable
      refine Integrable.mono' hΨ.norm (?_) (ae_of_all _ fun g => ?_)
      · have : (fun g => chiDet (𝓞 K) K χ (e j₀) * Φ ((e j₀)⁻¹ * g))
            = fun g => (∑ j, chiDet (𝓞 K) K χ (e j) * Φ ((e j)⁻¹ * g)) * m g := funext hkey
        rw [this]
        exact hΨm.mul hm_meas.aestronglyMeasurable
      · rw [hkey, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hm_bdd g)

    have hc0 : chiDet (𝓞 K) K χ (e j₀) ≠ 0 := by
      simp only [chiDet]
      exact Units.ne_zero _
    have hT' : Integrable (fun g => Φ ((e j₀)⁻¹ * g)) μ := by
      have := hT.const_mul (chiDet (𝓞 K) K χ (e j₀))⁻¹
      refine this.congr (ae_of_all _ fun g => ?_)
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    have := hT'.comp_mul_left (e j₀)
    refine this.congr (ae_of_all _ fun g => ?_)
    simp only
    rw [inv_mul_cancel_left]

theorem hasTranslates_of_isFormula [DecidableEq (HeightOneSpectrum (𝓞 K))] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {F : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ}
    (hF : IsFormula S F fa ff gS) {a : HeightOneSpectrum (𝓞 K)} (ha : a ∈ S)
    (hgSa : gS a = (localIntegralSet K a).indicator (fun _ => (1 : ℂ)))
    {J : Type} [Fintype J] (wa : J → GL (Fin 2) (a.adicCompletion K)) : HasTranslates a wa F := by
  classical
  refine ⟨fun g => if (∀ v ∉ S, finComponent (𝓞 K) K v (glFin (𝓞 K) K g) ∈ localIntegralSet K v) then
      fa (glArch (𝓞 K) K g) * ∏ v ∈ S.erase a, gS v (finComponent (𝓞 K) K v (glFin (𝓞 K) K g)) else 0,
    fun j g => ?_⟩
  rw [hF.2.2, map_mul, map_inv, glArch_emb, inv_one, one_mul, map_mul, map_inv, glFin_emb, localAt_def]
  dsimp only
  by_cases hint : ∀ v ∉ S, finComponent (𝓞 K) K v (glFin (𝓞 K) K g) ∈ localIntegralSet K v
  · have hint' : ∀ v ∉ S,
        finComponent (𝓞 K) K v ((localEmbed (𝓞 K) K a (wa j))⁻¹ * glFin (𝓞 K) K g) ∈ localIntegralSet K v := by
      intro v hv
      have hva : v ≠ a := fun e => hv (e ▸ ha)
      rw [finComponent_localEmbed_inv_mul_of_ne hva]
      exact hint v hv
    rw [hF.1 _ hint', if_pos hint, ← Finset.mul_prod_erase S _ ha, finComponent_localEmbed_inv_mul_self, hgSa,
      Finset.prod_congr rfl fun v hv => by rw [finComponent_localEmbed_inv_mul_of_ne (Finset.ne_of_mem_erase hv)]]
    ring
  · have hint2 := hint
    push_neg at hint2
    obtain ⟨v, hv, hbad⟩ := hint2
    have hva : v ≠ a := fun e => hv (e ▸ ha)
    have hbad' : ∃ v ∉ S,
        finComponent (𝓞 K) K v ((localEmbed (𝓞 K) K a (wa j))⁻¹ * glFin (𝓞 K) K g) ∉ localIntegralSet K v :=
      ⟨v, hv, by rwa [finComponent_localEmbed_inv_mul_of_ne hva]⟩
    rw [hF.2.1 _ hbad', if_neg hint]
    ring

variable {J : HeightOneSpectrum (𝓞 K) → Type} [∀ v, Fintype (J v)]
  (w : ∀ v : HeightOneSpectrum (𝓞 K), J v → GL (Fin 2) (v.adicCompletion K))

theorem integral_iter_mul_chiDet [DecidableEq (HeightOneSpectrum (𝓞 K))] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {F₀ : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ}
    (h₀ : IsFormula S F₀ fa ff₀ gS) (T' : Finset (HeightOneSpectrum (𝓞 K))) (hT'S : T' ⊆ S)
    (hgS : ∀ a ∈ T', gS a = (localIntegralSet K a).indicator (fun _ => (1 : ℂ))) :
    ∀ l : List (HeightOneSpectrum (𝓞 K)), l.Nodup → (∀ a ∈ l, a ∈ T') →
      ∫ g, iter w l F₀ g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        (l.map fun a => ∑ j, chiDet (𝓞 K) K χ (emb K a (w a j))).prod *
          ∫ g, F₀ g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
  | [], _, _ => by simp only [iter_nil, List.map_nil, List.prod_nil, one_mul]
  | a :: l, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have haT : a ∈ T' := hsub a List.mem_cons_self
    have hsub' : ∀ b ∈ l, b ∈ T' := fun b hb => hsub b (List.mem_cons_of_mem a hb)
    obtain ⟨ff, hff⟩ := exists_isFormula_iter w h₀ l hnd.2 (fun b hb => hT'S (hsub' b hb))
    have hga : gIter w gS l a = (localIntegralSet K a).indicator (fun _ => (1 : ℂ)) := by
      simp only [gIter, if_neg hnd.1]
      exact hgS a haT
    have hTr := hasTranslates_of_isFormula hff (hT'S haT) hga (w a)
    simp only [iter_cons]
    rw [integral_transSum_mul_chiDet χ a (w a) hTr, integral_iter_mul_chiDet h₀ T' hT'S hgS l hnd.2 hsub',
      List.map_cons, List.prod_cons, mul_assoc]

end Integral

end RowH

open RowH in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTd : Disjoint T SK)
    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hirr : ∀ v ∈ T, Irreducible (ϖKs v))
    (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (hcos : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hfact : IsUnitFactorization K (SK ∪ T) f faK ff
      (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (nKs v),
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
        else fSK v))
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ : ∀ v ∈ T, NumberField.TateGlobal.IsUnramifiedCharAt χ v) :
    ∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (∏ v ∈ T,
        (((HeckeEigensystem.cNorm v) + 1) *
            ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) ^ ks v *
          ((HeckeEigensystem.cNorm v)⁻¹ *
            ((HeckeEigensystem.cNorm v) *
              ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) ^ 2)) ^ js v) *
        ∫ g, {g : AdelicGL2 (𝓞 K) K |
              ∀ v ∉ SK, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
                localIntegralSet K v}.indicator
            (fun g => faK (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) g *
          chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  classical
  set F₀ : AdelicGL2 (𝓞 K) K → ℂ := {g : AdelicGL2 (𝓞 K) K |
      ∀ v ∉ SK, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ localIntegralSet K v}.indicator
    (fun g => faK (AdelicLevel.glArch (𝓞 K) K g) *
      ∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) with hF₀
  set w : ∀ v : HeightOneSpectrum (𝓞 K), (Fin (ks v) → Fin (nKs v)) → GL (Fin 2) (v.adicCompletion K) :=
    fun v ι => (List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v with hw
  set gS0 : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ :=
    fun v => if v ∈ T then (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) else fSK v with hgS0
  set ffF : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ := {h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) |
      ∀ v ∉ SK, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v}.indicator
    (fun h => ∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v h)) with hffF
  have hdisj : Disjoint SK T := hTd.symm

  have h₀ : RowH.IsFormula (SK ∪ T) F₀ faK ffF gS0 := by
    refine ⟨fun h hint => ?_, fun h hbad => ?_, fun g => ?_⟩
    · rw [Finset.prod_union hdisj]
      have hSK : ∏ v ∈ SK, gS0 v (AdelicLevel.finComponent (𝓞 K) K v h) =
          ∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v h) :=
        Finset.prod_congr rfl fun v hv => by
          simp only [hgS0, if_neg (Finset.disjoint_left.mp hdisj hv)]
      rw [hSK]
      by_cases hT : ∀ v ∈ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v
      · have hcond : ∀ v ∉ SK, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v := by
          intro v hv
          by_cases hvT : v ∈ T
          · exact hT v hvT
          · exact hint v (by rw [Finset.mem_union, not_or]; exact ⟨hv, hvT⟩)
        have hT1 : ∏ v ∈ T, gS0 v (AdelicLevel.finComponent (𝓞 K) K v h) = 1 :=
          Finset.prod_eq_one fun v hv => by
            simp only [hgS0, if_pos hv, Set.indicator_of_mem (hT v hv)]
        rw [hT1, mul_one]
        simp only [hffF]
        rw [Set.indicator_of_mem]
        exact hcond
      · push_neg at hT
        obtain ⟨v, hvT, hbad⟩ := hT
        have hT0 : ∏ v ∈ T, gS0 v (AdelicLevel.finComponent (𝓞 K) K v h) = 0 :=
          Finset.prod_eq_zero hvT (by simp only [hgS0, if_pos hvT, Set.indicator_of_notMem hbad])
        rw [hT0, mul_zero]
        simp only [hffF]
        rw [Set.indicator_of_notMem]
        intro hcond
        exact hbad (hcond v (Finset.disjoint_left.mp hTd hvT))
    · obtain ⟨v, hv, hbad⟩ := hbad
      rw [Finset.mem_union, not_or] at hv
      simp only [hffF]
      rw [Set.indicator_of_notMem]
      intro hcond
      exact hbad (hcond v hv.1)
    · simp only [hF₀, hffF, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp

  have hf' := RowH.isFormula_of_isUnitFactorization hfact

  have heq : RowH.iter w T.toList F₀ = f := by
    obtain ⟨ff', hff'⟩ := RowH.exists_isFormula_iter w h₀ T.toList (Finset.nodup_toList T)
      (fun a ha => Finset.mem_union_right _ (Finset.mem_toList.mp ha))
    refine RowH.eq_of_isFormula hff' hf' fun v _ => ?_
    by_cases hvT : v ∈ T
    · simp only [RowH.gIter, Finset.mem_toList, if_pos hvT, hgS0, hw]
    · simp only [RowH.gIter, Finset.mem_toList, if_neg hvT, hgS0]

  have hint := RowH.integral_iter_mul_chiDet χ w h₀ T Finset.subset_union_right
    (fun a ha => by simp only [hgS0, if_pos ha]) T.toList (Finset.nodup_toList T) (fun a ha => Finset.mem_toList.mp ha)
  rw [heq, Finset.prod_map_toList] at hint
  rw [hint]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  simp only [hw]
  exact RowH.wordSum_eq v (hχ v hv) (ϖKs v) (hirr v hv) (hϖKs0 v hv) (hcos v hv) (hzKs v hv) (ks v) (js v)

end

end S_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization (solution)
