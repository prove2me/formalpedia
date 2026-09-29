-- Prove2me | solution 1 for AutomorphicForm.finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/799939de-f0ce-5791-b532-421a83250e18

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped NNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "SquaresToXi finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff"
namespace RowF
p2m_open "AutomorphicForm"

section Arch

variable {K : Type} [Field K]

open scoped Classical in

def archPos (w : InfinitePlace K) : Set w.Completion :=
  if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw) ⁻¹' Set.Ioi 0 else Set.univ

theorem isOpen_archPos (w : InfinitePlace K) : IsOpen (archPos w) := by
  unfold archPos
  split_ifs with hw
  · exact isOpen_Ioi.preimage (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
  · exact isOpen_univ

theorem one_mem_archPos (w : InfinitePlace K) : (1 : w.Completion) ∈ archPos w := by
  unfold archPos
  split_ifs with hw
  · simp
  · trivial

theorem exists_mul_self_eq_of_mem_archPos (w : InfinitePlace K) {a : w.Completion}
    (ha : a ∈ archPos w) : ∃ b : w.Completion, b * b = a := by
  unfold archPos at ha
  split_ifs at ha with hw
  · have ha' : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw a := ha
    refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
      (Real.sqrt (InfinitePlace.Completion.ringEquivRealOfIsReal hw a)), ?_⟩
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective
    rw [map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt ha'.le]
  · rcases InfinitePlace.isReal_or_isComplex w with h | h
    · exact absurd h hw
    · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex h a) (n := 2) two_pos
      refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex h).symm z,
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex h).injective ?_⟩
      rw [map_mul, RingEquiv.apply_symm_apply, ← hz, pow_two]

end Arch

section Idele

variable (K : Type) [Field K] [NumberField K]

theorem fst_mul_inv (x : (AdeleRing (𝓞 K) K)ˣ) :
    (x : AdeleRing (𝓞 K) K).1 * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  have h := congr_arg Prod.fst x.mul_inv
  exact h

theorem fst_inv_mul (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * (x : AdeleRing (𝓞 K) K).1 = 1 := by
  have h := congr_arg Prod.fst x.inv_mul
  exact h

theorem snd_mul_inv (x : (AdeleRing (𝓞 K) K)ˣ) :
    (x : AdeleRing (𝓞 K) K).2 * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := by
  have h := congr_arg Prod.snd x.mul_inv
  exact h

theorem snd_inv_mul (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 * (x : AdeleRing (𝓞 K) K).2 = 1 := by
  have h := congr_arg Prod.snd x.inv_mul
  exact h

def archPart (x : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((x : AdeleRing (𝓞 K) K).1, 1)
  inv := (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1, 1)
  val_inv := Prod.ext (fst_mul_inv K x) (one_mul 1)
  inv_val := Prod.ext (fst_inv_mul K x) (one_mul 1)

def finPart (x : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (x : AdeleRing (𝓞 K) K).2)
  inv := (1, ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2)
  val_inv := Prod.ext (one_mul 1) (snd_mul_inv K x)
  inv_val := Prod.ext (one_mul 1) (snd_inv_mul K x)

theorem archPart_mul_finPart (x : (AdeleRing (𝓞 K) K)ˣ) : archPart K x * finPart K x = x :=
  Units.ext (Prod.ext (mul_one _) (one_mul _))

theorem coe_archPart_fst (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((archPart K x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = (x : AdeleRing (𝓞 K) K).1 := rfl

theorem coe_archPart_snd (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((archPart K x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem coe_finPart_fst (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((finPart K x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem coe_finPart_snd (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((finPart K x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = (x : AdeleRing (𝓞 K) K).2 := rfl

theorem exists_mul_self_eq_archPart (x : (AdeleRing (𝓞 K) K)ˣ)
    (hx : ∀ w : InfinitePlace K, (x : AdeleRing (𝓞 K) K).1 w ∈ archPos w) :
    ∃ y : (AdeleRing (𝓞 K) K)ˣ, y * y = archPart K x := by
  choose b hb using fun w => exists_mul_self_eq_of_mem_archPos w (hx w)
  have hx0 : ∀ w : InfinitePlace K, (x : AdeleRing (𝓞 K) K).1 w ≠ 0 := by
    intro w h
    have h1 : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by
      rw [Units.mul_inv]; rfl
    have h2 : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w
        = (x : AdeleRing (𝓞 K) K).1 w * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w := rfl
    rw [h2, h, zero_mul] at h1
    exact zero_ne_one h1
  have hb0 : ∀ w, b w ≠ 0 := fun w h => hx0 w (by rw [← hb w, h, zero_mul])
  let y : (AdeleRing (𝓞 K) K)ˣ :=
    ⟨((fun w => b w : InfiniteAdeleRing K), 1), ((fun w => (b w)⁻¹ : InfiniteAdeleRing K), 1),
      Prod.ext (funext fun w => show b w * (b w)⁻¹ = 1 from mul_inv_cancel₀ (hb0 w)) (one_mul 1),
      Prod.ext (funext fun w => show (b w)⁻¹ * b w = 1 from inv_mul_cancel₀ (hb0 w)) (one_mul 1)⟩
  exact ⟨y, Units.ext (Prod.ext (funext fun w => hb w) (one_mul 1))⟩

end Idele

section GL2

variable (K : Type) [Field K] [NumberField K]

@[scoped simp] theorem adele_fst_zero : (0 : AdeleRing (𝓞 K) K).1 = 0 := rfl
@[scoped simp] theorem adele_snd_zero : (0 : AdeleRing (𝓞 K) K).2 = 0 := rfl
@[scoped simp] theorem adele_fst_one : (1 : AdeleRing (𝓞 K) K).1 = 1 := rfl
@[scoped simp] theorem adele_snd_one : (1 : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem coe_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![(a : A), 1] := rfl

theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagOne, Matrix.det_diagonal]
  simp

theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (AdeleRing (𝓞 K) K)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, coe_diagOne]
    fin_cases i <;> fin_cases j
    · simpa using Units.continuous_val
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using continuous_const
  · have h : ∀ a : (AdeleRing (𝓞 K) K)ˣ,
        (((diagOne a)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
          = Matrix.diagonal ![((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] := fun a => by
      rw [← map_inv, coe_diagOne]
    simp only [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using Units.continuous_coe_inv
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using continuous_const

variable {N : Ideal (𝓞 K)}

theorem isOpen_principalLevel (hN : N ≠ ⊥) :
    IsOpen (principalLevel (𝓞 K) K N : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) := by
  have h1 := isOpen_levelOne (𝓞 K) K hN
  have : (principalLevel (𝓞 K) K N : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))
      = (levelOne (𝓞 K) K N : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) ∩
        (fun g => (weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K) ⁻¹'
          (levelOne (𝓞 K) K N : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) := by
    ext g
    simp only [SetLike.mem_coe, mem_principalLevel_iff, Set.mem_inter_iff, Set.mem_preimage,
      Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [this]
  exact h1.inter (h1.preimage ((continuous_const.mul continuous_id).mul continuous_const))

theorem mem_principalLevel_congr {g g' : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (h : glFin (𝓞 K) K g = glFin (𝓞 K) K g') :
    g ∈ principalLevel (𝓞 K) K N ↔ g' ∈ principalLevel (𝓞 K) K N := by
  simp only [mem_principalLevel_iff, mem_levelOne_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    map_mul, h]

theorem glFin_diagOne_finPart (x : (AdeleRing (𝓞 K) K)ˣ) :
    glFin (𝓞 K) K (diagOne (finPart K x)) = glFin (𝓞 K) K (diagOne x) := by
  ext i j
  rw [glFin_apply, glFin_apply, coe_diagOne, coe_diagOne]
  fin_cases i <;> fin_cases j <;> simp [coe_finPart_snd, adele_snd_zero, adele_snd_one]

theorem glArch_diagOne_finPart (x : (AdeleRing (𝓞 K) K)ˣ) :
    glArch (𝓞 K) K (diagOne (finPart K x)) = 1 := by
  ext i j
  rw [glArch_apply, coe_diagOne]
  fin_cases i <;> fin_cases j <;> simp [coe_finPart_fst, adele_fst_zero, adele_fst_one]

theorem diagOne_finPart_mem {x : (AdeleRing (𝓞 K) K)ˣ} (hx : diagOne x ∈ principalLevel (𝓞 K) K N) :
    diagOne (finPart K x) ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K :=
  ⟨(mem_principalLevel_congr K (glFin_diagOne_finPart K x)).mpr hx,
    (mem_finiteAdelicGL2Subgroup_iff K _).mpr (glArch_diagOne_finPart K x)⟩

end GL2

section Good

variable (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K))

def goodSet : Set (AdeleRing (𝓞 K) K)ˣ :=
  {x | diagOne x ∈ principalLevel (𝓞 K) K N ∧ ∀ w : InfinitePlace K, (x : AdeleRing (𝓞 K) K).1 w ∈ archPos w}

theorem one_mem_goodSet : (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ goodSet K N := by
  refine ⟨by rw [map_one]; exact Subgroup.one_mem _, fun w => ?_⟩
  rw [Units.val_one]
  exact one_mem_archPos w

variable {N} in
theorem isOpen_goodSet (hN : N ≠ ⊥) : IsOpen (goodSet K N) := by
  have h2 : IsOpen (⋂ w : InfinitePlace K,
      (fun x : (AdeleRing (𝓞 K) K)ˣ => archEval K w (adeleArch (𝓞 K) K (x : AdeleRing (𝓞 K) K)))
        ⁻¹' archPos w) :=
    isOpen_iInter_of_finite fun w => (isOpen_archPos w).preimage
      ((continuous_archEval K w).comp ((continuous_adeleArch (𝓞 K) K).comp Units.continuous_val))
  convert ((isOpen_principalLevel K hN).preimage (continuous_diagOne K)).inter h2 using 1
  ext x
  simp only [goodSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, archEval_apply,
    adeleArch_apply, SetLike.mem_coe]

structure IsGood (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop where
  sq : ∀ x, η x ^ 2 = 1
  principal : ∀ z ∈ M4aHerbrand.principalIdeles (𝓞 K) K, η z = 1
  level : ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
    η (Matrix.GeneralLinearGroup.det u) = 1

variable {K N} {η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

theorem IsGood.apply_mul_self (h : IsGood K N η) (y : (AdeleRing (𝓞 K) K)ˣ) : η (y * y) = 1 := by
  rw [map_mul, ← pow_two, h.sq]

theorem IsGood.eq_one_of_mem_goodSet (h : IsGood K N η) {x : (AdeleRing (𝓞 K) K)ˣ}
    (hx : x ∈ goodSet K N) : η x = 1 := by
  obtain ⟨y, hy⟩ := exists_mul_self_eq_archPart K x hx.2
  have h1 : η (archPart K x) = 1 := by rw [← hy]; exact h.apply_mul_self y
  have h2 : η (finPart K x) = 1 := by
    rw [← det_diagOne (finPart K x)]
    exact h.level _ (diagOne_finPart_mem K hx.1)
  rw [← archPart_mul_finPart K x, map_mul, h1, h2, one_mul]

end Good

section Cover

variable (K : Type) [Field K] [NumberField K]

theorem exists_finset_forall_mem_normOneIdeles {W : Set (AdeleRing (𝓞 K) K)ˣ} (hW : IsOpen W)
    (h1 : (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ W) :
    ∃ t : Finset (AdeleRing (𝓞 K) K)ˣ, ∀ a ∈ TateGlobal.normOneIdeles K,
      ∃ g ∈ t, ∃ w ∈ W, ∃ p ∈ M4aHerbrand.principalIdeles (𝓞 K) K, a = g * w * p := by
  classical
  haveI : CompactSpace (↥(TateGlobal.normOneIdeles K) ⧸
      (M4aHerbrand.principalIdeles (𝓞 K) K).subgroupOf (TateGlobal.normOneIdeles K)) :=
    TateGlobal.compactSpace_normOneIdeleClass K
  set A1 := TateGlobal.normOneIdeles K with hA1
  set P := M4aHerbrand.principalIdeles (𝓞 K) K with hP
  let W1 : Set A1 := Subtype.val ⁻¹' W
  have hW1 : IsOpen W1 := hW.preimage continuous_subtype_val
  let U : A1 → Set (A1 ⧸ P.subgroupOf A1) := fun g =>
    (QuotientGroup.mk : A1 → A1 ⧸ P.subgroupOf A1) '' ((fun w : A1 => g * w) '' W1)
  have hUo : ∀ g, IsOpen (U g) := fun g =>
    QuotientGroup.isOpenMap_coe _ ((Homeomorph.mulLeft g).isOpenMap _ hW1)
  have hcov : (Set.univ : Set (A1 ⧸ P.subgroupOf A1)) ⊆ ⋃ g, U g := by
    rintro q -
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    refine Set.mem_iUnion.mpr ⟨a, ⟨a, ⟨1, ?_, mul_one a⟩, rfl⟩⟩
    show ((1 : A1) : (AdeleRing (𝓞 K) K)ˣ) ∈ W
    exact h1
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hcov
  refine ⟨t.image Subtype.val, fun a ha => ?_⟩
  have hq := ht (Set.mem_univ (QuotientGroup.mk ⟨a, ha⟩ : A1 ⧸ P.subgroupOf A1))
  simp only [Set.mem_iUnion, exists_prop] at hq
  obtain ⟨g, hgt, hq⟩ := hq
  obtain ⟨_, ⟨w, hw, rfl⟩, hgw⟩ := hq
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hgw
  refine ⟨(g : (AdeleRing (𝓞 K) K)ˣ), Finset.mem_image_of_mem _ hgt, (w : (AdeleRing (𝓞 K) K)ˣ), hw,
    _, hgw, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_cancel_left]

end Cover

section Norm

variable (K : Type) [Field K] [NumberField K]

theorem exists_mem_normOneIdeles_mul (s : ℝ≥0ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hs : ∀ r : ℝ≥0ˣ, TateGlobal.ideleNorm K (s r) = ((r : ℝ≥0) : ℝ)) (x : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ a ∈ TateGlobal.normOneIdeles K, ∃ r : ℝ≥0ˣ, x = a * s (r * r) := by
  have hpos : 0 < TateGlobal.ideleNorm K x := TateGlobal.ideleNorm_pos x
  have hsq : 0 < NNReal.sqrt (TateGlobal.ideleNorm K x).toNNReal := by
    rw [NNReal.sqrt_pos]
    exact Real.toNNReal_pos.mpr hpos
  set r : ℝ≥0ˣ := Units.mk0 (NNReal.sqrt (TateGlobal.ideleNorm K x).toNNReal) hsq.ne' with hr
  have hrr : (((r * r : ℝ≥0ˣ) : ℝ≥0) : ℝ) = TateGlobal.ideleNorm K x := by
    rw [Units.val_mul, hr, Units.val_mk0, NNReal.mul_self_sqrt, Real.coe_toNNReal _ hpos.le]
  refine ⟨x * (s (r * r))⁻¹, ?_, r, (inv_mul_cancel_right x (s (r * r))).symm⟩
  rw [TateGlobal.mem_normOneIdeles_iff]
  have hmul := TateGlobal.ideleNorm_mul (x * (s (r * r))⁻¹) (s (r * r))
  rw [inv_mul_cancel_right, hs, hrr] at hmul
  have hne : TateGlobal.ideleNorm K x ≠ 0 := hpos.ne'
  exact (mul_eq_right₀ hne).mp hmul.symm

end Norm

section Key

variable (K : Type) [Field K] [NumberField K] {N : Ideal (𝓞 K)}

theorem exists_finset_forall_isGood (hN : N ≠ ⊥) :
    ∃ t : Finset (AdeleRing (𝓞 K) K)ˣ, ∀ x : (AdeleRing (𝓞 K) K)ˣ, ∃ g ∈ t,
      ∀ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsGood K N η → η x = η g := by
  obtain ⟨t, ht⟩ := exists_finset_forall_mem_normOneIdeles K (isOpen_goodSet K hN) (one_mem_goodSet K N)
  obtain ⟨s, -, hs, -⟩ := TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
  refine ⟨t, fun x => ?_⟩
  obtain ⟨a, ha, r, rfl⟩ := exists_mem_normOneIdeles_mul K s hs x
  obtain ⟨g, hg, w, hw, p, hp, rfl⟩ := ht a ha
  refine ⟨g, hg, fun η hη => ?_⟩
  rw [map_mul, map_mul s, hη.apply_mul_self, mul_one, map_mul, map_mul, hη.eq_one_of_mem_goodSet hw,
    hη.principal p hp, mul_one, mul_one]

theorem finite_setOf_sq_eq_one : {u : ℂˣ | u ^ 2 = 1}.Finite := by
  refine (Set.toFinite ({1, -1} : Set ℂˣ)).subset fun u hu => ?_
  have h : (u : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, Set.mem_setOf_eq.mp hu, Units.val_one]
  rcases sq_eq_one_iff.mp h with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))

theorem finite_of_forall_isGood_div (hN : N ≠ ⊥) (S : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
    (hS : ∀ χ ∈ S, ∀ χ₀ ∈ S, IsGood K N (χ / χ₀)) : S.Finite := by
  classical
  rcases S.eq_empty_or_nonempty with h | ⟨χ₀, hχ₀⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨t, ht⟩ := exists_finset_forall_isGood K hN
  let F : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → (↥t → ℂˣ) := fun χ g => (χ / χ₀) (g : (AdeleRing (𝓞 K) K)ˣ)
  have hfin : (Set.univ.pi fun _ : ↥t => {u : ℂˣ | u ^ 2 = 1}).Finite :=
    Set.Finite.pi fun _ => finite_setOf_sq_eq_one
  refine Set.Finite.of_finite_image (f := F) (hfin.subset ?_) ?_
  · rintro _ ⟨χ, hχ, rfl⟩
    exact fun g _ => (hS χ hχ χ₀ hχ₀).sq (g : (AdeleRing (𝓞 K) K)ˣ)
  · intro χ hχ χ' hχ' hF
    have key : χ / χ₀ = χ' / χ₀ := by
      ext x
      obtain ⟨g, hg, hgx⟩ := ht x
      rw [hgx _ (hS χ hχ χ₀ hχ₀), hgx _ (hS χ' hχ' χ₀ hχ₀)]
      exact congr_arg Units.val (congr_fun hF ⟨g, hg⟩)
    exact div_left_injective key

end Key

end AutomorphicForm.RowF
p2m_reactivate "P2MW.S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel.AutomorphicForm P2MW.S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel.AutomorphicForm.RowF"
p2m_reactivate "P2MW.S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel.AutomorphicForm P2MW.S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel.AutomorphicForm.RowF"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel.AutomorphicForm AutomorphicForm.RowF in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN0 : N ≠ ⊥) :
    {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        AutomorphicForm.SquaresToXi (𝓞 K) K ⊤ ξ χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
          χ (Matrix.GeneralLinearGroup.det u) = 1}.Finite := by
  refine finite_of_forall_isGood_div K hN0 _ fun χ hχ χ₀ hχ₀ => ⟨fun x => ?_, fun z hz => ?_, fun u hu => ?_⟩
  · have h1 : χ x ^ 2 = ξ ⟨x, Subgroup.mem_top x⟩ := hχ.1 ⟨x, Subgroup.mem_top x⟩
    have h2 : χ₀ x ^ 2 = ξ ⟨x, Subgroup.mem_top x⟩ := hχ₀.1 ⟨x, Subgroup.mem_top x⟩
    rw [MonoidHom.div_apply, div_pow, h1, h2, div_self']
  · rw [MonoidHom.div_apply, hχ.2.1 z hz, hχ₀.2.1 z hz, div_one]
  · rw [MonoidHom.div_apply, hχ.2.2.2 u hu, hχ₀.2.2.2 u hu, div_one]

end S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel
end P2MW
export P2MW.S_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel (solution)
