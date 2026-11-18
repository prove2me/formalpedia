-- Prove2me | solution 1 for ArtinKP.GR.secCut_of_isCyclotomicExtension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:39.478612+00:00
-- url     : https://prove2.me/submissions/9b4b0b1c-e519-4853-8a93-cbbe41df65e3

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
import Theorems.Thm_M4aHerbrand_prod_idelicArtinMap_single_eq_one
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_ArtinKP_GK_exists_isDelta
import Theorems.Thm_ArtinKP_GK_exists_summable_majorant_norm_jdef
import Theorems.Thm_ArtinKP_GR_thetaG_eq_tsum_forward
import Theorems.Thm_ArtinKP_GR_thetaG_eq_tsum_reflected
import Theorems.Thm_ArtinKP_GR_thmE
import Theorems.Thm_ArtinKP_GR_weylFlip_of_thmE

section
-- module Solutions.Artin.C0.C0R_P
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# C0-P: the `S`-integers form a PID once `S` contains the small primes

Every ideal class contains a nonzero ideal of bounded norm; once `𝔪` is divisible by every prime of
norm at most that bound, every ideal of `R = 𝓞_S` is principal.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

/-- **C0-P.** Once `S` contains the primes of small norm, `R = 𝓞_S` is a PID. -/
theorem exists_cutoff_isPrincipal_map (F : Type*) [Field F] [NumberField F] :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ I : Ideal (𝓞 F), (I.map (algebraMap (𝓞 F) (SInt 𝔪))).IsPrincipal := by
  classical
  let rep : ClassGroup (𝓞 F) → (Ideal (𝓞 F))⁰ :=
    fun C => Function.surjInv ClassGroup.mk0_surjective C
  have hrep : ∀ C, ClassGroup.mk0 (rep C) = C := fun C =>
    Function.surjInv_eq ClassGroup.mk0_surjective C
  refine ⟨Finset.univ.sup fun C => Ideal.absNorm (rep C : Ideal (𝓞 F)), ?_⟩
  intro 𝔪 h𝔪 hsmall I
  by_cases hI : I = ⊥
  · rw [hI, Ideal.map_bot]; exact bot_isPrincipal
  have hI' : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set J := rep (ClassGroup.mk0 ⟨I, hI'⟩)⁻¹ with hJdef
  have hJ0 : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have hIJ : (I * J).IsPrincipal := by
    have hmem : I * (J : Ideal (𝓞 F)) ∈ (Ideal (𝓞 F))⁰ := mul_mem hI' J.2
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have : (⟨I * J, hmem⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI'⟩ * J := rfl
    rw [this, map_mul, hJdef, hrep, mul_inv_cancel]
  have hJtop : (J : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
    apply C0R.map_eq_top_of_primes 𝔪 h𝔪 _
    intro Q hQ hJQ
    have hQ0 : Q ≠ ⊥ := fun h => hJ0 (le_bot_iff.1 (h ▸ hJQ))
    apply hsmall Q hQ hQ0
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hJQ
    have hJn : Ideal.absNorm (J : Ideal (𝓞 F)) ≠ 0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors J
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hJn) hdvd)
      (Finset.le_sup (f := fun C => Ideal.absNorm (rep C : Ideal (𝓞 F))) (Finset.mem_univ _))
  obtain ⟨a, ha⟩ := hIJ.principal
  rw [Ideal.submodule_span_eq] at ha
  refine ⟨⟨algebraMap (𝓞 F) (SInt 𝔪) a, ?_⟩⟩
  rw [Ideal.submodule_span_eq]
  calc I.map (algebraMap (𝓞 F) (SInt 𝔪))
      = I.map (algebraMap (𝓞 F) (SInt 𝔪)) * (J : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [hJtop, Ideal.mul_top]
    _ = (I * J).map (algebraMap (𝓞 F) (SInt 𝔪)) := (Ideal.map_mul _ _ _).symm
    _ = _ := by rw [ha, Ideal.map_span, Set.image_singleton]

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.C0.C0ZA
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: the library's idelic Artin map for an abelian extension, and ideles at one place. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

/-! ### Generic part: any abelian extension `K/E` of `Type`-level number fields -/

section Generic

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
  [IsGalois E K]

/-- No infinite place of `K` has a nontrivial decomposition group when `E` is totally complex. -/
theorem hinf_of_isTotallyComplex (hcx : ∀ v : InfinitePlace E, v.IsComplex) :
    ∀ (w : InfinitePlace K) (g : K ≃ₐ[E] K), g ∈ NumberField.InfPlaceDecomp.decomp E K w → g = 1 := by
  intro w g hg
  have hun : w.IsUnramified E :=
    InfinitePlace.isUnramified_iff.mpr (Or.inr (hcx _))
  have hcard := (InfinitePlace.isUnramified_iff_card_stabilizer_eq_one (k := E)).mp hun
  have : Subsingleton (MulAction.stabilizer (K ≃ₐ[E] K) w) := by
    exact ((Nat.card_eq_one_iff_unique).mp hcard).1
  exact congrArg Subtype.val (Subsingleton.elim (⟨g, hg⟩ : MulAction.stabilizer (K ≃ₐ[E] K) w) 1)

end Generic

/-! ### The idele supported at one finite place -/

section Single

variable (E : Type) [Field E] [NumberField E]

open scoped Classical

theorem finPart_single (v : HeightOneSpectrum (𝓞 E)) (z : (v.adicCompletion E)ˣ) :
    finPart v (single E v z) = z := by
  apply Units.ext
  show (fsingle E v (z : v.adicCompletion E)) v = z
  rw [fsingle_apply, Pi.mulSingle_eq_same]

theorem single_mem (v : HeightOneSpectrum (𝓞 E)) (z : (v.adicCompletion E)ˣ) :
    single E v z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) := by
  refine ⟨?_, fun w hw => ?_⟩
  · exact Units.ext rfl
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    apply Units.ext
    show (fsingle E v (z : v.adicCompletion E)) w = 1
    rw [fsingle_apply, Pi.mulSingle_eq_of_ne hw]

end Single

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZF
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: the Kummer fields `F(a^{1/ℓ})` and `F(a^{1/ℓ}, a'^{1/ℓ})` as splitting fields. -/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace C0Z

variable (F : Type) [Field F] (ℓ : ℕ)

variable (a a' : Fˣ)

variable {F ℓ}

section Comm

variable [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
include hζ

theorem eq_one_of_kch_KF (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a)
    (h : kch hζ g σ = 1) : σ = 1 := by
  have f1 := fixes_of_kch_eq_one hζ g σ h
  apply AlgEquiv.coe_toAlgHom_injective
  refine AlgHom.ext_of_adjoin_eq_top
    (IsSplittingField.adjoin_rootSet (KF F ℓ a) (X ^ ℓ - C (a : F))) fun r hr => ?_
  rw [mem_rootSet] at hr
  show σ r = r
  exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet hr.2]; exact hg.symm)

theorem kch_KF_injective (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) : Function.Injective (kch hζ g) :=
  (injective_iff_map_eq_one _).mpr fun σ h => eq_one_of_kch_KF a hζ g hg σ h

end Comm

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZP
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: the product formula for the Kummer symbols. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative

noncomputable section

namespace C0Z

variable {F : Type} [Field F] [NumberField F]

theorem finite_valuation_ne_one (b : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (b : F) ≠ 1}.Finite := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) (b : F)
  simp only at hnd
  have hd0 : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hnd
    rcases hnd with h | h
    · exact b.ne_zero h
    · exact hd0 ((FaithfulSMul.algebraMap_injective (𝓞 F) F) (by rw [h, map_zero]))
  refine ((Ideal.finite_factors (I := Ideal.span {n}) (by simpa using hn0)).union
    (Ideal.finite_factors (I := Ideal.span {(d : 𝓞 F)}) (by simpa using hd0))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, Ideal.dvd_span_singleton] at hcon
  have h1 : v.valuation F (algebraMap (𝓞 F) F n) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hcon.1
  have h2 : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hcon.2
  apply hv
  have := congrArg (v.valuation F) hnd
  rw [map_mul, h1, h2, mul_one] at this
  exact this

variable (F) {ℓ : ℕ} [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)

/-- Product formula: if the symbols vanish outside `T`, their product over `T` is `1`. -/
theorem prod_sym_eq_one (hcx : ∀ w : InfinitePlace F, w.IsComplex) (a b : Fˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v ∉ T, sym F hζ v a (C0Y.emb F v b) = 1) :
    ∏ v ∈ T, sym F hζ v a (C0Y.emb F v b) = 1 := by
  classical
  haveI := isMulCommutative_KF a hζ
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec F (KF F ℓ a)
  have hf0 : artinMod F (KF F ℓ a) ≠ ⊥ := h𝔣.1
  set A := (Ideal.finite_factors (I := artinMod F (KF F ℓ a)) hf0).toFinset ∪
    (finite_valuation_ne_one b).toFinset
  set T' := T ∪ A
  have hlib := prod_idelicArtinMap_single_eq_one F (KF F ℓ a) _ h𝔣 _ h1 h2 h3 h4
    (hinf_of_isTotallyComplex F (KF F ℓ a) hcx) b
    (fun v => single F v (C0Y.emb F v b)) (fun v => single_mem F v _)
    (fun v => finPart_single F v _) T'
    (fun v hv => Finset.mem_union_right _ (Finset.mem_union_left _ (by simpa using hv)))
    (fun v hv => by
      by_contra h
      exact hv (Finset.mem_union_right _ (Finset.mem_union_right _ (by simpa using h))))
  have hT' : ∏ v ∈ T', sym F hζ v a (C0Y.emb F v b) = 1 := by
    simp only [sym, MonoidHom.coe_comp, Function.comp_apply]
    rw [← map_prod, hlib, map_one]
  rw [← hT', ← Finset.prod_subset (Finset.subset_union_left (s₂ := A))]
  intro v _ hv
  exact hT v hv

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZL
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: the local image of the Artin map (decomposition and inertia groups). -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

section Generic

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
  [IsGalois E K]

/-- A place of `K` above a given place of `E`. -/
theorem exists_under (v : HeightOneSpectrum (𝓞 E)) :
    ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) = v := by
  refine ⟨⟨primeAbove E K v, (primeAbove_isMaximal E K v).isPrime, primeAbove_ne_bot E K v⟩, ?_⟩
  ext1
  exact under_primeAbove E K v

/-- Ideles trivial away from `v` are `single`s. -/
theorem eq_single_of_mem (v : HeightOneSpectrum (𝓞 E)) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) :
    x = single E v (finPart v x) := by
  classical
  obtain ⟨hinf, hfin⟩ := hx
  apply Units.ext
  refine Prod.ext ?_ ?_
  · exact congrArg Units.val hinf
  · apply RestrictedProduct.ext
    intro w
    show (x : AdeleRing (𝓞 E) E).2 w = (fsingle E v ((finPart v x : (v.adicCompletion E)ˣ) :
      v.adicCompletion E)) w
    rw [fsingle_apply]
    by_cases hw : w = v
    · subst hw
      rw [Pi.mulSingle_eq_same]
      rfl
    · rw [Pi.mulSingle_eq_of_ne hw]
      exact congrArg Units.val (hfin w hw)

variable [IsMulCommutative (K ≃ₐ[E] K)]

/-- The local Artin map at `v` lands in the decomposition group, and onto it. -/
theorem range_single_eq_decomp (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K))
    (hw : w.under (𝓞 E) = v) :
    ((artinMap E K).comp (single E v)).range = NumberField.PlaceDecomp.decomp E K w := by
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec E K
  have hdec := (map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia E K _ h𝔣 _
    h1 h2 h3 h4 v w hw).1
  rw [← hdec]
  ext σ
  simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, Subgroup.mem_map]
  constructor
  · rintro ⟨b, rfl⟩; exact ⟨single E v b, single_mem E v b, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨finPart v x, by rw [← eq_single_of_mem E v x hx]⟩

/-- Local units go to the inertia group. -/
theorem single_unit_mem_inertia (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K))
    (hw : w.under (𝓞 E) = v) (b : (v.adicCompletion E)ˣ)
    (hb : Valued.v (b : v.adicCompletion E) = 1) :
    artinMap E K (single E v b) ∈ w.asIdeal.inertia (K ≃ₐ[E] K) := by
  classical
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec E K
  have hin := (map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia E K _ h𝔣 _
    h1 h2 h3 h4 v w hw).2
  rw [← hin]
  refine ⟨single E v b, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_unitIdelesTrivialOn_iff]
  refine ⟨fun u hu => ?_, (single_mem E v b).1, (single_mem E v b).2⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at hu
  subst hu
  have hval : ∀ c : (u.adicCompletion E)ˣ, Valued.v (c : u.adicCompletion E) = 1 →
      ((single E u c : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 u ∈
        u.adicCompletionIntegers E := by
    intro c hc
    show (fsingle E u (c : u.adicCompletion E)) u ∈ _
    rw [fsingle_apply, Pi.mulSingle_eq_same, HeightOneSpectrum.mem_adicCompletionIntegers, hc]
  refine ⟨hval b hb, ?_⟩
  rw [← map_inv]
  apply hval
  rw [Units.val_inv_eq_inv_val, map_inv₀, hb, inv_one]

end Generic

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZN
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: local nondegeneracy of the Kummer symbol. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

theorem rootKF_pow (a : Fˣ) : (rootKF F a).β ^ ℓ = algebraMap F (KF F ℓ a) a :=
  (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec

/-- If `(a, ·)_v` is trivial then the decomposition group is trivial. -/
theorem decomp_eq_bot (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ)
    (h : ∀ b, sym F hζ v a b = 1) (w : HeightOneSpectrum (𝓞 (KF F ℓ a)))
    (hw : w.under (𝓞 F) = v) :
    haveI := isMulCommutative_KF a hζ
    NumberField.PlaceDecomp.decomp F (KF F ℓ a) w = ⊥ := by
  haveI := isMulCommutative_KF a hζ
  rw [← range_single_eq_decomp F (KF F ℓ a) v w hw, eq_bot_iff]
  rintro σ ⟨b, rfl⟩
  rw [Subgroup.mem_bot]
  apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
  rw [map_one]
  exact h b

/-- **Local nondegeneracy**: if `(a, b)_v = 1` for all `b ∈ F_vˣ` then `a` is a local `ℓ`-th
power. -/
theorem sym_nondeg (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (h : ∀ b, sym F hζ v a b = 1) :
    C0Y.emb F v a ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
  haveI := isMulCommutative_KF a hζ
  obtain ⟨w, hw⟩ := exists_under F (KF F ℓ a) v
  have hD := decomp_eq_bot F hζ v a h w hw
  subst hw
  set K := KF F ℓ a
  set y : w.adicCompletion K := algebraMap K (w.adicCompletion K) (rootKF F a).β
  have hy := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom F K w
    y).mp (fun σ => by
      have : (σ : K ≃ₐ[F] K) = 1 := by
        have h2 : (σ : K ≃ₐ[F] K) ∈ (⊥ : Subgroup (K ≃ₐ[F] K)) := by rw [← hD]; exact σ.2
        exact Subgroup.mem_bot.mp h2
      have hσ : σ = 1 := Subtype.ext this
      rw [hσ, one_smul])
  obtain ⟨c, hc⟩ := hy
  set φ := HeightOneSpectrum.Extension.adicCompletionSemialgHom F K
    (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 F) w).Extension (𝓞 K))
  have hφa : φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) a) =
      algebraMap K (w.adicCompletion K) (algebraMap F K a) := φ.commutes a
  have hcpow : φ (c ^ ℓ) = φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) a) := by
    rw [map_pow, hc, hφa, ← map_pow, rootKF_pow]
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hc' := hinj hcpow
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne ℓ), eq_comm, map_eq_zero] at hc'
    exact a.ne_zero hc'
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [hc']
  rfl

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZT
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: the Steinberg relation `(a, -a)_v = 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)
include hζ

/-- The Galois group of `F(a^{1/ℓ})` has order dividing `ℓ`. -/
theorem card_gal_dvd (a : Fˣ) : Nat.card (KF F ℓ a ≃ₐ[F] KF F ℓ a) ∣ ℓ := by
  have h1 := Subgroup.card_dvd_of_injective _ (kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a))
  have h2 : Nat.card (rootsOfUnity ℓ F) = ℓ := hζ.card_rootsOfUnity
  rw [h2] at h1
  exact h1

/-- When the Galois group has order `ℓ`: `∏_σ σ(-α) = -a`. -/
theorem prod_neg_root (a : Fˣ) (hcard : Nat.card (KF F ℓ a ≃ₐ[F] KF F ℓ a) = ℓ) :
    ∏ σ : (KF F ℓ a ≃ₐ[F] KF F ℓ a), σ (-(rootKF F a).β) = algebraMap F (KF F ℓ a) (-(a : F)) := by
  classical
  set K := KF F ℓ a
  set α := (rootKF (ℓ := ℓ) F a).β
  have hζK := hζ.map_of_injective (FaithfulSMul.algebraMap_injective F K)
  -- `σ α = ζ^{e σ} α`
  have hex : ∀ σ : K ≃ₐ[F] K, ∃ i < ℓ, ζ ^ i = ((kch hζ (rootKF F a) σ : Fˣ) : F) := by
    intro σ
    exact hζ.eq_pow_of_pow_eq_one (kval_pow hζ (rootKF F a) σ)
  choose e he heq using hex
  have hσ : ∀ σ : K ≃ₐ[F] K, σ α = algebraMap F K ζ ^ e σ * α := by
    intro σ
    rw [← map_pow, heq σ, algebraMap_kch, div_mul_cancel₀ _ (rootKF F a).ne_zero]
  let ef : (K ≃ₐ[F] K) → Fin ℓ := fun σ => ⟨e σ, he σ⟩
  have hinj : Function.Injective ef := by
    intro σ τ h
    have h' : e σ = e τ := congrArg Fin.val h
    apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
    apply Subtype.ext; apply Units.ext
    rw [← heq σ, ← heq τ, h']
  have hbij : Function.Bijective ef := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard]
  have key : (X ^ ℓ - C (algebraMap F K a)) =
      ∏ i ∈ Finset.range ℓ, (X - C (algebraMap F K ζ ^ i * α)) :=
    X_pow_sub_C_eq_prod hζK (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (rootKF_pow F a)
  have hev := congrArg (Polynomial.eval 0) key
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod, zero_sub] at hev
  rw [zero_pow (NeZero.ne ℓ), zero_sub] at hev
  calc ∏ σ : K ≃ₐ[F] K, σ (-α) = ∏ σ : K ≃ₐ[F] K, -(algebraMap F K ζ ^ (ef σ : ℕ) * α) := by
        refine Finset.prod_congr rfl fun σ _ => ?_
        rw [map_neg, hσ]
    _ = ∏ i : Fin ℓ, -(algebraMap F K ζ ^ (i : ℕ) * α) :=
        Fintype.prod_bijective ef hbij _ _ fun σ => rfl
    _ = ∏ i ∈ Finset.range ℓ, -(algebraMap F K ζ ^ i * α) :=
        Fin.prod_univ_eq_prod_range (fun i => -(algebraMap F K ζ ^ i * α)) ℓ
    _ = algebraMap F K (-(a : F)) := by
        rw [map_neg, hev]

omit hζ in
theorem smul_algebraMap {K : Type} [Field K] [NumberField K] [Algebra F K]
    (w : HeightOneSpectrum (𝓞 K)) (σ : NumberField.PlaceDecomp.decomp F K w) (y : K) :
    σ • algebraMap K (w.adicCompletion K) y = algebraMap K (w.adicCompletion K) ((σ : K ≃ₐ[F] K) y) := by
  rw [NumberField.PlaceDecomp.smul_def]
  exact NumberField.PlaceDecomp.actRingEquiv_coe σ (WithVal.toVal _ y)

/-- **Steinberg**: `(a, -a)_v = 1`. -/
theorem sym_steinberg (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    sym F hζ v a (C0Y.emb F v (-a)) = 1 := by
  classical
  haveI := isMulCommutative_KF a hζ
  set K := KF F ℓ a
  obtain ⟨w, hw⟩ := exists_under F K v
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec F K
  have hr : artinMap F K (single F v (C0Y.emb F v (-a))) = 1 := by
    rw [idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq F K _ h𝔣 _ h1 h2 h3 h4 v _ _
      (single_mem F v _) (finPart_single F v _) w hw]
    set φ := HeightOneSpectrum.Extension.adicCompletionSemialgHom F K
      (⟨w, hw⟩ : v.Extension (𝓞 K))
    have hφ : φ ((C0Y.emb F v (-a) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        algebraMap K (w.adicCompletion K) (algebraMap F K (-(a : F))) := φ.commutes _
    rw [hφ]
    have hne : ∀ y : K, y ≠ 0 → algebraMap K (w.adicCompletion K) y ≠ 0 := fun y hy => by
      rwa [Ne, map_eq_zero]
    by_cases hD : NumberField.PlaceDecomp.decomp F K w = ⊥
    · refine ⟨Units.mk0 (algebraMap K (w.adicCompletion K) (algebraMap F K (-(a : F))))
        (hne _ (by simp)), ?_⟩
      rw [finprod_eq_single _ 1 (fun σ hσ => absurd (Subtype.ext (by
        have h2 : (σ : K ≃ₐ[F] K) ∈ (⊥ : Subgroup (K ≃ₐ[F] K)) := by rw [← hD]; exact σ.2
        exact Subgroup.mem_bot.mp h2)) hσ)]
      rw [one_smul, Units.val_mk0]
    · have hG := card_gal_dvd F hζ a
      have hDG : Nat.card (NumberField.PlaceDecomp.decomp F K w) ∣ Nat.card (K ≃ₐ[F] K) :=
        Subgroup.card_subgroup_dvd_card _
      have hD1 : Nat.card (NumberField.PlaceDecomp.decomp F K w) ≠ 1 := fun h =>
        hD (Subgroup.card_eq_one.mp h)
      have hDl : Nat.card (NumberField.PlaceDecomp.decomp F K w) = ℓ :=
        ((hℓ.eq_one_or_self_of_dvd _ (hDG.trans hG)).resolve_left hD1)
      have hGl : Nat.card (K ≃ₐ[F] K) = ℓ :=
        Nat.dvd_antisymm hG (by have h := hDG; rw [hDl] at h; exact h)
      have hDtop : NumberField.PlaceDecomp.decomp F K w = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (hDl.trans hGl.symm)
      have hα0 : -(rootKF (ℓ := ℓ) F a).β ≠ 0 := neg_ne_zero.mpr (rootKF F a).ne_zero
      refine ⟨Units.mk0 _ (hne _ hα0), ?_⟩
      rw [finprod_eq_prod_of_fintype, Units.coe_prod]
      simp only [NumberField.PlaceDecomp.coe_smul_units, Units.val_mk0, smul_algebraMap]
      rw [← map_prod, ← prod_neg_root F hζ a hGl]
      congr 1
      refine Fintype.prod_bijective Subtype.val ⟨Subtype.val_injective, fun σ =>
        ⟨⟨σ, by rw [hDtop]; trivial⟩, rfl⟩⟩ _ _ fun σ => rfl
  show kch hζ (rootKF F a) (artinMap F K (single F v (C0Y.emb F v (-a)))) = 1
  rw [hr, map_one]

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZU
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: Kummer extensions are unramified at `v ∤ ℓ a`; the unit–unit symbol. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

/-- `n`-th roots of unity congruent modulo `Q` with `n ∉ Q` are equal. -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {n : ℕ}
    (hn : (n : R) ∉ Q) {a b : R} (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : a - b ∈ Q) : a = b := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  set η := b * a ^ (n - 1) with hη
  have han : a ^ (n - 1) * a = 1 := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), ha]
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ (n - 1) * (a - b) := by
      rw [hη, mul_sub, han]; ring
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · calc a = a * 1 := (mul_one a).symm
      _ = a * η := by rw [hη1]
      _ = b * (a ^ (n - 1) * a) := by rw [hη]; ring
      _ = b := by rw [han, mul_one]
  · exfalso
    have hηn : η ^ n = 1 := by
      rw [hη, mul_pow, ← pow_mul, hb, one_mul, mul_comm, pow_mul, ha, one_pow]
    have hsum : ∑ i ∈ Finset.range n, η ^ i = 0 := by
      have h := geom_sum_mul η n
      rw [hηn, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hη1)
    apply hn
    have : (n : R) = ∑ i ∈ Finset.range n, (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
    rw [this]
    refine Q.sum_mem fun i _ => ?_
    rw [← geom_sum_mul_neg]
    exact Q.mul_mem_left _ h1

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- An integral Kummer generator `β = d α` at a place where `a` is a unit. -/
theorem exists_intGen (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    ∃ (d n : 𝓞 F) (β : 𝓞 (KF F ℓ a)), d ∉ v.asIdeal ∧ n ∉ v.asIdeal ∧
      (a : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n ∧
      (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β ∧
      β ^ ℓ = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (d ^ (ℓ - 1) * n) := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (a : F) ha.le
  have hd : (d : 𝓞 F) ∉ v.asIdeal := d.2
  have hn : n ∉ v.asIdeal := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, ha,
      (v.valuation_eq_one_iff_notMem (K := F)).mpr hd, one_mul]
  set K := KF F ℓ a
  set β : K := algebraMap F K (algebraMap (𝓞 F) F d) * (rootKF F a).β
  have hβpow : β ^ ℓ = algebraMap F K (algebraMap (𝓞 F) F ((d : 𝓞 F) ^ (ℓ - 1) * n)) := by
    have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm
    rw [mul_pow, rootKF_pow, ← map_pow, ← map_mul]
    congr 1
    rw [map_mul, map_pow, ← hnd]
    conv_lhs => rw [hℓ1, pow_succ]
    ring
  have hint : IsIntegral ℤ β := by
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow, ← IsScalarTower.algebraMap_apply]
    exact ((((d : 𝓞 F) ^ (ℓ - 1) * n).isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F K))
  refine ⟨d, n, ⟨β, hint⟩, hd, hn, hnd, rfl, ?_⟩
  apply RingOfIntegers.ext
  simp only [map_pow]
  show β ^ ℓ = _
  rw [hβpow, ← IsScalarTower.algebraMap_apply]
  rfl

omit [NumberField F] in
theorem rootO_pow (μ : rootsOfUnity ℓ F) : rootO F μ ^ ℓ = 1 := by
  apply RingOfIntegers.ext
  show ((μ : Fˣ) : F) ^ ℓ = 1
  have := μ.2; rw [mem_rootsOfUnity] at this
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

include hζ in
/-- `σ β = μ_σ β` in `𝓞 K`. -/
theorem smul_intGen (a : Fˣ) (d : 𝓞 F) (β : 𝓞 (KF F ℓ a))
    (hβ : (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β)
    (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a) :
    σ • β = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ)) * β := by
  apply RingOfIntegers.ext
  have e : ∀ x : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x : 𝓞 (KF F ℓ a)) : KF F ℓ a) =
      algebraMap F (KF F ℓ a) (x : F) := fun x => rfl
  show σ (β : KF F ℓ a) = ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) _ : 𝓞 (KF F ℓ a)) : KF F ℓ a) *
    (β : KF F ℓ a)
  rw [e, hβ]
  show σ _ = algebraMap F (KF F ℓ a) ((kch hζ (rootKF F a) σ : Fˣ) : F) * _
  rw [algebraMap_kch, map_mul, AlgEquiv.commutes]
  field_simp [(rootKF (ℓ := ℓ) F a).ne_zero]

include hζ in
/-- **Kummer extensions are unramified** at `v ∤ ℓ` where `a` is a unit. -/
theorem inertia_eq_bot (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) (w : HeightOneSpectrum (𝓞 (KF F ℓ a)))
    (hw : w.under (𝓞 F) = v) :
    w.asIdeal.inertia (KF F ℓ a ≃ₐ[F] KF F ℓ a) = ⊥ := by
  obtain ⟨d, n, β, hd, hn, -, hβ, hβpow⟩ := exists_intGen (ℓ := ℓ) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ ℓ ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow] at this
    have h2 := hmem _ this
    rcases v.isPrime.mem_or_mem h2 with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have h1 := hσ β
  rw [smul_intGen F hζ a d β hβ σ] at h1
  have h2 : (algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ) - 1)) * β ∈
      w.asIdeal := by rw [map_sub, map_one, sub_mul, one_mul]; exact h1
  rcases w.isPrime.mem_or_mem h2 with h3 | h3
  · have h4 := hmem _ h3
    have h5 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F _) (one_pow ℓ) h4
    apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
    rw [map_one]
    apply Subtype.ext; apply Units.ext
    have := congrArg (fun z : 𝓞 F => (z : F)) h5
    exact this
  · exact absurd h3 hβw

include hζ in
/-- Symbols of two units at `v ∤ ℓ` are trivial. -/
theorem sym_unit_unit (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a b : Fˣ)
    (ha : v.valuation F (a : F) = 1) (hb : v.valuation F (b : F) = 1) :
    sym F hζ v a (C0Y.emb F v b) = 1 := by
  haveI := isMulCommutative_KF a hζ
  obtain ⟨w, hw⟩ := exists_under F (KF F ℓ a) v
  have hmem := single_unit_mem_inertia F (KF F ℓ a) v w hw (C0Y.emb F v b) (by
    show Valued.v ((b : F) : v.adicCompletion F) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hb])
  rw [inertia_eq_bot F hζ v hv a ha w hw, Subgroup.mem_bot] at hmem
  show kch hζ (rootKF F a) (artinMap F (KF F ℓ a) (single F v (C0Y.emb F v b))) = 1
  rw [hmem, map_one]

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZV
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: the tame formula `(a, π)_v ≡ a^{(Nv - 1)/ℓ} (mod v)` at `v ∤ ℓ`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

omit [NumberField F] in
theorem toO_pow (x : F) (hx : x ^ ℓ = 1) : toO F x hx ^ ℓ = 1 := by
  apply RingOfIntegers.ext; show x ^ ℓ = 1; exact hx

include hζ in
/-- `ℓ ∣ N v - 1` when `v ∤ ℓ`. -/
theorem dvd_card_sub_one (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) :
    ℓ ∣ Nat.card (𝓞 F ⧸ v.asIdeal) - 1 := by
  classical
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  set z := toO F ζ hζ.pow_eq_one
  have hz : z ^ ℓ = 1 := toO_pow F ζ _
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal z) ℓ := by
    refine ⟨by rw [← map_pow, hz, map_one], fun l hl => ?_⟩
    have h1 : z ^ l - 1 ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hl, map_one, sub_self]
    have h2 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv
      (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (one_pow ℓ) h1
    apply hζ.dvd_of_pow_eq_one
    have := congrArg (fun x : 𝓞 F => (x : F)) h2
    simpa [z, toO] using this
  have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk v.asIdeal z)
    (hη.ne_zero (NeZero.ne ℓ))
  rw [Fintype.card_eq_nat_card] at this
  exact hη.dvd_of_pow_eq_one _ this

include hζ in
/-- The place over `v` used for the Frobenius. -/
theorem placeOrd_single (v : HeightOneSpectrum (𝓞 F)) (π : Fˣ)
    (hπ : v.valuation F (π : F) = WithZero.exp (-1 : ℤ)) :
    placeOrd F (projFin F (single F v (C0Y.emb F v π))) v = 1 := by
  classical
  unfold placeOrd
  have : ((projFin F (single F v (C0Y.emb F v π)) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v = ((π : F) : v.adicCompletion F) := by
    show (fsingle F v ((C0Y.emb F v π : (v.adicCompletion F)ˣ) : v.adicCompletion F)) v = _
    rw [fsingle_apply, Pi.mulSingle_eq_same]
    rfl
  rw [this, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, WithZero.log_exp]
  norm_num

include hζ in
/-- **Tame formula.** -/
theorem sym_tame (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a π : Fˣ) (ω : F)
    (ha : v.valuation F (a : F) = 1) (hπ : v.valuation F (π : F) = WithZero.exp (-1 : ℤ))
    (hω : ω ^ ℓ = 1)
    (hcong : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / ℓ) - ω) < 1) :
    ((sym F hζ v a (C0Y.emb F v π) : Fˣ) : F) = ω := by
  classical
  haveI := isMulCommutative_KF a hζ
  set K := KF F ℓ a
  set Q := primeAbove F K v
  let w : HeightOneSpectrum (𝓞 K) := ⟨Q, (primeAbove_isMaximal F K v).isPrime, primeAbove_ne_bot F K v⟩
  have hw : w.under (𝓞 F) = v := by ext1; exact under_primeAbove F K v
  have hQv : Q.under (𝓞 F) = v.asIdeal := under_primeAbove F K v
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec F K
  set φ := artinFrob F K v
  have hφ : IsArithFrobAt (𝓞 F) φ w.asIdeal := isArithFrobAt_artinFrob F K v
  have hin := idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt F K _ h𝔣 _ h1 h2 h3 h4
    v (C0Y.emb F v π) (single F v (C0Y.emb F v π)) (single_mem F v _) (finPart_single F v _) w hw φ hφ
  rw [placeOrd_single F hζ v π hπ, inertia_eq_bot F hζ v hv a ha w hw, Subgroup.mem_bot,
    zpow_one, mul_inv_eq_one] at hin
  show ((kch hζ (rootKF F a) (artinMap F K (single F v (C0Y.emb F v π))) : Fˣ) : F) = ω
  rw [hin]
  -- the Kummer value of the Frobenius
  set μ := kch hζ (rootKF F a) φ
  obtain ⟨d, n, β, hd, hn, hnd, hβ, hβpow⟩ := exists_intGen (ℓ := ℓ) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ ℓ ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow] at this
    rcases v.isPrime.mem_or_mem (hmem _ this) with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  set q := Nat.card (𝓞 F ⧸ v.asIdeal)
  have hq : q = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hFrob : ∀ x : 𝓞 K, φ • x - x ^ q ∈ w.asIdeal := by
    intro x
    have := hφ x
    rw [show w.asIdeal.under (𝓞 F) = v.asIdeal from hQv] at this
    exact this
  -- `ℓ ∣ q - 1`
  have hℓq : ℓ ∣ q - 1 := dvd_card_sub_one F hζ v hv
  obtain ⟨K', hK'⟩ := hℓq
  have hq1 : q = ℓ * K' + 1 := by
    have : 0 < q := by
      rw [hq]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    omega
  have hK'eq : (Ideal.absNorm v.asIdeal - 1) / ℓ = K' := by
    rw [← hq, hK', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  rw [hK'eq] at hcong
  set μO := rootO F μ
  have hsm := smul_intGen F hζ a d β hβ φ
  have hfb := hFrob β
  rw [hsm, hq1, pow_succ, pow_mul, hβpow] at hfb
  have hfb' : algebraMap (𝓞 F) (𝓞 K) (μO - ((d ^ (ℓ - 1) * n) ^ K')) * β ∈ w.asIdeal := by
    rw [map_sub, map_pow, sub_mul]; convert hfb using 1
  have hμA : μO - (d ^ (ℓ - 1) * n) ^ K' ∈ v.asIdeal := by
    rcases w.isPrime.mem_or_mem hfb' with h | h
    · exact hmem _ h
    · exact absurd h hβw
  -- valuations in `F`
  set D : F := algebraMap (𝓞 F) F d
  set A : F := algebraMap (𝓞 F) F ((d ^ (ℓ - 1) * n) ^ K')
  have hDv : v.valuation F D = 1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hA : A = D ^ (q - 1) * (a : F) ^ K' := by
    have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm
    simp only [A, map_pow, map_mul]
    rw [← hnd, hK']
    have e : D ^ (ℓ - 1) * ((a : F) * D) = (a : F) * D ^ ℓ := by
      conv_rhs => rw [hℓ1, pow_succ]
      ring
    rw [e, mul_pow, ← pow_mul, mul_comm]
  -- Fermat: `D^{q-1} ≡ 1`
  have hferm : v.valuation F (D ^ (q - 1) - 1) < 1 := by
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    have hmd : Ideal.Quotient.mk v.asIdeal d ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ hmd
    rw [Fintype.card_eq_nat_card, ← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal),
      Ideal.Quotient.eq] at this
    have e : D ^ (q - 1) - 1 = algebraMap (𝓞 F) F (d ^ (q - 1) - 1) := by
      simp [D]
    rw [e]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr this
  set ωO := toO F ω hω
  have hωF : algebraMap (𝓞 F) F ωO = ω := rfl
  have hωv : v.valuation F ω ≤ 1 := by rw [← hωF]; exact v.valuation_le_one (K := F) ωO
  have hAω : v.valuation F (A - ω) < 1 := by
    rw [hA]
    have e : D ^ (q - 1) * (a : F) ^ K' - ω =
        D ^ (q - 1) * ((a : F) ^ K' - ω) + (D ^ (q - 1) - 1) * ω := by ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow, hDv, one_pow, one_mul]; exact hcong
    · rw [map_mul]
      calc _ ≤ v.valuation F (D ^ (q - 1) - 1) * 1 := mul_le_mul_right hωv _
        _ < 1 := by rw [mul_one]; exact hferm
  have hμv : v.valuation F (algebraMap (𝓞 F) F μO - A) < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F) _).mpr hμA
    change v.valuation F (algebraMap (𝓞 F) F (μO - _)) < 1 at this
    rwa [map_sub] at this
  have hμω : μO - ωO ∈ v.asIdeal := by
    rw [← v.valuation_lt_one_iff_mem (K := F)]
    change v.valuation F (algebraMap (𝓞 F) F (μO - ωO)) < 1
    rw [map_sub, hωF]
    have e : algebraMap (𝓞 F) F μO - ω = (algebraMap (𝓞 F) F μO - A) + (A - ω) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hμv hAω)
  have heq := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F μ) (toO_pow F ω hω) hμω
  have := congrArg (fun x : 𝓞 F => (x : F)) heq
  simpa [μO, rootO, ωO, toO] using this

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZPkg
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! C0Z: the local-symbol package from the idelic Artin map, and C0-H. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace C0Z

/-- **The local Hilbert-symbol package exists** (from the library's idelic Artin map). -/
theorem pkgHyp : C0Y.PkgHyp := by
  intro F _ _ ℓ hℓ hζ' hcx
  obtain ⟨ζ, hζ⟩ := hζ'
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact ⟨{ h := symHom F hζ
           steinberg := fun v a => sym_steinberg F hζ hℓ v a
           prod_eq_one := fun a b T hT => prod_sym_eq_one F hζ hcx a b T hT
           nondeg := fun v a h => sym_nondeg F hζ v a h
           unit_unit := fun v hv a b ha hb => sym_unit_unit F hζ v hv a b ha hb
           tame := fun v hv a π ω ha hπ hω hc => sym_tame F hζ v hv a π ω ha hπ hω hc }⟩

end C0Z
end
end

section
-- module Solutions.Artin.KP.A_Pkg
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-A: the global cubic symbol package and the `S`-Hilbert pairing

`CubicPkg F` is a universe-polymorphic, completion-free form of `C0Y.SymbolPkg F 3`: local cubic
Hilbert symbols `hv v : Fˣ →* Fˣ →* μ₃(F)` evaluated on *global* elements, with Steinberg, the
product formula, triviality on units and the tame formula at places prime to `3`, and local
constancy (`deep`).  Everything in WP-A is derived from a `CubicPkg`.

The orientation is pinned by the field `tame`: `hv v a π ≡ a^{(Nv-1)/3} (mod v)` for a `v`-unit
`a` and a uniformizer `π`.

Main results: `CubicPkg.skew`, `CubicPkg.self`, `CubicPkg.isTame` (the bridge to `A_Local`),
`CubicPkg.tame_zpow` (A1 for a unit against any element), `CubicPkg.tame_formula` (A1),
`CubicPkg.HS` (the pairing `(a,b)_S`), `CubicPkg.HS_mul_prod` (A2, product formula),
`CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`, `CubicPkg.exists_isDeepLevel`,
`CubicPkg.HS_deep_right/left` (A4).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable (F : Type*) [Field F] [NumberField F]

variable {F}

namespace CubicPkg

variable (P : CubicPkg F)

/-! ### The `S`-part -/

/-! ### Deep units -/

theorem IsDeepLevel.mono {𝔪 : Ideal (𝓞 F)} {N N' : ℕ} (h : P.IsDeepLevel 𝔪 N) (hN : N ≤ N') :
    P.IsDeepLevel 𝔪 N' := fun v hv a b hb =>
  h v hv a b (hb.trans (by rw [WithZero.exp_le_exp]; omega))

end CubicPkg

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Exist
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-A: existence of the cubic package for `F : Type`

`CubicPkg F` is obtained from `C0Y.SymbolPkg F 3` (`C0Z.pkgHyp`, built on the library's idelic
Artin map, which lives in universe `0`).  The field `deep` comes from the openness of the cubes
in `(F_v)ˣ` (library statement `NumberField.isOpen_range_powMonoidHom_units_adicCompletion`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace ArtinKP.A

variable {F : Type} [Field F] [NumberField F]

/-- **Existence of the cubic package** for totally complex `F : Type` containing `μ₃`. -/
theorem nonempty_cubicPkg (F : Type) [Field F] [NumberField F]
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ 3) (hcx : ∀ w : InfinitePlace F, w.IsComplex) :
    Nonempty (CubicPkg F) :=
  (C0Z.pkgHyp F 3 Nat.prime_three hζ hcx).map ofSymbolPkg

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Residue
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-A: the exterior cubic residue symbol and reciprocity

* `Good 𝔪`: the standing hypotheses on the modulus (`𝔪 ≠ ⊥`, every prime over `6` divides `𝔪`,
  `R = SInt 𝔪` is a PID in the form "every extended ideal is principal");
  `exists_cutoff_good` gives it from `SmallPrimesDvd N₀ 𝔪`.
* `cubicExt ι 𝔪 d c = ∏_{P ∉ S, P ∣ c} χ_P(d)^{2 v_P(c)}` in terms of the goal's
  `sexticResidueSymbol`.
* `cubicExt_eq_prod`: `(d/c) = ι ∏_v (d, c)_v` over the exterior places dividing `c`.
* `cubicExt_reciprocity` (A3): `(d/c) = (c/d) · (c, d)_S` — with the orientation of `CubicPkg`
  the sign in MATH.md (A3) is `+1`.
* unit laws, multiplicativity, dependence on `d mod c` only.

The first section is a universe-polymorphic copy of `C0Y.val_generator`, `C0Y.sextic_spec`
(`Solutions/Artin/C0/C0YR.lean`, stated there for `F : Type`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-- `Good 𝔪` holds as soon as `𝔪` is divisible by all primes of small norm. -/
theorem exists_cutoff_good (F : Type*) [Field F] [NumberField F] :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → Good 𝔪 := by
  obtain ⟨N₁, hN₁⟩ := exists_cutoff_isPrincipal_map F
  refine ⟨max N₁ (Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})), fun 𝔪 h𝔪 hs =>
    ⟨h𝔪, fun v h6 => ?_, hN₁ 𝔪 h𝔪 fun P hP h0 hN => hs P hP h0 (hN.trans (le_max_left _ _))⟩⟩
  apply hs v.asIdeal v.isPrime v.ne_bot
  have h60 : Ideal.span {(6 : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h0
    have := congrArg (algebraMap (𝓞 F) F) h0
    simp at this
  have hle : Ideal.span {(6 : 𝓞 F)} ≤ v.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h6
  have hn0 : Ideal.absNorm (Ideal.span {(6 : 𝓞 F)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact h60
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Ideal.absNorm_dvd_absNorm_of_le hle)).trans
    (le_max_right _ _)

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Transport
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S.brk_neg_left _root_.ArtinKP.S.brk_neg_right _root_.ArtinKP.S.brk_one_left _root_.ArtinKP.S.brk_one_right _root_.ArtinKP.S.brk_pow_three_left _root_.ArtinKP.S.brk_pow_three_right _root_.ArtinKP.S.brk_self _root_.ArtinKP.S.brk_zero_left _root_.ArtinKP.S.brk_zero_right _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-A: transport of the cubic package along a field isomorphism; existence in every universe

`CubicPkg.transport e P'` moves a package along `e : F ≃+* F'`.  With
`F ≃+* CyclotomicField n ℚ` this gives `nonempty_cubicPkg_cyclotomic` for `F : Type*`
(the library's Artin map, hence `C0Z.pkgHyp`, only exists for `F : Type`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

/-- **Existence of the cubic package** for cyclotomic `F ⊇ μ₁₂` in any universe. -/
theorem nonempty_cubicPkg_of_isCyclotomicExtension (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] :
    Nonempty (CubicPkg F) := by
  have : NeZero n := ⟨hn0.ne'⟩
  have : NeZero ((n : ℚ)) := ⟨by exact_mod_cast hn0.ne'⟩
  have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let e : F ≃+* CyclotomicField n ℚ :=
    (IsCyclotomicExtension.algEquiv {n} ℚ F (CyclotomicField n ℚ)).toRingEquiv
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  have h3 : ∃ z : CyclotomicField n ℚ, IsPrimitiveRoot z 3 := by
    obtain ⟨m, hm⟩ : 3 ∣ n := dvd_trans (by norm_num) hn
    exact ⟨_, hζ.pow hn0 (by rw [hm, mul_comm])⟩
  have hcx : ∀ w : InfinitePlace (CyclotomicField n ℚ), w.IsComplex :=
    (IsCyclotomicExtension.Rat.isTotallyComplex (n := n) (CyclotomicField n ℚ)
      (lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd hn0 hn))).isComplex
  exact (nonempty_cubicPkg (CyclotomicField n ℚ) h3 hcx).map (CubicPkg.transport e)

end ArtinKP.A
end
end

section
-- module Solutions.Artin.T12.C3B_Unit
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end residue

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3B_Good
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- A prime of norm divisible by the rational prime `p` has norm at most `p^[F:ℚ]`. -/
theorem absNorm_le_of_prime_dvd (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    [P.IsMaximal] (hpd : p ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ p ^ Module.finrank ℤ (𝓞 F) := by
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard := card_quot P hP0
  obtain ⟨f, hq, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at hpd
  have hpq : p = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd)
  have hp0 : ((p : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [hpq]; exact ringChar.Nat.cast_ringChar
  have hmem : (p : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  have hle : Ideal.span {(p : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (p : 𝓞 F) = algebraMap ℤ (𝓞 F) p by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  exact Nat.le_of_dvd (pow_pos hp.pos _) hdvd

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Cut
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3I_Cut: the cutoff — exterior primes of `ℚ(μ_n)`, `12 ∣ n`, are good

`N₀ = max(3^[F:ℚ], N 𝔇)`: an exterior prime has norm `> N₀`, so it lies over neither `2` nor `3`
(`12 ∣ N P − 1`) and does not divide the different. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F] (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 12 := by
    have c2 : Q.Coprime 2 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 c2) c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ12 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 12)) 12 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ12.toInteger 12 := hζ12.toInteger_isPrimitiveRoot
  have hQ1 : Q ≠ 1 := by
    have : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
    omega
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk hQ1 hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- A primitive sixth root of unity in `𝓞 F`. -/
theorem exists_prim_six (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F] :
    ∃ ω : 𝓞 F, IsPrimitiveRoot ω 6 := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  exact ⟨hζ6.toInteger, hζ6.toInteger_isPrimitiveRoot⟩

/-- Exterior primes are good once `N₀ ≥ cutN F`. -/
theorem good_of_exterior (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {N₀ : ℕ} (hN₀ : cutN F ≤ N₀) {𝔪 : Ideal (𝓞 F)} (hsm : SmallPrimesDvd N₀ 𝔪)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hext : IsExterior 𝔪 P) :
    Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)) := by
  have hbig : N₀ < Ideal.absNorm P := by
    by_contra hcon
    apply hP.ne_top
    rw [eq_top_iff, ← hext.2]
    exact sup_le le_rfl (hsm P hP hext.1 (by omega))
  have h1 : 3 ^ Module.finrank ℤ (𝓞 F) ≤ cutN F := le_max_left _ _
  have h2 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≤ cutN F := le_max_right _ _
  refine ⟨hext.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hext.1 (by omega), ?_⟩
  intro hD
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hD
  have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
  change Ideal.absNorm P ≤ _ at this
  omega

end C3I

open NumberField

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.DD_Cut
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-DD, part 1: the different is supported in `S` once the cut-off is large

* `DiffInS 𝔪`: no prime outside `placesOf 𝔪` divides the different of `F`. This is, verbatim,
  the hypothesis `hdiff` of `C9_Dual` (`C9.dualCover_of_transLevel`, `C9.theta_eq_zero_of_tau'`).
* `cutD F = N(𝔡_F)`; `diffInS_of_smallPrimesDvd : cutD F ≤ N → SmallPrimesDvd N 𝔪 → DiffInS 𝔪`.
* `smallPrimesDvd_mono`; `exists_cutoff_diffInS`, and the combined, monotone form
  `exists_cutoff_good_diffInS : ∃ N₁, ∀ N, N₁ ≤ N → ∀ 𝔪 ≠ ⊥, SmallPrimesDvd N 𝔪 → Good 𝔪 ∧ DiffInS 𝔪`.
* `diffInS_of_cutN`: the cut-off `C3I.cutN F` already used at assembly (`H_Aut`) is enough;
  `diffInS_of_good`: the alternative source `C3I.Good.diff` at every exterior prime.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

namespace ArtinKP.DD

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-- The same, positively: every prime dividing the different divides `𝔪`. -/
theorem diffInS_iff {𝔪 : Ideal (𝓞 F)} :
    DiffInS 𝔪 ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → 𝔪 ≤ v.asIdeal :=
  ⟨fun h v hv => by_contra fun hn => h v hn hv, fun h v hv hd => hv (h v hd)⟩

/-- Every prime dividing the different has norm at most `cutD F`. -/
theorem absNorm_le_cutD (v : HeightOneSpectrum (𝓞 F))
    (hv : differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) : Ideal.absNorm v.asIdeal ≤ cutD F := by
  have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) (Ideal.absNorm_dvd_absNorm_of_le hv)

/-- **The different is supported in `S`** as soon as the cut-off is at least `cutD F`. -/
theorem diffInS_of_smallPrimesDvd {N : ℕ} (hN : cutD F ≤ N) {𝔪 : Ideal (𝓞 F)}
    (hs : SmallPrimesDvd N 𝔪) : DiffInS 𝔪 :=
  diffInS_iff.mpr fun v hv =>
    hs v.asIdeal v.isPrime v.ne_bot ((absNorm_le_cutD v hv).trans hN)

/-- The assembly's cut-off `C3I.cutN F` (`H_Aut`, `L3*`) dominates `cutD F`. -/
theorem cutD_le_cutN (F : Type*) [Field F] [NumberField F] : cutD F ≤ C3I.cutN F :=
  le_max_right _ _

theorem diffInS_of_cutN {N : ℕ} (hN : C3I.cutN F ≤ N) {𝔪 : Ideal (𝓞 F)}
    (hs : SmallPrimesDvd N 𝔪) : DiffInS 𝔪 :=
  diffInS_of_smallPrimesDvd ((cutD_le_cutN F).trans hN) hs

end ArtinKP.DD
end

section
-- module Solutions.Artin.T12.C3M_Base
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

lemma exterior_of_mem_factors {𝔞 Q : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (hQ : Q ∈ normalizedFactors 𝔞) : Q.IsPrime ∧ IsExterior 𝔪 Q := by
  have hpr : Prime Q := prime_of_normalized_factor Q hQ
  refine ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero, ?_⟩
  have hle : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  exact eq_top_iff.mpr (h𝔞.2 ▸ sup_le_sup_right hle 𝔪)

/-! ### Residue symbols -/

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.GK_J
/-! # WP-GK, file 2: the function `J` and its majorant `bf` (MATH3 §4)

For a section `Φ₀` and a level `k`:

* `Jdef hG hz6 Φ₀ cl y' = (−1)^r · ⟨ν̃, η′⟩ · ξ_{wΦ₀}(η′)` with chosen representatives `ν̃` of
  `cl : SFinCls 𝔪 k` and `η′` of `y' : SFin 𝔪 k` (MATH3 (2d)).
* `exists_bf_J`: a majorant `bf` on `SFin 𝔪 k` with `‖J cl y‖ ≤ bf y` and `Σ bf · |y|^σ < ∞` for
  `σ > −1/3`, for every section `Φ₀` (no hypothesis on `Φ₀`).
* `xi_w_inv` — **(INV)** for `ξ`: `ξ_{wΦ₀}(βu) = ξ_{wΦ₀}(β)` for `u ∈ U_k`, `Φ₀` a delta section.
* `Jdef_mk` — **well-definedness**: for a delta section `Φ₀` (level `k`, `k + 1` deep) and any
  representatives `x, η ∈ F^×`: `J([x], [η]) = (−1)^r ⟨x, η⟩ ξ_{wΦ₀}(η)`.
* `xi_w_PhiY` — MATH3 (4.1): `ξ_{wΦ_{y_f}}(ν̃) = ⟨ν̃, β₀⟩⁻¹ ξ_{wΦ₀}(ν̃/β₀)` for
  `Φ_{y_f} = |β₀|^{1/3} Ã(β₀) Φ₀`, and its `J`-form `xi_w_PhiY_eq_J`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {k : ℕ}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **`‖J cl y‖ ≤ bf y`** — the cut's first clause, literal form. -/
theorem norm_J_le (Φ₀ : GSection ι P 𝔪) (k : ℕ) :
    ∀ (cl : SFinCls 𝔪 k) (y : SFin 𝔪 k), ‖Jdef hG hz6 Φ₀ cl y‖ ≤ bfdef hG hz6 Φ₀ k y :=
  (Classical.choose_spec (exists_summable_majorant_norm_jdef hG hz6 Φ₀ k)).1

/-- **`Σ_y bf(y) |y|^σ < ∞` for `σ ≥ −1/4`** — the cut's second clause with `α = 1/4`,
literal form. -/
theorem summable_bf (Φ₀ : GSection ι P 𝔪) (k : ℕ) :
    ∀ σ : ℝ, -(1 / 4 : ℝ) ≤ σ →
      Summable (fun y => bfdef hG hz6 Φ₀ k y * (SFin.norm y) ^ σ) :=
  fun σ hσ => (Classical.choose_spec (exists_summable_majorant_norm_jdef hG hz6 Φ₀ k)).2 σ (by linarith)

/-! ### (INV) and well-definedness for a delta section -/

end

end ArtinKP.GK
end

section
-- module Solutions.Artin.KP.GK_Main
/-! # WP-GK, file 3: the setting of the cut, the assembled section data, axiom check

* `exists_cutoff`: one cut-off `N₀` after which `Good 𝔪`, every exterior prime is `C3I.Good`, and
  `DD.DiffInS 𝔪` (for `F = ℚ(ζ_n)`, `12 ∣ n`).
* `exists_data`: for `SmallPrimesDvd N₀ 𝔪`, a deep level `k + 1` and `g : AllowedGen ι 𝔪`:
  the delta section `Φ₀`, Theorem E, (INV), `J := Jdef hG hz6 Φ₀`, `bf := bfdef hG hz6 Φ₀ k` with
  the two clauses of `HB.SecCut` in literal form (`α = 1/4`), well-definedness of `J`, and
  MATH3 (4.1).
* `exists_secData`: the same in the quantifier pattern of `HB.SecCut` (`∃ N₀, ∀ 𝔪 …, ∀ g,
  ∃ k₀, ∀ k ≥ k₀`), the `CubicPkg` chosen first.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.B7

noncomputable section

/-- **The setting of the cut**: after one cut-off, `Good 𝔪`, all exterior primes are good, and
the different is supported in `S`. -/
theorem exists_cutoff (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      Good 𝔪 ∧
      (∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
        C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F))) ∧
      DD.DiffInS 𝔪 := by
  obtain ⟨N₁, hGood⟩ := A.exists_cutoff_good F
  refine ⟨max N₁ (C3I.cutN F), fun 𝔪 h𝔪 hs => ⟨hGood 𝔪 h𝔪 ?_, ?_, ?_⟩⟩
  · exact fun Q hQ hQ0 hle => hs Q hQ hQ0 (hle.trans (le_max_left _ _))
  · exact fun Q hQ hext => C3I.good_of_exterior n hn0 hn (le_max_right _ _) hs hQ hext
  · exact DD.diffInS_of_cutN (le_max_right _ _) hs

end

end ArtinKP.GK
end

section
-- module Solutions.Artin.KP.HB_C
/-! # WP-HB, file 4: the element `c_v` of a digit vector

MATH3 §3.1.  For a digit vector `v ∈ Dig 𝔪 𝔟`: `D = {P ∣ 𝔟 : v_P ≠ 0}`,
`c_v = ∏_{P ∈ D} gen P = cdig g 𝔟 v` (as a product over all `P ∣ 𝔟` of `cfac P ∈ {1, gen P}`),
`ccof P = c_v / cfac P`.

* `val_cdig`, `vP_cdig`: `v_P(c_v) = 1` for `P ∈ D` and `0` at the other exterior primes;
* `cubicExt_cdig`: `(d / c_v) = ∏_{P ∈ D} χ_P(d)²` (so `κ(γ) = ∏_{P ∈ D} χ_P(d)^{−2}`);
* `exists_pf`: partial fractions, `e(r / c_v) = ∏_{P ∈ D} e(r m_P / p_P)` with
  `m_P · ccof P ≡ 1 mod P`.

(`res_cdig_xdig` is in `HB_Loc`, `exists_gamma` in `HB_Refl`.) -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

theorem pidx_ext {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (P : PIdx 𝔟) :
    P.1.IsPrime ∧ IsExterior 𝔪 P.1 :=
  C3M.exterior_of_mem_factors h𝔟 (Multiset.mem_toFinset.1 P.2)

theorem cfac_ne_zero (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) (P : PIdx 𝔟) : (cfac g 𝔟 v P : F) ≠ 0 := by
  unfold cfac
  split_ifs
  · simp
  · exact C3B.gen_ne_zero g P.1 (pidx_ext h𝔟 P).2

theorem coe_cdig (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟) :
    ((cdig g 𝔟 v : SInt 𝔪) : F) = ∏ P : PIdx 𝔟, (cfac g 𝔟 v P : F) := by
  unfold cdig
  exact map_prod ((placesOf 𝔪).integer F).subtype _ _

theorem cdig_ne_zero (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) : (cdig g 𝔟 v : F) ≠ 0 := by
  rw [coe_cdig]
  exact Finset.prod_ne_zero_iff.2 fun P _ => cfac_ne_zero g h𝔟 v P

/-! ### The Kubota symbol of `γ_v` -/

/-! ### Partial fractions -/

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.GR_Main
/-! # WP-GR, file 4: the final assembly

* `weylFlip`: the named hypothesis `GR.WeylFlip` discharged by `GW.weyl_flip_thetaT`.
* **`secCut : HB.SecCut n F ι`** — `c = 4π`, `α = 1/4`, `J = GK.Jdef hG hz6 Φ₀`,
  `bf = GK.bfdef hG hz6 Φ₀ k`, `Θ = GR.ThetaG hG hz6 m Φ₀`, `k₀` a deep level of the symbol package.
* `autCut2`, `kpCutNu`, and **`goal`**: the frozen statement 8b3180bd, written out (checked against the stub in `GR_Check`).
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.G2a

noncomputable section

/-- **The section-level cut `HB.SecCut`** (the target of package G). -/
theorem secCut_of_isCyclotomicExtension_oai (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    HB.SecCut n F ι := by
  have : NeZero n := ⟨hn0.ne'⟩
  have : IsTotallyComplex F := IsCyclotomicExtension.Rat.isTotallyComplex (n := n) F
    (by have := Nat.le_of_dvd hn0 hn; omega)
  obtain ⟨Pk⟩ := A.nonempty_cubicPkg_of_isCyclotomicExtension n hn0 hn F
  obtain ⟨z6, hz6⟩ := C3I.exists_prim_six n hn0 hn (F := F)
  obtain ⟨N₀, hN₀⟩ := GK.exists_cutoff n hn0 hn F
  refine ⟨N₀, fun 𝔪 h𝔪 hs g => ?_⟩
  obtain ⟨hG, hgood, hd⟩ := hN₀ 𝔪 h𝔪 hs
  obtain ⟨N, -, hN⟩ := Pk.exists_isDeepLevel hG.ne_bot
  refine ⟨N, fun k hk => ?_⟩
  have hk' : Pk.IsDeepLevel 𝔪 (k + 1) := CubicPkg.IsDeepLevel.mono Pk hN (by omega)
  obtain ⟨Φ₀, hΦ₀⟩ := GK.exists_isDelta (ι := ι) hG hz6 g hgood hd k hk'
  have hE : ThmE hG hz6 g Pk := thmE hG hz6 g hgood
  refine ⟨4 * Real.pi, 1 / 4, by positivity, by norm_num, by norm_num, fun m hm => ?_⟩
  refine ⟨GK.Jdef hG hz6 Φ₀, GK.bfdef hG hz6 Φ₀ k, GK.norm_J_le hG hz6 Φ₀ k,
    GK.summable_bf hG hz6 Φ₀ k, Pk, ThetaG hG hz6 m Φ₀, ?_, ?_⟩
  · intro 𝔟 _ v y
    have h := thetaG_eq_tsum_forward hE hk' hΦ₀ m hm (-(H.xdig g 𝔟 v)) y
    simp only [mul_neg, neg_neg] at h
    exact h
  · intro 𝔟 h𝔟 v γ hc hd' y
    have hcF : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0 := by
      rw [hc]; exact HB.cdig_ne_zero g h𝔟 v
    have h := thetaG_eq_tsum_reflected hE hgood hd (weylFlip_of_thmE hE) hk' hΦ₀ m hm (-(H.xdig g 𝔟 v)) γ hcF
      (by rw [hd', hc]; ring) y
    rw [hc] at h
    exact h

end

end ArtinKP.GR
end

theorem solution.{u_1} : type_of% @ArtinKP.GR.secCut_of_isCyclotomicExtension_oai.{u_1} := @ArtinKP.GR.secCut_of_isCyclotomicExtension_oai.{u_1}
