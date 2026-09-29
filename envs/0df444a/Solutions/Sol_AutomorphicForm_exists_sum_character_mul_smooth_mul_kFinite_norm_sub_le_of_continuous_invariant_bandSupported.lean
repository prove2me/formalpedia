-- Prove2me | solution 1 for AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/91348719-a197-5242-a566-3eb8ce4fb962

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_TateGlobal_forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one
import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped Topology

noncomputable section

namespace Ws31
namespace SW3

variable (F : Type) [Field F] [NumberField F]

abbrev T : Type := ↥(NumberField.TateGlobal.normOneIdeles F) ⧸
  (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F)

abbrev KK : Type := ↥(adelicMaximalCompact F)

abbrev P (A B : ℝ) : Type := T F × ↥(Set.Icc A B) × KK F

scoped instance : CompactSpace (T F) := NumberField.TateGlobal.compactSpace_normOneIdeleClass F
scoped instance : CompactSpace (KK F) := isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_adelicMaximalCompact F)

variable {F}

def IsKFin (m : KK F → ℂ) : Prop :=
  ∃ W : Submodule ℂ (KK F → ℂ), FiniteDimensional ℂ W ∧ ∀ k₀ : KK F, (fun k => m (k * k₀)) ∈ W

def IsKfSm (m : KK F → ℂ) : Prop :=
  ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u : KK F),
    (u : AdelicGL2 (𝓞 F) F) ∈ V → (u : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F → m (k * u) = m k

def IsElem {A B : ℝ} (f : C(P F A B, ℂ)) : Prop :=
  ∃ (χ : T F →* ℂˣ) (h : ℝ → ℂ) (m : KK F → ℂ), Continuous χ ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧ Continuous m ∧
    IsKFin m ∧ IsKfSm m ∧ ∀ p : P F A B, f p = ((χ p.1 : ℂˣ) : ℂ) * h (p.2.1 : ℝ) * m p.2.2

def elemSet {A B : ℝ} : Set C(P F A B, ℂ) := {f | IsElem f}

theorem isKFin_one : IsKFin (F := F) (fun _ => (1 : ℂ)) :=
  ⟨Submodule.span ℂ {fun _ => (1 : ℂ)}, inferInstance, fun k₀ => Submodule.subset_span rfl⟩

theorem isKFin_mul {m m' : KK F → ℂ} (hm : IsKFin m) (hm' : IsKFin m') : IsKFin (fun k => m k * m' k) := by
  obtain ⟨W, hW, hWm⟩ := hm
  obtain ⟨W', hW', hWm'⟩ := hm'

  let μ2 : (KK F → ℂ) →ₗ[ℂ] (KK F → ℂ) →ₗ[ℂ] (KK F → ℂ) := LinearMap.mul ℂ (KK F → ℂ)
  refine ⟨Submodule.map₂ μ2 W W', ?_, fun k₀ => ?_⟩
  · exact Submodule.fg_iff_finiteDimensional _ |>.mp ((Submodule.fg_iff_finiteDimensional _ |>.mpr hW).map₂ μ2 ((Submodule.fg_iff_finiteDimensional _).mpr hW'))
  · exact Submodule.apply_mem_map₂ μ2 (hWm k₀) (hWm' k₀)

theorem isKFin_star {m : KK F → ℂ} (hm : IsKFin m) : IsKFin (fun k => (starRingEnd ℂ) (m k)) := by
  obtain ⟨W, hW, hWm⟩ := hm

  let σ : (KK F → ℂ) →ₗ⋆[ℂ] (KK F → ℂ) :=
    { toFun := fun f k => (starRingEnd ℂ) (f k)
      map_add' := fun f g => by funext k; simp
      map_smul' := fun c f => by funext k; simp }
  refine ⟨W.map σ, ?_, fun k₀ => ⟨fun k => m (k * k₀), hWm k₀, rfl⟩⟩
  exact (Submodule.fg_iff_finiteDimensional _).mp (((Submodule.fg_iff_finiteDimensional _).mpr hW).map σ)

theorem isKfSm_one : IsKfSm (F := F) (fun _ => (1 : ℂ)) :=
  ⟨Set.univ, Filter.univ_mem, fun _ _ _ _ => rfl⟩

theorem isKfSm_mul {m m' : KK F → ℂ} (hm : IsKfSm m) (hm' : IsKfSm m') : IsKfSm (fun k => m k * m' k) := by
  obtain ⟨V, hV, h⟩ := hm
  obtain ⟨V', hV', h'⟩ := hm'
  exact ⟨V ∩ V', Filter.inter_mem hV hV', fun k u hu huf => by simp only [h k u hu.1 huf, h' k u hu.2 huf]⟩

theorem isKfSm_star {m : KK F → ℂ} (hm : IsKfSm m) : IsKfSm (fun k => (starRingEnd ℂ) (m k)) := by
  obtain ⟨V, hV, h⟩ := hm
  exact ⟨V, hV, fun k u hu huf => by simp only [h k u hu huf]⟩

theorem contDiff_conj_comp {h : ℝ → ℂ} {n : WithTop ℕ∞} (hh : ContDiff ℝ n h) :
    ContDiff ℝ n (fun u => (starRingEnd ℂ) (h u)) := by
  have : (fun u => (starRingEnd ℂ) (h u)) = (Complex.conjCLE : ℂ → ℂ) ∘ h := by
    funext u; simp
  rw [this]
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hh

section Elem
variable {A B : ℝ}

theorem one_mem_elemSet : (1 : C(P F A B, ℂ)) ∈ elemSet (F := F) :=
  ⟨1, fun _ => 1, fun _ => 1, continuous_const, contDiff_const, continuous_const, isKFin_one, isKfSm_one,
    fun p => by simp⟩

theorem mul_mem_elemSet {f g : C(P F A B, ℂ)} (hf : f ∈ elemSet) (hg : g ∈ elemSet) : f * g ∈ elemSet (F := F) := by
  obtain ⟨χ₁, h₁, m, h1, h2, h3, h4, h4', h5⟩ := hf
  obtain ⟨χ₁', h₁', m', h1', h2', h3', h44, h44', h5'⟩ := hg
  refine ⟨χ₁ * χ₁', fun u => h₁ u * h₁' u, fun k => m k * m' k, ?_, h2.mul h2', h3.mul h3', isKFin_mul h4 h44,
    isKfSm_mul h4' h44', fun p => ?_⟩
  · exact Continuous.mul h1 h1'
  · rw [ContinuousMap.mul_apply, h5 p, h5' p]
    simp only [MonoidHom.mul_apply, Units.val_mul]
    ring

theorem star_mem_elemSet {f : C(P F A B, ℂ)} (hf : f ∈ elemSet) : star f ∈ elemSet (F := F) := by
  obtain ⟨χ₁, h₁, m, h1, h2, h3, h4, h4', h5⟩ := hf
  let cU : ℂˣ →* ℂˣ := Units.map (starRingEnd ℂ : ℂ →* ℂ)
  have hcU : Continuous cU := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact Complex.continuous_conj.comp Units.continuous_val
    · exact Complex.continuous_conj.comp Units.continuous_coe_inv
  refine ⟨cU.comp χ₁, fun u => (starRingEnd ℂ) (h₁ u), fun k => (starRingEnd ℂ) (m k), hcU.comp h1,
    contDiff_conj_comp h2, Complex.continuous_conj.comp h3, isKFin_star h4, isKfSm_star h4', fun p => ?_⟩
  rw [ContinuousMap.star_apply, h5 p]
  simp [cU]

end Elem

section Adjoin
variable {A B : ℝ}

set_option synthInstance.maxHeartbeats 800000 in

private theorem _root_.Ws31.SW3.adjoin_eq_span :
    Subalgebra.toSubmodule (StarAlgebra.adjoin ℂ (elemSet (F := F) (A := A) (B := B))).toSubalgebra = Submodule.span ℂ (elemSet (F := F) (A := A) (B := B)) := by
  rw [StarAlgebra.adjoin_eq_span]
  congr 1
  apply le_antisymm
  ·
    have hsub : elemSet (F := F) ∪ star (elemSet (F := F) (A := A) (B := B)) ⊆ elemSet := by
      rintro f (hf | hf)
      · exact hf
      · have : star (star f) ∈ elemSet (F := F) := star_mem_elemSet hf
        simpa using this
    intro f hf
    refine Submonoid.closure_induction (s := elemSet ∪ star elemSet) (fun x hx => hsub hx) one_mem_elemSet
      (fun x y _ _ hx hy => mul_mem_elemSet hx hy) hf
  · exact (Set.subset_union_left).trans Submonoid.subset_closure

p2m_export "Ws31.SW3" "adjoin_eq_span"
end Adjoin

def evalFin (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : AdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun z := z.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_evalFin (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Continuous (evalFin (F := F) v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem isClopen_setOf_valued_le (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F)
    (ht : t ≠ 0) : IsClopen {y : v.adicCompletion F | Valued.v y ≤ Valued.v t} := by
  exact ⟨NumberField.AdelicLevel.isClosed_setOf_valued_le v t ht, NumberField.AdelicLevel.isOpen_setOf_valued_le v t ht⟩

theorem exists_isKFin_apply_ne_of_fin_ne (k k' : KK F) (i j : Fin 2) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (h : (((k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ≠
      (((k' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) :
    ∃ m : KK F → ℂ, Continuous m ∧ IsKFin m ∧ IsKfSm m ∧ m k ≠ m k' := by
  classical

  let e : Fin 2 → Fin 2 → KK F → v.adicCompletion F := fun a b x =>
    evalFin v (((x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) a b)
  have he_c : ∀ a b, Continuous (e a b) := fun a b =>
    (continuous_evalFin v).comp (Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) a b)
  have he_mul : ∀ (a b : Fin 2) (x y : KK F), e a b (x * y) = ∑ l, e a l x * e l b y := by
    intro a b x y
    simp only [e, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]
  have he_one : ∀ a b : Fin 2, e a b 1 = if a = b then 1 else 0 := by
    intro a b
    simp only [e, OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
    split_ifs <;> simp

  set u : KK F := k⁻¹ * k' with hu
  have hku : k * u = k' := by rw [hu, mul_inv_cancel_left]
  obtain ⟨a, b, hab⟩ : ∃ a b, e a b u ≠ e a b 1 := by
    by_contra hall
    push Not at hall
    apply h
    show e i j k = e i j k'
    rw [← hku, he_mul]
    simp_rw [hall, he_one]
    simp [Finset.sum_ite_eq']

  set d : v.adicCompletion F := e a b u - e a b 1 with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hab
  obtain ⟨c, hc⟩ : ∃ c : v.adicCompletion F, Valued.v c = WithZero.exp (-1 : ℤ) := by
    obtain ⟨ϖ, hϖ⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
    refine ⟨_, (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F ϖ)).trans ?_⟩
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hϖ]
  set t₀ : v.adicCompletion F := d * c with ht₀
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have ht₀0 : t₀ ≠ 0 := mul_ne_zero hd0 hc0
  have hlt : Valued.v t₀ < Valued.v d := by
    rw [ht₀, Valuation.map_mul, hc]
    have hdpos : 0 < Valued.v d := (Valuation.pos_iff _).mpr hd0
    have h1 : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    calc Valued.v d * WithZero.exp (-1 : ℤ) < Valued.v d * 1 := mul_lt_mul_of_pos_left h1 hdpos
      _ = Valued.v d := mul_one _
  let W : Set (KK F) := {x | Valued.v (e a b x - e a b 1) ≤ Valued.v t₀}
  have hWclopen : IsClopen W :=
    (isClopen_setOf_valued_le v t₀ ht₀0).preimage ((he_c a b).sub continuous_const)
  have h1W : (1 : KK F) ∈ W := by simp [W]
  have huW : u ∉ W := fun huW' => absurd (lt_of_le_of_lt huW' hlt) (by rw [hd]; exact lt_irrefl _)

  obtain ⟨H, hHW⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hWclopen h1W
  haveI : H.toSubgroup.Normal := H.isNormal'
  haveI : DiscreteTopology (KK F ⧸ H.toSubgroup) := QuotientGroup.discreteTopology H.isOpen'
  haveI : Finite (KK F ⧸ H.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ H.isOpen'
  let ind : KK F ⧸ H.toSubgroup → KK F → ℂ := fun c x =>
    if (QuotientGroup.mk x : KK F ⧸ H.toSubgroup) = c then 1 else 0
  have hind_c : ∀ c, Continuous (ind c) := fun c =>
    (continuous_of_discreteTopology (f := fun q : KK F ⧸ H.toSubgroup => if q = c then (1 : ℂ) else 0)).comp
      QuotientGroup.continuous_mk
  refine ⟨ind (QuotientGroup.mk k), hind_c _, ?_, ?_, ?_⟩
  · refine ⟨Submodule.span ℂ (Set.range ind), FiniteDimensional.span_of_finite ℂ (Set.finite_range ind), fun k₀ => ?_⟩
    have hiff : ∀ x : KK F, ((QuotientGroup.mk (x * k₀) : KK F ⧸ H.toSubgroup) = QuotientGroup.mk k) ↔
        ((QuotientGroup.mk x : KK F ⧸ H.toSubgroup) = QuotientGroup.mk (k * k₀⁻¹)) := by
      intro x
      rw [QuotientGroup.eq, QuotientGroup.eq]

      constructor
      · intro hx
        have := H.isNormal'.conj_mem _ hx k₀
        simpa [mul_assoc, mul_inv_rev] using this
      · intro hx
        have := H.isNormal'.conj_mem _ hx k₀⁻¹
        simpa [mul_assoc, mul_inv_rev] using this
    have e1 : (fun x => ind (QuotientGroup.mk k) (x * k₀)) = ind (QuotientGroup.mk (k * k₀⁻¹)) := by
      funext x
      simp only [ind, hiff]
    rw [e1]
    exact Submodule.subset_span ⟨_, rfl⟩
  ·
    obtain ⟨U, hU, hUH⟩ : ∃ U : Set (AdelicGL2 (𝓞 F) F), IsOpen U ∧ Subtype.val ⁻¹' U = (H : Set (KK F)) :=
      isOpen_induced_iff.mp H.isOpen'
    refine ⟨U, hU.mem_nhds ?_, fun x u' hu' _ => ?_⟩
    · have h1H : (1 : KK F) ∈ Subtype.val ⁻¹' U := by rw [hUH]; exact H.toSubgroup.one_mem
      exact h1H
    · have hu'H : u' ∈ (H : Set (KK F)) := by
        have : u' ∈ Subtype.val ⁻¹' U := hu'
        rwa [hUH] at this
      have hmk : (QuotientGroup.mk (x * u') : KK F ⧸ H.toSubgroup) = QuotientGroup.mk x := by
        rw [QuotientGroup.eq, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact H.toSubgroup.inv_mem hu'H
      simp only [ind, hmk]
  ·
    have hk : ind (QuotientGroup.mk k) k = 1 := by simp [ind]
    have hk' : ind (QuotientGroup.mk k) k' = 0 := by
      simp only [ind]
      rw [if_neg]
      intro heq
      rw [QuotientGroup.eq] at heq

      have : u ∈ (H : Set (KK F)) := by
        have := H.toSubgroup.inv_mem heq
        simp [hu, mul_inv_rev] at this
        exact this
      exact huW (hHW this)
    rw [hk, hk']
    exact one_ne_zero

theorem exists_isKFin_apply_ne_of_arch_ne (k k' : KK F) (i j : Fin 2) (w : InfinitePlace F)
    (h : (((k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w ≠
      (((k' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w) :
    ∃ m : KK F → ℂ, Continuous m ∧ IsKFin m ∧ IsKfSm m ∧ m k ≠ m k' := by
  classical

  let π : AdeleRing (𝓞 F) F →+* ℂ :=
    (InfinitePlace.Completion.extensionEmbedding w).comp
      ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp
        (RingHom.fst (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
  have hπ : ∀ z : AdeleRing (𝓞 F) F, π z = InfinitePlace.Completion.extensionEmbedding w (z.1 w) := fun z => rfl
  have hπc : Continuous π :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst)
  let ent : Fin 2 → Fin 2 → KK F → ℂ := fun a b x =>
    π ((((x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) a b))
  have hent_c : ∀ a b, Continuous (ent a b) := by
    intro a b
    exact hπc.comp (Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) a b)
  have hent_mul : ∀ (a b : Fin 2) (x y : KK F), ent a b (x * y) = ∑ l, ent a l x * ent l b y := by
    intro a b x y
    simp only [ent, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]
  refine ⟨ent i j, hent_c i j, ?_, ?_, ?_⟩
  · refine ⟨Submodule.span ℂ (Set.range fun l : Fin 2 => ent i l), FiniteDimensional.span_of_finite ℂ (Set.finite_range _), fun k₀ => ?_⟩
    have e1 : (fun x => ent i j (x * k₀)) = ∑ l, ent l j k₀ • ent i l := by
      funext x; simp only [hent_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul];
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [e1]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  ·
    refine ⟨Set.univ, Filter.univ_mem, fun x u' _ hu' => ?_⟩
    have h1 : NumberField.AdelicLevel.glArch (𝓞 F) F ((u' : KK F) : AdelicGL2 (𝓞 F) F) = 1 :=
      (AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff F _).mp hu'
    have hent1 : ∀ l b : Fin 2, ent l b u' = if l = b then 1 else 0 := by
      intro l b
      have h2 : ((((u' : KK F) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) l b).1 =
          ((1 : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) l b := by
        rw [← NumberField.AdelicLevel.glArch_apply (𝓞 F) F ((u' : KK F) : AdelicGL2 (𝓞 F) F) l b, h1]
      show π ((((u' : KK F) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) l b) = _
      rw [hπ, h2]
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs
      · rw [show ((1 : InfiniteAdeleRing F) w) = 1 from rfl, map_one]
      · rw [show ((0 : InfiniteAdeleRing F) w) = 0 from rfl, map_zero]
    rw [hent_mul]
    simp_rw [hent1]
    simp [Finset.sum_ite_eq']
  · intro heq
    exact h ((InfinitePlace.Completion.isometry_extensionEmbedding w).injective (by simpa [ent, hπ] using heq))

theorem exists_isKFin_apply_ne (k k' : KK F) (hk : k ≠ k') :
    ∃ m : KK F → ℂ, Continuous m ∧ IsKFin m ∧ IsKfSm m ∧ m k ≠ m k' := by
  have hne : ((k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ≠
      ((k' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    intro h; exact hk (Subtype.ext (Units.ext h))
  obtain ⟨i, j, hij⟩ : ∃ i j, ((k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j ≠
      ((k' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j := by
    by_contra hall; push Not at hall; exact hne (Matrix.ext fun i j => hall i j)
  by_cases h1 : (((k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (((k' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
  · have h2 : (((k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 ≠
        (((k' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 := by
      intro h2; exact hij (Prod.ext h1 h2)
    obtain ⟨v, hv⟩ : ∃ v, (((k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ≠
        (((k' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v := by
      by_contra hall; push Not at hall
      exact h2 (RestrictedProduct.ext _ _ fun v => hall v)
    exact exists_isKFin_apply_ne_of_fin_ne k k' i j v hv
  · obtain ⟨w, hw⟩ : ∃ w, (((k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w ≠
        (((k' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w := by
      by_contra hall; push Not at hall; exact h1 (funext hall)
    exact exists_isKFin_apply_ne_of_arch_ne k k' i j w hw

theorem exists_char_apply_ne (x y : T F) (hxy : x ≠ y) :
    ∃ χ : T F →* ℂˣ, Continuous χ ∧ χ x ≠ χ y := by
  have hne : x * y⁻¹ ≠ 1 := fun h => hxy (mul_inv_eq_one.mp h)
  obtain ⟨χ, hχ, hχx⟩ :=
    NumberField.TateGlobal.forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one F (x * y⁻¹) hne
  refine ⟨χ, hχ, fun h => hχx ?_⟩
  rw [map_mul, map_inv, h, mul_inv_cancel]

section Sep
variable {A B : ℝ}

set_option synthInstance.maxHeartbeats 800000 in

theorem separatesPoints : (StarAlgebra.adjoin ℂ (elemSet (F := F) (A := A) (B := B))).toSubalgebra.SeparatesPoints := by
  intro p q hpq

  suffices h : ∃ f : C(P F A B, ℂ), f ∈ elemSet (F := F) ∧ f p ≠ f q by
    obtain ⟨f, hf, hne⟩ := h
    exact ⟨f, ⟨f, StarAlgebra.subset_adjoin ℂ _ hf, rfl⟩, hne⟩
  by_cases h1 : p.1 = q.1
  · by_cases h2 : p.2.1 = q.2.1
    · have h3 : p.2.2 ≠ q.2.2 := fun h3 => hpq (Prod.ext h1 (Prod.ext h2 h3))
      obtain ⟨m, hmc, hmK, hmS, hm⟩ := exists_isKFin_apply_ne p.2.2 q.2.2 h3
      refine ⟨⟨fun r => m r.2.2, hmc.comp (continuous_snd.comp continuous_snd)⟩,
        ⟨1, fun _ => 1, m, continuous_const, contDiff_const, hmc, hmK, hmS, fun r => by simp⟩, ?_⟩
      simpa using hm
    ·
      have h2' : ((p.2.1 : ℝ) : ℂ) ≠ ((q.2.1 : ℝ) : ℂ) := by
        intro h; exact h2 (Subtype.ext (Complex.ofReal_injective h))
      refine ⟨⟨fun r => ((r.2.1 : ℝ) : ℂ),
          Complex.continuous_ofReal.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))⟩,
        ⟨1, fun u => (u : ℂ), fun _ => 1, continuous_const, Complex.ofRealCLM.contDiff, continuous_const,
          isKFin_one, isKfSm_one, fun r => by simp⟩, ?_⟩
      simpa using h2'
  · obtain ⟨χ, hχ, hne⟩ := exists_char_apply_ne p.1 q.1 h1
    refine ⟨⟨fun r => ((χ r.1 : ℂˣ) : ℂ), Units.continuous_val.comp (hχ.comp continuous_fst)⟩,
      ⟨χ, fun _ => 1, fun _ => 1, hχ, contDiff_const, continuous_const, isKFin_one, isKfSm_one, fun r => by simp⟩, ?_⟩
    simpa [Units.ext_iff] using hne

end Sep

end Ws31.SW3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31 P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31 P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3"

set_option synthInstance.maxHeartbeats 800000 in
open Ws31.SW3 in

theorem Ws31.SW3.sw3
    (F : Type) [Field F] [NumberField F] (A B : ℝ)
    (Φ : C(Ws31.SW3.P F A B, ℂ)) (ε : ℝ) (_hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (χ : Fin n → (Ws31.SW3.T F →* ℂˣ)) (h : Fin n → ℝ → ℂ)
      (m : Fin n → (Ws31.SW3.KK F → ℂ)),
      (∀ j, Continuous (χ j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (h j)) ∧ (∀ j, Continuous (m j)) ∧
      (∀ j, Ws31.SW3.IsKFin (m j)) ∧ (∀ j, Ws31.SW3.IsKfSm (m j)) ∧
      ∀ p : Ws31.SW3.P F A B,
        ‖Φ p - ∑ j, c j * (((χ j p.1 : ℂˣ) : ℂ) * h j (p.2.1 : ℝ) * m j p.2.2)‖ < ε := by
  classical
  let 𝒜 : StarSubalgebra ℂ C(P F A B, ℂ) := StarAlgebra.adjoin ℂ (elemSet (F := F) (A := A) (B := B))
  have hdense : 𝒜.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints 𝒜 separatesPoints
  have hmem : Φ ∈ 𝒜.topologicalClosure := by rw [hdense]; trivial
  have hcl : Φ ∈ closure (𝒜 : Set C(P F A B, ℂ)) := hmem
  obtain ⟨g, hgA, hg⟩ := Metric.mem_closure_iff.mp hcl ε _hε
  have hgspan : g ∈ Submodule.span ℂ (elemSet (F := F) (A := A) (B := B)) := by
    rw [← adjoin_eq_span]; exact hgA
  obtain ⟨c, t, hts, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hgspan
  set n := t.card with hn
  let e : Fin n ≃ ↥t := (t.equivFin).symm
  have hel : ∀ j : Fin n, IsElem ((e j : C(P F A B, ℂ))) := fun j => hts (e j).2
  choose χ h m h1 h2 h3 h4 h4' h5 using hel
  refine ⟨n, fun j => c (e j), χ, h, m, h1, h2, h3, h4, h4', fun p => ?_⟩
  have hgp : g p = ∑ j, c (e j) * (((χ j p.1 : ℂˣ) : ℂ) * h j (p.2.1 : ℝ) * m j p.2.2) := by
    rw [← hsum, ContinuousMap.coe_sum, Finset.sum_apply]
    rw [← Finset.sum_coe_sort t]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, h5 j p]
  rw [← hgp]
  have := (ContinuousMap.dist_lt_iff _hε).mp hg p
  rw [dist_eq_norm] at this
  exact this

namespace Ws31
namespace SW3

theorem exists_smooth_cutoff (A B A' B' : ℝ) (hA : A' < A) (hB : B < B') :
    ∃ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧ (∀ u ∈ Set.Icc A B, θ u = 1) ∧
      (∀ u, θ u ≠ 0 → u ∈ Set.Ioo A' B') ∧ (∀ u, 0 ≤ θ u) ∧ ∀ u, θ u ≤ 1 := by
  by_cases hAB : A ≤ B
  ·
    set c : ℝ := (A + B) / 2 with hc
    set r : ℝ := (B - A) / 2 with hr
    set η : ℝ := min (A - A') (B' - B) / 2 with hη
    have hη0 : 0 < η := by
      rw [hη]; exact div_pos (lt_min (sub_pos.mpr hA) (sub_pos.mpr hB)) two_pos
    have hr0 : 0 ≤ r := by rw [hr]; linarith
    let f : ContDiffBump c := ⟨r + η / 2, r + η, by linarith, by linarith⟩
    refine ⟨f, f.contDiff, f.hasCompactSupport, fun u hu => ?_, fun u hu => ?_, fun u => f.nonneg,
      fun u => f.le_one⟩
    · apply f.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq]
      have : |u - c| ≤ r := by
        rw [abs_le]; constructor <;> [skip; skip] <;> simp only [hc, hr] <;> linarith [hu.1, hu.2]
      show |u - c| ≤ r + η / 2
      linarith
    · have hmem : u ∈ Function.support (f : ℝ → ℝ) := hu
      rw [f.support_eq, Metric.mem_ball, Real.dist_eq] at hmem
      change |u - c| < r + η at hmem
      rw [abs_lt] at hmem
      have hη1 : η ≤ (A - A') / 2 := by
        rw [hη]; exact div_le_div_of_nonneg_right (min_le_left _ _) two_pos.le
      have hη2 : η ≤ (B' - B) / 2 := by
        rw [hη]; exact div_le_div_of_nonneg_right (min_le_right _ _) two_pos.le
      constructor
      · simp only [hc, hr] at hmem; linarith [hmem.1]
      · simp only [hc, hr] at hmem; linarith [hmem.2]
  ·
    refine ⟨0, contDiff_const, ?_, fun u hu => ?_, fun u hu => absurd rfl hu, fun _ => le_rfl, fun _ => zero_le_one⟩
    · exact HasCompactSupport.zero
    · exact absurd (hu.1.trans hu.2) hAB

theorem core
    (F : Type) [Field F] [NumberField F] (A B A' B' : ℝ) (hA : A' < A) (hB : B < B')
    (Φ : T F × ℝ × KK F → ℂ) (hΦ : Continuous Φ) (hsupp : ∀ p, Φ p ≠ 0 → p.2.1 ∈ Set.Icc A B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (χ : Fin n → (T F →* ℂˣ)) (h : Fin n → ℝ → ℂ) (m : Fin n → KK F → ℂ),
      (∀ j, Continuous (χ j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (h j)) ∧ (∀ j, HasCompactSupport (h j)) ∧
      (∀ (j : Fin n) (u : ℝ), h j u ≠ 0 → u ∈ Set.Icc A' B') ∧
      (∀ j, Continuous (m j)) ∧ (∀ j, IsKFin (m j)) ∧ (∀ j, IsKfSm (m j)) ∧
      ∀ p : T F × ℝ × KK F, ‖Φ p - ∑ j, ((χ j p.1 : ℂˣ) : ℂ) * h j p.2.1 * m j p.2.2‖ < ε := by
  classical
  obtain ⟨θ, hθs, hθc, hθ1, hθsupp, hθ0, hθle⟩ := exists_smooth_cutoff A B A' B' hA hB

  let Ψ : C(P F A' B', ℂ) :=
    ⟨fun q => Φ (q.1, (q.2.1 : ℝ), q.2.2),
      hΦ.comp (continuous_fst.prodMk ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)))⟩
  obtain ⟨n, c, χ, h, m, h1, h2, h3, h4, h4', hg⟩ := sw3 F A' B' Ψ ε hε
  refine ⟨n, χ, fun j u => ((θ u : ℝ) : ℂ) * (c j * h j u), m, h1, fun j => ?_, fun j => ?_, fun j u hu => ?_,
    h3, h4, h4', fun p => ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hθs).mul (contDiff_const.mul (h2 j))
  · exact (hθc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right
  · have : θ u ≠ 0 := by
      intro h0; apply hu; simp [h0]
    exact Set.Ioo_subset_Icc_self (hθsupp u this)
  · obtain ⟨τ, u, k⟩ := p

    have hS : ∑ j, ((χ j τ : ℂˣ) : ℂ) * (((θ u : ℝ) : ℂ) * (c j * h j u)) * m j k =
        ((θ u : ℝ) : ℂ) * ∑ j, c j * (((χ j τ : ℂˣ) : ℂ) * h j u * m j k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only
    rw [hS]
    by_cases hu : u ∈ Set.Icc A' B'
    · let q : P F A' B' := (τ, ⟨u, hu⟩, k)
      have hq := hg q
      have hΨq : Ψ q = Φ (τ, u, k) := rfl
      by_cases huAB : u ∈ Set.Icc A B
      · rw [hθ1 u huAB]
        simpa [hΨq] using hq
      · have hΦ0 : Φ (τ, u, k) = 0 := by
          by_contra hne; exact huAB (hsupp (τ, u, k) hne)
        rw [hΦ0, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hθ0 u)]
        rw [hΨq, hΦ0, zero_sub, norm_neg] at hq
        calc θ u * ‖∑ j, c j * (((χ j τ : ℂˣ) : ℂ) * h j (q.2.1 : ℝ) * m j k)‖
            ≤ 1 * ‖∑ j, c j * (((χ j τ : ℂˣ) : ℂ) * h j (q.2.1 : ℝ) * m j k)‖ :=
              mul_le_mul_of_nonneg_right (hθle u) (norm_nonneg _)
          _ < ε := by rw [one_mul]; exact hq
    · have hθu : θ u = 0 := by
        by_contra hne; exact hu (Set.Ioo_subset_Icc_self (hθsupp u hne))
      have hΦ0 : Φ (τ, u, k) = 0 := by
        by_contra hne
        exact hu (Set.Icc_subset_Icc hA.le hB.le (hsupp (τ, u, k) hne))
      rw [hθu, hΦ0]
      simpa using hε

end Ws31.SW3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31 P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31 P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3"

noncomputable section

namespace Ws31
namespace S2a

open NumberField.TateGlobal Ws31.SW3
open scoped NNReal

theorem norm_apply_eq_one_of_compactSpace {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (χ : G →* ℂˣ) (hχ : Continuous χ) (g : G) : ‖((χ g : ℂˣ) : ℂ)‖ = 1 := by
  set N : G → ℝ := fun x => ‖((χ x : ℂˣ) : ℂ)‖ with hN
  have hc : Continuous N := (Units.continuous_val.comp hχ).norm
  have hNmul : ∀ x y, N (x * y) = N x * N y := by
    intro x y; simp only [hN, map_mul, Units.val_mul, norm_mul]
  have hN1 : N 1 = 1 := by simp [hN]
  have hNpow : ∀ (x : G) (n : ℕ), N (x ^ n) = N x ^ n := by
    intro x n; simp only [hN, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hNpos : ∀ x, 0 < N x := by
    intro x; simp only [hN]; exact norm_pos_iff.mpr (Units.ne_zero _)
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  have hle : ∀ g, N g ≤ 1 := by
    intro g
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (N x₀) hlt
    have h1 : N (g ^ n) ≤ N x₀ := (isMaxOn_iff.mp hx₀) (g ^ n) (Set.mem_univ _)
    rw [hNpow] at h1
    exact absurd (lt_of_le_of_lt h1 hn) (lt_irrefl _)
  have hge : 1 ≤ N g := by
    have h1 := hle g⁻¹
    have hprod : N g * N g⁻¹ = 1 := by rw [← hNmul, mul_inv_cancel, hN1]
    nlinarith [hNpos g, hNpos g⁻¹]
  exact le_antisymm (hle g) hge

variable {F : Type} [Field F] [NumberField F]

def eN (u : ℝ) : ℝ≥0 := ⟨Real.exp u, (Real.exp_pos u).le⟩

theorem coe_eN (u : ℝ) : ((eN u : ℝ≥0) : ℝ) = Real.exp u := rfl

theorem eN_ne_zero (u : ℝ) : eN u ≠ 0 := by
  rw [← NNReal.coe_ne_zero]; exact (Real.exp_pos u).ne'

theorem continuous_eN : Continuous eN := Real.continuous_exp.subtype_mk _

def eU (u : ℝ) : ℝ≥0ˣ := Units.mk0 (eN u) (eN_ne_zero u)

theorem coe_eU (u : ℝ) : ((eU u : ℝ≥0) : ℝ) = Real.exp u := rfl

theorem eU_add (u v : ℝ) : eU (u + v) = eU u * eU v := by
  apply Units.ext
  apply NNReal.eq
  rw [Units.val_mul, NNReal.coe_mul]
  exact Real.exp_add u v

theorem eU_zero : eU 0 = 1 := by
  apply Units.ext
  apply NNReal.eq
  rw [Units.val_one, NNReal.coe_one]
  exact Real.exp_zero

theorem continuous_eU : Continuous eU := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_eN
  · show Continuous fun u => (eN u)⁻¹
    exact continuous_eN.inv₀ eN_ne_zero

theorem ideleNorm_one : ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  simp [ideleNorm]

theorem ideleNorm_inv (x : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F x⁻¹ = (ideleNorm F x)⁻¹ := by
  have h := ideleNorm_mul x⁻¹ x
  rw [inv_mul_cancel, ideleNorm_one] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

section WithSection

variable (s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ) (hs : ∀ r : ℝ≥0ˣ, ideleNorm F (s r) = ((r : ℝ≥0) : ℝ))

def rho1 : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 F) F)ˣ where
  toFun t := t * (s (eU (Real.log (ideleNorm F t))))⁻¹
  map_one' := by rw [ideleNorm_one, Real.log_one, eU_zero, map_one, inv_one, mul_one]
  map_mul' x y := by
    rw [ideleNorm_mul, Real.log_mul (ideleNorm_pos x).ne' (ideleNorm_pos y).ne', eU_add, map_mul, mul_inv]
    simp only [mul_assoc, mul_left_comm y]

theorem rho1_apply (t : (AdeleRing (𝓞 F) F)ˣ) :
    rho1 s t = t * (s (eU (Real.log (ideleNorm F t))))⁻¹ := rfl

include hs in
theorem ideleNorm_rho1 (t : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F (rho1 s t) = 1 := by
  rw [rho1_apply, ideleNorm_mul, ideleNorm_inv, hs, coe_eU, Real.exp_log (ideleNorm_pos t),
    mul_inv_cancel₀ (ideleNorm_pos t).ne']

def rho2 : (AdeleRing (𝓞 F) F)ˣ →* ↥(normOneIdeles F) :=
  (rho1 s).codRestrict (normOneIdeles F) (fun t => (mem_normOneIdeles_iff _).mpr (ideleNorm_rho1 s hs t))

def rho0 : (AdeleRing (𝓞 F) F)ˣ →* T F :=
  (QuotientGroup.mk' _).comp (rho2 s hs)

theorem rho0_apply (t : (AdeleRing (𝓞 F) F)ˣ) :
    rho0 s hs t = (QuotientGroup.mk (rho2 s hs t) : T F) := rfl

theorem coe_rho2 (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((rho2 s hs t : ↥(normOneIdeles F)) : (AdeleRing (𝓞 F) F)ˣ) = rho1 s t := rfl

theorem continuous_rho1 (hsc : Continuous s) : Continuous (rho1 s) := by
  have hN : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F t) :=
    (NumberField.TateGlobal.continuous_ideleNorm F).log (fun t => (ideleNorm_pos t).ne')
  show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => t * (s (eU (Real.log (ideleNorm F t))))⁻¹
  exact continuous_id.mul ((hsc.comp (continuous_eU.comp hN)).inv)

theorem continuous_rho0 (hsc : Continuous s) : Continuous (rho0 s hs) := by
  refine QuotientGroup.continuous_mk.comp ?_
  exact (continuous_rho1 s hsc).subtype_mk _

theorem rho0_eq_one_of_mem {q : (AdeleRing (𝓞 F) F)ˣ} (hq : q ∈ M4aHerbrand.principalIdeles (𝓞 F) F)
    (hq1 : ideleNorm F q = 1) : rho0 s hs q = 1 := by
  rw [rho0_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, coe_rho2, rho1_apply, hq1, Real.log_one,
    eU_zero, map_one, inv_one, mul_one]
  exact hq

end WithSection
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31 P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3"

end Ws31.S2a
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31 P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31 P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31 P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open Ws31.SW3 Ws31.S2a NumberField.TateGlobal in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (a' b' a₁ b₁ : ℝ) (ha' : 0 < a') (ha₁ : a' < a₁) (hb₁ : b₁ < b')
    (G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ) (hGc : Continuous G)
    (hGinv : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G (γ * p.1, p.2) = G p)
    (hGsupp : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G p ≠ 0 → NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a₁ b₁)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (μ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (h : Fin n → ℝ → ℂ)
      (m : Fin n → ↥(adelicMaximalCompact F) → ℂ),
      (∀ j, IsUnitaryChar (𝓞 F) F (μ j)) ∧ (∀ j, IsIdeleClassChar (𝓞 F) F (μ j)) ∧
      (∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ j x : ℂˣ) : ℂ)) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (h j)) ∧ (∀ j, HasCompactSupport (h j)) ∧
      (∀ (j : Fin n) (u : ℝ), h j u ≠ 0 → u ∈ Set.Icc (Real.log a') (Real.log b')) ∧
      (∀ j, Continuous (m j)) ∧
      (∀ j, ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => m j (k * k₀)) ∈ W) ∧
      (∀ j, ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u : ↥(adelicMaximalCompact F)),
        (u : AdelicGL2 (𝓞 F) F) ∈ V → (u : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          m j (k * u) = m j k) ∧
      ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), ‖G p - ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2‖ ≤ ε := by
  classical

  by_cases hb0 : 0 < b₁
  swap
  · have hG0 : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G p = 0 := by
      intro p
      by_contra hne
      have h := (hGsupp p hne).2
      exact hb0 (lt_of_lt_of_le (ideleNorm_pos p.1) h)
    refine ⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
      fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
      fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun p => ?_⟩
    simp [hG0 p, hε.le]
  have ha₁0 : 0 < a₁ := ha'.trans ha₁

  obtain ⟨s, hsc, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F

  have hwd : ∀ (u : ℝ) (k : ↥(adelicMaximalCompact F)) (a b : ↥(normOneIdeles F)),
      @Setoid.r _ (QuotientGroup.leftRel
        ((M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F))) a b →
        G ((a : (AdeleRing (𝓞 F) F)ˣ) * s (eU u), k) = G ((b : (AdeleRing (𝓞 F) F)ˣ) * s (eU u), k) := by
    intro u k a b hab
    have hab' : ((a⁻¹ * b : ↥(normOneIdeles F)) : (AdeleRing (𝓞 F) F)ˣ) ∈ M4aHerbrand.principalIdeles (𝓞 F) F :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)
    have hb : (b : (AdeleRing (𝓞 F) F)ˣ) * s (eU u) =
        ((a⁻¹ * b : ↥(normOneIdeles F)) : (AdeleRing (𝓞 F) F)ˣ) * ((a : (AdeleRing (𝓞 F) F)ˣ) * s (eU u)) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [mul_mul_mul_comm, inv_mul_cancel, one_mul]
    rw [hb]
    exact (hGinv _ hab' ((a : (AdeleRing (𝓞 F) F)ˣ) * s (eU u), k)).symm
  let Φ : T F × ℝ × KK F → ℂ := fun p =>
    Quotient.liftOn' p.1 (fun x : ↥(normOneIdeles F) => G ((x : (AdeleRing (𝓞 F) F)ˣ) * s (eU p.2.1), p.2.2))
      (fun a b hab => hwd p.2.1 p.2.2 a b hab)
  have hΦmk : ∀ (x : ↥(normOneIdeles F)) (u : ℝ) (k : KK F),
      Φ ((QuotientGroup.mk x : T F), u, k) = G ((x : (AdeleRing (𝓞 F) F)ˣ) * s (eU u), k) := fun _ _ _ => rfl
  have hΦc : Continuous Φ := by
    have hq : IsOpenQuotientMap
        (Prod.map (QuotientGroup.mk : ↥(normOneIdeles F) → T F) (Prod.map (id : ℝ → ℝ) (id : KK F → KK F))) :=
      QuotientGroup.isOpenQuotientMap_mk.prodMap (IsOpenQuotientMap.id.prodMap IsOpenQuotientMap.id)
    rw [← hq.continuous_comp_iff]
    change Continuous fun x : ↥(normOneIdeles F) × ℝ × KK F =>
      G (((x.1 : ↥(normOneIdeles F)) : (AdeleRing (𝓞 F) F)ˣ) * s (eU x.2.1), x.2.2)
    exact hGc.comp (((continuous_subtype_val.comp continuous_fst).mul
      (hsc.comp (continuous_eU.comp (continuous_fst.comp continuous_snd)))).prodMk
        (continuous_snd.comp continuous_snd))

  have hΦsupp : ∀ p : T F × ℝ × KK F, Φ p ≠ 0 → p.2.1 ∈ Set.Icc (Real.log a₁) (Real.log b₁) := by
    rintro ⟨τ, u, k⟩ hne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective τ
    rw [hΦmk] at hne
    have hmem := hGsupp _ hne
    have hnorm : ideleNorm F ((x : (AdeleRing (𝓞 F) F)ˣ) * s (eU u)) = Real.exp u := by
      rw [ideleNorm_mul, (mem_normOneIdeles_iff _).mp x.2, hs, coe_eU, one_mul]
    simp only [hnorm] at hmem
    constructor
    · have := Real.log_le_log ha₁0 hmem.1
      rwa [Real.log_exp] at this
    · have := Real.log_le_log (Real.exp_pos u) hmem.2
      rwa [Real.log_exp] at this

  obtain ⟨n, χ, h, m, h1, h2, h3, h4, h5, h6, h7, hcore⟩ :=
    Ws31.SW3.core F (Real.log a₁) (Real.log b₁) (Real.log a') (Real.log b')
      (Real.log_lt_log ha' ha₁) (Real.log_lt_log hb0 hb₁) Φ hΦc hΦsupp ε hε

  have hq1 : ∀ u : Fˣ, ideleNorm F ((Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) u) = 1 := by
    intro u
    have hpf : distribHaarChar (AdeleRing (𝓞 F) F)
        ((Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) u) = 1 :=
      NumberField.AdeleRing.distribHaarChar_algebraMap F u
    show ((distribHaarChar (AdeleRing (𝓞 F) F) _ : ℝ≥0) : ℝ) = 1
    rw [hpf, NNReal.coe_one]
  refine ⟨n, fun j => (χ j).comp (rho0 s hs), h, m, fun j x => ?_, fun j u => ?_, fun j => ?_, h2, h3, h4,
    h5, h6, h7, fun p => ?_⟩
  · exact norm_apply_eq_one_of_compactSpace (χ j) (h1 j) (rho0 s hs x)
  · have h0 : rho0 s hs ((Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) u) = 1 :=
      rho0_eq_one_of_mem s hs ⟨u, rfl⟩ (hq1 u)
    exact (congrArg (χ j) h0).trans (map_one (χ j))
  · exact Units.continuous_val.comp ((h1 j).comp (continuous_rho0 s hs hsc))
  · obtain ⟨t, k⟩ := p
    have hkey : G (t, k) = Φ (rho0 s hs t, Real.log (ideleNorm F t), k) := by
      rw [rho0_apply, hΦmk, coe_rho2, rho1_apply, inv_mul_cancel_right]
    have := hcore (rho0 s hs t, Real.log (ideleNorm F t), k)
    rw [← hkey] at this
    exact this.le

end S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
end P2MW
export P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported (solution)
