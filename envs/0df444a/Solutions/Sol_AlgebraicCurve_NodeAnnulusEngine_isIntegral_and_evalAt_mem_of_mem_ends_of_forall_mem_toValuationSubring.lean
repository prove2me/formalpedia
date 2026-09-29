-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8b7234dc-e2a6-53bc-94d6-1e839157d15e

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_ValuationSubring_exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
import Theorems.Thm_existsUnique_valuationSubring_of_pow_eq_mul
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Theorems.Thm_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open scoped IntermediateField Polynomial

namespace TubeMaxChild

section ValSub

theorem mul_mem_nonunits_of_mem {K : Type*} [Field K] (O : ValuationSubring K) {a b : K} (ha : a ∈ O) (hb : b ∈ O.nonunits) :
    a * b ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hb ⊢
  rw [map_mul]
  have ha' : O.valuation a ≤ 1 := (O.valuation_le_one_iff a).mpr ha
  calc O.valuation a * O.valuation b ≤ O.valuation b := mul_le_of_le_one_left' ha'
    _ < 1 := hb

theorem mem_nonunits_iff_inv_not_mem {K : Type*} [Field K] (O : ValuationSubring K) {s : K} (hs0 : s ≠ 0) :
    s ∈ O.nonunits ↔ s⁻¹ ∉ O := by
  have h := O.inv_mem_nonunits_iff (x := s⁻¹)
  rw [inv_inv] at h
  rw [h]
  constructor
  · rintro (h0 | h0)
    · exact absurd (inv_eq_zero.mp h0) hs0
    · exact h0
  · exact fun h0 => Or.inr h0

theorem inv_mem_of_not_mem_nonunits {K : Type*} [Field K] (O : ValuationSubring K) {s : K} (hs0 : s ≠ 0) (hs : s ∉ O.nonunits) :
    s⁻¹ ∈ O := by
  by_contra h
  exact hs ((mem_nonunits_iff_inv_not_mem O hs0).mpr h)

theorem nonunits_subset {K : Type*} [Field K] (O : ValuationSubring K) {s : K} (hs : s ∈ O.nonunits) : s ∈ O :=
  O.nonunits_le hs

theorem zero_mem_nonunits {K : Type*} [Field K] (O : ValuationSubring K) : (0 : K) ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one

theorem ne_top_of_mem_nonunits {K : Type*} [Field K] (O : ValuationSubring K) {s : K} (hs0 : s ≠ 0) (hs : s ∈ O.nonunits) : O ≠ ⊤ := by
  intro h
  have : s⁻¹ ∉ O := (mem_nonunits_iff_inv_not_mem O hs0).mp hs
  exact this (h ▸ ValuationSubring.mem_top _)

theorem eq_of_le_of_nonunits {K : Type*} [Field K] (V O : ValuationSubring K) (hle : ∀ z, z ∈ V → z ∈ O)
    (hdom : ∀ z, z ∈ V.nonunits → z ∈ O.nonunits) : V = O := by
  refine le_antisymm (fun z hz => hle z hz) fun z hz => ?_
  by_contra hzV
  have hz0 : z ≠ 0 := fun h => hzV (h ▸ V.zero_mem)
  have h1 : z⁻¹ ∈ V.nonunits := (V.inv_mem_nonunits_iff).mpr (Or.inr hzV)
  have h2 : z⁻¹ ∈ O.nonunits := hdom _ h1
  rcases (O.inv_mem_nonunits_iff).mp h2 with h | h
  · exact hz0 h
  · exact h hz

end ValSub

section Centre

def toValSub {F : Type*} [Field F] (N : Subring F) (O : ValuationSubring F) (h : ∀ g : F, g ∈ N → g ∈ O) : N →+* O :=
  (N.subtype).codRestrict O (fun g => h g g.2)

@[scoped simp] theorem coe_toValSub {F : Type*} [Field F] (N : Subring F) (O : ValuationSubring F) (h : ∀ g : F, g ∈ N → g ∈ O) (g : N) :
    ((toValSub N O h g : O) : F) = (g : F) := rfl

def cen {F : Type*} [Field F] (N : Subring F) (O : ValuationSubring F) (h : ∀ g : F, g ∈ N → g ∈ O) : Ideal N :=
  (maximalIdeal O).comap (toValSub N O h)

theorem mem_cen_iff {F : Type*} [Field F] (N : Subring F) (O : ValuationSubring F) (h : ∀ g : F, g ∈ N → g ∈ O) (g : N) :
    g ∈ cen N O h ↔ (g : F) ∈ O.nonunits := by
  rw [cen, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

scoped instance cen_isPrime {F : Type*} [Field F] (N : Subring F) (O : ValuationSubring F) (h : ∀ g : F, g ∈ N → g ∈ O) :
    (cen N O h).IsPrime :=
  Ideal.comap_isPrime _ _

theorem cen_ne_top {F : Type*} [Field F] (N : Subring F) (O : ValuationSubring F) (h : ∀ g : F, g ∈ N → g ∈ O) : cen N O h ≠ ⊤ :=
  (cen_isPrime N O h).ne_top

theorem inv_mem_of_not_mem_cen {F : Type*} [Field F] (N : Subring F) (O : ValuationSubring F) (h : ∀ g : F, g ∈ N → g ∈ O)
    {s : N} (hs : s ∉ cen N O h) (hs0 : (s : F) ≠ 0) : (s : F)⁻¹ ∈ O :=
  inv_mem_of_not_mem_nonunits O hs0 (by rwa [mem_cen_iff] at hs)

end Centre

section Eval

def resEquiv {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) : L ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap L P.ResidueField) ⟨(algebraMap L P.ResidueField).injective, hP⟩

@[scoped simp] theorem resEquiv_apply {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) (c : L) :
    resEquiv P hP c = algebraMap L P.ResidueField c := rfl

def evalHom {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) : P.toValuationSubring →+* L :=
  (resEquiv P hP).symm.toRingHom.comp (IsLocalRing.residue P.toValuationSubring)

theorem evalHom_apply {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) (g : P.toValuationSubring) :
    evalHom P hP g = P.evalAt (g : F) := by
  apply (resEquiv P hP).injective
  change (resEquiv P hP) ((resEquiv P hP).symm (IsLocalRing.residue P.toValuationSubring g)) = _
  rw [RingEquiv.apply_symm_apply, resEquiv_apply, P.algebraMap_evalAt hP g.2]

theorem evalAt_eq_evalHom {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) {g : F} (hg : g ∈ P.toValuationSubring) :
    P.evalAt g = evalHom P hP ⟨g, hg⟩ :=
  (evalHom_apply P hP ⟨g, hg⟩).symm

theorem evalHom_algebraMap {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) (c : L) :
    evalHom P hP (algebraMap L P.toValuationSubring c) = c := by
  apply (resEquiv P hP).injective
  change (resEquiv P hP) ((resEquiv P hP).symm
    (IsLocalRing.residue P.toValuationSubring (algebraMap L P.toValuationSubring c))) = _
  rw [RingEquiv.apply_symm_apply, resEquiv_apply, IsScalarTower.algebraMap_apply L P.toValuationSubring P.ResidueField]
  rfl

theorem evalAt_algebraMap {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) (c : L) : P.evalAt (algebraMap L F c) = c := by
  rw [evalAt_eq_evalHom P hP (P.algebraMap_mem' c)]
  exact evalHom_algebraMap P hP c

theorem evalHom_eq_zero_iff {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) (g : P.toValuationSubring) :
    evalHom P hP g = 0 ↔ g ∈ maximalIdeal P.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro h
    apply (resEquiv P hP).symm.injective
    rw [map_zero]
    exact h
  · intro h
    change (resEquiv P hP).symm (IsLocalRing.residue P.toValuationSubring g) = 0
    rw [h, map_zero]

end Eval

section Vertical

theorem crossingSwap_const' {W : Type*} [CommRing W] (π : W) (w : W) :
    crossingSwap π (const π w) = const π w := by
  change crossingSwap π (UVCrossingModel.mk π (MvPowerSeries.C w)) = UVCrossingModel.mk π (MvPowerSeries.C w)
  rw [crossingSwap_mk, uvSwapEquiv_C]

theorem crossingSwap_U' {W : Type*} [CommRing W] (π : W) : crossingSwap π (U π) = V π := by
  change crossingSwap π (UVCrossingModel.mk π (MvPowerSeries.X 0)) = UVCrossingModel.mk π (MvPowerSeries.X 1)
  rw [crossingSwap_mk, uvSwapEquiv_X_zero]

theorem crossingSwap_V' {W : Type*} [CommRing W] (π : W) : crossingSwap π (V π) = U π := by
  change crossingSwap π (UVCrossingModel.mk π (MvPowerSeries.X 1)) = UVCrossingModel.mk π (MvPowerSeries.X 0)
  rw [crossingSwap_mk, uvSwapEquiv_X_one]

theorem branch_primes {F : Type*} [Field F]
    (𝒩₀ : Subring F) [IsLocalRing 𝒩₀] [IsNoetherianRing 𝒩₀]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (t x y : 𝒩₀)
    (ht : ι (algebraMap 𝒩₀ (AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀) t) = const (π ^ E) π)
    (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hx : ι (algebraMap 𝒩₀ (AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀) x) = (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hy : ι (algebraMap 𝒩₀ (AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀) y) = (γV : UVCrossingModel W (π ^ E)) * V (π ^ E)) :
    (∃ u : 𝒩₀, IsUnit u ∧ x * y = t ^ E * u) ∧
    ((Ideal.span {t, y}).IsPrime ∧ x ∉ Ideal.span {t, y} ∧
      (∀ 𝔮 : Ideal 𝒩₀, 𝔮.IsPrime → t ∈ 𝔮 → x ∉ 𝔮 → 𝔮 ≠ maximalIdeal 𝒩₀ → 𝔮 = Ideal.span {t, y}) ∧
      (Ideal.span {t, y}).height = 1) ∧
    ((Ideal.span {t, x}).IsPrime ∧ y ∉ Ideal.span {t, x} ∧
      (∀ 𝔮 : Ideal 𝒩₀, 𝔮.IsPrime → t ∈ 𝔮 → y ∉ 𝔮 → 𝔮 ≠ maximalIdeal 𝒩₀ → 𝔮 = Ideal.span {t, x}) ∧
      (Ideal.span {t, x}).height = 1) := by
  obtain ⟨hnode, hV⟩ :=
    IsLocalRing.exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel
      π hπ E hE ι t x y ht γU γV hx hy

  set ι' : AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀ ≃+* UVCrossingModel W (π ^ E) := ι.trans (crossingSwap (π ^ E)) with hι'
  have hι'_apply : ∀ z, ι' z = crossingSwap (π ^ E) (ι z) := fun z => rfl
  have ht' : ι' (algebraMap 𝒩₀ (AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀) t) = const (π ^ E) π := by
    rw [hι'_apply, ht, crossingSwap_const']
  set δU : (UVCrossingModel W (π ^ E))ˣ := Units.map (crossingSwap (π ^ E)).toRingHom.toMonoidHom γV with hδU
  set δV : (UVCrossingModel W (π ^ E))ˣ := Units.map (crossingSwap (π ^ E)).toRingHom.toMonoidHom γU with hδV
  have hy' : ι' (algebraMap 𝒩₀ (AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀) y) =
      (δU : UVCrossingModel W (π ^ E)) * U (π ^ E) := by
    rw [hι'_apply, hy, map_mul, crossingSwap_V']
    rfl
  have hx' : ι' (algebraMap 𝒩₀ (AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀) x) =
      (δV : UVCrossingModel W (π ^ E)) * V (π ^ E) := by
    rw [hι'_apply, hx, map_mul, crossingSwap_U']
    rfl
  obtain ⟨-, hU⟩ :=
    IsLocalRing.exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel
      π hπ E hE ι' t y x ht' δU δV hy' hx'
  exact ⟨hnode, hV, hU⟩

theorem dvr_branch {F : Type*} [Field F] (𝒩₀ : Subring F) [IsLocalRing 𝒩₀] [IsNoetherianRing 𝒩₀] [IsIntegrallyClosed 𝒩₀]
    (t a b u : 𝒩₀) (hu : IsUnit u) (E : ℕ) (hE : 1 ≤ E) (hab : a * b = t ^ E * u)
    (𝔭 : Ideal 𝒩₀) [𝔭.IsPrime] (h𝔭 : 𝔭 = Ideal.span {t, b}) (ha : a ∉ 𝔭) (hht : 𝔭.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime 𝔭) ∧
      maximalIdeal (Localization.AtPrime 𝔭) = Ideal.span {algebraMap 𝒩₀ (Localization.AtPrime 𝔭) t} := by
  subst h𝔭
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {t, b})) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one _ hht
  refine ⟨hdvr, ?_⟩
  set j := algebraMap 𝒩₀ (Localization.AtPrime (Ideal.span {t, b})) with hj
  have hau : IsUnit (j a) :=
    IsLocalization.map_units (Localization.AtPrime (Ideal.span {t, b})) (⟨a, ha⟩ : (Ideal.span {t, b}).primeCompl)
  have hbmem : j b ∈ Ideal.span {j t} := by
    obtain ⟨ai, hai⟩ := hau.exists_left_inv
    have : j b = ai * j t ^ E * j u := by
      calc j b = ai * j a * j b := by rw [hai, one_mul]
        _ = ai * j (a * b) := by rw [map_mul, mul_assoc]
        _ = ai * j t ^ E * j u := by rw [hab, map_mul, map_pow, mul_assoc]
    rw [this]
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hE
    rw [hk, pow_add, pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.mem_span_singleton_self _
    · exact hbmem
  · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

end Vertical

section Ends

theorem mem_maximalIdeal_iff_inv_not_mem {K : Type*} [Field K] (X : ValuationSubring K) {z : K} (hz : z ∈ X) (hz0 : z ≠ 0) :
    (⟨z, hz⟩ : X) ∈ maximalIdeal X ↔ z⁻¹ ∉ X := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  exact mem_nonunits_iff_inv_not_mem X hz0

theorem mem_maximalIdeal_comap_iff {K : Type*} [Field K] {E : Type*} [Field E] (X : ValuationSubring K) (φ : E →+* K) (e : E)
    (he : e ∈ X.comap φ) : (⟨e, he⟩ : X.comap φ) ∈ maximalIdeal (X.comap φ) ↔ φ e ∈ X.nonunits := by
  by_cases he0 : e = 0
  · subst he0
    have h1 : (⟨(0 : E), he⟩ : X.comap φ) = 0 := rfl
    rw [h1, map_zero]
    exact ⟨fun _ => zero_mem_nonunits X, fun _ => Ideal.zero_mem _⟩
  · rw [mem_maximalIdeal_iff_inv_not_mem (X.comap φ) he he0, ValuationSubring.mem_comap, map_inv₀,
      mem_nonunits_iff_inv_not_mem X ((map_ne_zero φ).mpr he0)]

set_option maxHeartbeats 16000000 in

theorem mem_of_mem_layer_of_mem_end {F : Type*} [Field F]
    (𝒩₀ : Subring F) [IsLocalRing 𝒩₀] [IsNoetherianRing 𝒩₀] [CharZero F]
    [Algebra (FractionRing 𝒩₀) F] [IsScalarTower 𝒩₀ (FractionRing 𝒩₀) F]
    (𝔭 : Ideal 𝒩₀) [𝔭.IsPrime] (hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔭))
    (t : 𝒩₀) (ht0 : (t : F) ≠ 0)
    (hunif : maximalIdeal (Localization.AtPrime 𝔭) = Ideal.span {algebraMap 𝒩₀ (Localization.AtPrime 𝔭) t})
    (θ : F) (hθ : IsIntegral 𝒩₀ θ) (n : ℕ) (hn : 0 < n)
    (hθn : Module.finrank (FractionRing 𝒩₀) (FractionRing 𝒩₀)⟮θ⟯ ≤ n)
    (v w : F) (hv : v ∈ (FractionRing 𝒩₀)⟮θ⟯) (hw : w ∈ (FractionRing 𝒩₀)⟮θ⟯) (hvw : v * w = 1)
    (hvi : IsIntegral 𝒩₀ v) (hwi : IsIntegral 𝒩₀ w) (hθw : θ ^ n = (t : F) * w)
    (R O : ValuationSubring F) (hR : ∀ g : F, g ∈ 𝒩₀ → g ∈ R) (hO : ∀ g : F, g ∈ 𝒩₀ → g ∈ O)
    (htR : (t : F) ∈ R.nonunits) (htO : (t : F) ∈ O.nonunits)
    (hsR : ∀ s : 𝒩₀, s ∉ 𝔭 → (s : F)⁻¹ ∈ R) (hsO : ∀ s : 𝒩₀, s ∉ 𝔭 → (s : F)⁻¹ ∈ O)
    {g : F} (hg : g ∈ (FractionRing 𝒩₀)⟮θ⟯) (hgR : g ∈ R) : g ∈ O := by
  haveI := hdvr

  set F₀ := FractionRing 𝒩₀ with hF₀
  set Oℓ := Localization.AtPrime 𝔭 with hOℓ
  haveI : CharZero F₀ := (algebraMap F₀ F).charZero
  have hθ₀ : IsIntegral F₀ θ := hθ.tower_top
  haveI hfd : FiniteDimensional F₀ F₀⟮θ⟯ := IntermediateField.adjoin.finiteDimensional hθ₀

  letI algOE : Algebra Oℓ F₀⟮θ⟯ := ((algebraMap F₀ F₀⟮θ⟯).comp (algebraMap Oℓ F₀)).toAlgebra
  haveI : IsScalarTower Oℓ F₀ F₀⟮θ⟯ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hOE : ∀ z : Oℓ, ((algebraMap Oℓ F₀⟮θ⟯ z : F₀⟮θ⟯) : F) = algebraMap F₀ F (algebraMap Oℓ F₀ z) := fun _ => rfl
  have hNE : ∀ b : 𝒩₀, ((algebraMap 𝒩₀ F₀⟮θ⟯ b : F₀⟮θ⟯) : F) = (b : F) := fun _ => rfl
  have hNOF : ∀ b : 𝒩₀, algebraMap F₀ F (algebraMap Oℓ F₀ (algebraMap 𝒩₀ Oℓ b)) = (b : F) := by
    intro b
    rw [← IsScalarTower.algebraMap_apply 𝒩₀ Oℓ F₀, ← IsScalarTower.algebraMap_apply 𝒩₀ F₀ F]
    rfl
  haveI : IsScalarTower 𝒩₀ Oℓ F₀⟮θ⟯ := by
    refine IsScalarTower.of_algebraMap_eq (fun b => Subtype.ext ?_)
    rw [hNE, hOE, hNOF]
  haveI : IsScalarTower 𝒩₀ F₀⟮θ⟯ F := IsScalarTower.of_algebraMap_eq (fun b => (hNE b).symm)

  set θE : F₀⟮θ⟯ := ⟨θ, IntermediateField.mem_adjoin_simple_self F₀ θ⟩ with hθE
  set vE : F₀⟮θ⟯ := ⟨v, hv⟩ with hvE
  set wE : F₀⟮θ⟯ := ⟨w, hw⟩ with hwE
  have hinjE : Function.Injective (IsScalarTower.toAlgHom 𝒩₀ F₀⟮θ⟯ F) := fun a b h => Subtype.ext h
  have hvi' : IsIntegral Oℓ vE :=
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒩₀ F₀⟮θ⟯ F) hinjE (x := vE)).mp hvi).tower_top
  have hwi' : IsIntegral Oℓ wE :=
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒩₀ F₀⟮θ⟯ F) hinjE (x := wE)).mp hwi).tower_top
  have hwv : wE * vE = 1 := Subtype.ext (by change w * v = 1; rw [mul_comm]; exact hvw)
  set tℓ : Oℓ := algebraMap 𝒩₀ Oℓ t with htℓ
  have htℓ0 : tℓ ≠ 0 := by
    intro h
    apply ht0
    rw [← hNOF t, ← htℓ, h, map_zero, map_zero]
  have hirr : Irreducible tℓ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal tℓ htℓ0 hunif
  have hθpow : θE ^ n = algebraMap Oℓ F₀⟮θ⟯ tℓ * wE := by
    apply Subtype.ext
    change θ ^ n = ((algebraMap Oℓ F₀⟮θ⟯ tℓ : F₀⟮θ⟯) : F) * w
    rw [hOE, htℓ, hNOF, hθw]

  obtain ⟨-, Wv, hRW, -, -, -, -, -, hWuniq⟩ :=
    existsUnique_valuationSubring_of_pow_eq_mul Oℓ F₀ F₀⟮θ⟯ n hn hθn tℓ hirr wE vE hwv hwi' hvi' θE hθpow

  have htrace : ∀ X : ValuationSubring F, (∀ g : F, g ∈ 𝒩₀ → g ∈ X) → (t : F) ∈ X.nonunits →
      (∀ s : 𝒩₀, s ∉ 𝔭 → (s : F)⁻¹ ∈ X) → X.comap (algebraMap F₀⟮θ⟯ F) = Wv := by
    intro X hX htX hsX
    have hmem : ∀ r : Oℓ, algebraMap Oℓ F₀⟮θ⟯ r ∈ X.comap (algebraMap F₀⟮θ⟯ F) := by
      intro r
      obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj 𝔭.primeCompl r
      rw [ValuationSubring.mem_comap]
      change ((algebraMap Oℓ F₀⟮θ⟯ r : F₀⟮θ⟯) : F) ∈ X
      rw [hOE]
      have hs0 : ((s : 𝒩₀) : F) ≠ 0 := by
        intro h
        have : (s : 𝒩₀) = 0 := Subtype.ext h
        exact s.2 (this ▸ 𝔭.zero_mem)
      have hpsF : algebraMap F₀ F (algebraMap Oℓ F₀ r) * ((s : 𝒩₀) : F) = ((p : 𝒩₀) : F) := by
        have := congrArg (fun z => algebraMap F₀ F (algebraMap Oℓ F₀ z)) hps
        simp only [map_mul] at this
        rwa [hNOF, hNOF] at this
      have : algebraMap F₀ F (algebraMap Oℓ F₀ r) = ((p : 𝒩₀) : F) * (((s : 𝒩₀) : F))⁻¹ := by
        rw [← hpsF, mul_inv_cancel_right₀ hs0]
      rw [this]
      exact X.toSubring.mul_mem (hX _ p.2) (hsX s s.2)
    refine hWuniq _ hmem ?_
    intro r hr
    rw [mem_maximalIdeal_comap_iff]
    change ((algebraMap Oℓ F₀⟮θ⟯ r : F₀⟮θ⟯) : F) ∈ X.nonunits
    rw [hOE]
    rw [hunif, Ideal.mem_span_singleton] at hr
    obtain ⟨r₂, rfl⟩ := hr
    rw [map_mul, map_mul, htℓ, hNOF]
    have h2 : algebraMap F₀ F (algebraMap Oℓ F₀ r₂) ∈ X := by
      have := hmem r₂
      rw [ValuationSubring.mem_comap] at this
      exact this
    rw [mul_comm]
    exact mul_mem_nonunits_of_mem X h2 htX
  have hRO : R.comap (algebraMap F₀⟮θ⟯ F) = O.comap (algebraMap F₀⟮θ⟯ F) := by
    rw [htrace R hR htR hsR, htrace O hO htO hsO]
  have hgE : (⟨g, hg⟩ : F₀⟮θ⟯) ∈ R.comap (algebraMap F₀⟮θ⟯ F) := by
    rw [ValuationSubring.mem_comap]; exact hgR
  rw [hRO, ValuationSubring.mem_comap] at hgE
  exact hgE

end Ends

section Hartogs

set_option maxHeartbeats 16000000 in

theorem isIntegral_of_forall_valuationSubring {F : Type*} [Field F]
    (𝒩₀ : Subring F) [IsLocalRing 𝒩₀] [IsNoetherianRing 𝒩₀] [IsIntegrallyClosed 𝒩₀] [CharZero F]
    [Algebra (FractionRing 𝒩₀) F] [IsScalarTower 𝒩₀ (FractionRing 𝒩₀) F]
    (θ : F) (hθ : IsIntegral 𝒩₀ θ)
    (t x y : 𝒩₀) (ht0 : t ≠ 0)
    (𝔭 : Ideal 𝒩₀) [𝔭.IsPrime] (h𝔭 : 𝔭 = Ideal.span {t, y}) (hx𝔭 : x ∉ 𝔭)
    (g : F) (hg : g ∈ (FractionRing 𝒩₀)⟮θ⟯)
    (hval : ∀ O : ValuationSubring F, (∀ z : F, z ∈ 𝒩₀ → z ∈ O) → O ≠ ⊤ →
      ¬ ((t : F) ∈ O.nonunits ∧ (x : F) ∈ O.nonunits ∧ (y : F) ∈ O.nonunits) → g ∈ O) :
    IsIntegral 𝒩₀ g := by
  haveI : CharZero (FractionRing 𝒩₀) := (algebraMap (FractionRing 𝒩₀) F).charZero
  have hθ₀ : IsIntegral (FractionRing 𝒩₀) θ := hθ.tower_top
  haveI hfd : FiniteDimensional (FractionRing 𝒩₀) (FractionRing 𝒩₀)⟮θ⟯ := IntermediateField.adjoin.finiteDimensional hθ₀
  have hNE : ∀ b : 𝒩₀, ((algebraMap 𝒩₀ (FractionRing 𝒩₀)⟮θ⟯ b : (FractionRing 𝒩₀)⟮θ⟯) : F) = (b : F) := fun _ => rfl
  haveI : IsScalarTower 𝒩₀ (FractionRing 𝒩₀)⟮θ⟯ F := IsScalarTower.of_algebraMap_eq (fun b => (hNE b).symm)

  haveI : IsNoetherianRing (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) := integralClosure.isNoetherianRing (A := 𝒩₀) (K := (FractionRing 𝒩₀)) ↥(FractionRing 𝒩₀)⟮θ⟯
  haveI : IsIntegrallyClosed (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) := integralClosure.isIntegrallyClosedOfFiniteExtension (R := 𝒩₀) (FractionRing 𝒩₀)
  haveI : IsFractionRing (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) ↥(FractionRing 𝒩₀)⟮θ⟯ := integralClosure.isFractionRing_of_finite_extension (FractionRing 𝒩₀) ↥(FractionRing 𝒩₀)⟮θ⟯
  have h1E : ∀ z : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯), (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) (FractionRing 𝒩₀)⟮θ⟯ z) = (z : (FractionRing 𝒩₀)⟮θ⟯) := fun _ => rfl
  have h01 : ∀ b : 𝒩₀, ((algebraMap 𝒩₀ (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) b : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) : (FractionRing 𝒩₀)⟮θ⟯) = algebraMap 𝒩₀ (FractionRing 𝒩₀)⟮θ⟯ b := fun _ => rfl
  have hinj01 : Function.Injective (algebraMap 𝒩₀ (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) := by
    intro a b hab
    have := congrArg (fun z : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) => ((z : (FractionRing 𝒩₀)⟮θ⟯) : F)) hab
    simp only [h01, hNE] at this
    exact Subtype.ext this
  haveI : FaithfulSMul 𝒩₀ (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) := (faithfulSMul_iff_algebraMap_injective 𝒩₀ (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)).mpr hinj01
  set gE : (FractionRing 𝒩₀)⟮θ⟯ := ⟨g, hg⟩ with hgE
  suffices h : gE ∈ Set.range (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) (FractionRing 𝒩₀)⟮θ⟯) by
    obtain ⟨z, hz⟩ := h
    have hzint : IsIntegral 𝒩₀ (z : (FractionRing 𝒩₀)⟮θ⟯) := (mem_integralClosure_iff 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯).mp z.2
    have h3 : ((z : (FractionRing 𝒩₀)⟮θ⟯) : F) = g := by
      rw [h1E] at hz
      rw [hz]
    obtain ⟨p, hp, hpz⟩ := hzint
    refine ⟨p, hp, ?_⟩
    have := congrArg (algebraMap (FractionRing 𝒩₀)⟮θ⟯ F) hpz
    rw [Polynomial.hom_eval₂, map_zero] at this
    rw [← h3]
    exact this
  apply IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one gE
  intro 𝔓 h𝔓 hht
  haveI := h𝔓
  have h𝔓0 : 𝔓 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hht
    exact zero_ne_one hht

  set Loc := Localization.AtPrime 𝔓 with hLoc
  have hunits : ∀ s : 𝔓.primeCompl, IsUnit (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) (FractionRing 𝒩₀)⟮θ⟯ s) := by
    intro s
    apply IsUnit.mk0
    intro h0
    apply s.2
    have : (s : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) = 0 := by
      apply Subtype.ext
      rw [h1E] at h0
      exact h0
    rw [this]; exact 𝔓.zero_mem
  set ψ : Loc →+* (FractionRing 𝒩₀)⟮θ⟯ := IsLocalization.lift (M := 𝔓.primeCompl) hunits with hψ
  have hψ_alg : ∀ z : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯), ψ (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z) = (z : (FractionRing 𝒩₀)⟮θ⟯) := fun z => IsLocalization.lift_eq hunits z
  set φ : Loc →+* F := (algebraMap (FractionRing 𝒩₀)⟮θ⟯ F).comp ψ with hφ
  have hφ_alg : ∀ z : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯), φ (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z) = ((z : (FractionRing 𝒩₀)⟮θ⟯) : F) := by
    intro z; change algebraMap (FractionRing 𝒩₀)⟮θ⟯ F (ψ _) = _; rw [hψ_alg]; rfl
  obtain ⟨O, hOmem, hloc⟩ := IsLocalRing.exists_factor_valuationRing φ

  have h1O : ∀ z : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯), ((z : (FractionRing 𝒩₀)⟮θ⟯) : F) ∈ O := fun z => by rw [← hφ_alg]; exact hOmem _
  have h0O : ∀ z : F, z ∈ 𝒩₀ → z ∈ O := by
    intro z hz
    have := h1O (algebraMap 𝒩₀ (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) ⟨z, hz⟩)
    rwa [h01, hNE] at this

  have hdom : ∀ z : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯), z ∈ 𝔓 ↔ ((z : (FractionRing 𝒩₀)⟮θ⟯) : F) ∈ O.nonunits := by
    intro z
    constructor
    · intro hz
      have hm : algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z ∈ maximalIdeal Loc :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff Loc 𝔓 z).mpr hz
      have hnu : ¬ IsUnit (φ.codRestrict O.toSubring hOmem (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z)) := fun hu =>
        (mem_maximalIdeal _ |>.mp hm) (IsLocalHom.map_nonunit _ hu)
      have hmax : (⟨φ (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z), hOmem _⟩ : O) ∈ maximalIdeal O := hnu
      rw [← hφ_alg]
      exact ValuationSubring.coe_mem_nonunits_iff.mpr hmax
    · intro hz
      by_contra hz𝔓
      have hu : IsUnit (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z) :=
        IsLocalization.map_units Loc (⟨z, hz𝔓⟩ : 𝔓.primeCompl)
      have hu' : IsUnit (φ.codRestrict O.toSubring hOmem (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z)) := hu.map _
      have hmax : (⟨φ (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z), hOmem _⟩ : O) ∈ maximalIdeal O := by
        rw [← ValuationSubring.coe_mem_nonunits_iff]
        change φ (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc z) ∈ O.nonunits
        rwa [hφ_alg]
      exact (mem_maximalIdeal _ |>.mp hmax) hu'

  have hOtop : O ≠ ⊤ := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔓0
    refine ne_top_of_mem_nonunits O ?_ ((hdom z).mp hz)
    intro h
    apply hz0
    apply Subtype.ext
    exact Subtype.ext h
  by_cases hcase : (t : F) ∈ O.nonunits ∧ (x : F) ∈ O.nonunits ∧ (y : F) ∈ O.nonunits
  ·
    exfalso
    obtain ⟨htO, hxO, hyO⟩ := hcase
    set 𝔮 : Ideal 𝒩₀ := 𝔓.under 𝒩₀ with h𝔮
    have hmem𝔮 : ∀ b : 𝒩₀, b ∈ 𝔮 ↔ (b : F) ∈ O.nonunits := by
      intro b
      rw [h𝔮, Ideal.under_def, Ideal.mem_comap, hdom, h01, hNE]
    have hlt : 𝔭 < 𝔮 := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [h𝔭, Ideal.span_le]
        rintro b (rfl | rfl)
        · exact (hmem𝔮 _).mpr htO
        · exact (hmem𝔮 _).mpr hyO
      · intro h
        exact hx𝔭 (h ▸ (hmem𝔮 x).mpr hxO)
    haveI : 𝔓.LiesOver 𝔮 := ⟨rfl⟩
    obtain ⟨𝔓', hlt', h𝔓', hover⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := 𝔭) (q := 𝔮) 𝔓 hlt
    have ht𝔭 : t ∈ 𝔭 := by rw [h𝔭]; exact Ideal.subset_span (Set.mem_insert _ _)
    have h𝔓'0 : (⊥ : Ideal (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) < 𝔓' := by
      refine lt_of_le_of_ne bot_le ?_
      intro h
      have htm : algebraMap 𝒩₀ (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) t ∈ 𝔓' := by
        have : t ∈ 𝔓'.under 𝒩₀ := hover.1 ▸ ht𝔭
        rwa [Ideal.under_def, Ideal.mem_comap] at this
      rw [← h] at htm
      rw [Ideal.mem_bot] at htm
      exact ht0 (hinj01 (by rw [htm, map_zero]))
    have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime h𝔓'0
    have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt'
    rw [hht, ENat.lt_one_iff_eq_zero] at h2
    rw [h2, Ideal.height_bot] at h1
    exact lt_irrefl _ h1
  ·
    have hgO : g ∈ O := hval O h0O hOtop hcase
    haveI : IsDiscreteValuationRing Loc :=
      Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one 𝔓 hht
    obtain ⟨a₀, s₀, hs₀, hgas⟩ := IsFractionRing.div_surjective (A := (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) gE
    have hs₀0 : s₀ ≠ 0 := nonZeroDivisors.ne_zero hs₀
    have hs₀E : (s₀ : (FractionRing 𝒩₀)⟮θ⟯) ≠ 0 := fun h => hs₀0 (Subtype.ext h)
    have hgs : gE * (s₀ : (FractionRing 𝒩₀)⟮θ⟯) = a₀ := by
      rw [← hgas, h1E, h1E, div_mul_cancel₀ _ hs₀E]
    have hinjLoc : Function.Injective (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc) :=
      IsLocalization.injective Loc 𝔓.primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc a₀) (algebraMap (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯) Loc s₀)
    obtain ⟨⟨p', q⟩, hcq⟩ := IsLocalization.surj 𝔓.primeCompl c

    rcases hc with hc | hc
    ·
      have hrel : a₀ * p' = s₀ * (q : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) := by
        apply hinjLoc
        rw [map_mul, map_mul, ← hcq, ← mul_assoc, hc]
      by_cases hp' : p' ∈ 𝔓
      · exfalso

        have hgp : g * ((p' : (FractionRing 𝒩₀)⟮θ⟯) : F) = (((q : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) : (FractionRing 𝒩₀)⟮θ⟯) : F) := by
          have : gE * (p' : (FractionRing 𝒩₀)⟮θ⟯) = ((q : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) : (FractionRing 𝒩₀)⟮θ⟯) := by
            have h3 : gE * (p' : (FractionRing 𝒩₀)⟮θ⟯) * (s₀ : (FractionRing 𝒩₀)⟮θ⟯) = ((q : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) : (FractionRing 𝒩₀)⟮θ⟯) * (s₀ : (FractionRing 𝒩₀)⟮θ⟯) := by
              rw [mul_right_comm, hgs, ← Subalgebra.coe_mul, hrel, Subalgebra.coe_mul, mul_comm]
            exact mul_right_cancel₀ hs₀E h3
          exact congrArg (fun z : (FractionRing 𝒩₀)⟮θ⟯ => (z : F)) this
        have h4 : g * ((p' : (FractionRing 𝒩₀)⟮θ⟯) : F) ∈ O.nonunits := mul_mem_nonunits_of_mem O hgO ((hdom p').mp hp')
        rw [hgp] at h4
        exact q.2 ((hdom q).mpr h4)
      · refine ⟨q, p', hp', ?_⟩
        rw [h1E, h1E]
        have h3 : gE * (p' : (FractionRing 𝒩₀)⟮θ⟯) * (s₀ : (FractionRing 𝒩₀)⟮θ⟯) = ((q : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) : (FractionRing 𝒩₀)⟮θ⟯) * (s₀ : (FractionRing 𝒩₀)⟮θ⟯) := by
          rw [mul_right_comm, hgs, ← Subalgebra.coe_mul, hrel, Subalgebra.coe_mul, mul_comm]
        exact mul_right_cancel₀ hs₀E h3
    ·
      have hrel : s₀ * p' = a₀ * (q : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) := by
        apply hinjLoc
        rw [map_mul, map_mul, ← hcq, ← mul_assoc, hc]
      refine ⟨p', q, q.2, ?_⟩
      rw [h1E, h1E]
      have h3 : gE * ((q : (integralClosure 𝒩₀ ↥(FractionRing 𝒩₀)⟮θ⟯)) : (FractionRing 𝒩₀)⟮θ⟯) * (s₀ : (FractionRing 𝒩₀)⟮θ⟯) = (p' : (FractionRing 𝒩₀)⟮θ⟯) * (s₀ : (FractionRing 𝒩₀)⟮θ⟯) := by
        rw [mul_right_comm, hgs, ← Subalgebra.coe_mul, ← hrel, Subalgebra.coe_mul, mul_comm]
      exact mul_right_cancel₀ hs₀E h3

end Hartogs

section Layer

def jCN {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (𝒩₀ : Subring F) (C : Subring L) (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀) : C →+* 𝒩₀ :=
  ((algebraMap L F).comp C.subtype).codRestrict 𝒩₀ (fun c => hCmem c c.2)

theorem coe_jCN {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (𝒩₀ : Subring F) (C : Subring L) (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀) (c : C) :
    ((jCN 𝒩₀ C hCmem c : 𝒩₀) : F) = algebraMap L F (c : L) := rfl

theorem jCN_injective {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (𝒩₀ : Subring F) (C : Subring L) (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀) :
    Function.Injective (jCN 𝒩₀ C hCmem) := by
  intro a b h
  have := congrArg (fun z : 𝒩₀ => (z : F)) h
  simp only [coe_jCN] at this
  exact Subtype.ext ((algebraMap L F).injective this)

theorem isIntegral_algebraMap_of_isIntegral {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (𝒩₀ : Subring F) (C : Subring L)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀) {z : L} (hz : IsIntegral C z) :
    IsIntegral 𝒩₀ (algebraMap L F z) := by
  obtain ⟨p, hp, hpz⟩ := hz
  refine ⟨p.map (jCN 𝒩₀ C hCmem), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap 𝒩₀ F).comp (jCN 𝒩₀ C hCmem) = (algebraMap L F).comp (algebraMap C L) :=
    RingHom.ext (fun _ => rfl)
  rw [this, ← Polynomial.hom_eval₂, hpz, map_zero]

set_option maxHeartbeats 16000000 in

theorem exists_layer {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] [CharZero L]
    (A : ValuationSubring L) (𝒩₀ : Subring F) [IsLocalRing 𝒩₀] [IsNoetherianRing 𝒩₀]
    [Algebra (FractionRing 𝒩₀) F] [IsScalarTower 𝒩₀ (FractionRing 𝒩₀) F]
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)
    (hκ : ∀ a : ↥A, ∃ c : ↥C, a - ⟨(c : L), hC c c.2⟩ ∈ maximalIdeal ↥A)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)
    (f : F) (m : ℕ) (c : Fin m → L) (a : Fin m → ↥𝒩₀) (b : ↥𝒩₀) (hb : (b : F) ≠ 0)
    (hfb : f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F)) :
    ∃ (θ v w : F) (n : ℕ), 0 < n ∧ IsIntegral 𝒩₀ θ ∧
      Module.finrank (FractionRing 𝒩₀) (FractionRing 𝒩₀)⟮θ⟯ ≤ n ∧
      v ∈ (FractionRing 𝒩₀)⟮θ⟯ ∧ w ∈ (FractionRing 𝒩₀)⟮θ⟯ ∧ v * w = 1 ∧
      IsIntegral 𝒩₀ v ∧ IsIntegral 𝒩₀ w ∧ θ ^ n = algebraMap L F ((ϖ : ↥C) : L) * w ∧
      f ∈ (FractionRing 𝒩₀)⟮θ⟯ := by

  have hinjC : Function.Injective (algebraMap C L) := Subtype.val_injective
  letI algK : Algebra (FractionRing C) L := (IsFractionRing.lift hinjC).toAlgebra
  have hK_alg : ∀ x : C, algebraMap (FractionRing C) L (algebraMap C (FractionRing C) x) = (x : L) :=
    fun x => IsFractionRing.lift_algebraMap hinjC x
  haveI : IsScalarTower C (FractionRing C) L := IsScalarTower.of_algebraMap_eq (fun x => (hK_alg x).symm)
  have hinjCK : Function.Injective (algebraMap C (FractionRing C)) := IsFractionRing.injective C (FractionRing C)

  have halgL : ∀ z : L, IsAlgebraic C z := fun z => by
    rcases A.mem_or_inv_mem z with h | h
    · exact halg z h
    · exact IsAlgebraic.inv_iff.mp (halg _ h)
  have hintK : ∀ z : L, IsIntegral (FractionRing C) z := fun z =>
    (IsAlgebraic.extendScalars (S := FractionRing C) hinjCK (halgL z)).isIntegral

  haveI : FiniteDimensional (FractionRing C) (IntermediateField.adjoin (FractionRing C) (Set.range c)) :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => hintK z)
  obtain ⟨ϖ₁, v₀, w₀, -, hv₀K, hw₀K, hϖ₁i, hv₀i, hw₀i, hvw₀, hϖeq, hgenK⟩ :=
    ValuationSubring.exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq A C hC ϖ hϖ hϖ0 hκ
      huniq (FractionRing C) (IntermediateField.adjoin (FractionRing C) (Set.range c))
  set n := Module.finrank (FractionRing C) (IntermediateField.adjoin (FractionRing C) (Set.range c)) with hn
  have hn0 : 0 < n := Module.finrank_pos

  set θ : F := algebraMap L F ϖ₁ with hθ
  have hθi : IsIntegral 𝒩₀ θ := isIntegral_algebraMap_of_isIntegral 𝒩₀ C hCmem hϖ₁i
  have hθ₀ : IsIntegral (FractionRing 𝒩₀) θ := hθi.tower_top
  have hNF : ∀ z : F, z ∈ 𝒩₀ → z ∈ (FractionRing 𝒩₀)⟮θ⟯ := by
    intro z hz
    have : z = algebraMap (FractionRing 𝒩₀) F (algebraMap 𝒩₀ (FractionRing 𝒩₀) ⟨z, hz⟩) := by
      rw [← IsScalarTower.algebraMap_apply]; rfl
    rw [this]
    exact IntermediateField.algebraMap_mem _ _

  have hmemF : ∀ z : L, z ∈ (FractionRing C)⟮ϖ₁⟯ → algebraMap L F z ∈ (FractionRing 𝒩₀)⟮θ⟯ := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact IntermediateField.mem_adjoin_simple_self _ θ
    | algebraMap k =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := C) k
      rw [map_div₀, hK_alg, hK_alg, map_div₀]
      exact div_mem (hNF _ (hCmem _ p.2)) (hNF _ (hCmem _ q.2))
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hmemK₁ : ∀ z : L, z ∈ IntermediateField.adjoin (FractionRing C) (Set.range c) →
      algebraMap L F z ∈ (FractionRing 𝒩₀)⟮θ⟯ := fun z hz => hmemF z (hgenK ▸ hz)
  refine ⟨θ, algebraMap L F v₀, algebraMap L F w₀, n, hn0, hθi, ?_, hmemK₁ _ hv₀K, hmemK₁ _ hw₀K, ?_,
    isIntegral_algebraMap_of_isIntegral 𝒩₀ C hCmem hv₀i, isIntegral_algebraMap_of_isIntegral 𝒩₀ C hCmem hw₀i,
    ?_, ?_⟩
  ·
    set φ₀ : FractionRing C →+* FractionRing 𝒩₀ :=
      IsFractionRing.lift (g := (algebraMap 𝒩₀ (FractionRing 𝒩₀)).comp (jCN 𝒩₀ C hCmem))
        ((IsFractionRing.injective 𝒩₀ (FractionRing 𝒩₀)).comp (jCN_injective 𝒩₀ C hCmem)) with hφ₀
    have hφ₀_alg : ∀ x : C, φ₀ (algebraMap C (FractionRing C) x) =
        algebraMap 𝒩₀ (FractionRing 𝒩₀) (jCN 𝒩₀ C hCmem x) := fun x => IsFractionRing.lift_algebraMap _ x
    have hcomp : (algebraMap (FractionRing 𝒩₀) F).comp φ₀ = (algebraMap L F).comp (algebraMap (FractionRing C) L) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors C)
      ext x
      change algebraMap (FractionRing 𝒩₀) F (φ₀ (algebraMap C (FractionRing C) x)) =
        algebraMap L F (algebraMap (FractionRing C) L (algebraMap C (FractionRing C) x))
      rw [hφ₀_alg, hK_alg, ← IsScalarTower.algebraMap_apply]
      rfl
    set Q := (minpoly (FractionRing C) ϖ₁).map φ₀ with hQ
    have hQm : Q.Monic := (minpoly.monic (hintK ϖ₁)).map φ₀
    have hQθ : Polynomial.aeval θ Q = 0 := by
      rw [Polynomial.aeval_def, hQ, Polynomial.eval₂_map, hcomp, hθ, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    have hdvd : minpoly (FractionRing 𝒩₀) θ ∣ Q := minpoly.dvd _ θ hQθ
    have hdeg : (minpoly (FractionRing 𝒩₀) θ).natDegree ≤ (minpoly (FractionRing C) ϖ₁).natDegree := by
      have := Polynomial.natDegree_le_of_dvd hdvd hQm.ne_zero
      rwa [hQ, (minpoly.monic (hintK ϖ₁)).natDegree_map] at this
    rw [IntermediateField.adjoin.finrank hθ₀]
    refine hdeg.trans (le_of_eq ?_)
    rw [← IntermediateField.adjoin.finrank (hintK ϖ₁), hn, hgenK]
  · rw [← map_mul, hvw₀, map_one]
  · have : ϖ₁ ^ n = ((ϖ : ↥C) : L) * w₀ := by
      rw [hϖeq, mul_assoc, mul_left_comm, hvw₀, mul_one]
    rw [hθ, ← map_pow, this, map_mul]
  ·
    have hsum : f * (b : F) ∈ (FractionRing 𝒩₀)⟮θ⟯ := by
      rw [hfb]
      refine sum_mem fun i _ => ?_
      rw [Algebra.smul_def]
      exact mul_mem (hmemK₁ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)) (hNF _ (a i).2)
    have : f = f * (b : F) * (b : F)⁻¹ := by rw [mul_inv_cancel_right₀ hb]
    rw [this]
    exact mul_mem hsum (inv_mem (hNF _ b.2))

end Layer

section Values

theorem evalAt_mem_of_isIntegral {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (A : ValuationSubring L) (P : Place L F) (hP : P.IsRational)
    (𝒩₀ : Subring F) (hN : ∀ g : F, g ∈ 𝒩₀ → g ∈ P.toValuationSubring)
    (hNA : ∀ g : 𝒩₀, P.evalAt (g : F) ∈ A)
    {f : F} (hf : f ∈ P.toValuationSubring) (hfi : IsIntegral 𝒩₀ f) : P.evalAt f ∈ A := by
  set ψ := evalHom P hP with hψ
  set j := toValSub 𝒩₀ P.toValuationSubring hN with hj
  have hχA : ∀ g : 𝒩₀, (ψ.comp j) g ∈ A := by
    intro g
    change ψ (j g) ∈ A
    rw [evalHom_apply]
    exact hNA g
  set χA : 𝒩₀ →+* A := (ψ.comp j).codRestrict A hχA with hχA'
  obtain ⟨p, hp, hpf⟩ := hfi
  set fP : P.toValuationSubring := ⟨f, hf⟩ with hfP
  have h1 : Polynomial.eval₂ j fP p = 0 := by
    apply Subtype.val_injective
    change (P.toValuationSubring.subtype) (Polynomial.eval₂ j fP p) = ((0 : P.toValuationSubring) : F)
    rw [Polynomial.hom_eval₂]
    exact hpf
  have h2 : Polynomial.eval₂ (algebraMap A L) (ψ fP) (p.map χA) = 0 := by
    rw [Polynomial.eval₂_map]
    have : (algebraMap (↥A) L).comp χA = ψ.comp j := RingHom.ext (fun _ => rfl)
    rw [this, ← Polynomial.hom_eval₂, h1, map_zero]
  have hint : IsIntegral A (ψ fP) := ⟨p.map χA, hp.map _, h2⟩
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := L)).mp hint
  rw [evalAt_eq_evalHom P hP hf, ← hψ, ← hz]
  exact z.2

theorem evalAt_add {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (P : Place L F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring)
    (hg : g ∈ P.toValuationSubring) : P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  rw [evalAt_eq_evalHom P hP hf, evalAt_eq_evalHom P hP hg, evalAt_eq_evalHom P hP (add_mem hf hg), ← map_add]
  rfl

end Values

section Assembly

theorem not_isUnit_of_mem_nonunits {F : Type*} [Field F] (𝒩₀ : Subring F) (R : ValuationSubring F) (h : ∀ g : F, g ∈ 𝒩₀ → g ∈ R)
    {z : 𝒩₀} (hz : (z : F) ∈ R.nonunits) : ¬ IsUnit z := by
  intro hu
  obtain ⟨zi, hzi⟩ := hu.exists_right_inv
  have hzzi : (z : F) * (zi : F) = 1 := by
    have := congrArg (fun w : 𝒩₀ => (w : F)) hzi
    simpa using this
  have hz0 : (z : F) ≠ 0 := left_ne_zero_of_mul_eq_one hzzi
  have hinv : (z : F)⁻¹ = (zi : F) := inv_eq_of_mul_eq_one_right hzzi
  exact (mem_nonunits_iff_inv_not_mem R hz0).mp hz (hinv ▸ h _ zi.2)

theorem inv_mem_of_not_mem_span {F : Type*} [Field F] (𝒩₀ : Subring F) [IsLocalRing 𝒩₀] (t a b : 𝒩₀)
    (ha : a ∈ maximalIdeal 𝒩₀)
    (huq : ∀ 𝔮 : Ideal 𝒩₀, 𝔮.IsPrime → t ∈ 𝔮 → a ∉ 𝔮 → 𝔮 ≠ maximalIdeal 𝒩₀ → 𝔮 = Ideal.span {t, b})
    (O : ValuationSubring F) (hO : ∀ g : F, g ∈ 𝒩₀ → g ∈ O)
    (htO : (t : F) ∈ O.nonunits) (haO : (a : F) ∉ O.nonunits) :
    ∀ s : 𝒩₀, s ∉ Ideal.span {t, b} → (s : F)⁻¹ ∈ O := by
  have hcen : cen 𝒩₀ O hO = Ideal.span {t, b} := by
    refine huq _ (cen_isPrime 𝒩₀ O hO) ((mem_cen_iff _ _ _ _).mpr htO)
      (fun h => haO ((mem_cen_iff _ _ _ _).mp h)) ?_
    intro h
    exact haO ((mem_cen_iff _ _ _ _).mp (h ▸ ha))
  intro s hs
  rw [← hcen] at hs
  refine inv_mem_of_not_mem_cen 𝒩₀ O hO hs ?_
  intro h0
  apply hs
  have : s = 0 := Subtype.ext h0
  rw [this]
  exact Ideal.zero_mem _

end Assembly

end TubeMaxChild
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring.TubeMaxChild"

open TubeMaxChild in
set_option maxHeartbeats 16000000 in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)

    (hκ : ∀ a : ↥A, ∃ c : ↥C, a - ⟨(c : L), hC c c.2⟩ ∈ maximalIdeal ↥A)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)

    (R₁ R₂ : ValuationSubring F)
    (h₁ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₁) (h₂ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₂)
    (hϖ₁ : algebraMap L F ((ϖ : ↥C) : L) ∈ R₁.nonunits) (hϖ₂ : algebraMap L F ((ϖ : ↥C) : L) ∈ R₂.nonunits)

    (x y : ↥𝒩₀) (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hιx : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) x) =
      (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hιy : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) y) =
      (γV : UVCrossingModel W (π ^ E)) * V (π ^ E))
    (hx₁ : ((x : ↥𝒩₀) : F) ∉ R₁.nonunits) (hx₂ : ((x : ↥𝒩₀) : F) ∈ R₂.nonunits)
    (hy₁ : ((y : ↥𝒩₀) : F) ∈ R₁.nonunits) (hy₂ : ((y : ↥𝒩₀) : F) ∉ R₂.nonunits) :
    ∀ f : F, f ∈ R₁ → f ∈ R₂ → (∀ P ∈ S, f ∈ P.toValuationSubring) →
      IsIntegral ↥𝒩₀ f ∧ ∀ P ∈ S, P.evalAt f ∈ A := by
  intro f hf₁ hf₂ hfS

  letI algF₀ : Algebra (FractionRing 𝒩₀) F :=
    (IsFractionRing.lift (K := FractionRing 𝒩₀) (g := 𝒩₀.subtype) Subtype.val_injective).toAlgebra
  haveI : IsScalarTower 𝒩₀ (FractionRing 𝒩₀) F := IsScalarTower.of_algebraMap_eq
    (fun z => (IsFractionRing.lift_algebraMap (K := FractionRing 𝒩₀) (g := 𝒩₀.subtype) Subtype.val_injective z).symm)
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap L F).injective
  haveI : IsIntegrallyClosed 𝒩₀ :=
    IsLocalRing.isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel π hπ E hE ι

  set ϖN : 𝒩₀ := ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ with hϖN
  have hϖNF : (ϖN : F) = algebraMap L F ((ϖ : ↥C) : L) := rfl
  have hϖN0 : (ϖN : F) ≠ 0 := by rw [hϖNF]; exact (map_ne_zero _).mpr hϖ0
  have hϖNne : ϖN ≠ 0 := fun h => hϖN0 (by rw [h]; rfl)
  have ht : ι (algebraMap 𝒩₀ (AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀) ϖN) = const (π ^ E) π := by
    rw [hϖN, ← hσπ, hconst]
  have hϖNu : ¬ IsUnit ϖN := not_isUnit_of_mem_nonunits 𝒩₀ R₁ h₁ hϖ₁
  have hxm : x ∈ maximalIdeal 𝒩₀ := not_isUnit_of_mem_nonunits 𝒩₀ R₂ h₂ hx₂
  have hym : y ∈ maximalIdeal 𝒩₀ := not_isUnit_of_mem_nonunits 𝒩₀ R₁ h₁ hy₁

  obtain ⟨⟨u, hu, hxy⟩, ⟨hVp, hxV, hVuniq, hVht⟩, ⟨hUp, hyU, hUuniq, hUht⟩⟩ :=
    branch_primes 𝒩₀ π hπ E hE ι ϖN x y ht γU γV hιx hιy
  haveI := hVp
  haveI := hUp
  obtain ⟨hdvrV, hunifV⟩ := dvr_branch 𝒩₀ ϖN x y u hu E hE hxy (Ideal.span {ϖN, y}) rfl hxV hVht
  obtain ⟨hdvrU, hunifU⟩ :=
    dvr_branch 𝒩₀ ϖN y x u hu E hE (by rw [mul_comm]; exact hxy) (Ideal.span {ϖN, x}) rfl hyU hUht

  obtain ⟨m, c, a, b, hb, hfb⟩ := hgen f
  obtain ⟨θ, v, w, n, hn, hθi, hθn, hv, hw, hvw, hvi, hwi, hθw, hfθ⟩ :=
    exists_layer A 𝒩₀ C hC hCmem ϖ hϖ hϖ0 halg hκ huniq f m c a b hb hfb
  rw [← hϖNF] at hθw

  have hint : IsIntegral 𝒩₀ f := by
    refine isIntegral_of_forall_valuationSubring 𝒩₀ θ hθi ϖN x y hϖNne (Ideal.span {ϖN, y}) rfl hxV f hfθ ?_
    intro O hO hOtop hnot
    by_cases htO : (ϖN : F) ∈ O.nonunits
    · by_cases hxO : (x : F) ∈ O.nonunits
      ·
        have hyO : (y : F) ∉ O.nonunits := fun h => hnot ⟨htO, hxO, h⟩
        exact mem_of_mem_layer_of_mem_end 𝒩₀ (Ideal.span {ϖN, x}) hdvrU ϖN hϖN0 hunifU θ hθi n hn hθn v w hv hw
          hvw hvi hwi hθw R₂ O h₂ hO hϖ₂ htO
          (inv_mem_of_not_mem_span 𝒩₀ ϖN y x hym hUuniq R₂ h₂ hϖ₂ hy₂)
          (inv_mem_of_not_mem_span 𝒩₀ ϖN y x hym hUuniq O hO htO hyO) hfθ hf₂
      ·
        exact mem_of_mem_layer_of_mem_end 𝒩₀ (Ideal.span {ϖN, y}) hdvrV ϖN hϖN0 hunifV θ hθi n hn hθn v w hv hw
          hvw hvi hwi hθw R₁ O h₁ hO hϖ₁ htO
          (inv_mem_of_not_mem_span 𝒩₀ ϖN x y hxm hVuniq R₁ h₁ hϖ₁ hx₁)
          (inv_mem_of_not_mem_span 𝒩₀ ϖN x y hxm hVuniq O hO htO hxO) hfθ hf₁
    ·
      obtain ⟨P, hPS, hPO⟩ :=
        AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_toValuationSubring_eq_of_forall_mem_of_not_mem_nonunits
          A S 𝒩₀ hS C hC hCmem ϖ hϖ halg huniq hϖNu O hO htO hOtop
      rw [← hPO]
      exact hfS P hPS
  refine ⟨hint, fun P hP => ?_⟩

  have hPr : P.IsRational := hrat P hP
  have hN : ∀ g : F, g ∈ 𝒩₀ → g ∈ P.toValuationSubring := ((hS P).mp hP).1
  have hNA : ∀ g : 𝒩₀, P.evalAt (g : F) ∈ A := by
    intro g
    obtain ⟨o, ho⟩ := hres g
    obtain ⟨hmA, -⟩ := ((hS P).mp hP).2 _ ho
    have hoA : P.evalAt (algebraMap L F (o : L)) ∈ A := by
      rw [evalAt_algebraMap P hPr]
      exact hC _ o.2
    have hsum : (g : F) = ((g - ⟨algebraMap L F (o : L), hCmem o o.2⟩ : 𝒩₀) : F) + algebraMap L F (o : L) := by
      change (g : F) = (g : F) - algebraMap L F (o : L) + algebraMap L F (o : L)
      rw [sub_add_cancel]
    rw [hsum, evalAt_add P hPr (hN _ (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩ : 𝒩₀).2) (hN _ (hCmem o o.2))]
    exact A.toSubring.add_mem hmA hoA
  exact evalAt_mem_of_isIntegral A P hPr 𝒩₀ hN hNA (hfS P hP) hint

end
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring.TubeMaxChild"

end S_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring (solution)
