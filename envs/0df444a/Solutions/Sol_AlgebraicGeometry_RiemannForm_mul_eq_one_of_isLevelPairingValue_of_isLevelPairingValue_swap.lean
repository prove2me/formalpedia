-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.mul_eq_one_of_isLevelPairingValue_of_isLevelPairingValue_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/491a63a1-ad82-5711-a766-281066c8a6c0

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
import Theorems.Thm_Subgroup_commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_mul_eq_one_of_isLevelPairingValue_of_isLevelPairingValue_swap
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

open scoped commutatorElement

namespace B16RFALT

theorem commutator_mul_commutator_eq_one
    {G : Type*} [Group G] (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (hcomm : ∀ g h : G, ⁅g, h⁆ ∈ Z)
    (a a₁ b b₁ : G) (n : ℕ) (ha : a⁻¹ * a₁ ^ n ∈ Z) (hb : b⁻¹ * b₁ ^ n ∈ Z) :
    ⁅a, b₁⁆ * ⁅b, a₁⁆ = 1 := by
  obtain ⟨hdesc, hL, hR, hskew, hself, hpow⟩ :=
    Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center Z hZ hcomm
  have h1 : ⁅a, b₁⁆ = ⁅a₁, b₁⁆ ^ n := by
    rw [hdesc a (a₁ ^ n) b₁ b₁ ha (by rw [inv_mul_cancel]; exact Z.one_mem), (hpow a₁ b₁ n).1]
  have h2 : ⁅b, a₁⁆ = ⁅b₁, a₁⁆ ^ n := by
    rw [hdesc b (b₁ ^ n) a₁ a₁ hb (by rw [inv_mul_cancel]; exact Z.one_mem), (hpow b₁ a₁ n).1]
  have hc : Commute ⁅a₁, b₁⁆ ⁅b₁, a₁⁆ := by
    have := Subgroup.mem_center_iff.1 (hZ (hcomm a₁ b₁)) ⁅b₁, a₁⁆
    exact this.symm
  rw [h1, h2, ← hc.mul_pow, hskew, one_pow]

theorem nsmul_fst_eq_nsmul_fst {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) {t t' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)} (h : t = t')
    (n : ℕ) (P : SchemeHomOver t f) (P' : SchemeHomOver t' f) (hPP' : P.1 = P'.1) :
    (L.nsmul t n P).1 = (L.nsmul t' n P').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hPP'
  rfl

theorem connectedSpace_of_abelianSchemePropertyBundle {k : Type} [Field k] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k f) : ConnectedSpace A := by
  rw [connectedSpace_iff_univ]
  let s : Spec (CommRingCat.of k) := ⟨⊥, Ideal.bot_prime⟩
  have hs : f.base ⁻¹' {s} = Set.univ := by
    refine Set.eq_univ_of_forall (fun a => ?_)
    show f.base a = s
    apply PrimeSpectrum.ext
    exact Ideal.eq_bot_of_prime _
  rw [← hs]
  exact hA.connectedFibres s

theorem exists_nsmul_eq (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (n : ℕ) (hn : (n : k) ≠ 0) (y : L.AlgPoints hc k) : ∃ y₁ : L.AlgPoints hc k, n • y₁ = y := by
  haveI : Smooth f := hA.smooth
  haveI : ConnectedSpace A := connectedSpace_of_abelianSchemePropertyBundle hA
  obtain ⟨P₁, hP₁⟩ := GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace L
    (fun t x y => hc.mul_comm t x y) n (isUnit_iff_ne_zero.2 hn) (toUnitPt f (RelativeGroupLaw.AlgPoints.toPoint y))
  refine ⟨RelativeGroupLaw.AlgPoints.ofPoint (ofUnitPt f P₁), ?_⟩
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  apply Subtype.ext
  rw [RelativeGroupLaw.AlgPoints.toPoint_nsmul, RelativeGroupLaw.AlgPoints.toPoint_ofPoint,
    nsmul_fst_eq_nsmul_fst L (specMap_algebraMap_self) n (ofUnitPt f P₁) P₁ rfl, hP₁]
  rfl

end B16RFALT

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (n : ℕ) (hn : (n : k) ≠ 0) (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (c c' : k)
    (h₁ : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c)
    (h₂ : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint Q) (RelativeGroupLaw.AlgPoints.toPoint P) c') :
    c * c' = 1 := by
  classical

  have hM : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) :=
    Scheme.Modules.IsInvertible.pullback _ h𝓛
  obtain ⟨hcen, hcomm⟩ := thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker k f L hc hA _ hM
  obtain ⟨huniq, hmul, hone, -⟩ := thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul k f L hc hA _ hM

  have hxP := translation_comp_schemeNsmul_of_nsmul_eq_zero k f L hc P n hP
  have hxQ := translation_comp_schemeNsmul_of_nsmul_eq_zero k f L hc Q n hQ

  obtain ⟨Q₁, hQ₁⟩ := B16RFALT.exists_nsmul_eq k L hc hA n hn Q
  obtain ⟨P₁, hP₁⟩ := B16RFALT.exists_nsmul_eq k L hc hA n hn P

  obtain ⟨gy, hgy, s₁⟩ := (thetaGroup.isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
    k f L hc 𝓛 n P hxP c).2 Q₁ (by rw [hQ₁]; exact h₁)
  obtain ⟨gx, hgx, s₂⟩ := (thetaGroup.isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
    k f L hc 𝓛 n Q hxQ c').2 P₁ (by rw [hP₁]; exact h₂)

  have hmemP : (levelLift f L hc 𝓛 n P hxP)⁻¹ * gx ^ n ∈ (thetaGroup.pt f L hc _).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, pt_levelLift, hgx, ← ofAdd_nsmul, hP₁, inv_mul_cancel]
  have hmemQ : (levelLift f L hc 𝓛 n Q hxQ)⁻¹ * gy ^ n ∈ (thetaGroup.pt f L hc _).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, pt_levelLift, hgy, ← ofAdd_nsmul, hQ₁, inv_mul_cancel]

  have hprod : ⁅levelLift f L hc 𝓛 n P hxP, gy⁆ * ⁅levelLift f L hc 𝓛 n Q hxQ, gx⁆ = 1 :=
    B16RFALT.commutator_mul_commutator_eq_one _ hcen hcomm _ gx _ gy n hmemP hmemQ

  have s₁₂ := hmul _ _ _ _ s₁ s₂
  rw [hprod] at s₁₂
  obtain ⟨c₀, -, hc₀⟩ := huniq 1 (map_one _)
  exact (hc₀ _ s₁₂).trans (hc₀ _ hone).symm

end S_AlgebraicGeometry_RiemannForm_mul_eq_one_of_isLevelPairingValue_of_isLevelPairingValue_swap
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_mul_eq_one_of_isLevelPairingValue_of_isLevelPairingValue_swap (solution)
