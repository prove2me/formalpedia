-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5390d95a-9079-5e02-8283-b6e40a49bcde

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace Dim2G2bE96

theorem two_le_ringKrullDim_of_not_subsingleton_minimalPrimes
    (O : Type u) [CommRing O] [IsDomain O] [IsLocalRing O] (a : O)
    (hmany : ¬ ((Ideal.span {a} : Ideal O).minimalPrimes).Subsingleton) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim O := by
  obtain ⟨P₁, hP₁, P₂, hP₂, hne⟩ := Set.not_subsingleton_iff.mp hmany
  have ha : a ≠ 0 := by
    rintro rfl
    apply hmany
    have : (Ideal.span {(0 : O)} : Ideal O) = ⊥ := by simp
    rw [this, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.subsingleton_singleton
  haveI hP₁p : P₁.IsPrime := hP₁.1.1
  haveI hP₂p : P₂.IsPrime := hP₂.1.1
  have hle₁ : Ideal.span {a} ≤ P₁ := hP₁.1.2
  have hle₂ : Ideal.span {a} ≤ P₂ := hP₂.1.2

  obtain ⟨P, hP, hPm⟩ : ∃ P ∈ (Ideal.span {a} : Ideal O).minimalPrimes,
      P ≠ IsLocalRing.maximalIdeal O := by
    by_cases h₁ : P₁ = IsLocalRing.maximalIdeal O
    · exact ⟨P₂, hP₂, fun h₂ => hne (h₁.trans h₂.symm)⟩
    · exact ⟨P₁, hP₁, h₁⟩
  haveI hPp : P.IsPrime := hP.1.1
  have haP : a ∈ P := hP.1.2 (Ideal.subset_span rfl)
  have hbot : (⊥ : Ideal O) < P := by
    rw [bot_lt_iff_ne_bot]
    intro h
    exact ha (by simpa [h] using haP)
  have htop : P < IsLocalRing.maximalIdeal O :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hPp.ne_top) hPm

  let b : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  let p : PrimeSpectrum O := ⟨P, hPp⟩
  let m : PrimeSpectrum O := ⟨IsLocalRing.maximalIdeal O, inferInstance⟩
  have hbp : b < p := hbot
  have hpm : p < m := htop
  have hlt : 1 < Order.height m := Order.one_lt_height_iff.mpr ⟨p, b, hbp, hpm⟩
  have h2 : (2 : ℕ∞) ≤ Order.height m := by
    have := Order.add_one_le_of_lt hlt
    simpa [one_add_one_eq_two] using this
  have h2' : (2 : WithBot ℕ∞) ≤ (Order.height m : WithBot ℕ∞) := by
    have h3 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.height m : WithBot ℕ∞) := WithBot.coe_le_coe.mpr h2
    simpa using h3
  exact h2'.trans (Order.height_le_krullDim m)

section chart
variable (R : Type u) [CommRing R] [IsNoetherianRing R] (F : Type u) [Field F] [Algebra R F] (t : F)

theorem ringKrullDim_adjoin_le (hR : ringKrullDim R = 1) :
    ringKrullDim ↥(Algebra.adjoin R ({t} : Set F)) ≤ 2 := by
  set B : Subalgebra R F := Algebra.adjoin R ({t} : Set F)
  let tB : B := ⟨t, Algebra.self_mem_adjoin_singleton R t⟩
  let f : R[X] →+* B := (Polynomial.aeval tB).toRingHom
  have hf : Function.Surjective f := by
    intro b
    have hb : (b : F) ∈ (Polynomial.aeval (R := R) t).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval R t]; exact b.2
    obtain ⟨q, hq⟩ := hb
    refine ⟨q, Subtype.ext ?_⟩
    change ((Polynomial.aeval tB q : B) : F) = b
    rw [← hq]
    exact (Polynomial.aeval_algHom_apply B.val tB q).symm
  calc ringKrullDim B ≤ ringKrullDim R[X] := ringKrullDim_le_of_surjective f hf
    _ = ringKrullDim R + 1 := Polynomial.ringKrullDim_of_isNoetherianRing
    _ = 2 := by rw [hR]; rfl

theorem ringKrullDim_chartAlg_le (hR : ringKrullDim R = 1) :
    ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F ({t} : Set F)) ≤ 2 := by
  set B : Subalgebra R F := Algebra.adjoin R ({t} : Set F)
  set A : Subalgebra R F := AlgebraicCurve.TwoChartIntegralModel.chartAlg R F ({t} : Set F)
  have hBA : B ≤ A := AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg R F _
  letI : Algebra B A := (Subalgebra.inclusion hBA).toAlgebra
  have hint : ∀ x : A, IsIntegral B x := by
    intro x
    have hx : IsIntegral B (x : F) := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff R F).mp x.2

    haveI : IsScalarTower B A F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B A F) Subtype.val_injective).mp hx
  have hmono : StrictMono (fun P : PrimeSpectrum A =>
      (⟨P.asIdeal.comap (algebraMap B A), inferInstance⟩ : PrimeSpectrum B)) := by
    intro P Q hPQ
    have hlt : P.asIdeal < Q.asIdeal := hPQ
    obtain ⟨x, hxQ, hxP⟩ := Set.exists_of_ssubset hlt
    change Ideal.comap (algebraMap B A) P.asIdeal < Ideal.comap (algebraMap B A) Q.asIdeal
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff hlt.le ⟨hxQ, hxP⟩ (hint x)
  calc ringKrullDim A ≤ ringKrullDim B := Order.krullDim_le_of_strictMono _ hmono
    _ ≤ 2 := ringKrullDim_adjoin_le R F t hR

theorem ringKrullDim_localization_chartAlg_le (hR : ringKrullDim R = 1)
    (q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F ({t} : Set F))) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q) ≤ 2 := by
  have hmono : StrictMono (fun P : PrimeSpectrum (Localization.AtPrime q) =>
      (⟨P.asIdeal.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F ({t} : Set F))
        (Localization.AtPrime q)), inferInstance⟩ :
        PrimeSpectrum ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F ({t} : Set F)))) := by
    intro P Q hPQ
    have hlt : P.asIdeal < Q.asIdeal := hPQ
    change Ideal.comap _ P.asIdeal < Ideal.comap _ Q.asIdeal
    exact (IsLocalization.orderEmbedding q.primeCompl (Localization.AtPrime q)).strictMono hlt
  calc ringKrullDim (Localization.AtPrime q)
      ≤ ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F ({t} : Set F)) :=
        Order.krullDim_le_of_strictMono _ hmono
    _ ≤ 2 := ringKrullDim_chartAlg_le R F t hR

end chart

theorem ringKrullDim_stalk_eq_of_chart
    {A : Type u} [CommRing A] {X : Scheme.{u}} (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (y : PrimeSpectrum A) :
    ringKrullDim (X.presheaf.stalk (ι.base y)) = ringKrullDim (Localization.AtPrime y.asIdeal) := by
  let e₁ : Localization.AtPrime y.asIdeal ≃+* (Spec (CommRingCat.of A)).presheaf.stalk y :=
    (StructureSheaf.stalkIso A y).toRingEquiv
  haveI : IsIso (ι.stalkMap y) := inferInstance
  let e₂ : X.presheaf.stalk (ι.base y) ≃+* (Spec (CommRingCat.of A)).presheaf.stalk y :=
    (asIso (ι.stalkMap y)).commRingCatIsoToRingEquiv
  exact ringKrullDim_eq_of_ringEquiv (e₂.trans e₁.symm)

end Dim2G2bE96

end

open AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R = 1)
    (F : Type u) [Field F] [Algebra R F] (hinj : Function.Injective (algebraMap R F))
    (j : F) [Fact (j ≠ 0)]
    (ϖ : R) (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))
    (hmany : ¬ ((Ideal.span {ϖz} : Ideal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)).minimalPrimes).Subsingleton) :
    ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) = 2  := by
  haveI : IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegral R F j
  refine le_antisymm ?_ (Dim2G2bE96.two_le_ringKrullDim_of_not_subsingleton_minimalPrimes _ ϖz hmany)
  rcases mem_range_ιFin_or_mem_range_ιInf R F j z with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rw [Dim2G2bE96.ringKrullDim_stalk_eq_of_chart (ιFin R F j) y]
    exact Dim2G2bE96.ringKrullDim_localization_chartAlg_le R F j hR y.asIdeal
  · rw [Dim2G2bE96.ringKrullDim_stalk_eq_of_chart (ιInf R F j) y]
    exact Dim2G2bE96.ringKrullDim_localization_chartAlg_le R F j⁻¹ hR y.asIdeal

end S_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes (solution)
