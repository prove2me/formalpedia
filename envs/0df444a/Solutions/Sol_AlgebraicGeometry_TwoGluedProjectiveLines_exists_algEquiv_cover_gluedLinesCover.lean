-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedProjectiveLines.exists_algEquiv_cover_gluedLinesCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6979b4bd-caa1-5664-a8dc-eefc0962d4cb

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_TwoChartCech_GluedLines
import Theorems.Thm_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover.AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover.AlgebraicCurve"

universe u

section eng15_NT
open Opposite

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel Place Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum RationalFunctionField.placeOfPoint RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum RationalFunctionField.placeOfPoint_injective RationalFunctionField.placeInfty RationalFunctionField.placeInfty_toValuationSubring CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl"
p2m_open "AlgebraicCurve"

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal placeOfPoint placeOfPoint_eq_ofHeightOneSpectrum placeOfPoint_injective placeInfty placeInfty_toValuationSubring"
p2m_open "AlgebraicCurve.RationalFunctionField"

p2m_open "Polynomial AlgebraicGeometry.Polynomial IsDedekindDomain"

variable (k : Type u) [Field k]

theorem eval_denom_ne_zero_of_mem_placeOfPoint (c : k) (f : RatFunc k)
    (hf : f ∈ (placeOfPoint k c).toValuationSubring) : f.denom.eval c ≠ 0 := by
  set w := heightOneSpectrumOfIrreducible k (irreducible_X_sub_C c) with hw
  have hfval : w.valuation (RatFunc k) f ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := k) (F := RatFunc k) w).le_one_iff_le_one.mpr
      ((Place.mem_iff_adicValuation_le_one _).mp hf)
  have hden_ne : algebraMap k[X] (RatFunc k) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr f.denom_ne_zero
  have hmul : f * algebraMap k[X] (RatFunc k) f.denom = algebraMap k[X] (RatFunc k) f.num :=
    ((div_eq_iff hden_ne).mp f.num_div_denom).symm
  have hden : f.denom ∉ w.asIdeal := by
    intro hd
    have hnum : f.num ∉ w.asIdeal := by
      intro hn
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
      obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom f
      exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
    have h1 : w.valuation (RatFunc k) (algebraMap k[X] (RatFunc k) f.num) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
    refine absurd h1 (ne_of_lt ?_)
    calc w.valuation (RatFunc k) (algebraMap k[X] (RatFunc k) f.num)
        = w.valuation (RatFunc k) f * w.valuation (RatFunc k) (algebraMap k[X] (RatFunc k) f.denom) := by
          rw [← map_mul, hmul]
      _ ≤ w.valuation (RatFunc k) (algebraMap k[X] (RatFunc k) f.denom) := mul_le_of_le_one_left' hfval
      _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w f.denom).mpr hd
  intro h0
  apply hden
  rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton]
  exact dvd_iff_isRoot.mpr h0

theorem sub_C_eval_mem_nonunits_placeOfPoint (c : k) (f : RatFunc k)
    (hf : f ∈ (placeOfPoint k c).toValuationSubring) :
    f - RatFunc.C (RatFunc.eval (RingHom.id k) c f) ∈
      (placeOfPoint k c).toValuationSubring.nonunits := by
  set w := heightOneSpectrumOfIrreducible k (irreducible_X_sub_C c) with hw
  have hden0 := eval_denom_ne_zero_of_mem_placeOfPoint k c f hf
  set e : k := RatFunc.eval (RingHom.id k) c f with he

  set r : k[X] := f.num - Polynomial.C e * f.denom with hr
  have hden_ne : algebraMap k[X] (RatFunc k) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr f.denom_ne_zero
  have hfr : f - RatFunc.C e = algebraMap k[X] (RatFunc k) r / algebraMap k[X] (RatFunc k) f.denom := by
    rw [eq_div_iff hden_ne, sub_mul, hr, map_sub, map_mul]
    congr 1
    exact ((div_eq_iff hden_ne).mp f.num_div_denom).symm
  have hre : r.eval c = 0 := by
    have : e = f.num.eval c / f.denom.eval c := by
      rw [he, RatFunc.eval, Polynomial.eval₂_id, Polynomial.eval₂_id]
    rw [hr, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, this, div_mul_cancel₀ _ hden0,
      sub_self]
  have hrmem : r ∈ w.asIdeal := by
    rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton]
    exact dvd_iff_isRoot.mpr hre
  have hden : f.denom ∉ w.asIdeal := by
    intro hd; apply hden0
    rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton] at hd
    exact dvd_iff_isRoot.mp hd

  have hlt : w.valuation (RatFunc k) (f - RatFunc.C e) < 1 := by
    rw [hfr, map_div₀, (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hden, div_one]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w r).mpr hrmem

  have hmem : f - RatFunc.C e ∈ (placeOfPoint k c).toValuationSubring :=
    (Place.mem_iff_adicValuation_le_one _).mpr
      ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := k) (F := RatFunc k) w).le_one_iff_le_one.mp
        hlt.le)
  have hlt' : (placeOfPoint k c).adicValuation (f - RatFunc.C e) < 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := k) (F := RatFunc k) w).lt_one_iff_lt_one.mp hlt
  have := (Place.mem_maximalIdeal_iff_adicValuation_lt_one (placeOfPoint k c) ⟨_, hmem⟩).mpr hlt'
  exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmem⟩)).mpr this

end RationalFunctionField

end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel Place Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum RationalFunctionField.placeOfPoint RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum RationalFunctionField.placeOfPoint_injective RationalFunctionField.placeInfty RationalFunctionField.placeInfty_toValuationSubring CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "placeEquiv placeEquiv_apply placeOfPoint mk.injEq toBase C range_stalk_eq ffEquiv ffEquiv_algebraMap smooth mk range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L] (M : CurveModel k L)

private noncomputable def _root_.AlgebraicCurve.CurveModel.stalkToFF (P : closedPoints M.C) : M.C.presheaf.stalk P.1 →+* L :=
  (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
    (algebraMap (M.C.presheaf.stalk P.1) M.C.functionField)

p2m_export "AlgebraicCurve.CurveModel" "stalkToFF"
private theorem _root_.AlgebraicCurve.CurveModel.stalkToFF_injective (P : closedPoints M.C) : Function.Injective (M.stalkToFF P) :=
  M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk P.1) M.C.functionField)

p2m_export "AlgebraicCurve.CurveModel" "stalkToFF_injective"
theorem range_stalkToFF (P : closedPoints M.C) :
    (M.stalkToFF P).range = (M.placeOfPoint P).toValuationSubring.toSubring :=
  M.range_stalk_eq P

private theorem _root_.AlgebraicCurve.CurveModel.stalkToFF_mem (P : closedPoints M.C) (s : M.C.presheaf.stalk P.1) :
    M.stalkToFF P s ∈ (M.placeOfPoint P).toValuationSubring := by
  have : M.stalkToFF P s ∈ (M.stalkToFF P).range := ⟨s, rfl⟩
  rw [range_stalkToFF] at this
  exact this

p2m_export "AlgebraicCurve.CurveModel" "stalkToFF_mem"

theorem isUnit_iff_isUnit_stalkToFF (P : closedPoints M.C) (s : M.C.presheaf.stalk P.1) :
    IsUnit s ↔ IsUnit (⟨M.stalkToFF P s, M.stalkToFF_mem P s⟩ : (M.placeOfPoint P).toValuationSubring) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨⟨M.stalkToFF P u, M.stalkToFF_mem P u⟩, ⟨M.stalkToFF P ↑u⁻¹, M.stalkToFF_mem P _⟩, ?_, ?_⟩, rfl⟩
    · ext
      show M.stalkToFF P u * M.stalkToFF P ↑u⁻¹ = 1
      rw [← map_mul, Units.mul_inv, map_one]
    · ext
      show M.stalkToFF P ↑u⁻¹ * M.stalkToFF P u = 1
      rw [← map_mul, Units.inv_mul, map_one]
  · rintro ⟨u, hu⟩

    have hinv : ((u⁻¹ : ((M.placeOfPoint P).toValuationSubring)ˣ) : (M.placeOfPoint P).toValuationSubring).1 ∈
        (M.stalkToFF P).range := by
      rw [range_stalkToFF]; exact ((u⁻¹ : ((M.placeOfPoint P).toValuationSubring)ˣ) : (M.placeOfPoint P).toValuationSubring).2
    obtain ⟨t, ht⟩ := hinv
    have hst : M.stalkToFF P (s * t) = 1 := by
      rw [map_mul, ht]
      have := congrArg (fun z : (M.placeOfPoint P).toValuationSubring => (z : L)) u.mul_inv
      rw [hu] at this
      exact this
    have hst' : s * t = 1 := M.stalkToFF_injective P (by rw [hst, map_one])
    exact IsUnit.of_mul_eq_one _ hst'

theorem mem_maximalIdeal_iff (P : closedPoints M.C) (s : M.C.presheaf.stalk P.1) :
    s ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk P.1) ↔
      M.stalkToFF P s ∈ (M.placeOfPoint P).toValuationSubring.nonunits := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_isUnit_stalkToFF]
  exact ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, M.stalkToFF_mem P s⟩)).trans
    ((IsLocalRing.mem_maximalIdeal _).trans mem_nonunits_iff)).symm

private theorem _root_.AlgebraicCurve.CurveModel.stalkToFF_germ (P : closedPoints M.C) (W : M.C.Opens) [Nonempty W] (hP : P.1 ∈ W) (g : Γ(M.C, W)) :
    M.stalkToFF P (M.C.presheaf.germ W P.1 hP g) =
      ((M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap Γ(M.C, W) M.C.functionField)) g := by
  show M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk P.1) M.C.functionField (M.C.presheaf.germ W P.1 hP g)) =
    M.ffEquiv.symm (algebraMap Γ(M.C, W) M.C.functionField g)
  congr 1
  have := (IsScalarTower.algebraMap_apply Γ(M.C, W) (M.C.presheaf.stalk (⟨P.1, hP⟩ : W).1) M.C.functionField g)
  exact this.symm

p2m_export "AlgebraicCurve.CurveModel" "stalkToFF_germ"

theorem stalkToFF_germ_algebraMap (P : closedPoints M.C) (W : M.C.Opens) (hP : P.1 ∈ W) (a : k) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase W
    M.stalkToFF P (M.C.presheaf.germ W P.1 hP (algebraMap k Γ(M.C, W) a)) = algebraMap k L a := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase W
  apply M.ffEquiv.injective
  rw [M.ffEquiv_algebraMap]
  show M.ffEquiv (M.ffEquiv.symm _) = _
  rw [RingEquiv.apply_symm_apply, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]

  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply, RingHom.algebraMap_toAlgebra]
  show (M.C.presheaf.germ ⊤ P.1 trivial ≫ M.C.presheaf.stalkSpecializes _) _ = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  rfl

private theorem _root_.AlgebraicCurve.CurveModel.evaluation_eq_evaluation_algebraMap_of_sub_mem_nonunits (P : closedPoints M.C) (W : M.C.Opens) [Nonempty W]
    (hP : P.1 ∈ W) (g : Γ(M.C, W)) (e : k)
    (he : ((M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap Γ(M.C, W) M.C.functionField)) g
        - algebraMap k L e ∈ (M.placeOfPoint P).toValuationSubring.nonunits) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase W
    M.C.evaluation W P.1 hP g = M.C.evaluation W P.1 hP (algebraMap k Γ(M.C, W) e) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase W
  show M.C.residue P.1 (M.C.presheaf.germ W P.1 hP g) = M.C.residue P.1 (M.C.presheaf.germ W P.1 hP _)
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [mem_maximalIdeal_iff, map_sub, stalkToFF_germ, stalkToFF_germ_algebraMap]
  exact he

p2m_export "AlgebraicCurve.CurveModel" "evaluation_eq_evaluation_algebraMap_of_sub_mem_nonunits"
end AlgebraicCurve.CurveModel

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel Place Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum RationalFunctionField.placeOfPoint RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum RationalFunctionField.placeOfPoint_injective RationalFunctionField.placeInfty RationalFunctionField.placeInfty_toValuationSubring CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "placeEquiv placeEquiv_apply placeOfPoint mk.injEq toBase C range_stalk_eq ffEquiv ffEquiv_algebraMap smooth mk range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

private theorem _root_.AlgebraicCurve.CurveModel.evaluation_eq_evaluation_algebraMap_eval {k : Type u} [Field k] (M : CurveModel k (RatFunc k))
    (W : M.C.Opens) [Nonempty W] (c : k)
    (hP : (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k c)).1 ∈ W) (g : Γ(M.C, W)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase W
    M.C.evaluation W _ hP g =
      M.C.evaluation W _ hP (algebraMap k Γ(M.C, W)
        (RatFunc.eval (RingHom.id k) c
          (((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M.C, W) M.C.functionField)) g))) := by
  set P := M.placeEquiv.symm (RationalFunctionField.placeOfPoint k c) with hPdef
  have hv : M.placeOfPoint P = RationalFunctionField.placeOfPoint k c := by
    rw [← placeEquiv_apply, hPdef, Equiv.apply_symm_apply]
  apply M.evaluation_eq_evaluation_algebraMap_of_sub_mem_nonunits P W hP g
  rw [hv]
  have hf : ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc k).toRingHom.comp
      (algebraMap Γ(M.C, W) M.C.functionField)) g ∈ (RationalFunctionField.placeOfPoint k c).toValuationSubring := by
    rw [← hv, ← M.stalkToFF_germ P W hP g]
    exact M.stalkToFF_mem P _
  exact RationalFunctionField.sub_C_eval_mem_nonunits_placeOfPoint k c _ hf

p2m_export "AlgebraicCurve.CurveModel" "evaluation_eq_evaluation_algebraMap_eval"
end AlgebraicCurve.CurveModel

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.evaluation_naturality_apply basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appLE_map'_assoc Spec Scheme Scheme.Hom.naturality IsClosedImmersion IsReduced Scheme.Hom.comp_app IsAffineOpen Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen"
namespace TwoGluedProjectiveLines
p2m_open "AlgebraicGeometry"

open CategoryTheory.Limits

theorem evaluation_map_eqToHom {Y : Scheme.{u}} {V V' : Y.Opens} (h : V = V') (z : Y) (hz : z ∈ V)
    (t : Γ(Y, V')) :
    Y.evaluation V z hz (Y.presheaf.map (eqToHom h).op t) = Y.evaluation V' z (h ▸ hz) t := by
  subst h
  simp

theorem evaluation_app_eq_evaluation_appLE_eval {k : Type u} [Field k] (M : CurveModel k (RatFunc k))
    {Z : Scheme.{u}} (f : Z ⟶ M.C) (V : M.C.Opens) [Nonempty V] (g : Γ(M.C, V)) (c : k) (z : Z)
    (hz : z ∈ f ⁻¹ᵁ V) (hfz : f.base z = (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k c)).1) :
    Z.evaluation (f ⁻¹ᵁ V) z hz (f.app V g) =
      Z.evaluation (f ⁻¹ᵁ V) z hz ((f ≫ M.toBase).appLE ⊤ (f ⁻¹ᵁ V) le_top
        ((Scheme.ΓSpecIso (.of k)).inv
          (RatFunc.eval (RingHom.id k) c
            (((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc k).toRingHom.comp
              (algebraMap Γ(M.C, V) M.C.functionField)) g)))) := by
  set v : k := RatFunc.eval (RingHom.id k) c
      (((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc k).toRingHom.comp
        (algebraMap Γ(M.C, V) M.C.functionField)) g) with hv
  have key : ∀ (p : M.C) (hp : p ∈ V), p = (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k c)).1 →
      M.C.evaluation V p hp g =
        M.C.evaluation V p hp (M.toBase.appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of k)).inv v)) := by
    intro p hp hpP
    subst hpP
    exact M.evaluation_eq_evaluation_algebraMap_eval V c hp g
  have h1 := Scheme.evaluation_naturality_apply f z hz g
  have h2 := Scheme.evaluation_naturality_apply f z hz (M.toBase.appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of k)).inv v))
  rw [← h1, key (f.base z) hz hfz, h2]
  congr 1
  have hc := Scheme.Hom.appLE_comp_appLE f M.toBase ⊤ V (f ⁻¹ᵁ V) le_top le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hc
  rw [← CommRingCat.comp_apply, hc]

variable (k : Type u) [Field k]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of k))
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    {s : ℕ} (a b : Fin s → kˣ)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (U : X.Opens) [Nonempty (i₁ ⁻¹ᵁ U : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ U : M₂.C.Opens)]
    (g₁ : Γ(M₁.C, i₁ ⁻¹ᵁ U)) (g₂ : Γ(M₂.C, i₂ ⁻¹ᵁ U))

include hi₁ hi₂ hnode hinter htrans in

theorem app_pullback_eq_iff_eval_eq :
    (pullback i₁ i₂).presheaf.map
        (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
      ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁) =
      (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂ ↔
    ∀ i : Fin s, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∈ U →
      RatFunc.eval (RingHom.id k) (a i : k)
          (((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ U) M₁.C.functionField)) g₁) =
        RatFunc.eval (RingHom.id k) (b i : k)
          (((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ U) M₂.C.functionField)) g₂) := by

  have e : (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have hzb : pullback.fst i₁ i₂ ≫ M₁.toBase = pullback.snd i₁ i₂ ≫ M₂.toBase := by
    rw [← hi₁, ← hi₂, ← Category.assoc, pullback.condition, Category.assoc]

  let W₂ : (pullback i₁ i₂).Opens := (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U)
  let κ : ∀ (z : ↥(pullback i₁ i₂)) (_ : z ∈ W₂), k →+* ((pullback i₁ i₂).residueField z) := fun z hz =>
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.snd i₁ i₂ ≫ M₂.toBase).appLE ⊤ W₂ le_top ≫
      (pullback i₁ i₂).evaluation W₂ z hz).hom

  have hR : ∀ (z : ↥(pullback i₁ i₂)) (hz : z ∈ W₂) (i : Fin s), (pullback.snd i₁ i₂).base z = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1 →
      (pullback i₁ i₂).evaluation W₂ z hz ((pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂) =
        κ z hz (RatFunc.eval (RingHom.id k) (b i : k)
          (((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ U) M₂.C.functionField)) g₂)) := by
    intro z hz i hzi
    exact evaluation_app_eq_evaluation_appLE_eval M₂ (pullback.snd i₁ i₂) (i₂ ⁻¹ᵁ U) g₂ (b i : k) z hz hzi
  have hL : ∀ (z : ↥(pullback i₁ i₂)) (hz : z ∈ W₂) (i : Fin s), (pullback.fst i₁ i₂).base z = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 →
      (pullback i₁ i₂).evaluation W₂ z hz ((pullback i₁ i₂).presheaf.map (eqToHom e).op
          ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁)) =
        κ z hz (RatFunc.eval (RingHom.id k) (a i : k)
          (((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ U) M₁.C.functionField)) g₁)) := by
    intro z hz i hzi
    rw [evaluation_map_eqToHom e z hz,
      evaluation_app_eq_evaluation_appLE_eval M₁ (pullback.fst i₁ i₂) (i₁ ⁻¹ᵁ U) g₁ (a i : k) z (e ▸ hz) hzi,
      hzb]

    rw [← evaluation_map_eqToHom e z hz]
    change ((pullback.snd i₁ i₂ ≫ M₂.toBase).appLE ⊤ _ _ ≫ (pullback i₁ i₂).presheaf.map (eqToHom e).op ≫
      (pullback i₁ i₂).evaluation W₂ z hz) _ = _
    rw [Scheme.Hom.appLE_map'_assoc]
    rfl
  constructor
  ·
    intro h i hi
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback _ _ (hnode i)
    have hz : z ∈ W₂ := by
      show (pullback.snd i₁ i₂).base z ∈ i₂ ⁻¹ᵁ U
      rw [hz2]
      show i₂.base _ ∈ U
      rw [← hnode i]; exact hi
    have := congrArg ((pullback i₁ i₂).evaluation W₂ z hz) h
    rw [hL z hz i hz1, hR z hz i hz2] at this
    exact (κ z hz).injective this
  ·
    intro h
    haveI := htrans
    apply sub_eq_zero.mp
    apply (basicOpen_eq_bot_iff _).mp
    apply ((pullback i₁ i₂).basicOpen_eq_bot_iff_forall_evaluation_eq_zero _).mpr
    rintro ⟨z, hz⟩
    have hcond : i₁.base ((pullback.fst i₁ i₂).base z) = i₂.base ((pullback.snd i₁ i₂).base z) := by
      have := congrArg (fun φ => φ.base z) (pullback.condition (f := i₁) (g := i₂))
      simpa using this
    obtain ⟨i, hz1, hz2⟩ := hinter _ _ hcond
    have hi : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∈ U := by
      rw [← hz1, hcond]; exact hz
    rw [map_sub, hL z hz i hz1, hR z hz i hz2, h i hi, sub_self]

end AlgebraicGeometry.TwoGluedProjectiveLines

end eng15_NT

section eng17_lemmas
p2m_open "Polynomial AlgebraicGeometry.Polynomial"
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"
namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.evaluation_naturality_apply basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appLE_map'_assoc Spec Scheme Scheme.Hom.naturality IsClosedImmersion IsReduced Scheme.Hom.comp_app IsAffineOpen Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app evaluation_naturality_apply germToFunctionField Hom mk Hom.appLE_comp_appLE germToFunctionField_injective Γ Hom.appLE_map'_assoc basicOpen_eq_bot_iff_forall_evaluation_eq_zero functionField Hom.naturality residueField Hom.comp_app mk.injEq Opens residue Hom.app_eq_appLE Hom.comp_preimage Pullback.exists_preimage_pullback Hom.appLE ΓSpecIso evaluation Hom.appLE_eq_app TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom TwoAffineOpenCover.algebraMap_algebraOfHom" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "congr_app image appLE_comp_appLE app appLE_map'_assoc injective mk appTop naturality comp_app mk.injEq cover app_eq_appLE comp_preimage comp_apply appLE appLE_eq_app" end AlgebraicGeometry.Scheme.Hom
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem AlgebraicGeometry.Scheme.Hom.map_eqToHom_fst_app_app_eq_snd_app_app
    {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    (pullback i₁ i₂).presheaf.map
        (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
      ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) ((i₁.app U) f)) =
      (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) ((i₂.app U) f) := by
  have h := Scheme.Hom.congr_app (pullback.condition (f := i₁) (g := i₂)).symm U
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at h
  have h' := congrArg (fun φ => (ConcreteCategory.hom φ) f) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
  exact h'.symm

namespace RatFunc p2m_export "RatFunc" "isCoprime_num_denom algebraMap_X adicValuation_not_isEquiv_infty_valuation X eval_algebraMap X_ne_zero map algebraMap_C num denom eval num_div_denom C denom_ne_zero eval_C algebraMap_apply eval_mul denom_div_dvd denom_algebraMap" end RatFunc
p2m_open_scoped "RatFunc" in

theorem RatFunc.eval_ringHomId_eval₂_laurent (k : Type u) [Field k] (c : k) (hc : c ≠ 0)
    (p : LaurentPolynomial k) :
    RatFunc.eval (RingHom.id k) c
        (LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) p)
      = TwoChartCech.levalUnit k (Units.mk0 c hc) p := by
  set ι : LaurentPolynomial k →+* RatFunc k :=
    LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) with hι
  have hιC : ι.comp Polynomial.toLaurent = algebraMap k[X] (RatFunc k) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, Polynomial.toLaurent_C, hι, LaurentPolynomial.eval₂_C, RatFunc.algebraMap_C (K := k)]
      rfl
    · rw [RingHom.comp_apply, Polynomial.toLaurent_X, hι, LaurentPolynomial.eval₂_T, zpow_one, Units.val_mk0,
        RatFunc.algebraMap_X (K := k)]
  have hιL : ∀ q : k[X], ι (Polynomial.toLaurent q) = algebraMap k[X] (RatFunc k) q := fun q => by
    rw [← hιC, RingHom.comp_apply]
  have hιT : ∀ n : ℤ, ι (LaurentPolynomial.T n) = RatFunc.X ^ n := fun n => by
    rw [hι, LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

  obtain ⟨N, q, hq⟩ := LaurentPolynomial.exists_T_pow p

  have hXN : (algebraMap k[X] (RatFunc k) ((Polynomial.X : Polynomial k) ^ N) : RatFunc k) = RatFunc.X ^ N := by
    rw [map_pow, RatFunc.algebraMap_X]
  have hmul : ι p * algebraMap k[X] (RatFunc k) ((Polynomial.X : Polynomial k) ^ N) = algebraMap k[X] (RatFunc k) q := by
    rw [← hιL q, hq, map_mul, hιT, zpow_natCast, hXN]
  have hιp : ι p = algebraMap k[X] (RatFunc k) q / algebraMap k[X] (RatFunc k) ((Polynomial.X : Polynomial k) ^ N) := by
    rw [eq_div_iff (by rw [hXN]; exact pow_ne_zero N RatFunc.X_ne_zero), hmul]

  have hcN : Polynomial.eval₂ (RingHom.id k) c ((Polynomial.X : Polynomial k) ^ N) ≠ 0 := by
    rw [Polynomial.eval₂_X_pow]; exact pow_ne_zero N hc
  have hden : Polynomial.eval₂ (RingHom.id k) c (ι p).denom ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := (hιp ▸ RatFunc.denom_div_dvd q ((Polynomial.X : Polynomial k) ^ N) : (ι p).denom ∣ (Polynomial.X : Polynomial k) ^ N)
    apply hcN
    rw [hr, Polynomial.eval₂_mul, h0, zero_mul]

  have heval := congrArg (RatFunc.eval (RingHom.id k) c) hmul
  rw [RatFunc.eval_mul (RingHom.id k) c hden (by rw [RatFunc.denom_algebraMap, Polynomial.eval₂_one]; exact one_ne_zero),
    RatFunc.eval_algebraMap, RatFunc.eval_algebraMap, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply,
    Polynomial.eval₂_X_pow] at heval

  have hlev : TwoChartCech.levalUnit k (Units.mk0 c hc) p * c ^ N = Polynomial.eval₂ (RingHom.id k) c q := by
    have := congrArg (TwoChartCech.levalUnit k (Units.mk0 c hc)) hq
    rw [map_mul, LaurentPolynomial.eval₂_toLaurent, Units.val_mk0, LaurentPolynomial.eval₂_T, zpow_natCast,
      Units.val_pow_eq_pow_val, Units.val_mk0] at this
    exact this.symm
  have hcN' : (c ^ N : k) ≠ 0 := pow_ne_zero N hc

  have e1 : RatFunc.eval (RingHom.id k) c (ι p) = Polynomial.eval₂ (RingHom.id k) c q / c ^ N := by
    rw [eq_div_iff hcN']
    simpa using heval
  have e2 : TwoChartCech.levalUnit k (Units.mk0 c hc) p = Polynomial.eval₂ (RingHom.id k) c q / c ^ N := by
    rw [eq_div_iff hcN', hlev]
  rw [e1, e2]

end eng17_lemmas

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.evaluation_naturality_apply basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appLE_map'_assoc Spec Scheme Scheme.Hom.naturality IsClosedImmersion IsReduced Scheme.Hom.comp_app IsAffineOpen Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen"
namespace TwoGluedProjectiveLines
namespace S1a
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable {k : Type u} [Field k]

noncomputable def sec (M : CurveModel k (RatFunc k)) (W : M.C.Opens) [Nonempty W] :
    Γ(M.C, W) →+* RatFunc k :=
  (M.ffEquiv.symm : M.C.functionField ≃+* RatFunc k).toRingHom.comp (algebraMap Γ(M.C, W) M.C.functionField)

theorem sec_apply (M : CurveModel k (RatFunc k)) (W : M.C.Opens) [Nonempty W] (g : Γ(M.C, W)) :
    sec M W g = M.ffEquiv.symm (M.C.germToFunctionField W g) := rfl

theorem sec_injective (M : CurveModel k (RatFunc k)) (W : M.C.Opens) [Nonempty W] :
    Function.Injective (sec M W) :=
  M.ffEquiv.symm.injective.comp (M.C.germToFunctionField_injective W)

theorem sec_map (M : CurveModel k (RatFunc k)) {W W' : M.C.Opens} [Nonempty W] [Nonempty W'] (ι : W' ⟶ W)
    (g : Γ(M.C, W)) : sec M W' (M.C.presheaf.map ι.op g) = sec M W g := by
  rw [sec_apply, sec_apply]
  congr 1
  exact TopCat.Presheaf.germ_res_apply M.C.presheaf ι _ _ g

theorem sec_algebraMap (M : CurveModel k (RatFunc k)) (W : M.C.Opens) [Nonempty W] (r : k) :
    sec M W ((algebraOfHom M.toBase W).algebraMap r) = algebraMap k (RatFunc k) r := by
  rw [algebraMap_algebraOfHom, sec_apply]
  have h1 : M.C.germToFunctionField W ((M.toBase.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))
      = baseToFunctionField M.toBase r := by
    change ((M.toBase.appLE ⊤ W le_top) ≫ M.C.germToFunctionField W).hom _ = _
    rw [Scheme.Hom.appLE, Category.assoc]
    erw [TopCat.Presheaf.germ_res M.C.presheaf (homOfLE (le_top : W ≤ ⊤))]
    rfl
  rw [h1]
  apply M.ffEquiv.injective
  rw [RingEquiv.apply_symm_apply, ← M.ffEquiv_algebraMap]

end AlgebraicGeometry.TwoGluedProjectiveLines.S1a

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.evaluation_naturality_apply basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appLE_map'_assoc Spec Scheme Scheme.Hom.naturality IsClosedImmersion IsReduced Scheme.Hom.comp_app IsAffineOpen Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen"
namespace TwoGluedProjectiveLines
namespace S1a
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable {k : Type u} [Field k]

theorem app_algebraMap {X C : Scheme.{u}} (x : X ⟶ Spec (.of k)) (c : C ⟶ Spec (.of k)) (i : C ⟶ X)
    (hi : i ≫ x = c) (U : X.Opens) (r : k) :
    (i.app U).hom ((algebraOfHom x U).algebraMap r) = (algebraOfHom c (i ⁻¹ᵁ U)).algebraMap r := by
  rw [algebraMap_algebraOfHom, algebraMap_algebraOfHom]
  subst hi
  change (x.appLE ⊤ U le_top ≫ i.app U).hom _ = ((i ≫ x).appLE ⊤ (i ⁻¹ᵁ U) le_top).hom _
  rw [Scheme.Hom.app_eq_appLE i, Scheme.Hom.appLE_comp_appLE]

noncomputable def appAlgHom {X C : Scheme.{u}} (x : X ⟶ Spec (.of k)) (c : C ⟶ Spec (.of k)) (i : C ⟶ X)
    (hi : i ≫ x = c) (U : X.Opens) :
    letI := algebraOfHom x U; letI := algebraOfHom c (i ⁻¹ᵁ U)
    Γ(X, U) →ₐ[k] Γ(C, i ⁻¹ᵁ U) :=
  letI := algebraOfHom x U; letI := algebraOfHom c (i ⁻¹ᵁ U)
  { (i.app U).hom with commutes' := app_algebraMap x c i hi U }

noncomputable def secAlgHom (M : CurveModel k (RatFunc k)) (W : M.C.Opens) [Nonempty W] :
    letI := algebraOfHom M.toBase W
    Γ(M.C, W) →ₐ[k] RatFunc k :=
  letI := algebraOfHom M.toBase W
  { sec M W with commutes' := sec_algebraMap M W }

section J

variable {X : Scheme.{u}} (x : X ⟶ Spec (.of k))
  (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
  (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)

noncomputable def J (U : X.Opens) [Nonempty (i₁ ⁻¹ᵁ U : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ U : M₂.C.Opens)] :
    letI := algebraOfHom x U
    Γ(X, U) →ₐ[k] RatFunc k × RatFunc k :=
  letI := algebraOfHom x U
  letI := algebraOfHom M₁.toBase (i₁ ⁻¹ᵁ U); letI := algebraOfHom M₂.toBase (i₂ ⁻¹ᵁ U)
  ((secAlgHom M₁ (i₁ ⁻¹ᵁ U)).comp (appAlgHom x M₁.toBase i₁ hi₁ U)).prod
    ((secAlgHom M₂ (i₂ ⁻¹ᵁ U)).comp (appAlgHom x M₂.toBase i₂ hi₂ U))

variable {x M₁ M₂ i₁ i₂}

theorem J_apply (U : X.Opens) [Nonempty (i₁ ⁻¹ᵁ U : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ U : M₂.C.Opens)]
    (f : Γ(X, U)) :
    letI := algebraOfHom x U
    J x M₁ M₂ i₁ i₂ hi₁ hi₂ U f = (sec M₁ (i₁ ⁻¹ᵁ U) ((i₁.app U).hom f), sec M₂ (i₂ ⁻¹ᵁ U) ((i₂.app U).hom f)) :=
  rfl

theorem J_injective [IsReduced X] [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (U : X.Opens) (hUa : IsAffineOpen U) [Nonempty (i₁ ⁻¹ᵁ U : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ U : M₂.C.Opens)] :
    letI := algebraOfHom x U
    Function.Injective (J x M₁ M₂ i₁ i₂ hi₁ hi₂ U) := by
  intro f g h
  have h' := Prod.ext_iff.mp h
  apply (AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
    i₁ i₂ hcover U hUa).1
  exact Prod.ext (sec_injective _ _ h'.1) (sec_injective _ _ h'.2)

theorem J_map {U V : X.Opens} (h : V ≤ U)
    [Nonempty (i₁ ⁻¹ᵁ U : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ U : M₂.C.Opens)]
    [Nonempty (i₁ ⁻¹ᵁ V : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ V : M₂.C.Opens)] (f : Γ(X, U)) :
    letI := algebraOfHom x U; letI := algebraOfHom x V
    J x M₁ M₂ i₁ i₂ hi₁ hi₂ V (X.presheaf.map (homOfLE h).op f) = J x M₁ M₂ i₁ i₂ hi₁ hi₂ U f := by
  rw [J_apply, J_apply]
  have n₁ : (i₁.app V).hom (X.presheaf.map (homOfLE h).op f)
      = M₁.C.presheaf.map ((TopologicalSpace.Opens.map i₁.base).map (homOfLE h)).op ((i₁.app U).hom f) := by
    change (X.presheaf.map (homOfLE h).op ≫ i₁.app V).hom f = _
    rw [Scheme.Hom.naturality]; rfl
  have n₂ : (i₂.app V).hom (X.presheaf.map (homOfLE h).op f)
      = M₂.C.presheaf.map ((TopologicalSpace.Opens.map i₂.base).map (homOfLE h)).op ((i₂.app U).hom f) := by
    change (X.presheaf.map (homOfLE h).op ≫ i₂.app V).hom f = _
    rw [Scheme.Hom.naturality]; rfl
  rw [n₁, n₂, sec_map, sec_map]

end J

end AlgebraicGeometry.TwoGluedProjectiveLines.S1a

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.evaluation_naturality_apply basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appLE_map'_assoc Spec Scheme Scheme.Hom.naturality IsClosedImmersion IsReduced Scheme.Hom.comp_app IsAffineOpen Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen"
namespace TwoGluedProjectiveLines
namespace S1a
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable (k : Type u) [Field k]

noncomputable def ιₐ : LaurentPolynomial k →ₐ[k] RatFunc k :=
  { LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) with
    commutes' := fun r => by
      change LaurentPolynomial.eval₂ _ _ (algebraMap k (LaurentPolynomial k) r) = _
      rw [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.eval₂_C]; rfl }

theorem ιₐ_apply (p : LaurentPolynomial k) :
    ιₐ k p = LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) p :=
  rfl

noncomputable def ιι : (LaurentPolynomial k × LaurentPolynomial k) →ₐ[k] (RatFunc k × RatFunc k) :=
  ((ιₐ k).comp (AlgHom.fst k _ _)).prod ((ιₐ k).comp (AlgHom.snd k _ _))

theorem ιι_apply (f : LaurentPolynomial k × LaurentPolynomial k) : ιι k f = (ιₐ k f.1, ιₐ k f.2) := rfl

theorem ιι_injective (hι : Function.Injective (ιₐ k)) : Function.Injective (ιι k) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  simp only [ιι_apply, Prod.mk.injEq] at h
  exact Prod.ext (hι h.1) (hι h.2)

variable {k}

theorem exists_algEquiv_of_range_eq {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] (J : A →ₐ[k] C) (I : B →ₐ[k] C)
    (hJ : Function.Injective J) (hI : Function.Injective I) (h : Set.range J = Set.range I) :
    ∃ e : A ≃ₐ[k] B, ∀ x, I (e x) = J x := by
  have hr : J.range = I.range := by
    ext c
    rw [AlgHom.mem_range, AlgHom.mem_range, ← Set.mem_range, ← Set.mem_range, h]
  refine ⟨(AlgEquiv.ofInjective J hJ).trans ((Subalgebra.equivOfEq _ _ hr).trans (AlgEquiv.ofInjective I hI).symm),
    fun x => ?_⟩
  set z := (Subalgebra.equivOfEq _ _ hr) (AlgEquiv.ofInjective J hJ x) with hz
  have h1 : (z : C) = J x := rfl
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, ← hz, ← h1, ← AlgEquiv.ofInjective_apply I hI,
    AlgEquiv.apply_symm_apply]

section places
variable (k)
variable (M : CurveModel k (RatFunc k)) in

noncomputable abbrev pt (v : Place k (RatFunc k)) : M.C := (M.placeEquiv.symm v).1

variable (M : CurveModel k (RatFunc k)) in
theorem pt_injective : Function.Injective (pt k M) :=
  Subtype.val_injective.comp M.placeEquiv.symm.injective

variable [DecidableEq (RatFunc k)]

theorem ofHeightOneSpectrum_ne_placeInfty (w : IsDedekindDomain.HeightOneSpectrum (Polynomial k)) :
    Place.ofHeightOneSpectrum (K := k) (F := RatFunc k) w ≠ RationalFunctionField.placeInfty k := by
  intro h
  apply RatFunc.adicValuation_not_isEquiv_infty_valuation w
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← Place.ofHeightOneSpectrum_toValuationSubring (K := k) (F := RatFunc k), h,
    RationalFunctionField.placeInfty_toValuationSubring]

theorem placeOfPoint_ne_placeInfty' (c : k) :
    RationalFunctionField.placeOfPoint k c ≠ RationalFunctionField.placeInfty k := by
  rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum]
  exact ofHeightOneSpectrum_ne_placeInfty k _

variable (M : CurveModel k (RatFunc k))

theorem pt_placeOfPoint_mem_of_coe_eq_compl_infty {W : M.C.Opens}
    (hW : ((W : Set M.C)) = {pt k M (RationalFunctionField.placeInfty k)}ᶜ) (c : k) :
    pt k M (RationalFunctionField.placeOfPoint k c) ∈ W := by
  change pt k M _ ∈ (W : Set M.C)
  rw [hW, Set.mem_compl_singleton_iff]
  exact fun h => placeOfPoint_ne_placeInfty' k c (pt_injective k M h)

omit [DecidableEq (RatFunc k)] in
theorem pt_placeOfPoint_mem_of_coe_eq_compl_zero {W : M.C.Opens}
    (hW : ((W : Set M.C)) = {pt k M (RationalFunctionField.placeOfPoint k 0)}ᶜ) {c : k} (hc : c ≠ 0) :
    pt k M (RationalFunctionField.placeOfPoint k c) ∈ W := by
  change pt k M _ ∈ (W : Set M.C)
  rw [hW, Set.mem_compl_singleton_iff]
  exact fun h => hc (RationalFunctionField.placeOfPoint_injective k (pt_injective k M h))

theorem pt_placeInfty_mem_of_coe_eq_compl_zero {W : M.C.Opens}
    (hW : ((W : Set M.C)) = {pt k M (RationalFunctionField.placeOfPoint k 0)}ᶜ) :
    pt k M (RationalFunctionField.placeInfty k) ∈ W := by
  change pt k M _ ∈ (W : Set M.C)
  rw [hW, Set.mem_compl_singleton_iff]
  exact fun h => placeOfPoint_ne_placeInfty' k 0 (pt_injective k M h).symm

end places

end AlgebraicGeometry.TwoGluedProjectiveLines.S1a

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.evaluation_naturality_apply basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appLE_map'_assoc Spec Scheme Scheme.Hom.naturality IsClosedImmersion IsReduced Scheme.Hom.comp_app IsAffineOpen Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen"
namespace TwoGluedProjectiveLines
namespace S1a
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

section range

variable {k : Type u} [Field k]
  {X : Scheme.{u}} {x : X ⟶ Spec (.of k)} [IsReduced X]
  {M₁ M₂ : CurveModel k (RatFunc k)} {i₁ : M₁.C ⟶ X} {i₂ : M₂.C ⟶ X}
  [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
  {s : ℕ} {a b : Fin s → kˣ}
  (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
    i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
  (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
    ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
      q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
  (htrans : IsReduced (pullback i₁ i₂))

include hcover hnode hinter htrans in

theorem range_J_eq (U : X.Opens) (hUa : IsAffineOpen U)
    [Nonempty (i₁ ⁻¹ᵁ U : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ U : M₂.C.Opens)]
    (hU : ∀ i, i₁.base (pt k M₁ (RationalFunctionField.placeOfPoint k (a i : k))) ∈ U)
    (S₁ S₂ : Subring (LaurentPolynomial k))
    (h₁ : ((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
          (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ U) M₁.C.functionField)).range =
        S₁.map (LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)))
    (h₂ : ((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
          (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ U) M₂.C.functionField)).range =
        S₂.map (LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero))) :
    letI := algebraOfHom x U
    Set.range (J x M₁ M₂ i₁ i₂ hi₁ hi₂ U) =
      ιι k '' {f | f ∈ TwoChartCech.gluedLinesOverlap k a b ∧ f.1 ∈ S₁ ∧ f.2 ∈ S₂} := by
  letI := algebraOfHom x U
  have GEN := AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
    i₁ i₂ hcover U hUa
  have NT := AlgebraicGeometry.TwoGluedProjectiveLines.app_pullback_eq_iff_eval_eq k x M₁ M₂ i₁ i₂ hi₁ hi₂ a b
    hnode hinter htrans U

  have r₁ : ∀ y, (∃ g, sec M₁ (i₁ ⁻¹ᵁ U) g = y) ↔ ∃ p ∈ S₁, ιₐ k p = y := fun y => by
    have e := SetLike.ext_iff.mp h₁ y
    rw [RingHom.mem_range, Subring.mem_map] at e
    exact e
  have r₂ : ∀ y, (∃ g, sec M₂ (i₂ ⁻¹ᵁ U) g = y) ↔ ∃ p ∈ S₂, ιₐ k p = y := fun y => by
    have e := SetLike.ext_iff.mp h₂ y
    rw [RingHom.mem_range, Subring.mem_map] at e
    exact e
  have LB : ∀ (u : kˣ) (p : LaurentPolynomial k), RatFunc.eval (RingHom.id k) (u : k) (ιₐ k p) =
      TwoChartCech.levalUnit k u p := fun u p => by
    rw [ιₐ_apply, RatFunc.eval_ringHomId_eval₂_laurent k (u : k) u.ne_zero, Units.mk0_val]
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨p₁, hp₁, e₁⟩ := (r₁ _).mp ⟨(i₁.app U).hom f, rfl⟩
    obtain ⟨p₂, hp₂, e₂⟩ := (r₂ _).mp ⟨(i₂.app U).hom f, rfl⟩
    refine ⟨(p₁, p₂), ⟨fun i => ?_, hp₁, hp₂⟩, ?_⟩
    · have hc := AlgebraicGeometry.Scheme.Hom.map_eqToHom_fst_app_app_eq_snd_app_app i₁ i₂ U f
      have hv := (NT ((i₁.app U).hom f) ((i₂.app U).hom f)).mp hc i (hU i)
      change RatFunc.eval _ _ (sec M₁ _ _) = RatFunc.eval _ _ (sec M₂ _ _) at hv
      rw [← e₁, ← e₂, LB, LB] at hv
      exact hv
    · rw [J_apply, ιι_apply, e₁, e₂]
  · rintro ⟨⟨p₁, p₂⟩, ⟨hpq, hp₁, hp₂⟩, rfl⟩
    obtain ⟨g₁, e₁⟩ := (r₁ _).mpr ⟨p₁, hp₁, rfl⟩
    obtain ⟨g₂, e₂⟩ := (r₂ _).mpr ⟨p₂, hp₂, rfl⟩
    have hc := (NT g₁ g₂).mpr (fun i _ => by
      change RatFunc.eval _ _ (sec M₁ _ g₁) = RatFunc.eval _ _ (sec M₂ _ g₂)
      rw [e₁, e₂, LB, LB]
      exact hpq i)
    obtain ⟨f, hf₁, hf₂⟩ := GEN.2 g₁ g₂ hc
    refine ⟨f, ?_⟩
    have hf₁' : (i₁.app U).hom f = g₁ := hf₁
    have hf₂' : (i₂.app U).hom f = g₂ := hf₂
    rw [J_apply, ιι_apply, hf₁', hf₂', e₁, e₂]

end range

end AlgebraicGeometry.TwoGluedProjectiveLines.S1a

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.evaluation_naturality_apply basicOpen_eq_bot_iff Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appLE_map'_assoc Spec Scheme Scheme.Hom.naturality IsClosedImmersion IsReduced Scheme.Hom.comp_app IsAffineOpen Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen"
namespace TwoGluedProjectiveLines
namespace S1a
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

section model_sets
variable (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ)

theorem coe_overlap_inf_prod (S : Subalgebra k (LaurentPolynomial k)) :
    ((TwoChartCech.gluedLinesOverlap k a b ⊓ S.prod S : Subalgebra k _) :
        Set (LaurentPolynomial k × LaurentPolynomial k)) =
      {f | f ∈ TwoChartCech.gluedLinesOverlap k a b ∧ f.1 ∈ S.toSubring ∧ f.2 ∈ S.toSubring} := by
  ext f
  simp only [SetLike.mem_coe, Algebra.mem_inf, Subalgebra.mem_prod, Set.mem_setOf_eq, Subalgebra.mem_toSubring]

theorem coe_overlap_eq :
    ((TwoChartCech.gluedLinesOverlap k a b : Subalgebra k _) : Set (LaurentPolynomial k × LaurentPolynomial k)) =
      {f | f ∈ TwoChartCech.gluedLinesOverlap k a b ∧ f.1 ∈ (⊤ : Subring (LaurentPolynomial k)) ∧
        f.2 ∈ (⊤ : Subring (LaurentPolynomial k))} := by
  ext f
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, Subring.mem_top, and_true]

theorem range_ιι_comp_val (T : Subalgebra k (LaurentPolynomial k × LaurentPolynomial k)) :
    Set.range ((ιι k).comp T.val) = ιι k '' (T : Set (LaurentPolynomial k × LaurentPolynomial k)) := by
  ext y
  simp only [Set.mem_range, Set.mem_image, AlgHom.coe_comp, Function.comp_apply, Subalgebra.coe_val, SetLike.mem_coe]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
  · rintro ⟨f, hf, rfl⟩; exact ⟨⟨f, hf⟩, rfl⟩

end model_sets

end AlgebraicGeometry.TwoGluedProjectiveLines.S1a

open AlgebraicGeometry.TwoGluedProjectiveLines.S1a AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem solution
    (k : Type u) [Field k] [DecidableEq (RatFunc k)]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of k)) [IsReduced X]
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (𝒲₀ : X.TwoAffineOpenCover)
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
 :
    ∃ (φ₀ : (𝒲₀.cover x).A0 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A0)
      (φ₁ : (𝒲₀.cover x).A1 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A1)
      (φ₀₁ : (𝒲₀.cover x).A01 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A01),
      (∀ f, φ₀₁ ((𝒲₀.cover x).ρ0 f) = (TwoChartCech.gluedLinesCover k a b).ρ0 (φ₀ f)) ∧
      (∀ f, φ₀₁ ((𝒲₀.cover x).ρ1 f) = (TwoChartCech.gluedLinesCover k a b).ρ1 (φ₁ f)) := by
  letI := algebraOfHom x 𝒲₀.U0; letI := algebraOfHom x 𝒲₀.U1; letI := algebraOfHom x (𝒲₀.U0 ⊓ 𝒲₀.U1)

  have m0₁ : ∀ c : k, pt k M₁ (RationalFunctionField.placeOfPoint k c) ∈ i₁ ⁻¹ᵁ 𝒲₀.U0 :=
    pt_placeOfPoint_mem_of_coe_eq_compl_infty k M₁ hU0₁
  have m0₂ : ∀ c : k, pt k M₂ (RationalFunctionField.placeOfPoint k c) ∈ i₂ ⁻¹ᵁ 𝒲₀.U0 :=
    pt_placeOfPoint_mem_of_coe_eq_compl_infty k M₂ hU0₂
  have m1₁ : ∀ {c : k}, c ≠ 0 → pt k M₁ (RationalFunctionField.placeOfPoint k c) ∈ i₁ ⁻¹ᵁ 𝒲₀.U1 :=
    fun hc => pt_placeOfPoint_mem_of_coe_eq_compl_zero k M₁ hU1₁ hc
  have m1₂ : ∀ {c : k}, c ≠ 0 → pt k M₂ (RationalFunctionField.placeOfPoint k c) ∈ i₂ ⁻¹ᵁ 𝒲₀.U1 :=
    fun hc => pt_placeOfPoint_mem_of_coe_eq_compl_zero k M₂ hU1₂ hc

  haveI n0₁ : Nonempty (i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) := ⟨⟨_, m0₁ 0⟩⟩
  haveI n0₂ : Nonempty (i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) := ⟨⟨_, m0₂ 0⟩⟩
  haveI n1₁ : Nonempty (i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) := ⟨⟨_, m1₁ one_ne_zero⟩⟩
  haveI n1₂ : Nonempty (i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) := ⟨⟨_, m1₂ one_ne_zero⟩⟩
  haveI n01₁ : Nonempty (i₁ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1) : M₁.C.Opens) := ⟨⟨_, m0₁ 1, m1₁ one_ne_zero⟩⟩
  haveI n01₂ : Nonempty (i₂ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1) : M₂.C.Opens) := ⟨⟨_, m0₂ 1, m1₂ one_ne_zero⟩⟩
  haveI n01₁' : Nonempty (i₁ ⁻¹ᵁ 𝒲₀.U0 ⊓ i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) := n01₁
  haveI n01₂' : Nonempty (i₂ ⁻¹ᵁ 𝒲₀.U0 ⊓ i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) := n01₂

  obtain ⟨hι, hr0₁, hr1₁, hr01₁⟩ :=
    AlgebraicCurve.CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl k M₁
      (i₁ ⁻¹ᵁ 𝒲₀.U0) (i₁ ⁻¹ᵁ 𝒲₀.U1) (𝒲₀.isAffineOpen_U0.preimage i₁) (𝒲₀.isAffineOpen_U1.preimage i₁)
      (𝒲₀.isAffineOpen_inf.preimage i₁) hU0₁ hU1₁
  obtain ⟨-, hr0₂, hr1₂, hr01₂⟩ :=
    AlgebraicCurve.CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl k M₂
      (i₂ ⁻¹ᵁ 𝒲₀.U0) (i₂ ⁻¹ᵁ 𝒲₀.U1) (𝒲₀.isAffineOpen_U0.preimage i₂) (𝒲₀.isAffineOpen_U1.preimage i₂)
      (𝒲₀.isAffineOpen_inf.preimage i₂) hU0₂ hU1₂
  have hι' : Function.Injective (ιₐ k) := fun p q h => hι h

  have R0 := range_J_eq hi₁ hi₂ hcover hnode hinter htrans 𝒲₀.U0 𝒲₀.isAffineOpen_U0 (fun i => m0₁ (a i : k))
    (TwoChartCech.polyPart k).toSubring (TwoChartCech.polyPart k).toSubring hr0₁ hr0₂
  have R1 := range_J_eq hi₁ hi₂ hcover hnode hinter htrans 𝒲₀.U1 𝒲₀.isAffineOpen_U1 (fun i => m1₁ (a i).ne_zero)
    (TwoChartCech.invPolyPart k).toSubring (TwoChartCech.invPolyPart k).toSubring hr1₁ hr1₂
  have R01 := range_J_eq hi₁ hi₂ hcover hnode hinter htrans (𝒲₀.U0 ⊓ 𝒲₀.U1) 𝒲₀.isAffineOpen_inf
    (fun i => ⟨m0₁ (a i : k), m1₁ (a i).ne_zero⟩) ⊤ ⊤
    (hr01₁.trans (RingHom.range_eq_map _)) (hr01₂.trans (RingHom.range_eq_map _))
  rw [← coe_overlap_inf_prod, ← range_ιι_comp_val] at R0 R1
  rw [← coe_overlap_eq, ← range_ιι_comp_val] at R01

  have inj : ∀ T : Subalgebra k (LaurentPolynomial k × LaurentPolynomial k), Function.Injective ((ιι k).comp T.val) :=
    fun T => (ιι_injective k hι').comp Subtype.val_injective
  obtain ⟨e₀, he₀⟩ := exists_algEquiv_of_range_eq _ _ (J_injective hi₁ hi₂ hcover 𝒲₀.U0 𝒲₀.isAffineOpen_U0) (inj _) R0
  obtain ⟨e₁, he₁⟩ := exists_algEquiv_of_range_eq _ _ (J_injective hi₁ hi₂ hcover 𝒲₀.U1 𝒲₀.isAffineOpen_U1) (inj _) R1
  obtain ⟨e₀₁, he₀₁⟩ := exists_algEquiv_of_range_eq _ _ (J_injective hi₁ hi₂ hcover (𝒲₀.U0 ⊓ 𝒲₀.U1) 𝒲₀.isAffineOpen_inf) (inj _) R01
  refine ⟨e₀, e₁, e₀₁, fun f => ?_, fun f => ?_⟩
  · apply inj
    change ((ιι k).comp (TwoChartCech.gluedLinesOverlap k a b).val)
        (e₀₁ (X.presheaf.map (homOfLE (inf_le_left : 𝒲₀.U0 ⊓ 𝒲₀.U1 ≤ 𝒲₀.U0)).op f)) =
      ιι k ((e₀ f : ↥(TwoChartCech.gluedLinesOverlap k a b ⊓ (TwoChartCech.polyPart k).prod (TwoChartCech.polyPart k))) :
        LaurentPolynomial k × LaurentPolynomial k)
    rw [he₀₁, J_map, ← he₀ f]
    rfl
  · apply inj
    change ((ιι k).comp (TwoChartCech.gluedLinesOverlap k a b).val)
        (e₀₁ (X.presheaf.map (homOfLE (inf_le_right : 𝒲₀.U0 ⊓ 𝒲₀.U1 ≤ 𝒲₀.U1)).op f)) =
      ιι k ((e₁ f : ↥(TwoChartCech.gluedLinesOverlap k a b ⊓ (TwoChartCech.invPolyPart k).prod (TwoChartCech.invPolyPart k))) :
        LaurentPolynomial k × LaurentPolynomial k)
    rw [he₀₁, J_map, ← he₁ f]
    rfl

end S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover (solution)
