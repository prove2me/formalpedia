-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/93eb7d65-39e8-50e0-8991-0055f9ec849d

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

namespace P0InfAux

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem pt_eq (z : ↥(XMid R F j)) :
    (ιFin R F j).base ((fFin R F j).base z) = (ιInf R F j).base ((fInf R F j).base z) := by
  have := congrArg (fun f => f.base z) (glue_condition R F j)
  simpa using this

theorem stalkMap_germ_secFin (w : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)) :
    (ιFin R F j).stalkMap w
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base w) ⟨w, trivial, rfl⟩).hom
        (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b))) =
    (StructureSheaf.toStalk ↥(chartAlgFin R F j) w).hom b := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply,
    Scheme.ΓSpecIso_inv]
  exact (RingHom.congr_arg _ rfl).symm

theorem stalkMap_germ_secInf (w : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)) :
    (ιInf R F j).stalkMap w
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base w) ⟨w, trivial, rfl⟩).hom
        (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))) =
    (StructureSheaf.toStalk ↥(chartAlgInf R F j) w).hom b := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply,
    Scheme.ΓSpecIso_inv]
  exact (RingHom.congr_arg _ rfl).symm

theorem pull_fin (z : ↥(XMid R F j)) (b : ↥(chartAlgFin R F j)) :
    (fFin R F j).stalkMap z ((ιFin R F j).stalkMap ((fFin R F j).base z)
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤)
          ((ιFin R F j).base ((fFin R F j).base z)) ⟨(fFin R F j).base z, trivial, rfl⟩).hom
        (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b)))) =
    (StructureSheaf.toStalk ↥(chartAlgMid R F j) z).hom (inclFin R F j b) := by
  rw [stalkMap_germ_secFin]
  exact stalkMap_toStalk_apply (CommRingCat.ofHom (inclFin R F j).toRingHom) z b

set_option maxHeartbeats 6400000 in

theorem pull_inf (z : ↥(XMid R F j)) (b : ↥(chartAlgInf R F j)) :
    (fFin R F j).stalkMap z ((ιFin R F j).stalkMap ((fFin R F j).base z)
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤)
          ((ιFin R F j).base ((fFin R F j).base z)) ⟨(fInf R F j).base z, trivial, (pt_eq R F j z).symm⟩).hom
        (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b)))) =
    (StructureSheaf.toStalk ↥(chartAlgMid R F j) z).hom (inclInf R F j b) := by
  have key : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤)
        ((ιFin R F j).base ((fFin R F j).base z)) ⟨(fInf R F j).base z, trivial, (pt_eq R F j z).symm⟩ ≫
        (ιFin R F j).stalkMap ((fFin R F j).base z) ≫ (fFin R F j).stalkMap z =
      (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤)
        ((ιInf R F j).base ((fInf R F j).base z)) ⟨(fInf R F j).base z, trivial, rfl⟩ ≫
        (ιInf R F j).stalkMap ((fInf R F j).base z) ≫ (fInf R F j).stalkMap z := by
    rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom _ _ (glue_condition R F j) z]
    simp only [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rfl
  have key' := congrArg (fun φ => φ.hom (((ιInf R F j).appIso ⊤).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))) key
  simp only [CommRingCat.comp_apply] at key'
  rw [key', stalkMap_germ_secInf]
  exact stalkMap_toStalk_apply (CommRingCat.ofHom (inclInf R F j).toRingHom) z b

end P0InfAux

open P0InfAux in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    (φ : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField)
    (hφFin : ∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b)))) :
    ∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))) := by
  classical
  intro y b'

  let z : ↥(XMid R F j) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ↥(chartAlgMid R F j))
  let w : ↥(XFin R F j) := (fFin R F j).base z
  have hI : (ιFin R F j).base w ∈ (ιInf R F j) ''ᵁ ⊤ := ⟨(fInf R F j).base z, trivial, (pt_eq R F j z).symm⟩

  let secF : ↥(chartAlgFin R F j) → ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.obj (Opposite.op ((ιFin R F j) ''ᵁ ⊤))) := fun b =>
    ((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b)
  let secI : ↥(chartAlgInf R F j) → ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.obj (Opposite.op ((ιInf R F j) ''ᵁ ⊤))) := fun b =>
    ((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b)
  let GF : ↥(chartAlgFin R F j) → ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base w)) := fun b =>
    ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base w) ⟨w, trivial, rfl⟩).hom (secF b)
  let GI : ↥(chartAlgInf R F j) → ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base w)) := fun b =>
    ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιFin R F j).base w) hI).hom (secI b)
  have hGFmul : ∀ b c, GF (b * c) = GF b * GF c := fun b c => by simp only [GF, secF, map_mul]
  have hGFpow : ∀ b (n : ℕ), GF (b ^ n) = GF b ^ n := fun b n => by simp only [GF, secF, map_pow]

  let T : ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base w)) → ↑((XMid R F j).presheaf.stalk z) := fun s =>
    (fFin R F j).stalkMap z ((ιFin R F j).stalkMap w s)
  have hTinj : Function.Injective T :=
    (ConcreteCategory.bijective_of_isIso ((fFin R F j).stalkMap z)).1.comp
      (ConcreteCategory.bijective_of_isIso ((ιFin R F j).stalkMap w)).1
  have hTmul : ∀ s t, T (s * t) = T s * T t := fun s t => by simp only [T, map_mul]
  have hTF : ∀ b, T (GF b) = (StructureSheaf.toStalk ↥(chartAlgMid R F j) z).hom (inclFin R F j b) :=
    fun b => pull_fin R F j z b
  have hTI : ∀ b, T (GI b) = (StructureSheaf.toStalk ↥(chartAlgMid R F j) z).hom (inclInf R F j b) :=
    fun b => pull_inf R F j z b

  have hb'mid : (b' : F) ∈ chartAlg R F (insert j⁻¹ ({j} : Set F)) := by
    have : (insert j⁻¹ ({j} : Set F)) = {j, j⁻¹} := Set.pair_comm _ _
    rw [this]; exact (inclInf R F j b').2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (R := R) (Set.mem_singleton j) (j_ne_zero j) hb'mid
  have hR1 : GI b' * GF (jChartFin R F j) ^ n = GF ⟨j ^ n * (b' : F), hn⟩ := by
    apply hTinj
    rw [hTmul, ← hGFpow, hTF, hTF, hTI]
    have e : inclInf R F j b' * inclFin R F j (jChartFin R F j ^ n) = inclFin R F j ⟨j ^ n * (b' : F), hn⟩ := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, map_pow, Subalgebra.coe_pow, coe_chartIncl, coe_jChartFin]
      ring
    rw [← e, map_mul]
    rfl

  have hR2 : GI (jInvChartInf R F j) * GF (jChartFin R F j) = 1 := by
    apply hTinj
    rw [hTmul, hTF, hTI, show T 1 = 1 from by simp only [T, map_one]]
    have e : inclInf R F j (jInvChartInf R F j) * inclFin R F j (jChartFin R F j) = 1 :=
      Subtype.ext (by rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_jInvChartInf, coe_jChartFin,
        Subalgebra.coe_one, inv_mul_cancel₀ (j_ne_zero j)])
    have := congrArg (StructureSheaf.toStalk ↥(chartAlgMid R F j) z).hom e
    rw [map_mul, map_one] at this
    exact this

  let A := algebraMap ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base w)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
  have hφF : ∀ b : ↥(chartAlgFin R F j), φ (b : F) = A (GF b) := fun b => hφFin w b

  have hξ : genericPoint (AlgebraicCurve.TwoChartIntegralModel R F j) ∈ (ιInf R F j) ''ᵁ ⊤ :=
    ((genericPoint_spec (AlgebraicCurve.TwoChartIntegralModel R F j)).mem_open_set_iff ((ιInf R F j) ''ᵁ ⊤).isOpen).mpr ⟨_, Set.mem_univ _, hI⟩
  have hgen : ∀ (x : ↑(AlgebraicCurve.TwoChartIntegralModel R F j)) (hx : x ∈ (ιInf R F j) ''ᵁ ⊤) (s),
      algebraMap ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) x hx).hom s) =
        ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) (genericPoint (AlgebraicCurve.TwoChartIntegralModel R F j)) hξ).hom s := by
    intro x hx s
    show ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) x hx ≫ (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalkSpecializes _).hom s = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]

  have hj : φ j ≠ 0 := by
    intro h0; exact j_ne_zero j (φ.injective (by rw [h0, map_zero]))
  have h1 : φ (b' : F) * φ j ^ n = A (GI b') * φ j ^ n := by
    rw [← map_pow, ← map_mul, show φ (↑b' * j ^ n) = φ (((⟨j ^ n * (b' : F), hn⟩ : ↥(chartAlgFin R F j)) : F)) from by
      simp only [mul_comm], hφF, ← hR1, map_mul, map_pow]
    congr 1
    rw [← hφF, ← map_pow]
    rfl
  have main : φ (b' : F) = A (GI b') := mul_right_cancel₀ (pow_ne_zero n hj) h1
  rw [main]
  exact (hgen _ hI (secI b')).trans (hgen ((ιInf R F j).base y) ⟨y, trivial, rfl⟩ (secI b')).symm

end S_AlgebraicCurve_TwoChartIntegralModel_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin (solution)
