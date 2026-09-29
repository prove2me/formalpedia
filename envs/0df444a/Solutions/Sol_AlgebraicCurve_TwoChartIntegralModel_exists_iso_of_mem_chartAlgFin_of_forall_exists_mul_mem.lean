-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b9cd83f8-6326-5db7-8fa0-1ec83dcd87f9

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_of_mem_chartAlgFin_of_forall_pow_mul_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace UB

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j j' : F) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]

omit [Fact (j ≠ 0)] [Fact (j' ≠ 0)] in

theorem exists_uniform [Algebra.FiniteType R (chartAlgInf R F j')]
    (hvis : ∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j) :
    ∃ s : chartAlgInf R F j, (∃ a : chartAlgInf R F j, s = 1 + jInvChartInf R F j * a) ∧
      ∀ y ∈ chartAlgInf R F j', ∃ n : ℕ, (s : F) ^ n * y ∈ chartAlgInf R F j := by
  classical
  set A := chartAlgInf R F j with hA
  set A' := chartAlgInf R F j' with hA'
  choose! σ hσA hσ1 hσy using hvis
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := R) (A := A')

  let sF : F := ∏ t ∈ T, σ (t : F)
  have hjinv : (j⁻¹ : F) ∈ A := subset_chartAlg R F _ rfl

  have hsA : sF ∈ A := Subalgebra.prod_mem _ fun t _ => hσA _ t.2

  have hs1 : ∃ a ∈ A, sF = 1 + j⁻¹ * a := by
    refine Finset.prod_induction (fun t : A' => σ (t : F)) (fun x : F => ∃ a ∈ A, x = 1 + j⁻¹ * a)
      ?_ ⟨0, zero_mem _, by ring⟩ (fun t _ => hσ1 _ t.2)
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b + j⁻¹ * a * b, add_mem (add_mem ha hb) (mul_mem (mul_mem hjinv ha) hb), by ring⟩

  have hgen : ∀ t ∈ T, sF * (t : F) ∈ A := by
    intro t ht
    have : sF = (∏ x ∈ T.erase t, σ (x : F)) * σ (t : F) := by
      rw [mul_comm]; exact (Finset.mul_prod_erase T (fun x : A' => σ (x : F)) ht).symm
    rw [this, mul_assoc]
    exact mul_mem (Subalgebra.prod_mem _ fun x _ => hσA _ x.2) (hσy _ t.2)

  have hall : ∀ y : A', ∃ n : ℕ, sF ^ n * (y : F) ∈ A := by
    intro y
    have hy : y ∈ Algebra.adjoin R (T : Set A') := by rw [hT]; exact Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem t ht => exact ⟨1, by rw [pow_one]; exact hgen t ht⟩
    | algebraMap r =>
      refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      change algebraMap R F r ∈ A
      exact Subalgebra.algebraMap_mem _ r
    | add y z _ _ hy hz =>
      obtain ⟨m, hm⟩ := hy
      obtain ⟨n, hn⟩ := hz
      refine ⟨m + n, ?_⟩
      have : sF ^ (m + n) * ((y + z : A') : F) = sF ^ n * (sF ^ m * (y : F)) + sF ^ m * (sF ^ n * (z : F)) := by
        rw [Subalgebra.coe_add]; ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hsA n) hm) (mul_mem (pow_mem hsA m) hn)
    | mul y z _ _ hy hz =>
      obtain ⟨m, hm⟩ := hy
      obtain ⟨n, hn⟩ := hz
      refine ⟨m + n, ?_⟩
      have : sF ^ (m + n) * ((y * z : A') : F) = (sF ^ m * (y : F)) * (sF ^ n * (z : F)) := by
        rw [Subalgebra.coe_mul]; ring
      rw [this]
      exact mul_mem hm hn
  obtain ⟨a, ha, hsa⟩ := hs1
  refine ⟨⟨sF, hsA⟩, ⟨⟨a, ha⟩, Subtype.ext ?_⟩, fun y hy => hall ⟨y, hy⟩⟩
  simpa using hsa

omit [Fact (j' ≠ 0)] in

theorem spec_map_comp_eq_id {A B : Type u} [CommRing A] [CommRing B] (a : B →+* A) (b : A →+* B)
    (hab : ∀ x, a (b x) = x) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show a.comp b = RingHom.id A from RingHom.ext hab, CommRingCat.ofHom_id]
  exact Spec.map_id _

omit [Fact (j' ≠ 0)] in

theorem isDominant_ιFin [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)] :
    IsDominant (ιFin R F j) :=
  ⟨(ιFin R F j).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

theorem main
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)] [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j')]
    [IsSeparated (toBase R F j)] [IsSeparated (toBase R F j')]
    [Algebra.FiniteType R (chartAlgInf R F j)] [Algebra.FiniteType R (chartAlgInf R F j')]
    (hfin : j' ∈ chartAlgFin R F j) (hfin' : j ∈ chartAlgFin R F j')
    (hvis : ∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j)
    (hvis' : ∀ y ∈ chartAlgInf R F j, ∃ s ∈ chartAlgInf R F j',
      (∃ a ∈ chartAlgInf R F j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j')
      (ιF : chartAlgFin R F j' →ₐ[R] chartAlgFin R F j)
      (s : chartAlgInf R F j) (ψ : chartAlgInf R F j' →ₐ[R] Localization.Away s),
      (∀ x, (ιF x : F) = x) ∧ Function.Bijective ιF ∧
      (∃ a : chartAlgInf R F j, s = 1 + jInvChartInf R F j * a) ∧
      (∀ y : chartAlgInf R F j', ∃ (n : ℕ) (z : chartAlgInf R F j), (s : F) ^ n * (y : F) = z ∧
        ψ y * algebraMap _ (Localization.Away s) (s ^ n) = algebraMap _ (Localization.Away s) z) ∧
      w.hom ≫ toBase R F j' = toBase R F j ∧
      ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F j' ∧
      Spec.map (CommRingCat.ofHom (algebraMap (chartAlgInf R F j) (Localization.Away s))) ≫ ιInf R F j ≫ w.hom =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ιInf R F j' := by
  obtain ⟨s, hs, hU⟩ := exists_uniform R F j j' hvis
  obtain ⟨s', hs', hU'⟩ := exists_uniform R F j' j hvis'
  obtain ⟨g, ιF, ψ, hιF, hψ, hgb, hgFin, hgInf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_hom_of_mem_chartAlgFin_of_forall_pow_mul_mem
      R F j j' hfin s hs hU
  obtain ⟨g', ιF', ψ', hιF', -, hg'b, hg'Fin, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_hom_of_mem_chartAlgFin_of_forall_pow_mul_mem
      R F j' j hfin' s' hs' hU'
  haveI := isDominant_ιFin R F j
  haveI := isDominant_ιFin R F j'
  have hFF' : ∀ x, ιF (ιF' x) = x := fun x => Subtype.ext (by rw [hιF, hιF'])
  have hF'F : ∀ x, ιF' (ιF x) = x := fun x => Subtype.ext (by rw [hιF', hιF])

  have h1 : g ≫ g' = 𝟙 _ := by
    refine ext_of_isDominant_of_isSeparated (toBase R F j) ?_ (ιFin R F j) ?_
    · rw [Category.assoc, hg'b, hgb, Category.id_comp]
    · rw [← Category.assoc, hgFin, Category.assoc, hg'Fin, ← Category.assoc,
        spec_map_comp_eq_id ιF.toRingHom ιF'.toRingHom hFF', Category.id_comp, Category.comp_id]
  have h2 : g' ≫ g = 𝟙 _ := by
    refine ext_of_isDominant_of_isSeparated (toBase R F j') ?_ (ιFin R F j') ?_
    · rw [Category.assoc, hgb, hg'b, Category.id_comp]
    · rw [← Category.assoc, hg'Fin, Category.assoc, hgFin, ← Category.assoc,
        spec_map_comp_eq_id ιF'.toRingHom ιF.toRingHom hF'F, Category.id_comp, Category.comp_id]
  refine ⟨⟨g, g', h1, h2⟩, ιF, s, ψ, hιF, ⟨fun x y hxy => ?_, fun z => ⟨ιF' z, hFF' z⟩⟩, hs, hψ,
    hgb, hgFin, hgInf⟩
  exact Subtype.ext (by rw [← hιF x, ← hιF y, hxy])

end UB

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j j' : F) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)] [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j')]
    [IsSeparated (toBase R F j)] [IsSeparated (toBase R F j')]
    [Algebra.FiniteType R (chartAlgInf R F j)] [Algebra.FiniteType R (chartAlgInf R F j')]
    (hfin : j' ∈ chartAlgFin R F j) (hfin' : j ∈ chartAlgFin R F j')
    (hvis : ∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j)
    (hvis' : ∀ y ∈ chartAlgInf R F j, ∃ s ∈ chartAlgInf R F j',
      (∃ a ∈ chartAlgInf R F j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j')
      (ιF : chartAlgFin R F j' →ₐ[R] chartAlgFin R F j)
      (s : chartAlgInf R F j) (ψ : chartAlgInf R F j' →ₐ[R] Localization.Away s),
      (∀ x, (ιF x : F) = x) ∧ Function.Bijective ιF ∧
      (∃ a : chartAlgInf R F j, s = 1 + jInvChartInf R F j * a) ∧
      (∀ y : chartAlgInf R F j', ∃ (n : ℕ) (z : chartAlgInf R F j), (s : F) ^ n * (y : F) = z ∧
        ψ y * algebraMap _ (Localization.Away s) (s ^ n) = algebraMap _ (Localization.Away s) z) ∧
      w.hom ≫ toBase R F j' = toBase R F j ∧
      ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F j' ∧
      Spec.map (CommRingCat.ofHom (algebraMap (chartAlgInf R F j) (Localization.Away s))) ≫ ιInf R F j ≫ w.hom =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ιInf R F j' :=
  UB.main R F j j' hfin hfin' hvis hvis'

end S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem (solution)
