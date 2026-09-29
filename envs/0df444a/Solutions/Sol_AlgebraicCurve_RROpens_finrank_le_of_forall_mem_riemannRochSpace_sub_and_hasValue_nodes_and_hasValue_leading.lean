-- Prove2me | solution 1 for AlgebraicCurve.RROpens.finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7ef4eb4e-4c44-5800-a544-33b571e804d6

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Theorems.Thm_AlgebraicCurve_RROpens_exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RROpens_finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading

set_option autoImplicit false

universe u v

open AlgebraicCurve IsLocalRing

namespace CountSol

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem isRational_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem evalAt_eq_of_hasValue (v : Place K F) {f : F} {a : K} (h : v.HasValue f a) : v.evalAt f = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, v.algebraMap_evalAt hv (add_mem hf hg)]
  have : (⟨f + g, add_mem hf hg⟩ : v.toValuationSubring) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
  rw [this, map_add]

theorem evalAt_smul (v : Place K F) (hv : v.IsRational) (c : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (c • f) = c * v.evalAt f := by
  have hcf : c • f ∈ v.toValuationSubring := by
    rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' c) hf
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv hcf, v.algebraMap_evalAt hv hf]
  have : (⟨c • f, hcf⟩ : v.toValuationSubring) = ⟨algebraMap K F c, v.algebraMap_mem' c⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def c f)
  rw [this, map_mul]
  congr 1

theorem evalAt_zero' (v : Place K F) : v.evalAt (0 : F) = 0 := by
  have h : v.HasValue (0 : F) 0 := by simpa using v.hasValue_algebraMap (0 : K)
  exact evalAt_eq_of_hasValue v h

theorem ord_ge_of_mem_lSpace {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) (hf0 : f ≠ 0) (v : Place K F) :
    -D v ≤ v.ord f := by
  rcases mem_lSpace_iff_ord.mp hf with h | h
  · exact absurd h hf0
  · exact h v

theorem mul_zpow_mem_of_mem_lSpace {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) (v : Place K F) (x : F) (hx0 : x ≠ 0)
    (n : ℤ) (h : 0 ≤ -D v + n * v.ord x) : f * x ^ n ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0, zero_mul]; exact zero_mem _
  · refine v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hf0 (zpow_ne_zero _ hx0)) ?_
    rw [v.ord_mul hf0 (zpow_ne_zero _ hx0), v.ord_zpow]
    have := ord_ge_of_mem_lSpace hf hf0 v
    linarith

theorem mem_of_mem_lSpace {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) (v : Place K F) (h : D v ≤ 0) :
    f ∈ v.toValuationSubring := by
  have := mul_zpow_mem_of_mem_lSpace hf v 1 one_ne_zero 0 (by simp; linarith)
  simpa using this

end CountSol

open CountSol

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (SS : Finset (Place K F × Place K F))
    (hinj : Set.InjOn Prod.fst (SS : Set (Place K F × Place K F)))
    (s : Place K F × Place K F) (hs : s ∈ SS)
    (D₁ D₂ : Divisor K F) (hD₁ : ∀ t ∈ SS, D₁ t.1 = 0) (hD₂ : ∀ t ∈ SS, D₂ t.2 = 0)
    (x y : F) (hx : s.1.ord x = 1) (hy : s.2.ord y = 1)
    (u : K) (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k)
    (hdeg₁ : 2 * (g : ℤ) + m + SS.card ≤ Divisor.degree D₁)
    (hdeg₂ : 2 * (g : ℤ) + k + SS.card ≤ Divisor.degree D₂)
    (P : Submodule K (Fin 2 → F))
    (hP : ∀ h ∈ P,
      h 0 ∈ riemannRochSpace (D₁ - Finsupp.single s.1 m) ∧
      h 1 ∈ riemannRochSpace (D₂ - Finsupp.single s.2 k) ∧
      (∀ t ∈ SS, t ≠ s → ∃ c : K, t.1.HasValue (h 0) c ∧ t.2.HasValue (h 1) c) ∧
      (∃ lam : K, s.2.HasValue (h 1 * y ^ (-k)) lam ∧ s.1.HasValue (h 0 * x ^ (-m)) (u * lam))) :
    FiniteDimensional K ↥P ∧
      (Module.finrank K ↥P : ℤ) ≤
        (Divisor.degree D₁ - m) + (Divisor.degree D₂ - k) + 2 - 2 * (g : ℤ) - SS.card := by
  classical

  have hrat : ∀ v : Place K F, v.IsRational := isRational_of_isAlgClosed
  have hdeg1 : ∀ v : Place K F, (v.deg : ℤ) = 1 := fun v => by
    rw [Place.deg_eq_one_of_isRational (hrat v)]; rfl
  have hdegs : ∀ (v : Place K F) (n : ℤ), Divisor.degree (Finsupp.single v n) = n := fun v n => by
    rw [Divisor.degree_single, hdeg1, mul_one]
  have hKc : Divisor.degree Kc = 2 * (g : ℤ) - 2 := by
    have h0 := hRR 0
    have h1 := hRR Kc
    rw [sub_zero, map_zero] at h0
    rw [sub_self] at h1
    omega
  have hell : ∀ D' : Divisor K F, 2 * (g : ℤ) - 1 ≤ Divisor.degree D' → (ell D' : ℤ) = Divisor.degree D' + 1 - g := by
    intro D' hD'
    have hneg : Divisor.degree (Kc - D') < 0 := by rw [map_sub, hKc]; omega
    have h0 : ell (Kc - D') = 0 := AlgebraicCurve.ell_eq_zero_of_degree_neg hneg
    have := hRR D'
    rw [h0] at this
    push_cast at this
    omega
  have hcard1 : 1 ≤ SS.card := Finset.card_pos.mpr ⟨s, hs⟩

  set E₁ : Divisor K F := D₁ - Finsupp.single s.1 m with hE₁
  set E₂ : Divisor K F := D₂ - Finsupp.single s.2 k with hE₂
  have hE₁deg : Divisor.degree E₁ = Divisor.degree D₁ - m := by rw [hE₁, map_sub, hdegs]
  have hE₂deg : Divisor.degree E₂ = Divisor.degree D₂ - k := by rw [hE₂, map_sub, hdegs]
  have hell₁ : (ell E₁ : ℤ) = Divisor.degree D₁ - m + 1 - g := by rw [hell E₁ (by omega), hE₁deg]
  have hell₂ : (ell E₂ : ℤ) = Divisor.degree D₂ - k + 1 - g := by rw [hell E₂ (by omega), hE₂deg]
  haveI hfin₁ : FiniteDimensional K ↥(LSpace E₁) := by
    refine Module.finite_of_finrank_pos ?_
    have : (0 : ℤ) < ell E₁ := by rw [hell₁]; omega
    exact_mod_cast this
  haveI hfin₂ : FiniteDimensional K ↥(LSpace E₂) := by
    refine Module.finite_of_finrank_pos ?_
    have : (0 : ℤ) < ell E₂ := by rw [hell₂]; omega
    exact_mod_cast this

  have hE₁t : ∀ t ∈ SS, E₁ t.1 ≤ 0 := by
    intro t ht
    rw [hE₁, Finsupp.sub_apply, hD₁ t ht, Finsupp.single_apply]
    split_ifs <;> omega
  have hE₂t : ∀ t ∈ SS, E₂ t.2 ≤ 0 := by
    intro t ht
    rw [hE₂, Finsupp.sub_apply, hD₂ t ht, Finsupp.single_apply]
    split_ifs <;> omega
  have hE₁s : E₁ s.1 = -m := by rw [hE₁, Finsupp.sub_apply, hD₁ s hs, Finsupp.single_apply, if_pos rfl]; ring
  have hE₂s : E₂ s.2 = -k := by rw [hE₂, Finsupp.sub_apply, hD₂ s hs, Finsupp.single_apply, if_pos rfl]; ring
  have hx0 : x ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hx; exact zero_ne_one hx
  have hy0 : y ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hy; exact zero_ne_one hy

  have hreg₁ : ∀ (f : ↥(LSpace E₁)) (t : Place K F × Place K F), t ∈ SS → (f : F) ∈ t.1.toValuationSubring :=
    fun f t ht => mem_of_mem_lSpace f.2 t.1 (hE₁t t ht)
  have hreg₂ : ∀ (f : ↥(LSpace E₂)) (t : Place K F × Place K F), t ∈ SS → (f : F) ∈ t.2.toValuationSubring :=
    fun f t ht => mem_of_mem_lSpace f.2 t.2 (hE₂t t ht)
  have hregx : ∀ f : ↥(LSpace E₁), (f : F) * x ^ (-m) ∈ s.1.toValuationSubring :=
    fun f => mul_zpow_mem_of_mem_lSpace f.2 s.1 x hx0 (-m) (by rw [hE₁s, hx]; ring_nf; exact le_rfl)
  have hregy : ∀ f : ↥(LSpace E₂), (f : F) * y ^ (-k) ∈ s.2.toValuationSubring :=
    fun f => mul_zpow_mem_of_mem_lSpace f.2 s.2 y hy0 (-k) (by rw [hE₂s, hy]; ring_nf; exact le_rfl)

  let φ : ↥SS → (↥(LSpace E₁) × ↥(LSpace E₂)) →ₗ[K] K := fun t =>
    { toFun := fun fg =>
        if (t : Place K F × Place K F) = s then
          s.1.evalAt ((fg.1 : F) * x ^ (-m)) - u * s.2.evalAt ((fg.2 : F) * y ^ (-k))
        else (t : Place K F × Place K F).1.evalAt (fg.1 : F) - (t : Place K F × Place K F).2.evalAt (fg.2 : F)
      map_add' := by
        intro fg fg'
        split_ifs with hts
        · rw [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Submodule.coe_add, add_mul, add_mul,
            evalAt_add s.1 (hrat _) (hregx fg.1) (hregx fg'.1), evalAt_add s.2 (hrat _) (hregy fg.2) (hregy fg'.2)]
          ring
        · rw [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Submodule.coe_add,
            evalAt_add _ (hrat _) (hreg₁ fg.1 t t.2) (hreg₁ fg'.1 t t.2),
            evalAt_add _ (hrat _) (hreg₂ fg.2 t t.2) (hreg₂ fg'.2 t t.2)]
          ring
      map_smul' := by
        intro c fg
        simp only [RingHom.id_apply, smul_eq_mul]
        split_ifs with hts
        · rw [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Submodule.coe_smul, smul_mul_assoc, smul_mul_assoc,
            evalAt_smul s.1 (hrat _) c (hregx fg.1), evalAt_smul s.2 (hrat _) c (hregy fg.2)]
          ring
        · rw [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Submodule.coe_smul,
            evalAt_smul _ (hrat _) c (hreg₁ fg.1 t t.2), evalAt_smul _ (hrat _) c (hreg₂ fg.2 t t.2)]
          ring }
  let Φ : (↥(LSpace E₁) × ↥(LSpace E₂)) →ₗ[K] (↥SS → K) := LinearMap.pi φ
  have hΦ_apply : ∀ (fg : ↥(LSpace E₁) × ↥(LSpace E₂)) (t : ↥SS), Φ fg t =
      (if (t : Place K F × Place K F) = s then
          s.1.evalAt ((fg.1 : F) * x ^ (-m)) - u * s.2.evalAt ((fg.2 : F) * y ^ (-k))
        else (t : Place K F × Place K F).1.evalAt (fg.1 : F) - (t : Place K F × Place K F).2.evalAt (fg.2 : F)) :=
    fun fg t => rfl

  let ι : ↥P →ₗ[K] (↥(LSpace E₁) × ↥(LSpace E₂)) :=
    { toFun := fun h => (⟨(h : Fin 2 → F) 0, (hP h h.2).1⟩, ⟨(h : Fin 2 → F) 1, (hP h h.2).2.1⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι_inj : Function.Injective ι := by
    intro h h' hh
    have h0 : (h : Fin 2 → F) 0 = (h' : Fin 2 → F) 0 := congrArg (fun q => ((q.1 : ↥(LSpace E₁)) : F)) hh
    have h1 : (h : Fin 2 → F) 1 = (h' : Fin 2 → F) 1 := congrArg (fun q => ((q.2 : ↥(LSpace E₂)) : F)) hh
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hι_ker : LinearMap.range ι ≤ LinearMap.ker Φ := by
    rintro _ ⟨h, rfl⟩
    rw [LinearMap.mem_ker]
    funext t
    rw [hΦ_apply, Pi.zero_apply]
    obtain ⟨-, -, hnodes, lam, hlam2, hlam1⟩ := hP h h.2
    split_ifs with hts
    · show s.1.evalAt ((h : Fin 2 → F) 0 * x ^ (-m)) - u * s.2.evalAt ((h : Fin 2 → F) 1 * y ^ (-k)) = 0
      rw [evalAt_eq_of_hasValue _ hlam1, evalAt_eq_of_hasValue _ hlam2, sub_self]
    · obtain ⟨c, hc1, hc2⟩ := hnodes t t.2 hts
      show (t : Place K F × Place K F).1.evalAt ((h : Fin 2 → F) 0) - (t : Place K F × Place K F).2.evalAt ((h : Fin 2 → F) 1) = 0
      rw [evalAt_eq_of_hasValue _ hc1, evalAt_eq_of_hasValue _ hc2, sub_self]

  have hΦ_surj : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro b

    let Z : Finset (Place K F) := (SS.erase s).image Prod.fst
    let c : Place K F → K := fun z => ∑ t ∈ SS.attach, if (t : Place K F × Place K F).1 = z ∧ (t : Place K F × Place K F) ≠ s then b t else 0
    have hc : ∀ t : ↥SS, (t : Place K F × Place K F) ≠ s → c (t : Place K F × Place K F).1 = b t := by
      intro t hts
      show (∑ t' ∈ SS.attach, if (t' : Place K F × Place K F).1 = (t : Place K F × Place K F).1 ∧ (t' : Place K F × Place K F) ≠ s
        then b t' else 0) = b t
      rw [Finset.sum_eq_single_of_mem t (Finset.mem_attach _ _)]
      · rw [if_pos ⟨rfl, hts⟩]
      · intro t' _ hne
        rw [if_neg]
        rintro ⟨h1, -⟩
        exact hne (Subtype.ext (hinj t'.2 t.2 h1))
    have hZ : ∀ z ∈ Z, D₁ z = 0 := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact hD₁ t (Finset.mem_of_mem_erase ht)
    have hsZ : s.1 ∉ Z := by
      intro hz
      obtain ⟨t, ht, hts1⟩ := Finset.mem_image.mp hz
      obtain ⟨hne, htS⟩ := Finset.mem_erase.mp ht
      exact hne (hinj htS hs hts1)
    have hZcard : (Z.card : ℤ) ≤ SS.card - 1 := by
      have h1 : Z.card ≤ (SS.erase s).card := Finset.card_image_le
      have h2 := Finset.card_erase_of_mem hs
      omega
    obtain ⟨f, hfmem, hflead, hfval⟩ :=
      AlgebraicCurve.RROpens.exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue Kc g hRR D₁ Z hZ c
        s.1 hsZ (hD₁ s hs) x hx m.toNat (b ⟨s, hs⟩) (by rw [Int.toNat_of_nonneg hm]; omega)
    have hmto : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    rw [hmto] at hfmem hflead
    refine ⟨(⟨f, hfmem⟩, 0), ?_⟩
    funext t
    rw [hΦ_apply]
    split_ifs with hts
    · simp only [Submodule.coe_zero, zero_mul, evalAt_zero', mul_zero, sub_zero]
      rw [evalAt_eq_of_hasValue _ hflead]
      congr 1
      exact Subtype.ext hts.symm
    · simp only [Submodule.coe_zero, evalAt_zero', sub_zero]
      have hz : (t : Place K F × Place K F).1 ∈ Z :=
        Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨hts, t.2⟩, rfl⟩
      rw [evalAt_eq_of_hasValue _ (hfval _ hz), hc t hts]

  haveI : FiniteDimensional K (↥(LSpace E₁) × ↥(LSpace E₂)) := inferInstance
  have hPfin : FiniteDimensional K ↥P := Module.Finite.of_injective ι hι_inj
  refine ⟨hPfin, ?_⟩
  have h1 : Module.finrank K ↥P = Module.finrank K ↥(LinearMap.range ι) := (LinearMap.finrank_range_of_inj hι_inj).symm
  have h2 : Module.finrank K ↥(LinearMap.range ι) ≤ Module.finrank K ↥(LinearMap.ker Φ) := Submodule.finrank_mono hι_ker
  have h3 := LinearMap.finrank_range_add_finrank_ker Φ
  have h4 : Module.finrank K ↥(LinearMap.range Φ) = SS.card := by
    rw [hΦ_surj, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h5 : Module.finrank K (↥(LSpace E₁) × ↥(LSpace E₂)) = ell E₁ + ell E₂ := Module.finrank_prod
  have h6 : (Module.finrank K ↥(LinearMap.ker Φ) : ℤ) = ell E₁ + ell E₂ - SS.card := by
    have : (Module.finrank K ↥(LinearMap.range Φ) : ℤ) + Module.finrank K ↥(LinearMap.ker Φ) = ell E₁ + ell E₂ := by
      exact_mod_cast (h3.trans h5)
    rw [h4] at this
    omega
  calc (Module.finrank K ↥P : ℤ) ≤ Module.finrank K ↥(LinearMap.ker Φ) := by rw [h1]; exact_mod_cast h2
    _ = _ := by rw [h6, hell₁, hell₂]; ring

end S_AlgebraicCurve_RROpens_finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading
end P2MW
export P2MW.S_AlgebraicCurve_RROpens_finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading (solution)
