-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/50f6f116-734f-5348-a642-1d3207c27453

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_pow_mul_mem_chartAlgFin_of_forall_place
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData

set_option autoImplicit false

universe u

p2m_open "IsLocalRing AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData.AlgebraicCurve.TwoChartIntegralModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel Place Place.ord_inv Divisor Divisor.degree Divisor.degree_single IsCurveOver IsCurveOver.finiteResidue lSpaceOn mem_lSpaceOn_iff mem_lSpaceOn_iff_ord"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg mem_chartAlg_iff chartAlgFin chartAlgInf chartAlgMid jChartFin finiteType_chartAlgFin_and_chartAlgInf exists_pow_mul_mem_chartAlgFin_of_forall_place exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

namespace GenFibre

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_pos_of_mem_nonunits (v : Place K F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring.nonunits) :
    0 < v.ord f := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hf
  rcases hf with h | h
  · exact absurd h hf0
  · by_contra hle
    apply h
    apply mem_of_ord_nonneg v (inv_ne_zero hf0)
    rw [Place.ord_inv]; omega

theorem mem_of_adicValuation_le_one (v : Place K F) {f : F} (h : v.adicValuation f ≤ 1) :
    f ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact v.toValuationSubring.zero_mem
  · rcases (v.adicValuation_le_one_iff).1 h with h' | h'
    · exact absurd h' hf0
    · exact mem_of_ord_nonneg v hf0 h'

end GenFibre

open GenFibre in
theorem main
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] [IsCurveOver K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal)
    (hϖ𝔪 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔪 i) (hf𝔪 : ∀ i, jChartFin R F f ∈ 𝔪 i)
    (I : ι → Ideal ↥(chartAlgFin R F f))
    (hI : ∀ i (a : ↥(chartAlgFin R F f)), a ∈ I i ↔
      ∃ s : ↥(chartAlgFin R F f), s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {jChartFin R F f})
    (hne : ∀ i, I i ≠ ⊤)
    (htor : ∀ i (y : ↥(chartAlgFin R F f) ⧸ I i), algebraMap R (↥(chartAlgFin R F f) ⧸ I i) ϖ * y = 0 → y = 0)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i) :
    ∃ D_K : Divisor K₀ F, 0 ≤ D_K ∧ 0 < Divisor.degree D_K ∧
      (∀ v : Place K₀ F, f⁻¹ ∈ v.toValuationSubring → D_K v = 0) ∧
      ∀ n : ℕ,

        (∀ g : F, g ∈ lSpaceOn {v : Place K₀ F | f ∈ v.toValuationSubring} ((n : ℤ) • D_K) →
          ∃ k : ℕ, ∀ a ∈ (∏ i, I i) ^ n, ∃ b : ↥(chartAlgFin R F f),
            algebraMap R F ϖ ^ k * g * (a : F) = (b : F)) ∧

        (∀ z : ↥(chartAlgMid R F f), (z : F) ∈
          lSpaceOn ({v : Place K₀ F | f ∈ v.toValuationSubring} ∩ {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring})
            ((n : ℤ) • D_K)) ∧

        (∀ g : F, g ∈ lSpaceOn {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring} ((n : ℤ) • D_K) →
          ∃ (k : ℕ) (b : ↥(chartAlgInf R F f)), algebraMap R F ϖ ^ k * g = (b : F)) := by
  classical

  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hf0 : f ≠ 0 := Fact.out
  haveI hfi : Fact (f⁻¹ ≠ 0) := ⟨inv_ne_zero hf0⟩
  have hadj : IntermediateField.adjoin K₀ ({f⁻¹} : Set F) = IntermediateField.adjoin K₀ ({f} : Set F) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K₀ f)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := inv_mem (IntermediateField.mem_adjoin_simple_self K₀ f⁻¹)
      rwa [inv_inv] at h
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f⁻¹} : Set F)) F := by rw [hadj]; exact hFD
  obtain ⟨hFT, -⟩ := finiteType_chartAlgFin_and_chartAlgInf R K₀ F f htf hFD hsep
  haveI := hFT
  haveI : IsNoetherianRing ↥(chartAlgFin R F f) := Algebra.FiniteType.isNoetherianRing R _
  have hϖprime : Prime ϖ := ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ).prime
  have hϖ0 : algebraMap R F ϖ ≠ 0 := (map_ne_zero_iff _ hRF).2 hϖprime.ne_zero

  have hKv : ∀ (v : Place K₀ F) (a : K₀), algebraMap K₀ F a ∈ v.toValuationSubring := fun v a => v.algebraMap_mem' a
  have hRv : ∀ (v : Place K₀ F) (r : R), algebraMap R F r ∈ v.toValuationSubring := fun v r => by
    rw [IsScalarTower.algebraMap_apply R K₀ F]; exact hKv v _

  have hchart : ∀ (S : Set F) (v : Place K₀ F), S ⊆ v.toValuationSubring →
      ∀ z : ↥(chartAlg R F S), (z : F) ∈ v.toValuationSubring := by
    intro S v hS z
    have hadjO : ∀ y : F, y ∈ Algebra.adjoin R S → y ∈ v.toValuationSubring := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem w hw => exact hS hw
      | algebraMap r => exact hRv v r
      | add a b _ _ ha hb => exact v.toValuationSubring.add_mem _ _ ha hb
      | mul a b _ _ ha hb => exact v.toValuationSubring.mul_mem _ _ ha hb
    let φ : ↥(Algebra.adjoin R S) →+* ↥v.toValuationSubring :=
      { toFun := fun y => ⟨(y : F), hadjO y y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    letI : Algebra ↥(Algebra.adjoin R S) ↥v.toValuationSubring := φ.toAlgebra
    haveI : IsScalarTower ↥(Algebra.adjoin R S) ↥v.toValuationSubring F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hz : IsIntegral ↥(Algebra.adjoin R S) (z : F) := (mem_chartAlg_iff R F).mp z.2
    have hzO : IsIntegral ↥v.toValuationSubring (z : F) := hz.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥v.toValuationSubring) (K := F)).mp hzO
    rw [← hy]; exact y.2
  have hAv : ∀ v : Place K₀ F, f ∈ v.toValuationSubring → ∀ a : ↥(chartAlgFin R F f), (a : F) ∈ v.toValuationSubring :=
    fun v hv => hchart {f} v (Set.singleton_subset_iff.mpr hv)

  have hfI : ∀ i, jChartFin R F f ∈ I i := fun i =>
    (hI i _).2 ⟨1, fun h => (h𝔪 i).ne_top ((Ideal.eq_top_iff_one _).2 h), by rw [one_mul]; exact Ideal.mem_span_singleton_self _⟩

  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  obtain ⟨v₀, hAv₀, hIv₀⟩ :=
    exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp R ϖ hϖ K₀ F f htf hFD hsep
      (I i₀) (hne i₀) (hfI i₀) (htor i₀)
  have hfv₀ : f ∈ v₀.toValuationSubring.nonunits := hIv₀ _ (hfI i₀)
  have hordf : 0 < v₀.ord f := ord_pos_of_mem_nonunits v₀ hf0 hfv₀
  let D_K : Divisor K₀ F := Finsupp.single v₀ (v₀.ord f)
  have hDv₀ : D_K v₀ = v₀.ord f := Finsupp.single_eq_same
  have hDne : ∀ v, v ≠ v₀ → D_K v = 0 := fun v hv => Finsupp.single_eq_of_ne hv
  have hDnn : 0 ≤ D_K := by
    intro v
    by_cases hv : v = v₀
    · subst hv; rw [hDv₀]; exact hordf.le
    · rw [hDne v hv]; exact le_rfl

  have hunit : ∀ s : ↥(chartAlgFin R F f), s ∉ 𝔪 i₀ → v₀.adicValuation (s : F) = 1 := by

    let toO : ↥(chartAlgFin R F f) →+* ↥v₀.toValuationSubring :=
      ((chartAlgFin R F f).val.toRingHom).codRestrict v₀.toValuationSubring.toSubring (fun a => hAv₀ a)
    let 𝔭 : Ideal ↥(chartAlgFin R F f) := (maximalIdeal ↥v₀.toValuationSubring).comap toO
    have hmem : ∀ a, a ∈ 𝔭 ↔ ((a : ↥(chartAlgFin R F f)) : F) ∈ v₀.toValuationSubring.nonunits := by
      intro a
      rw [Ideal.mem_comap]
      exact (ValuationSubring.coe_mem_nonunits_iff (A := v₀.toValuationSubring) (a := toO a)).symm
    have h𝔭le : 𝔭 ≤ 𝔪 i₀ := hle i₀ 𝔭 (Ideal.comap_isPrime toO _) (fun a ha => (hmem a).2 (hIv₀ a ha))
    intro s hs
    have hsn : (s : F) ∉ v₀.toValuationSubring.nonunits := fun h => hs (h𝔭le ((hmem s).2 h))
    have hsu : IsUnit (toO s) := by
      by_contra hu
      exact hsn ((ValuationSubring.coe_mem_nonunits_iff (A := v₀.toValuationSubring) (a := toO s)).2
        ((mem_maximalIdeal _).2 hu))
    exact (v₀.adicValuation_coe_eq_one_iff (toO s)).2 hsu
  have hvalI : ∀ a ∈ I i₀, v₀.adicValuation ((a : ↥(chartAlgFin R F f)) : F) ≤ v₀.adicValuation f := by
    intro a ha
    obtain ⟨s, hs, hsa⟩ := (hI i₀ a).1 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hsa

    have hF : (c : F) * f = (s : F) * (a : F) := by
      have := congrArg (fun x : ↥(chartAlgFin R F f) => (x : F)) hc
      simpa using this
    have : v₀.adicValuation ((s : F) * (a : F)) = v₀.adicValuation (c : F) * v₀.adicValuation f := by
      rw [← hF, map_mul]
    rw [map_mul, hunit s hs, one_mul] at this
    rw [this]
    exact mul_le_of_le_one_left' (v₀.adicValuation_le_one_of_mem (hAv₀ c))

  have hJle : (∏ i, I i) ≤ I i₀ := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀)]
    exact Ideal.mul_le_right
  have hvalJ : ∀ n : ℕ, ∀ a ∈ (∏ i, I i) ^ n,
      v₀.adicValuation ((a : ↥(chartAlgFin R F f)) : F) ≤ v₀.adicValuation f ^ n := by
    intro n
    induction n with
    | zero =>
      intro a _
      rw [pow_zero]; exact v₀.adicValuation_le_one_of_mem (hAv₀ a)
    | succ n ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro x hx y hy
        rw [Subalgebra.coe_mul, map_mul, pow_succ]
        exact mul_le_mul' (ih x hx) ((hvalI y (hJle hy)))
      · intro x y hx hy
        rw [Subalgebra.coe_add]
        exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  refine ⟨D_K, hDnn, ?_, ?_, ?_⟩
  ·
    haveI : Module.Finite K₀ v₀.ResidueField := IsCurveOver.finiteResidue v₀
    have hdeg : 0 < (v₀.deg : ℤ) := by
      have : 0 < v₀.deg := Module.finrank_pos
      exact_mod_cast this
    show 0 < Divisor.degree (Finsupp.single v₀ (v₀.ord f))
    rw [Divisor.degree_single]
    exact mul_pos hordf hdeg
  ·
    intro v hv
    by_cases hvv : v = v₀
    · subst hvv
      exfalso
      rw [ValuationSubring.mem_nonunits_iff_or] at hfv₀
      rcases hfv₀ with h | h
      · exact hf0 h
      · exact h hv
    · exact hDne v hvv
  · intro n
    have hnD : ∀ v, ((n : ℤ) • D_K) v = (n : ℤ) * D_K v := fun v => by simp
    refine ⟨?_, ?_, ?_⟩
    ·
      intro g hg
      rw [mem_lSpaceOn_iff] at hg

      have hga : ∀ a ∈ (∏ i, I i) ^ n, ∀ v : Place K₀ F, f ∈ v.toValuationSubring →
          g * ((a : ↥(chartAlgFin R F f)) : F) ∈ v.toValuationSubring := by
        intro a ha v hvf
        have hg' := hg v hvf
        by_cases hvv : v₀ = v
        · subst hvv

          have h1 : v₀.adicValuation g ≤ WithZero.exp ((n : ℤ) * v₀.ord f) := by rwa [hnD, hDv₀] at hg'
          have h2 : v₀.adicValuation ((a : ↥(chartAlgFin R F f)) : F) ≤ WithZero.exp (-((n : ℤ) * v₀.ord f)) := by
            have := hvalJ n a ha
            rwa [v₀.adicValuation_eq_exp_neg_ord hf0, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg] at this
          have h3 : v₀.adicValuation (g * ((a : ↥(chartAlgFin R F f)) : F)) ≤ 1 := by
            rw [map_mul]
            calc v₀.adicValuation g * v₀.adicValuation ((a : ↥(chartAlgFin R F f)) : F)
                ≤ WithZero.exp ((n : ℤ) * v₀.ord f) * WithZero.exp (-((n : ℤ) * v₀.ord f)) := mul_le_mul' h1 h2
              _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
          exact mem_of_adicValuation_le_one v₀ h3
        · have h1 : v.adicValuation g ≤ 1 := by rwa [hnD, hDne v (fun h => hvv h.symm), mul_zero, WithZero.exp_zero] at hg'
          exact v.toValuationSubring.mul_mem _ _ (mem_of_adicValuation_le_one v h1) (hAv v hvf a)

      obtain ⟨s, hs⟩ := (IsNoetherian.noetherian ((∏ i, I i) ^ n) : ((∏ i, I i) ^ n).FG)
      have hks : ∀ a : ↥s, ∃ k : ℕ, algebraMap R F ϖ ^ k * (g * ((a : ↥(chartAlgFin R F f)) : F)) ∈ chartAlgFin R F f := by
        intro a
        have ha : (a : ↥(chartAlgFin R F f)) ∈ (∏ i, I i) ^ n := by rw [← hs]; exact Submodule.subset_span a.2
        exact exists_pow_mul_mem_chartAlgFin_of_forall_place R ϖ hϖ K₀ F f hFD _ (hga _ ha)
      choose ks hks' using hks
      let k : ℕ := Finset.univ.sup ks
      refine ⟨k, ?_⟩
      intro a ha
      rw [← hs] at ha
      induction ha using Submodule.span_induction with
      | mem a has =>
        have hle' : ks ⟨a, has⟩ ≤ k := Finset.le_sup (Finset.mem_univ _)
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle'
        have hmem := hks' ⟨a, has⟩
        refine ⟨⟨algebraMap R F ϖ ^ d, pow_mem ((chartAlgFin R F f).algebraMap_mem ϖ) d⟩ * ⟨_, hmem⟩, ?_⟩
        change algebraMap R F ϖ ^ k * g * (a : F) =
          algebraMap R F ϖ ^ d * (algebraMap R F ϖ ^ ks ⟨a, has⟩ * (g * (a : F)))
        rw [hd, pow_add]; ring
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ iha ihb =>
        obtain ⟨ba, hba⟩ := iha
        obtain ⟨bb, hbb⟩ := ihb
        exact ⟨ba + bb, by rw [Subalgebra.coe_add, Subalgebra.coe_add, ← hba, ← hbb]; ring⟩
      | smul c a _ iha =>
        obtain ⟨ba, hba⟩ := iha
        refine ⟨c * ba, ?_⟩
        rw [Subalgebra.coe_mul, ← hba, smul_eq_mul, Subalgebra.coe_mul]; ring
    ·
      intro z
      rw [mem_lSpaceOn_iff_ord]
      rintro v ⟨hvf, hvfi⟩
      right
      have hS : ({f, f⁻¹} : Set F) ⊆ v.toValuationSubring := by
        intro w hw
        rcases hw with rfl | rfl
        · exact hvf
        · exact hvfi
      have hz : (z : F) ∈ v.toValuationSubring := hchart {f, f⁻¹} v hS z
      have h0 := ord_nonneg_of_mem v hz
      have hD : 0 ≤ D_K v := hDnn v
      rw [hnD]
      nlinarith
    ·
      intro g hg
      rw [mem_lSpaceOn_iff] at hg
      have hgv : ∀ v : Place K₀ F, f⁻¹ ∈ v.toValuationSubring → g ∈ v.toValuationSubring := by
        intro v hv
        have hvv : v ≠ v₀ := by
          intro h; subst h
          rw [ValuationSubring.mem_nonunits_iff_or] at hfv₀
          rcases hfv₀ with h | h
          · exact hf0 h
          · exact h hv
        have h1 : v.adicValuation g ≤ 1 := by
          have := hg v hv
          rwa [hnD, hDne v hvv, mul_zero, WithZero.exp_zero] at this
        exact mem_of_adicValuation_le_one v h1
      obtain ⟨k, hk⟩ := exists_pow_mul_mem_chartAlgFin_of_forall_place R ϖ hϖ K₀ F f⁻¹ hFD' g hgv
      exact ⟨k, ⟨_, hk⟩, rfl⟩

end AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] [IsCurveOver K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal)
    (hϖ𝔪 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔪 i) (hf𝔪 : ∀ i, jChartFin R F f ∈ 𝔪 i)
    (I : ι → Ideal ↥(chartAlgFin R F f))
    (hI : ∀ i (a : ↥(chartAlgFin R F f)), a ∈ I i ↔
      ∃ s : ↥(chartAlgFin R F f), s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {jChartFin R F f})
    (hne : ∀ i, I i ≠ ⊤)
    (htor : ∀ i (y : ↥(chartAlgFin R F f) ⧸ I i), algebraMap R (↥(chartAlgFin R F f) ⧸ I i) ϖ * y = 0 → y = 0)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i) :
    ∃ D_K : Divisor K₀ F, 0 ≤ D_K ∧ 0 < Divisor.degree D_K ∧
      (∀ v : Place K₀ F, f⁻¹ ∈ v.toValuationSubring → D_K v = 0) ∧
      ∀ n : ℕ,

        (∀ g : F, g ∈ lSpaceOn {v : Place K₀ F | f ∈ v.toValuationSubring} ((n : ℤ) • D_K) →
          ∃ k : ℕ, ∀ a ∈ (∏ i, I i) ^ n, ∃ b : ↥(chartAlgFin R F f),
            algebraMap R F ϖ ^ k * g * (a : F) = (b : F)) ∧

        (∀ z : ↥(chartAlgMid R F f), (z : F) ∈
          lSpaceOn ({v : Place K₀ F | f ∈ v.toValuationSubring} ∩ {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring})
            ((n : ℤ) • D_K)) ∧

        (∀ g : F, g ∈ lSpaceOn {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring} ((n : ℤ) • D_K) →
          ∃ (k : ℕ) (b : ↥(chartAlgInf R F f)), algebraMap R F ϖ ^ k * g = (b : F)) :=
  AlgebraicCurve.TwoChartIntegralModel.main R ϖ hϖ K₀ F f htf hFD hsep 𝔪 h𝔪 hϖ𝔪 hf𝔪 I hI hne htor hle

end S_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData (solution)
