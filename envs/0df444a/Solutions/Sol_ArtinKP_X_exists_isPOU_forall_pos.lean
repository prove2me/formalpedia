-- Prove2me | solution 1 for ArtinKP.X.exists_isPOU_forall_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:21:14.323546+00:00
-- url     : https://prove2.me/submissions/1bcb1152-1dcd-4912-8220-c536242abc58

import Mathlib
import Definitions.Def_ArtinKPB007
import Definitions.Def_ArtinKPB008

section
-- module Solutions.Artin.KP.X_Quot
/-! # WP-X, file 5: quotient measures and unfolding without fundamental domains

Abstract setting: a countable group `G` acting measurably on `(α, μ)` and preserving `μ`.
A *partition of unity* for the action is a measurable `η : α → ℝ≥0∞` with
`∑_g η (g • a) = 1` for all `a` (the indicator of a strict fundamental domain is one; in a
properly discontinuous situation an everywhere positive one always exists, `exists_isPOU`).
The quotient measure on `G \ α` is the push-forward of `η μ`; it does not depend on `η`
(`quotMeasure_eq`).  Everything is Tonelli:

* `lintegral_tsum_swap` : `∫ φ · Σ_g ψ∘g = ∫ ψ · Σ_g φ∘g`;
* `lintegral_mul_pou_eq` : independence of `η`;
* `lintegral_autom_mul_eq` : unfolding `∫_{G\α} (Σ_{H\G} f∘γ) u = ∫_{H\α} f u`;
* `setLIntegral_le_mul_lintegral_pou` : a set meeting each orbit at most `m` times has
  `∫_B f ≤ m ∫_{G\α} f`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

lemma tsum_smul_comp_smul (ψ : α → ℝ≥0∞) (g₀ : G) (a : α) :
    ∑' g : G, ψ (g • g₀ • a) = ∑' g : G, ψ (g • a) := by
  have := (Equiv.mulRight g₀).tsum_eq (fun g : G => ψ (g • a))
  simpa [mul_smul] using this

/-! ### The quotient measure -/

/-! ### Unfolding -/

/-! ### Multiplicity and existence of partitions of unity -/

/-- If the return set of `B` is contained in the finite set `R`, every orbit meets `B` at most
`R.card` times. -/
theorem tsum_indicator_le_card {B : Set α} (R : Finset G)
    (hR : ∀ g : G, (∃ a ∈ B, g • a ∈ B) → g ∈ R) (a : α) :
    ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ R.card := by
  classical
  by_cases h : ∃ g₀ : G, g₀ • a ∈ B
  · obtain ⟨g₀, hg₀⟩ := h
    have hzero : ∀ g ∉ R.image (· * g₀), B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) = 0 := by
      intro g hg
      refine indicator_of_notMem (fun hgB => hg ?_) _
      refine Finset.mem_image.mpr ⟨g * g₀⁻¹, hR _ ⟨g₀ • a, hg₀, ?_⟩, by simp⟩
      rwa [← mul_smul, inv_mul_cancel_right]
    rw [tsum_eq_sum hzero]
    calc ∑ g ∈ R.image (· * g₀), B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a)
        ≤ ∑ _g ∈ R.image (· * g₀), (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun g _ => by by_cases hg : g • a ∈ B <;> simp [hg]
      _ = (R.image (· * g₀)).card := by simp
      _ ≤ R.card := by exact_mod_cast Finset.card_image_le
  · push Not at h
    have : ∀ g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) = 0 := fun g =>
      indicator_of_notMem (h g) _
    simp [this]

/-- **Existence of a partition of unity** for an action with a countable measurable cover by sets
with finite return sets (proper discontinuity). The partition is everywhere positive. -/
theorem exists_isPOU (U : ℕ → Set α) (hU : ∀ n, MeasurableSet (U n)) (hcov : ∀ a, ∃ n, a ∈ U n)
    (hfin : ∀ n, ∃ R : Finset G, ∀ g : G, (∃ a ∈ U n, g • a ∈ U n) → g ∈ R) :
    ∃ η : α → ℝ≥0∞, IsPOU G η ∧ ∀ a, 0 < η a := by
  choose R hR using hfin
  let w : ℕ → ℝ≥0∞ := fun n => (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((R n).card + 1 : ℝ≥0∞)⁻¹
  have hw0 : ∀ n, w n ≠ 0 := fun n => by
    refine mul_ne_zero (pow_ne_zero _ (by simp)) (ENNReal.inv_ne_zero.mpr ?_)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩
  let h : α → ℝ≥0∞ := fun a => ∑' n, w n * (U n).indicator (fun _ => (1 : ℝ≥0∞)) a
  have hmeas : Measurable h :=
    Measurable.ennreal_tsum fun n => measurable_const.mul (measurable_const.indicator (hU n))
  let Hs : α → ℝ≥0∞ := fun a => ∑' g : G, h (g • a)
  have hHmeas : Measurable Hs :=
    Measurable.ennreal_tsum fun g => hmeas.comp (measurable_const_smul g)
  have hpos : ∀ a, 0 < h a := by
    intro a
    obtain ⟨n, hn⟩ := hcov a
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum n)
    simp [hn, pos_iff_ne_zero, hw0 n]
  have hHle : ∀ a, Hs a ≤ 1 := by
    intro a
    change ∑' g : G, ∑' n, w n * (U n).indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ 1
    rw [ENNReal.tsum_comm]
    calc ∑' n, ∑' g : G, w n * (U n).indicator (fun _ => (1 : ℝ≥0∞)) (g • a)
        ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          rw [ENNReal.tsum_mul_left]
          calc w n * ∑' g : G, (U n).indicator (fun _ => (1 : ℝ≥0∞)) (g • a)
              ≤ w n * (R n).card := by gcongr; exact tsum_indicator_le_card (R n) (hR n) a
            _ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) * (((R n).card + 1 : ℝ≥0∞)⁻¹ * ((R n).card + 1)) := by
                rw [mul_assoc]; gcongr; exact le_self_add
            _ = (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
                rw [ENNReal.inv_mul_cancel (by simp)
                  (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩), mul_one]
      _ = 1 := by
          simp_rw [pow_succ]
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
          exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hHpos : ∀ a, Hs a ≠ 0 := fun a => by
    have h1 : h ((1 : G) • a) ≤ Hs a := ENNReal.le_tsum (f := fun g : G => h (g • a)) 1
    rw [one_smul] at h1
    exact (lt_of_lt_of_le (hpos a) h1).ne'
  have hHtop : ∀ a, Hs a ≠ ⊤ := fun a => ((hHle a).trans_lt ENNReal.one_lt_top).ne
  have hHinv : ∀ (g : G) (a : α), Hs (g • a) = Hs a := fun g a => tsum_smul_comp_smul h g a
  refine ⟨fun a => h a / Hs a, ⟨hmeas.div hHmeas, fun a => ?_⟩, fun a => ?_⟩
  · simp_rw [hHinv, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel (hHpos a) (hHtop a)
  · exact ENNReal.div_pos (hpos a).ne' (hHtop a)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

lemma X.exists_mem_box (P : X F) : ∃ n : ℕ, P ∈ X.box n := by
  have h1 : ∃ n : ℕ, ∀ w, ‖P.x w‖ ≤ n ∧ P.v w ≤ n ∧ 1 / P.v w ≤ n := by
    obtain ⟨n, hn⟩ := exists_nat_ge
      (∑ w : InfinitePlace F, (‖P.x w‖ + P.v w + 1 / P.v w))
    refine ⟨n, fun w => ?_⟩
    have hnn : ∀ w' ∈ (Finset.univ : Finset (InfinitePlace F)),
        0 ≤ ‖P.x w'‖ + P.v w' + 1 / P.v w' := fun w' _ => by
      have := P.v_pos w'
      positivity
    have := (Finset.single_le_sum hnn (Finset.mem_univ w)).trans hn
    have hv := P.v_pos w
    have h3 : 0 < 1 / P.v w := by positivity
    have h4 := norm_nonneg (P.x w)
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨n, hn⟩ := h1
  refine ⟨n, fun w => ⟨(hn w).1, ?_, ?_⟩⟩
  · have hv := P.v_pos w
    have h3 := (hn w).2.2
    change 1 / ((n : ℝ) + 1) ≤ P.v w
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hv] at h3
    nlinarith
  · have := (hn w).2.1
    change P.v w ≤ (n : ℝ) + 1
    linarith

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-- Every subgroup of `SL(2,𝓞_F)` has an everywhere positive partition of unity on `X`. -/
theorem exists_isPOU_forall_pos_oai (Γ : Subgroup (SL(2, 𝓞 F))) :
    ∃ η : X F → ℝ≥0∞, IsPOU Γ η ∧ ∀ P, 0 < η P := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  classical
  refine exists_isPOU (G := Γ) (fun n => (X.box n : Set (X F))) X.measurableSet_box
    X.exists_mem_box fun n => ?_
  have hfin := finite_return_box (F := F) n
  have hfin' : {γ : Γ | ∃ P ∈ (X.box n : Set (X F)), γ • P ∈ (X.box n : Set (X F))}.Finite :=
    hfin.preimage (f := fun γ : Γ => (γ : SL(2, 𝓞 F))) Subtype.val_injective.injOn
  exact ⟨hfin'.toFinset, fun γ hγ => hfin'.mem_toFinset.mpr hγ⟩

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.exists_isPOU_forall_pos_oai.{u_1} := @ArtinKP.X.exists_isPOU_forall_pos_oai.{u_1}
