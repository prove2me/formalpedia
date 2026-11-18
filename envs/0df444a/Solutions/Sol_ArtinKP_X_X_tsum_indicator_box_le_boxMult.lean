-- Prove2me | solution 1 for ArtinKP.X.X.tsum_indicator_box_le_boxMult
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:21:35.818643+00:00
-- url     : https://prove2.me/submissions/335220a8-5b30-46bd-a371-a8d753b1958b

import Mathlib
import Definitions.Def_ArtinKPB007

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

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
/-! # WP-X, file 9: local restriction and coefficient functionals on `L²(Γ\X)`

* `X.vol_box_lt_top`: boxes have finite measure;
* `X.restrictBox Γ n : L²(Γ\X) →L[ℂ] L²(box n)`, bounded;
* `X.coeffFunctional Γ n ψ … : L²(Γ\X) →L[ℂ] ℂ`, `u ↦ ∫_{box n} conj ψ · u`, for bounded measurable
  `ψ`.  The Fourier-coefficient functional `ℓ_{ν,φ}` of MATH (C6) is the case
  `ψ(P) = 1_D(x) · conj(e_∞(-ν x) φ(v))` with `D` a fundamental set of the translation lattice
  and `supp φ` compact (so that `D × supp φ` lies in a box).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma X.tsum_indicator_box_le_boxMult_oai (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (P : X F) :
    ∑' γ : Γ, (X.box n : Set (X F)).indicator (fun _ => (1 : ℝ≥0∞)) (γ • P) ≤ (X.boxMult Γ n : ℝ≥0∞) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  tsum_indicator_le_card _ (fun γ hγ => (Set.Finite.mem_toFinset _).mpr hγ) P

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.tsum_indicator_box_le_boxMult_oai.{u_1} := @ArtinKP.X.X.tsum_indicator_box_le_boxMult_oai.{u_1}
