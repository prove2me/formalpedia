-- Prove2me | Definitions.Def_ArtinKPB012
-- name    : ArtinKPB012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:32:49.166211+00:00
-- url     : https://prove2.me/theorems/bc721107-9c8a-4d81-a150-e8139e6147af
-- title:
--   Definitions bundle ArtinKPB012 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 5 declarations of that development: 1 instance and 4 theorems.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X_Fourier`, `KP.X_L2`, `KP.X_Quot`.
--
--   **Imports.** It imports the bundle `ArtinKPB011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB015`; the proofs of `ArtinKP.N2.integrable_lift_pou` and `ArtinKP.X.X.dense_range_coreL2`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinKPB011

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

/-- A set meeting every orbit at most `m` times (with multiplicity) carries at most `m` times the
quotient integral of an invariant function. -/
theorem setLIntegral_le_mul_lintegral_pou {η : α → ℝ≥0∞} (hη : IsPOU G η)
    {f : α → ℝ≥0∞} (hf : Measurable f) (hinv : ∀ (g : G) (a : α), f (g • a) = f a)
    {B : Set α} (hB : MeasurableSet B) (m : ℝ≥0∞)
    (hm : ∀ a, ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ m) :
    ∫⁻ a in B, f a ∂μ ≤ m * ∫⁻ a, f a * η a ∂μ := by
  have h1 : Measurable (B.indicator f) := hf.indicator hB
  have h := lintegral_tsum_swap (G := G) (μ := μ) h1 hη.measurable
  simp only [hη.tsum_eq, mul_one] at h
  have hfη : Measurable fun a => f a * η a := hf.mul hη.measurable
  rw [← lintegral_indicator hB, h, ← lintegral_const_mul m hfη]
  · refine lintegral_mono fun a => ?_
    have : ∑' g : G, B.indicator f (g • a) = f a * ∑' g : G,
        B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun g => ?_
      by_cases hg : g • a ∈ B
      · simp [hg, hinv]
      · simp [hg]
    rw [this]
    calc η a * (f a * ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a))
        ≤ η a * (f a * m) := by gcongr; exact hm a
      _ = m * (f a * η a) := by ring

/-! ### The quotient measure -/

/-! ### Unfolding -/

/-! ### Multiplicity and existence of partitions of unity -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_L2
/-! # WP-X, file 7: `L²` of the quotient and local restriction maps (abstract)

For a partition of unity `η` and a measurable set `B` meeting each orbit at most `m < ∞` times,
pulling back and restricting is a bounded operator
`restrictL2 : L²(G \ α) →L[ℂ] L²(B, μ)` of norm `≤ √m`.  Every functional
`u ↦ ∫_B conj ψ · u` with `ψ ∈ L²(B)` is therefore continuous on `L²(G \ α)`
(`pairingL2`).  This is the continuity of Fourier-coefficient functionals (MATH (C6)).
-/

open scoped ENNReal ComplexConjugate InnerProductSpace
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {η : α → ℝ≥0∞}

lemma stronglyMeasurable_liftQ (u : Lp ℂ 2 (quotMeasure G η μ)) :
    StronglyMeasurable (liftQ u) :=
  (Lp.stronglyMeasurable u).comp_measurable measurable_mk

/-- The `L²(B)`-norm of the pull-back is at most `√m` times the norm on the quotient. -/
theorem eLpNorm_liftQ_restrict_le (hη : IsPOU G η) {B : Set α} (hB : MeasurableSet B)
    (m : ℝ≥0∞) (hm : ∀ a, ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ m)
    (u : Lp ℂ 2 (quotMeasure G η μ)) :
    eLpNorm (liftQ u) 2 (μ.restrict B) ≤ m ^ (1 / 2 : ℝ) * eLpNorm u 2 (quotMeasure G η μ) := by
  have hu : Measurable (u : Quotient (MulAction.orbitRel G α) → ℂ) :=
    (Lp.stronglyMeasurable u).measurable
  have hF : Measurable fun q : Quotient (MulAction.orbitRel G α) => ‖u q‖ₑ ^ (2 : ℝ) :=
    hu.enorm.pow_const _
  have hFc : Measurable fun a : α => ‖u (Quotient.mk (MulAction.orbitRel G α) a)‖ₑ ^ (2 : ℝ) :=
    hF.comp measurable_mk
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have key := setLIntegral_le_mul_lintegral_pou (μ := μ) hη hFc
    (fun g a => by rw [mk_smul]) hB m hm
  rw [← lintegral_quotMeasure hη.measurable hF] at key
  calc (∫⁻ a in B, ‖liftQ u a‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
      ≤ (m * ∫⁻ q, ‖u q‖ₑ ^ (2 : ℝ) ∂quotMeasure G η μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)

lemma memLp_liftQ_restrict (hη : IsPOU G η) {B : Set α} (hB : MeasurableSet B)
    {m : ℝ≥0∞} (hmtop : m ≠ ⊤)
    (hm : ∀ a, ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ m)
    (u : Lp ℂ 2 (quotMeasure G η μ)) : MemLp (liftQ u) 2 (μ.restrict B) :=
  ⟨(stronglyMeasurable_liftQ u).aestronglyMeasurable,
    (eLpNorm_liftQ_restrict_le hη hB m hm u).trans_lt
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hmtop)
        (Lp.eLpNorm_lt_top u))⟩

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
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

instance instIsFiniteMeasureXRestrictVolBox (n : ℕ) : IsFiniteMeasure ((X.vol F).restrict (X.box n)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact X.vol_box_lt_top n⟩

end

end ArtinKP.X
end


