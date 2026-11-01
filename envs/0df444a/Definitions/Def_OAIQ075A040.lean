-- Prove2me | Definitions.Def_OAIQ075A040
-- name    : OAIQ075A040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T10:26:17.168641+00:00
-- url     : https://prove2.me/theorems/d2242a14-2d20-4c93-bd14-9bd5c58a8585
-- title:
--   Definitions bundle OAIQ075A040 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonSimilarity_Tracial_SourceMomentConstruction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceMomentConstruction.lean), [`KadisonSimilarity_Tracial_SourceMomentSequence`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceMomentSequence.lean), [`KadisonSimilarity_Tracial_SourceQuotientMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceQuotientMoments.lean), [`KadisonSimilarity_Tracial_SourceUnitaryMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceUnitaryMoments.lean).
--
--   **Imports.** It imports the bundle `OAIQ075A039` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A041`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A039

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceMomentConstruction
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Maximal partial unitaries for ambient moments, ordered inside the source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open Filter Topology
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

attribute [local instance] OAI.KadisonSimilarity.momentSourceClosed
include hfactor hdiff hirr in
/-- Partial unitaries of every trace below one satisfy prescribed ambient
moment bounds. The maximality argument is carried out in the source. -/
theorem exists_source_partial_unitary_moments {I : Type*} [Fintype I]
    (F : I → M.toStarSubalgebra)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, υ.trace (F i) = 0)
    {K N : ℕ} (hK : 0 < K) {δ T : ℝ} (hδ : 0 < δ) (hT0 : 0 ≤ T) (hT : T < 1) :
    ∃ v : PartialUnitary R.toStarSubalgebra,
      (υ.trace (coordinateInclusion hRM v.support)).re = T ∧
      MomentBound F (vectorPositiveFunctional M υ.vector) (K := K) (N := N)
        (expBudget δ (patchRate N T)) (SourcePartialUnitary.map (coordinateInclusion hRM) v) := by
  let φ := coordinateInclusion hRM
  let τR := vectorPositiveFunctional R υ.vector
  let τM := vectorPositiveFunctional M υ.vector
  have htrR : ∀ a b, τR (a * b) = τR (b * a) := (restrictedTrace υ hRM).trace_mul_comm
  have h1R : τR 1 = 1 := vectorPositiveFunctional_one R υ.vector υ.norm_vector
  have hfR (a : R.toStarSubalgebra) (ha : τR (star a * a) = 0) : a = 0 := by
    apply (restrictedTrace υ hRM).separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace (restrictedTrace υ hRM) a a).trans ha)
  let b := expBudget δ (patchRate N T)
  let P : PartialUnitary R.toStarSubalgebra → Prop := fun v =>
    (τR v.support).re ≤ T ∧ MomentBound F τM (K := K) (N := N) b (SourcePartialUnitary.map φ v)
  have h0 : P 0 := by
    constructor
    · simpa only [PartialUnitary.support_zero, map_zero, Complex.zero_re] using hT0
    · rw [SourcePartialUnitary.map_zero]
      exact momentBound_zero F τM (by dsimp only [b]; rw [expBudget_zero])
  have hclosed : ∀ (a : ℕ → PartialUnitary R.toStarSubalgebra) (s : PartialUnitary R.toStarSubalgebra),
      Monotone a → (∀ n, P (a n)) →
      GNSTendsto τR (fun n => (a n : R.toStarSubalgebra)) atTop (s : R.toStarSubalgebra) → P s := by
    intro a s _ha hPa ht
    constructor
    · have hs := (ht.star τR htrR).mul τR htrR ht 1
        (fun n => by simpa only [norm_star] using (a n).norm_le_one)
      have htrace := (Complex.continuous_re.tendsto _).comp (trace_tendsto_of_gns τR h1R hs)
      exact le_of_tendsto htrace (Filter.Eventually.of_forall (fun n => (hPa n).1))
    · exact source_momentBound_limit υ hRM F ht
        (expBudget_continuous δ _).continuousAt (fun n => (hPa n).2)
  obtain ⟨v, hv⟩ := PartialUnitary.maximal_of_sequentially_closed
    (concretePredualEquiv R) τR (HochschildSakai.mul_hasPreadjoint (concretePredualEquiv R))
    (vectorPositiveFunctional_normal R υ.vector) htrR hfR P h0 hclosed
  have hs0 : 0 ≤ (τR v.support).re := (τR.map_nonneg v.support_proj.nonneg).1
  have hb : 0 ≤ b ((τR v.support).re) := expBudget_nonneg hδ.le
    ((by norm_num : (0 : ℝ) ≤ 1).trans (patchRate_ge_one hT)) hs0
  refine ⟨v, ?_, hv.1.2⟩
  by_contra hne
  have hsT : (τR v.support).re < T := lt_of_le_of_ne hv.1.1 hne
  obtain ⟨w, horth, hwpos, hwt, hwm⟩ := exists_source_incremental_patch υ hRM hfactor hdiff hirr
    F hF hFτ hK v hb hv.1.2 (hsT.trans hT)
    (patchTolerance_pos hδ (Nat.cast_nonneg N)) (sub_pos.mpr hsT)
  change 0 < (τR w.support).re at hwpos
  change (τR w.support).re < T - (τR v.support).re at hwt
  let z := v.orthogonalSum w horth
  have hzs : (τR z.support).re = (τR v.support).re + (τR w.support).re := by
    rw [PartialUnitary.support_orthogonalSum, map_add, Complex.add_re]
  have hz : P z := by
    constructor
    · rw [hzs]; linarith
    · intro a ha
      have hh := hwm a ha
      have hr := expBudget_patch_bound hδ.le (Nat.cast_nonneg N) hT hs0 hv.1.1 hwpos.le
      change ‖τM (mixedEval F (SourcePartialUnitary.map φ z) a.1 a.2.val)‖ ≤
        b ((τR z.support).re)
      rw [hzs]
      exact hh.trans hr
  have hvz : v ≤ z := v.le_orthogonalSum w horth
  have hzv : z ≤ v := hv.2 hz hvz
  have he : z = v := le_antisymm hzv hvz
  rw [he] at hzs
  linarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceUnitaryMoments
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completing the source partial unitary controls every prescribed finite
family of ambient mixed moments. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

include hfactor hdiff hirr in
/-- A unitary in the source makes any finite family of centered ambient
mixed moments arbitrarily small. -/
theorem exists_source_unitary_small_moments {I : Type*} [Fintype I]
    (F : I → M.toStarSubalgebra)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, υ.trace (F i) = 0)
    {K N : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : unitary R.toStarSubalgebra, ∀ a : BoundedWord I K N,
      admissibleTail a.2.val →
        ‖υ.trace (mixedEval F (SourcePartialUnitary.map (coordinateInclusion hRM)
          (asPartialUnitary u)) a.1 a.2.val)‖ < ε := by
  let φ := coordinateInclusion hRM
  let τ := vectorPositiveFunctional M υ.vector
  let t : ℝ := min (1 / 2) (ε / (4 * ((N : ℝ) + 1)))
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htε : t ≤ ε / (4 * ((N : ℝ) + 1)) := min_le_right _ _
  let T : ℝ := 1 - t
  have hT0 : 0 ≤ T := by dsimp only [T]; linarith
  have hT : T < 1 := by dsimp only [T]; linarith
  let C := patchRate (N : ℝ) T
  let δ := ε / (4 * Real.exp (C * T))
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) (Real.exp_pos _))
  obtain ⟨v, hvs, hvm⟩ := exists_source_partial_unitary_moments υ hRM hfactor hdiff hirr
    F hF hFτ hK (N := N) hδ hT0 hT
  let w := ofCornerUnitary (1 - v.support) v.support_proj.one_sub 1
  have hw : w.support = 1 - v.support := ofCornerUnitary_support ..
  have horth : v.support * w.support = 0 := by
    rw [hw, mul_sub, mul_one, v.support_proj.isIdempotentElem.eq, sub_self]
  let V := SourcePartialUnitary.map φ v
  let W := SourcePartialUnitary.map φ w
  have horthM : V.support * W.support = 0 := by
    rw [SourcePartialUnitary.support_map, SourcePartialUnitary.support_map,
      ← map_mul, horth, map_zero]
  have hwt : (τ W.support).re = t := by
    rw [SourcePartialUnitary.support_map, hw, map_sub, map_one]
    change (υ.trace (1 - φ v.support)).re = t
    rw [trace_sub, υ.trace_one, Complex.sub_re, Complex.one_re, hvs]
    dsimp only [T]
    ring
  have he : asPartialUnitary (unitaryCompletion v) = v.orthogonalSum w horth := by
    apply HochschildComparison.PartialUnitary.ext
    rfl
  refine ⟨unitaryCompletion v, fun a ha => ?_⟩
  rw [he, SourcePartialUnitary.map_orthogonalSum]
  change ‖τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val)‖ < ε
  have herr := trace_mixedEval_patch τ υ.trace_mul_comm F V W horthM hF a.1 a.2.val
  rw [hwt] at herr
  have hvb := hvm a ha
  change ‖τ (mixedEval F V a.1 a.2.val)‖ ≤
    expBudget δ (patchRate N T) (υ.trace (φ v.support)).re at hvb
  rw [hvs] at hvb
  have hb : expBudget δ (patchRate N T) T ≤ ε / 4 := by
    change δ * (Real.exp (C * T) - 1) ≤ ε / 4
    have heq : δ * Real.exp (C * T) = ε / 4 := by dsimp only [δ]; field_simp
    nlinarith
  have hn : (a.2.val.length : ℝ) * t ≤ ε / 4 := by
    have hnN : (a.2.val.length : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast (a.2.property.trans (Nat.le_succ N))
    have hnt := mul_le_mul_of_nonneg_right hnN ht0.le
    have hpos : 0 < 4 * ((N : ℝ) + 1) := by positivity
    have hbound := (le_div_iff₀ hpos).mp htε
    nlinarith
  have htotal : ‖τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val)‖ ≤ ε / 2 := by
    calc
      _ ≤ ‖τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val) -
          τ (mixedEval F V a.1 a.2.val)‖ + ‖τ (mixedEval F V a.1 a.2.val)‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          (τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val) - τ (mixedEval F V a.1 a.2.val))
          (τ (mixedEval F V a.1 a.2.val))
      _ ≤ ε / 4 + ε / 4 := add_le_add (herr.trans hn) (hvb.trans hb)
      _ = _ := by ring
  exact htotal.trans_lt (by linarith)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceMomentSequence
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A diagonal sequence of source unitaries annihilates every fixed finite
mixed word in a countable family of ambient coefficient sequences. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open Filter Topology
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

include hfactor hdiff hirr in
theorem exists_source_small_moment_sequence
    (F : ℕ → ℕ → M.toStarSubalgebra)
    (hF : ∀ n i, ‖F n i‖ ≤ 1) (hFτ : ∀ n i, υ.trace (F n i) = 0) :
    ∃ u : ℕ → unitary R.toStarSubalgebra, ∀ m K N : ℕ,
      ∀ a : BoundedWord (Fin m) K N, admissibleTail a.2.val →
      Tendsto (fun n => υ.trace (mixedEval (fun i : Fin m => F n i.val)
        (SourcePartialUnitary.map (coordinateInclusion hRM) (asPartialUnitary (u n)))
        a.1 a.2.val)) atTop (𝓝 0) := by
  classical
  have hex (n : ℕ) := exists_source_unitary_small_moments υ hRM hfactor hdiff hirr
    (fun i : Fin n => F n i.val) (fun i => hF n i.val) (fun i => hFτ n i.val)
    (Nat.zero_lt_succ n) (N := n) (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose u hu using hex
  refine ⟨u, fun m K N a ha => ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨b, hb⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop (max b (max m (max K N)))] with n hn
  have hbn : b ≤ n := (le_max_left _ _).trans hn
  have hmn : m ≤ n := (le_max_left m (max K N)).trans ((le_max_right b _).trans hn)
  have hKn : K ≤ n := (le_max_left K N).trans ((le_max_right m _).trans ((le_max_right b _).trans hn))
  have hNn : N ≤ n := (le_max_right K N).trans ((le_max_right m _).trans ((le_max_right b _).trans hn))
  let f : Fin m → Fin n := fun i => ⟨i.val, i.isLt.trans_le hmn⟩
  let g : Fin K → Fin (n + 1) := fun i => ⟨i.val, i.isLt.trans_le (hKn.trans (Nat.le_succ n))⟩
  let a' : BoundedWord (Fin n) (n + 1) n :=
    (a.1.map f, ⟨a.2.val.map (mapAtom f g), by simpa using a.2.property.trans hNn⟩)
  have htest := hu n a' (admissibleTail_map f g a.2.val ha)
  change ‖υ.trace (mixedEval (fun i : Fin n => F n i.val)
    (SourcePartialUnitary.map (coordinateInclusion hRM) (asPartialUnitary (u n)))
    (a.1.map f) (a.2.val.map (mapAtom f g)))‖ < _ at htest
  rw [mixedEval_map _ f g (fun _ => rfl)] at htest
  have hFcomp : (fun i : Fin n => F n i.val) ∘ f = (fun i : Fin m => F n i.val) := rfl
  rw [hFcomp] at htest
  have hne : 1 / ((n : ℝ) + 1) < ε := by
    have hbR : (b : ℝ) ≤ n := by exact_mod_cast hbn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply (div_lt_iff₀ hpos).mpr
    have hh := (div_lt_iff₀ hε).mp hb
    nlinarith
  simpa only [dist_zero_right] using htest.trans hne

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceQuotientMoments
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing ultrapower moments produced by a sequence of source unitaries. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance quotientMomentAmbientClosed_r8577bc_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.quotientMomentSourceClosed
include hfactor hdiff hirr in
theorem exists_centered_source_moment_sequence
    (A : ℕ → (ℕ →ᵇ M.toStarSubalgebra)) (hA : ∀ i n, ‖A i n‖ ≤ 1) :
    ∃ u : ℕ → unitary R.toStarSubalgebra, ∀ m K N : ℕ,
      ∀ a : BoundedWord (Fin m) K N, admissibleTail a.2.val →
      Tendsto (fun n => (vectorPositiveFunctional M υ.vector) (mixedEval
        (fun i : Fin m => (1 / 2 : ℂ) • (A i.val n - υ.trace (A i.val n) • 1))
        (asPartialUnitary (mapUnitary (coordinateInclusion hRM) (u n))) a.1 a.2.val))
        atTop (𝓝 0) := by
  let τ := vectorPositiveFunctional M υ.vector
  let F : ℕ → ℕ → M.toStarSubalgebra := fun n i => (1 / 2 : ℂ) • (A i n - τ (A i n) • 1)
  obtain ⟨u, hu⟩ := exists_source_small_moment_sequence υ hRM hfactor hdiff hirr F
    (fun n i => norm_centered_half τ υ.trace_one (A i n) (hA i n))
    (fun n i => trace_centered_half τ υ.trace_one (A i n))
  refine ⟨u, ?_⟩
  intro m K N a ha
  have h := hu m K N a ha
  simp only [source_map_asPartialUnitary] at h
  exact h

include hfactor hdiff hirr in
/-- A sequence from the source annihilates all fixed finite quotient words
in a countable family of centered ambient bounded sequences. -/
theorem exists_source_quotient_unitary_moments
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (A : ℕ → (ℕ →ᵇ M.toStarSubalgebra)) (hA : ∀ i n, ‖A i n‖ ≤ 1) :
    ∃ u : ℕ → unitary R.toStarSubalgebra,
      FiniteQuotientMoments (B := M.toStarSubalgebra) (vectorPositiveFunctional M υ.vector) υ.trace_one ω υ.trace_mul_comm
        A (fun n => mapUnitary (coordinateInclusion hRM) (u n)) := by
  obtain ⟨u, hu⟩ := exists_centered_source_moment_sequence υ hRM hfactor hdiff hirr A hA
  exact ⟨u, finiteQuotientMoments_of_limits (B := M.toStarSubalgebra) (vectorPositiveFunctional M υ.vector)
    υ.trace_one ω υ.trace_mul_comm hω A
    (fun n => mapUnitary (coordinateInclusion hRM) (u n)) hu⟩

end KadisonSimilarity

end

end OAI
end


