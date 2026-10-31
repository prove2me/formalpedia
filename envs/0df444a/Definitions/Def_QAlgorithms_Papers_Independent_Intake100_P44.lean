-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P44
-- name    : QAlgorithms_Papers_Independent_Intake100_P44
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:27:11.385598+00:00
-- url     : https://prove2.me/theorems/263f61cb-8a87-4148-9f6f-45695862e88d
-- title:
--   Definitions for Banach embedding properties of non-commutative L^p-spaces
-- statement:
--   The objects the formalized statements of *Banach embedding properties of non-commutative L^p-spaces* (arXiv:math/0005150) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteBasic`: Finite basic sequences: linear independence and initial-segment projections bounded by lambda, the standard Banach basis-constant convention used on PDF pp.26–28 (Corollary 4.5). No normalization of the vectors is imposed.
--   - `finiteSuppressionUnconditional`: Suppression unconditionality: every coordinate projection has norm at most u on the span, PDF pp.26–28, in particular Corollary 4.5.
--   - `finiteUnconditional`: Complex unconditionality with unimodular multipliers, as defined on PDF p.2 and recalled in (3.1), p.15.
--   - `finiteDisjointnessBound`: The explicit cardinality bound in Lemma 4.10B and its remark, PDF pp.30–31. The natural floor is used only at positive eps in the theorem.
--   - `intervalLp`: The actual complex commutative Lp space on [0,1]. The extended exponent is finite and at least one in every use as a Banach space below.
--   - `isSign`: A sign function as an Lp class: the representative is ±1 almost everywhere, so a change on a null set is immaterial, PDF p.40, Lemma 6.4.
--   - `weaklyNull`: Weak convergence to zero in the Banach weak topology, tested against every bounded complex-linear functional, Definition 5.5, PDF p.37.
--   - `normalizedPartialSum`: The HRS normalized partial-sum norm, Definition 5.5, PDF p.37. Index 0 corresponds to the source's index 1. Its value at n=0 does not affect any limit at infinity; the source uses this expression for positive n.
--   - `banachSaksSequence`: Definition 5.5(a)(i), PDF p.37: weak-null is part of the definition, and ordinary Cesaro decay is required on every subsequence.
--   - `pBanachSaksSequence`: Definition 5.5(a)(ii), PDF p.37, formula (5.32). The eventual epsilon-bound is exactly limsup ≤ C, with one finite real C before every subsequence. This avoids a default-valued real limsup on an unbounded sequence. The definition is used for 1 < p < infinity in the paper.
--   - `strongPBanachSaksSequence`: Definition 5.5(a)(iii), PDF p.37: ordinary rate decay on every subsequence. No common convergence threshold over subsequences is demanded.
--   - `banachSaksProperty`: Definition 5.5(b), PDF p.37: every weakly null sequence has an HRS Banach–Saks subsequence. This is the weak-null version of the property.
--   - `pBanachSaksProperty`: Definition 5.5(b), PDF p.37, for the p-rate property.
--   - `strongPBanachSaksProperty`: Definition 5.5(b), PDF p.37, for the strong p-rate property.
-- source:
--   Banach embedding properties of non-commutative L^p-spaces, arXiv:math/0005150v1, https://arxiv.org/abs/math/0005150v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P30

/-!
Statements and concrete local interfaces for Haagerup–Rosenthal–Sukochev,
arXiv:math/0005150v1. The noncommutative constructions not yet available in
the pinned library are explicitly deferred in the accompanying HARD.md.
Definition 5.5 is encoded independently of any proposed noncommutative Lp model.
-/

noncomputable section

open scoped BigOperators ENNReal

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Next46.P30 (intervalMeasure)

namespace QAlgorithms.Papers.Independent.Intake100.P44

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Finite basic sequences: linear independence and initial-segment projections
bounded by lambda, the standard Banach basis-constant convention used on PDF
pp.26–28 (Corollary 4.5). No normalization of the vectors is imposed. -/
def finiteBasic {n : ℕ} (lambda : ℝ) (x : Fin n → E) : Prop :=
  LinearIndependent ℂ x ∧
    ∀ (a : Fin n → ℂ) (m : ℕ),
      ‖∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), a i • x i‖ ≤
        lambda * ‖∑ i : Fin n, a i • x i‖

/-- Suppression unconditionality: every coordinate projection has norm at most
u on the span, PDF pp.26–28, in particular Corollary 4.5. -/
def finiteSuppressionUnconditional {n : ℕ} (u : ℝ) (x : Fin n → E) : Prop :=
  ∀ (a : Fin n → ℂ) (s : Finset (Fin n)),
    ‖∑ i ∈ s, a i • x i‖ ≤ u * ‖∑ i : Fin n, a i • x i‖

/-- Complex unconditionality with unimodular multipliers, as defined on PDF
p.2 and recalled in (3.1), p.15. -/
def finiteUnconditional {n : ℕ} (u : ℝ) (x : Fin n → E) : Prop :=
  ∀ (a z : Fin n → ℂ), (∀ i, ‖z i‖ = 1) →
    ‖∑ i : Fin n, (z i * a i) • x i‖ ≤ u * ‖∑ i : Fin n, a i • x i‖

example (lambda : ℝ) (x : Fin 0 → E) : finiteBasic lambda x := by
  refine ⟨linearIndependent_empty_type, ?_⟩
  intro a m
  simp

example (u : ℝ) (x : Fin 0 → E) : finiteSuppressionUnconditional u x := by
  intro a s
  have hs : s = ∅ := by
    ext i
    exact Fin.elim0 i
  rw [hs]
  simp

example (u : ℝ) (x : Fin 0 → E) : finiteUnconditional u x := by
  intro a z hz
  simp

/-- The explicit cardinality bound in Lemma 4.10B and its remark, PDF pp.30–31.
The natural floor is used only at positive eps in the theorem. -/
def finiteDisjointnessBound (k : ℕ) (eps : ℝ) : ℕ :=
  k ^ (⌊eps⁻¹⌋₊ + 1)

example (eps : ℝ) : finiteDisjointnessBound 1 eps = 1 := by
  simp [finiteDisjointnessBound]

/-- The actual complex commutative Lp space on [0,1]. The extended exponent
is finite and at least one in every use as a Banach space below. -/
abbrev intervalLp (p : ℝ≥0∞) := MeasureTheory.Lp ℂ p intervalMeasure

/-- A sign function as an Lp class: the representative is ±1 almost everywhere,
so a change on a null set is immaterial, PDF p.40, Lemma 6.4. -/
def isSign {p : ℝ≥0∞} (f : intervalLp p) : Prop :=
  ∀ᵐ t ∂intervalMeasure, f t = (1 : ℂ) ∨ f t = (-1 : ℂ)

example : intervalMeasure Set.univ = 1 := by
  simp [intervalMeasure, Real.volume_Icc]

/-- Weak convergence to zero in the Banach weak topology, tested against every
bounded complex-linear functional, Definition 5.5, PDF p.37. -/
def weaklyNull (x : ℕ → E) : Prop :=
  ∀ phi : E →L[ℂ] ℂ, Tendsto (fun n => phi (x n)) atTop (nhds 0)

/-- The HRS normalized partial-sum norm, Definition 5.5, PDF p.37.
Index 0 corresponds to the source's index 1. Its value at n=0 does not affect
any limit at infinity; the source uses this expression for positive n. -/
def normalizedPartialSum (p : ℝ) (x : ℕ → E) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-1 / p) * ‖∑ j ∈ Finset.range n, x j‖

/-- Definition 5.5(a)(i), PDF p.37: weak-null is part of the definition, and
ordinary Cesaro decay is required on every subsequence. -/
def banachSaksSequence (x : ℕ → E) : Prop :=
  weaklyNull x ∧ ∀ s : ℕ → ℕ, StrictMono s →
    Tendsto (normalizedPartialSum 1 (fun j => x (s j))) atTop (nhds 0)

/-- Definition 5.5(a)(ii), PDF p.37, formula (5.32). The eventual epsilon-bound
is exactly limsup ≤ C, with one finite real C before every subsequence. This
avoids a default-valued real limsup on an unbounded sequence. The definition
is used for 1 < p < infinity in the paper. -/
def pBanachSaksSequence (p : ℝ) (x : ℕ → E) : Prop :=
  weaklyNull x ∧ ∃ C : ℝ, ∀ s : ℕ → ℕ, StrictMono s →
    ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n in atTop, normalizedPartialSum p (fun j => x (s j)) n ≤ C + eps

/-- Definition 5.5(a)(iii), PDF p.37: ordinary rate decay on every subsequence.
No common convergence threshold over subsequences is demanded. -/
def strongPBanachSaksSequence (p : ℝ) (x : ℕ → E) : Prop :=
  weaklyNull x ∧ ∀ s : ℕ → ℕ, StrictMono s →
    Tendsto (normalizedPartialSum p (fun j => x (s j))) atTop (nhds 0)

/-- Definition 5.5(b), PDF p.37: every weakly null sequence has an HRS
Banach–Saks subsequence. This is the weak-null version of the property. -/
def banachSaksProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ x : ℕ → E, weaklyNull x →
    ∃ s : ℕ → ℕ, StrictMono s ∧ banachSaksSequence (fun j => x (s j))

/-- Definition 5.5(b), PDF p.37, for the p-rate property. -/
def pBanachSaksProperty (p : ℝ)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ x : ℕ → E, weaklyNull x →
    ∃ s : ℕ → ℕ, StrictMono s ∧ pBanachSaksSequence p (fun j => x (s j))

/-- Definition 5.5(b), PDF p.37, for the strong p-rate property. -/
def strongPBanachSaksProperty (p : ℝ)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ x : ℕ → E, weaklyNull x →
    ∃ s : ℕ → ℕ, StrictMono s ∧ strongPBanachSaksSequence p (fun j => x (s j))

example : weaklyNull (fun _ : ℕ => (0 : E)) := by
  intro phi
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))

example (p : ℝ) (n : ℕ) : normalizedPartialSum p (fun _ : ℕ => (0 : E)) n = 0 := by
  simp [normalizedPartialSum]

example (p : ℝ) : strongPBanachSaksSequence p (fun _ : ℕ => (0 : E)) := by
  constructor
  · intro phi
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  · intro s hs
    change Tendsto (fun n : ℕ => normalizedPartialSum p (fun _ : ℕ => (0 : E)) n)
      atTop (nhds 0)
    simp only [normalizedPartialSum, Finset.sum_const_zero, norm_zero, mul_zero]
    exact tendsto_const_nhds

example (p : ℝ) : pBanachSaksSequence p (fun _ : ℕ => (0 : E)) := by
  constructor
  · intro phi
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  · refine ⟨0, ?_⟩
    intro s hs eps heps
    exact Filter.Eventually.of_forall (fun n => by
      simpa [normalizedPartialSum] using heps.le)

end QAlgorithms.Papers.Independent.Intake100.P44


