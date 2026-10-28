-- Prove2me | Definitions.Def_OAIQ9Tr000
-- name    : OAIQ9Tr000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T09:49:07.970959+00:00
-- url     : https://prove2.me/theorems/fe4c2cdb-de78-4ea9-8285-ef4020ffa147
-- title:
--   Definitions bundle OAIQ9Tr000 of the split of OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 719 declarations of OpenAI's Lean: 489 definitions, 15 inductive types or structures, 26 instances and 189 theorems. The definitions and types are `OAI.TraceReconstruction.ApproximatesTrace`, `OAI.TraceReconstruction.BinaryWindowLabels`, `OAI.TraceReconstruction.BinaryWindowLabels.allowed`, `OAI.TraceReconstruction.BinaryWindowLabels.central`, `OAI.TraceReconstruction.BinaryWindowLabels.close`, `OAI.TraceReconstruction.BinaryWindowLabels.distinct`, `OAI.TraceReconstruction.BoundedMarks`, `OAI.TraceReconstruction.BoundedTrace`, `OAI.TraceReconstruction.CentralMotifSupport`, `OAI.TraceReconstruction.ClippedOracle`, `OAI.TraceReconstruction.ClippedOracle.prod`, `OAI.TraceReconstruction.ClippedOracle.sigma`, `OAI.TraceReconstruction.ClippedOracle.trivial`, `OAI.TraceReconstruction.ClippedOracle.weaken`, `OAI.TraceReconstruction.CoefficientShape`, `OAI.TraceReconstruction.CoefficientShape.Admissible`, `OAI.TraceReconstruction.CoefficientShape.Choice`, `OAI.TraceReconstruction.CoefficientShape.eval`, `OAI.TraceReconstruction.CoefficientShape.termTree`, `OAI.TraceReconstruction.CoefficientShape.weight`, `OAI.TraceReconstruction.ConcreteLevelPair`, `OAI.TraceReconstruction.ConcreteLevelPair.oracle`, `OAI.TraceReconstruction.DegreeForcedRole`, `OAI.TraceReconstruction.DegreeForcedRole.encoding`, `OAI.TraceReconstruction.DegreeForcedRole.shape`, `OAI.TraceReconstruction.DegreeForcedShape`, `OAI.TraceReconstruction.DegreeForcedShape.forced`, `OAI.TraceReconstruction.DegreeLeafSubset`, `OAI.TraceReconstruction.EmissionOutcome`, `OAI.TraceReconstruction.EmissionSlot`, `OAI.TraceReconstruction.FiniteLaw`, `OAI.TraceReconstruction.FiniteLaw.Associated`, `OAI.TraceReconstruction.FiniteLaw.affinity`, `OAI.TraceReconstruction.FiniteLaw.bind`, `OAI.TraceReconstruction.FiniteLaw.commonClipEvent`, `OAI.TraceReconstruction.FiniteLaw.commonPart`, `OAI.TraceReconstruction.FiniteLaw.condition`, `OAI.TraceReconstruction.FiniteLaw.coordinateProduct`, `OAI.TraceReconstruction.FiniteLaw.dependentProduct`, `OAI.TraceReconstruction.FiniteLaw.evenMomentSq` and 464 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/TraceReconstruction, in whole or in part: `TraceReconstruction_Amplification`, `TraceReconstruction_Anchors`, `TraceReconstruction_Binomial`, `TraceReconstruction_Differences`, `TraceReconstruction_Energy`, `TraceReconstruction_ErrorRates`, `TraceReconstruction_FiniteLaw`, `TraceReconstruction_Induction`, `TraceReconstruction_InitialDensity`, `TraceReconstruction_InitialMoments`, `TraceReconstruction_InitialOracle`, `TraceReconstruction_InitialOverlap`, `TraceReconstruction_InitialRates`, `TraceReconstruction_Kernels`, `TraceReconstruction_Layout`, `TraceReconstruction_LayoutRates`, `TraceReconstruction_LeafOracle`, `TraceReconstruction_Metadata`, `TraceReconstruction_Model`, `TraceReconstruction_Oracles`, `TraceReconstruction_Parity`, `TraceReconstruction_Patterns`, `TraceReconstruction_Propagation`, `TraceReconstruction_Ranks`, `TraceReconstruction_Restoration`, `TraceReconstruction_Scales`, `TraceReconstruction_Shapes`, `TraceReconstruction_Simulation`, `TraceReconstruction_SourceOracle`, `TraceReconstruction_Testing`.
--
--   **Imports.** It imports the published bundle `Def_TraceReconstruction`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ9Tr002`; the statements `OAI.TraceReconstruction.actual_initial_oracles`, `OAI.TraceReconstruction.initial_pure_sigma_clipped_exists`, `OAI.TraceReconstruction.initial_sigma_clipped_exists`, `OAI.TraceReconstruction.source_all_levels_eventually`, `OAI_TraceReconstruction_source_initial_at_smallest_scale`, `OAI.TraceReconstruction.source_initial_level_eventually`, `OAI_TraceReconstruction_source_level_step` and `OAI_TraceReconstruction_source_warmup_nested_overlap`; the proofs of `OAI_TraceReconstruction_source_initial_at_smallest_scale`, `OAI_TraceReconstruction_source_level_step` and `OAI_TraceReconstruction_source_warmup_nested_overlap`.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/TraceReconstruction at commit adc7f12

import Mathlib
import Definitions.Def_TraceReconstruction

section
-- module Solutions.OAIQ9_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# FiniteLaw

Finite laws, common-reference total variation, Hellinger affinity, overlap, scalar moments, hypercontractivity, clipping, and leaf densities.
-/

open scoped ENNReal
noncomputable section

noncomputable section
namespace TraceReconstruction

/-- Finite probability laws used for the exact statistical transfer. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

def tv (P Q : FiniteLaw α) : ℝ := (1 / 2 : ℝ) * ∑ a, |P.mass a - Q.mass a|
def hellingerSq (P Q : FiniteLaw α) : ℝ :=
  ∑ a, (Real.sqrt (P.mass a) - Real.sqrt (Q.mass a)) ^ 2
def affinity (P Q : FiniteLaw α) : ℝ :=
  ∑ a, Real.sqrt (P.mass a) * Real.sqrt (Q.mass a)

theorem affinity_nonneg (P Q : FiniteLaw α) : 0 ≤ affinity P Q := by
  apply Finset.sum_nonneg
  intro a _; positivity

theorem hellingerSq_nonneg (P Q : FiniteLaw α) : 0 ≤ hellingerSq P Q := by
  apply Finset.sum_nonneg
  intro a _; positivity

theorem hellingerSq_eq (P Q : FiniteLaw α) :
    hellingerSq P Q = 2 - 2 * affinity P Q := by
  unfold hellingerSq affinity
  calc
    _ = (∑ a, P.mass a) + (∑ a, Q.mass a) - 2 * ∑ a,
        Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have hp := Real.sq_sqrt (P.nonneg a)
      have hq := Real.sq_sqrt (Q.nonneg a)
      nlinarith only [hp, hq]
    _ = _ := by rw [P.total, Q.total]; ring

theorem affinity_le_one (P Q : FiniteLaw α) : affinity P Q ≤ 1 := by
  have h := hellingerSq_nonneg P Q
  rw [hellingerSq_eq] at h
  linarith

def product (P : FiniteLaw α) (m : ℕ) : FiniteLaw (Fin m → α) where
  mass a := ∏ j, P.mass (a j)
  nonneg a := Finset.prod_nonneg fun j _ => P.nonneg (a j)
  total := by
    rw [← Fintype.prod_sum]
    simp [P.total]


theorem sqrt_sub_one_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ (t - 1) ^ 2 := by
  have hs2 := Real.sq_sqrt ht
  have hprod := mul_nonneg (Real.sqrt_nonneg t)
    (mul_nonneg (show 0 ≤ Real.sqrt t + 2 by positivity) (sq_nonneg (Real.sqrt t - 1)))
  conv_rhs => rw [← hs2]
  nlinarith only [hprod]

theorem hellingerSq_le_score (P Q : FiniteLaw α) (Z : α → ℝ)
    (hZ : ∀ a, Q.mass a = P.mass a * (1 + Z a)) :
    hellingerSq P Q ≤ ∑ a, P.mass a * Z a ^ 2 := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hp0 : P.mass a = 0
  · have hq0 : Q.mass a = 0 := by rw [hZ, hp0, zero_mul]
    simp [hp0, hq0]
  have hp : 0 < P.mass a := lt_of_le_of_ne (P.nonneg a) (Ne.symm hp0)
  have ht : 0 ≤ 1 + Z a := by
    have hq := Q.nonneg a
    rw [hZ] at hq
    exact nonneg_of_mul_nonneg_right hq hp
  have hs := sqrt_sub_one_sq_le ht
  have hmul := mul_le_mul_of_nonneg_left hs (P.nonneg a)
  have hp2 := Real.sq_sqrt (P.nonneg a)
  rw [hZ, Real.sqrt_mul (P.nonneg a)]
  calc
    _ = P.mass a * (Real.sqrt (1 + Z a) - 1) ^ 2 := by
      calc
        _ = Real.sqrt (P.mass a) ^ 2 * (Real.sqrt (1 + Z a) - 1) ^ 2 := by ring
        _ = _ := by rw [hp2]
    _ ≤ P.mass a * ((1 + Z a) - 1) ^ 2 := hmul
    _ = _ := by ring

def bind (P : FiniteLaw α) (K : α → FiniteLaw β) : FiniteLaw β where
  mass b := ∑ a, P.mass a * (K a).mass b
  nonneg b := Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) ((K a).nonneg b)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (K _).total, mul_one]
    exact P.total

theorem tv_symm (P Q : FiniteLaw α) : tv P Q = tv Q P := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl
  intro a _; exact abs_sub_comm _ _

theorem expectation_diff_le_tv (P Q : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ a, f a ∈ Set.Icc 0 1) :
    (∑ a, P.mass a * f a) - (∑ a, Q.mass a * f a) ≤ tv P Q := by
  have hz : (∑ a, (P.mass a - Q.mass a)) = 0 := by
    rw [Finset.sum_sub_distrib, P.total, Q.total, sub_self]
  have h (a : α) : (P.mass a - Q.mass a) * f a ≤
      (|P.mass a - Q.mass a| + (P.mass a - Q.mass a)) / 2 := by
    by_cases hd : 0 ≤ P.mass a - Q.mass a
    · rw [abs_of_nonneg hd]
      have := mul_le_mul_of_nonneg_left (hf a).2 hd
      linarith
    · rw [abs_of_neg (lt_of_not_ge hd)]
      have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd) (hf a).1
      linarith
  calc
    _ = ∑ a, (P.mass a - Q.mass a) * f a := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _; ring
    _ ≤ ∑ a, (|P.mass a - Q.mass a| + (P.mass a - Q.mass a)) / 2 :=
      Finset.sum_le_sum fun a _ => h a
    _ = tv P Q := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, hz, add_zero]
      unfold tv
      ring


theorem sum_max_eq (P Q : FiniteLaw α) :
    (∑ a, max (P.mass a) (Q.mass a)) = 1 + tv P Q := by
  have hpoint (a : α) : max (P.mass a) (Q.mass a) =
      (P.mass a + Q.mass a + |P.mass a - Q.mass a|) / 2 := by
    by_cases h : P.mass a ≤ Q.mass a
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]; ring
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, P.total, Q.total]
  unfold tv
  ring

def tensor (P : FiniteLaw α) (R : FiniteLaw β) : FiniteLaw (α × β) where
  mass z := P.mass z.1 * R.mass z.2
  nonneg z := mul_nonneg (P.nonneg z.1) (R.nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, R.total, mul_one]
    exact P.total

def overlap (P Q : FiniteLaw α) : ℝ := ∑ a, min (P.mass a) (Q.mass a)

theorem overlap_eq_one_sub_tv (P Q : FiniteLaw α) : overlap P Q = 1 - tv P Q := by
  have hm : overlap P Q + (∑ a, max (P.mass a) (Q.mass a)) = 2 := by
    rw [overlap, ← Finset.sum_add_distrib]
    simp_rw [min_add_max]
    rw [Finset.sum_add_distrib, P.total, Q.total]
    norm_num
  rw [sum_max_eq] at hm
  linarith

def commonPart (P Q : FiniteLaw α) (h : 0 < overlap P Q) : FiniteLaw α where
  mass a := min (P.mass a) (Q.mass a) / overlap P Q
  nonneg a := div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le
  total := by rw [← Finset.sum_div]; exact div_self h.ne'

theorem commonPart_le_left (P Q : FiniteLaw α) (h : 0 < overlap P Q)
    {ω : ℝ} (hω : ω ≤ overlap P Q) (a : α) :
    ω * (commonPart P Q h).mass a ≤ P.mass a := by
  change ω * (min (P.mass a) (Q.mass a) / overlap P Q) ≤ _
  calc
    _ ≤ overlap P Q * (min (P.mass a) (Q.mass a) / overlap P Q) :=
      mul_le_mul_of_nonneg_right hω (div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le)
    _ = min (P.mass a) (Q.mass a) := by field_simp
    _ ≤ _ := min_le_left _ _

def remainderLaw (P H : FiniteLaw α) (ω : ℝ) (hω : ω < 1)
    (hdom : ∀ a, ω * H.mass a ≤ P.mass a) : FiniteLaw α where
  mass a := (P.mass a - ω * H.mass a) / (1 - ω)
  nonneg a := div_nonneg (sub_nonneg.mpr (hdom a)) (sub_pos.mpr hω).le
  total := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, P.total, H.total, mul_one]
    exact div_self (sub_pos.mpr hω).ne'

end FiniteLaw
end TraceReconstruction

namespace TraceReconstruction.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

def prod (P : FiniteLaw α) (Q : FiniteLaw β) : FiniteLaw (α × β) where
  mass x := P.mass x.1 * Q.mass x.2
  nonneg x := mul_nonneg (P.nonneg _) (Q.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Q.total, mul_one]
    exact P.total

def expect (P : FiniteLaw α) (f : α → ℝ) : ℝ := ∑ a, P.mass a * f a

theorem expect_const (P : FiniteLaw α) (c : ℝ) : P.expect (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, P.total, one_mul]

theorem expect_mono (P : FiniteLaw α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    P.expect f ≤ P.expect g := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (h a) (P.nonneg a)

theorem expect_prod (P : FiniteLaw α) (Q : FiniteLaw β) (f : α × β → ℝ) :
    (P.prod Q).expect f = P.expect (fun a => Q.expect (fun b => f (a, b))) := by
  unfold expect prod
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]

/-- Association is only used for increasing likelihood-threshold events. -/
def Associated [Preorder α] (P : FiniteLaw α) : Prop :=
  ∀ f g : α → ℝ, Monotone f → Monotone g →
    P.expect f * P.expect g ≤ P.expect (fun a => f a * g a)

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]
/-- Orientation `false` uses P,Q in chronological order; true reverses them. -/
def orientedProd (P Q : FiniteLaw α) (b : Bool) : FiniteLaw (α × α) :=
  if b then Q.prod P else P.prod Q

def pairedHiddenMass (H : FiniteLaw α) (ω : ℝ) (z : α × α) : ℝ :=
  ω ^ 2 * H.mass z.1 * H.mass z.2

theorem pairedHiddenMass_le (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω * H.mass a ≤ P.mass a) (hQ : ∀ a, ω * H.mass a ≤ Q.mass a)
    (b : Bool) (z : α × α) : pairedHiddenMass H ω z ≤ (orientedProd P Q b).mass z := by
  have hm (R S : FiniteLaw α) (hR : ∀ a, ω * H.mass a ≤ R.mass a)
      (hS : ∀ a, ω * H.mass a ≤ S.mass a) :
      pairedHiddenMass H ω z ≤ R.mass z.1 * S.mass z.2 := by
    calc
      _ = (ω * H.mass z.1) * (ω * H.mass z.2) := by unfold pairedHiddenMass; ring
      _ ≤ _ := mul_le_mul (hR z.1) (hS z.2)
        (mul_nonneg hω (H.nonneg _)) (R.nonneg _)
  cases b
  · exact hm P Q hP hQ
  · exact hm Q P hQ hP

/-- None is the joint hidden flag; a visible flag reports the true orientation. -/
def pairedFlagMass (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool)
    (z : Option Bool × (α × α)) : ℝ :=
  match z.1 with
  | none => pairedHiddenMass H ω z.2
  | some c => if c = b then (orientedProd P Q b).mass z.2 - pairedHiddenMass H ω z.2 else 0

theorem pairedFlagMass_nonneg (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω * H.mass a ≤ P.mass a) (hQ : ∀ a, ω * H.mass a ≤ Q.mass a)
    (b : Bool) (z : Option Bool × (α × α)) : 0 ≤ pairedFlagMass P Q H ω b z := by
  unfold pairedFlagMass
  split
  · unfold pairedHiddenMass
    positivity [H.nonneg z.2.1, H.nonneg z.2.2]
  · split_ifs
    · exact sub_nonneg.mpr (pairedHiddenMass_le P Q H hω hP hQ b z.2)
    · rfl

theorem pairedFlagMass_sum (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool) :
    (∑ z, pairedFlagMass P Q H ω b z) = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hp (z : α × α) : (∑ c : Option Bool, pairedFlagMass P Q H ω b (c, z)) =
      (orientedProd P Q b).mass z := by
    cases b <;> simp [pairedFlagMass, Fintype.sum_option ]
  simp_rw [hp]
  exact (orientedProd P Q b).total

def pairedFlagLaw (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω * H.mass a ≤ P.mass a) (hQ : ∀ a, ω * H.mass a ≤ Q.mass a)
    (b : Bool) : FiniteLaw (Option Bool × (α × α)) :=
  ⟨pairedFlagMass P Q H ω b, pairedFlagMass_nonneg P Q H hω hP hQ b,
    pairedFlagMass_sum P Q H ω b⟩

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction
variable {α : Type*}
def multilinear {n : ℕ} (A : (Fin n → Bool) → ℝ) (Z : α → ℝ) (x : Fin n → α) : ℝ :=
  ∑ σ, A σ * ∏ j, if σ j then Z (x j) else 1

def multilinearEnergy {n : ℕ} (A : (Fin n → Bool) → ℝ) (R : ℝ) : ℝ :=
  ∑ σ, A σ ^ 2 * ∏ j, if σ j then R ^ 2 else 1

def monomialDegree {n : ℕ} (σ : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun j => σ j = true)).card

/-- Squared L^(2k)-norm for a finite law, expressed without measure coercions. -/
def FiniteLaw.evenMomentSq {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f : α → ℝ) (k : ℕ) : ℝ :=
  (P.expect (fun a => |f a| ^ (2 * k))) ^ (1 / (k : ℝ))

end TraceReconstruction

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]
def eventMass (P : FiniteLaw α) (A : Finset α) : ℝ := ∑ a ∈ A, P.mass a

def condition (P : FiniteLaw α) (A : Finset α) (hA : 0 < P.eventMass A) : FiniteLaw α := by
  classical
  exact {
    mass := fun a => if a ∈ A then P.mass a / P.eventMass A else 0
    nonneg := fun a => by split <;> positivity [P.nonneg a]
    total := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hA) }

/-- Densities relative to one finite reference, preserving the exact normalization. -/
def withDensity (P : FiniteLaw α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hmean : P.expect f = 1) : FiniteLaw α where
  mass a := P.mass a * f a
  nonneg a := mul_nonneg (P.nonneg a) (hf a)
  total := hmean

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]
def coordinateProduct {n : ℕ} (P : Fin n → FiniteLaw α) : FiniteLaw (Fin n → α) where
  mass x := ∏ i, (P i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg (x i))
  total := by rw [← Fintype.prod_sum]; simp only [FiniteLaw.total, Finset.prod_const_one]

def mixture (R : FiniteLaw β) (P : β → FiniteLaw α) : FiniteLaw α where
  mass a := ∑ b, R.mass b * (P b).mass a
  nonneg a := Finset.sum_nonneg (fun b _ => mul_nonneg (R.nonneg b) ((P b).nonneg a))
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteLaw.total, mul_one]
    exact R.total
end FiniteLaw
variable {α Ω : Type*} [Fintype Ω]

def selectionCoefficient {n : ℕ} (θ σ : Fin n → Bool) : ℝ :=
  ∏ i, if σ i then (if θ i then 1 else 0) else 1

def selectionDensity {n : ℕ} (θ : Fin n → Bool) (Z : α → ℝ) (x : Fin n → α) : ℝ :=
  ∏ i, if θ i then 1 + Z (x i) else 1

def averagedCoefficient {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (σ : Fin n → Bool) : ℝ := R.expect (fun ω => selectionCoefficient (θ ω) σ)

def averagedDensity {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (Z : α → ℝ) (x : Fin n → α) : ℝ := R.expect (fun ω => selectionDensity (θ ω) Z x)

theorem selectionDensity_expansion {n : ℕ} (θ : Fin n → Bool) (Z : α → ℝ)
    (x : Fin n → α) : selectionDensity θ Z x = multilinear (selectionCoefficient θ) Z x := by
  unfold selectionDensity multilinear selectionCoefficient
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if b then (if θ i then (1 : ℝ) else 0) else 1) * (if b then Z (x i) else 1))]
  apply Finset.prod_congr rfl
  intro i _
  cases θ i <;> simp [add_comm]

theorem averagedDensity_expansion {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (Z : α → ℝ) (x : Fin n → α) :
    averagedDensity R θ Z x = multilinear (averagedCoefficient R θ) Z x := by
  unfold averagedDensity averagedCoefficient
  simp_rw [selectionDensity_expansion]
  unfold multilinear FiniteLaw.expect
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Exact density of the conditionally independent leaf oracle used in the source. -/
theorem leaf_oracle_density [Fintype α] {n : ℕ} (P Q : FiniteLaw α) (Z : α → ℝ)
    (hscore : ∀ a, Q.mass a = P.mass a * (1 + Z a))
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) (x : Fin n → α) :
    (R.mixture (fun ω => FiniteLaw.coordinateProduct (fun i => if θ ω i then Q else P))).mass x =
      (∏ i, P.mass (x i)) * averagedDensity R θ Z x := by
  unfold FiniteLaw.mixture FiniteLaw.coordinateProduct averagedDensity FiniteLaw.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have he : (∏ i, (if θ ω i then Q else P).mass (x i)) =
      (∏ i, P.mass (x i)) * selectionDensity (θ ω) Z x := by
    rw [selectionDensity, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases θ ω i <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one, hscore]
  change R.mass ω * (∏ i, (if θ ω i then Q else P).mass (x i)) =
    (∏ i, P.mass (x i)) * (R.mass ω * selectionDensity (θ ω) Z x)
  rw [he]
  ring
end TraceReconstruction

end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Model

Independent deletion, complete trace observations, randomized estimators, ENNReal fixed-budget complexity, concatenation, and literal input words.
-/

open scoped ENNReal
noncomputable section

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction




/-! ## Exact finite channel laws -/

theorem traceOfMask_length_le {n : ℕ} (x : Word n) (a : Mask n) :
    (traceOfMask x a).length ≤ n := by
  simpa [traceOfMask] using List.length_filter_le (fun i => a i) (List.finRange n)

theorem mem_traceSpace_of_length_le {n : ℕ} (w : Trace) (h : w.length ≤ n) :
    w ∈ traceSpace n := by
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨w.length, Nat.lt_succ_of_le h⟩, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem length_le_of_mem_traceSpace {n : ℕ} {w : Trace} (h : w ∈ traceSpace n) :
    w.length ≤ n := by
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hk
  simpa using Nat.le_of_lt_succ k.isLt

@[simp] theorem mem_traceSpace {n : ℕ} {w : Trace} :
    w ∈ traceSpace n ↔ w.length ≤ n :=
  ⟨length_le_of_mem_traceSpace, mem_traceSpace_of_length_le w⟩

theorem maskWeight_nonneg {n : ℕ} {q : ℝ} (hq : q ∈ Set.Icc 0 1) (a : Mask n) :
    0 ≤ maskWeight q a := by
  apply Finset.prod_nonneg
  intro i _
  split <;> linarith [hq.1, hq.2]

@[simp] theorem sum_maskWeight {n : ℕ} (q : ℝ) :
    ∑ a : Mask n, maskWeight q a = 1 := by
  unfold maskWeight
  change (∑ a : Fin n → Bool, ∏ i, (fun (_ : Fin n) (b : Bool) =>
    if b then 1 - q else q) i (a i)) = 1
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b then 1 - q else q)]
  simp

theorem traceMass_nonneg {n : ℕ} {q : ℝ} (hq : q ∈ Set.Icc 0 1)
    (x : Word n) (w : Trace) : 0 ≤ traceMass q x w := by
  apply Finset.sum_nonneg
  intro a _
  split
  · exact maskWeight_nonneg hq a
  · exact le_rfl

@[simp] theorem sum_traceMass {n : ℕ} (q : ℝ) (x : Word n) :
    ∑ w ∈ traceSpace n, traceMass q x w = 1 := by
  unfold traceMass
  rw [Finset.sum_comm]
  simp [traceOfMask_length_le]

@[simp] theorem traceTV_self {n : ℕ} (q : ℝ) (x : Word n) : traceTV q x x = 0 := by
  simp [traceTV]


end TraceReconstruction

namespace TraceReconstruction
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem ext {P Q : FiniteLaw α} (h : P.mass = Q.mass) : P = Q := by
  cases P with
  | mk pm pn pt => cases Q with
    | mk qm qn qt => cases h; rfl

noncomputable def pure (a : α) : FiniteLaw α := by
  classical
  exact ⟨(fun b => if a = b then 1 else 0),
    (fun b => by split_ifs <;> norm_num), by simp⟩

noncomputable def map (P : FiniteLaw α) (f : α → β) : FiniteLaw β :=
  P.bind (fun a => pure (f a))

theorem map_mass [DecidableEq β] (P : FiniteLaw α) (f : α → β) (b : β) :
    (P.map f).mass b = ∑ a, if f a = b then P.mass a else 0 := by
  classical
  unfold map bind pure
  simp only
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem expectation_map (P : FiniteLaw α) (f : α → β) (F : β → ℝ) :
    (∑ b, (P.map f).mass b * F b) = ∑ a, P.mass a * F (f a) := by
  classical
  simp_rw [map_mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

end FiniteLaw

abbrev BoundedTrace (n : ℕ) := ↥(traceSpace n)

def maskLaw {n : ℕ} (q : ℝ) (hq : q ∈ Set.Icc 0 1) : FiniteLaw (Mask n) :=
  ⟨maskWeight q, maskWeight_nonneg hq, sum_maskWeight q⟩

def completeTraceLaw {n : ℕ} (q : ℝ) (hq : q ∈ Set.Icc 0 1) (x : Word n) :
    FiniteLaw (BoundedTrace n) where
  mass w := traceMass q x w
  nonneg w := traceMass_nonneg hq x w
  total := by rw [Finset.sum_coe_sort]; exact sum_traceMass q x

theorem trace_filterMap {n : ℕ} (x : Word n) (a : Mask n) :
    traceOfMask x a = (List.ofFn fun i => if a i then some (x i) else none).filterMap id := by
  have hlist (l : List (Fin n)) :
      (l.filter fun i => a i).map x = l.filterMap (fun i => if a i then some (x i) else none) := by
    induction l with
    | nil => rfl
    | cons i l ih => cases hai : a i <;> simp [hai, ih]
  unfold traceOfMask
  rw [hlist]
  have heq : (List.ofFn fun i => if a i then some (x i) else none) =
      (List.finRange n).map (fun i => if a i then some (x i) else none) := by
    rw [← List.ofFn_id, List.map_ofFn]
    rfl
  rw [heq, List.filterMap_map]
  rfl

end TraceReconstruction

namespace TraceReconstruction

/-- The four complete traces possible from the ordinary primitive `01`. -/
abbrev PrimitiveMark := Fin 4

def primitiveOutput : PrimitiveMark → List Bool := ![[], [false], [true], [false, true]]
def ordinaryPrimitiveMass (q : ℝ) : PrimitiveMark → ℝ :=
  ![q ^ 2, q * (1 - q), q * (1 - q), (1 - q) ^ 2]
def defectPrimitiveMass (q : ℝ) : PrimitiveMark → ℝ := ![q, 0, 1 - q, 0]
def primitiveErasure (q : ℝ) : ℝ := q ^ 2 / 2

def primitiveMarkMass (q : ℝ) (isDefect : Bool) (z : PrimitiveMark) : ℝ :=
  ((if isDefect then defectPrimitiveMass q z else ordinaryPrimitiveMass q z) -
    if z = 0 then primitiveErasure q else 0) / (1 - primitiveErasure q)

theorem primitive_retain_pos {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    0 < 1 - primitiveErasure q := by
  unfold primitiveErasure
  nlinarith [hq.1, hq.2]

theorem primitiveMarkMass_nonneg {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (b : Bool) (z : PrimitiveMark) : 0 ≤ primitiveMarkMass q b z := by
  apply div_nonneg _ (primitive_retain_pos hq).le
  cases b <;> fin_cases z <;>
    simp [ordinaryPrimitiveMass, defectPrimitiveMass, primitiveErasure] <;>
    nlinarith [hq.1, hq.2]

theorem primitiveMarkMass_sum {q : ℝ} (hq : q ∈ Set.Ioo 0 1) (b : Bool) :
    ∑ z : PrimitiveMark, primitiveMarkMass q b z = 1 := by
  have hd := ne_of_gt (primitive_retain_pos hq)
  unfold primitiveMarkMass
  rw [← Finset.sum_div]
  apply (div_eq_one_iff_eq hd).mpr
  cases b <;> simp [ordinaryPrimitiveMass, defectPrimitiveMass, primitiveErasure, Fin.sum_univ_succ]
  all_goals ring

def primitiveMarkLaw (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (b : Bool) : FiniteLaw PrimitiveMark :=
  ⟨primitiveMarkMass q b, primitiveMarkMass_nonneg hq b, primitiveMarkMass_sum hq b⟩

def primitiveScore (q : ℝ) : PrimitiveMark → ℝ := ![2 / q - 2, -1, 1 / q - 1, -1]

theorem primitive_score_identity {q : ℝ} (hq : q ∈ Set.Ioo 0 1) (z : PrimitiveMark) :
    primitiveMarkMass q true z = primitiveMarkMass q false z * (1 + primitiveScore q z) := by
  have hq0 := ne_of_gt hq.1
  have hd := ne_of_gt (primitive_retain_pos hq)
  fin_cases z <;>
    simp [primitiveMarkMass, ordinaryPrimitiveMass, defectPrimitiveMass, primitiveScore, primitiveErasure] <;>
    field_simp
  all_goals ring

end TraceReconstruction

namespace TraceReconstruction
def ordinaryRun : ℕ → List Bool
  | 0 => []
  | m + 1 => false :: true :: ordinaryRun m

@[simp] theorem ordinaryRun_length (m : ℕ) : (ordinaryRun m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [ordinaryRun, List.length_cons, ih]; omega

/-- A period of m primitives with its unique `1` defect at zero-based slot d. -/
def initialPeriod (m d : ℕ) : List Bool :=
  ordinaryRun d ++ [true] ++ ordinaryRun (m - 1 - d)

def periodString (m P : ℕ) (d : Fin P → Fin m) : List Bool :=
  (List.ofFn (fun i => initialPeriod m (d i))).flatten

end TraceReconstruction

namespace TraceReconstruction
/-- Uniformly sized binary atoms concatenated without boundary marks. -/
def atomString (P : ℕ) (w : Bool → List Bool) (θ : Fin P → Bool) : List Bool :=
  (List.ofFn (fun i => w (θ i))).flatten

/-- Zero-based notation for the source complementary template; `true` is minus.
The motif itself is fixed independently of the hypothesis. -/
def templateType (P a L : ℕ) (sign : Fin L → Bool) (τ : Bool) (i : Fin P) : Bool :=
  if h : a ≤ i.val ∧ i.val < a + L then xor τ (sign ⟨i.val - a, by omega⟩) else false

def complementaryWords (P a L : ℕ) (sign : Fin L → Bool) (w : Bool → List Bool)
    (τ : Bool) : List Bool := atomString P w (templateType P a L sign τ)

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Parity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parity

Parity-tree roles, forced leaves, coefficient shapes, and exact unsigned/signed motif expansions.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

/-- Three roles of an active odd child in the manuscript parity expansion:
constant, unsigned motif, and signed motif. -/
def roleWeight (χ σ : ℝ) (r : Fin 3) : ℝ :=
  if r=0 then 1 else if r=1 then -χ else σ

def signedRoleCount {n : ℕ} (r : Fin n → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => r i=2).card

def activeRoleCount {n : ℕ} (r : Fin n → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => r i≠0).card



/-- A term in the parity expansion retains the occupied ordered shape,
all roles, and all extra children, rather than assuming it is binary. -/
inductive OccupiedParityTree : ℕ → Type
  | leaf : OccupiedParityTree 0
  | node {b : ℕ} (n : ℕ) (children : Fin n → OccupiedParityTree b)
      (roles : Fin n → Fin 3) : OccupiedParityTree (b+1)

def OccupiedParityTree.isOdd : {b : ℕ} → OccupiedParityTree b → Prop
  | _, .leaf => True
  | _, .node _ _ roles => Odd (signedRoleCount roles)

def OccupiedParityTree.leafCount : {b : ℕ} → OccupiedParityTree b → ℕ
  | _, .leaf => 1
  | _, .node _ children _ => ∑ i, (children i).leafCount

/-- Only odd-role child terms may acquire an active parent multiplier. -/
def OccupiedParityTree.valid : {b : ℕ} → OccupiedParityTree b → Prop
  | _, .leaf => True
  | _, .node _ children roles =>
      (∀ i, roles i ≠ 0 → (children i).isOdd) ∧ ∀ i, (children i).valid

def OccupiedParityTree.noSingleton : {b : ℕ} → OccupiedParityTree b → Prop
  | _, .leaf => True
  | _, .node _ children roles =>
      (Odd (signedRoleCount roles) → activeRoleCount roles ≠ 1) ∧
        ∀ i, (children i).noSingleton

end TraceReconstruction

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
attribute [local instance] Classical.propDecidable

/-- The literal unsigned/signed motif values at one child index. -/
def IsMotifValue (χ σ : ℝ) : Prop :=
  (χ=0 ∧ σ=0) ∨ (χ=1 ∧ (σ=1 ∨ σ= -1))

def IsTypeSign (τ : ℝ) : Prop := τ=1 ∨ τ= -1

/-- At the last internal level every selected leaf has to be active.
Role zero has weight zero; unsigned and signed roles are respectively
χ/2 and -σ/2 in (χ-στ)/2. -/
def bottomRoleWeight (χ σ : ℝ) (a : Fin 3) : ℝ :=
  if a=0 then 0 else if a=1 then χ/2 else -σ/2

def internalRoleWeight (odd : Prop) [Decidable odd] (χ σ : ℝ) (a : Fin 3) : ℝ :=
  if odd then roleWeight χ σ a else if a=0 then 1 else 0

/-- An arbitrary occupied ordered subtree, with motif values at its actual
child labels. Depth zero here means a bottom sibling group, so it already
has one internal level. No binary-shape assumption is made. -/
inductive CoefficientShape : ℕ → Type
  | bottom (n : ℕ) (χ σ : Fin n → ℝ) : CoefficientShape 0
  | node {b : ℕ} (n : ℕ) (χ σ : Fin n → ℝ)
      (children : Fin n → CoefficientShape b) : CoefficientShape (b+1)

namespace CoefficientShape

def Admissible : {b : ℕ} → CoefficientShape b → Prop
  | _, .bottom _ χ σ => ∀ i, IsMotifValue (χ i) (σ i)
  | _, .node _ χ σ children => (∀ i, IsMotifValue (χ i) (σ i)) ∧ ∀ i, (children i).Admissible

def eval : {b : ℕ} → CoefficientShape b → ℝ → ℝ
  | _, .bottom _ χ σ, τ => ∏ i, (χ i-σ i*τ)/2
  | _, .node _ χ σ children, τ => ∏ i, (children i).eval (1-χ i+σ i*τ)

def Choice : {b : ℕ} → CoefficientShape b → Type
  | _, .bottom n _ _ => Fin n → Fin 3
  | _, .node n _ _ children => ((i : Fin n) → (children i).Choice) × (Fin n → Fin 3)

noncomputable instance choiceFintype : {b : ℕ} → (t : CoefficientShape b) → Fintype t.Choice
  | _, .bottom _ _ _ => by unfold Choice; infer_instance
  | _, .node _ _ _ children => by
      letI := fun i => choiceFintype (children i)
      unfold Choice
      first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def termTree : {b : ℕ} → (t : CoefficientShape b) → t.Choice → OccupiedParityTree (b+1)
  | _, .bottom n _ _, a => .node n (fun _ => .leaf) a
  | _, .node n _ _ children, a => .node n (fun i => (children i).termTree (a.1 i)) a.2

noncomputable def weight : {b : ℕ} → (t : CoefficientShape b) → t.Choice → ℝ
  | _, .bottom _ χ σ, a => ∏ i, bottomRoleWeight (χ i) (σ i) (a i)
  | _, .node _ χ σ children, a => ∏ i,
      (children i).weight (a.1 i) *
        @internalRoleWeight ((children i).termTree (a.1 i)).isOdd (Classical.propDecidable _)
          (χ i) (σ i) (a.2 i)

end CoefficientShape
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
namespace OccupiedParityTree

/-- The actual binary selection sits inside an arbitrary occupied parity
term, retaining its unselected children rather than assuming binary input. -/
inductive Forced : {b : ℕ} → OccupiedParityTree b → Type
  | leaf : Forced .leaf
  | node {b n : ℕ} {children : Fin n → OccupiedParityTree b} {roles : Fin n → Fin 3}
      (a c : Fin n) (hne : a≠c) (ha : roles a≠0) (hc : roles c≠0)
      (left : Forced (children a)) (right : Forced (children c)) :
      Forced (.node n children roles)

/-- Occupied shapes have at least one selected leaf below every vertex. -/
def occupied : {b : ℕ} → OccupiedParityTree b → Prop
  | _, .leaf => True
  | _, .node n children _ => 0<n ∧ ∀ i, (children i).occupied

/-- Number of vertices at a given distance below the root. -/
def levelCount : {b : ℕ} → OccupiedParityTree b → ℕ → ℕ
  | _, _, 0 => 1
  | _, .leaf, _+1 => 0
  | _, .node _ children _, k+1 => ∑ i, (children i).levelCount k

theorem leafCount_pos {b : ℕ} (t : OccupiedParityTree b) (ht : t.occupied) :
    0<t.leafCount := by
  induction t with
  | leaf => exact Nat.zero_lt_one
  | @node b n children roles ih =>
    let i : Fin n := ⟨0,ht.1⟩
    have hp := ih i (ht.2 i)
    change 0 < ∑ k, (children k).leafCount
    exact hp.trans_le (Finset.single_le_sum (fun k _ => Nat.zero_le ((children k).leafCount)) (Finset.mem_univ i))

/-- Two chosen coordinates supply an additive gain in a finite sum. -/
theorem sum_two_improvements {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℕ) {a c : ι} (hne : a≠c) (A B : ℕ)
    (hrest : ∀ i, i≠a → i≠c → x i≤y i)
    (ha : x a+A≤y a+B) (hc : x c+A≤y c+B) :
    (∑ i, x i)+2*A ≤ (∑ i, y i)+2*B := by
  have hc' : c∈Finset.univ.erase a := by simp [hne.symm]
  have hx1 := Finset.sum_erase_add Finset.univ x (Finset.mem_univ a)
  have hy1 := Finset.sum_erase_add Finset.univ y (Finset.mem_univ a)
  have hx2 := Finset.sum_erase_add (Finset.univ.erase a) x hc'
  have hy2 := Finset.sum_erase_add (Finset.univ.erase a) y hc'
  have hrem : (∑ i∈(Finset.univ.erase a).erase c, x i) ≤
      ∑ i∈(Finset.univ.erase a).erase c, y i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hrest i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      (Finset.mem_erase.mp hi).1
  omega

theorem Forced.leaf_lower {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    2^b ≤ t.leafCount := by
  classical
  induction F with
  | leaf => simp [leafCount]
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    have hh := sum_two_improvements (fun _ : Fin n => 0)
      (fun i => (children i).leafCount) hne (2^b) 0
      (fun _ _ _ => Nat.zero_le _) (by simpa using ihl) (by simpa using ihr)
    simpa only [Finset.sum_const_zero,zero_add,add_zero,zero_mul,pow_succ,Nat.mul_comm,leafCount] using hh

end OccupiedParityTree
end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Binomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Binomial

Fair and biased binomial laws, generating series, differences, concentration, Gaussian overlap, hidden counts, and local lower bounds.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

/-! ## Quantitative fair-binomial anti-concentration

A direct inductive bound, avoiding an unformalized appeal to Stirling.
It is one of the estimates needed for signed binomial smoothing and
for the local/global anchor kernels.
-/

/-- Fair-binomial mass, extended by zero beyond its natural support. -/
def fairBinomial (n k : ℕ) : ℝ := (n.choose k : ℝ) / 2 ^ n

theorem fairBinomial_nonneg (n k : ℕ) : 0 ≤ fairBinomial n k := by
  unfold fairBinomial
  positivity


/-! ## Discrete convolution estimates for the hidden displacement kernels -/

abbrev IntSeries := AddMonoidAlgebra ℝ ℤ

def seriesL1 (f : IntSeries) : ℝ := ∑' z : ℤ, |f.coeff z|
def seriesL2Sq (f : IntSeries) : ℝ := ∑' z : ℤ, f.coeff z ^ 2

/-! The probability generating series of the fair binomial kernel. -/
def fairSeries (n : ℕ) : IntSeries :=
  (AddMonoidAlgebra.single 1 (1 / 2) + AddMonoidAlgebra.single 0 (1 / 2)) ^ n

theorem fairSeries_sum (n : ℕ) :
    fairSeries n = ∑ k ∈ Finset.range (n + 1),
      AddMonoidAlgebra.single (k : ℤ) (fairBinomial n k) := by
  unfold fairSeries
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  congr 1
  rw [← pow_add, Nat.add_sub_of_le hkn]
  unfold fairBinomial
  rw [div_pow]
  simp [div_eq_mul_inv, mul_comm]

theorem fairSeries_coeff_nat (n k : ℕ) :
    (fairSeries n).coeff (k : ℤ) = fairBinomial n k := by
  rw [fairSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
    · intro b _ hb
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hb]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [Finset.sum_eq_zero]
    · simp [fairBinomial, Nat.choose_eq_zero_of_lt (by omega : n < k)]
    · intro b hb
      have hbk : b ≠ k := by simp only [Finset.mem_range] at hb; omega
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Nat.cast_inj, ite_eq_right hbk]

theorem fairSeries_coeff_neg (n : ℕ) (z : ℤ) (hz : z < 0) :
    (fairSeries n).coeff z = 0 := by
  rw [fairSeries_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  have h : (b : ℤ) ≠ z := by omega
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right h]

def firstDifference : IntSeries :=
  AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single 1 1

def binomialBound (n : ℕ) : ℝ := Real.sqrt (2 / ((n : ℝ) + 1))

theorem fairSeries_nonneg (n : ℕ) (z : ℤ) : 0 ≤ (fairSeries n).coeff z := by
  by_cases hz : 0 ≤ z
  · rw [← Int.toNat_of_nonneg hz, fairSeries_coeff_nat]
    exact fairBinomial_nonneg _ _
  · rw [fairSeries_coeff_neg n z (by omega)]

def geomSeries (k : ℕ) : IntSeries := ∑ a ∈ Finset.range k, (AddMonoidAlgebra.single 1 1) ^ a

def prouhetSeries (s : ℕ) : IntSeries :=
  ∏ v ∈ Finset.range s, (1 - (AddMonoidAlgebra.single 1 1) ^ (2 ^ v))

def prouhetQuotient (s : ℕ) : IntSeries :=
  ∏ v ∈ Finset.range s, geomSeries (2 ^ v)


/-! ## Nonfair anti-concentration without an assumed Stirling estimate -/

def binomialMass (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

theorem binomialMass_nonneg (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    0 ≤ binomialMass n p k := by
  unfold binomialMass
  positivity [hp.1, sub_nonneg.mpr hp.2]

theorem sum_binomialMass (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k = 1 := by
  have h := add_pow p (1 - p) n
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  unfold binomialMass
  ring


def mixedFairSeries (n : ℕ) (p : ℝ) : IntSeries :=
  (p • fairSeries 1 + (1 - p) • (1 : IntSeries)) ^ n

def biasedSeries (n : ℕ) (p : ℝ) : IntSeries :=
  (AddMonoidAlgebra.single 1 p + AddMonoidAlgebra.single 0 (1 - p)) ^ n


def biasedBinomialBound (n : ℕ) (p : ℝ) : ℝ :=
  Real.sqrt (1 / (((n : ℝ) + 1) * p * (1 - p)))

/-! ## Gaussian overlap by exponential tilting of the exact binomial law -/

end TraceReconstruction

namespace TraceReconstruction
def hypergeomMass (V M m v : ℕ) : ℝ :=
  if v ≤ m then (V.choose v : ℝ) * (M.choose (m-v) : ℝ) / ((V+M).choose m : ℝ) else 0

theorem hypergeomMass_nonneg (V M m v : ℕ) : 0 ≤ hypergeomMass V M m v := by
  unfold hypergeomMass
  split <;> positivity

theorem sum_hypergeomMass (V M m : ℕ) (hm : m ≤ V+M) :
    ∑ v ∈ Finset.range (m+1), hypergeomMass V M m v = 1 := by
  have hc : (0 : ℝ) < (V+M).choose m := by exact_mod_cast Nat.choose_pos hm
  have hv := Nat.add_choose_eq V M m
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  simp only [hypergeomMass]
  have he : (∑ v ∈ Finset.range (m+1),
      if v ≤ m then (V.choose v : ℝ)*(M.choose (m-v) : ℝ)/((V+M).choose m : ℝ) else 0) =
    (∑ v ∈ Finset.range (m+1), (V.choose v : ℝ)*(M.choose (m-v) : ℝ))/((V+M).choose m : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v hv'
    rw [ite_eq_left (by simp only [Finset.mem_range] at hv'; omega)]
  rw [he]
  have he' : (∑ v ∈ Finset.range (m+1), (V.choose v : ℝ)*(M.choose (m-v) : ℝ)) =
      ((V+M).choose m : ℝ) := by exact_mod_cast hv.symm
  rw [he', div_self (ne_of_gt hc)]

def hypergeomHiddenMode (V M m : ℕ) : ℕ := (M+1)*(m+1)/(V+M+2)

def hypergeomHiddenFlux (V M m k : ℕ) : ℝ :=
  (V:ℝ)/(V+M)*hypergeomMass M (V-1) m k

/-- Exact adjacent visible-count TV, expressed with complementary hidden counts.
The shift by one is essential: the two totals are different. -/
def adjacentHypergeomTV (V M m : ℕ) : ℝ :=
  (1/2:ℝ)*(hypergeomMass M V (m+1) 0 +
    ∑ k ∈ Finset.range (M+1), |hypergeomMass M V (m+1) (k+1)-hypergeomMass M V m k|)

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Kernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Kernels

Constrained rank-gap sums, correlated anchor kernels, window kernels, lattice Laplace sums, and geometric degree bounds.
-/

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction

def windowKernel (n L : ℕ) (z : ℤ) : ℝ :=
  ∑ a ∈ Finset.range L, (fairSeries n).coeff ((a:ℤ)-z)

def jointWindowKernel (g n₁ n₂ L : ℕ) (z₁ z₂ : ℤ) : ℝ :=
  ∑ v ∈ (fairSeries g).coeff.support,
    (fairSeries g).coeff v * windowKernel n₁ L (z₁+v) * windowKernel n₂ L (z₂+v)

end TraceReconstruction

open Filter
open scoped Topology


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scales

Exact block exponents, deletion reduction, induction depth, backward target scales, and uniform power absorption.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction
/-- The exact real scale exponents in the scale inequalities; natural indices are zero-based. -/
def scaleA (b j : ℕ) (ε : ℝ) : ℝ := (1+ε)* (2:ℝ)^j / (2:ℝ)^b - ε

def scaleKappa (b j : ℕ) (ε : ℝ) : ℝ :=
  scaleA b (j-1) ε - 3*((2:ℝ)^j-1)*ε

def sourceEpsilon (B D : ℕ) : ℝ := 1 / ((2:ℝ)^(4*B+100) * (D+1))

def forcedDecay (b : ℕ) (ε d : ℝ) : ℝ :=
  ε/2 + ∑ k ∈ Finset.range (b-1),
    ((2:ℝ)^b / (2:ℝ)^(k+2))*(scaleKappa b (k+2) ε / 2 + ε) +
  (2:ℝ)^b * scaleA b 0 ε * d

end TraceReconstruction

open Filter
open scoped Topology


open Filter
open scoped Topology
namespace TraceReconstruction

def blockGain (b : ℕ) : ℝ := ((b:ℝ)-1)/4-1/20
def warmupBlocks (B : ℕ) : ℕ := 5*2^B
def totalScoreExponent (B D : ℕ) : ℝ :=
  11/5+∑ i ∈ Finset.range D, blockGain (if i<warmupBlocks B then 2 else B)
def finalSlope (B : ℕ) (ζ : ℝ) : ℝ := (1-ζ)*blockGain B/((B:ℝ)*Real.log 2)

end TraceReconstruction

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open Filter

/-- Literal source block dimensions, with zero-based block number. -/
def sourceDimension (B i : ℕ) : ℕ := if i < warmupBlocks B then 2 else B

def sourceScaleProduct (B D i : ℕ) : ℝ :=
  ∏j∈Finset.Ico i D,scaleA (sourceDimension B j) 0 (sourceEpsilon B D)

/-- The backwards target scales as an exact product of source exponents. -/
def sourceTargetScale (B D : ℕ) (n : ℝ) (i : ℕ) : ℝ := n ^ sourceScaleProduct B D i

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology

/-- Logarithmic order along a genuine diverging positive scale. -/
def PowerRate (N f : ℕ → ℝ) (a : ℝ) : Prop :=
  (∀ᶠ t in Filter.atTop, 0 < f t) ∧ Tendsto (fun t => Real.log (f t) / Real.log (N t)) Filter.atTop (𝓝 a)

/-- A robust upper order, with arbitrary strictly positive exponent slack. -/
def PowerUpper (N f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ b, a < b → ∀ᶠ t in Filter.atTop, |f t| ≤ (N t)^b

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Ranks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ranks

Retained subsets, conditional rank experiments, tagged gaps, period geometry, Gaussian Schur estimates, and uniform square sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


namespace TraceReconstruction

variable {α : Type*} [Fintype α]

def subsetWeight (p : ℝ) (S : Finset α) : ℝ :=
  p^S.card * (1-p)^(Fintype.card α-S.card)

theorem sum_subsetWeight (p : ℝ) : (∑ S : Finset α, subsetWeight p S)=1 := by
  classical
  have h := Finset.sum_pow_mul_eq_add_pow p (1-p) (Finset.univ : Finset α)
  simpa [subsetWeight] using h

def subsetLaw (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FiniteLaw (Finset α) where
  mass := subsetWeight p
  nonneg S := by unfold subsetWeight; positivity [hp.1, sub_nonneg.mpr hp.2]
  total := sum_subsetWeight p

abbrev FixedSubset (α : Type*) [Fintype α] (l : ℕ) := {S : Finset α // S.card=l}

theorem card_fixedSubset (l : ℕ) :
    Fintype.card (FixedSubset α l)=(Fintype.card α).choose l := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun S : Finset α => S.card=l)) =
      (Finset.univ : Finset α).powersetCard l := by ext; simp
  rw [hset, Finset.card_powersetCard, Finset.card_univ]

def uniformSubsetLaw (l : ℕ) (hl : l ≤ Fintype.card α) : FiniteLaw (FixedSubset α l) where
  mass _ := 1 / ((Fintype.card α).choose l : ℝ)
  nonneg _ := by positivity
  total := by
    classical
    simp only [Finset.sum_const, Finset.card_univ, card_fixedSubset, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast (Nat.choose_pos hl).ne')

/-- Slot at an observed return rank, with the original total order. -/
def slotAtRank {n l : ℕ} (S : FixedSubset (Fin n) l) (v : Fin l) : Fin n :=
  (S.val.orderIsoOfFin S.property v).val

theorem slotAtRank_mem {n l : ℕ} (S : FixedSubset (Fin n) l) (v : Fin l) :
    slotAtRank S v ∈ S.val := (S.val.orderIsoOfFin S.property v).property

def defectAtRank {n l : ℕ} (D : Finset (Fin n)) (S : FixedSubset (Fin n) l)
    (v : Fin l) : Bool := decide (slotAtRank S v ∈ D)

def taggedRankEvent {n l r : ℕ} (p : Fin r → Fin n) (v : Fin r → Fin l)
    (S : FixedSubset (Fin n) l) : Prop := ∀ i, slotAtRank S (v i)=p i

/-- Unhypothesized rank kernel: defined from the actual uniformly retained subset. -/
def subsetRankKernel {n l r : ℕ} (hl : l≤n) (p : Fin r → Fin n) (v : Fin r → Fin l) : ℝ := by
  classical
  exact ∑ S : FixedSubset (Fin n) l, if taggedRankEvent p v S then
    (uniformSubsetLaw l (by simpa using hl)).mass S else 0


/-- Canonical slot universe split at the tagged positions. Actual order is only
needed to identify each component with its before/between/after interval. -/
abbrev GapUniverse (r d : ℕ) (g : Fin d → ℕ) := Fin r ⊕ ((i : Fin d) × Fin (g i))

def gapDecode {r d : ℕ} {g : Fin d → ℕ} (S : Finset (GapUniverse r d g))
    (i : Fin d) : Finset (Fin (g i)) :=
  Finset.univ.filter fun a => Sum.inr ⟨i,a⟩ ∈ S

def gapEncode {r d : ℕ} {g : Fin d → ℕ} (A : (i : Fin d) → Finset (Fin (g i))) :
    Finset (GapUniverse r d g) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | Sum.inl _ => True
    | Sum.inr a => a.2 ∈ A a.1

@[simp] theorem mem_gapEncode_left {r d : ℕ} {g : Fin d → ℕ}
    (A : (i : Fin d) → Finset (Fin (g i))) (a : Fin r) :
    Sum.inl a ∈ gapEncode A := by simp [gapEncode]

@[simp] theorem mem_gapEncode_right {r d : ℕ} {g : Fin d → ℕ}
    (A : (i : Fin d) → Finset (Fin (g i))) (i : Fin d) (a : Fin (g i)) :
    Sum.inr ⟨i,a⟩ ∈ gapEncode (r := r) A ↔ a ∈ A i := by simp [gapEncode]

@[simp] theorem gapDecode_encode {r d : ℕ} {g : Fin d → ℕ}
    (A : (i : Fin d) → Finset (Fin (g i))) (i : Fin d) :
    gapDecode (gapEncode (r := r) A) i=A i := by ext; simp [gapDecode]

theorem gapEncode_decode {r d : ℕ} {g : Fin d → ℕ}
    (S : Finset (GapUniverse r d g)) (hS : ∀ a, Sum.inl a∈S) :
    gapEncode (gapDecode S)=S := by
  ext x
  cases x with
  | inl a => simp [hS]
  | inr a => rcases a with ⟨i,a⟩; simp [gapDecode]

def gapEvent {r d : ℕ} {g : Fin d → ℕ} (z : Fin d → ℕ)
    (S : Finset (GapUniverse r d g)) : Prop :=
  (∀ a, Sum.inl a∈S) ∧ ∀ i, (gapDecode S i).card=z i

instance gapEvent_decidable {r d : ℕ} {g : Fin d → ℕ} (z : Fin d → ℕ)
    (S : Finset (GapUniverse r d g)) : Decidable (gapEvent z S) := by
  unfold gapEvent
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def gapEventEquiv {r d : ℕ} {g z : Fin d → ℕ} :
    {S : Finset (GapUniverse r d g) // gapEvent z S} ≃
      ((i : Fin d) → FixedSubset (Fin (g i)) (z i)) where
  toFun S i := ⟨gapDecode S.val i, S.property.2 i⟩
  invFun A := ⟨gapEncode (fun i => (A i).val), by
    constructor
    · intro a; simp
    · intro i; simp only [gapDecode_encode, (A i).property]⟩
  left_inv S := by
    apply Subtype.ext
    exact gapEncode_decode S.val S.property.1
  right_inv A := by
    funext i
    apply Subtype.ext
    change gapDecode (gapEncode (fun i => (A i).val)) i = (A i).val
    exact gapDecode_encode _ _

theorem card_gapEncode {r d : ℕ} {g : Fin d → ℕ}
    (A : (i : Fin d) → Finset (Fin (g i))) :
    (gapEncode (r := r) A).card = r + ∑ i, (A i).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  simp only [gapEncode, Finset.sum_filter]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ x : Fin (g i), if x ∈ A i then (1:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    _ = _ := (Finset.card_eq_sum_ite (Finset.subset_univ (A i))).symm

theorem card_of_gapEvent {r d : ℕ} {g z : Fin d → ℕ}
    (S : Finset (GapUniverse r d g)) (hS : gapEvent z S) :
    S.card = r+∑ i, z i := by
  rw [← gapEncode_decode S hS.1, card_gapEncode]
  simp only [hS.2]


end TraceReconstruction


namespace TraceReconstruction

theorem slotAtRank_lower_card {n l : ℕ} (S : FixedSubset (Fin n) l) (v : Fin l) :
    (S.val.filter fun j => j < slotAtRank S v).card = v.val := by
  classical
  let e := S.val.orderEmbOfFin S.property
  have hslot (i:Fin l) : e i = slotAtRank S i := rfl
  have hmap : (Finset.Iio v).map e.toEmbedding = S.val.filter (fun j => j<e v) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_Iio, Finset.mem_filter, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨S.val.orderEmbOfFin_mem S.property i, e.strictMono hi⟩
    · rintro ⟨hj,hv⟩
      obtain ⟨i,hi⟩ := (S.val.orderIsoOfFin S.property).surjective ⟨j,hj⟩
      have hei : e i=j := congrArg Subtype.val hi
      refine ⟨i, ?_, hei⟩
      exact e.lt_iff_lt.mp (hei.symm ▸ hv)
  rw [← hslot, ← hmap, Finset.card_map, Fin.card_Iio]

theorem slotAtRank_eq_iff {n l : ℕ} (S : FixedSubset (Fin n) l) (v : Fin l) (p : Fin n) :
    slotAtRank S v=p ↔ p∈S.val ∧ (S.val.filter fun j => j<p).card=v.val := by
  classical
  constructor
  · intro h
    rw [← h]
    exact ⟨slotAtRank_mem S v, slotAtRank_lower_card S v⟩
  · rintro ⟨hp,hcard⟩
    obtain ⟨i,hi⟩ := (S.val.orderIsoOfFin S.property).surjective ⟨p,hp⟩
    have he : slotAtRank S i=p := congrArg Subtype.val hi
    have hcv := slotAtRank_lower_card S i
    rw [he,hcard] at hcv
    have hiv : i=v := Fin.ext hcv.symm
    simpa [hiv] using he

/-- Bounds for the open gaps of an increasing tuple; slots and ranks are zero-based. -/
def tupleLower {n r : ℕ} (p : Fin r → Fin n) : Fin (r+1) → ℕ :=
  Fin.cons 0 (fun i => (p i).val + 1)

def tupleUpper {n r : ℕ} (p : Fin r → Fin n) : Fin (r+1) → ℕ :=
  Fin.snoc (fun i => (p i).val) n

def tupleGap {n r : ℕ} (p : Fin r → Fin n) (j : Fin (r+1)) : ℕ :=
  tupleUpper p j - tupleLower p j

@[simp] theorem tupleLower_zero {n r : ℕ} (p : Fin r → Fin n) : tupleLower p 0 = 0 :=
  Fin.cons_zero _ _
@[simp] theorem tupleLower_succ {n r : ℕ} (p : Fin r → Fin n) (i : Fin r) :
    tupleLower p i.succ = (p i).val + 1 := Fin.cons_succ _ _ _
@[simp] theorem tupleUpper_castSucc {n r : ℕ} (p : Fin r → Fin n) (i : Fin r) :
    tupleUpper p i.castSucc = (p i).val := Fin.snoc_castSucc _ _ _
@[simp] theorem tupleUpper_last {n r : ℕ} (p : Fin r → Fin n) :
    tupleUpper p (Fin.last r) = n := Fin.snoc_last _ _

theorem tupleLower_le_tag {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) (j : Fin (r+1)) (hji : j ≤ i.castSucc) :
    tupleLower p j ≤ (p i).val := by
  induction j using Fin.cases with
  | zero => simp
  | succ a =>
    simp only [tupleLower_succ]
    have hai : a < i := by
      change a.val < i.val
      have hh : a.val + 1 ≤ i.val := hji
      omega
    exact hp hai

theorem tag_lt_tupleLower {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) (j : Fin (r+1)) (hij : i.castSucc < j) :
    (p i).val < tupleLower p j := by
  induction j using Fin.cases with
  | zero => exact False.elim (by simp at hij)
  | succ a =>
    simp only [tupleLower_succ]
    have hia : i ≤ a := by
      change i.val ≤ a.val
      have hh : i.val < a.val + 1 := hij
      omega
    exact Nat.lt_succ_of_le (hp.monotone hia)

theorem tupleUpper_le_total {n r : ℕ} (p : Fin r → Fin n) (j : Fin (r+1)) :
    tupleUpper p j ≤ n := by
  induction j using Fin.lastCases with
  | last => simp
  | cast i => simpa only [tupleUpper_castSucc] using (p i).isLt.le

theorem tupleLower_le_total {n r : ℕ} (p : Fin r → Fin n) (j : Fin (r+1)) :
    tupleLower p j ≤ n := by
  induction j using Fin.cases with
  | zero => simp
  | succ i => simpa only [tupleLower_succ] using Nat.succ_le_of_lt (p i).isLt

theorem tupleLower_le_upper {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (j : Fin (r+1)) : tupleLower p j ≤ tupleUpper p j := by
  induction j using Fin.lastCases with
  | last => simpa using tupleLower_le_total p (Fin.last r)
  | cast i => simpa using tupleLower_le_tag p hp i i.castSucc le_rfl

theorem tupleGap_total {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p) :
    r + ∑ j, tupleGap p j = n := by
  have hrs : r ≤ n := by simpa using Fintype.card_le_of_injective p hp.injective
  have ha : (∑ j, tupleLower p j) = (∑ i, (p i).val) + r := by
    rw [Fin.sum_univ_succ]
    simp [Finset.sum_add_distrib]
  have hb : (∑ j, tupleUpper p j) = (∑ i, (p i).val) + n := by
    rw [Fin.sum_univ_castSucc]
    simp
  simp only [tupleGap]
  rw [Finset.sum_tsub_distrib _ (fun j _ => tupleLower_le_upper p hp j), ha, hb]
  omega

/-- Maps abstract gap coordinates to their actual source slots. -/
def tupleGapMap {n r : ℕ} (p : Fin r → Fin n) :
    GapUniverse r (r+1) (tupleGap p) → Fin n
  | .inl i => p i
  | .inr ⟨j,a⟩ => ⟨tupleLower p j + a.val, by
      have hx := a.isLt
      have hu := tupleUpper_le_total p j
      simp only [tupleGap] at hx
      omega⟩

theorem tupleGapMap_gap_lt_tag {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) (j : Fin (r+1)) (a : Fin (tupleGap p j)) :
    tupleGapMap p (.inr ⟨j,a⟩) < p i ↔ j ≤ i.castSucc := by
  constructor
  · intro h
    by_contra hn
    have hx := tag_lt_tupleLower p hp i j (lt_of_not_ge hn)
    change tupleLower p j + a.val < (p i).val at h
    omega
  · intro h
    have hji : j.val < r := lt_of_le_of_lt (show j.val ≤ i.val from h) i.isLt
    let k : Fin r := ⟨j.val, hji⟩
    have hjk : j = k.castSucc := Fin.ext rfl
    have ht : tupleUpper p j ≤ (p i).val := by
      rw [hjk, tupleUpper_castSucc]
      exact hp.monotone (show k ≤ i from h)
    have hx := a.isLt
    change tupleLower p j + a.val < (p i).val
    unfold tupleGap at hx
    omega

theorem tupleGapMap_tag_lt_gap {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) (j : Fin (r+1)) (a : Fin (tupleGap p j)) :
    p i < tupleGapMap p (.inr ⟨j,a⟩) ↔ i.castSucc < j := by
  constructor
  · intro h
    by_contra hn
    have hx := (tupleGapMap_gap_lt_tag p hp i j a).2 (le_of_not_gt hn)
    exact (lt_asymm h hx)
  · intro h
    have hx := tag_lt_tupleLower p hp i j h
    change (p i).val < tupleLower p j + a.val
    omega

theorem tupleGapMap_injective {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p) :
    Function.Injective (tupleGapMap p) := by
  rintro (i | ⟨j,a⟩) (i' | ⟨j',a'⟩) h
  · exact congrArg Sum.inl (hp.injective h)
  · have hn : p i ≠ tupleGapMap p (.inr ⟨j',a'⟩) := by
      rcases le_or_gt j' i.castSucc with hj | hj
      · exact ne_of_gt ((tupleGapMap_gap_lt_tag p hp i j' a').2 hj)
      · exact ne_of_lt ((tupleGapMap_tag_lt_gap p hp i j' a').2 hj)
    exact False.elim (hn h)
  · have hn : p i' ≠ tupleGapMap p (.inr ⟨j,a⟩) := by
      rcases le_or_gt j i'.castSucc with hj | hj
      · exact ne_of_gt ((tupleGapMap_gap_lt_tag p hp i' j a).2 hj)
      · exact ne_of_lt ((tupleGapMap_tag_lt_gap p hp i' j a).2 hj)
    exact False.elim (hn h.symm)
  · have hj : j=j' := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hj | hj
      · let i : Fin r := ⟨j.val, lt_of_lt_of_le hj (Nat.le_of_lt_succ j'.isLt)⟩
        have hji : j=i.castSucc := Fin.ext rfl
        have h1 := (tupleGapMap_gap_lt_tag p hp i j a).2 (by rw [hji])
        have h2 := (tupleGapMap_tag_lt_gap p hp i j' a').2 (by rwa [← hji])
        rw [h] at h1
        exact (lt_asymm h1 h2)
      · let i : Fin r := ⟨j'.val, lt_of_lt_of_le hj (Nat.le_of_lt_succ j.isLt)⟩
        have hji : j'=i.castSucc := Fin.ext rfl
        have h1 := (tupleGapMap_gap_lt_tag p hp i j' a').2 (by rw [hji])
        have h2 := (tupleGapMap_tag_lt_gap p hp i j a).2 (by rwa [← hji])
        rw [h] at h2
        exact (lt_asymm h1 h2)
    subst j'
    have ha : a=a' := by
      apply Fin.ext
      have hh := congrArg Fin.val h
      change tupleLower p j + a.val = tupleLower p j + a'.val at hh
      omega
    subst a'
    rfl

def tupleGapEquiv {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p) :
    GapUniverse r (r+1) (tupleGap p) ≃ Fin n :=
  Equiv.ofBijective (tupleGapMap p) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨tupleGapMap_injective p hp, by
      simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
      exact tupleGap_total p hp⟩)

/-- The count below a tagged slot is its tag index plus the retained gap counts. -/
theorem gapEncoded_lower_card {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (A : (j : Fin (r+1)) → Finset (Fin (tupleGap p j))) (i : Fin r) :
    (((gapEncode A).map (tupleGapEquiv p hp).toEmbedding).filter
      fun x => x < p i).card = i.val + ∑ j ∈ Finset.Iic i.castSucc, (A j).card := by
  classical
  have hmap : (((gapEncode A).map (tupleGapEquiv p hp).toEmbedding).filter
      fun x => x < p i) =
      ((gapEncode A).filter fun x => tupleGapMap p x < p i).map
        (tupleGapEquiv p hp).toEmbedding := by
    rw [Finset.filter_map]
    rfl
  rw [hmap, Finset.card_map, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, gapEncode]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only
  simp only [↓reduceIte]
  have hleft : (∑ a : Fin r, if tupleGapMap p (.inl a) < p i then (1:ℕ) else 0) = i.val := by
    simp only [tupleGapMap, hp.lt_iff_lt]
    have hx : (Finset.univ.filter fun a : Fin r => a < i) = Finset.Iio i := by ext; simp
    rw [← Finset.sum_filter, hx, Finset.sum_const, Fin.card_Iio, smul_eq_mul, mul_one]
  rw [hleft]
  congr 1
  simp_rw [tupleGapMap_gap_lt_tag p hp]
  have hr (j : Fin (r+1)) :
      (∑ a : Fin (tupleGap p j), if a ∈ A j then
        (if j ≤ i.castSucc then (1:ℕ) else 0) else 0) =
      if j ≤ i.castSucc then (A j).card else 0 := by
    by_cases hj : j ≤ i.castSucc
    · simp only [hj, ite_true]
      exact (Finset.card_eq_sum_ite (Finset.subset_univ (A j))).symm
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => hr j), ← Finset.sum_filter]
  congr 1
  ext j
  simp

@[simp] theorem gapEncode_univ {r d : ℕ} {g : Fin d → ℕ} :
    gapEncode (r := r) (fun i => (Finset.univ : Finset (Fin (g i)))) = Finset.univ := by
  ext x
  cases x with
  | inl i => simp
  | inr p => rcases p with ⟨j,a⟩; simp

theorem tupleGap_prefix {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) : i.val + ∑ j ∈ Finset.Iic i.castSucc, tupleGap p j = (p i).val := by
  have h := gapEncoded_lower_card p hp (fun _ => Finset.univ) i
  have hset : (Finset.univ.filter fun x : Fin n => x < p i) = Finset.Iio (p i) := by
    ext; simp
  simpa only [gapEncode_univ, Finset.map_univ_equiv,
    hset, Fin.card_Iio, Finset.card_univ, Fintype.card_fin] using h.symm

/-- Initial-segment sums determine a family of natural numbers. -/
theorem fin_prefix_sum_injective {d : ℕ} (f g : Fin d → ℕ)
    (h : ∀ i, (∑ j ∈ Finset.Iic i, f j) = ∑ j ∈ Finset.Iic i, g j) : f=g := by
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hset : Finset.Iic i = insert i (Finset.Iio i) := by ext; simp
    have hprev : (∑ j ∈ Finset.Iio i, f j) = ∑ j ∈ Finset.Iio i, g j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact ih j (Finset.mem_Iio.mp hj)
    have hh := h i
    rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp), hprev] at hh
    omega

def pullGapSet {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) : Finset (GapUniverse r (r+1) (tupleGap p)) :=
  S.map (tupleGapEquiv p hp).symm.toEmbedding

@[simp] theorem mem_pullGapSet {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) (x : GapUniverse r (r+1) (tupleGap p)) :
    x ∈ pullGapSet p hp S ↔ tupleGapMap p x ∈ S := by
  simp [pullGapSet, tupleGapEquiv]

@[simp] theorem map_pullGapSet {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) :
    (pullGapSet p hp S).map (tupleGapEquiv p hp).toEmbedding = S := by
  ext x
  simp only [pullGapSet, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

@[simp] theorem pullGapSet_map {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (T : Finset (GapUniverse r (r+1) (tupleGap p))) :
    pullGapSet p hp (T.map (tupleGapEquiv p hp).toEmbedding) = T := by
  ext x
  simp only [pullGapSet, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem pullGapSet_lower_card {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) (hS : ∀ i, p i ∈ S) (i : Fin r) :
    (S.filter fun x => x < p i).card =
      i.val + ∑ j ∈ Finset.Iic i.castSucc, (gapDecode (pullGapSet p hp S) j).card := by
  have hT : ∀ a, Sum.inl a ∈ pullGapSet p hp S := by
    intro a
    simpa only [mem_pullGapSet, tupleGapMap] using hS a
  have h := gapEncoded_lower_card p hp (gapDecode (pullGapSet p hp S)) i
  rwa [gapEncode_decode _ hT, map_pullGapSet] at h

theorem pullGapSet_total_card {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) (hS : ∀ i, p i ∈ S) :
    S.card = r + ∑ j, (gapDecode (pullGapSet p hp S) j).card := by
  have hT : ∀ a, Sum.inl a ∈ pullGapSet p hp S := by
    intro a
    simpa only [mem_pullGapSet, tupleGapMap] using hS a
  have h := card_gapEncode (r := r) (gapDecode (pullGapSet p hp S))
  rw [gapEncode_decode _ hT] at h
  simpa only [pullGapSet, Finset.card_map] using h

theorem taggedRankEvent_iff_gapEvent {n l r : ℕ} (p : Fin r → Fin n)
    (hp : StrictMono p) (v : Fin r → Fin l) (hv : StrictMono v)
    (S : FixedSubset (Fin n) l) :
    taggedRankEvent p v S ↔ gapEvent (tupleGap v) (pullGapSet p hp S.val) := by
  constructor
  · intro h
    have hS : ∀ i, p i ∈ S.val := fun i => (slotAtRank_eq_iff S (v i) (p i)).mp (h i) |>.1
    have hbefore : ∀ i, (S.val.filter fun x => x < p i).card = (v i).val :=
      fun i => (slotAtRank_eq_iff S (v i) (p i)).mp (h i) |>.2
    refine ⟨?_, ?_⟩
    · intro i
      simpa only [mem_pullGapSet, tupleGapMap] using hS i
    · have heq : (fun j => (gapDecode (pullGapSet p hp S.val) j).card) = tupleGap v := by
        apply fin_prefix_sum_injective
        intro j
        induction j using Fin.lastCases with
        | last =>
          have htot := pullGapSet_total_card p hp S.val hS
          have hvtot := tupleGap_total v hv
          have hset : Finset.Iic (Fin.last r) = Finset.univ := by ext; simp [Fin.le_last]
          rw [hset]
          rw [S.property] at htot
          omega
        | cast i =>
          have hpre := pullGapSet_lower_card p hp S.val hS i
          rw [hbefore i] at hpre
          have hvpre := tupleGap_prefix v hv i
          omega
      intro j
      exact congrFun heq j
  · intro h
    have hS : ∀ i, p i ∈ S.val := by
      intro i
      simpa only [mem_pullGapSet, tupleGapMap] using h.1 i
    intro i
    apply (slotAtRank_eq_iff S (v i) (p i)).2
    refine ⟨hS i, ?_⟩
    rw [pullGapSet_lower_card p hp S.val hS i]
    simp_rw [h.2]
    exact tupleGap_prefix v hv i

/-- The actual event of seeing specified source slots at specified output ranks
is in bijection with independent choices of the retained slots in each gap. -/
def rankGapEventEquiv {n l r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (v : Fin r → Fin l) (hv : StrictMono v) :
    {S : FixedSubset (Fin n) l // taggedRankEvent p v S} ≃
      {T : Finset (GapUniverse r (r+1) (tupleGap p)) // gapEvent (tupleGap v) T} where
  toFun S := ⟨pullGapSet p hp S.val.val, (taggedRankEvent_iff_gapEvent p hp v hv S.val).mp S.property⟩
  invFun T :=
    let S : FixedSubset (Fin n) l := ⟨T.val.map (tupleGapEquiv p hp).toEmbedding, by
      rw [Finset.card_map, card_of_gapEvent T.val T.property, tupleGap_total v hv]⟩
    ⟨S, (taggedRankEvent_iff_gapEvent p hp v hv S).mpr (by
      change gapEvent (tupleGap v) (pullGapSet p hp (T.val.map (tupleGapEquiv p hp).toEmbedding))
      rw [pullGapSet_map]
      exact T.property)⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_pullGapSet p hp S.val.val
  right_inv T := by
    apply Subtype.ext
    exact pullGapSet_map p hp T.val

end TraceReconstruction

namespace TraceReconstruction

/-- Twice the coarse period gaps (endpoints are half-integral before doubling). -/
def coarsePeriodGap {u r : ℕ} (j : Fin r → Fin u) (i : Fin (r+1)) : ℕ :=
  2 * tupleGap j i + if i = 0 ∨ i = Fin.last r then 1 else 2

theorem coarsePeriodGap_sum {u r : ℕ} (hr : 0 < r) (j : Fin r → Fin u)
    (hj : StrictMono j) : ∑ i, coarsePeriodGap j i = 2*u := by
  classical
  have hc : (∑ i : Fin (r+1), if i = 0 ∨ i = Fin.last r then 1 else 2) = 2*r := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    rw [Fin.sum_univ_succ]
    simp only [true_or, ↓reduceIte, Fin.succ_ne_zero, false_or]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_last, ↓reduceIte]
    have hx (i : Fin d) : i.castSucc.succ ≠ Fin.last (d+1) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
      omega
    simp only [hx, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    omega
  simp only [coarsePeriodGap, Finset.sum_add_distrib, ← Finset.mul_sum]
  have ht := tupleGap_total j hj
  omega

theorem coarsePeriodGap_le {u r : ℕ} (hr : 0 < r) (j : Fin r → Fin u)
    (hj : StrictMono j) (i : Fin (r+1)) : coarsePeriodGap j i ≤ 2*u := by
  rw [← coarsePeriodGap_sum hr j hj]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Actual defect slot in a period, with zero-based period and slot indices. -/
def periodSlot {u m : ℕ} (off : Fin u → Fin m) (j : Fin u) : Fin (u*m) :=
  ⟨j.val*m + (off j).val, by
    have h := (off j).isLt
    have h' := Nat.mul_le_mul_right m (Nat.succ_le_of_lt j.isLt)
    nlinarith⟩

end TraceReconstruction

namespace TraceReconstruction

/-- An increasing tuple enumerates a monomial's distinct observed ranks. -/
abbrev IncreasingTuple (n r : ℕ) := {v : Fin r → Fin n // StrictMono v}

noncomputable instance increasingTupleFintype (n r : ℕ) : Fintype (IncreasingTuple n r) :=
  Fintype.ofFinite _

theorem tupleGap_le_remainder {n r : ℕ} (v : IncreasingTuple n r) (i : Fin (r+1)) :
    tupleGap v.val i ≤ n-r := by
  have ht := tupleGap_total v.val v.property
  have hle : tupleGap v.val i ≤ ∑ j, tupleGap v.val j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

def rankGapProfile {n r : ℕ} (σ : Equiv.Perm (Fin (r+1))) (v : IncreasingTuple n r) :
    Fin (r+1) → Fin (n-r+1) :=
  fun i => ⟨tupleGap v.val (σ i), Nat.lt_succ_of_le (tupleGap_le_remainder v (σ i))⟩

end TraceReconstruction


namespace TraceReconstruction

def periodProfile {u r : ℕ} (hr : 0 < r) (σ : Equiv.Perm (Fin (r+1)))
    (j : IncreasingTuple u r) : Fin (r+1) → Fin (2*u+1) :=
  fun i => ⟨coarsePeriodGap j.val (σ i),
    Nat.lt_succ_of_le (coarsePeriodGap_le hr j.val j.property (σ i))⟩

end TraceReconstruction


namespace TraceReconstruction

def LargePeriodTuple (u r : ℕ) (e : Fin (r+1)) :=
  {j : IncreasingTuple u r // 2*u ≤ (r+1)*coarsePeriodGap j.val e}

noncomputable instance largePeriodTupleFintype (u r : ℕ) (e : Fin (r+1)) :
    Fintype (LargePeriodTuple u r e) := by
  unfold LargePeriodTuple
  exact Fintype.ofFinite _

end TraceReconstruction

namespace TraceReconstruction

noncomputable def rankSchurConstant : ℝ :=
  884736 * (2/(1-Real.exp (-(1/1024:ℝ)))) * Real.exp 1

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Differences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differences

Tensor gap differences, positional shifts, two-gap elimination, central clipping, disjoint rank regions, and weighted period sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

namespace TraceReconstruction

/-- Forward length differences of the actual binomial probability
polynomial, before imposing the conditional rank total. -/
def binomialLengthDifference (g s : ℕ) (p : ℝ) : IntSeries :=
  (biasedSeries 1 p - 1)^s * biasedSeries g p

/-- Explicit fixed-order smoothing constant; no asymptotic hypothesis is hidden. -/
def lengthDifferenceConstant (s : ℕ) (p : ℝ) : ℝ :=
  2 * Real.sqrt (((s:ℝ)+1)/(p*(1-p)))

end TraceReconstruction

namespace TraceReconstruction

/-- Product coefficients of signed gap series, including an arbitrary
translation of each observed rank gap. -/
def signedRankProduct {l r : ℕ} (f : Fin (r+1) → IntSeries)
    (shift : Fin (r+1) → ℤ) (v : IncreasingTuple l r) : ℝ :=
  ∏ i, (f i).coeff ((tupleGap v.val i : ℤ)-shift i)

end TraceReconstruction

namespace TraceReconstruction


/-- Embedding one integral exponent into its own gap coordinate. -/
def coordinateExponent {ι : Type*} [DecidableEq ι] (i : ι) : ℤ →+ (ι → ℤ) where
  toFun := fun a => Pi.single (M := fun _ => ℤ) i a
  map_zero' := Pi.single_zero i
  map_add' := fun a b => by
    ext j
    by_cases h : j=i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]

def coordinateSeriesHom {ι : Type*} [DecidableEq ι] (i : ι) :
    IntSeries →+* AddMonoidAlgebra ℝ (ι → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom ℝ (coordinateExponent i)

end TraceReconstruction

namespace TraceReconstruction

inductive GapDifference
  | unchanged | first | second
  deriving DecidableEq

def GapDifference.order : GapDifference → ℕ
  | .unchanged => 0 | .first => 1 | .second => 2

def adjacentGap {r : ℕ} (h : Fin r) (b : Bool) : Fin (r+1) :=
  if b then h.succ else h.castSucc

def gapTermWeight (k : GapDifference) (a : Bool × Bool) : ℝ :=
  match k with
  | .unchanged => 1/4
  | .first => (if a.1 then -1 else 1)/2
  | .second => (if a.1 then -1 else 1)*(if a.2 then -1 else 1)/2

def gapTermOrder {r : ℕ} (h : Fin r) (k : GapDifference) (a : Bool × Bool)
    (i : Fin (r+1)) : ℕ :=
  match k with
  | .unchanged => 0
  | .first => if i = adjacentGap h a.1 then 1 else 0
  | .second => (if i = adjacentGap h a.1 then 1 else 0) +
      (if i = adjacentGap h a.2 then 1 else 0)

def gapTermExtra {r : ℕ} (h : Fin r) (k : GapDifference) (a : Bool × Bool)
    (i : Fin (r+1)) : ℕ :=
  match k with
  | .unchanged => (if i = h.castSucc then 1 else 0) + (if i = h.succ then 1 else 0)
  | .first => if i = adjacentGap h a.2 then 1 else 0
  | .second => 0

/-- Polynomial of a centered positional operator after removing from
both incident gaps the one unit needed for either direction of movement. -/
def gapOperator {r : ℕ} (h : Fin r) (k : GapDifference) (p : ℝ) :
    AddMonoidAlgebra ℝ (Fin (r+1) → ℤ) :=
  let L := coordinateSeriesHom h.castSucc (biasedSeries 1 p)
  let R := coordinateSeriesHom h.succ (biasedSeries 1 p)
  match k with
  | .unchanged => L*R
  | .first => (1/2:ℝ) • (L^2-R^2)
  | .second => (1/2:ℝ) • (L^2+R^2-2*L*R)

end TraceReconstruction



noncomputable section



noncomputable section
namespace TraceReconstruction

/-- Enough vacant slots for independent one-step displacements of every tag. -/
def SafeTaggedTuple {n r : ℕ} (p : Fin r → Fin n) : Prop :=
  (∀ i, 1 ≤ (p i).val ∧ (p i).val+1 < n) ∧
  ∀ i j, i < j → (p i).val+3 ≤ (p j).val

def shiftedTag {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p)
    (a : Fin r → Fin 3) (i : Fin r) : Fin n :=
  ⟨(p i).val+(a i).val-1, by
    have h := hp.1 i
    have ha := (a i).isLt
    omega⟩

def gapIncidence (r : ℕ) (i : Fin (r+1)) : ℕ :=
  Fin.cons (α := fun _ => ℕ) 0 (fun _ : Fin r => 1) i + Fin.snoc (α := fun _ => ℕ) (fun _ : Fin r => 1) 0 i

def shiftGapExtra {r : ℕ} (a : Fin r → Fin 3) (i : Fin (r+1)) : ℕ :=
  Fin.cons (α := fun _ => ℕ) 0 (fun h => 2-(a h).val) i + Fin.snoc (α := fun _ => ℕ) (fun h => (a h).val) 0 i

/-- Literal adjacent-gap allocation of the units used by a displacement.
Value zero means translate left, one leave fixed, two translate right. -/
def localShiftExtra {r : ℕ} (h : Fin r) (a : Fin 3) (i : Fin (r+1)) : ℕ :=
  (if i=h.castSucc then a.val else 0) + (if i=h.succ then 2-a.val else 0)


/-- Coefficients of the unchanged, centered first, and centered second
one-step positional operators. -/
def positionalWeight (k : GapDifference) (a : Fin 3) : ℝ :=
  match k with
  | .unchanged => if a=1 then 1 else 0
  | .first => if a=0 then -1/2 else if a=2 then 1/2 else 0
  | .second => if a=1 then -1 else 1/2


/-- Simultaneous literal positional operators applied to the actual
conditional retained-subset kernel. -/
def positionalRankDifference {n l r : ℕ} (hl : l ≤ n) (p : Fin r → Fin n)
    (hp : SafeTaggedTuple p) (k : Fin r → GapDifference) (v : IncreasingTuple l r) : ℝ :=
  ∑ a : Fin r → Fin 3, (∏ h, positionalWeight (k h) (a h)) *
    subsetRankKernel hl (shiftedTag p hp a) v.val

end TraceReconstruction



noncomputable section



noncomputable section


noncomputable section
namespace TraceReconstruction

/-- Explicit source rank-difference prefactor. It depends on the period
count, slot length, derivative order and Bernoulli parameter, not the
selected period tuple. -/
def periodDifferencePrefactor (u m r d : ℕ) (θ : ℝ) : ℝ :=
  144*((u*m:ℕ):ℝ)*(2:ℝ)^(2*r)*(lengthDifferenceConstant d θ)^(2*d+r+2) /
    (((m:ℝ)/4)^d*Real.sqrt ((u:ℝ)*m/(2*(r+1:ℝ)))*
      (Real.sqrt ((m:ℝ)/4))^(r+1))

end TraceReconstruction

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction

abbrev RemainingCoordinates {ι : Type*} (e d : ι) := {i : ι // i≠e ∧ i≠d}

/-- The fixed involved label is a genuine geometric fiber, not an extra
 analytic hypothesis on the rank kernel. -/
def FixedPeriodTuple (u r : ℕ) (a : Fin r) (h : Fin u) :=
  {j : IncreasingTuple u r // j.val a=h}

noncomputable instance fixedPeriodTupleFintype (u r : ℕ) (a : Fin r) (h : Fin u) :
    Fintype (FixedPeriodTuple u r a h) := by
  unfold FixedPeriodTuple
  exact Fintype.ofFinite _

def fixedPeriodProfile {u r : ℕ} (a : Fin r) (h : Fin u) (j : FixedPeriodTuple u r a h) :
    Fin (r+1) → Fin (2*u+1) := fun i =>
  ⟨coarsePeriodGap j.val.val i, Nat.lt_succ_of_le
    (coarsePeriodGap_le (Nat.zero_lt_of_lt a.isLt) j.val.val j.val.property i)⟩

end TraceReconstruction
noncomputable section
noncomputable section


noncomputable section


noncomputable section


noncomputable section
open scoped Classical
namespace TraceReconstruction

/-- The literal rank-clipping rectangles used in the manuscript, with
 doubled coarse gaps to avoid half-integer natural indices. Only the
 first and internal gaps are needed to determine the period tuple. -/
def PeriodRankRegion {u l r : ℕ} (m : ℕ) (θ : ℝ)
    (j : IncreasingTuple u r) (v : IncreasingTuple l r) : Prop :=
  ∀ i : Fin r, |(tupleGap v.val i.castSucc:ℝ)-
    θ*m*(coarsePeriodGap j.val i.castSucc:ℝ)/2| < (m:ℝ)/8

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

instance instFintypeGapDifference : Fintype GapDifference :=
  ⟨{.unchanged,.first,.second}, by intro k; cases k <;> simp⟩

/-- The sign-dependent displacement in {-1,0,1}, represented by Fin 3. -/
def motifShift (χ β τ : ℝ) : Fin 3 :=
  if χ=0 then 1 else if β*τ=1 then 2 else 0

/-- Coefficients of 1 + χ V + τ β D. -/
def motifDifferenceWeight (χ β τ : ℝ) : GapDifference → ℝ
  | .unchanged => 1 | .first => τ*β | .second => χ

def firstDifferenceCount {r : ℕ} (k : Fin r → GapDifference) : ℕ :=
  (Finset.univ.filter fun h => k h = .first).card

def secondDifferenceCount {r : ℕ} (k : Fin r → GapDifference) : ℕ :=
  (Finset.univ.filter fun h => k h = .second).card

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal support indicator of the length-2^s signed block. -/
def motifIndicator (s : ℕ) (z : ℤ) : ℝ :=
  if 0 ≤ z ∧ z < (2^s : ℕ) then 1 else 0

/-- A kernel-pattern multiplier averaged over the actual finitely supported
 anchor law. No independence of its involved positions is asserted. -/
def motifPatternMultiplier {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (k : Fin r → GapDifference) : ℝ :=
  ∑ X ∈ π.coeff.support, π.coeff X *
    ∏ h, motifDifferenceWeight (motifIndicator s (j h-X))
      ((prouhetSeries s).coeff (j h-X)) 1 (k h)

def linearPattern {r : ℕ} (h : Fin r) (a : Fin r) : GapDifference :=
  if a=h then .first else .unchanged

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Explicit central-anchor summation constant for doubled period gaps. -/
def periodCentralSumConstant (u r : ℕ) : ℝ :=
  ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(2*Real.sqrt (2*u:ℕ))^(r-1)

def periodBoundedSumConstant (u r M : ℕ) : ℝ :=
  ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(M+1)*(2*Real.sqrt (2*u:ℕ))^(r-2)

end TraceReconstruction


namespace TraceReconstruction

/-- A displaced child window as an actual interval of the deterministic
 parent template. `t` is the realized count of atoms before the window. -/
def childWindowIndex {P T : ℕ} (t : ℕ) (hfit : t+T ≤ P) (h : Fin T) : Fin P :=
  ⟨t+h.val, by omega⟩

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialDensity

Defect monomials, orthogonality, normalized initial densities, and common mass.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction
open FiniteLaw

def rankDefectCoefficient {n l u r : ℕ} (hl : l ≤ n) (d : Fin u → Fin n)
    (v : IncreasingTuple l r) : ℝ := by
  classical
  exact (uniformSubsetLaw l (by simpa using hl)).expect (fun S =>
    if ∀ i, slotAtRank S (v.val i) ∈ Set.range d then 1 else 0)

def rankMask {l r : ℕ} (v : IncreasingTuple l r) : Fin l → Bool :=
  fun i => decide (i ∈ Set.range v.val)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open FiniteLaw

/-- Conditional average densities are nonnegative when the coordinate
likelihoods are nonnegative. -/
theorem averagedDensity_nonneg {α Ω : Type*} [Fintype Ω] {n : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) (Z : α → ℝ)
    (hZ : ∀ a, 0 ≤ 1+Z a) (x : Fin n → α) :
    0 ≤ averagedDensity R θ Z x := by
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg (R.nonneg ω)
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact hZ _
  · norm_num

/-- Every independent-score likelihood product is normalized. -/
theorem selectionDensity_mean {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (hZ : P.expect Z = 0) {n : ℕ} (θ : Fin n → Bool) :
    (P.product n).expect (selectionDensity θ Z) = 1 := by
  unfold FiniteLaw.expect FiniteLaw.product selectionDensity
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (a : α) => P.mass a * (if θ i then 1+Z a else 1))]
  apply Finset.prod_eq_one
  intro i _
  cases θ i
  · simp only [Bool.false_eq_true,↓reduceIte,mul_one,P.total]
  · simp only [↓reduceIte,mul_add,mul_one,Finset.sum_add_distrib,P.total]
    exact add_eq_left.mpr hZ

theorem averagedDensity_mean {α Ω : Type*} [Fintype α] [Fintype Ω]
    (P : FiniteLaw α) (R : FiniteLaw Ω) (Z : α → ℝ) (hZ : P.expect Z = 0)
    {n : ℕ} (θ : Ω → Fin n → Bool) :
    (P.product n).expect (averagedDensity R θ Z) = 1 := by
  unfold averagedDensity FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (ω : Ω) : (∑ x : Fin n → α, (P.product n).mass x * (R.mass ω * selectionDensity (θ ω) Z x)) =
      R.mass ω * (P.product n).expect (selectionDensity (θ ω) Z) := by
    rw [FiniteLaw.expect,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [he,selectionDensity_mean P Z hZ,mul_one]
  exact R.total

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patterns

Pattern serialization, motif norms, flag posteriors, signed rank coefficients, translated binomials, and support geometry.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


namespace TraceReconstruction

def pureAtomRun (w : List Bool) (n : ℕ) : List Bool :=
  (List.replicate n w).flatten

end TraceReconstruction


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

/-- Exact orientation law after a report: only invisible bits remain random. -/
def flagPosterior (d : Option Bool) : FiniteLaw Bool where
  mass b := match d with
    | none => 1/2
    | some c => if b=c then 1 else 0
  nonneg := by
    intro b
    cases d with
    | none => norm_num
    | some c => dsimp; split_ifs <;> norm_num
  total := by cases d with
    | none => norm_num [Fintype.sum_bool]
    | some c => simp

def pairedReportMass (P Q H : FiniteLaw α) (ω : ℝ)
    (z : Option Bool × (α × α)) : ℝ :=
  ∑ b : Bool, (1/2 : ℝ)*pairedFlagMass P Q H ω b z

theorem pairedReportMass_nonneg (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω*H.mass a ≤ P.mass a) (hQ : ∀ a, ω*H.mass a ≤ Q.mass a)
    (z : Option Bool × (α × α)) : 0 ≤ pairedReportMass P Q H ω z := by
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (by norm_num) (pairedFlagMass_nonneg P Q H hω hP hQ b z)

theorem pairedReportMass_total (P Q H : FiniteLaw α) (ω : ℝ) :
    (∑ z, pairedReportMass P Q H ω z)=1 := by
  unfold pairedReportMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,pairedFlagMass_sum]
  norm_num [Fintype.sum_bool]

def pairedReport (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω*H.mass a ≤ P.mass a) (hQ : ∀ a, ω*H.mass a ≤ Q.mass a) :
    FiniteLaw (Option Bool × (α × α)) :=
  ⟨pairedReportMass P Q H ω, pairedReportMass_nonneg P Q H hω hP hQ,
    pairedReportMass_total P Q H ω⟩

end TraceReconstruction.FiniteLaw


noncomputable section
namespace TraceReconstruction
open scoped Classical

def bitIndex (b : Bool) : ℕ := if b then 1 else 0

def posteriorBitSeries (d : Option Bool) : IntSeries :=
  ∑ b : Bool, AddMonoidAlgebra.single (bitIndex b : ℤ) ((FiniteLaw.flagPosterior d).mass b)

def visibleOnes (d : Option Bool) : ℕ := if d=some true then 1 else 0

def hiddenTrial (d : Option Bool) : ℕ := if d=none then 1 else 0

theorem posteriorBitSeries_factor (d : Option Bool) :
    posteriorBitSeries d = AddMonoidAlgebra.single (visibleOnes d : ℤ) 1 * fairSeries (hiddenTrial d) := by
  cases d with
  | none => simp [posteriorBitSeries,FiniteLaw.flagPosterior,bitIndex,visibleOnes,hiddenTrial,fairSeries,
      add_comm]
  | some b => cases b <;> simp [posteriorBitSeries,FiniteLaw.flagPosterior,bitIndex,visibleOnes,hiddenTrial,
      fairSeries]

/-- The count distribution of the literal posterior orientation bits is
 a translated fair binomial, including reports of probability zero. -/
theorem posterior_count_series {ι : Type*} [Fintype ι] (d : ι → Option Bool) :
    (∑ b : ι → Bool, AddMonoidAlgebra.single (∑ i, (bitIndex (b i):ℤ))
      (∏ i, (FiniteLaw.flagPosterior (d i)).mass (b i))) =
      AddMonoidAlgebra.single (∑ i, (visibleOnes (d i):ℤ)) 1 *
        fairSeries (∑ i, hiddenTrial (d i)) := by
  have he : (∑ b : ι → Bool, AddMonoidAlgebra.single (∑ i, (bitIndex (b i):ℤ))
      (∏ i, (FiniteLaw.flagPosterior (d i)).mass (b i))) = ∏ i, posteriorBitSeries (d i) := by
    rw [show (∏ i, posteriorBitSeries (d i)) =
      ∏ i, ∑ b : Bool, AddMonoidAlgebra.single (bitIndex b : ℤ) ((FiniteLaw.flagPosterior (d i)).mass b) from rfl]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [AddMonoidAlgebra.prod_single]
  rw [he]
  simp_rw [posteriorBitSeries_factor]
  rw [Finset.prod_mul_distrib,AddMonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one]
  congr 1
  unfold fairSeries
  exact Finset.prod_pow_eq_pow_sum _ _ _

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def signedPeriodDefects {u m : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) : Fin u → Fin (u*m) :=
  shiftedTag (periodSlot (fun _ => off)) hsafe
    (fun j => motifShift (motifIndicator s ((j.val:ℤ)-X)) ((prouhetSeries s).coeff ((j.val:ℤ)-X)) τ)

theorem SafeTaggedTuple.comp {n u r : ℕ} {p : Fin u → Fin n}
    (hp : SafeTaggedTuple p) (j : Fin r → Fin u) (hj : StrictMono j) :
    SafeTaggedTuple (p ∘ j) :=
  ⟨fun i => hp.1 (j i),fun i k hik => hp.2 (j i) (j k) (hj hik)⟩

/-- Exact degree-r coefficient difference of the actual randomized motif
 in the marked central run, prior to any rank clipping. -/
def signedRankCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (v : IncreasingTuple l r) : ℝ :=
  ∑ X ∈ π.coeff.support, π.coeff X *
    (rankDefectCoefficient hl (signedPeriodDefects off hsafe s X 1) v -
     rankDefectCoefficient hl (signedPeriodDefects off hsafe s X (-1)) v)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def translateSeries (c : ℤ) (f : IntSeries) : IntSeries :=
  AddMonoidAlgebra.single c 1*f

theorem translateSeries_coeff (c : ℤ) (f : IntSeries) (z : ℤ) :
    (translateSeries c f).coeff z = f.coeff (z-c) := by
  rw [translateSeries,AddMonoidAlgebra.coeff_single_mul_apply,one_mul]
  congr 1; omega

theorem translated_binomial_nonneg (g : ℕ) (c z : ℤ) :
    0≤(translateSeries c (fairSeries g)).coeff z := by
  rw [translateSeries_coeff]
  exact fairSeries_nonneg _ _

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A support criterion obtained from the actual side-count range. -/
def CentralMotifSupport (u s : ℕ) (π : IntSeries) : Prop :=
  ∀X∈π.coeff.support,
    (u:ℝ)/3≤2*(X:ℝ)+1 ∧ (u:ℝ)/3≤2*u-(2*((X:ℝ)+(2:ℝ)^s)+1)

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialMoments

Initial coefficient tails, primitive conditioning, mark-list oracle densities, pure norm estimates, and moment energies.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

def signedTupleKernel {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (j : IncreasingTuple u r) (v : IncreasingTuple l r) : ℝ :=
  ∑X∈π.coeff.support, π.coeff X*
    (subsetRankKernel hl (signedPeriodDefects off hsafe s X 1 ∘ j.val) v.val -
     subsetRankKernel hl (signedPeriodDefects off hsafe s X (-1) ∘ j.val) v.val)

def clippedSignedRankCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (v : IncreasingTuple l r) : ℝ :=
  ∑j, if PeriodRankRegion m θ j v then signedTupleKernel hl off hsafe π s j v else 0

def clippedPatternCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (k : Fin r → GapDifference) (v : IncreasingTuple l r) : ℝ :=
  ∑j, if PeriodRankRegion m θ j v then
    motifPatternMultiplier π s (fun i => (j.val i).val) k *
      positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
        (hsafe.comp j.val j.property) k v else 0

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

def signedPatternBound (u m r s : ℕ) (π : IntSeries) (θ : ℝ)
    (k : Fin r → GapDifference) : ℝ :=
  if ∃a, k=linearPattern a then
    periodDifferencePrefactor u m r 1 θ * periodCentralSumConstant u r * seriesL2Sq (prouhetSeries s*π)
  else periodDifferencePrefactor u m r (∑h, (k h).order) θ *
    periodBoundedSumConstant u r (2*(2^s)) * seriesL2Sq (geomSeries (2^s)*π)

end TraceReconstruction
noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact complete-trace expectation, recursively on the actual binary word. -/
def listDeletionExpectation (q : ℝ) : List Bool → (List Bool → ℝ) → ℝ
  | [], F => F []
  | b::w, F => q*listDeletionExpectation q w F +
      (1-q)*listDeletionExpectation q w (fun t => F (b::t))

theorem traceOfMask_cons {n : ℕ} (x : Word (n+1)) (b : Bool) (a : Mask n) :
    traceOfMask x (Fin.cons b a)=
      if b then x 0::traceOfMask (fun i => x i.succ) a
      else traceOfMask (fun i => x i.succ) a := by
  rw [trace_filterMap,List.ofFn_succ,trace_filterMap]
  cases b <;> simp

theorem maskWeight_cons {n : ℕ} (q : ℝ) (b : Bool) (a : Mask n) :
    maskWeight q (Fin.cons b a)=(if b then 1-q else q)*maskWeight q a := by
  simp [maskWeight,Fin.prod_univ_succ]

theorem listDeletionExpectation_ofFn {n : ℕ} (q : ℝ) (x : Word n) (F : List Bool → ℝ) :
    listDeletionExpectation q (List.ofFn x) F =
      ∑a : Mask n, maskWeight q a*F (traceOfMask x a) := by
  induction n generalizing F with
  | zero => simp [listDeletionExpectation,maskWeight,traceOfMask]
  | succ n ih =>
    rw [List.ofFn_succ,listDeletionExpectation,ih,ih]
    symm
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp,Fintype.sum_prod_type]
    change (∑b : Bool, ∑a : Mask n, maskWeight q (Fin.cons b a)*F (traceOfMask x (Fin.cons b a)))=_
    simp_rw [maskWeight_cons,traceOfMask_cons]
    simp only [Bool.false_eq_true,ite_false,ite_true,Fintype.sum_bool]
    simp only [mul_assoc,← Finset.mul_sum]
    ring

theorem listDeletionExpectation_append (q : ℝ) (x y : List Bool) (F : List Bool → ℝ) :
    listDeletionExpectation q (x++y) F =
      listDeletionExpectation q x (fun t => listDeletionExpectation q y (fun u => F (t++u))) := by
  induction x generalizing F with
  | nil => simp [listDeletionExpectation]
  | cons b x ih => simp only [List.cons_append,listDeletionExpectation,ih]

/-- The primitive alphabet consists of the literal strings 01 and 1. -/
def primitiveBlock (b : Bool) : List Bool := if b then [true] else [false,true]

/-- Independent silent block erasures and conditionally emitted primitive marks.
 An emitted empty mark is retained in the list and differs from a silent erasure. -/
def silentMarkExpectation (q : ℝ) : List Bool → (List PrimitiveMark → ℝ) → ℝ
  | [], F => F []
  | b::bs, F => primitiveErasure q*silentMarkExpectation q bs F +
      (1-primitiveErasure q)*∑z : PrimitiveMark, primitiveMarkMass q b z*
        silentMarkExpectation q bs (fun ys => F (z::ys))

def joinPrimitiveMarks (ys : List PrimitiveMark) : List Bool := (ys.map primitiveOutput).flatten

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Every emitted mark is counted, including the empty primitive output. -/
def emittedMarkExpectation (q : ℝ) : List Bool → (List PrimitiveMark → ℝ) → ℝ
  | [], F => F []
  | b::bs, F => ∑z : PrimitiveMark, primitiveMarkMass q b z*
      emittedMarkExpectation q bs (fun ys => F (z::ys))

def maskSubset {n : ℕ} (a : Mask n) : Finset (Fin n) := Finset.univ.filter fun i => a i

def maskSubsetEquiv (n : ℕ) : Mask n ≃ Finset (Fin n) where
  toFun := maskSubset
  invFun S i := decide (i∈S)
  left_inv a := by funext i; simp [maskSubset]
  right_inv S := by ext i; simp [maskSubset]

def cardinalSubsetEquiv (n : ℕ) : Finset (Fin n) ≃ Σl : Fin (n+1), FixedSubset (Fin n) l.val where
  toFun S := ⟨⟨S.card, by have := Finset.card_le_univ S; simpa using Nat.lt_succ_of_le this⟩,⟨S,rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨l,hl⟩,⟨S,hS⟩⟩
    dsimp
    change S.card=l at hS
    subst l
    rfl

/-- The literal conditional-list oracle used by the rank coefficients. -/
def conditionalPrimitiveLaw {n l : ℕ} (hl : l ≤ n) (q : ℝ) (hq : q∈Set.Ioo 0 1)
    (θ : Fin n → Bool) : FiniteLaw (Fin l → PrimitiveMark) :=
  (uniformSubsetLaw l (by simpa using hl)).mixture fun S =>
    FiniteLaw.coordinateProduct (fun v => primitiveMarkLaw q hq (θ (slotAtRank S v)))

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Density of the actual uniform-subset primitive oracle, over the ordinary
 mark product law. This is exactly the channel defined by silent erasures. -/
theorem conditionalPrimitiveLaw_density {n l : ℕ} (hl : l ≤ n)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (θ : Fin n → Bool) (x : Fin l → PrimitiveMark) :
    (conditionalPrimitiveLaw hl q hq θ).mass x =
      ((primitiveMarkLaw q hq false).product l).mass x *
        averagedDensity (uniformSubsetLaw l (by simpa using hl))
          (fun S v => θ (slotAtRank S v)) (primitiveScore q) x := by
  have he : (fun S : FixedSubset (Fin n) l =>
      FiniteLaw.coordinateProduct (fun v => primitiveMarkLaw q hq (θ (slotAtRank S v)))) =
      (fun S : FixedSubset (Fin n) l =>
      FiniteLaw.coordinateProduct (fun v => if θ (slotAtRank S v) then
        primitiveMarkLaw q hq true else primitiveMarkLaw q hq false)) := by
    funext S
    congr 1
    funext v
    cases θ (slotAtRank S v) <;> rfl
  unfold conditionalPrimitiveLaw
  rw [he]
  exact leaf_oracle_density (primitiveMarkLaw q hq false) (primitiveMarkLaw q hq true)
    (primitiveScore q) (primitive_score_identity hq)
    (uniformSubsetLaw l (by simpa using hl)) (fun S v => θ (slotAtRank S v)) x

def defectTypes {n u : ℕ} (d : Fin u → Fin n) (i : Fin n) : Bool := decide (i∈Set.range d)

theorem defectTypes_atRank {n l u : ℕ} (d : Fin u → Fin n) (S : FixedSubset (Fin n) l) :
    (fun v => defectTypes d (slotAtRank S v))=defectAtRank (Finset.univ.image d) S := by
  funext v
  simp [defectTypes,defectAtRank,Set.mem_range]

theorem conditionalDefectLaw_density {n l u : ℕ} (hl : l ≤ n)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (d : Fin u → Fin n) (x : Fin l → PrimitiveMark) :
    (conditionalPrimitiveLaw hl q hq (defectTypes d)).mass x =
      ((primitiveMarkLaw q hq false).product l).mass x *
        multilinear (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
          (defectAtRank (Finset.univ.image d))) (primitiveScore q) x := by
  rw [conditionalPrimitiveLaw_density,show (fun S v => defectTypes d (slotAtRank S v))=
      defectAtRank (Finset.univ.image d) by funext S; exact defectTypes_atRank d S,
      averagedDensity_expansion]

/-- The finite-support law of the hidden motif anchor, not an additional
 distributional assumption or a changed channel parameter. -/
def seriesProbabilityLaw (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X)
    (hπsum : ∑X∈π.coeff.support, π.coeff X=1) : FiniteLaw ↥π.coeff.support where
  mass X := π.coeff X.val
  nonneg X := hπ X.val
  total := by simpa only [Finset.univ_eq_attach,Finset.sum_attach] using hπsum

def mixedMotifCoefficient {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (τ : ℝ) (σ : Fin l → Bool) : ℝ :=
  ∑X∈π.coeff.support, π.coeff X*
    averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
      (defectAtRank (Finset.univ.image (signedPeriodDefects off hsafe s X τ))) σ

def conditionalMotifLaw {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X)
    (hπsum : ∑X∈π.coeff.support, π.coeff X=1) (s : ℕ) (τ : ℝ) :
    FiniteLaw (Fin l → PrimitiveMark) :=
  (seriesProbabilityLaw π hπ hπsum).mixture fun X =>
    conditionalPrimitiveLaw hl q hq (defectTypes (signedPeriodDefects off hsafe s X.val τ))

theorem conditionalMotifLaw_density {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X)
    (hπsum : ∑X∈π.coeff.support, π.coeff X=1) (s : ℕ) (τ : ℝ) (x : Fin l → PrimitiveMark) :
    (conditionalMotifLaw hl off hsafe hq π hπ hπsum s τ).mass x=
      ((primitiveMarkLaw q hq false).product l).mass x *
        multilinear (mixedMotifCoefficient hl off hsafe π s τ) (primitiveScore q) x := by
  unfold conditionalMotifLaw FiniteLaw.mixture seriesProbabilityLaw
  simp_rw [conditionalDefectLaw_density]
  let F : ℤ → ℝ := fun X => π.coeff X *
    (((primitiveMarkLaw q hq false).product l).mass x *
      multilinear (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (signedPeriodDefects off hsafe s X τ))))
        (primitiveScore q) x)
  change (∑ X : ↥π.coeff.support, F X.val) = _
  rw [Finset.sum_coe_sort]
  dsimp only [F]
  unfold mixedMotifCoefficient multilinear
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X _
  ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def unchangedPattern (r : ℕ) : Fin r → GapDifference := fun _ => .unchanged

def purePatternBound (u m r s : ℕ) (π : IntSeries) (θ : ℝ)
    (k : Fin r → GapDifference) : ℝ :=
  if ∃a, k=linearPattern a then
    periodDifferencePrefactor u m r 1 θ * periodCentralSumConstant u r * seriesL2Sq (prouhetSeries s*π)
  else periodDifferencePrefactor u m r (∑h, (k h).order) θ *
    periodCentralSumConstant u r * seriesL2Sq (geomSeries (2^s)*π)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def pureRankCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (v : IncreasingTuple l r) : ℝ :=
  ∑X∈π.coeff.support, π.coeff X *
    (rankDefectCoefficient hl (signedPeriodDefects off hsafe s X 1) v -
     rankDefectCoefficient hl (periodSlot (fun _ => off)) v)

def pureTupleKernel {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (j : IncreasingTuple u r) (v : IncreasingTuple l r) : ℝ :=
  ∑X∈π.coeff.support, π.coeff X *
    (subsetRankKernel hl (signedPeriodDefects off hsafe s X 1 ∘ j.val) v.val -
     subsetRankKernel hl (periodSlot (fun _ => off) ∘ j.val) v.val)

def clippedPureRankCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (v : IncreasingTuple l r) : ℝ :=
  ∑j, if PeriodRankRegion m θ j v then pureTupleKernel hl off hsafe π s j v else 0

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def scaleCoefficient {n : ℕ} (A : (Fin n → Bool) → ℝ) (L : ℝ) (σ : Fin n → Bool) : ℝ :=
  A σ * ∏ i, if σ i then L else 1

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Oracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oracles

TV kernels and trace simulation, anchor costs, counted primitives, common-part lifting, concrete oracle pairs, and paired-flag metadata.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem law_ext {P Q : FiniteLaw α} (h : ∀a,P.mass a=Q.mass a) : P=Q := by
  cases P; cases Q; congr; exact funext h

theorem tv_le_one (P Q : FiniteLaw α) : P.tv Q≤1 := by
  unfold tv
  have h : (∑a,|P.mass a-Q.mass a|)≤2 := by
    calc
      _ ≤ ∑a, (P.mass a+Q.mass a) := Finset.sum_le_sum (fun a _ =>
        (abs_sub (P.mass a) (Q.mass a)).trans_eq (by rw [abs_of_nonneg (P.nonneg a),abs_of_nonneg (Q.nonneg a)]))
      _ = 2 := by rw [Finset.sum_add_distrib,P.total,Q.total]; norm_num
  linarith

theorem tv_prod_eq_left (P Q : FiniteLaw α) (R : FiniteLaw β) :
    (P.prod R).tv (Q.prod R)=P.tv Q := by
  unfold tv prod
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [← sub_mul,abs_mul,abs_of_nonneg (R.nonneg _),← Finset.mul_sum,R.total,mul_one]

end TraceReconstruction.FiniteLaw


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem expect_coordinateProduct_succ {n : ℕ} (P : Fin (n+1) → FiniteLaw α)
    (F : (Fin (n+1) → α) → ℝ) :
    (coordinateProduct P).expect F =
      (P 0).expect (fun a => (coordinateProduct (fun i => P i.succ)).expect
        (fun x => F (Fin.cons a x))) := by
  change (∑x : Fin (n+1) → α, (∏i,(P i).mass (x i))*F x)=
    ∑a : α, (P 0).mass a*(∑x : Fin n → α, (∏i,(P i.succ).mass (x i))*F (Fin.cons a x))
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp,Fintype.sum_prod_type]
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  simp_rw [Finset.mul_sum,mul_assoc]

end TraceReconstruction.FiniteLaw


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem FiniteLaw.expect_sub {α : Type*} [Fintype α] (P : FiniteLaw α)
    (F G : α → ℝ) : P.expect (fun a => F a-G a)=P.expect F-P.expect G := by
  simp only [FiniteLaw.expect,mul_sub,Finset.sum_sub_distrib]

theorem FiniteLaw.abs_expect_le {α : Type*} [Fintype α] (P : FiniteLaw α) (F : α → ℝ) :
    |P.expect F|≤P.expect (fun a => |F a|) := by
  simpa only [FiniteLaw.expect,abs_mul,abs_of_nonneg (P.nonneg _)] using
    Finset.abs_sum_le_sum_abs (fun a => P.mass a*F a) Finset.univ

/-- A finite auxiliary observation, decoded by a fixed function, simulates the
usual deletion channel on a literal binary word. Test functions range over the
observable traces only, never latent boundaries. -/
def SimulatesTrace {α : Type*} [Fintype α] (q : ℝ) (P : FiniteLaw α)
    (decode : α → List Bool) (w : List Bool) : Prop :=
  ∀ F : List Bool → ℝ, P.expect (fun a => F (decode a))=listDeletionExpectation q w F

def ApproximatesTrace {α : Type*} [Fintype α] (q : ℝ) (P : FiniteLaw α)
    (decode : α → List Bool) (w : List Bool) (E : ℝ) : Prop :=
  ∀ F : List Bool → ℝ, (∀t,F t∈Set.Icc 0 1) →
    |P.expect (fun a => F (decode a))-listDeletionExpectation q w F|≤E

theorem listDeletionExpectation_const (q c : ℝ) (w : List Bool) :
    listDeletionExpectation q w (fun _ => c)=c := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [listDeletionExpectation,ih]; ring

theorem listDeletionExpectation_mono {q : ℝ} (hq : q∈Set.Icc 0 1)
    (w : List Bool) {F G : List Bool → ℝ} (h : ∀t,F t≤G t) :
    listDeletionExpectation q w F≤listDeletionExpectation q w G := by
  induction w generalizing F G with
  | nil => exact h []
  | cons b w ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (ih h) hq.1)
      (mul_le_mul_of_nonneg_left (ih (fun t => h (b::t))) (sub_nonneg.mpr hq.2))

theorem listDeletionExpectation_range {q : ℝ} (hq : q∈Set.Icc 0 1)
    (w : List Bool) (F : List Bool → ℝ) (hF : ∀t,F t∈Set.Icc 0 1) :
    listDeletionExpectation q w F∈Set.Icc 0 1 := by
  constructor
  · simpa only [listDeletionExpectation_const] using
      listDeletionExpectation_mono hq w (fun t => (hF t).1)
  · simpa only [listDeletionExpectation_const] using
      listDeletionExpectation_mono hq w (fun t => (hF t).2)

theorem SimulatesTrace.approximate {α : Type*} [Fintype α]
    {q : ℝ} {P : FiniteLaw α} {f : α → List Bool} {w : List Bool}
    (h : SimulatesTrace q P f w) : ApproximatesTrace q P f w 0 := by
  intro F _
  rw [h,sub_self,abs_zero]

theorem ApproximatesTrace.append {α β : Type*} [Fintype α] [Fintype β]
    {q : ℝ} (hq : q∈Set.Icc 0 1) {P : FiniteLaw α} {Q : FiniteLaw β}
    {f : α → List Bool} {g : β → List Bool} {x y : List Bool} {E D : ℝ}
    (hP : ApproximatesTrace q P f x E) (hQ : ApproximatesTrace q Q g y D) :
    ApproximatesTrace q (P.prod Q) (fun a => f a.1++g a.2) (x++y) (E+D) := by
  intro F hF
  rw [FiniteLaw.expect_prod,listDeletionExpectation_append]
  let H : List Bool → ℝ := fun t => listDeletionExpectation q y (fun u => F (t++u))
  have hH : ∀t,H t∈Set.Icc 0 1 := fun t => listDeletionExpectation_range hq y _ (fun u => hF (t++u))
  have h1 := hP H hH
  have h2 : |P.expect (fun a => Q.expect (fun b => F (f a++g b)))-P.expect (fun a => H (f a))|≤D := by
    rw [← FiniteLaw.expect_sub]
    calc
      _ ≤ P.expect (fun a => |Q.expect (fun b => F (f a++g b))-H (f a)|) := FiniteLaw.abs_expect_le _ _
      _ ≤ P.expect (fun _ => D) := FiniteLaw.expect_mono _ (fun a => hQ _ (fun t => hF (f a++t)))
      _ = D := FiniteLaw.expect_const _ _
  exact (abs_sub_le _ _ _).trans (by linarith only [h1,h2])

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Admissible close child labels, without relaxing any plateau restrictions
on the anchor. An arbitrary finite label domain is retained. -/
def closeLabels (A : Finset ℤ) (L : ℕ) (a : ℤ) : Finset ℤ :=
  A.filter (fun c => |c-a| < (L:ℤ))

def binaryTreeBudget (C : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => C n*(binaryTreeBudget C n)^2

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sum_range_extend_zero {f : ℕ→ℝ} {m n : ℕ} (hmn : m≤n)
    (hz : ∀k,m≤k→f k=0) : ∑k∈Finset.range n,f k=∑k∈Finset.range m,f k := by
  symm
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro k _ hk
  exact hz k (by simpa using hk)

theorem hypergeomMass_above_total (V M m v : ℕ) (h : m<v) :
    hypergeomMass V M m v=0 := by simp only [hypergeomMass,ite_eq_right (by omega : ¬v≤ m)]

def hypergeomLaw (V M m : ℕ) (hm : m≤V+M) : FiniteLaw (Fin (V+M+1)) where
  mass v := hypergeomMass V M m v
  nonneg _ := hypergeomMass_nonneg _ _ _ _
  total := by
    rw [Fin.sum_univ_eq_sum_range]
    rw [sum_range_extend_zero (Nat.add_le_add_right hm 1) (fun k hk =>
      hypergeomMass_above_total V M m k (by omega))]
    exact sum_hypergeomMass V M m hm

end TraceReconstruction
noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem expect_map (P : FiniteLaw α) (f : α→β) (G : β→ℝ) :
    (P.map f).expect G=P.expect (G∘f) := expectation_map P f G

end FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

def fixedSubsetEquiv (e : α≃β) (m : ℕ) : FixedSubset α m ≃ FixedSubset β m where
  toFun S := ⟨S.val.map e.toEmbedding,by simpa only [Finset.card_map] using S.property⟩
  invFun T := ⟨T.val.map e.symm.toEmbedding,by simpa only [Finset.card_map] using T.property⟩
  left_inv S := by apply Subtype.ext; exact e.finsetCongr.left_inv S.val
  right_inv T := by apply Subtype.ext; exact e.finsetCongr.right_inv T.val

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

abbrev HiddenIndex (H : Finset α) := {a : α // a∈H}
abbrev VisibleIndex (H : Finset α) := {a : α // a∉H}

def splitIndexEquiv (H : Finset α) : VisibleIndex H⊕HiddenIndex H ≃ α :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl (fun a => a∈H))

theorem card_splitIndex (H : Finset α) :
    Fintype.card (VisibleIndex H)+Fintype.card (HiddenIndex H)=Fintype.card α := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (splitIndexEquiv H)

def eraseScheduleLaw (H : Finset α) (m : ℕ) (hm : m≤Fintype.card α) : FiniteLaw (Finset α) :=
  (uniformSubsetLaw m hm).map (fun S => S.val\H)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]

def sigma (P : FiniteLaw ι) (K : ∀i, FiniteLaw (β i)) : FiniteLaw (Σi,β i) where
  mass a:=P.mass a.1*(K a.1).mass a.2
  nonneg a:=mul_nonneg (P.nonneg _) ((K _).nonneg _)
  total:=by
    rw [Fintype.sum_sigma]
    simp_rw [←Finset.mul_sum,(K _).total,mul_one]
    exact P.total

theorem expect_sigma (P : FiniteLaw ι) (K : ∀i,FiniteLaw (β i)) (F : (Σi,β i)→ℝ) :
    (P.sigma K).expect F=P.expect (fun i => (K i).expect (fun b => F ⟨i,b⟩)) := by
  simp only [expect,sigma,Fintype.sum_sigma,Finset.mul_sum,mul_assoc]

end FiniteLaw

theorem sum_binomialMass_cutoff {n N : ℕ} (hn : n≤N) (p : ℝ) :
    ∑l : Fin (N+1),binomialMass n p l.val=1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => binomialMass n p k) (N+1)]
  rw [←sum_binomialMass n p]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k _ hk
  have hn' : n<k := by simp only [Finset.mem_range] at hk; omega
  simp [binomialMass,Nat.choose_eq_zero_of_lt hn']

def boundedCountLaw {n N : ℕ} (hn : n≤N) (p : ℝ) (hp : p∈Set.Icc 0 1) : FiniteLaw (Fin (N+1)) where
  mass l:=binomialMass n p l.val
  nonneg l:=binomialMass_nonneg n l.val hp
  total:=sum_binomialMass_cutoff hn p

abbrev BoundedMarks (N : ℕ) := Σl : Fin (N+1),Fin l.val→PrimitiveMark

def boundedConditionalPrimitiveLaw {n N : ℕ} {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (θ : Fin n→Bool) (l : Fin (N+1)) : FiniteLaw (Fin l.val→PrimitiveMark) :=
  if h : l.val≤n then conditionalPrimitiveLaw h q hq θ else (primitiveMarkLaw q hq false).product l.val

theorem primitiveRetention_mem {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    1-primitiveErasure q∈Set.Icc 0 1 := by
  constructor
  · exact (primitive_retain_pos hq).le
  · unfold primitiveErasure; nlinarith [sq_nonneg q]

def countedPrimitiveLaw {n N : ℕ} (hn : n≤N) {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (θ : Fin n→Bool) : FiniteLaw (BoundedMarks N) :=
  (boundedCountLaw hn (1-primitiveErasure q) (primitiveRetention_mem hq)).sigma
    (boundedConditionalPrimitiveLaw hq θ)

def decodeBoundedMarks {N : ℕ} (a : BoundedMarks N) : List Bool := joinPrimitiveMarks (List.ofFn a.2)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

def hiddenScheduleLaw (p : ℝ) (hp : p∈Set.Icc 0 1) (m : ℕ) (hm : m≤Fintype.card α) :
    FiniteLaw (Finset α×Finset α) :=
  (subsetLaw p hp).bind (fun H => (eraseScheduleLaw H m hm).map (fun S => (H,S)))

end TraceReconstruction
noncomputable section

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

def schedulePayload {n : ℕ} (U P Q : FiniteLaw α) (z : Finset (Fin n)×Finset (Fin n)) :
    FiniteLaw (Fin n→α) :=
  FiniteLaw.coordinateProduct (fun i => if i∈z.1 then U else if i∈z.2 then Q else P)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

def coordinateWord {n : ℕ} (w : Fin n→List Bool) : List Bool := (List.ofFn w).flatten

theorem coordinateWord_succ {n : ℕ} (w : Fin (n+1)→List Bool) :
    coordinateWord w=w 0++coordinateWord (fun i => w i.succ) := by
  simp only [coordinateWord,List.ofFn_succ,List.flatten_cons]

end TraceReconstruction
noncomputable section
universe u



/-!
Concrete objects for the scale inequalities, Definition 3 (the level invariant).
The observable channel remains the complete deletion trace of a literal word.
-/
noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α : Type*} [Fintype α]

/-- The maximizing test for total variation on a finite sample space. -/
theorem tv_eq_positive_test (P Q : FiniteLaw α) :
    P.tv Q = P.expect (fun a => if Q.mass a ≤ P.mass a then 1 else 0) -
      Q.expect (fun a => if Q.mass a ≤ P.mass a then 1 else 0) := by
  have hz : (∑ a, (P.mass a - Q.mass a)) = 0 := by
    rw [Finset.sum_sub_distrib, P.total, Q.total, sub_self]
  have he (a : α) :
      |P.mass a-Q.mass a|+(P.mass a-Q.mass a) =
        2*((P.mass a-Q.mass a)*(if Q.mass a ≤ P.mass a then 1 else 0)) := by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]; ring
  have hs := congrArg (fun f : α → ℝ => ∑ a, f a) (funext he)
  simp only [Finset.sum_add_distrib, hz, add_zero, ← Finset.mul_sum] at hs
  simp only [tv, expect]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  linarith only [hs]

/-- Dual characterization, sufficient for simulators with different latent spaces. -/
theorem tv_le_of_tests (P Q : FiniteLaw α) {E : ℝ}
    (h : ∀ f : α → ℝ, (∀ a, f a ∈ Set.Icc 0 1) →
      P.expect f-Q.expect f ≤ E) : P.tv Q ≤ E := by
  rw [tv_eq_positive_test]
  exact h _ (fun a => by split_ifs <;> norm_num)

theorem abs_expect_sub_le_tv (P Q : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ a, f a ∈ Set.Icc 0 1) : |P.expect f-Q.expect f| ≤ P.tv Q := by
  apply abs_le.mpr
  constructor
  · have h := expectation_diff_le_tv Q P f hf
    rw [tv_symm Q P] at h
    change Q.expect f-P.expect f ≤ P.tv Q at h
    linarith
  · exact expectation_diff_le_tv P Q f hf
end FiniteLaw

/-- The genuine complete-trace law embedded in a specified finite trace space.
The extra elements have mass zero, not a cemetery mass. -/
def listTraceLaw (q : ℝ) (hq : q ∈ Set.Icc 0 1) (w : List Bool)
    (M : ℕ) (hw : w.length ≤ M) : FiniteLaw (BoundedTrace M) :=
  (maskLaw (n:=w.length) q hq).map (fun a =>
    ⟨traceOfMask w.get a, mem_traceSpace_of_length_le _
      ((traceOfMask_length_le w.get a).trans hw)⟩)

theorem listTraceLaw_expect (q : ℝ) (hq : q ∈ Set.Icc 0 1) (w : List Bool)
    (M : ℕ) (hw : w.length ≤ M) (F : List Bool → ℝ) :
    (listTraceLaw q hq w M hw).expect (fun a => F a.val) =
      listDeletionExpectation q w F := by
  rw [listTraceLaw, FiniteLaw.expect_map]
  have h := listDeletionExpectation_ofFn q w.get F
  rw [List.ofFn_get] at h
  exact h.symm

theorem listTraceLaw_simulates (q : ℝ) (hq : q ∈ Set.Icc 0 1) (w : List Bool)
    (M : ℕ) (hw : w.length ≤ M) :
    SimulatesTrace q (listTraceLaw q hq w M hw) Subtype.val w :=
  listTraceLaw_expect q hq w M hw

/-- Ordinary overlap of complete traces, including unequal input lengths. -/
def listTraceOverlap (q : ℝ) (hq : q ∈ Set.Icc 0 1) (x y : List Bool) : ℝ :=
  let M := max x.length y.length
  FiniteLaw.overlap (listTraceLaw q hq x M (le_max_left _ _))
    (listTraceLaw q hq y M (le_max_right _ _))

/-- Common approximate simulation transfers distinguishability to genuine
complete traces, without revealing the latent partition. -/
theorem approximations_trace_tv {α : Type*} [Fintype α]
    {q : ℝ} (hq : q ∈ Set.Icc 0 1) (P Q : FiniteLaw α) (decode : α → List Bool)
    (x y : List Bool) (Ex Ey : ℝ) (M : ℕ) (hx : x.length ≤ M) (hy : y.length ≤ M)
    (hP : ApproximatesTrace q P decode x Ex)
    (hQ : ApproximatesTrace q Q decode y Ey) :
    (listTraceLaw q hq x M hx).tv (listTraceLaw q hq y M hy) ≤ P.tv Q+Ex+Ey := by
  apply FiniteLaw.tv_le_of_tests
  intro f hf
  let F : List Bool → ℝ := fun t => if h : t ∈ traceSpace M then f ⟨t,h⟩ else 0
  have hF : ∀ t, F t ∈ Set.Icc 0 1 := by
    intro t
    dsimp [F]
    split_ifs with h
    · exact hf ⟨t,h⟩
    · norm_num
  have hFx : (listTraceLaw q hq x M hx).expect f = listDeletionExpectation q x F := by
    rw [← listTraceLaw_expect q hq x M hx F]
    congr 1
    funext t
    simp only [F, dite_eq_left t.property]
  have hFy : (listTraceLaw q hq y M hy).expect f = listDeletionExpectation q y F := by
    rw [← listTraceLaw_expect q hq y M hy F]
    congr 1
    funext t
    simp only [F, dite_eq_left t.property]
  rw [hFx,hFy]
  have hp := hP F hF
  have hq' := hQ F hF
  have ht := FiniteLaw.abs_expect_sub_le_tv P Q (fun a => F (decode a)) (fun a => hF _)
  linarith [le_abs_self (P.expect (fun a => F (decode a))-Q.expect (fun a => F (decode a))),
    (abs_le.mp hp).1, (abs_le.mp hp).2, (abs_le.mp hq').1, (abs_le.mp hq').2]

/-- A literal witness of the source level invariant. `halfOrder` is half its
positive even moment order. `countFactor` is the prescribed upper multiplier
`C^(2*B*i+O_B(1))`, to be instantiated uniformly in the actual construction.
Finite outcomes suffice for the source's finite latent experiments, and any
randomized common decoder can be included as an additional latent draw. -/
structure ConcreteLevelPair (q : ℝ) (hq : q ∈ Set.Icc 0 1)
    (N Δ d ω countFactor : ℝ) (i halfOrder : ℕ) where
  left : List Bool
  right : List Bool
  equalLength : left.length = right.length
  different : left ≠ right
  length_lower : N/2 ≤ (left.length : ℝ)
  length_upper : (left.length : ℝ) ≤ N
  Outcome : Type
  finiteOutcome : Fintype Outcome
  firstLaw : @FiniteLaw Outcome finiteOutcome
  secondLaw : @FiniteLaw Outcome finiteOutcome
  decode : Outcome → List Bool
  error : ℝ
  error_nonneg : 0 ≤ error
  normalized_error : error/(left.length : ℝ) ≤ ((i:ℝ)+1)*Δ
  first_simulation : @ApproximatesTrace Outcome finiteOutcome q firstLaw decode left error
  second_simulation : @ApproximatesTrace Outcome finiteOutcome q secondLaw decode right error
  score : Outcome → ℝ
  density : ∀ a, secondLaw.mass a = firstLaw.mass a*(1+score a)
  score_bound : @FiniteLaw.evenMomentSq Outcome finiteOutcome firstLaw score halfOrder ≤ N ^ (-d)
  overlapCount : ℕ
  overlapCount_lower : left.length ≤ overlapCount
  overlapCount_upper : (overlapCount:ℝ) ≤ countFactor*(left.length:ℝ)
  power_overlap : ω ≤ listTraceOverlap q hq (pureAtomRun left overlapCount)
    (pureAtomRun left (overlapCount+1))

end TraceReconstruction



/-! The actual finite paired-flag experiment.  We separate its unconditional
orientation-first generation (used for trace simulation) from its exact
metadata-first Bayes factorization (used for the density estimates).
Neither construction conditions on successful window layout. -/
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- A joint law retaining both the latent variable and its conditional draw. -/
def joint (P : FiniteLaw α) (K : α → FiniteLaw β) : FiniteLaw (α × β) where
  mass z := P.mass z.1 * (K z.1).mass z.2
  nonneg z := mul_nonneg (P.nonneg _) ((K _).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (K _).total, mul_one]
    exact P.total

end FiniteLaw

variable {Side Leaf : Type*} [Fintype Side] [Fintype Leaf] {m n : ℕ}

/-- Data of the paired mechanisms, with common submass proved for each side.
All words and their actual trace laws will be substituted in these fields. -/
structure PairedMechanisms (Side : Type*) [Fintype Side] (m : ℕ) where
  first : Fin m → FiniteLaw Side
  second : Fin m → FiniteLaw Side
  common : Fin m → FiniteLaw Side
  hiddenWeight : Fin m → ℝ
  weight_nonneg : ∀ i, 0 ≤ hiddenWeight i
  common_first : ∀ i a, hiddenWeight i*(common i).mass a ≤ (first i).mass a
  common_second : ∀ i a, hiddenWeight i*(common i).mass a ≤ (second i).mass a

abbrev Reports (Side : Type*) (m : ℕ) := Fin m → Option Bool × (Side × Side)

namespace PairedMechanisms
variable (M : PairedMechanisms Side m)

def reports : FiniteLaw (Reports Side m) :=
  FiniteLaw.coordinateProduct (fun i => FiniteLaw.pairedReport (M.first i) (M.second i)
    (M.common i) (M.weight_nonneg i) (M.common_first i) (M.common_second i))

def reportsGiven (b : Fin m → Bool) : FiniteLaw (Reports Side m) :=
  FiniteLaw.coordinateProduct (fun i => FiniteLaw.pairedFlagLaw (M.first i) (M.second i)
    (M.common i) (M.weight_nonneg i) (M.common_first i) (M.common_second i) (b i))

/-- Bit orientations, prior to generating any emissions. -/
def fairOrientations (m : ℕ) : FiniteLaw (Fin m → Bool) :=
  (FiniteLaw.flagPosterior none).product m

/-- Exact posterior, with zero-mass metadata treated by the same canonical
formula. In particular unseen orientations are independent fair bits. -/
def orientationsGiven (z : Reports Side m) : FiniteLaw (Fin m → Bool) :=
  FiniteLaw.coordinateProduct (fun i => FiniteLaw.flagPosterior (z i).1)

def selectedLeafLaw (P Q : FiniteLaw Leaf) (θ : Fin n → Bool) :
    FiniteLaw (Fin n → Leaf) :=
  FiniteLaw.coordinateProduct (fun i => if θ i then Q else P)

/-- Actual orientation-first, unconditioned augmented observation. -/
def orientationOracle (P Q : FiniteLaw Leaf) (θ : (Fin m → Bool) → Fin n → Bool) :
    FiniteLaw (Reports Side m × (Fin n → Leaf)) :=
  (fairOrientations m).mixture (fun b => (M.reportsGiven b).prod (selectedLeafLaw P Q (θ b)))

/-- Metadata-first factorization of exactly the same law, not a new oracle. -/
def canonicalOracle (P Q : FiniteLaw Leaf) (θ : (Fin m → Bool) → Fin n → Bool) :
    FiniteLaw (Reports Side m × (Fin n → Leaf)) :=
  M.reports.joint (fun z => (orientationsGiven z).mixture (fun b => selectedLeafLaw P Q (θ b)))

end PairedMechanisms
end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialOverlap

Literal periods, count overlap, initial low/high energies, genuine densities, and centered moment bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Absolute constant in the conditional second-moment exponent. -/
def primitivePeriodConstant : ℝ := 36*rankSchurConstant^2

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical


/-- The actual base count, with no redefinition of the working channel. -/
def initialSideCount (q : ℝ) (m : ℕ) : ℕ := ⌊q*(m:ℝ)⌋₊

/-- An injective enumeration of m common integer counts; no asymptotic
cardinality argument is left implicit. -/
def commonCountIndex {m : ℕ} (k : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) (j : Fin m) :
    Fin ((k+1)*m+1) :=
  ⟨⌊p*((k*m:ℕ):ℝ)⌋₊+j.val,by
    have ha : (⌊p*((k*m:ℕ):ℝ)⌋₊:ℝ) ≤ ((k*m:ℕ):ℝ) := by
      exact (Nat.floor_le (mul_nonneg hp.1 (Nat.cast_nonneg _))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg _) hp.2)
    have ha' : ⌊p*((k*m:ℕ):ℝ)⌋₊ ≤ k*m := by exact_mod_cast ha
    have hj := j.isLt
    rw [Nat.add_mul,one_mul]
    omega⟩

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The common-mass constant depends only on the working deletion rate. -/
def initialOverlapLower (q : ℝ) : ℝ :=
  Real.exp (-(32+3*primitivePeriodConstant)/q^3)/1536

end TraceReconstruction



/-! From the actual displaced period words to their conditional oracle
moments.  The coefficient bounds are the rank kernels,
not assumptions on an abstract pair. -/
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- An interior period slot admits the three literal shifts. -/
def oneStepOffset {m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m) (a : Fin 3) : Fin m :=
  ⟨off.val+a.val-1,by have ha := a.isLt; omega⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Explicit low-degree majorant from the signed finite-difference estimate. -/
def signedInitialDegreeBound (u m r s : ℕ) (π : IntSeries) (θ : ℝ) (l : ℕ) : ℝ :=
  if r=0 then 0 else
    8*(Fintype.card (Fin r → GapDifference):ℝ)*
      (∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
        signedPatternBound u m r s π θ k else 0) +
    2*((Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))))^2

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem primitive_reference_mass_pos {q : ℝ} (hq : q∈Set.Ioo 0 1) (z : PrimitiveMark) :
    0 < (primitiveMarkLaw q hq false).mass z := by
  change 0 < primitiveMarkMass q false z
  apply div_pos _ (primitive_retain_pos hq)
  fin_cases z <;> simp [ordinaryPrimitiveMass,primitiveErasure] <;> nlinarith [hq.1,hq.2]

theorem primitive_product_mass_pos {q : ℝ} (hq : q∈Set.Ioo 0 1) {l : ℕ}
    (x : Fin l → PrimitiveMark) : 0 < ((primitiveMarkLaw q hq false).product l).mass x :=
by
  change 0 < ∏ i, (primitiveMarkLaw q hq false).mass (x i)
  exact Finset.prod_pos (fun _ _ => primitive_reference_mass_pos hq _)

/-- The density in the actual base experiment, not an independent model. -/
def initialMotifDensity {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (τ q : ℝ) : (Fin l → PrimitiveMark) → ℝ :=
  multilinear (mixedMotifCoefficient hl off hsafe π s τ) (primitiveScore q)

theorem initialMotifDensity_nonneg {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q : ℝ} (hq : q∈Set.Ioo 0 1) (x : Fin l → PrimitiveMark) :
    0 ≤ initialMotifDensity hl off hsafe π s τ q x := by
  have h := (conditionalMotifLaw hl off hsafe hq π hπ hπsum s τ).nonneg x
  rw [conditionalMotifLaw_density] at h
  exact nonneg_of_mul_nonneg_right h (primitive_product_mass_pos hq x)

theorem initialMotifDensity_mean {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    ((primitiveMarkLaw q hq false).product l).expect (initialMotifDensity hl off hsafe π s τ q)=1 := by
  have h := (conditionalMotifLaw hl off hsafe hq π hπ hπsum s τ).total
  simpa only [conditionalMotifLaw_density,FiniteLaw.expect,initialMotifDensity] using h

/-- The constant-term deletion of a polynomial. -/
def nonconstantCoefficient {l : ℕ} (A : (Fin l → Bool) → ℝ) (σ : Fin l → Bool) : ℝ :=
  if σ=(fun _ => false) then 0 else A σ

end TraceReconstruction


end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LeafOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LeafOracle

Recursive leaf oracles, sparse high tails, occupied shapes, posterior smoothing, source bit trees, and singleton cancellation.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Complete window-tree leaf indices, with counts numbered from the bottom.
The tree is fixed before any occupied subset or orientation is selected. -/
def WindowLeaf (T : ℕ → ℕ) : ℕ → Type
  | 0 => Fin 1
  | b+1 => Fin (T b) × WindowLeaf T b

noncomputable instance windowLeafFintype (T : ℕ → ℕ) : (b : ℕ) → Fintype (WindowLeaf T b)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | b+1 => by
    letI := windowLeafFintype T b
    exact inferInstanceAs (Fintype (Fin (T b) × WindowLeaf T b))

/-- A motif's actual outgoing type, allowing every integer displacement. -/
def motifChildSign (s : ℕ) (X : ℤ) (h : ℕ) (τ : ℝ) : ℝ :=
  1-motifIndicator s ((h:ℤ)-X)+(prouhetSeries s).coeff ((h:ℤ)-X)*τ

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def boolSupport {n : ℕ} (θ : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => θ i=true)

def degreeTail {n : ℕ} (A : (Fin n → Bool) → ℝ) (k : ℕ) (σ : Fin n → Bool) : ℝ :=
  if k ≤ monomialDegree σ then A σ else 0

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def selectedChildren {α β : Type*} [DecidableEq α] (S : Finset (α × β)) : Finset α :=
  S.image Prod.fst

def selectedChildLeaves {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (h : α) : Finset β :=
  (S.filter (fun v => v.1=h)).image Prod.snd

@[to_additive]
theorem selected_prod_children {α β M : Type*} [DecidableEq α] [DecidableEq β]
    [CommMonoid M] (S : Finset (α × β)) (f : α × β → M) :
    (∏h∈selectedChildren S, ∏v∈selectedChildLeaves S h, f (h,v)) = ∏v∈S, f v := by
  have he (h : α) : (∏v∈selectedChildLeaves S h, f (h,v)) =
      ∏v∈S.filter (fun v => v.1=h), f v := by
    unfold selectedChildLeaves
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro v hv
      rw [←(Finset.mem_filter.mp hv).2]
    · intro v hv w hw h
      apply Prod.ext
      · exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
      · exact h
  simp_rw [he]
  exact Finset.prod_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) f

@[to_additive]
theorem selected_prod_index {α M : Type*} [DecidableEq α] [CommMonoid M]
    (S : Finset α) (f : α → M) :
    (∏i : Fin S.card, f (S.equivFin.symm i).val) = ∏v∈S, f v := by
  have h := Equiv.prod_comp S.equivFin.symm (fun v : S => f v.val)
  simpa only [Finset.prod_coe_sort] using h

/-- Occupied shape of an actual subset of a complete window tree. Only
occupied children are enumerated, so its leaves are exactly the selected
monomial variables, not the other complete-tree leaves. -/
def occupiedWindowShape (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ) :
    (b : ℕ) → (path : List ℕ) → Finset (WindowLeaf T (b+1)) → CoefficientShape b
  | 0, path, S => .bottom S.card
      (fun i => motifIndicator s (((S.equivFin.symm i).val.1.val:ℤ)-X path))
      (fun i => (prouhetSeries s).coeff (((S.equivFin.symm i).val.1.val:ℤ)-X path))
  | b+1, path, S => .node (selectedChildren S).card
      (fun i => motifIndicator s ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X path))
      (fun i => (prouhetSeries s).coeff ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X path))
      (fun i => occupiedWindowShape T s X b
        (path++[((selectedChildren S).equivFin.symm i).val.val])
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val))

theorem selected_children_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) :
    (∑h∈selectedChildren S, (selectedChildLeaves S h).card) = S.card := by
  simpa only [Finset.sum_const,smul_eq_mul,mul_one] using
    selected_sum_children S (fun _ => (1:ℕ))

theorem selectedChildLeaves_nonempty {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (h : α) (hh : h∈selectedChildren S) :
    (selectedChildLeaves S h).Nonempty := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hh
  exact ⟨v.2,Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩,rfl⟩⟩

theorem occupiedWindowShape_leafCount (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : (occupiedWindowShape T s X b path S).Choice) :
    ((occupiedWindowShape T s X b path S).termTree a).leafCount = S.card := by
  induction b generalizing path with
  | zero => simp [occupiedWindowShape,CoefficientShape.termTree,OccupiedParityTree.leafCount]
  | succ b ih =>
    change (∑i : Fin (selectedChildren S).card, _) = _
    simp_rw [ih]
    exact (selected_sum_index (selectedChildren S) (fun h =>
      (selectedChildLeaves S h).card)).trans (selected_children_card S)

theorem occupiedWindowShape_occupied (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) (hS : S.Nonempty)
    (a : (occupiedWindowShape T s X b path S).Choice) :
    ((occupiedWindowShape T s X b path S).termTree a).occupied := by
  induction b generalizing path with
  | zero => exact ⟨hS.card_pos,fun _ => trivial⟩
  | succ b ih =>
    refine ⟨(Finset.image_nonempty.mpr hS).card_pos,fun i => ?_⟩
    exact ih _ _ (selectedChildLeaves_nonempty S _
      ((selectedChildren S).equivFin.symm i).property) (a.1 i)

/-- The role choices depend only on the selected subset, not on any hidden
orientation. This common index type permits averaging before norm estimates. -/
def OccupiedWindowChoice (T : ℕ → ℕ) :
    (b : ℕ) → Finset (WindowLeaf T (b+1)) → Type
  | 0, S => Fin S.card → Fin 3
  | b+1, S =>
      ((i : Fin (selectedChildren S).card) → OccupiedWindowChoice T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)) ×
      (Fin (selectedChildren S).card → Fin 3)

noncomputable instance occupiedWindowChoiceFintype (T : ℕ → ℕ) :
    (b : ℕ) → (S : Finset (WindowLeaf T (b+1))) → Fintype (OccupiedWindowChoice T b S)
  | 0, S => by unfold OccupiedWindowChoice; infer_instance
  | b+1, S => by
      letI := fun i : Fin (selectedChildren S).card =>
        occupiedWindowChoiceFintype T b
          (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)
      unfold OccupiedWindowChoice
      first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def occupiedWindowChoiceEquiv (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ) :
    (b : ℕ) → (path : List ℕ) → (S : Finset (WindowLeaf T (b+1))) →
      OccupiedWindowChoice T b S ≃ (occupiedWindowShape T s X b path S).Choice
  | 0, _, _ => Equiv.refl _
  | b+1, path, S => Equiv.prodCongr
      (Equiv.piCongrRight fun i => occupiedWindowChoiceEquiv T s X b
        (path++[((selectedChildren S).equivFin.symm i).val.val])
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val))
      (Equiv.refl _)

/-- The parity tree of a role choice is independent of all displacement bits. -/
noncomputable def occupiedWindowTerm (T : ℕ → ℕ) :
    (b : ℕ) → (S : Finset (WindowLeaf T (b+1))) →
      OccupiedWindowChoice T b S → OccupiedParityTree (b+1)
  | 0, S, a => .node S.card (fun _ => .leaf) a
  | b+1, S, a => .node (selectedChildren S).card
      (fun i => occupiedWindowTerm T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)) a.2

 theorem occupiedWindowTerm_eq (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : OccupiedWindowChoice T b S) :
    (occupiedWindowShape T s X b path S).termTree
      (occupiedWindowChoiceEquiv T s X b path S a) = occupiedWindowTerm T b S a := by
  induction b generalizing path with
  | zero => rfl
  | succ b ih =>
    change OccupiedParityTree.node _ (fun i => _) _ = OccupiedParityTree.node _ _ _
    congr 1
    funext i
    exact ih _ _ _

noncomputable def occupiedWindowWeight (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : OccupiedWindowChoice T b S) : ℝ :=
  (occupiedWindowShape T s X b path S).weight
    (occupiedWindowChoiceEquiv T s X b path S a)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Arbitrary functions of the actual posterior count have the translated
fair-binomial law, not only its generating polynomial. -/
theorem posterior_count_average {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (F : ℤ → ℝ) :
    (∑ b : ι → Bool, (∏i, (flagPosterior (d i)).mass (b i)) *
      F (∑i, (bitIndex (b i):ℤ))) =
    ∑k∈Finset.range ((∑i, hiddenTrial (d i))+1),
      fairBinomial (∑i, hiddenTrial (d i)) k * F ((∑i,(visibleOnes (d i):ℤ))+k) := by
  have H := congrArg (fun p : IntSeries => Finsupp.linearCombination ℝ F p.coeff)
    (posterior_count_series d)
  rw [fairSeries_sum,Finset.mul_sum] at H
  simp only [AddMonoidAlgebra.single_mul_single,one_mul,
    AddMonoidAlgebra.coeff_sum,AddMonoidAlgebra.coeff_single,map_sum,
    Finsupp.linearCombination_single,smul_eq_mul] at H
  exact H

theorem fairBinomial_reflect (n k : ℕ) (hk : k ≤ n) :
    fairBinomial n (n-k) = fairBinomial n k := by
  simp only [fairBinomial,Nat.choose_symm hk]

/-- Reflection of the remaining hidden count. The known visible contribution
is kept, and no positivity assumption on the metadata mass is needed. -/
theorem posterior_count_average_reflected {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (F : ℤ → ℝ) :
    (∑ b : ι → Bool, (∏i, (flagPosterior (d i)).mass (b i)) *
      F (∑i, (bitIndex (b i):ℤ))) =
    ∑k∈Finset.range ((∑i, hiddenTrial (d i))+1),
      fairBinomial (∑i, hiddenTrial (d i)) k *
        F ((∑i,(visibleOnes (d i):ℤ))+(∑i,hiddenTrial (d i))-k) := by
  rw [posterior_count_average]
  rw [←Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ ∑i,hiddenTrial (d i) := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
  simp only [Nat.add_sub_cancel,fairBinomial_reflect _ _ hk',Nat.cast_sub hk']
  congr 2
  ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The actual two-sibling anchor multiplier. Global bits are shared by the
two siblings until AFTER averaging; their local bits are independent. -/
def posteriorJointAnchors {ιg ι₁ ι₂ : Type*} [Fintype ιg] [Fintype ι₁] [Fintype ι₂]
    (dg : ιg → Option Bool) (d₁ : ι₁ → Option Bool) (d₂ : ι₂ → Option Bool)
    (s : ℕ) (z₁ z₂ : ℤ) : ℝ :=
  ∑bg : ιg → Bool, (∏i,(flagPosterior (dg i)).mass (bg i)) *
    (∑b₁ : ι₁ → Bool, (∏i,(flagPosterior (d₁ i)).mass (b₁ i)) *
      motifIndicator s (z₁+(∑i,(bitIndex (bg i):ℤ))+(∑i,(bitIndex (b₁ i):ℤ)))) *
    (∑b₂ : ι₂ → Bool, (∏i,(flagPosterior (d₂ i)).mass (b₂ i)) *
      motifIndicator s (z₂+(∑i,(bitIndex (bg i):ℤ))+(∑i,(bitIndex (b₂ i):ℤ))))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- All local and global orientation collections on the complete index tree,
including unoccupied vertices and paths which do not fit. The type is fixed
before any selected monomial or role choices. `n` is the local trial count,
`g` the number of global paired trials, and T the full window counts. -/
def WindowAssignments (T n g : ℕ → ℕ) (A : Type) : ℕ → Type
  | 0 => PUnit
  | b+1 => (Fin (n b) → A) × (Fin (g b) → A) ×
      (Fin (T b) → WindowAssignments T n g A b)

noncomputable instance windowAssignmentsFintype (T n g : ℕ → ℕ) (A : Type) [Fintype A] :
    (b : ℕ) → Fintype (WindowAssignments T n g A b)
  | 0 => inferInstanceAs (Fintype PUnit)
  | b+1 => by
      letI := windowAssignmentsFintype T n g A b
      exact inferInstanceAs (Fintype ((Fin (n b) → A) × (Fin (g b) → A) ×
        (Fin (T b) → WindowAssignments T n g A b)))

def posteriorArray {n : ℕ} (d : Fin n → Option Bool) : FiniteLaw (Fin n → Bool) :=
  coordinateProduct (fun i => flagPosterior (d i))

/-- Actual independent posterior orientations at exact non-leaf metadata.
The common global bits in a group are drawn only once. -/
def windowPosteriorLaw (T n g : ℕ → ℕ) : (b : ℕ) →
    WindowAssignments T n g (Option Bool) b → FiniteLaw (WindowAssignments T n g Bool b)
  | 0, _ => ⟨fun _ => 1,fun _ => by norm_num,by change (∑_ : PUnit,(1:ℝ))=1; simp⟩
  | b+1, d => (posteriorArray d.1).prod ((posteriorArray d.2.1).prod
      (coordinateProduct (fun i => windowPosteriorLaw T n g b (d.2.2 i))))

/-- Displacements from the jointly generated bit tree. The ancestor global
map may vary off its plateau. No independent jitter per child is introduced.
The fixed center includes the deterministic half-trial corrections. -/
def sourceTreeAnchors (T n g : ℕ → ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → WindowAssignments T n g Bool b → ℤ → List ℕ → ℤ
  | 0, _, _, _ => 0
  | b+1, bits, incoming, [] => center b - (∑i,(bitIndex (bits.1 i):ℤ))-incoming
  | b+1, bits, _, h::tail => if hh : h<T b then
      sourceTreeAnchors T n g center globalShift b (bits.2.2 ⟨h,hh⟩)
        (globalShift b bits.2.1 ⟨h,hh⟩) tail else 0

end TraceReconstruction

-- Actual subtree coefficient factorization and singleton cancellation.
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The factor at the current vertex of a fixed actual occupied role choice.
It only uses that vertex's displacement, never any descendant mechanism. -/
def occupiedRootWeight (T : ℕ → ℕ) (s : ℕ) :
    (b : ℕ) → (S : Finset (WindowLeaf T (b+1))) →
      OccupiedWindowChoice T b S → ℤ → ℝ
  | 0, S, a, X => ∏i : Fin S.card,
      bottomRoleWeight (motifIndicator s (((S.equivFin.symm i).val.1.val:ℤ)-X))
        ((prouhetSeries s).coeff (((S.equivFin.symm i).val.1.val:ℤ)-X)) (a i)
  | b+1, S, a, X => ∏i : Fin (selectedChildren S).card,
      @internalRoleWeight (occupiedWindowTerm T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)).isOdd
        (Classical.propDecidable _)
        (motifIndicator s ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X))
        ((prouhetSeries s).coeff ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X)) (a.2 i)


/-- A fixed real coefficient term evaluated on the actual complete bit tree.
The selected role choice is fixed independently of these bits. -/
def sourceRoleTerm (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) : ℝ :=
  occupiedWindowWeight T s (sourceTreeAnchors T n g center globalShift (b+1) bits incoming)
    b [] S a

def sourceRoleAverage (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) : ℝ :=
  (windowPosteriorLaw T n g (b+1) d).expect
    (fun bits => sourceRoleTerm T n g s center globalShift b bits incoming S a)

/-- The exact signed smoothing cost read off the visible metadata alone. -/
def posteriorSmoothingCost {ι : Type*} [Fintype ι] (s : ℕ) (d : ι → Option Bool) : ℝ :=
  (2:ℝ)^(s*s)*((2*binomialBound ((∑i,hiddenTrial (d i))/(s+1)))^s *
    binomialBound ((∑i,hiddenTrial (d i))/(s+1)))

/-- A purely numerical typical-metadata condition on every local collection.
It includes unoccupied vertices and is fixed before a coefficient is chosen. -/
def MetadataSmoothingCap (T n g : ℕ → ℕ) (s : ℕ) (η : ℝ) :
    (b : ℕ) → WindowAssignments T n g (Option Bool) b → Prop
  | 0, _ => True
  | b+1, d => posteriorSmoothingCost s d.1 ≤ η ∧
      ∀h, MetadataSmoothingCap T n g s η b (d.2.2 h)

def occupiedRootHasSingleton (T : ℕ → ℕ) : (b : ℕ) →
    (S : Finset (WindowLeaf T (b+1))) → OccupiedWindowChoice T b S → Prop
  | 0, _, a => ∃i, a i=2 ∧ ∀j,j≠i → a j=0
  | _+1, _, a => ∃i, a.2 i=2 ∧ ∀j,j≠i → a.2 j=0

end TraceReconstruction

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Anchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Anchors

Forced anchors, extra-leaf closeness, and correlated group square-sum estimates.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- A concrete binary selection of labels in the complete index tree.
Unlike a free abstract shape this retains every actual column label. -/
def BinaryWindowLabels (T : ℕ → ℕ) : ℕ → Type
  | 0 => PUnit
  | b+1 => Fin (T b) × Fin (T b) × BinaryWindowLabels T b × BinaryWindowLabels T b

noncomputable instance binaryWindowLabelsFintype (T : ℕ → ℕ) :
    (b : ℕ) → Fintype (BinaryWindowLabels T b)
  | 0 => inferInstanceAs (Fintype PUnit)
  | b+1 => by
      letI := binaryWindowLabelsFintype T b
      exact inferInstanceAs (Fintype (Fin (T b) × Fin (T b) × BinaryWindowLabels T b × BinaryWindowLabels T b))

/-- The forced children are distinct at every split. Central restrictions
are separate deterministic predicates, not conditioning events. -/
def BinaryWindowLabels.distinct (T : ℕ → ℕ) : (b : ℕ) → BinaryWindowLabels T b → Prop
  | 0, _ => True
  | b+1, p => p.1≠p.2.1 ∧ distinct T b p.2.2.1 ∧ distinct T b p.2.2.2

/-- Product of the first-child unsigned anchor at every forced nonleaf,
evaluated using the literal complete-tree orientation assignment. -/
def binaryAnchorKernel (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → BinaryWindowLabels T b → WindowAssignments T n g Bool b → ℤ → ℝ
  | 0, _, _, _ => 1
  | b+1, p, bits, incoming =>
      motifIndicator s ((p.1.val:ℤ)-center b+(∑i,(bitIndex (bits.1 i):ℤ))+incoming) *
      (binaryAnchorKernel T n g s center globalShift b p.2.2.1 (bits.2.2 p.1)
        (globalShift b bits.2.1 p.1) *
       binaryAnchorKernel T n g s center globalShift b p.2.2.2 (bits.2.2 p.2.1)
        (globalShift b bits.2.1 p.2.1))

def binaryAnchorAverage (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T b) (d : WindowAssignments T n g (Option Bool) b)
    (incoming : ℤ) : ℝ :=
  (windowPosteriorLaw T n g b d).expect (fun bits =>
    binaryAnchorKernel T n g s center globalShift b p bits incoming)

/-- Local unsigned anchor averaged against its actual known/hidden flags. -/
def localAnchorAverage {m : ℕ} (d : Fin m → Option Bool) (s : ℕ) (z : ℤ) : ℝ :=
  (posteriorArray d).expect (fun bits => motifIndicator s (z+∑i,(bitIndex (bits i):ℤ)))

/-- Product of all lower sibling-group factors. Each group still averages
its own single common global draw, not two independent global draws. -/
def binaryAnchorBelow (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → BinaryWindowLabels T (b+1) → WindowAssignments T n g (Option Bool) (b+1) → ℝ
  | 0, _, _ => 1
  | b+1, p, d =>
      (posteriorArray d.2.1).expect (fun glob =>
        localAnchorAverage (d.2.2 p.1).1 s
          ((p.2.2.1.1.val:ℤ)-center b+globalShift (b+1) glob p.1) *
        localAnchorAverage (d.2.2 p.2.1).1 s
          ((p.2.2.2.1.val:ℤ)-center b+globalShift (b+1) glob p.2.1)) *
      (binaryAnchorBelow T n g s center globalShift b p.2.2.1 (d.2.2 p.1) *
       binaryAnchorBelow T n g s center globalShift b p.2.2.2 (d.2.2 p.2.1))

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- A role-selected forced subtree remembers the actual complete-tree labels,
not merely its abstract binary shape. -/
def forcedWindowLabels (T : ℕ → ℕ) : (b : ℕ) →
    (S : Finset (WindowLeaf T (b+1))) → (a : OccupiedWindowChoice T b S) →
    (occupiedWindowTerm T b S a).Forced → BinaryWindowLabels T (b+1)
  | 0, S, _, .node i j _ _ _ _ _ =>
      ((S.equivFin.symm i).val.1,(S.equivFin.symm j).val.1,PUnit.unit,PUnit.unit)
  | b+1, S, a, .node i j _ _ _ left right =>
      (((selectedChildren S).equivFin.symm i).val,
       ((selectedChildren S).equivFin.symm j).val,
       forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)
         (a.1 i) left,
       forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val)
         (a.1 j) right)

end TraceReconstruction


namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The unsigned bottom constraint at one literal complete-tree leaf. -/
def sourceBottomIndicator (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → WindowAssignments T n g Bool (b+1) → ℤ → WindowLeaf T (b+1) → ℝ
  | 0, bits, incoming, v =>
      motifIndicator s ((v.1.val:ℤ)-center 0+(∑i,(bitIndex (bits.1 i):ℤ))+incoming)
  | b+1, bits, _, v => sourceBottomIndicator T n g s center globalShift b
      (bits.2.2 v.1) (globalShift (b+1) bits.2.1 v.1) v.2

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Deterministic closeness of each forced split; it is a restriction on
labels, never an additional conditioning event for the random bits. -/
def BinaryWindowLabels.close (T : ℕ → ℕ) (s : ℕ) : (b : ℕ) → BinaryWindowLabels T b → Prop
  | 0, _ => True
  | b+1, p => |(p.1.val:ℤ)-p.2.1.val|<(2^s:ℕ) ∧ close T s b p.2.2.1 ∧ close T s b p.2.2.2

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The literal finite child labels embedded in the integer line. -/
def finIntegerLabels (N : ℕ) : Finset ℤ := Finset.univ.image (fun i : Fin N => (i.val:ℤ))

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The actual finite central domain, distinctness and close-label restriction.
It is purely deterministic and is never added to the orientation posterior. -/
def anchorPairAllowed (T : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b))) (s b : ℕ)
    (a c : Fin (T b)) : Prop := a∈A b ∧ c∈A b ∧ a≠c ∧ |(c.val:ℤ)-a.val|<(2^s:ℕ)

/-- The source global plateau identity is required pointwise for bits, not
just in distribution and not after conditioning on successful layout. -/
def HasGlobalPlateau (T g : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) : Prop :=
  ∀b glob u, u∈A b → globalShift b glob u=(∑i,(bitIndex (glob i):ℤ))-shift b

/-- Numerical binomial caps extracted from the literal known/hidden metadata.
In applications these are proved using the source hidden-trial lower bounds. -/
def MetadataBinomialCaps (T n g : ℕ → ℕ) (B C : ℕ → ℝ) :
    (b : ℕ) → WindowAssignments T n g (Option Bool) b → Prop
  | 0, _ => True
  | b+1, d => binomialBound (∑i, hiddenTrial (d.1 i)) ≤ B b ∧
      binomialBound (∑i, hiddenTrial (d.2.1 i)) ≤ C b ∧
      ∀u, MetadataBinomialCaps T n g B C b (d.2.2 u)

/-- One correlated sibling-group anchor, using the actual child metadata
and their parent's one shared global orientation collection. -/
def binarySiblingAnchor (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1+1))
    (u v : Fin (T (b+1))) (a c : Fin (T b)) : ℝ :=
  (posteriorArray d.2.1).expect (fun glob =>
    localAnchorAverage (d.2.2 u).1 s ((a.val:ℤ)-center b+globalShift (b+1) glob u) *
    localAnchorAverage (d.2.2 v).1 s ((c.val:ℤ)-center b+globalShift (b+1) glob v))

/-- Exact dynamic sum of squared group anchors over the allowed finite
labels below a fixed forced split. Distinct groups retain their own metadata. -/
def binaryDescendantEnergy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) :
    (b : ℕ) → WindowAssignments T n g (Option Bool) (b+1) → Fin (T b) → Fin (T b) → ℝ
  | 0, _, _, _ => 1
  | b+1, d, u, v =>
      ∑a : Fin (T b),∑c : Fin (T b),∑e : Fin (T b),∑f : Fin (T b),
        if anchorPairAllowed T A s b a c ∧ anchorPairAllowed T A s b e f then
          binarySiblingAnchor T n g s center globalShift b d u v a e ^ 2 *
            binaryDescendantEnergy T n g s center globalShift A b (d.2.2 u) a c *
            binaryDescendantEnergy T n g s center globalShift A b (d.2.2 v) e f
        else 0

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def BinaryWindowLabels.allowed (T : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b))) (s : ℕ) :
    (b : ℕ) → BinaryWindowLabels T b → Prop
  | 0, _ => True
  | b+1, p => anchorPairAllowed T A s b p.1 p.2.1 ∧
      allowed T A s b p.2.2.1 ∧ allowed T A s b p.2.2.2

/-- Regroup the two real top child labels, without changing the actual
finite label type or declaration order. -/
def joinBinaryLabels {T : ℕ → ℕ} {b : ℕ} (a : Fin (T b) × Fin (T b))
    (p : BinaryWindowLabels T b × BinaryWindowLabels T b) : BinaryWindowLabels T (b+1) :=
  (a.1,a.2,p.1,p.2)

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Shapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shapes

Global schedules, edge labels, forced/extra coordinate splitting, finite shape codes, and occupied-label counts.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Source central third, in the zero-based child label convention. The
shift of the source one-based indices is recorded in center parameters. -/
def centralThird (N : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun u => N ≤ 3*u.val ∧ 3*u.val ≤ 2*N)

/-- One actual global-pair orientation, ordered by its pre-region block and
its local identifier there. -/
def globalTrialIndex (N t : ℕ) (v : Fin (N/4)) (a : Fin t) : Fin ((N/4)*t) :=
  ⟨v.val*t+a.val, by nlinarith [v.isLt,a.isLt]⟩

/-- Literal net global displacement immediately before a child window:
a pre block at v+1 remains active through its matched post region N-v.
The paired displacement has even t trials in each affected region. -/
def scheduledGlobalShift (N t : ℕ) (bits : Fin ((N/4)*t) → Bool) (u : Fin N) : ℤ :=
  ∑v : Fin (N/4), if v.val ≤ u.val ∧ u.val+v.val<N then
    (∑a : Fin t, (bitIndex (bits (globalTrialIndex N t v a)):ℤ))-(t/2:ℕ) else 0

theorem globalTrialIndex_bijective (N t : ℕ) :
    Function.Bijective (fun x : Fin (N/4) × Fin t => globalTrialIndex N t x.1 x.2) := by
  constructor
  · intro x y he
    have he' := congrArg Fin.val he
    change x.1.val*t+x.2.val = y.1.val*t+y.2.val at he'
    have hx := x.2.isLt
    have hy := y.2.isLt
    have hv : x.1.val=y.1.val := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h <;> nlinarith
    have ha : x.2.val=y.2.val := by rw [hv] at he'; omega
    exact Prod.ext (Fin.ext hv) (Fin.ext ha)
  · intro i
    have ht : 0<t := by
      by_contra h
      have hz : t=0 := by omega
      have := i.isLt
      simp only [hz,Nat.mul_zero] at this
      omega
    refine ⟨(⟨i.val/t, (Nat.div_lt_iff_lt_mul ht).mpr i.isLt⟩,
      ⟨i.val%t,Nat.mod_lt _ ht⟩),?_⟩
    apply Fin.ext
    change i.val/t*t+i.val%t=i.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod i.val t

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- One actual child-label coordinate of an arbitrary ordered occupied
shape. Unlike a complete r-ary padding, this contains no unused edges. -/
def Edge : {b : ℕ} → OccupiedParityTree b → Type
  | _, .leaf => PEmpty
  | _, .node n children _ => Fin n ⊕ ((i : Fin n) × Edge (children i))

noncomputable instance edgeFintype : {b : ℕ} → (t : OccupiedParityTree b) → Fintype t.Edge
  | _, .leaf => inferInstanceAs (Fintype PEmpty)
  | _, .node n children roles => by
      letI := fun i => edgeFintype (children i)
      exact inferInstanceAs (Fintype (Fin n ⊕ ((i : Fin n) × Edge (children i))))

def Edge.height : {b : ℕ} → {t : OccupiedParityTree b} → t.Edge → ℕ
  | _, .leaf, e => e.elim
  | _, @OccupiedParityTree.node b _n _children _roles, e =>
      match e with
      | Sum.inl _ => b
      | Sum.inr z => Edge.height z.2

/-- All literal label assignments to this particular ordered shape. -/
def Labels (T : ℕ → ℕ) {b : ℕ} (t : OccupiedParityTree b) :=
  (e : t.Edge) → Fin (T e.height)

noncomputable instance labelsFintype (T : ℕ → ℕ) {b : ℕ} (t : OccupiedParityTree b) :
    Fintype (t.Labels T) := inferInstanceAs (Fintype ((e : t.Edge) → Fin (T e.height)))

def Labels.child (T : ℕ → ℕ) {b n : ℕ} {children : Fin n → OccupiedParityTree b}
    {roles : Fin n → Fin 3} (x : (OccupiedParityTree.node n children roles).Labels T)
    (i : Fin n) : (children i).Labels T := fun e => x (Sum.inr ⟨i,e⟩)

/-- Projection to the actual labels of a fixed forced subtree. The shape
selection is independent of these labels and of all random orientations. -/
def Forced.labels (T : ℕ → ℕ) : {b : ℕ} → {t : OccupiedParityTree b} →
    t.Forced → t.Labels T → BinaryWindowLabels T b
  | _, _, .leaf, _ => PUnit.unit
  | _, _, .node a c _ _ _ left right, x =>
      (x (Sum.inl a),x (Sum.inl c),left.labels T (x.child T a),right.labels T (x.child T c))

/-- Edge addresses in a complete binary tree, independent of all actual
numeric labels. False and true are its two children. -/
def BinaryEdge : ℕ → Type
  | 0 => PEmpty
  | b+1 => Bool ⊕ (Bool × BinaryEdge b)

noncomputable instance binaryEdgeFintype : (b : ℕ) → Fintype (BinaryEdge b)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | b+1 => by
      letI := binaryEdgeFintype b
      exact inferInstanceAs (Fintype (Bool ⊕ (Bool × BinaryEdge b)))

def BinaryEdge.height : {b : ℕ} → BinaryEdge b → ℕ
  | 0, e => e.elim
  | b+1, Sum.inl _ => b
  | _b+1, Sum.inr e => BinaryEdge.height e.2

/-- The forced binary tree is embedded in the actual occupied edge set. -/
def Forced.edge : {b : ℕ} → {t : OccupiedParityTree b} → t.Forced → BinaryEdge b → t.Edge
  | _, _, .leaf, e => e.elim
  | _, _, .node a _ _ _ _ _ _, Sum.inl false => Sum.inl a
  | _, _, .node _ c _ _ _ _ _, Sum.inl true => Sum.inl c
  | _, _, .node a _ _ _ _ left _, Sum.inr (false,e) => Sum.inr ⟨a,left.edge e⟩
  | _, _, .node _ c _ _ _ _ right, Sum.inr (true,e) => Sum.inr ⟨c,right.edge e⟩

theorem Forced.edge_injective {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Function.Injective F.edge := by
  induction F with
  | leaf => intro i; exact i.elim
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        cases i <;> cases j
        · rfl
        · exact (hne (Sum.inl.inj he)).elim
        · exact (hne (Sum.inl.inj he).symm).elim
        · rfl
      | inr j => cases i <;> rcases j with ⟨j,e⟩ <;> cases j <;> cases he
    | inr i =>
      cases j with
      | inl j => rcases i with ⟨i,e⟩; cases i <;> cases j <;> cases he
      | inr j =>
        rcases i with ⟨i,e⟩
        rcases j with ⟨j,f⟩
        cases i <;> cases j
        · have hh := Sum.inr.inj he
          have hh' : left.edge e=left.edge f := by injection hh
          exact congrArg (fun e => Sum.inr (false,e)) (ihl hh')
        · have hh := congrArg Sigma.fst (Sum.inr.inj he)
          exact (hne hh).elim
        · have hh := congrArg Sigma.fst (Sum.inr.inj he)
          exact (hne hh.symm).elim
        · have hh := Sum.inr.inj he
          have hh' : right.edge e=right.edge f := by injection hh
          exact congrArg (fun e => Sum.inr (true,e)) (ihr hh')

theorem Forced.edge_height {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (e : BinaryEdge b) : (F.edge e).height=e.height := by
  induction F with
  | leaf => exact e.elim
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    cases e with
    | inl i => cases i <;> rfl
    | inr z => rcases z with ⟨i,e⟩; cases i; exact ihl e; exact ihr e

/-- The finite number of edge coordinates at a given child height. -/
def edgeCount {b : ℕ} (t : OccupiedParityTree b) (h : ℕ) : ℕ :=
  Fintype.card {e : t.Edge // e.height=h}

theorem Edge.height_lt {b : ℕ} {t : OccupiedParityTree b} (e : t.Edge) : e.height<b := by
  induction t with
  | leaf => exact e.elim
  | @node b n children roles ih =>
    cases e with
    | inl i => exact Nat.lt_succ_self b
    | inr z => exact Nat.lt_succ_of_lt (ih z.1 z.2)

def BinaryEdgeLabels (T : ℕ → ℕ) (b : ℕ) := (e : BinaryEdge b) → Fin (T e.height)

noncomputable instance binaryEdgeLabelsFintype (T : ℕ → ℕ) (b : ℕ) :
    Fintype (BinaryEdgeLabels T b) := inferInstanceAs (Fintype ((e : BinaryEdge b) → Fin (T e.height)))

/-- Exact coordinates of the recursively defined forced label tuple. -/
def binaryLabelsEquiv (T : ℕ → ℕ) : (b : ℕ) → BinaryEdgeLabels T b ≃ BinaryWindowLabels T b
  | 0 =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ e => e.elim
      left_inv := fun _ => by funext e; exact e.elim
      right_inv := fun y => by cases y; rfl }
  | b+1 =>
    { toFun := fun x => (x (Sum.inl false),x (Sum.inl true),
        binaryLabelsEquiv T b (fun e => x (Sum.inr (false,e))),
        binaryLabelsEquiv T b (fun e => x (Sum.inr (true,e))))
      invFun := fun x e => match e with
        | Sum.inl false => x.1
        | Sum.inl true => x.2.1
        | Sum.inr (false,e) => (binaryLabelsEquiv T b).symm x.2.2.1 e
        | Sum.inr (true,e) => (binaryLabelsEquiv T b).symm x.2.2.2 e
      left_inv := fun x => by
        funext e
        cases e with
        | inl j => cases j <;> rfl
        | inr z =>
          rcases z with ⟨j,e⟩
          cases j <;> exact congrFun ((binaryLabelsEquiv T b).symm_apply_apply _) e
      right_inv := fun x => by
        rcases x with ⟨a,c,l,r⟩
        simp only [Equiv.apply_symm_apply]
        rfl }

/-- Restriction to the real forced coordinates, with only equality transport
of the child-height index. -/
def Forced.restrict (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (x : t.Labels T) : BinaryEdgeLabels T b := fun e =>
  Fin.cast (congrArg T (F.edge_height e)) (x (F.edge e))

end OccupiedParityTree
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

def Forced.ExtraEdge {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  {e : t.Edge // e∉Set.range F.edge}

noncomputable instance forcedExtraEdgeFintype {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Fintype F.ExtraEdge := inferInstanceAs (Fintype {e : t.Edge // e∉Set.range F.edge})

def Forced.ExtraLabels (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  (e : F.ExtraEdge) → Fin (T e.val.height)

noncomputable instance forcedExtraLabelsFintype (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) : Fintype (F.ExtraLabels T) :=
  inferInstanceAs (Fintype ((e : F.ExtraEdge) → Fin (T e.val.height)))

/-- Exact bijective partition of all actual edge coordinates into the
forced binary coordinates and the genuine extra coordinates. -/
noncomputable def Forced.labelsEquiv (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    t.Labels T ≃ BinaryWindowLabels T b × F.ExtraLabels T := by
  classical
  letI : DecidablePred (Set.range F.edge) := fun _ => Classical.propDecidable _
  exact (Equiv.piEquivPiSubtypeProd (Set.range F.edge) (fun e : t.Edge => Fin (T e.height))).trans
    (Equiv.prodCongr
      (((Equiv.piCongrLeft (fun e : Set.range F.edge => Fin (T e.val.height))
        (Equiv.ofInjective F.edge F.edge_injective)).symm.trans
          (Equiv.piCongrRight fun e => finCongr (congrArg T (F.edge_height e)))).trans
            (binaryLabelsEquiv T b))
      (Equiv.refl _))

def Forced.ExtraLeafEdge {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  {e : F.ExtraEdge // e.val.height=0}

def Forced.ExtraInteriorEdge {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  {e : F.ExtraEdge // e.val.height≠0}

noncomputable instance extraLeafEdgeFintype {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Fintype F.ExtraLeafEdge := inferInstanceAs (Fintype {e : F.ExtraEdge // e.val.height=0})

noncomputable instance extraInteriorEdgeFintype {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Fintype F.ExtraInteriorEdge := inferInstanceAs (Fintype {e : F.ExtraEdge // e.val.height≠0})

def Forced.InteriorLabels (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  (e : F.ExtraInteriorEdge) → Fin (T e.val.val.height)

noncomputable instance extraInteriorLabelsFintype (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) : Fintype (F.InteriorLabels T) :=
  inferInstanceAs (Fintype ((e : F.ExtraInteriorEdge) → Fin (T e.val.val.height)))

/-- Extra bottom labels are separated from all nonleaf labels without
introducing any T₁ factor. -/
noncomputable def Forced.extraLabelsEquiv (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) : F.ExtraLabels T ≃ (F.ExtraLeafEdge → Fin (T 0)) × F.InteriorLabels T :=
  (Equiv.piEquivPiSubtypeProd (fun e : F.ExtraEdge => e.val.height=0)
    (fun e : F.ExtraEdge => Fin (T e.val.height))).trans
    (Equiv.prodCongr (Equiv.piCongrRight fun e => finCongr (congrArg T e.property)) (Equiv.refl _))

end OccupiedParityTree
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- The parent address of an edge in the full deterministic numerical index
tree. In particular it does not contain the edge's own child label. -/
def Edge.parentPath (T : ℕ → ℕ) : {b : ℕ} → {t : OccupiedParityTree b} →
    t.Labels T → t.Edge → List ℕ
  | _, .leaf, _, e => e.elim
  | _, .node _n _children _roles, x, e => match e with
    | Sum.inl _ => []
    | Sum.inr z => (x (Sum.inl z.1)).val :: Edge.parentPath T (x.child T z.1) z.2

/-- The combined exact split into forced, extra-leaf and extra-interior labels. -/
noncomputable def Forced.fullLabelsEquiv (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) : t.Labels T ≃
      BinaryWindowLabels T b × (F.ExtraLeafEdge → Fin (T 0)) × F.InteriorLabels T :=
  (F.labelsEquiv T).trans (Equiv.prodCongr (Equiv.refl _) (F.extraLabelsEquiv T))

end OccupiedParityTree
end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- A finite ordered-role shape code with at most r children at every
vertex. There are no numerical child labels in this type. -/
def FiniteRoleShape (r : ℕ) : ℕ → Type
  | 0 => PUnit
  | b+1 => (n : Fin (r+1)) × (Fin n.val → FiniteRoleShape r b) × (Fin n.val → Fin 3)

noncomputable instance finiteRoleShapeFintype (r : ℕ) : (b : ℕ) → Fintype (FiniteRoleShape r b)
  | 0 => inferInstanceAs (Fintype PUnit)
  | b+1 => by
    letI := finiteRoleShapeFintype r b
    exact inferInstanceAs (Fintype ((n : Fin (r+1)) ×
      (Fin n.val → FiniteRoleShape r b) × (Fin n.val → Fin 3)))

def FiniteRoleShape.toTree (r : ℕ) : (b : ℕ) → FiniteRoleShape r b → OccupiedParityTree b
  | 0, _ => .leaf
  | b+1, x => .node x.1.val (fun i => (x.2.1 i).toTree r b) x.2.2

theorem occupied_arity_le_leaves {b n : ℕ} (children : Fin n → OccupiedParityTree b)
    (roles : Fin n → Fin 3) (ht : (OccupiedParityTree.node n children roles).occupied) :
    n≤(OccupiedParityTree.node n children roles).leafCount := by
  have h (i : Fin n) : 1≤(children i).leafCount := leafCount_pos _ (ht.2 i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,leafCount]
    using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i)

theorem child_le_leaves {b n : ℕ} (children : Fin n → OccupiedParityTree b)
    (roles : Fin n → Fin 3) (i : Fin n) :
    (children i).leafCount≤(OccupiedParityTree.node n children roles).leafCount :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((children j).leafCount)) (Finset.mem_univ i)

/-- Every occupied shape with r selected leaves really has a finite code
whose domain depends only on r and the depth, not on any window size. -/
theorem exists_finiteRoleShape {b : ℕ} (t : OccupiedParityTree b) (r : ℕ)
    (ht : t.occupied) (hr : t.leafCount ≤ r) :
    ∃x : FiniteRoleShape r b,x.toTree r b=t := by
  induction t with
  | leaf => exact ⟨PUnit.unit,rfl⟩
  | @node b n children roles ih =>
    have hn : n < r+1 := by have := occupied_arity_le_leaves children roles ht; omega
    have hx (i : Fin n) : ∃x : FiniteRoleShape r b,x.toTree r b=children i :=
      ih i (ht.2 i) ((child_le_leaves children roles i).trans hr)
    choose x hx using hx
    refine ⟨⟨⟨n,hn⟩,x,roles⟩,?_⟩
    change OccupiedParityTree.node n (fun i => (x i).toTree r b) roles = _
    congr 1
    exact funext hx

/-- The manuscript's finite shape/role constant, now a literal natural
number independent of the actual child-label sizes and all channel data. -/
def shapeRoleConstant (r b : ℕ) : ℕ := Fintype.card (FiniteRoleShape r b)

theorem finite_bounded_occupied_shapes (b r : ℕ) :
    Finite {t : OccupiedParityTree b // t.occupied ∧ t.leafCount ≤ r} := by
  let f : {t : OccupiedParityTree b // t.occupied ∧ t.leafCount ≤ r} → FiniteRoleShape r b :=
    fun t => Classical.choose (exists_finiteRoleShape t.val r t.property.1 t.property.2)
  apply Finite.of_injective f
  intro x y he
  apply Subtype.ext
  have hx := Classical.choose_spec (exists_finiteRoleShape x.val r x.property.1 x.property.2)
  have hy := Classical.choose_spec (exists_finiteRoleShape y.val r y.property.1 y.property.2)
  dsimp only [f] at he
  exact hx.symm.trans ((congrArg (FiniteRoleShape.toTree r b) he).trans hy)
end OccupiedParityTree
end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Extra-leaf index set version of the whole-bit-law sum. -/
def indexedExtraAverage {Ω E : Type*} [Fintype Ω] [Fintype E] (P : FiniteLaw Ω)
    (s N : ℕ) (f : Ω → ℝ) (X : Ω → E → ℤ) (h : E → Fin N) : ℝ :=
  P.expect (fun ω => f ω*∏j,motifIndicator s (((h j).val:ℤ)-X ω j))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open OccupiedParityTree

/-- Node-wise assembly of genuine edge labels. -/
def OccupiedParityTree.Labels.node (T : ℕ → ℕ) {b k : ℕ}
    {children : Fin k → OccupiedParityTree b} {roles : Fin k → Fin 3}
    (h : Fin k → Fin (T b)) (z : (i : Fin k) → (children i).Labels T) :
    (OccupiedParityTree.node k children roles).Labels T :=
  fun e => match e with
  | Sum.inl i => h i
  | Sum.inr q => z q.1 q.2

/-- The real numeric labels of the selected occupied configuration. -/
def occupiedTermLabels (T : ℕ → ℕ) : (b : ℕ) →
    (S : Finset (WindowLeaf T (b+1))) → (a : OccupiedWindowChoice T b S) →
      (occupiedWindowTerm T b S a).Labels T
  | 0, S, _ => Labels.node T (fun i => (S.equivFin.symm i).val.1) (fun _ e => e.elim)
  | b+1, S, a => Labels.node T (fun i => ((selectedChildren S).equivFin.symm i).val)
      (fun i => occupiedTermLabels T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i))

namespace OccupiedParityTree
/-- Reading the set of leaf addresses from a shape and numeric edge labels.
Repeated or unordered coordinates are allowed; the true encoding is a
particular subset of this unrestricted label domain. -/
def labelledLeaves (T : ℕ → ℕ) : {b : ℕ} → (t : OccupiedParityTree b) →
    t.Labels T → Finset (WindowLeaf T b)
  | 0, .leaf, _ => {(⟨0,by decide⟩ : Fin 1)}
  | b+1, .node n children roles, x => Finset.univ.biUnion fun i : Fin n =>
      ((children i).labelledLeaves T (x.child T i)).image (fun v => (x (Sum.inl i),v))
end OccupiedParityTree

/-- Unrestricted shape/label space really covers the coefficient index
without multiplicity. -/
def occupiedTermEncoding (T : ℕ → ℕ) (b : ℕ)
    (w : (S : Finset (WindowLeaf T (b+1))) × OccupiedWindowChoice T b S) :
    (t : OccupiedParityTree (b+1)) × t.Labels T :=
  ⟨occupiedWindowTerm T b w.1 w.2,occupiedTermLabels T b w.1 w.2⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

noncomputable def Forced.edgeEquiv {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    BinaryEdge b ⊕ F.ExtraEdge ≃ t.Edge := by
  classical
  letI : DecidablePred (Set.range F.edge) := fun _ => Classical.propDecidable _
  exact (Equiv.sumCongr (Equiv.ofInjective F.edge F.edge_injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (Set.range F.edge))

def binaryEdgeCount (b h : ℕ) : ℕ := Fintype.card {e : BinaryEdge b // e.height=h}

def Forced.extraCount {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (h : ℕ) : ℕ :=
  Fintype.card {e : F.ExtraEdge // e.val.height=h}

/-- Extra nonleaf numeric labels grouped by their actual child height. -/
def Forced.interiorHeight {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (e : F.ExtraInteriorEdge) : Fin b := ⟨e.val.val.height,e.val.val.height_lt⟩

end OccupiedParityTree
end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy

Shaped envelopes, actual coefficient aggregation, role counts, central contributions, and full coefficient energy.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
namespace OccupiedParityTree

/-- Actual unsigned coefficient envelope on one ordered occupied shape.
No bits are resampled for the additional leaves. -/
def Forced.envelope (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (x : t.Labels T)
    (bits : WindowAssignments T n g Bool b) (incoming : ℤ) : ℝ :=
  binaryAnchorKernel T n g s center globalShift b (F.labels T x) bits incoming *
    ∏e : F.ExtraLeafEdge, motifIndicator s ((x e.val.val).val-
      sourceTreeAnchors T n g center globalShift b bits incoming (e.val.val.parentPath T x))

def Forced.averagedEnvelope (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (x : t.Labels T)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) : ℝ :=
  (windowPosteriorLaw T n g b d).expect
    (fun bits => F.envelope T n g s center globalShift x bits incoming)

/-- Offsets for all extra leaf constraints, with only their labels replaced
by zero. The location of each constraint is not changed by that replacement. -/
def Forced.extraOffsets (T n g : ℕ → ℕ) (hT : 0<T 0) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (p : BinaryWindowLabels T b) (z : F.InteriorLabels T)
    (bits : WindowAssignments T n g Bool b) (incoming : ℤ) (e : F.ExtraLeafEdge) : ℤ :=
  sourceTreeAnchors T n g center globalShift b bits incoming
    (e.val.val.parentPath T ((F.fullLabelsEquiv T).symm (p,(fun _ => ⟨0,hT⟩),z)))

end OccupiedParityTree
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- The actual full-tree leaf address of a bottom edge, including the edge's
own numeric label. -/
def Edge.bottomAddress (T : ℕ → ℕ) : {b : ℕ} → {t : OccupiedParityTree b} →
    (x : t.Labels T) → (e : t.Edge) → e.height=0 → WindowLeaf T b
  | _, .leaf, _, e, _ => e.elim
  | b+1, .node k children roles, x, Sum.inl i, he => by
      change b=0 at he
      subst b
      exact (x (Sum.inl i),(⟨0,by decide⟩ : Fin 1))
  | b+1, .node k children roles, x, Sum.inr z, he =>
      (x (Sum.inl z.1), Edge.bottomAddress T (x.child T z.1) z.2 he)

end OccupiedParityTree
end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
open OccupiedParityTree

theorem occupiedWindowTerm_leafCount (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) :
    (occupiedWindowTerm T b S a).leafCount=S.card := by
  rw [←occupiedWindowTerm_eq T 0 (fun _ => 0) b [] S a]
  exact occupiedWindowShape_leafCount T 0 (fun _ => 0) b [] S _

theorem occupiedWindowTerm_occupied (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) (hS : S.Nonempty) :
    (occupiedWindowTerm T b S a).occupied := by
  rw [←occupiedWindowTerm_eq T 0 (fun _ => 0) b [] S a]
  exact occupiedWindowShape_occupied T 0 (fun _ => 0) b [] S hS _

/-- Only the unlabeled ordered role shape is selected here; no child label
or hidden orientation enters the forced choice. -/
abbrev DegreeForcedShape (b r : ℕ) :=
  {t : OccupiedParityTree b // t.occupied ∧ t.leafCount=r ∧ Nonempty t.Forced}

instance degreeForcedShapeFinite (b r : ℕ) : Finite (DegreeForcedShape b r) := by
  let := finite_bounded_occupied_shapes b r
  exact Finite.of_injective
    (fun t : DegreeForcedShape b r =>
      (⟨t.val,t.property.1,t.property.2.1.le⟩ : {t : OccupiedParityTree b // t.occupied ∧ t.leafCount ≤ r}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun q : {t : OccupiedParityTree b // t.occupied ∧ t.leafCount ≤ r} => q.val) h))

noncomputable instance degreeForcedShapeFintype (b r : ℕ) : Fintype (DegreeForcedShape b r) :=
  Fintype.ofFinite _

def DegreeForcedShape.forced {b r : ℕ} (t : DegreeForcedShape b r) : t.val.Forced :=
  Classical.choice t.property.2.2

abbrev SourceRoleIndex (T : ℕ → ℕ) (b : ℕ) :=
  (S : Finset (WindowLeaf T (b+1))) × OccupiedWindowChoice T b S

abbrev DegreeForcedRole (T : ℕ → ℕ) (b r : ℕ) :=
  {w : SourceRoleIndex T b // w.1.card=r ∧ Nonempty (occupiedWindowTerm T b w.1 w.2).Forced}

def DegreeForcedRole.shape (T : ℕ → ℕ) (b r : ℕ) (w : DegreeForcedRole T b r) :
    DegreeForcedShape (b+1) r := by
  refine ⟨occupiedWindowTerm T b w.val.1 w.val.2,?_,?_,w.property.2⟩
  · apply occupiedWindowTerm_occupied
    apply Finset.card_pos.mp
    obtain ⟨F⟩ := w.property.2
    have hh := F.leaf_lower
    rw [occupiedWindowTerm_leafCount] at hh
    exact (Nat.pow_pos (by decide : (0:ℕ)<2)).trans_le hh
  · exact (occupiedWindowTerm_leafCount T b w.val.1 w.val.2).trans w.property.1

def DegreeForcedRole.encoding (T : ℕ → ℕ) (b r : ℕ) (w : DegreeForcedRole T b r) :
    (t : DegreeForcedShape (b+1) r) × t.val.Labels T :=
  ⟨w.shape T b r,occupiedTermLabels T b w.val.1 w.val.2⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
open OccupiedParityTree

/-- A degree-r sum over the genuine pairs (selected leaves, roles),
restricted only by deterministic allowed forced labels. -/
def degreeForcedRoleEnergy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) : ℝ :=
  ∑w : DegreeForcedRole T b r,
    if BinaryWindowLabels.allowed T A s (b+1)
      ((w.shape T b r).forced.labels T (occupiedTermLabels T b w.val.1 w.val.2)) then
      (sourceRoleAverage T n g s center globalShift b d incoming w.val.1 w.val.2)^2 else 0

/-- Uniform arithmetic interior-label budget of a degree-r depth-(b+1)
shape. This includes no factor for a bottom label. -/
def interiorLabelBudget (T : ℕ → ℕ) (b r : ℕ) : ℝ :=
  ((∏j : Fin (b+1),if j.val=0 then 1 else T j.val : ℕ):ℝ)^(r-2^(b+1))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

abbrev DegreeLeafSubset (T : ℕ → ℕ) (b r : ℕ) :=
  {S : Finset (WindowLeaf T (b+1)) // S.card=r}

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- All actual motif support lies in the chosen central interval at every
vertex of the full window tree. This is a predicate of the complete bits,
not an event on which any posterior law is conditioned. -/
def SourceCentral (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) :
    (b : ℕ) → WindowAssignments T n g Bool b → ℤ → Prop
  | 0, _, _ => True
  | b+1, bits, incoming =>
      (∀h : Fin (T b), motifIndicator s ((h.val:ℤ)-center b+
        (∑i,(bitIndex (bits.1 i):ℤ))+incoming)≠0 → h∈A b) ∧
      ∀h, SourceCentral T n g s center globalShift A b (bits.2.2 h) (globalShift b bits.2.1 h)

def BinaryWindowLabels.central (T : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b))) :
    (b : ℕ) → BinaryWindowLabels T b → Prop
  | 0, _ => True
  | b+1, p => p.1∈A b ∧ p.2.1∈A b ∧ central T A b p.2.2.1 ∧ central T A b p.2.2.2

/-- The discarded noncentral role contributions are bounded by the actual
conditional probability of a failed full-tree layout. Typical metadata may
bound this mass; the averaging distribution itself remains unconditional. -/
def sourceNoncentralMass (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) : ℝ :=
  (windowPosteriorLaw T n g b d).expect
    (fun bits => if SourceCentral T n g s center globalShift A b bits incoming then 0 else 1)

end TraceReconstruction


end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Layout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Layout

Multiwindow and paired layouts, coordinate simulations, and literal source types and trees.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Literal unmarked concatenation of fixed windows with separately reported
pure pre/post regions. Counts are in atoms, not surviving trace symbols. -/
def framedConcat {α : Type*} (e : α) {k : ℕ}
    (pre post : Fin k → ℕ) (W : Fin k → List α) : List α :=
  (List.ofFn (fun i => List.replicate (pre i) e ++ W i ++
    List.replicate (post i) e)).flatten

/-- Number of atoms strictly before the indicated padded unit. -/
def framePrefix {k : ℕ} (pre post : Fin k → ℕ) (len : Fin k → ℕ) (i : ℕ) : ℕ :=
  ∑j : Fin k, if j.val < i then pre j+len j+post j else 0

end TraceReconstruction

noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {K : Type*} [Fintype K]

/-- Counts of literal side chunks, with one deterministic pure filler in
 each region. A bundle can contain any even number of paired chunks. -/
def pairedPreCount {N : ℕ} (left : K → Fin N) (filler : Fin N → ℕ)
    (first : K → ℕ) (u : Fin N) : ℕ :=
  filler u + ∑v, if left v=u then first v else 0

def pairedPostCount {N : ℕ} (right : K → Fin N) (filler : Fin N → ℕ)
    (reserve first : K → ℕ) (u : Fin N) : ℕ :=
  filler u + ∑v, if right v=u then 2*reserve v-first v else 0

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {K : Type*} [Fintype K]

/-- One localBits bundle at each child, and one globalBits bundle at each vertex in
 the first quarter, paired with the reflected last-quarter post region. -/
abbrev SourceBundle (N : ℕ) := Fin N ⊕ Fin (N/4)

def sourceBundleLeft (N : ℕ) : SourceBundle N → Fin N
  | .inl u => u
  | .inr v => ⟨v.val,by have := v.isLt; omega⟩

def sourceBundleRight (N : ℕ) : SourceBundle N → Fin N
  | .inl u => u
  | .inr v => ⟨N-1-v.val,by have := v.isLt; omega⟩

def sourceBundleCount (N t h : ℕ) (localBits : Fin N → Fin t → Bool)
    (globalBits : Fin ((N/4)*t) → Bool) : SourceBundle N → ℕ
  | .inl u => t*h+∑a,bitIndex (localBits u a)
  | .inr v => t*h+∑a : Fin t,bitIndex (globalBits (globalTrialIndex N t v a))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- One-bundle reserved nominal count is integral because the number of
 paired trials is even. The actual filler reserves both local and global
 bundles when both are present in a region. -/
def sourceLayoutReserve (t h : ℕ) : ℕ := t*h+t/2

def sourcePreFiller (N A t h : ℕ) (u : Fin N) : ℕ :=
  A-∑v : SourceBundle N,if sourceBundleLeft N v=u then sourceLayoutReserve t h else 0

def sourcePostFiller (N B t h : ℕ) (u : Fin N) : ℕ :=
  B-∑v : SourceBundle N,if sourceBundleRight N v=u then sourceLayoutReserve t h else 0

def sourceDisplacement (N t : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) (u : Fin N) : ℤ :=
  (∑a : Fin t,(bitIndex (loc u a):ℤ))-(t/2:ℕ)+scheduledGlobalShift N t glob u

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Independent emissions at all literal slots accumulate their actual
 approximation errors. The decoders may depend on the fixed slot ID. -/
theorem coordinateProduct_approximates {α : Type*} [Fintype α]
    {n : ℕ} {q : ℝ} (hq : q∈Set.Icc 0 1) (P : Fin n → FiniteLaw α)
    (f : Fin n → α → List Bool) (w : Fin n → List Bool) (E : Fin n → ℝ)
    (h : ∀i,ApproximatesTrace q (P i) (f i) (w i) (E i)) :
    ApproximatesTrace q (FiniteLaw.coordinateProduct P)
      (fun x => coordinateWord (fun i => f i (x i))) (coordinateWord w) (∑i,E i) := by
  induction n with
  | zero =>
    intro F hF
    change |(FiniteLaw.coordinateProduct P).expect (fun _ => F [])-F []|≤∑i : Fin 0,E i
    simp only [FiniteLaw.expect_const,sub_self,abs_zero,Finset.univ_eq_empty,Finset.sum_empty,le_refl]
  | succ n ih =>
    intro F hF
    have ht := ih (fun i => P i.succ) (fun i => f i.succ)
      (fun i => w i.succ) (fun i => E i.succ) (fun i => h i.succ)
    have hh := ApproximatesTrace.append hq (h 0) ht F hF
    rw [FiniteLaw.expect_prod] at hh
    rw [FiniteLaw.expect_coordinateProduct_succ,coordinateWord_succ,Fin.sum_univ_succ]
    have he (a : α) (x : Fin n → α) :
        coordinateWord (fun i => f i ((Fin.cons a x : Fin (n+1) → α) i))=
          f 0 a++coordinateWord (fun i => f i.succ (x i)) := by
      rw [coordinateWord_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    simp_rw [he]
    exact hh

namespace FiniteLaw
variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]

/-- Independent emissions indexed by the actual token IDs of the layout. -/
def indexedProduct (P : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  mass x := ∏i,(P i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg _)
  total := by
    rw [←Fintype.prod_sum]
    simp only [(P _).total,Finset.prod_const_one]

end FiniteLaw

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The Boolean representation of the source Prouhet signs; true denotes
 a negative type. No sign convention is changed in passing to literal words. -/
def boolTypeSign (b : Bool) : ℝ := if b then -1 else 1

def prouhetBool (s : ℕ) (i : Fin (2^s)) : Bool :=
  decide ((prouhetSeries s).coeff (i.val:ℤ)= -1)

/-- The actual recursively substituted source block words. Indices in P
 are shifted down by one, but physical binary strings are unchanged. -/
def sourceBlockWord (s : ℕ) (P : ℕ → ℕ) (atom : Bool → List Bool) : ℕ → Bool → List Bool
  | 0 => atom
  | j+1 => complementaryWords (P j) (P j/2-1) (2^s) (prouhetBool s)
      (sourceBlockWord s P atom j)

def sourceBlockLength (P : ℕ → ℕ) (S : ℕ) : ℕ → ℕ
  | 0 => S
  | j+1 => P j*sourceBlockLength P S j

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Total Boolean type, also on failed layouts; no conditioning is hidden
 in the definition. -/
def integerTemplateType (N s : ℕ) (X : ℤ) (τ : Bool) (u : Fin N) : Bool :=
  decide (motifChildSign s X u.val (boolTypeSign τ)= -1)

/-- Global trials at a parent use its children's local-trial count. This
 fixes the index shift between source level labels and zero-based arrays. -/
def sourceScheduledTrials (T n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | b+1 => (T (b+1)/4)*n b

def sourceScheduledShift (T n : ℕ → ℕ) :
    (b : ℕ) → (Fin (sourceScheduledTrials T n b) → Bool) → Fin (T b) → ℤ
  | 0, _, _ => 0
  | b+1, glob, u => scheduledGlobalShift (T (b+1)) (n b) glob u

def sourceLocalCenter (T n : ℕ → ℕ) (b : ℕ) : ℤ :=
  (T b/2:ℕ)-1+(n b/2:ℕ)

def sourceNodeAnchor (T n : ℕ → ℕ) (center : ℕ → ℤ) (b : ℕ)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) (incoming : ℤ) : ℤ :=
  center b-(∑i,(bitIndex (bits.1 i):ℤ))-incoming

/-- All actual leaf Booleans on the complete deterministic window tree. -/
def sourceTreeLeafBool (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℤ → Bool → WindowLeaf T b → Bool
  | 0, _, _, τ, _ => τ
  | b+1, bits, incoming, τ, v =>
      sourceTreeLeafBool T n s center b (bits.2.2 v.1)
        (sourceScheduledShift T n b bits.2.1 v.1)
        (integerTemplateType (T b) s (sourceNodeAnchor T n center b bits incoming) τ v.1) v.2

def sourceNominalPre (P T : ℕ → ℕ) (b : ℕ) : ℕ := (P b-T b)/2
def sourceNominalPost (P T : ℕ → ℕ) (b : ℕ) : ℕ := P b-T b-sourceNominalPre P T b

/-- The actual center before recursively cutting its pure side regions. -/
def sourceCenterWord (s : ℕ) (P T n : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℤ → Bool → List Bool
  | 0, _, _, τ => atom τ
  | b+1, bits, incoming, τ => atomString (T b) (sourceBlockWord s P atom b)
      (integerTemplateType (T b) s (sourceNodeAnchor T n center b bits incoming) τ)

/-- The actual fit event uses a joint test of all displacements. It does not
 assert independence and will only be charged probabilistically afterwards. -/
def SourceTreeFit (T n : ℕ → ℕ) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → Prop
  | 0, _ => True
  | 1, _ => True
  | b+2, bits =>
      (∀u, |8*sourceDisplacement (T (b+1)) (n b) (fun v => (bits.2.2 v).1) bits.2.1 u| ≤ (T b:ℤ)) ∧
      ∀u, SourceTreeFit T n (b+1) (bits.2.2 u)

/-- Numerical layout conditions from the source. These contain no word or
 statistical conclusions, only the genuine integer margins. -/
structure SourceLayoutMargins (s : ℕ) (P T n h : ℕ → ℕ) (b : ℕ) : Prop where
  positive : ∀j<b, 0<T j
  large : ∀j<b, 16≤T j
  even_window : ∀j<b, Even (T j)
  ambient : ∀j<b, 2*T j≤P j
  motif : ∀j<b, 8*2^s≤T j
  even_trials : ∀j<b, Even (n j)
  pre_reserve : ∀j<b, 2*sourceLayoutReserve (n j) (h j)≤ sourceNominalPre P T j
  post_reserve : ∀j<b, 2*sourceLayoutReserve (n j) (h j)≤ sourceNominalPost P T j

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Metadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metadata

Hidden metadata, fair jitter, heterogeneous emissions, independent window trials, concentration, and fit.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace PairedMechanisms
variable {Side : Type*} [Fintype Side] {m : ℕ} (M : PairedMechanisms Side m)

def hiddenCount (z : Reports Side m) : ℕ := ∑i,hiddenTrial (z i).1

end PairedMechanisms
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The unconditional orientation distribution on any actual finite trial ID set. -/
def fairField (ι : Type*) [Fintype ι] : FiniteLaw (ι → Bool) :=
  FiniteLaw.indexedProduct (fun _ => FiniteLaw.flagPosterior none)

def fairLinearSum {ι : Type*} [Fintype ι] (c : ι → ℝ) (bits : ι → Bool) : ℝ :=
  ∑i,c i*((bitIndex (bits i):ℝ)-1/2)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀i,Fintype (A i)]

/-- Independent observations at literal slot IDs, allowing different outcome
 types (side traces and old leaf oracles carry genuinely different data). -/
def dependentProduct (P : ∀i,FiniteLaw (A i)) : FiniteLaw (∀i,A i) where
  mass x := ∏i,(P i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg _)
  total := by rw [←Fintype.prod_sum]; simp only [(P _).total,Finset.prod_const_one]

end FiniteLaw

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Actual IDs of every local or global paired trial on the whole window tree. -/
def WindowTrial (T n g : ℕ → ℕ) : ℕ → Type
  | 0 => PEmpty
  | b+1 => Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b))

noncomputable instance windowTrialFintype (T n g : ℕ → ℕ) :
    (b : ℕ) → Fintype (WindowTrial T n g b)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | b+1 => by
    letI := windowTrialFintype T n g b
    exact inferInstanceAs (Fintype (Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b))))

/-- A fixed bijection, independent of every bit, reveal and hypothesis. -/
def windowAssignmentEquiv (T n g : ℕ → ℕ) (A : Type) :
    (b : ℕ) → WindowAssignments T n g A b ≃ (WindowTrial T n g b → A)
  | 0 =>
    { toFun := fun _ i => PEmpty.elim i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by funext i; exact PEmpty.elim i }
  | b+1 =>
    { toFun := fun x i => match i with
        | .inl k => x.1 k
        | .inr (.inl k) => x.2.1 k
        | .inr (.inr (u,k)) => windowAssignmentEquiv T n g A b (x.2.2 u) k
      invFun := fun x => (fun k => x (.inl k),fun k => x (.inr (.inl k)),
        fun u => (windowAssignmentEquiv T n g A b).symm (fun k => x (.inr (.inr (u,k)))))
      left_inv := fun x => by
        rcases x with ⟨loc,glob,kids⟩
        change (loc,glob,fun u => (windowAssignmentEquiv T n g A b).symm
          (windowAssignmentEquiv T n g A b (kids u)))=(loc,glob,kids)
        simp only [Equiv.symm_apply_apply]

      right_inv := fun x => by
        funext i
        rcases i with k | k
        · rfl
        · rcases k with k | ⟨u,k⟩
          · rfl
          · exact congrFun ((windowAssignmentEquiv T n g A b).apply_symm_apply
              (fun k => x (.inr (.inr (u,k))))) k }

def noReveals (T n g : ℕ → ℕ) (b : ℕ) : WindowAssignments T n g (Option Bool) b :=
  (windowAssignmentEquiv T n g (Option Bool) b).symm (fun _ => none)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal global schedule is indexed by a fixed pair/block bijection. -/
def globalTrialEquiv (N t : ℕ) : (Fin (N/4) × Fin t) ≃ Fin ((N/4)*t) :=
  Equiv.ofBijective _ (globalTrialIndex_bijective N t)

end TraceReconstruction


end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simulation

Canonical and filled simulations, central fit, root words, chronology, slots, finite codes, and complete-trace decoding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Each paired mechanism owns two distinct side slots; fillers and old leaf
 oracles have their own IDs. This type is independent of every orientation. -/
abbrev EmissionSlot (m k n : ℕ) := (Fin m × Bool) ⊕ (Fin k ⊕ Fin n)

def EmissionOutcome (Side Leaf : Type) {m k n : ℕ} : EmissionSlot m k n → Type
  | .inl _ => Side
  | .inr (.inl _) => Side
  | .inr (.inr _) => Leaf

instance emissionOutcomeFintype {Side Leaf : Type} [Fintype Side] [Fintype Leaf]
    {m k n : ℕ} (i : EmissionSlot m k n) : Fintype (EmissionOutcome Side Leaf i) := by
  rcases i with a | a
  · exact inferInstanceAs (Fintype Side)
  · rcases a with a | a
    · exact inferInstanceAs (Fintype Side)
    · exact inferInstanceAs (Fintype Leaf)

/-- Actual arrays and slot observations are bijective, not a lossy interface. -/
def emissionAssignmentEquiv (Side Leaf : Type) (m k n : ℕ) :
    ((Fin m → Side × Side) × (Fin k → Side) × (Fin n → Leaf)) ≃
      (∀i : EmissionSlot m k n,EmissionOutcome Side Leaf i) where
  toFun x i := match i with
    | .inl (j,false) => (x.1 j).1
    | .inl (j,true) => (x.1 j).2
    | .inr (.inl j) => x.2.1 j
    | .inr (.inr j) => x.2.2 j
  invFun x := (fun j => (x (.inl (j,false)),x (.inl (j,true))),
    fun j => x (.inr (.inl j)),fun j => x (.inr (.inr j)))
  left_inv x := by
    rcases x with ⟨z,f,l⟩
    change (fun j => ((z j).1,(z j).2),f,l)=(z,f,l)
    simp only [Prod.mk.eta]
  right_inv x := by
    funext i
    rcases i with ⟨j,b⟩ | i
    · cases b <;> rfl
    · cases i <;> rfl

namespace PairedMechanisms
variable {Side Leaf : Type} [Fintype Side] [Fintype Leaf] {m k n : ℕ}
variable (M : PairedMechanisms Side m)

def slotLaw (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (bits : Fin m → Bool) (θ : Fin n → Bool) :
    (i : EmissionSlot m k n) → FiniteLaw (EmissionOutcome Side Leaf i)
  | .inl (j,false) => if bits j then M.second j else M.first j
  | .inl (j,true) => if bits j then M.first j else M.second j
  | .inr (.inl j) => R j
  | .inr (.inr j) => if θ j then Q else P

/-- The common, bit-blind projection simply forgets flags and concatenates in
 the publicly fixed ID order. -/
def slotDecode (f : Side → List Bool) (g : Leaf → List Bool) :
    (i : EmissionSlot m k n) → EmissionOutcome Side Leaf i → List Bool
  | .inl _,x => f x
  | .inr (.inl _),x => f x
  | .inr (.inr _),x => g x

def slotWord (U V : Fin m → List Bool) (W : Fin k → List Bool)
    (atom : Bool → List Bool) (bits : Fin m → Bool) (θ : Fin n → Bool) :
    EmissionSlot m k n → List Bool
  | .inl (j,false) => if bits j then V j else U j
  | .inl (j,true) => if bits j then U j else V j
  | .inr (.inl j) => W j
  | .inr (.inr j) => atom (θ j)

def slotCost (E : ℝ) : EmissionSlot m k n → ℝ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr _) => E

end PairedMechanisms
end TraceReconstruction


noncomputable section



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Pure filler IDs. At bottom leaf windows the two fillers have zero length;
 they are deterministic empty outputs, not extra information. -/
def WindowFiller (T : ℕ → ℕ) : ℕ → Type
  | 0 => PEmpty
  | b+1 => (Fin (T b) × Bool) ⊕ (Fin (T b) × WindowFiller T b)

noncomputable instance windowFillerFintype (T : ℕ → ℕ) : (b : ℕ) → Fintype (WindowFiller T b)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | b+1 => by
    letI := windowFillerFintype T b
    exact inferInstanceAs (Fintype ((Fin (T b) × Bool) ⊕ (Fin (T b) × WindowFiller T b)))

abbrev TreeEmission (T n g : ℕ → ℕ) (b : ℕ) :=
  (WindowTrial T n g b × Bool) ⊕ (WindowFiller T b ⊕ WindowLeaf T b)

def TreeEmission.up (T n g : ℕ → ℕ) (b : ℕ) (u : Fin (T b)) :
    TreeEmission T n g b → TreeEmission T n g (b+1)
  | .inl (i,p) => .inl (.inr (.inr (u,i)),p)
  | .inr (.inl f) => .inr (.inl (.inr (u,f)))
  | .inr (.inr v) => .inr (.inr (u,v))

def treeLocalSlots (T n g : ℕ → ℕ) (b : ℕ) (p : Bool) : List (TreeEmission T n g (b+1)) :=
  List.ofFn (fun k : Fin (n b) => Sum.inl (Sum.inl k,p))

def treeGlobalSlots (T n g : ℕ → ℕ) (b : ℕ) (p : Bool)
    (pos : Fin (g b) → Fin (T b)) (u : Fin (T b)) : List (TreeEmission T n g (b+1)) :=
  ((List.ofFn id : List (Fin (g b))).filter (fun k => pos k=u)).map
    (fun k => Sum.inl (Sum.inr (Sum.inl k),p))

/-- Public chronological IDs. Each child carries its own local paired sides;
 the group's global sides and deterministic fillers surround that child.
 The order is fixed independently of all bits and both hypotheses. -/
def treeChronology (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) :
    (b : ℕ) → List (TreeEmission T n g b)
  | 0 => [.inr (.inr (show WindowLeaf T 0 from (0 : Fin 1)))]
  | b+1 => treeLocalSlots T n g b false ++
      (List.ofFn (fun u : Fin (T b) =>
        treeGlobalSlots T n g b false (pre b) u ++
        [.inr (.inl (.inl (u,false)))] ++
        (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) ++
        treeGlobalSlots T n g b true (post b) u ++
        [.inr (.inl (.inl (u,true)))])).flatten ++
      treeLocalSlots T n g b true

theorem sum_fiber_list_length {α ι : Type*} [Fintype ι] [DecidableEq ι] (pos : α → ι) (l : List α) :
    (∑i,(l.filter (fun a => pos a=i)).length)=l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hh (i : ι) : ((a::l).filter (fun a => pos a=i)).length=
        (if pos a=i then 1 else 0)+(l.filter (fun a => pos a=i)).length := by
      by_cases h : pos a=i <;> simp [h,Nat.add_comm]
    simp_rw [hh]
    rw [Finset.sum_add_distrib,ih]
    simp [Nat.add_comm]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def pairedSideCount (h : ℕ) (bit side : Bool) : ℕ := h+bitIndex (Bool.xor bit side)

/-- Global trial positions are ID functions, not positions inferred from a
 realized output or orientation. -/
def sourceGlobalPre (N t : ℕ) (k : Fin ((N/4)*t)) : Fin N :=
  ⟨((globalTrialEquiv N t).symm k).1.val,by
    have := ((globalTrialEquiv N t).symm k).1.isLt; omega⟩

def sourceGlobalPost (N t : ℕ) (k : Fin ((N/4)*t)) : Fin N :=
  ⟨N-1-((globalTrialEquiv N t).symm k).1.val,by
    have := ((globalTrialEquiv N t).symm k).1.isLt; omega⟩

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceScheduledPre (T n : ℕ → ℕ) :
    (b : ℕ) → Fin (sourceScheduledTrials T n b) → Fin (T b)
  | 0,k => Fin.elim0 k
  | b+1,k => sourceGlobalPre (T (b+1)) (n b) k

def sourceScheduledPost (T n : ℕ → ℕ) :
    (b : ℕ) → Fin (sourceScheduledTrials T n b) → Fin (T b)
  | 0,k => Fin.elim0 k
  | b+1,k => sourceGlobalPost (T (b+1)) (n b) k

/-- Two actual deterministic pure binary side words for each paired trial ID. -/
def sourceTrialWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowTrial T n (sourceScheduledTrials T n) b → Bool → List Bool
  | 0,i,_ => PEmpty.elim i
  | b+1,.inl _,c => pureAtomRun (sourceBlockWord s P atom b false) (h b+bitIndex c)
  | 1,.inr (.inl k),_ => Fin.elim0 k
  | b+2,.inr (.inl _),c => pureAtomRun (sourceBlockWord s P atom b false) (h b+bitIndex c)
  | b+1,.inr (.inr (_,i)),c => sourceTrialWord s P T n h atom b i c

/-- Fixed pure fillers, including the deterministic empty bottom fillers. -/
def sourceFillerWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowFiller T b → List Bool
  | 0,i => PEmpty.elim i
  | b+1,.inl (u,p) => match b,u with
    | 0,_ => []
    | b+1,u => pureAtomRun (sourceBlockWord s P atom b false)
        (if p then sourcePostFiller (T (b+1)) (sourceNominalPost P T b) (n b) (h b) u
          else sourcePreFiller (T (b+1)) (sourceNominalPre P T b) (n b) (h b) u)
  | b+1,.inr (_,i) => sourceFillerWord s P T n h atom b i

def sourceSlotWord (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) : TreeEmission T n (sourceScheduledTrials T n) b → List Bool
  | .inl (i,side) => sourceTrialWord s P T n h atom b i
      (Bool.xor (windowAssignmentEquiv T n (sourceScheduledTrials T n) Bool b bits i) side)
  | .inr (.inl i) => sourceFillerWord s P T n h atom b i
  | .inr (.inr v) => atom (sourceTreeLeafBool T n s center b bits incoming τ v)

def sourceChronologicalWord (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) : List Bool :=
  ((treeChronology T n (sourceScheduledTrials T n) (sourceScheduledPre T n) (sourceScheduledPost T n) b).map
    (sourceSlotWord s P T n h center atom b bits incoming τ)).flatten

end TraceReconstruction



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

def finEnumeration (α : Type) [Fintype α] : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm

abbrev SourceTrialCount (T n : ℕ → ℕ) (b : ℕ) := Fintype.card (WindowTrial T n (sourceScheduledTrials T n) b)
abbrev SourceFillerCount (T : ℕ → ℕ) (b : ℕ) := Fintype.card (WindowFiller T b)
abbrev SourceLeafCount (T : ℕ → ℕ) (b : ℕ) := Fintype.card (WindowLeaf T b)

def sourceEmissionEnum (T n : ℕ → ℕ) (b : ℕ) :
    EmissionSlot (SourceTrialCount T n b) (SourceFillerCount T b) (SourceLeafCount T b) ≃
      TreeEmission T n (sourceScheduledTrials T n) b :=
  Equiv.sumCongr (Equiv.prodCongr (finEnumeration _) (Equiv.refl Bool))
    (Equiv.sumCongr (finEnumeration _) (finEnumeration _))

def sourceAssignmentCode (T n : ℕ → ℕ) (A : Type) (b : ℕ) :
    WindowAssignments T n (sourceScheduledTrials T n) A b ≃ (Fin (SourceTrialCount T n b) → A) where
  toFun bits j := windowAssignmentEquiv T n (sourceScheduledTrials T n) A b bits (finEnumeration _ j)
  invFun bits := (windowAssignmentEquiv T n (sourceScheduledTrials T n) A b).symm
    (fun i => bits ((finEnumeration _).symm i))
  left_inv bits := by simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  right_inv bits := by
    funext j
    simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]

end TraceReconstruction



end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_SourceOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# SourceOracle

Actual source mechanisms and posteriors, typical metadata, sparse degrees, common-event clipping, approximate oracles, and mixed Hellinger bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Ambient finite trace-space choice does not lose any of the genuine
complete-trace common mass. The embedding adds only zero-mass points. -/
theorem listTraceOverlap_le_ambient {q : ℝ} (hq : q∈Set.Icc 0 1)
    (x y : List Bool) (M : ℕ) (hx : x.length≤M) (hy : y.length≤M) :
    listTraceOverlap q hq x y≤
      (listTraceLaw q hq x M hx).overlap (listTraceLaw q hq y M hy) := by
  let M₀ := max x.length y.length
  have H := approximations_trace_tv hq
    (listTraceLaw q hq x M₀ (le_max_left _ _))
    (listTraceLaw q hq y M₀ (le_max_right _ _)) Subtype.val x y 0 0 M hx hy
    (listTraceLaw_simulates q hq x M₀ _).approximate
    (listTraceLaw_simulates q hq y M₀ _).approximate
  simp only [add_zero] at H
  unfold listTraceOverlap
  rw [FiniteLaw.overlap_eq_one_sub_tv,FiniteLaw.overlap_eq_one_sub_tv]
  linarith

namespace FiniteLaw
variable {α : Type*} [Fintype α]
theorem commonPart_le_right (P Q : FiniteLaw α) (h : 0<P.overlap Q)
    {ω : ℝ} (hω : ω≤P.overlap Q) (a : α) :
    ω*(commonPart P Q h).mass a≤Q.mass a := by
  change ω*(min (P.mass a) (Q.mass a)/P.overlap Q)≤_
  calc
    _ ≤ P.overlap Q*(min (P.mass a) (Q.mass a)/P.overlap Q) :=
      mul_le_mul_of_nonneg_right hω (div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le)
    _ = min (P.mass a) (Q.mass a) := by field_simp
    _ ≤ _ := min_le_right _ _
end FiniteLaw

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The actual report flags, in the literal nested trial coordinates. -/
def sourceReportFlags {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b)) :
    WindowAssignments T n (sourceScheduledTrials T n) (Option Bool) b :=
  (sourceAssignmentCode T n (Option Bool) b).symm (fun j => (z j).1)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace PairedMechanisms
variable {Side : Type*} [Fintype Side] {m : ℕ} (M : PairedMechanisms Side m)

def hiddenSubset (S : Finset (Fin m)) (z : Reports Side m) : ℕ := ∑i : S,hiddenTrial (z i.val).1


end PairedMechanisms
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- IDs for precisely one local and one global collection at every genuine
 nonleaf of the complete source window tree. -/
def WindowCollection (T : ℕ → ℕ) : ℕ → Type
  | 0 => PEmpty
  | b+1 => Bool ⊕ (Fin (T b) × WindowCollection T b)

noncomputable instance windowCollectionFintype (T : ℕ → ℕ) :
    (b : ℕ) → Fintype (WindowCollection T b)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | b+1 => by
    letI := windowCollectionFintype T b
    exact inferInstanceAs (Fintype (Bool ⊕ (Fin (T b) × WindowCollection T b)))

def collectionCount (T n g : ℕ → ℕ) : (b : ℕ) → WindowCollection T b → ℕ
  | b+1, .inl false => n b
  | b+1, .inl true => g b
  | b+1, .inr (_,v) => collectionCount T n g b v

def collectionTrial (T n g : ℕ → ℕ) :
    (b : ℕ) → (v : WindowCollection T b) → Fin (collectionCount T n g b v) → WindowTrial T n g b
  | _+1, .inl false, j => .inl j
  | _+1, .inl true, j => .inr (.inl j)
  | b+1, .inr (u,v), j => .inr (.inr (u,collectionTrial T n g b v j))

def collectionFlags (T n g : ℕ → ℕ) {A : Type} :
    (b : ℕ) → WindowAssignments T n g A b → (v : WindowCollection T b) →
      Fin (collectionCount T n g b v) → A
  | _+1, d, .inl false => d.1
  | _+1, d, .inl true => d.2.1
  | b+1, d, .inr (u,v) => collectionFlags T n g b (d.2.2 u) v

/-- This is the source hidden-count predicate, before any conditioning on fit. -/
def HiddenCollectionConditions (T n g : ℕ → ℕ) (ω : ℝ) :
    (b : ℕ) → WindowAssignments T n g (Option Bool) b → Prop
  | 0, _ => True
  | b+1, d =>
      (n b:ℝ)*ω^2/2≤∑i,(hiddenTrial (d.1 i):ℝ) ∧
      (g b:ℝ)*ω^2/2≤∑i,(hiddenTrial (d.2.1 i):ℝ) ∧
      ∀u,HiddenCollectionConditions T n g ω b (d.2.2 u)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Numerical cap forced by at least half the mean number of hidden pairs. -/
def hiddenBinomialCap (m : ℕ) (ω : ℝ) : ℝ := Real.sqrt (4/((m:ℝ)*ω^2+2))

def hiddenSmoothingBound (m s : ℕ) (ω : ℝ) : ℝ :=
  (2:ℝ)^(s*s)*((2*Real.sqrt (4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)))^s *
    Real.sqrt (4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- One metadata event, fixed before choosing a coefficient, controls
 local and global smoothing and all internal central-third tests. -/
def SourceTypical {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ) (ω a : ℝ)
    (z : Reports Side (SourceTrialCount T n (b+1))) : Prop :=
  HiddenCollectionConditions T n (sourceScheduledTrials T n) ω (b+1)
    (sourceReportFlags T n (b+1) z) ∧
  sourceNoncentralMass T n (sourceScheduledTrials T n) s (sourceLocalCenter T n)
    (sourceScheduledShift T n) (fun j => centralThird (T j)) (b+1)
    (sourceReportFlags T n (b+1) z) 0<a

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceSparseCount (T : ℕ → ℕ) (s b : ℕ) : ℕ :=
  2^s*∏j∈Finset.range b,T (j+1)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem abs_expect_pow_le (P : FiniteLaw α) (F : α → ℝ) (t : ℕ) :
    |P.expect F|^t ≤ P.expect (fun a => |F a|^t) := by
  have habs : |P.expect F| ≤ P.expect (fun a => |F a|) := by
    calc
      _ ≤ ∑a, |P.mass a*F a| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul,abs_of_nonneg (P.nonneg _)]; rfl
  apply (pow_le_pow_left₀ (abs_nonneg _) habs t).trans
  simpa only [smul_eq_mul,expect] using
    (convexOn_pow (𝕜:=ℝ) t).map_sum_le (t:=Finset.univ)
      (w:=P.mass) (p:=fun a => |F a|) (fun a _ => P.nonneg a) P.total (fun a _ => (show |F a| ∈ Set.Ici (0:ℝ) from abs_nonneg (F a)))

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

def commonClipEvent (B : Finset α) (f : α → ℝ) : Finset α :=
  B.filter (fun a => 1/2 ≤ f a)

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A pair produced by genuine common-event normalized conditioning. The
 outcome space and public decoder remain unchanged. -/
structure ClippedOracle {α : Type*} [Fintype α] (P Q : FiniteLaw α) (k : ℕ) (e V : ℝ) where
  first : FiniteLaw α
  second : FiniteLaw α
  score : α → ℝ
  density : ∀a,second.mass a=first.mass a*(1+score a)
  likelihood_nonneg : ∀a,0 ≤ 1+score a
  centered : first.expect score=0
  moment : first.evenMomentSq score k ≤ V
  first_tv : first.tv P ≤ e
  second_tv : second.tv Q ≤ e

end TraceReconstruction

noncomputable section

noncomputable section

noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

local instance (priority := 10000) instDecidableEqProd_solutions {α β : Type*} : DecidableEq (α × β) := Classical.decEq _

def sourceCenteredBudget (T : ℕ → ℕ) (s b k : ℕ) (L : ℝ) : ℝ :=
  (((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b)/
    (1-((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace ClippedOracle
variable {α β : Type*} [Fintype α] [Fintype β]
    {P Q : FiniteLaw α} {k : ℕ} {e V : ℝ}

def prod (C : ClippedOracle P Q k e V) (R : FiniteLaw β) :
    ClippedOracle (P.prod R) (Q.prod R) k e V where
  first := C.first.prod R
  second := C.second.prod R
  score := fun x => C.score x.1
  density x := by
    change C.second.mass x.1*R.mass x.2=(C.first.mass x.1*R.mass x.2)*(1+C.score x.1)
    rw [C.density]; ring
  likelihood_nonneg x := C.likelihood_nonneg x.1
  centered := by
    rw [FiniteLaw.expect_prod]
    simp_rw [FiniteLaw.expect_const]
    exact C.centered
  moment := by
    unfold FiniteLaw.evenMomentSq
    rw [FiniteLaw.expect_prod]
    simp_rw [FiniteLaw.expect_const]
    exact C.moment
  first_tv := by rw [FiniteLaw.tv_prod_eq_left]; exact C.first_tv
  second_tv := by rw [FiniteLaw.tv_prod_eq_left]; exact C.second_tv
end ClippedOracle

/-- A finite genuine approximate oracle pair with a common complete-trace
 decoder. It does not include an overlap or any unproved scale conclusion. -/
structure OracleTracePair (q : ℝ) (x y : List Bool) (k : ℕ) (E V : ℝ) where
  Outcome : Type
  finiteOutcome : Fintype Outcome
  first : @FiniteLaw Outcome finiteOutcome
  second : @FiniteLaw Outcome finiteOutcome
  decode : Outcome → List Bool
  first_simulation : @ApproximatesTrace Outcome finiteOutcome q first decode x E
  second_simulation : @ApproximatesTrace Outcome finiteOutcome q second decode y E
  score : Outcome → ℝ
  density : ∀a,second.mass a=first.mass a*(1+score a)
  likelihood_nonneg : ∀a,0≤1+score a
  centered : first.expect score=0
  moment : @FiniteLaw.evenMomentSq Outcome finiteOutcome first score k ≤ V

end TraceReconstruction


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem expect_nonneg (P : FiniteLaw α) (F : α → ℝ) (hF : ∀a,0≤F a) : 0≤P.expect F :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (hF a))

theorem evenMomentSq_nonneg (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) :
    0≤P.evenMomentSq F k := Real.rpow_nonneg (P.expect_nonneg _ (fun _ => by positivity)) _

theorem evenMomentSq_pow (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) (hk : 1≤k) :
    (P.evenMomentSq F k)^k=P.expect (fun a => |F a|^(2*k)) := by
  unfold evenMomentSq
  rw [one_div,Real.rpow_inv_natCast_pow (P.expect_nonneg _ (fun _ => by positivity)) (by omega)]

theorem expect_even_pow_le_of_moment (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) (hk : 1≤k)
    {V : ℝ} (h : P.evenMomentSq F k≤V) :
    P.expect (fun a => |F a|^(2*k))≤V^k := by
  rw [←P.evenMomentSq_pow F k hk]
  exact pow_le_pow_left₀ (P.evenMomentSq_nonneg F k) h k

theorem secondMoment_le_evenMomentSq (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) (hk : 1≤k) :
    P.expect (fun a => F a^2)≤P.evenMomentSq F k := by
  have hn : 0≤P.expect (fun a => F a^2) := P.expect_nonneg _ (fun _ => sq_nonneg _)
  have hj := P.abs_expect_pow_le (fun a => F a^2) k
  simp only [abs_of_nonneg hn,abs_pow,←pow_mul] at hj
  have hr := Real.rpow_le_rpow (pow_nonneg hn k) hj (by positivity : 0≤(k:ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hn (by omega)] at hr
  simpa only [evenMomentSq,one_div] using hr

theorem affinity_coordinateProduct {n : ℕ} (P Q : Fin n → FiniteLaw α) :
    (coordinateProduct P).affinity (coordinateProduct Q)=∏i,(P i).affinity (Q i) := by
  unfold affinity coordinateProduct
  simp only
  have he (a : Fin n → α) :
      Real.sqrt (∏i,(P i).mass (a i))*Real.sqrt (∏i,(Q i).mass (a i))=
        ∏i,Real.sqrt ((P i).mass (a i))*Real.sqrt ((Q i).mass (a i)) := by
    rw [Real.sqrt_prod _ (fun i _ => (P i).nonneg (a i)),
      Real.sqrt_prod _ (fun i _ => (Q i).nonneg (a i)),Finset.prod_mul_distrib]
  simp_rw [he]
  exact (Fintype.prod_sum (fun (i : Fin n) a => Real.sqrt ((P i).mass a)*Real.sqrt ((Q i).mass a))).symm

theorem one_sub_prod_le_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h0 : ∀i∈S,0≤f i) (h1 : ∀i∈S,f i≤1) :
    1-∏i∈S,f i≤∑i∈S,(1-f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    have H := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hs : 0≤∑i∈S,(1-f i) := Finset.sum_nonneg (fun i hi => sub_nonneg.mpr (h1 i (Finset.mem_insert_of_mem hi)))
    have hm := mul_le_mul_of_nonneg_left H (h0 a (Finset.mem_insert_self a S))
    have hm' := mul_le_mul_of_nonneg_right (h1 a (Finset.mem_insert_self a S)) hs
    nlinarith

theorem hellingerSq_coordinateProduct_le {n : ℕ} (P Q : Fin n → FiniteLaw α) :
    (coordinateProduct P).hellingerSq (coordinateProduct Q)≤∑i,(P i).hellingerSq (Q i) := by
  simp_rw [hellingerSq_eq]
  rw [affinity_coordinateProduct]
  have h := one_sub_prod_le_sum Finset.univ (fun i => (P i).affinity (Q i))
    (fun i _ => affinity_nonneg _ _) (fun i _ => affinity_le_one _ _)
  have he : (∑i,(2-2*(P i).affinity (Q i)))=2*∑i,(1-(P i).affinity (Q i)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [he]
  linarith

@[simp] theorem hellingerSq_self (P : FiniteLaw α) : P.hellingerSq P=0 := by
  simp [hellingerSq]

theorem hellingerSq_symm (P Q : FiniteLaw α) : P.hellingerSq Q=Q.hellingerSq P := by
  apply Finset.sum_congr rfl; intro a _; ring

end TraceReconstruction.FiniteLaw


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Amplification

Oracle products, mixed powers, padding, warmup and nested template Hellinger estimates, overlap, and block assembly.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem coordinateWord_constant (w : List Bool) (n : ℕ) :
    coordinateWord (fun _ : Fin n => w)=pureAtomRun w n := by
  induction n with
  | zero => simp [coordinateWord,pureAtomRun]
  | succ n ih =>
    rw [coordinateWord_succ,ih]
    simp only [pureAtomRun,List.replicate_succ,List.flatten_cons]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem hellingerSq_mixedProduct_le {n : ℕ} (P Q : FiniteLaw α) {V : ℝ}
    (hH : P.hellingerSq Q ≤ V) (τ σ : Fin n → Bool) :
    (coordinateProduct (fun i => if τ i then Q else P)).hellingerSq
      (coordinateProduct (fun i => if σ i then Q else P)) ≤
      (∑i,if τ i=σ i then (0:ℝ) else 1)*V := by
  apply (hellingerSq_coordinateProduct_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  cases τ i <;> cases σ i <;> simp only [Bool.false_eq_true,Bool.true_eq_false,
    ite_false,ite_true,zero_mul,one_mul,hellingerSq_self,le_refl]
  · exact hH
  · rw [hellingerSq_symm]; exact hH

end FiniteLaw

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- An exact common prefix and suffix are observed as ordinary independent
 complete traces. They neither change the score moment nor cost simulation
 error. This is the source's deterministic residual convention. -/
def OracleTracePair.pad {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (u v : List Bool) :
    OracleTracePair q (u++x++v) (u++y++v) k E V := by
  let := C.finiteOutcome
  let P := listTraceLaw q hq u u.length le_rfl
  let Q := listTraceLaw q hq v v.length le_rfl
  refine {
    Outcome := (BoundedTrace u.length × C.Outcome) × BoundedTrace v.length
    finiteOutcome := inferInstance
    first := (P.prod C.first).prod Q
    second := (P.prod C.second).prod Q
    decode := fun z => z.1.1.val++C.decode z.1.2++z.2.val
    score := fun z => C.score z.1.2
    density := by
      intro z
      change (P.mass z.1.1*C.second.mass z.1.2)*Q.mass z.2=_
      rw [C.density]
      change _=(P.mass z.1.1*C.first.mass z.1.2)*Q.mass z.2*(1+C.score z.1.2)
      ring
    likelihood_nonneg := fun z => C.likelihood_nonneg z.1.2
    centered := by
      simp only [FiniteLaw.expect_prod,FiniteLaw.expect_const,C.centered]
    moment := by
      simpa only [FiniteLaw.evenMomentSq,FiniteLaw.expect_prod,FiniteLaw.expect_const] using C.moment
    first_simulation := by
      have H := ((listTraceLaw_simulates q hq u u.length le_rfl).approximate.append hq
        C.first_simulation).append hq (listTraceLaw_simulates q hq v v.length le_rfl).approximate
      simpa only [zero_add,add_zero] using H
    second_simulation := by
      have H := ((listTraceLaw_simulates q hq u u.length le_rfl).approximate.append hq
        C.second_simulation).append hq (listTraceLaw_simulates q hq v v.length le_rfl).approximate
      simpa only [zero_add,add_zero] using H }

def centeredLeftResidual (N P : ℕ) : ℕ := N/2-1-(P/2-1)
def centeredRightResidual (N P : ℕ) : ℕ := N-(centeredLeftResidual N P+P)

end TraceReconstruction



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The number of differing labels of complementary templates is bounded
 by the actual motif length, without any assumption that it fills the word. -/
theorem templateType_difference_count (N a L : ℕ) (sign : Fin L → Bool) (τ σ : Bool) :
    (∑i : Fin N,if templateType N a L sign τ i=templateType N a L sign σ i then (0:ℝ) else 1) ≤ L := by
  let S : Finset (Fin N) := Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a+L)
  have hi (i : S) : a ≤ i.val.val ∧ i.val.val < a+L := (Finset.mem_filter.mp i.property).2
  let f : S → Fin L := fun i => ⟨i.val.val-a,by have h := hi i; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h := congrArg Fin.val hij
    have h₁ := hi i
    have h₂ := hi j
    dsimp [f] at h
    apply Subtype.ext
    apply Fin.ext
    omega
  have hc : S.card ≤ L := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  calc
    _ ≤ ∑i : Fin N,if i∈S then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : i∈S
      · rw [ite_eq_left h]; split_ifs <;> norm_num
      · have h' : ¬(a ≤ i.val ∧ i.val < a+L) := by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using h
        simp [templateType,h',h]
    _ = (S.card:ℝ) := by simp
    _ ≤ L := by exact_mod_cast hc

/-- Actual paired finite observations with a common complete-trace decoder
 and a squared Hellinger bound. This auxiliary structure is constructed from
 the source score oracle and closed under literal template substitution. -/
structure HellingerTracePair (q : ℝ) (x y : List Bool) (E V : ℝ) where
  Outcome : Type
  finiteOutcome : Fintype Outcome
  first : @FiniteLaw Outcome finiteOutcome
  second : @FiniteLaw Outcome finiteOutcome
  decode : Outcome → List Bool
  first_simulation : @ApproximatesTrace Outcome finiteOutcome q first decode x E
  second_simulation : @ApproximatesTrace Outcome finiteOutcome q second decode y E
  bound : @FiniteLaw.hellingerSq Outcome finiteOutcome first second ≤ V

def OracleTracePair.hellinger {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hk : 1 ≤ k) : HellingerTracePair q x y E V := by
  let := C.finiteOutcome
  exact {
    Outcome := C.Outcome
    finiteOutcome := C.finiteOutcome
    first := C.first
    second := C.second
    decode := C.decode
    first_simulation := C.first_simulation
    second_simulation := C.second_simulation
    bound := (C.first.hellingerSq_le_score C.second C.score C.density).trans
      ((C.first.secondMoment_le_evenMomentSq C.score k hk).trans C.moment) }

def HellingerTracePair.mix {q E V : ℝ} {x y : List Bool} (C : HellingerTracePair q x y E V)
    (hq : q∈Set.Icc 0 1) {N : ℕ} (τ σ : Fin N → Bool) :
    HellingerTracePair q (coordinateWord (fun i => if τ i then y else x))
      (coordinateWord (fun i => if σ i then y else x)) ((N:ℝ)*E)
      ((∑i,if τ i=σ i then (0:ℝ) else 1)*V) := by
  let := C.finiteOutcome
  have ha (ρ : Fin N → Bool) : ApproximatesTrace q
      (FiniteLaw.coordinateProduct (fun i => if ρ i then C.second else C.first))
      (fun z => coordinateWord (fun i => C.decode (z i)))
      (coordinateWord (fun i => if ρ i then y else x)) ((N:ℝ)*E) := by
    have H := coordinateProduct_approximates hq
      (fun i => if ρ i then C.second else C.first) (fun _ => C.decode)
      (fun i => if ρ i then y else x) (fun _ => E) (fun i => ?_)
    · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H
    · cases ρ i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact C.first_simulation
      · exact C.second_simulation
  exact {
    Outcome := Fin N → C.Outcome
    finiteOutcome := inferInstance
    first := FiniteLaw.coordinateProduct (fun i => if τ i then C.second else C.first)
    second := FiniteLaw.coordinateProduct (fun i => if σ i then C.second else C.first)
    decode := fun z => coordinateWord (fun i => C.decode (z i))
    first_simulation := ha τ
    second_simulation := ha σ
    bound := FiniteLaw.hellingerSq_mixedProduct_le C.first C.second C.bound τ σ }

def HellingerTracePair.weaken {q E V W : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (h : V ≤ W) : HellingerTracePair q x y E W :=
  { C with bound := C.bound.trans h }

def HellingerTracePair.template {q E V : ℝ} {x y : List Bool} (C : HellingerTracePair q x y E V)
    (hq : q∈Set.Icc 0 1) (N a L : ℕ) (sign : Fin L → Bool) :
    HellingerTracePair q
      (complementaryWords N a L sign (fun τ => if τ then y else x) false)
      (complementaryWords N a L sign (fun τ => if τ then y else x) true) ((N:ℝ)*E) ((L:ℝ)*V) := by
  let := C.finiteOutcome
  let D := C.mix hq (templateType N a L sign false) (templateType N a L sign true)
  have hV : 0 ≤ V := (FiniteLaw.hellingerSq_nonneg _ _).trans C.bound
  exact D.weaken (mul_le_mul_of_nonneg_right (templateType_difference_count N a L sign false true) hV)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem templateType_one_count (N a L : ℕ) (sign : Fin L → Bool) (τ : Bool) :
    (∑i : Fin N,if false=templateType N a L sign τ i then (0:ℝ) else 1) ≤ L := by
  apply le_trans _ (templateType_difference_count N a L sign false true)
  apply Finset.sum_le_sum
  intro i _
  by_cases h : a ≤ i.val ∧ i.val < a+L
  · simp only [templateType,dite_eq_left h]
    cases hs : sign ⟨i.val-a,by omega⟩ <;> cases τ <;> norm_num
  · simp [templateType,h]

def HellingerTracePair.pure_template {q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (hq : q∈Set.Icc 0 1)
    (N a L : ℕ) (sign : Fin L → Bool) (τ : Bool) :
    HellingerTracePair q (pureAtomRun x N)
      (complementaryWords N a L sign (fun υ => if υ then y else x) τ) ((N:ℝ)*E) ((L:ℝ)*V) := by
  let := C.finiteOutcome
  let D := C.mix hq (fun _ : Fin N => false) (templateType N a L sign τ)
  have hV : 0 ≤ V := (FiniteLaw.hellingerSq_nonneg _ _).trans C.bound
  have W := D.weaken (mul_le_mul_of_nonneg_right (templateType_one_count N a L sign τ) hV)
  simp only [Bool.false_eq_true,ite_false,coordinateWord_constant] at W
  exact W

theorem bool_word_eta (w : Bool → List Bool) : (fun τ => if τ then w true else w false)=w := by
  funext τ
  cases τ <;> rfl

end TraceReconstruction



noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem OracleTracePair.error_nonneg {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) : 0 ≤ E := by
  let := C.finiteOutcome
  have h := C.first_simulation (fun _ => 0) (fun _ => ⟨le_rfl,zero_le_one⟩)
  exact (abs_nonneg _).trans h

/-- Conversion of a produced genuine oracle into the manuscript invariant.
 The scalar bounds here are exactly those to be discharged by scale margins. -/
def OracleTracePair.toConcrete {q E V N Δ d ω F : ℝ} {x y : List Bool} {k i h : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1)
    (hlen : x.length=y.length) (hne : x≠y) (hlo : N/2 ≤ (x.length:ℝ))
    (hhi : (x.length:ℝ) ≤ N) (herror : E/(x.length:ℝ) ≤ ((i:ℝ)+1)*Δ)
    (hV : V ≤ N^(-d)) (hhlo : x.length ≤ h) (hhhi : (h:ℝ) ≤ F*(x.length:ℝ))
    (hov : ω ≤ listTraceOverlap q hq (pureAtomRun x h) (pureAtomRun x (h+1))) :
    ConcreteLevelPair q hq N Δ d ω F i k := {
  left := x
  right := y
  equalLength := hlen
  different := hne
  length_lower := hlo
  length_upper := hhi
  Outcome := C.Outcome
  finiteOutcome := C.finiteOutcome
  firstLaw := C.first
  secondLaw := C.second
  decode := C.decode
  error := E
  error_nonneg := C.error_nonneg
  normalized_error := herror
  first_simulation := C.first_simulation
  second_simulation := C.second_simulation
  score := C.score
  density := C.density
  score_bound := C.moment.trans hV
  overlapCount := h
  overlapCount_lower := hhlo
  overlapCount_upper := hhhi
  power_overlap := hov }

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialOracle

Actual initial scores and anchors, count partitions and typicality, clipped metadata, common decoding, sharp hidden-count energy, tails, and budget caps.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def initialMomentRatio (u m : ℕ) (q w : ℝ) : ℝ :=
  w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)

def initialSignedBudget (u m l R s : ℕ) (π : IntSeries) (θ q w : ℝ) : ℝ :=
  (∑r∈Finset.range R,w^(2*r)*signedInitialDegreeBound u m r s π θ l)+
    4*(initialMomentRatio u m q w)^R/(1-initialMomentRatio u m q w)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem evenMomentSq_le_of_expect (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) (hk : 1≤k)
    {V : ℝ} (hV : 0≤V) (h : P.expect (fun a => |F a|^(2*k))≤V^k) :
    P.evenMomentSq F k≤V := by
  have H := Real.rpow_le_rpow (P.expect_nonneg _ (fun _ => by positivity)) h (by positivity : 0≤(k:ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hV (by omega)] at H
  simpa only [FiniteLaw.evenMomentSq,one_div] using H

theorem tv_sigma_eq {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]
    (M : FiniteLaw ι) (P Q : ∀i,FiniteLaw (β i)) :
    (M.sigma P).tv (M.sigma Q)=M.expect (fun i => (P i).tv (Q i)) := by
  simp only [tv,sigma,expect,Fintype.sum_sigma,←mul_sub,abs_mul,abs_of_nonneg (M.nonneg _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.mul_sum]
  ring

end FiniteLaw
namespace ClippedOracle
variable {α : Type*} [Fintype α] {P Q : FiniteLaw α} {k : ℕ} {e V E W : ℝ}

def weaken (C : ClippedOracle P Q k e V) (he : e≤E) (hV : V≤W) : ClippedOracle P Q k E W where
  first := C.first
  second := C.second
  score := C.score
  density := C.density
  likelihood_nonneg := C.likelihood_nonneg
  centered := C.centered
  moment := C.moment.trans hV
  first_tv := C.first_tv.trans he
  second_tv := C.second_tv.trans he

def trivial (P Q : FiniteLaw α) (k : ℕ) (hk : 1≤k) : ClippedOracle P Q k 1 0 where
  first := P
  second := P
  score := fun _ => 0
  density := fun _ => by ring
  likelihood_nonneg := fun _ => by norm_num
  centered := by simp [FiniteLaw.expect]
  moment := by
    apply P.evenMomentSq_le_of_expect _ k hk (by norm_num)
    simp [FiniteLaw.expect,zero_pow (by omega : 2*k≠0)]
  first_tv := by simp [FiniteLaw.tv]
  second_tv := FiniteLaw.tv_le_one _ _

/-- Reported metadata is retained, so the squared moment of a normalized
 score assembles without a mixing penalty. No conditioning of the original
 latent metadata distribution occurs. -/
def sigma {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]
    (M : FiniteLaw ι) (P Q : ∀i,FiniteLaw (β i)) (e : ι → ℝ)
    (k : ℕ) (hk : 1≤k) (V : ℝ) (hV : 0≤V)
    (C : ∀i,ClippedOracle (P i) (Q i) k (e i) V) :
    ClippedOracle (M.sigma P) (M.sigma Q) k (M.expect e) V where
  first := M.sigma (fun i => (C i).first)
  second := M.sigma (fun i => (C i).second)
  score := fun a => (C a.1).score a.2
  density := fun a => by dsimp only [FiniteLaw.sigma]; rw [(C a.1).density]; ring
  likelihood_nonneg := fun a => (C a.1).likelihood_nonneg a.2
  centered := by
    rw [FiniteLaw.expect_sigma]
    simp_rw [(C _).centered]
    simp [FiniteLaw.expect]
  moment := by
    apply FiniteLaw.evenMomentSq_le_of_expect _ _ k hk hV
    rw [FiniteLaw.expect_sigma]
    calc
      _ ≤ M.expect (fun _ => V^k) := M.expect_mono (fun i =>
        (C i).first.expect_even_pow_le_of_moment _ k hk (C i).moment)
      _ = _ := M.expect_const _
  first_tv := by
    rw [FiniteLaw.tv_sigma_eq]
    exact M.expect_mono (fun i => (C i).first_tv)
  second_tv := by
    rw [FiniteLaw.tv_sigma_eq]
    exact M.expect_mono (fun i => (C i).second_tv)

end ClippedOracle
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem translated_fair_eval (g : ℕ) (c : ℤ) (F : ℤ → ℝ) :
    (∑X∈(translateSeries c (fairSeries g)).coeff.support,
      (translateSeries c (fairSeries g)).coeff X*F X)=
    ∑k∈Finset.range (g+1),fairBinomial g k*F (c+k) := by
  have H := congrArg (fun p : IntSeries => Finsupp.linearCombination ℝ F p.coeff)
    (congrArg (translateSeries c) (fairSeries_sum g))
  simp only [translateSeries,Finset.mul_sum,AddMonoidAlgebra.single_mul_single,one_mul,
    AddMonoidAlgebra.coeff_sum,AddMonoidAlgebra.coeff_single,map_sum,
    Finsupp.linearCombination_single,smul_eq_mul] at H
  exact H

/-- The literal initial anchor after conditioning the paired side outputs. -/
def posteriorAnchorSeries {ι : Type*} [Fintype ι] (c : ℤ) (d : ι → Option Bool) : IntSeries :=
  translateSeries (c-(∑i,(visibleOnes (d i):ℤ))-(∑i,hiddenTrial (d i)))
    (fairSeries (∑i,hiddenTrial (d i)))

theorem posterior_anchor_average {ι : Type*} [Fintype ι]
    (c : ℤ) (d : ι → Option Bool) (F : ℤ → ℝ) :
    (∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i))*
      F (c-∑i,(bitIndex (b i):ℤ)))=
    ∑X∈(posteriorAnchorSeries c d).coeff.support,(posteriorAnchorSeries c d).coeff X*F X := by
  rw [posterior_count_average_reflected d (fun z => F (c-z)),posteriorAnchorSeries,translated_fair_eval]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  ring

theorem posteriorAnchorSeries_nonneg {ι : Type*} [Fintype ι]
    (c : ℤ) (d : ι → Option Bool) (X : ℤ) : 0 ≤ (posteriorAnchorSeries c d).coeff X :=
  translated_binomial_nonneg _ _ _

theorem posteriorAnchorSeries_total {ι : Type*} [Fintype ι]
    (c : ℤ) (d : ι → Option Bool) :
    ∑X∈(posteriorAnchorSeries c d).coeff.support,(posteriorAnchorSeries c d).coeff X=1 := by
  have H := posterior_anchor_average c d (fun _ => 1)
  simp only [mul_one] at H
  rw [←H]
  exact (FiniteLaw.indexedProduct (fun i => flagPosterior (d i))).total

namespace PairedMechanisms
variable {Side α : Type*} [Fintype Side] [Fintype α] {J : ℕ}

def emissionOracle (M : PairedMechanisms Side J) (K : (Fin J → Bool) → FiniteLaw α) :
    FiniteLaw (Reports Side J × α) :=
  M.reports.joint (fun z => (orientationsGiven z).mixture K)

end PairedMechanisms


/-- Initial observations retain the central count with its original binomial law. -/
def countedMotifLaw {u m : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X)
    (hπsum : ∑X∈π.coeff.support,π.coeff X=1) (s : ℕ) (τ : ℝ) :
    FiniteLaw (BoundedMarks (u*m)) :=
  (boundedCountLaw (le_refl (u*m)) (1-primitiveErasure q) (primitiveRetention_mem hq)).sigma
    (fun l => conditionalMotifLaw (by omega) off hsafe hq π hπ hπsum s τ)


end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The actual displaced primitive slot in a period. -/
def motifOffset {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (s : ℕ) (X : ℤ) (τ : ℝ) (j : ℤ) : Fin m :=
  ⟨off.val+(motifShift (motifIndicator s (j-X)) ((prouhetSeries s).coeff (j-X)) τ).val-1, by
    have H := (motifShift (motifIndicator s (j-X)) ((prouhetSeries s).coeff (j-X)) τ).isLt
    omega⟩

def motifPeriodWord {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (u s : ℕ) (X : ℤ) (τ : ℝ) : List Bool :=
  periodString m u (fun j => motifOffset off hi s X τ j.val)

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Three chronological streams, with side pairs independent across slots.
This forgets flags but does not separate any marks inside the central list. -/
def decodePairedEmission {Side α : Type*} {J : ℕ}
    (side : Side → List Bool) (central : α → List Bool) (z : Reports Side J × α) : List Bool :=
  coordinateWord (fun i => side (z.1 i).2.1) ++ central z.2 ++
    coordinateWord (fun i => side (z.1 i).2.2)

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact initial paired prefix and complementary suffix sizes. -/
def initialPrefixPeriods {J : ℕ} (k : ℕ) (b : Fin J → Bool) : ℕ :=
  ∑ i : Fin J, (k+bitIndex (b i))
def initialSuffixPeriods {J : ℕ} (k : ℕ) (b : Fin J → Bool) : ℕ :=
  ∑ i : Fin J, (k+(1-bitIndex (b i)))

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

abbrev InitialMetadata (Side : Type*) (J N : ℕ) := Reports Side J × Fin (N+1)
abbrev InitialObservation (Side : Type*) (J N : ℕ) :=
  Σz : InitialMetadata Side J N, Fin z.2.val → PrimitiveMark

def initialMetadataLaw {Side : Type*} [Fintype Side] {J : ℕ}
    (M : PairedMechanisms Side J) (N : ℕ) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    FiniteLaw (InitialMetadata Side J N) :=
  M.reports.prod (boundedCountLaw (le_refl N) (1-primitiveErasure q) (primitiveRetention_mem hq))

def initialConditionalLaw {Side : Type*} [Fintype Side] {J K m : ℕ}
    (off : Fin m) (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (s : ℕ) (τ : ℝ)
    (z : InitialMetadata Side J (K*m)) : FiniteLaw (Fin z.2.val → PrimitiveMark) :=
  conditionalMotifLaw (by have H:=z.2.isLt; omega) off hsafe hq
    (posteriorAnchorSeries c (fun i => (z.1 i).1))
    (posteriorAnchorSeries_nonneg c _) (posteriorAnchorSeries_total c _) s τ

def initialSigmaLaw {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (s : ℕ) (τ : ℝ) :
    FiniteLaw (InitialObservation Side J (K*m)) :=
  (initialMetadataLaw M (K*m) hq).sigma (initialConditionalLaw off hsafe hq c s τ)

def decodeInitialObservation {Side : Type*} {J N : ℕ} (side : Side → List Bool)
    (z : InitialObservation Side J N) : List Bool :=
  decodePairedEmission side decodeBoundedMarks (z.1.1,⟨z.1.2,z.2⟩)

/-- This is the literal count-typicality condition; it does not change the
 central count's original binomial law. -/
def initialCountAdmissible (N : ℕ) (q : ℝ) (l : Fin (N+1)) : Prop :=
  (l.val:ℝ)/(N:ℝ)∈Set.Icc (1-q^2) (1-q^2/4) ∧
    1  ≤  (N:ℝ)*((l.val:ℝ)/(N:ℝ))*(1-(l.val:ℝ)/(N:ℝ))

def initialMetadataGood {Side : Type*} {J N : ℕ} (q ω : ℝ)
    (z : InitialMetadata Side J N) : Prop :=
  initialCountAdmissible N q z.2 ∧ (J:ℝ)*ω^2/2  ≤  ∑i,(hiddenTrial (z.1 i).1:ℝ)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def purePeriodCoefficient {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m) : (Fin l → Bool) → ℝ :=
  averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
    (defectAtRank (Finset.univ.image (periodSlot (u:=u) (fun _ => off))))

/-- The pure comparison retains all low-degree cancellation, not just its
 total defect density. -/
def initialPureDegreeBound (u m r s : ℕ) (π : IntSeries) (θ : ℝ) (l : ℕ) : ℝ :=
  if r=0 then 0 else
    2*(Fintype.card (Fin r → GapDifference):ℝ)*
      (∑k : Fin r → GapDifference, if k=unchangedPattern r then 0 else purePatternBound u m r s π θ k)+
    2*((Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l*(2*Real.exp (-(m:ℝ)/(1024*u))))))^2

def initialPureBudget (u m l R s : ℕ) (π : IntSeries) (θ q w : ℝ) : ℝ :=
  (∑r∈Finset.range R,w^(2*r)*initialPureDegreeBound u m r s π θ l)+
    4*(initialMomentRatio u m q w)^R/(1-initialMomentRatio u m q w)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def purePeriodDensity {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m) (q : ℝ) :
    (Fin l → PrimitiveMark) → ℝ := multilinear (purePeriodCoefficient hl off) (primitiveScore q)

theorem purePeriodDensity_nonneg {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (x : Fin l → PrimitiveMark) :
    0 ≤ purePeriodDensity hl off q x := by
  have H := (conditionalPrimitiveLaw hl q hq (defectTypes (periodSlot (u:=u) (fun _ => off)))).nonneg x
  rw [conditionalDefectLaw_density] at H
  exact nonneg_of_mul_nonneg_right H (primitive_product_mass_pos hq x)

theorem purePeriodDensity_total {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    ((primitiveMarkLaw q hq false).product l).expect (purePeriodDensity hl off q)=1 := by
  have H := (conditionalPrimitiveLaw hl q hq (defectTypes (periodSlot (u:=u) (fun _ => off)))).total
  simpa only [conditionalDefectLaw_density,FiniteLaw.expect,purePeriodDensity,purePeriodCoefficient] using H

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def initialPureConditionalLaw {Side : Type*} {J K m : ℕ} (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (z : InitialMetadata Side J (K*m)) :
    FiniteLaw (Fin z.2.val → PrimitiveMark) :=
  conditionalPrimitiveLaw (by have H:=z.2.isLt; omega) q hq
    (defectTypes (periodSlot (u:=K) (fun _ => off)))

def initialPureSigmaLaw {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (off : Fin m) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    FiniteLaw (InitialObservation Side J (K*m)) :=
  (initialMetadataLaw M (K*m) hq).sigma (initialPureConditionalLaw off hq)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The half-mean hidden-count event yields the correct L², not supremum,
 exponent J^{-s-1/2} in the initial Prouhet cancellation. -/
def hiddenSignedL2Bound (J s : ℕ) (ω : ℝ) : ℝ :=
  ((2:ℝ)^(s*s))^2*((2*Real.sqrt (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2)))^s)^2*
    Real.sqrt (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2))

def hiddenUnsignedL2Bound (J s : ℕ) (ω : ℝ) : ℝ :=
  ((2:ℝ)^s)^2*hiddenBinomialCap J ω

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def initialDifferenceCap (d : ℕ) (q : ℝ) : ℝ :=
  2*Real.sqrt (8*((d:ℝ)+1)/q^2)

/-- All q dependence of a fixed rank-difference estimate is exposed here.
 The powers of u and m are retained exactly, including both large-gap gains. -/
def initialPrefactorCap (u m r d : ℕ) (q : ℝ) : ℝ :=
  144*((u*m:ℕ):ℝ)*(2:ℝ)^(2*r)*(initialDifferenceCap d q)^(2*d+r+2) /
    (((m:ℝ)/4)^d*Real.sqrt ((u:ℝ)*m/(2*(r+1:ℝ)))*
      (Real.sqrt ((m:ℝ)/4))^(r+1))

def initialRankTailCap (u m r : ℕ) : ℝ :=
  2*((Fintype.card (IncreasingTuple u r):ℝ)*
    (48*((r+1:ℕ):ℝ)*Real.sqrt (u*m:ℕ)*Real.exp (-(m:ℝ)/(1024*u))))^2

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def initialSignedPatternCap (J u m r s : ℕ) (q ω : ℝ) (k : Fin r → GapDifference) : ℝ :=
  if ∃a,k=linearPattern a then
    initialPrefactorCap u m r 1 q*periodCentralSumConstant u r*hiddenSignedL2Bound J s ω
  else initialPrefactorCap u m r (∑h,(k h).order) q*
    periodBoundedSumConstant u r (2*(2^s))*hiddenUnsignedL2Bound J s ω

def initialPurePatternCap (J u m r s : ℕ) (q ω : ℝ) (k : Fin r → GapDifference) : ℝ :=
  if ∃a,k=linearPattern a then
    initialPrefactorCap u m r 1 q*periodCentralSumConstant u r*hiddenSignedL2Bound J s ω
  else initialPrefactorCap u m r (∑h,(k h).order) q*
    periodCentralSumConstant u r*hiddenUnsignedL2Bound J s ω

def initialSignedDegreeCap (J u m r s : ℕ) (q ω : ℝ) : ℝ :=
  if r=0 then 0 else
    8*(Fintype.card (Fin r → GapDifference):ℝ)*
      (∑k : Fin r → GapDifference,if Odd (firstDifferenceCount k) then
        initialSignedPatternCap J u m r s q ω k else 0)+initialRankTailCap u m r

def initialPureDegreeCap (J u m r s : ℕ) (q ω : ℝ) : ℝ :=
  if r=0 then 0 else
    2*(Fintype.card (Fin r → GapDifference):ℝ)*
      (∑k : Fin r → GapDifference,if k=unchangedPattern r then 0 else
        initialPurePatternCap J u m r s q ω k)+initialRankTailCap u m r

/-- Scalar budgets independent of every actual report and count. The finite
 signed-pattern restriction is retained to preserve its three-difference gain. -/
def initialSignedCap (J u m R s : ℕ) (q ω w : ℝ) : ℝ :=
  (∑r∈Finset.range R,w^(2*r)*initialSignedDegreeCap J u m r s q ω)+
    4*(initialMomentRatio u m q w)^R/(1-initialMomentRatio u m q w)

def initialPureCap (J u m R s : ℕ) (q ω w : ℝ) : ℝ :=
  (∑r∈Finset.range R,w^(2*r)*initialPureDegreeCap J u m r s q ω)+
    4*(initialMomentRatio u m q w)^R/(1-initialMomentRatio u m q w)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def OracleTracePair.weaken {q E V E' V' : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hE : E ≤ E') (hV : V ≤ V') :
    OracleTracePair q x y k E' V' :=
  { C with
    first_simulation := fun F hF => (C.first_simulation F hF).trans hE
    second_simulation := fun F hF => (C.second_simulation F hF).trans hE
    moment := C.moment.trans hV }

def initialErrorCap (J K m k : ℕ) (q ω w : ℝ) : ℝ :=
  Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k)+
    (2*Real.exp (-((K*m:ℕ):ℝ)*q^4/64)+Real.exp (-(J:ℝ)*ω^4/16))

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialRates

Initial geometric parameters, moment depths, error and overlap rates, and production of the base induction pair.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

/-- Literal integer choices of the initial-pair construction, including the outer floors. -/
def sourceInitialM (N : ℝ) : ℕ := ⌊N^(62/125:ℝ)⌋₊
def sourceInitialK (N : ℝ) : ℕ := ⌊N^(123/250:ℝ)⌋₊
def sourceInitialPeriodSize (N : ℝ) : ℕ := 2*sourceInitialM N-1
def sourceInitialCapacity (N : ℝ) : ℕ := ⌊N/(sourceInitialPeriodSize N:ℝ)⌋₊
def sourceInitialJ (q N : ℝ) : ℕ :=
  ⌊((sourceInitialCapacity N:ℝ)-sourceInitialK N)/
    (2*(initialSideCount q (sourceInitialM N):ℝ)+1)⌋₊
def sourceInitialP (q N : ℝ) : ℕ :=
  sourceInitialJ q N*(2*initialSideCount q (sourceInitialM N)+1)+sourceInitialK N

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Source moment order is twice this integer. -/
def sourceHalfMoment (B D : ℕ) (n : ℝ) (i : ℕ) : ℕ :=
  ⌈(10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n/
    Real.log (sourceTargetScale B D n i)⌉₊

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

/-- Only arithmetic predicates on the literal source integers. -/
structure SourceInitialGeometry (q N : ℝ) : Prop where
  m_large : 128 ≤ sourceInitialM N
  K_pos : 0 < sourceInitialK N
  K_le_m : sourceInitialK N ≤ sourceInitialM N
  seed : 16 ≤ q^3*(sourceInitialM N:ℝ)
  count : 8 ≤ ((sourceInitialK N*sourceInitialM N:ℕ):ℝ)*q^2
  anchor_margin : 12*(sourceInitialJ q N+2^300+1) ≤ sourceInitialK N
  smoothing_margin : ((2*(2^300):ℕ):ℝ) < (sourceInitialK N:ℝ)/(3*(3000+1:ℝ))
  length_lower : N/2 ≤ (sourceInitialP q N:ℝ)*(sourceInitialPeriodSize N:ℝ)
  length_upper : (sourceInitialP q N:ℝ)*(sourceInitialPeriodSize N:ℝ) ≤ N

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N q w : ℕ→ℝ} {k : ℕ→ℕ}

def initialClipFactor (N q w : ℝ) : ℝ :=
  4*(initialMomentRatio (sourceInitialK N) (sourceInitialM N) q w/
    (1-initialMomentRatio (sourceInitialK N) (sourceInitialM N) q w))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

def sourceOverlapConstant (q : ℝ) : ℝ := (2:ℝ)^40/(q*initialOverlapLower q)

end TraceReconstruction


end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LayoutRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LayoutRates

Integer block schedules, rounding, length and trial margins, sparse gaps, and forced-anchor decay.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The source integer window size, with zero-based nesting index. -/
def sourceWindowSize (N : ℝ) (b : ℕ) (ε : ℝ) (j : ℕ) : ℕ :=
  4*⌊N^(scaleKappa b (j+1) ε)/4⌋₊

/-- At a nonroot node the source trial count is an even integer. -/
def sourceLocalTrials (P h : ℕ) : ℕ := 2*(P/(100*(2*h+1)))

/-- The root schedule count: the literal floor after subtracting its window. -/
def sourceRootTrials (N : ℝ) (S T h : ℕ) : ℕ :=
  (⌊N/(S:ℝ)⌋₊-T)/(2*h+1)

/-- Literal length and overlap-count state of one nested source block.
 `copies` and `trials` refer to the transition into this state. -/
structure SourceArithmeticStage where
  length : ℕ
  count : ℕ
  copies : ℕ
  trials : ℕ

def sourceArithmeticStages (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) :
    ℕ → SourceArithmeticStage
  | 0 => ⟨ell,k,1,0⟩
  | j+1 =>
    let prev := sourceArithmeticStages C N b ε ell k j
    let T := sourceWindowSize N b ε j
    let J := sourceRootTrials N prev.length T prev.count
    let P := if j+1=b then J*(2*prev.count+1)+T
      else ⌊N^(scaleA b (j+1) ε)/(prev.length:ℝ)⌋₊
    let m := if j+1=b then J else sourceLocalTrials P prev.count
    ⟨prev.length*P,⌈C*prev.count*P⌉₊,P,m⟩

def sourceArithmeticP (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (j : ℕ) : ℕ :=
  (sourceArithmeticStages C N b ε ell k (j+1)).copies

def sourceArithmeticTrials (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (j : ℕ) : ℕ :=
  (sourceArithmeticStages C N b ε ell k (j+1)).trials

def sourceArithmeticLength (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (j : ℕ) : ℕ :=
  (sourceArithmeticStages C N b ε ell k j).length

def sourceArithmeticCount (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (j : ℕ) : ℕ :=
  (sourceArithmeticStages C N b ε ell k j).count

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

def sourceDegreeCutoff (B : ℕ) : ℕ := 2^(10*B+40)

def sourceCancellationOrder (B D : ℕ) : ℕ :=
  ⌈100*(totalScoreExponent B D+(sourceDegreeCutoff B:ℝ)+B+10)/sourceEpsilon B D⌉₊

def sourceChannelLogConstant : ℝ := (2:ℝ)^40+1536+(32+3*primitivePeriodConstant)+1

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Levels outside the finite source block are irrelevant. Their harmless
 positive extension permits the global-index API of the finite tree lemmas. -/
def sourceBlockWindows (N : ℝ) (b : ℕ) (ε : ℝ) (j : ℕ) : ℕ :=
  if j<b then sourceWindowSize N b ε j else 24

structure SourceArithmeticBounds (C N F ε : ℝ) (s b ell k : ℕ) : Prop where
  lengths : ∀j ≤ b,N^(scaleA b j ε)/2 ≤ (sourceArithmeticLength C N b ε ell k j:ℝ) ∧
    (sourceArithmeticLength C N b ε ell k j:ℝ) ≤ N^(scaleA b j ε)
  counts : ∀j ≤ b,sourceArithmeticLength C N b ε ell k j ≤ sourceArithmeticCount C N b ε ell k j ∧
    (sourceArithmeticCount C N b ε ell k j:ℝ) ≤ C^(2*j)*F*sourceArithmeticLength C N b ε ell k j
  copies : ∀j<b,N^(scaleA b j ε)*N^ε/2 ≤ (sourceArithmeticP C N b ε ell k j:ℝ) ∧
    (sourceArithmeticP C N b ε ell k j:ℝ) ≤ 2*N^(scaleA b j ε)*N^ε
  trials : ∀j<b,N^ε/(600*(C^(2*b)*F)) ≤ (sourceArithmeticTrials C N b ε ell k j:ℝ) ∧
    (sourceArithmeticTrials C N b ε ell k j:ℝ) ≤ 2*N^ε
  windows : ∀j<b,24 ≤ sourceBlockWindows N b ε j ∧ 24*2^s ≤ sourceBlockWindows N b ε j ∧
    2*sourceBlockWindows N b ε j ≤ sourceArithmeticP C N b ε ell k j ∧
    4*(sourceArithmeticTrials C N b ε ell k j+1) ≤ sourceBlockWindows N b ε j

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact exponent of the full binary forced skeleton, in the same bottom-up
 order as `binaryTreeBudget`. -/
def binaryTreeExponent (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | b+1 => e b+2*binaryTreeExponent e b

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceSkeletonPrefactor (s b : ℕ) (K : ℝ) : ℝ :=
  (2*((2^s:ℕ):ℝ)^3*K)*binaryTreeBudget (fun _=>4*((2^s:ℕ):ℝ)^6*K^2) b

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_ErrorRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# ErrorRates

Realization of block caps, sparse scales, sharp and smoothing budgets, tree tails, fit errors, and uniform polynomial/exponential bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceBadRoleFactor (b R : ℕ) : ℝ :=
  ∑r∈Finset.range R,4*((3^((b+1)*r):ℕ):ℝ)^2

def sourceForcedRoleFactor (b R : ℕ) : ℝ :=
  ∑r∈Finset.range R,4*((3^((b+1)*r):ℕ):ℝ)*(OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceSmoothingPrefactor (s : ℕ) (K : ℝ) : ℝ :=
  (2:ℝ)^(s*s+s)*(((s:ℝ)+1)*K)^(s+1)

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- A convenience for the manuscript's fixed-B polynomial losses. This
 predicate is only used to prove bounds on the literal finite constants. -/
def SourcePolyUpper (f : ℕ→ℝ) : Prop :=
  ∃ C : ℝ,0 ≤ C ∧ ∃ h : ℕ,∀D,f D ≤ C*((D:ℝ)+1)^h

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Literal finite-block factors are subpower uniformly over the joint
 deletion regime when their logarithms grow polynomially in the depth. -/
def SourceExpUpper (f : ℕ→ℝ→ℝ) : Prop :=
  ∃ C : ℝ,0 ≤ C ∧ ∃ h : ℕ,∀D q,q∈Set.Ioc 0 (1/2:ℝ) →
    f D q ≤ Real.exp (C*((D:ℝ)+1)^h*q^(-3:ℤ))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

def sourceMomentEnvelope (B D : ℕ) : ℝ :=
  ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)*((D:ℝ)+1)*2^(B*D)

def sourceCapEnvelope (B D : ℕ) (q : ℝ) : ℝ :=
  200*(sourceOverlapConstant q)^(2*B*(D+1)+2)*(initialOverlapLower q)⁻¹

def sourceWeightEnvelope (B D : ℕ) : ℝ := 144*(sourceMomentEnvelope B D)^2

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Propagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Propagation

Moment restriction, scale margins, sharp budget closure, clipping and error propagation, and dense/warmup overlap.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem evenMomentSq_mono_order (P : FiniteLaw α) (F : α→ℝ) {j k : ℕ}
    (hj : 1≤j) (hjk : j≤k) : P.evenMomentSq F j ≤ P.evenMomentSq F k := by
  have hjp : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hp : 1≤(k:ℝ)/j := (one_le_div hjp).mpr (by exact_mod_cast hjk)
  have he (a : α) : (|F a|^(2*j))^((k:ℝ)/j)=|F a|^(2*k) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _),←Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
  have H := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ P.mass
    (fun a=>|F a|^(2*j)) (fun a _=>P.nonneg a) P.total (fun _ _=>by positivity) hp
  simp_rw [he] at H
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg (P.expect_nonneg _ (fun _=>by positivity)) _) H
    (show 0≤1/(k:ℝ) by positivity)
  change (P.expect (fun a=>|F a|^(2*j))^((k:ℝ)/j))^(1/(k:ℝ)) ≤ _ at hr
  rw [←Real.rpow_mul (P.expect_nonneg _ (fun _=>by positivity))] at hr
  have he' : (k:ℝ)/j*(1/(k:ℝ))=1/(j:ℝ) := by field_simp
  rw [he'] at hr
  exact hr

end FiniteLaw

def OracleTracePair.restrict {q E V : ℝ} {x y : List Bool} {j k : ℕ}
    (C : OracleTracePair q x y k E V) (hj : 1≤j) (hjk : j≤k) :
    OracleTracePair q x y j E V := by
  let := C.finiteOutcome
  exact {C with moment := (C.first.evenMomentSq_mono_order C.score hj hjk).trans C.moment}

/-- Null-mass outcomes are assigned zero score. This proves, rather than
 assumes, the pointwise positivity needed by the finite simulation API. -/
def ConcreteLevelPair.oracle {q N Δ d ω F : ℝ} {hq : q∈Set.Icc 0 1} {i k : ℕ}
    (C : ConcreteLevelPair q hq N Δ d ω F i k) :
    OracleTracePair q C.left C.right k C.error (N^(-d)) := by
  let := C.finiteOutcome
  let Z := fun a=>if C.firstLaw.mass a=0 then 0 else C.score a
  have hden (a) : C.secondLaw.mass a=C.firstLaw.mass a*(1+Z a) := by
    dsimp [Z]
    split_ifs with h
    · simpa only [h,zero_mul] using C.density a
    · exact C.density a
  have hpos (a) : 0≤1+Z a := by
    by_cases h : C.firstLaw.mass a=0
    · simp [Z,h]
    · have hp : 0<C.firstLaw.mass a := lt_of_le_of_ne (C.firstLaw.nonneg a) (Ne.symm h)
      exact (mul_nonneg_iff_of_pos_left hp).mp (by rw [←hden]; exact C.secondLaw.nonneg a)
  have hc : C.firstLaw.expect Z=0 := by
    have hsum := congrArg (fun f : C.Outcome→ℝ=>∑a,f a) (funext hden)
    simp only [Finset.sum_add_distrib,mul_add,mul_one] at hsum
    rw [C.firstLaw.total,C.secondLaw.total] at hsum
    dsimp [FiniteLaw.expect]
    linarith only [hsum]
  have hm : C.firstLaw.evenMomentSq Z k=C.firstLaw.evenMomentSq C.score k := by
    unfold FiniteLaw.evenMomentSq FiniteLaw.expect
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp [Z]
    split_ifs with h
    · simp only [h,zero_mul]
    · rfl
  exact {
    Outcome := C.Outcome
    finiteOutcome := C.finiteOutcome
    first := C.firstLaw
    second := C.secondLaw
    decode := C.decode
    first_simulation := C.first_simulation
    second_simulation := C.second_simulation
    score := Z
    density := hden
    likelihood_nonneg := hpos
    centered := hc
    moment := hm.le.trans C.score_bound
  }

end TraceReconstruction


noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

structure SourceNumericMargins (B D : ℕ) (q N : ℝ) : Prop where
  geometry : 1200*sourceCapEnvelope B D q ≤ N^(sourceEpsilon B D)
  motif : 48*(2:ℝ)^(sourceCancellationOrder B D) ≤ N^(sourceEpsilon B D)
  sparse : 8*sourceWeightEnvelope B D*((2:ℝ)^(sourceCancellationOrder B D))^2 ≤ N^(sourceEpsilon B D)
  smoothing : sourceSmoothingPrefactor (sourceCancellationOrder B D) (sourceCapEnvelope B D q) ≤ N^(sourceEpsilon B D)
  bad : ∀b ≤ B,384*sourceBadRoleFactor b (sourceDegreeCutoff B) ≤ N^(sourceEpsilon B D)
  force : ∀b ≤ B,192*(sourceForcedRoleFactor b (sourceDegreeCutoff B)*(sourceWeightEnvelope B D)^(2^(b+1))*
    sourceSkeletonPrefactor (sourceCancellationOrder B D) b (sourceCapEnvelope B D q)) ≤ N^(sourceEpsilon B D)
  tail : 1536 ≤ N^(sourceEpsilon B D)
  error : 64*(sourceCapEnvelope B D q+1)*((D:ℝ)+1) ≤ N^(sourceEpsilon B D)
  overlap : 1099511627776*(sourceCapEnvelope B D q+1)*(sourceWeightEnvelope B D+1)^2*
    ((2:ℝ)^(sourceCancellationOrder B D))^(B+2) ≤ N^(sourceEpsilon B D)

end TraceReconstruction
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Induction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Induction

Concrete level invariants, metadata prefixes, score/error budgets, overlap, the induction step, and the complete construction.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal induction invariant, including the depth-dependent moment,
 actual complete-trace simulator, distinct words, length, and power overlap. -/
abbrev SourceLevelPair (B D : ℕ) (n q : ℝ) (hq : q∈Set.Icc 0 1) (i : ℕ) :=
  ConcreteLevelPair q hq (sourceTargetScale B D n i)
    (n^(-100*(totalScoreExponent B D+B+1))) (totalScoreExponent B i)
    (initialOverlapLower q) ((sourceOverlapConstant q)^(2*B*i+2)) i (sourceHalfMoment B D n i)

end TraceReconstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Restoration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restoration

Restoration to honest complete traces, degradation to the requested channel, and exact-length padding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A total common finite projection. The fallback is never used by a
 genuine trace of a length-at-most-n input. -/
def boundedTraceProjection (n : ℕ) (w : List Bool) : BoundedTrace n :=
  if h : w∈traceSpace n then ⟨w,h⟩ else ⟨[],mem_traceSpace_of_length_le [] (by simp)⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def extraDeletion (r q : ℝ) : ℝ := (q-r)/(1-r)

theorem extraDeletion_bounds {r q : ℝ} (hr : r<1) (hrq : r≤q) (hq : q≤1) :
    extraDeletion r q∈Set.Icc 0 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hrq) (sub_pos.mpr hr).le
  · apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
    linarith only [hq]

end TraceReconstruction


end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Testing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Testing

Multi-gadget family restoration and common-reference many-hypothesis statistics for every positive success level.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem hellingerSq_prod_same_right (P Q : FiniteLaw α) (R : FiniteLaw β) :
    (P.prod R).hellingerSq (Q.prod R)=P.hellingerSq Q := by
  unfold hellingerSq prod
  rw [Fintype.sum_prod_type]
  have he (a : α) (b : β) :
      (Real.sqrt (P.mass a*R.mass b)-Real.sqrt (Q.mass a*R.mass b))^2=
        (Real.sqrt (P.mass a)-Real.sqrt (Q.mass a))^2*R.mass b := by
    rw [Real.sqrt_mul (P.nonneg a),Real.sqrt_mul (Q.nonneg a),←sub_mul,mul_pow,
      Real.sq_sqrt (R.nonneg b)]
  simp_rw [he,←Finset.mul_sum,R.total,mul_one]

end FiniteLaw

def HellingerTracePair.suffix {q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (hq : q∈Set.Icc 0 1) (w : List Bool) :
    HellingerTracePair q (x++w) (y++w) E V := by
  let := C.finiteOutcome
  let R := listTraceLaw q hq w w.length le_rfl
  exact {
    Outcome := C.Outcome × BoundedTrace w.length
    finiteOutcome := inferInstance
    first := C.first.prod R
    second := C.second.prod R
    decode := fun z=>C.decode z.1++z.2.val
    first_simulation := by
      simpa only [add_zero] using C.first_simulation.append hq
        (listTraceLaw_simulates q hq w w.length le_rfl).approximate
    second_simulation := by
      simpa only [add_zero] using C.second_simulation.append hq
        (listTraceLaw_simulates q hq w w.length le_rfl).approximate
    bound := by rw [FiniteLaw.hellingerSq_prod_same_right]; exact C.bound }

end TraceReconstruction


end
end

end OAI
end


