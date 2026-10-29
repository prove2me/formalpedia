-- Prove2me | Definitions.Def_OAIQ089A000
-- name    : OAIQ089A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T02:51:03.553391+00:00
-- url     : https://prove2.me/theorems/87bc55a2-af58-43df-86ce-c1749cf2a7a2
-- title:
--   Definitions bundle OAIQ089A000 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 803 declarations of OpenAI's Lean: 372 definitions, 17 inductive types or structures, 11 instances and 403 theorems. The definitions and types are `OAI.CommonBasesFPRAS.AccuratePhase`, `OAI.CommonBasesFPRAS.ChainIndex`, `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.ClassObservable`, `OAI.CommonBasesFPRAS.DefectState`, `OAI.CommonBasesFPRAS.DrawTree.optionValue`, `OAI.CommonBasesFPRAS.EdgeRespects`, `OAI.CommonBasesFPRAS.ExchangeAdjacent`, `OAI.CommonBasesFPRAS.ExchangeChoice`, `OAI.CommonBasesFPRAS.FiniteChain`, `OAI.CommonBasesFPRAS.FiniteChain.Inside`, `OAI.CommonBasesFPRAS.FiniteChain.Outside`, `OAI.CommonBasesFPRAS.FiniteChain.apply`, `OAI.CommonBasesFPRAS.FiniteChain.cappedTrace`, `OAI.CommonBasesFPRAS.FiniteChain.centeredPoint`, `OAI.CommonBasesFPRAS.FiniteChain.duration`, `OAI.CommonBasesFPRAS.FiniteChain.energy`, `OAI.CommonBasesFPRAS.FiniteChain.exitProbability`, `OAI.CommonBasesFPRAS.FiniteChain.harmonicExtension`, `OAI.CommonBasesFPRAS.FiniteChain.hitKernel`, `OAI.CommonBasesFPRAS.FiniteChain.inner`, `OAI.CommonBasesFPRAS.FiniteChain.insideMass`, `OAI.CommonBasesFPRAS.FiniteChain.iterate`, `OAI.CommonBasesFPRAS.FiniteChain.kernel`, `OAI.CommonBasesFPRAS.FiniteChain.killedChain`, `OAI.CommonBasesFPRAS.FiniteChain.mean`, `OAI.CommonBasesFPRAS.FiniteChain.mergeFun`, `OAI.CommonBasesFPRAS.FiniteChain.ofMoves`, `OAI.CommonBasesFPRAS.FiniteChain.offExtension`, `OAI.CommonBasesFPRAS.FiniteChain.partialResolvent`, `OAI.CommonBasesFPRAS.FiniteChain.pathExpectation`, `OAI.CommonBasesFPRAS.FiniteChain.pathProbability`, `OAI.CommonBasesFPRAS.FiniteChain.pathSum`, `OAI.CommonBasesFPRAS.FiniteChain.pointDensity`, `OAI.CommonBasesFPRAS.FiniteChain.returnCost`, `OAI.CommonBasesFPRAS.FiniteChain.squareMoment`, `OAI.CommonBasesFPRAS.FiniteChain.traceApply`, `OAI.CommonBasesFPRAS.FiniteChain.traceChain`, `OAI.CommonBasesFPRAS.FiniteChain.traceMatrix`, `OAI.CommonBasesFPRAS.FiniteChain.variance` and 349 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Dense_AffineRegion`, `ContingencyTables_Dense_AffineRegionVolume`, `ContingencyTables_Machines_BinIntervalProgram`, `ContingencyTables_Machines_MatrixEncoding`, `ContingencyTables_Machines_ScaledWordProgram`, `ContingencyTables_Machines_SignedFloorProgram`, `ContingencyTables_Machines_SignedPairProgram`, `ContingencyTables_Rooted_LargePairEnumeration`, `ContingencyTables_Sampling_PhysicalLargeProfiles`, `ContingencyTables_Transport_AffinePenalty`, `ContingencyTables_Transport_BalancedBox`, `ContingencyTables_Transport_BalancedCellFibres`, `ContingencyTables_Transport_BalancedEnumeration`, `ContingencyTables_Transport_BalancedFamily`, `ContingencyTables_Transport_BalancedPhysicalPartition`, `ContingencyTables_Transport_BalancedSummation`, `ContingencyTables_Transport_FactorialSignatures`, `ContingencyTables_Transport_IntegerMarginal`, `ContingencyTables_Transport_QuadraticTransport`, `MatchingCount_Arithmetic_ArithmeticSize`, `MatchingCount_Arithmetic_BinaryAddition`, `MatchingCount_Arithmetic_BinaryCompare`, `MatchingCount_Arithmetic_BinaryNormalize`, `MatchingCount_Arithmetic_BinarySubtract`, `MatchingCount_Arithmetic_SubtractProc`, `MatchingCount_Arithmetic_TreeCompare`, `MatchingCount_Arithmetic_TreeNatDivision`, `MatchingCount_Arithmetic_TreeNumberOps`, `MatchingCount_Arithmetic_TreeSubtract`, `MatchingCount_Complexity_GuardMachineBase`, `MatchingCount_Complexity_TreePolynomial`, `MatchingCount_Machines_FiniteStore`, `MatchingCount_Machines_RegisterControl`, `MatchingCount_Machines_RegisterProc`, `MatchingCount_Machines_RegisterStructured`, `MatchingCount_Machines_RegisterTree`, `MatchingCount_Machines_TableLookup`, `MatchingCount_Machines_TreeChoice`, `MatchingCount_Machines_TreeFold`, `MatchingCount_Machines_TreeFunction`, `MatchingCount_Machines_TreeList`, `MatchingCount_Machines_TreeLookup`, `MatchingCount_Machines_TreeMachine`, `MatchingCount_Machines_TreePartialChoice`, `MatchingCount_Machines_TreeTransfer`, `MatchingCount_Machines_TreeTyped`, `MatchingCount_Tapes_Parse`, `MatchingCount_Tapes_StackEmbedding`, `MatchingCount_Tapes_StackLens`, `MatchingCount_Tapes_TreeBits`, `MatchingCount_Tapes_WordOps`, `MatroidCounting_CommonBases`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ089A003`, `OAIQ089A004` and `OAIQ089A005`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables

section
-- module Solutions.OAIQ089_CT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AffinePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The softened affine feasibility penalty

The dense sampler uses the maximum of zero and the negatives of its
normalized affine table entries, minus a fixed slack. This actual penalty
is continuous and convex. Its change bound is proved from the entry
coefficients, including the dependent row and column entries.
-/

namespace ContingencyTables.AffinePenalty

open scoped BigOperators

variable {I G : Type*} [Fintype I] [Fintype G]

def affineValue (offset : ℝ) (coeff : I → ℝ) (x : I → ℝ) : ℝ :=
  offset + ∑ j, coeff j * x j

theorem affineValue_combine (offset : ℝ) (coeff : I → ℝ) (x y : I → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    affineValue offset coeff (a • x + b • y) =
      a * affineValue offset coeff x + b * affineValue offset coeff y := by
  simp only [affineValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  simp_rw [mul_left_comm (coeff _) a, mul_left_comm (coeff _) b,
    ← Finset.mul_sum]
  nlinarith [congrArg (fun z => z * offset) hab]

theorem affineValue_change (offset : ℝ) (coeff : I → ℝ) (x y : I → ℝ)
    (c r : ℝ) (hc : 0 ≤ c) (hcoeff : ∀ j, |coeff j| ≤ c)
    (hxy : ∀ j, |x j - y j| ≤ r) :
    |affineValue offset coeff x - affineValue offset coeff y| ≤
      Fintype.card I * c * r := by
  have heq : affineValue offset coeff x - affineValue offset coeff y =
      ∑ j, coeff j * (x j - y j) := by
    simp [affineValue, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ j, |coeff j * (x j - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : I, c * r := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hcoeff j) (hxy j) (abs_nonneg _) hc
    _ = _ := by simp; ring

def component (offset : G → ℝ) (coeff : G → I → ℝ) (slack : ℝ) :
    Option G → (I → ℝ) → ℝ
  | none, _ => 0
  | some g, x => -affineValue (offset g) (coeff g) x - slack

noncomputable def penalty (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun g : Option G => component offset coeff slack g x)

theorem component_le_penalty (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x : I → ℝ) (g : Option G) :
    component offset coeff slack g x ≤ penalty offset coeff slack x := by
  unfold penalty
  exact Finset.le_sup' (fun g : Option G => component offset coeff slack g x) (Finset.mem_univ g)

theorem penalty_nonnegative (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x : I → ℝ) : 0 ≤ penalty offset coeff slack x :=
  component_le_penalty offset coeff slack x none

omit [Fintype G] in
theorem component_combine (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (g : Option G) (x y : I → ℝ) (a b : ℝ) (hab : a + b = 1) :
    component offset coeff slack g (a • x + b • y) =
      a * component offset coeff slack g x + b * component offset coeff slack g y := by
  cases g with
  | none => simp [component]
  | some g =>
    simp only [component, affineValue_combine _ _ _ _ _ _ hab]
    nlinarith [congrArg (fun z => z * slack) hab]

theorem penalty_convex (offset : G → ℝ) (coeff : G → I → ℝ) (slack : ℝ)
    (K : Set (I → ℝ)) (hK : Convex ℝ K) :
    ConvexOn ℝ K (penalty offset coeff slack) := by
  refine ⟨hK, ?_⟩
  intro x _ y _ a b ha hb hab
  apply Finset.sup'_le
  intro g _
  rw [component_combine offset coeff slack g x y a b hab]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (component_le_penalty offset coeff slack x g) ha)
    (mul_le_mul_of_nonneg_left (component_le_penalty offset coeff slack y g) hb)

omit [Fintype G] in
theorem component_change (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (g : Option G) (x y : I → ℝ) (c r : ℝ)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hcoeff : ∀ g j, |coeff g j| ≤ c)
    (hxy : ∀ j, |x j - y j| ≤ r) :
    |component offset coeff slack g x - component offset coeff slack g y| ≤
      Fintype.card I * c * r := by
  cases g with
  | none => simp only [component, sub_self, abs_zero]; positivity
  | some g =>
    have heq : component offset coeff slack (some g) x -
        component offset coeff slack (some g) y =
        -(affineValue (offset g) (coeff g) x - affineValue (offset g) (coeff g) y) := by
      simp only [component]
      ring
    rw [heq, abs_neg]
    exact affineValue_change _ _ _ _ c r hc (hcoeff g) hxy

theorem penalty_sub_le (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x y : I → ℝ) (c r : ℝ)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hcoeff : ∀ g j, |coeff g j| ≤ c)
    (hxy : ∀ j, |x j - y j| ≤ r) :
    penalty offset coeff slack x ≤ penalty offset coeff slack y + Fintype.card I * c * r := by
  apply Finset.sup'_le
  intro g _
  have h := (abs_le.mp (component_change offset coeff slack g x y c r hc hr hcoeff hxy)).2
  linarith [component_le_penalty offset coeff slack y g]

theorem penalty_change (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x y : I → ℝ) (c r : ℝ)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hcoeff : ∀ g j, |coeff g j| ≤ c)
    (hxy : ∀ j, |x j - y j| ≤ r) :
    |penalty offset coeff slack x - penalty offset coeff slack y| ≤ Fintype.card I * c * r := by
  apply abs_le.mpr
  constructor
  · have h := penalty_sub_le offset coeff slack y x c r hc hr hcoeff
      (fun j => by simpa [abs_sub_comm] using hxy j)
    linarith
  · linarith [penalty_sub_le offset coeff slack x y c r hc hr hcoeff hxy]

theorem penalty_continuous (offset : G → ℝ) (coeff : G → I → ℝ) (slack : ℝ) :
    Continuous (penalty offset coeff slack) := by
  apply Continuous.finset_sup'_apply
  intro g _
  cases g with
  | none => exact continuous_const
  | some g =>
    exact (continuous_const.add (continuous_finsetSum Finset.univ
      (fun j _ => continuous_const.mul (continuous_apply j)))).neg.sub continuous_const

end ContingencyTables.AffinePenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_AffineRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inner and relaxed affine feasibility regions

The strict feasible point yields the two homothetic inclusions used in
the dense rejection proof. Volume scaling follows from the Lebesgue/Haar
change-of-variables theorem.
-/

namespace ContingencyTables.AffinePenalty

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {I G : Type*} [Fintype I]

def region (offset : G → ℝ) (coeff : G → I → ℝ) (γ : ℝ) : Set (I → ℝ) :=
  {x | ∀ g, γ ≤ affineValue (offset g) (coeff g) x}

theorem inner_region_map (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (η α : ℝ) (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hc : center ∈ region offset coeff η) :
    (fun x => (1 - α) • x + α • center) '' region offset coeff 0 ⊆
      region offset coeff (α * η) := by
  rintro y ⟨x, hx, rfl⟩ g
  rw [affineValue_combine _ _ _ _ _ _ (by ring)]
  have ha := mul_nonneg (sub_nonneg.mpr hα₁) (hx g)
  have hb := mul_le_mul_of_nonneg_left (hc g) hα
  linarith

theorem relaxed_region_pullback (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (d γ : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hc : center ∈ region offset coeff (1 / (2 * d)))
    (x : I → ℝ) (hx : x ∈ region offset coeff (-γ)) :
    (1 / (1 + 2 * d * γ)) • x + (2 * d * γ / (1 + 2 * d * γ)) • center ∈
      region offset coeff 0 := by
  have hden : 0 < 1 + 2 * d * γ := by positivity
  have hab : 1 / (1 + 2 * d * γ) + 2 * d * γ / (1 + 2 * d * γ) = 1 := by
    field_simp [ne_of_gt hden]
  intro g
  rw [affineValue_combine _ _ _ _ _ _ hab]
  calc
    0 = (1 / (1 + 2 * d * γ)) * (-γ) +
        (2 * d * γ / (1 + 2 * d * γ)) * (1 / (2 * d)) := by
      field_simp [ne_of_gt hd, ne_of_gt hden]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx g) (by positivity))
      (mul_le_mul_of_nonneg_left (hc g) (by positivity))

theorem relaxed_region_subset_expansion (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (d γ : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hc : center ∈ region offset coeff (1 / (2 * d))) :
    region offset coeff (-γ) ⊆
      (fun z => center + (1 + 2 * d * γ) • (z - center)) '' region offset coeff 0 := by
  intro x hx
  refine ⟨_, relaxed_region_pullback offset coeff center d γ hd hγ hc x hx, ?_⟩
  have hden : 1 + 2 * d * γ ≠ 0 := ne_of_gt (by positivity : 0 < 1 + 2 * d * γ)
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hden]
  ring

theorem volume_image_translate (c : I → ℝ) (S : Set (I → ℝ)) :
    volume ((fun x => c + x) '' S) = volume S := by
  have heq : (fun x => c + x) '' S = (fun x => -c + x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-c + x, hx, by simp⟩
  rw [heq, measure_preimage_add]

theorem volume_homothety (center : I → ℝ) (a : ℝ) (ha : 0 ≤ a) (S : Set (I → ℝ)) :
    volume ((fun z => center + a • (z - center)) '' S) =
      ENNReal.ofReal (a ^ Fintype.card I) * volume S := by
  have heq : (fun z => center + a • (z - center)) '' S =
      (fun z => center + z) '' (a • ((fun z => -center + z) '' S)) := by
    simp only [← Set.image_smul, Set.image_image]
    congr 1
    funext z
    rw [sub_eq_neg_add]
  rw [heq, volume_image_translate, Measure.addHaar_smul_of_nonneg volume ha,
    volume_image_translate, Module.finrank_fintype_fun_eq_card]

theorem relaxed_region_volume (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (d γ : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hc : center ∈ region offset coeff (1 / (2 * d))) :
    volume (region offset coeff (-γ)) ≤
      ENNReal.ofReal ((1 + 2 * d * γ) ^ Fintype.card I) * volume (region offset coeff 0) := by
  calc
    _ ≤ volume ((fun z => center + (1 + 2 * d * γ) • (z - center)) '' region offset coeff 0) :=
      measure_mono (relaxed_region_subset_expansion offset coeff center d γ hd hγ hc)
    _ = _ := volume_homothety center _ (by positivity) _

end

end ContingencyTables.AffinePenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_AffineRegionVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume comparisons used by dense rejection -/

namespace ContingencyTables.AffinePenalty

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {I G : Type*} [Fintype I]

theorem inner_region_volume (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (η α : ℝ) (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hc : center ∈ region offset coeff η) :
    ENNReal.ofReal ((1 - α) ^ Fintype.card I) * volume (region offset coeff 0) ≤
      volume (region offset coeff (α * η)) := by
  rw [← volume_homothety center (1 - α) (sub_nonneg.mpr hα₁)]
  have heq : (fun x : I → ℝ => center + (1 - α) • (x - center)) =
      (fun x => (1 - α) • x + α • center) := by
    ext x i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact measure_mono (inner_region_map offset coeff center η α hα hα₁ hc)

theorem relaxed_region_volume_exp (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (d γ : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hdim : (Fintype.card I : ℝ) ≤ d)
    (hc : center ∈ region offset coeff (1 / (2 * d))) :
    volume (region offset coeff (-γ)) ≤
      ENNReal.ofReal (Real.exp (2 * d ^ 2 * γ)) * volume (region offset coeff 0) := by
  have hpoly : (1 + 2 * d * γ) ^ Fintype.card I ≤ Real.exp (2 * d ^ 2 * γ) := by
    calc
      _ ≤ (Real.exp (2 * d * γ)) ^ Fintype.card I :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * d * γ)]) _
      _ = Real.exp ((Fintype.card I : ℝ) * (2 * d * γ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have h := mul_le_mul_of_nonneg_right hdim (show 0 ≤ 2 * d * γ by positivity)
        nlinarith)
  exact (relaxed_region_volume offset coeff center d γ hd hγ hc).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hpoly) _)

end

end ContingencyTables.AffinePenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_QuadraticTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quadratic ingredients for contingency-table transport

The quadratic-form version of the one-positive-direction property and
the scalar telescoping step give the balanced-pair transport argument in
both contingency-table sampling and counting papers.
-/

namespace ContingencyTables

open Finset
open LinearMap (BilinForm)

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A symmetric form is nonpositive on the form-orthogonal complement
of every vector of positive square. This is the quadratic formulation
of positive inertia at most one. -/
def OnePositiveDirection (B : BilinForm ℝ V) : Prop :=
  ∀ u, 0 < B u u → ∀ v, B u v = 0 → B v v ≤ 0

/-- Nonpositivity on the kernel of one linear functional suffices for
the quadratic signature needed in the manuscripts. -/
theorem onePositiveDirection_of_kernel (B : BilinForm ℝ V)
    (hsymm : ∀ x y, B x y = B y x) (ℓ : V →ₗ[ℝ] ℝ)
    (hker : ∀ v, ℓ v = 0 → B v v ≤ 0) : OnePositiveDirection B := by
  intro u hu v huv
  have hlu : ℓ u ≠ 0 := by
    intro h
    exact (not_le_of_gt hu) (hker u h)
  let a : ℝ := ℓ v / ℓ u
  have hw : ℓ (v - a • u) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, a]
    field_simp
    ring
  have hq := hker (v - a • u) hw
  have hvu : B v u = 0 := by rw [hsymm, huv]
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    huv, hvu, mul_zero, sub_zero, zero_sub] at hq
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  nlinarith

/-- The projection inequality (200-01, equation positive-projection;
200-02, equation signature-projection). -/
theorem positive_projection (B : BilinForm ℝ V)
    (hsymm : ∀ x y, B x y = B y x) (hsig : OnePositiveDirection B)
    (u v : V) (hu : 0 < B u u) :
    B v v ≤ (B u v) ^ 2 / B u u := by
  let a : ℝ := B u v / B u u
  have hzero : B u (v - a • u) = 0 := by
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, a]
    field_simp
    ring
  have hw := hsig u hu (v - a • u) hzero
  have hvu : B v u = B u v := hsymm v u
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hvu] at hw
  apply (le_div_iff₀ hu).2
  dsimp [a] at hw
  field_simp at hw
  nlinarith

end Forms

/-- Exact scalar expansion behind the balanced-pair telescoping
inequality. The two mixed entries are expressed as discrete differences
of the cumulative coefficients. -/
theorem pair_expansion (v um u up gm g gp : ℝ) :
    v + 2 * g * ((u * g - um * gm) - (up * gp - u * g)) +
        (um - 2 * u + up) * g ^ 2 -
        (um * (g - gm) ^ 2 + up * (g - gp) ^ 2) =
      v + 2 * u * g ^ 2 - um * gm ^ 2 - up * gp ^ 2 := by
  ring

/-- Once the local projection estimate is available, the exact
expansion gives equation pair-one in 200-01 and integer-telescoping
in 200-02. The hypothesis is a local quadratic estimate, not a claim
that the whole manuscript has been proved. -/
theorem pair_telescoping_step (v um u up gm g gp : ℝ)
    (hprojection :
      v + 2 * g * ((u * g - um * gm) - (up * gp - u * g)) +
          (um - 2 * u + up) * g ^ 2 ≤
        um * (g - gm) ^ 2 + up * (g - gp) ^ 2) :
    2 * u * g ^ 2 - um * gm ^ 2 - up * gp ^ 2 ≤ -v := by
  have h := sub_nonpos.mpr hprojection
  rw [pair_expansion] at h
  linarith

section PairProjection

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The local inequality follows from the signature even when either or
both of the fresh diagonal entries vanish. This includes the capacity-two
boundary case in both manuscripts. -/
theorem pair_step_of_signature (B : BilinForm ℝ V)
    (hsymm : ∀ x y, B x y = B y x) (hsig : OnePositiveDirection B)
    (h ea eb : V) (um u up gm g gp : ℝ)
    (haa : B ea ea = um) (hbb : B eb eb = up) (hab : B ea eb = u)
    (hha : B h ea = u * g - um * gm)
    (hhb : B h eb = up * gp - u * g)
    (hum : 0 ≤ um) (hup : 0 ≤ up)
    (hpositive : 0 < um ∨ 0 < up ∨ (um = 0 ∧ up = 0 ∧ 0 < u)) :
    2 * u * g ^ 2 - um * gm ^ 2 - up * gp ^ 2 ≤ -B h h := by
  let v := h + g • ea - g • eb
  have hba : B eb ea = u := by rw [hsymm, hab]
  have hv_a : B v ea = um * (g - gm) := by
    dsimp [v]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, haa, hba, hha]
    ring
  have hv_b : B v eb = up * (gp - g) := by
    dsimp [v]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hab, hbb, hhb]
    ring
  have hvv : B v v = B h h +
      2 * g * ((u * g - um * gm) - (up * gp - u * g)) +
      (um - 2 * u + up) * g ^ 2 := by
    have hah : B ea h = u * g - um * gm := by rw [hsymm, hha]
    have hbh : B eb h = up * gp - u * g := by rw [hsymm, hhb]
    dsimp [v]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      haa, hbb, hab, hba, hha, hhb, hah, hbh]
    ring
  have hbound : B v v ≤ um * (g - gm) ^ 2 + up * (g - gp) ^ 2 := by
    rcases hpositive with ha | hb | ⟨ha, hb, hu⟩
    · have hh := positive_projection B hsymm hsig ea v (by rwa [haa])
      rw [hsymm ea v, hv_a, haa] at hh
      have heq : (um * (g - gm)) ^ 2 / um = um * (g - gm) ^ 2 := by
        field_simp
      rw [heq] at hh
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg hup (sq_nonneg _)))
    · have hh := positive_projection B hsymm hsig eb v (by rwa [hbb])
      rw [hsymm eb v, hv_b, hbb] at hh
      have heq : (up * (gp - g)) ^ 2 / up = up * (g - gp) ^ 2 := by
        field_simp
        ring
      rw [heq] at hh
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg hum (sq_nonneg _)))
    · have hsum : B (ea + eb) (ea + eb) = 2 * u := by
        simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          haa, hbb, hab, hba, ha, hb]
        ring
      have horth : B (ea + eb) v = 0 := by
        rw [hsymm, LinearMap.BilinForm.add_right, hv_a, hv_b, ha, hb]
        ring
      have hh := hsig (ea + eb) (by rw [hsum]; linarith) v horth
      simpa only [ha, hb, zero_mul, zero_add] using hh
  rw [hvv] at hbound
  exact pair_telescoping_step _ _ _ _ _ _ _ hbound

end PairProjection

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Balanced-pair summation of two-removal forms

This is the finite unweighted closure step in paper 200-01,
Lemma `lem:pair-summation` (`D'=B`), and paper 200-02,
Lemma `lem:integer-signature`. The hypotheses describe the actual old/fresh
blocks and their adjacent cross entries. Cumulative coefficients are
constructed from those cross entries; no transport or closure conclusion is
assumed. In particular the zero-diagonal capacity-two case is included.
-/

namespace ContingencyTables

open scoped BigOperators
open LinearMap (BilinForm)

/-- The lower endpoint convention used by the balanced-pair matrices. -/
theorem sum_pred_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (2 * a j - a (j - 1) - a (j + 1))) =
      a n - a (n + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_sub_cancel]
    ring

section Cumulative

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The partial cross-entry sum in equation pair-cumulative. -/
def pairCumulative (S : ℕ → V →ₗ[ℝ] ℝ) (v : V) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range j, S (l + 1) v

lemma pairCumulative_zero (S : ℕ → V →ₗ[ℝ] ℝ) (v : V) : pairCumulative S v 0 = 0 := by
  simp [pairCumulative]

lemma pairCumulative_succ (S : ℕ → V →ₗ[ℝ] ℝ) (v : V) (j : ℕ) :
    pairCumulative S v (j + 1) = pairCumulative S v j + S (j + 1) v := by
  exact Finset.sum_range_succ _ _

/-- The cumulative coefficients, with division by zero harmless at the
endpoints because the corresponding cumulative mass is proved zero. -/
noncomputable def pairCoefficient (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ) (v : V) (j : ℕ) : ℝ :=
  pairCumulative S v j / u j

lemma pairCoefficient_represents (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ)
    (n : ℕ) (v : V)
    (huint : ∀ j, 0 < j → j < n → 0 < u j)
    (hbalance : pairCumulative S v n = 0) (hend : S (n + 1) v = 0)
    {j : ℕ} (hj : j ≤ n + 1) :
    u j * pairCoefficient S u v j = pairCumulative S v j := by
  by_cases hj0 : j = 0
  · subst j
    simp [pairCoefficient, pairCumulative_zero]
  by_cases hjn : j = n
  · subst j
    simp [pairCoefficient, hbalance]
  by_cases hjn1 : j = n + 1
  · subst j
    simp [pairCoefficient, pairCumulative_succ, hbalance, hend]
  have hu : u j ≠ 0 := ne_of_gt (huint j (by omega) (by omega))
  dsimp [pairCoefficient]
  field_simp

end Cumulative

section Closure

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Summing the old blocks of the two-removal matrices preserves the
one-positive-direction signature. The cumulative coefficients and common kernel are explicit. -/
theorem balancedPair_sum_onePositive
    (n : ℕ) (hn : 2 ≤ n)
    (B : ℕ → BilinForm ℝ W) (old : V →ₗ[ℝ] W) (ea eb : W)
    (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ)
    (hsymm : ∀ j ≤ n, ∀ x y, B j x y = B j y x)
    (hsig : ∀ j ≤ n, OnePositiveDirection (B j))
    (hu0 : u 0 = 0) (hun : u n = 0) (hun1 : u (n + 1) = 0)
    (huint : ∀ j, 0 < j → j < n → 0 < u j)
    (hS0 : S 0 = 0) (hSn1 : S (n + 1) = 0)
    (haa : ∀ j ≤ n, B j ea ea = u (j - 1))
    (hbb : ∀ j ≤ n, B j eb eb = u (j + 1))
    (hab : ∀ j ≤ n, B j ea eb = u j)
    (hha : ∀ j ≤ n, ∀ v, B j (old v) ea = S j v)
    (hhb : ∀ j ≤ n, ∀ v, B j (old v) eb = S (j + 1) v) :
    OnePositiveDirection (∑ j ∈ Finset.range (n + 1), (B j).compl₁₂ old old) := by
  let A : BilinForm ℝ V := ∑ j ∈ Finset.range (n + 1), (B j).compl₁₂ old old
  let L : V →ₗ[ℝ] ℝ := ∑ j ∈ Finset.range n, S (j + 1)
  have hA (v w : V) : A v w = ∑ j ∈ Finset.range (n + 1), B j (old v) (old w) := by
    simp only [A, LinearMap.sum_apply, LinearMap.compl₁₂_apply]
  have hu_nonneg {j : ℕ} (hj : j ≤ n + 1) : 0 ≤ u j := by
    by_cases hj0 : j = 0
    · simp [hj0, hu0]
    by_cases hjn : j = n
    · simp [hjn, hun]
    by_cases hjn1 : j = n + 1
    · simp [hjn1, hun1]
    exact le_of_lt (huint j (by omega) (by omega))
  change OnePositiveDirection A
  refine onePositiveDirection_of_kernel A ?_ L ?_
  · intro v w
    rw [hA, hA]
    apply Finset.sum_congr rfl
    intro j hj
    exact hsymm j (by simpa using Finset.mem_range.mp hj) _ _
  · intro v hv
    have hbalance : pairCumulative S v n = 0 := by
      simpa only [L, LinearMap.sum_apply, pairCumulative] using hv
    have hend : S (n + 1) v = 0 := by rw [hSn1]; rfl
    let g := pairCoefficient S u v
    have hrepr {j : ℕ} (hj : j ≤ n + 1) : u j * g j = pairCumulative S v j :=
      pairCoefficient_represents S u n v huint hbalance hend hj
    have hlocal {j : ℕ} (hj : j ≤ n) :
        2 * (u j * g j ^ 2) - (u (j - 1) * g (j - 1) ^ 2) -
          (u (j + 1) * g (j + 1) ^ 2) ≤ -B j (old v) (old v) := by
      have hleft : B j (old v) ea = u j * g j - u (j - 1) * g (j - 1) := by
        rw [hha j hj, hrepr (by omega), hrepr (by omega)]
        by_cases hj0 : j = 0
        · subst j
          simp [hS0, pairCumulative_zero]
        · have hc := pairCumulative_succ S v (j - 1)
          have heq : j - 1 + 1 = j := by omega
          rw [heq] at hc
          linarith
      have hright : B j (old v) eb = u (j + 1) * g (j + 1) - u j * g j := by
        rw [hhb j hj, hrepr (by omega), hrepr (by omega), pairCumulative_succ]
        ring
      have hpositive : 0 < u (j - 1) ∨ 0 < u (j + 1) ∨
          (u (j - 1) = 0 ∧ u (j + 1) = 0 ∧ 0 < u j) := by
        by_cases hm : 0 < u (j - 1)
        · exact Or.inl hm
        by_cases hp : 0 < u (j + 1)
        · exact Or.inr (Or.inl hp)
        have hj0 : 0 < j := by
          by_contra h
          have hjz : j = 0 := by omega
          subst j
          exact hp (huint 1 (by omega) (by omega))
        have hjn : j < n := by
          by_contra h
          have hjeq : j = n := by omega
          subst j
          exact hm (huint (n - 1) (by omega) (by omega))
        exact Or.inr (Or.inr ⟨le_antisymm (le_of_not_gt hm) (hu_nonneg (by omega)),
          le_antisymm (le_of_not_gt hp) (hu_nonneg (by omega)), huint j hj0 hjn⟩)
      simpa only [mul_assoc] using pair_step_of_signature (B j) (hsymm j hj) (hsig j hj) (old v) ea eb
        (u (j - 1)) (u j) (u (j + 1)) (g (j - 1)) (g j) (g (j + 1))
        (haa j hj) (hbb j hj) (hab j hj) hleft hright
        (hu_nonneg (by omega)) (hu_nonneg (by omega)) hpositive
    have hsum := Finset.sum_le_sum (s := Finset.range (n + 1))
      (fun j hj => hlocal (by simpa using Finset.mem_range.mp hj))
    rw [sum_pred_second_differences] at hsum
    simp only [hun, hun1, zero_mul, sub_self, Finset.sum_neg_distrib] at hsum
    rw [hA]
    linarith

end Closure

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

abbrev IndependenceOracle (n : ℕ) := Bool → (Fin n → Bool) → Bool

inductive Instruction (k s : ℕ) where
  | push (register : Fin (k + 8)) (bit : Bool) (next : Fin (s + 1))
  | pop (register : Fin (k + 8)) (empty zero one : Fin (s + 1))
  | coin (zero one : Fin (s + 1))
  | query (which : Bool) (register : Fin (k + 8)) (no yes : Fin (s + 1))
  | halt

def Program (k s : ℕ) := Fin (s + 1) → Instruction k s

def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * binaryValue l

structure MachineConfig (k s : ℕ) where
  registers : Fin (k + 8) → List Bool
  control : Fin (s + 1)
  output : Option ℚ := none
  oracleCalls : ℕ := 0
  bitOperations : ℕ := 0

def machineStep {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (randomBit : Bool) (c : MachineConfig k s) : MachineConfig k s :=
  if c.output.isSome then c else
  match P c.control with
  | .push i b next =>
    { c with
      registers := Function.update c.registers i (b :: c.registers i)
      control := next
      bitOperations := c.bitOperations + 1 }
  | .pop i empty zero one =>
    match c.registers i with
    | [] => { c with
      control := empty
      bitOperations := c.bitOperations + 1 }
    | b :: l =>
      { c with
      registers := Function.update c.registers i l
      control := if b then one else zero
      bitOperations := c.bitOperations + 1 }
  | .coin zero one =>
    { c with
      control := if randomBit then one else zero
      bitOperations := c.bitOperations + 1 }
  | .query which i no yes =>
    if (c.registers i).length = n then
      { c with
      control := if O which (fun j => (c.registers i)[j.val]?.getD false)
          then yes else no
      oracleCalls := c.oracleCalls + 1
      bitOperations := c.bitOperations + (c.registers i).length + n + 1 }
    else
      { c with
      output := some 0
      bitOperations := c.bitOperations + (c.registers i).length + n + 1 }
  | .halt =>
    { c with
      output := some ((binaryValue (c.registers ⟨6, by omega⟩) : ℚ) /
        (binaryValue (c.registers ⟨7, by omega⟩) : ℚ))
      bitOperations := c.bitOperations + (c.registers ⟨6, by omega⟩).length +
        (c.registers ⟨7, by omega⟩).length + 1 }

def execution {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) : ℕ → MachineConfig k s
  | 0 => c
  | t + 1 => machineStep P O (bits t) (execution P O c bits t)

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def OnePositive (B : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ e, 0 < B e e → ∀ v, B v e = 0 → B v v ≤ 0

section PositiveMatrix
variable {ι : Type*} [Fintype ι] [sectionInstance7 : DecidableEq ι]

theorem matrix_bilin_symm (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = A j i) :
    A.toBilin'.IsSymm := by
  constructor
  intro x y
  simp only [Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i]
  ring

def weightedSumLinear (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, a i * v i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

def diagonalScale (A : Matrix ι ι ℝ) (s : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => s i * A i j * s j

lemma onePositive_quadratic_bound {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : OnePositive B) (hS : B.IsSymm)
    (e v : V) (he : 0 < B e e) : B v v ≤ (B v e)^2 / B e e := by
  have hz : B ((B e e) • v - (B v e) • e) e = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hn := hB e he ((B e e) • v - (B v e) • e) hz
  have hev : B e v = B v e := hS.eq e v
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hev] at hn
  apply (le_div_iff₀ he).mpr
  have hf : B e e * (B v v * B e e - (B v e)^2) ≤ 0 := by nlinarith [hn]
  have hle : B v v * B e e - (B v e)^2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hf he
  linarith

def cubicContraction (C : ι → Matrix ι ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun j k => ∑ i, x i*C i j k

end PositiveMatrix

section MatroidFaces
open scoped Matroid BigOperators Classical
variable {ι : Type*} [sectionInstance10 : Fintype ι] [sectionInstance11 : DecidableEq ι]

noncomputable def faceHessian (f : Set ι → ℝ) (A : Set ι) :
    Matrix {i // i ∉ A} {i // i ∉ A} ℝ :=
  fun i j => if i = j then 0 else f (A ∪ {i.val,j.val})

end MatroidFaces

section DerivativeClosure
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance12 : Fintype ι] [sectionInstance13 : DecidableEq ι]
noncomputable def coeffDeriv (a : ι → ℝ) (f : Set ι → ℝ) (A : Set ι) : ℝ :=
  ∑ i, if i ∈ A then 0 else a i * f (insert i A)

noncomputable def coeffDerivs : List (ι → ℝ) → (Set ι → ℝ) → Set ι → ℝ
  | [], f => f
  | a :: as, f => coeffDeriv a (coeffDerivs as f)

def FullPositive (f : Set ι → ℝ) (k : ℕ) : Prop :=
  (∀ A, A.ncard + k ≤ Fintype.card ι → 0 < f A) ∧
  (∀ A, Fintype.card ι < A.ncard + k → f A = 0)

noncomputable def padMatrix (p : ι → Prop) [DecidablePred p]
    (B : Matrix {i // p i} {i // p i} ℝ) : Matrix ι ι ℝ :=
  fun i j => if hi : p i then if hj : p j then B ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

lemma matrix_reindex_bilin {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (B : Matrix κ κ ℝ) (v w : ι → ℝ) :
    (B.submatrix e e).toBilin' v w =
      B.toBilin' (fun j => v (e.symm j)) (fun j => w (e.symm j)) := by
  simp only [Matrix.toBilin'_apply, Matrix.submatrix_apply]
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp

lemma onePositive_reindex {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (B : Matrix κ κ ℝ) (hB : OnePositive B.toBilin') :
    OnePositive (B.submatrix e e).toBilin' := by
  intro x hx v hv
  rw [matrix_reindex_bilin] at hx hv ⊢
  exact hB _ hx _ hv

noncomputable def faceEraseEquiv (A : Set ι) (i : {i // i ∉ A}) :
    {j : {j // j ∉ A} // j ≠ i} ≃ {j // j ∉ insert i.val A} where
  toFun j := ⟨j.val.val, by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨fun h => j.property (Subtype.ext h), j.val.property⟩⟩
  invFun j := ⟨⟨j.val, fun h => j.property (Set.mem_insert_of_mem _ h)⟩,
    fun h => j.property (Or.inl (congrArg Subtype.val h))⟩
  left_inv j := rfl
  right_inv j := rfl

noncomputable def faceCubic (f : Set ι → ℝ) (A : Set ι) :
    {i // i ∉ A} → Matrix {i // i ∉ A} {i // i ∉ A} ℝ :=
  fun i j k => if i = j ∨ i = k ∨ j = k then 0 else f (insert i.val (A ∪ {j.val,k.val}))

lemma matrix_bilin_tendsto {κ : Type*} {l : Filter κ}
    (F : κ → Matrix ι ι ℝ) (B : Matrix ι ι ℝ)
    (hF : ∀ i j, Filter.Tendsto (fun t => F t i j) l (nhds (B i j)))
    (v w : ι → ℝ) :
    Filter.Tendsto (fun t => (F t).toBilin' v w) l (nhds (B.toBilin' v w)) := by
  simp only [Matrix.toBilin'_apply]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_const_nhds.mul (hF i j)).mul tendsto_const_nhds)

lemma onePositive_of_tendsto {κ : Type*} {l : Filter κ} [l.NeBot]
    (F : κ → Matrix ι ι ℝ) (B : Matrix ι ι ℝ)
    (hF : ∀ i j, Filter.Tendsto (fun t => F t i j) l (nhds (B i j)))
    (hS : ∀ t i j, F t i j = F t j i)
    (hP : ∀ᶠ t in l, OnePositive (F t).toBilin') : OnePositive B.toBilin' := by
  intro e he v hv
  have hee := matrix_bilin_tendsto F B hF e e
  have hvv := matrix_bilin_tendsto F B hF v v
  have hve := matrix_bilin_tendsto F B hF v e
  have hp : ∀ᶠ t in l, (F t).toBilin' v v * (F t).toBilin' e e ≤
      ((F t).toBilin' v e)^2 := by
    filter_upwards [hP, hee.eventually (eventually_gt_nhds he)] with t ht hte
    exact (le_div_iff₀ hte).mp
      (onePositive_quadratic_bound _ ht (matrix_bilin_symm _ (hS t)) e v hte)
  have hh := le_of_tendsto_of_tendsto (hvv.mul hee) (hve.pow 2) hp
  rw [hv, zero_pow (by decide : 2 ≠ 0)] at hh
  exact nonpos_of_mul_nonpos_right (by simpa [mul_comm] using hh) he

lemma onePositive_matrix_substitution {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (hB : OnePositive B.toBilin') (L : Matrix ι κ ℝ) :
    OnePositive (L.transpose * B * L).toBilin' := by
  rw [← Matrix.toBilin'_comp]
  intro e he v hv
  exact hB (L.toLin' e) he (L.toLin' v) hv

noncomputable def slotDirection (E : Finset ι) (i : ι) : ℝ := if i ∈ E then 1 else 0

lemma coeffDeriv_slot (E : Finset ι) (f : Set ι → ℝ) (A : Set ι) :
    coeffDeriv (slotDirection E) f A =
      ∑ i ∈ E, if i ∈ A then 0 else f (insert i A) := by
  classical
  unfold coeffDeriv slotDirection
  rw [← Finset.sum_subset (Finset.subset_univ E)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  · intro i _ hi
    simp [hi]

lemma coeffDeriv_pair (a b : ι) (hab : a ≠ b) (f : Set ι → ℝ) (A : Set ι)
    (ha : a ∉ A) (hb : b ∉ A) :
    coeffDeriv (slotDirection {a,b}) f A = f (insert a A) + f (insert b A) := by
  rw [coeffDeriv_slot]
  simp [hab, ha, hb]

lemma onePositive_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (hB : OnePositive B.toBilin') (e : κ → ι) :
    OnePositive (B.submatrix e e).toBilin' := by
  classical
  let L : Matrix ι κ ℝ := fun i j => if i = e j then 1 else 0
  have heq : L.transpose * B * L = B.submatrix e e := by
    ext i j
    change (∑ k, (∑ l, (if l = e i then (1 : ℝ) else 0) * B l k) *
      (if k = e j then (1 : ℝ) else 0)) = B (e i) (e j)
    simp
  rw [← heq]
  exact onePositive_matrix_substitution B hB L

end DerivativeClosure

section MatrixSplit

open scoped BigOperators
variable {ι : Type*} [Fintype ι] [sectionInstance15 : DecidableEq ι]

def splitMatrix (V : Matrix ι ι ℝ) (sa sb : ι → ℝ) (u : ℝ) :
    Matrix (ι ⊕ Bool) (ι ⊕ Bool) ℝ
  | .inl i, .inl j => V i j
  | .inl i, .inr false => sb i
  | .inl i, .inr true => sa i
  | .inr false, .inl i => sb i
  | .inr true, .inl i => sa i
  | .inr a, .inr b => if a = b then 0 else u

def oldVector (h : ι → ℝ) : (ι ⊕ Bool) → ℝ
  | .inl i => h i
  | .inr _ => 0

def splitPositive : (ι ⊕ Bool) → ℝ
  | .inl _ => 0
  | .inr _ => 1

def splitDifference : (ι ⊕ Bool) → ℝ
  | .inl _ => 0
  | .inr false => 1
  | .inr true => -1

def futureChild (V : Matrix ι ι ℝ) (c : ι → ℝ) : Matrix (Option ι) (Option ι) ℝ
  | some i, some j => V i j
  | some i, none => c i
  | none, some j => c j
  | none, none => 0

def extendVector (h : ι → ℝ) (a : ℝ) : Option ι → ℝ
  | some i => h i
  | none => a

end MatrixSplit

section RecursiveTransport
open scoped BigOperators Classical Matrix
variable {Γ : Type*} [sectionInstance16 : Fintype Γ] [sectionInstance17 : DecidableEq Γ]

noncomputable def pairDirection (p : Γ × Γ) : Γ → ℝ := slotDirection {p.1,p.2}

noncomputable def slotTotal (ps : List (Γ × Γ)) (f : Set Γ → ℝ) : Set Γ → ℝ :=
  coeffDerivs (ps.map pairDirection) f

lemma slotTotal_nil (f : Set Γ → ℝ) (A : Set Γ) : slotTotal [] f A = f A := rfl

lemma slotTotal_cons (p : Γ × Γ) (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (hp : p.1 ≠ p.2) (ha : p.1 ∉ A) (hb : p.2 ∉ A) :
    slotTotal (p::ps) f A = slotTotal ps f (insert p.1 A) +
      slotTotal ps f (insert p.2 A) := by
  exact coeffDeriv_pair p.1 p.2 hp (slotTotal ps f) A ha hb

def SlotsFresh : List (Γ × Γ) → Set Γ → Prop
  | [], _ => True
  | p::ps, B => p.1 ≠ p.2 ∧ p.1 ∉ B ∧ p.2 ∉ B ∧
      SlotsFresh ps (insert p.1 (insert p.2 B))

omit sectionInstance16 sectionInstance17 in
lemma SlotsFresh.mono [Fintype Γ] [DecidableEq Γ] {ps : List (Γ × Γ)} {A B : Set Γ}
    (h : SlotsFresh ps B) (hAB : A ⊆ B) : SlotsFresh ps A := by
  induction ps generalizing A B with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨hp,ha,hb,ht⟩ := h
    exact ⟨hp, fun hx => ha (hAB hx), fun hx => hb (hAB hx),
      ih ht (Set.insert_subset_insert (Set.insert_subset_insert hAB))⟩

lemma slotTotal_pos (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (hf : ∀ A, 0 < f A) (A : Set Γ) (hps : SlotsFresh ps A) :
    0 < slotTotal ps f A := by
  induction ps generalizing A with
  | nil => exact hf A
  | cons p ps ih =>
    obtain ⟨hp,ha,hb,ht⟩ := hps
    rw [slotTotal_cons p ps f A hp ha hb]
    apply add_pos
    · apply ih _ (ht.mono _)
      intro x hx
      rcases hx with rfl | hx
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)
    · apply ih _ (ht.mono _)
      intro x hx
      exact Set.mem_insert_of_mem _ hx

def appendPoint {ι : Type*} (e : ι → Γ) (a : Γ) : Option ι → Γ
  | none => a
  | some i => e i

noncomputable def pairMatrix {ι : Type*} [DecidableEq ι]
    (f : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) : Matrix ι ι ℝ :=
  fun i j => if i = j then 0 else f (insert (e i) (insert (e j) A))

def HasSlotSignature (f : Set Γ → ℝ) : Prop :=
  ∀ (ps : List (Γ × Γ)) (A : Set Γ),
    OnePositive (faceHessian (slotTotal ps f) A).toBilin'

section Clique
variable {ι : Type*} [Fintype ι] [sectionInstance19 : DecidableEq ι]

noncomputable def cliqueEnergy (s W H : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, min (W i*s i) (W j*s j) * (H i-H j)^2) / 2

end Clique

variable {ι : Type*} [sectionInstance20 : Fintype ι] [sectionInstance21 : DecidableEq ι]

def splitEmbedding (e : ι → Γ) (a b : Γ) : (ι ⊕ Bool) → Γ
  | .inl i => e i
  | .inr false => a
  | .inr true => b

noncomputable def transportDemand (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) : ℝ :=
  ∑ i, h i * slotTotal ps (fun S => f S*H S) (insert (e i) A)

noncomputable def transportPotential (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (W : Γ → ℝ) : ℝ :=
  ∑ i, slotTotal ps f (insert (e i) A) * (h i)^2 / W (e i)

def slotPunctures : List (Γ × Γ) → List ((Γ × Γ) × List (Γ × Γ))
  | [] => []
  | p::ps => (p,ps) :: (slotPunctures ps).map (fun x => (x.1,p::x.2))

noncomputable def transportCorrection (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (W : Γ → ℝ) : ℝ :=
  ((slotPunctures ps).map (fun x =>
    (pairMatrix (slotTotal x.2 f) A e).toBilin' h h / W x.1.1)).sum

noncomputable def transportEnergy {ι : Type*} [Fintype ι] (ps : List (Γ × Γ))
    (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ) : ℝ :=
  match ps with
  | [] => cliqueEnergy (fun i => f (insert (e i) A)) (fun i => W (e i))
      (fun i => H (insert (e i) A))
  | p::ps => transportEnergy ps f H (insert p.2 A) (appendPoint e p.1) W +
      transportEnergy ps f H (insert p.1 A) (appendPoint e p.2) W
termination_by ps.length

end RecursiveTransport

section TransportRoot
open scoped BigOperators Classical Matrix
variable {Γ ι : Type*} [sectionInstance22 : Fintype Γ] [sectionInstance23 : DecidableEq Γ]
  [Fintype ι] [sectionInstance25 : DecidableEq ι]

def rootEmbedding (p d : Γ) : Bool → Γ := fun b => if b then d else p

noncomputable def rootDemand (sp sd : ℝ) : Bool → ℝ :=
  fun b => if b then -(1/sd) else 1/sp

noncomputable def rootCoefficient (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) : ℝ :=
  let sp := slotTotal ps f (insert p A)
  let sd := slotTotal ps f (insert d A)
  1/(sp*W p) + 1/(sd*W d) + 2/(sp*sd)*
    ((slotPunctures ps).map (fun x => slotTotal x.2 f (insert p (insert d A))/W x.1.1)).sum

end TransportRoot

section TransportGraph
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance26 : Fintype Γ] [sectionInstance27 : DecidableEq Γ]

def ExchangeAdjacent (S T : Set Γ) : Prop :=
  ∃ (A : Set Γ) (a b : Γ), a ≠ b ∧ a ∉ A ∧ b ∉ A ∧
    S = insert a A ∧ T = insert b A

noncomputable def slotVertices {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ) : Finset (Set Γ) :=
  match ps with
  | [] => Finset.univ.image (fun i => insert (e i) A)
  | p::ps => slotVertices ps (insert p.2 A) (appendPoint e p.1) ∪
      slotVertices ps (insert p.1 A) (appendPoint e p.2)
termination_by ps.length

noncomputable def transportEdges {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ) : Finset (Set Γ × Set Γ) :=
  match ps with
  | [] => (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2)).image
      (fun ij => (insert (e ij.1) A, insert (e ij.2) A))
  | p::ps => transportEdges ps (insert p.2 A) (appendPoint e p.1) ∪
      transportEdges ps (insert p.1 A) (appendPoint e p.2)
termination_by ps.length

noncomputable def missingMultiplier {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (e : ι → Γ) (W : Γ → ℝ) (S : Set Γ) : ℝ :=
  (∑ i, if e i ∈ S then W (e i) else 0) +
    (ps.map (fun p => if p.1 ∈ S ∧ p.2 ∈ S then W p.1 else 0)).sum

noncomputable def slotEdgeEnergy {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (e : ι → Γ) (W : Γ → ℝ)
    (f H : Set Γ → ℝ) (ST : Set Γ × Set Γ) : ℝ :=
  min (missingMultiplier ps e W ST.1 * f ST.1)
      (missingMultiplier ps e W ST.2 * f ST.2) * (H ST.1-H ST.2)^2

noncomputable def slotGraphEdges {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ) : Finset (Set Γ × Set Γ) :=
  ((slotVertices ps A e).product (slotVertices ps A e)).filter
    (fun ST => ExchangeAdjacent ST.1 ST.2)

noncomputable def slotGraphEnergy {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ) : ℝ :=
  (∑ ST ∈ slotGraphEdges ps A e, slotEdgeEnergy ps e W f H ST)/2

end TransportGraph

section CoefficientInequalities
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance28 : Fintype ι] [sectionInstance29 : DecidableEq ι]

omit sectionInstance28 sectionInstance29 in
lemma SlotsFresh.swap [Fintype ι] [DecidableEq ι] {ps : List (ι × ι)} {p r : ι × ι} {A : Set ι}
    (h : SlotsFresh (p::r::ps) A) : SlotsFresh (r::p::ps) A := by
  obtain ⟨hp,hpa,hpb,hr,hra,hrb,hps⟩ := h
  refine ⟨hr,?_,?_,hp,?_,?_,?_⟩
  · exact fun hx => hra (Or.inr (Or.inr hx))
  · exact fun hx => hrb (Or.inr (Or.inr hx))
  · simp only [Set.mem_insert_iff, not_or] at hra hrb ⊢
    exact ⟨Ne.symm hra.1,Ne.symm hrb.1,hpa⟩
  · simp only [Set.mem_insert_iff, not_or] at hra hrb ⊢
    exact ⟨Ne.symm hra.2.1,Ne.symm hrb.2.1,hpb⟩
  · convert hps using 1 ; ext x ; simp ; tauto

end CoefficientInequalities

section IndexedSlotCoefficients
open scoped BigOperators Classical
variable {ι : Type*} [sectionInstance32 : Fintype ι] [DecidableEq ι]

lemma SlotsFresh.perm {ps qs : List (ι × ι)} (hperm : ps.Perm qs) (A : Set ι) :
    SlotsFresh ps A ↔ SlotsFresh qs A := by
  induction hperm generalizing A with
  | nil => rfl
  | cons p h ih =>
    change (_ ∧ _ ∧ _ ∧ SlotsFresh _ _) ↔ (_ ∧ _ ∧ _ ∧ SlotsFresh _ _)
    rw [ih]
  | swap p r ps => exact ⟨SlotsFresh.swap,SlotsFresh.swap⟩
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ A).trans (ih₂ A)

noncomputable def slotDefect (ps : List (ι × ι)) (f : Set ι → ℝ)
    (A : Set ι) (p r : ι × ι) : ℝ :=
  slotTotal ((ps.erase p).erase r) f (insert r.1 (insert r.2 A))

omit sectionInstance32 in
lemma slots_perm_two [Fintype ι] {ps : List (ι × ι)} {p r : ι × ι}
    (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    ps.Perm (p::r::(ps.erase p).erase r) := by
  exact (List.perm_cons_erase hp).trans
    ((List.perm_cons_erase ((List.mem_erase_of_ne hpr.symm).mpr hr)).cons p)

lemma slotDefect_pos (ps : List (ι × ι)) (f : Set ι → ℝ)
    (hf : ∀ S, 0 < f S) (A : Set ι) (hps : SlotsFresh ps A)
    (p r : ι × ι) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    0 < slotDefect ps f A p r := by
  have hh := (SlotsFresh.perm (slots_perm_two hp hr hpr) A).mp hps
  apply slotTotal_pos _ f hf _ (hh.2.2.2.2.2.2.mono _)
  intro x hx
  simp only [Set.mem_insert_iff] at hx ⊢
  tauto

end IndexedSlotCoefficients

section VarianceTree
open scoped BigOperators Classical
variable {ι : Type*} [sectionInstance34 : Fintype ι] [sectionInstance35 : DecidableEq ι]

noncomputable def slotVariance (ps : List (ι × ι)) (f H : Set ι → ℝ) (A : Set ι) : ℝ :=
  slotTotal ps (fun S => f S*(H S)^2) A -
    (slotTotal ps (fun S => f S*H S) A)^2 / slotTotal ps f A

end VarianceTree

section StateGeometry
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance36 : Fintype Γ] [sectionInstance37 : DecidableEq Γ]

def PairSingle (p : Γ × Γ) (S : Set Γ) : Prop :=
  (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.2 ∈ S ∧ p.1 ∉ S)
def PairFull (p : Γ × Γ) (S : Set Γ) : Prop := p.1 ∈ S ∧ p.2 ∈ S
def PairEmpty (p : Γ × Γ) (S : Set Γ) : Prop := p.1 ∉ S ∧ p.2 ∉ S

omit sectionInstance36 sectionInstance37 in
lemma PairSingle.not_full [Fintype Γ] [DecidableEq Γ] {p : Γ × Γ} {S : Set Γ} (h : PairSingle p S) : ¬ PairFull p S := by
  unfold PairSingle PairFull at *
  tauto
omit sectionInstance36 sectionInstance37 in
lemma PairSingle.not_empty [Fintype Γ] [DecidableEq Γ] {p : Γ × Γ} {S : Set Γ} (h : PairSingle p S) : ¬ PairEmpty p S := by
  unfold PairSingle PairEmpty at *
  tauto
omit sectionInstance36 sectionInstance37 in
lemma PairFull.not_empty [Fintype Γ] [DecidableEq Γ] {p : Γ × Γ} {S : Set Γ} (h : PairFull p S) : ¬ PairEmpty p S := by
  unfold PairFull PairEmpty at *
  tauto

def PlainState (gs : List (Γ × Γ)) (S : Set Γ) : Prop := ∀ p ∈ gs, PairSingle p S
def DefectState (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) : Prop :=
  p ∈ gs ∧ r ∈ gs ∧ p ≠ r ∧ PairEmpty p S ∧ PairFull r S ∧
    ∀ t ∈ gs, t ≠ p → t ≠ r → PairSingle t S

lemma DefectState.not_plain {gs : List (Γ × Γ)} {p r : Γ × Γ} {S : Set Γ}
    (h : DefectState gs p r S) : ¬ PlainState gs S := by
  intro hs
  exact (hs p h.1).not_empty h.2.2.2.1

lemma DefectState.unique {gs : List (Γ × Γ)} {p r p' r' : Γ × Γ} {S : Set Γ}
    (h : DefectState gs p r S) (h' : DefectState gs p' r' S) : p = p' ∧ r = r' := by
  obtain ⟨hp,hr,hpr,hep,hfr,hs⟩ := h
  obtain ⟨hp',hr',hpr',hep',hfr',hs'⟩ := h'
  have hpp : p = p' := by
    by_contra hne
    by_cases hpr' : p = r'
    · subst r'; exact hfr'.not_empty hep
    · exact (hs' p hp hne hpr').not_empty hep
  subst p'
  refine ⟨rfl,?_⟩
  by_contra hne
  exact (hs' r hr hpr.symm hne).not_full hfr

omit sectionInstance36 sectionInstance37 in
lemma SlotsFresh.elements_fresh [Fintype Γ] [DecidableEq Γ] {ps : List (Γ × Γ)} {A : Set Γ}
    (h : SlotsFresh ps A) (p : Γ × Γ) (hp : p ∈ ps) : p.1 ∉ A ∧ p.2 ∉ A := by
  induction ps generalizing A with
  | nil => simp at hp
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨h.2.1,h.2.2.1⟩
    · have hh := ih h.2.2.2 hp
      exact ⟨fun hx => hh.1 (Or.inr (Or.inr hx)), fun hx => hh.2 (Or.inr (Or.inr hx))⟩

lemma SlotsFresh.pair_ne_of_mem {ps : List (Γ × Γ)} {A : Set Γ} {p : Γ × Γ}
    (h : SlotsFresh (p::ps) A) {r : Γ × Γ} (hr : r ∈ ps) : p ≠ r := by
  intro heq
  subst r
  exact (h.2.2.2.elements_fresh p hr).1 (Set.mem_insert _ _)

end StateGeometry

section RestrictedEnergy
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance38 : Fintype Γ] [sectionInstance39 : DecidableEq Γ]

def Respects (A B S : Set Γ) : Prop := A ⊆ S ∧ Disjoint B S

def EdgeRespects (A B : Set Γ) (ST : Set Γ × Set Γ) : Prop :=
  Respects A B ST.1 ∧ Respects A B ST.2

noncomputable def restrictedEnergy (E : Finset (Set Γ × Set Γ))
    (c : (Set Γ × Set Γ) → ℝ) (H : Set Γ → ℝ) (A B : Set Γ) : ℝ :=
  (∑ ST ∈ E, if EdgeRespects A B ST then c ST*(H ST.1-H ST.2)^2 else 0)/2

end RestrictedEnergy

section ChainIdentification
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance40 : Fintype Γ] [sectionInstance41 : DecidableEq Γ]

def FixedOutside (gs ps : List (Γ × Γ)) (A B : Set Γ) : Prop :=
  ∀ r ∈ gs, r ∉ ps → (r.1 ∈ A ∧ r.2 ∈ B) ∨ (r.2 ∈ A ∧ r.1 ∈ B)

noncomputable def chainMultiplier (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (S : Set Γ) : ℝ :=
  if h : ∃ p r, DefectState gs p r S then w h.choose h.choose_spec.choose else 1

lemma chainMultiplier_plain (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (S : Set Γ) (h : PlainState gs S) : chainMultiplier gs w S = 1 := by
  unfold chainMultiplier
  rw [dite_eq_right]
  rintro ⟨p,r,hpr⟩
  exact hpr.not_plain h

lemma chainMultiplier_defect (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (S : Set Γ) {p r : Γ × Γ} (h : DefectState gs p r S) :
    chainMultiplier gs w S = w p r := by
  have he : ∃ p r, DefectState gs p r S := ⟨p,r,h⟩
  unfold chainMultiplier
  rw [dite_eq_left he]
  have hh := he.choose_spec.choose_spec.unique h
  exact congrArg₂ w hh.1 hh.2

omit sectionInstance41 in
lemma chainMultiplier_pos [DecidableEq Γ] (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (S : Set Γ) : 0 < chainMultiplier gs w S := by
  unfold chainMultiplier
  split_ifs <;> first | exact hw _ _ | norm_num

def ChainState (gs : List (Γ × Γ)) (S : Set Γ) : Prop :=
  PlainState gs S ∨ ∃ p r, DefectState gs p r S

noncomputable def chainEdges (gs : List (Γ × Γ)) : Finset (Set Γ × Set Γ) :=
  Finset.univ.filter (fun ST => ChainState gs ST.1 ∧ ChainState gs ST.2 ∧
    ExchangeAdjacent ST.1 ST.2)

noncomputable def chainConductance (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (ST : Set Γ × Set Γ) : ℝ :=
  min (chainMultiplier gs w ST.1*f ST.1) (chainMultiplier gs w ST.2*f ST.2)

lemma SlotsFresh.pair_contains_unique {ps : List (Γ × Γ)} {A : Set Γ}
    (h : SlotsFresh ps A) {p r : Γ × Γ} (hp : p ∈ ps) (hr : r ∈ ps)
    {x : Γ} (hxp : x = p.1 ∨ x = p.2) (hxr : x = r.1 ∨ x = r.2) : p = r := by
  by_contra hne
  have hh := (SlotsFresh.perm (slots_perm_two hp hr hne) A).mp h
  have hr₁ := hh.2.2.2.2.1
  have hr₂ := hh.2.2.2.2.2.1
  rcases hxp with rfl | rfl <;> rcases hxr with heq | heq
  · exact hr₁ (Or.inl heq.symm)
  · exact hr₂ (Or.inl heq.symm)
  · exact hr₁ (Or.inr (Or.inl heq.symm))
  · exact hr₂ (Or.inr (Or.inl heq.symm))

noncomputable def pairMultiplier (ps : List (Γ × Γ)) (w : (Γ × Γ) → ℝ) (x : Γ) : ℝ :=
  if h : ∃ p ∈ ps, x = p.1 ∨ x = p.2 then w h.choose else 1

end ChainIdentification

section TransversalVariance
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance42 : Fintype Γ] [sectionInstance43 : DecidableEq Γ]

def VarianceNode (gs ps : List (Γ × Γ)) (A B : Set Γ) : Prop :=
  Disjoint A B ∧ SlotsFresh ps (A ∪ B) ∧ (∀ p ∈ ps, p ∈ gs) ∧ FixedOutside gs ps A B

end TransversalVariance

section ChoiceEnumeration
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance44 : Fintype Γ] [sectionInstance45 : DecidableEq Γ]

def pairSupport (ps : List (Γ × Γ)) : Set Γ :=
  {x | ∃ p ∈ ps, x = p.1 ∨ x = p.2}

omit sectionInstance44 sectionInstance45 in
@[simp] lemma pairSupport_nil [Fintype Γ] [DecidableEq Γ] : pairSupport ([] : List (Γ × Γ)) = ∅ := by ext; simp [pairSupport]
omit sectionInstance44 sectionInstance45 in
lemma pairSupport_cons [Fintype Γ] [DecidableEq Γ] (p : Γ × Γ) (ps : List (Γ × Γ)) :
    pairSupport (p::ps) = insert p.1 (insert p.2 (pairSupport ps)) := by
  ext x
  simp only [pairSupport,Set.mem_ofPred_eq,List.mem_cons,Set.mem_insert_iff]
  aesop

noncomputable def choiceVertices (ps : List (Γ × Γ)) (A : Set Γ) : Finset (Set Γ) :=
  match ps with
  | [] => {A}
  | p::ps => choiceVertices ps (insert p.1 A) ∪ choiceVertices ps (insert p.2 A)

omit sectionInstance44 sectionInstance45 in
lemma choiceVertices_fixed [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) (A S : Set Γ)
    (hS : S ∈ choiceVertices ps A) : A ⊆ S := by
  induction ps generalizing A with
  | nil =>
    rw [choiceVertices,Finset.mem_singleton] at hS
    exact hS ▸ Set.Subset.rfl
  | cons p ps ih =>
    rw [choiceVertices] at hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact (Set.subset_insert _ _).trans (ih _ hS)
    · exact (Set.subset_insert _ _).trans (ih _ hS)

omit sectionInstance44 sectionInstance45 in
lemma choiceVertices_excluded [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) (A B S : Set Γ)
    (hAB : Disjoint A B) (hps : ∀ p ∈ ps, p.1 ∉ B ∧ p.2 ∉ B)
    (hS : S ∈ choiceVertices ps A) : Disjoint B S := by
  induction ps generalizing A with
  | nil =>
    rw [choiceVertices,Finset.mem_singleton] at hS
    exact hS ▸ hAB.symm
  | cons p ps ih =>
    obtain ⟨ha,hb⟩ := hps p List.mem_cons_self
    have hrest := fun r hr => hps r (List.mem_cons_of_mem _ hr)
    rw [choiceVertices] at hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact ih _ (Set.disjoint_insert_left.mpr ⟨ha,hAB⟩) hrest hS
    · exact ih _ (Set.disjoint_insert_left.mpr ⟨hb,hAB⟩) hrest hS

lemma choiceVertices_disjoint (ps : List (Γ × Γ)) (A : Set Γ) (p : Γ × Γ)
    (hps : SlotsFresh (p::ps) A) :
    Disjoint (choiceVertices ps (insert p.1 A)) (choiceVertices ps (insert p.2 A)) := by
  apply Finset.disjoint_left.mpr
  intro S h₁ h₂
  have hp₁ : p.1 ∈ S := choiceVertices_fixed ps (insert p.1 A) S h₁ (Set.mem_insert _ _)
  have hp₂ : Disjoint {p.1} S := choiceVertices_excluded ps (insert p.2 A) {p.1} S
    (by simp only [Set.disjoint_singleton_right,Set.mem_insert_iff,not_or]; exact ⟨hps.1,hps.2.1⟩)
    (by
      intro r hr
      have hh := hps.2.2.2.elements_fresh r hr
      exact ⟨fun heq => hh.1 (Or.inl heq),fun heq => hh.2 (Or.inl heq)⟩) h₂
  exact Set.disjoint_left.mp hp₂ rfl hp₁

lemma slotTotal_eq_choice_sum (ps : List (Γ × Γ)) (A : Set Γ) (f : Set Γ → ℝ)
    (hps : SlotsFresh ps A) : slotTotal ps f A = ∑ S ∈ choiceVertices ps A, f S := by
  induction ps generalizing A with
  | nil => simp [choiceVertices,slotTotal_nil]
  | cons p ps ih =>
    rw [slotTotal_cons p ps f A hps.1 hps.2.1 hps.2.2.1,choiceVertices,
      Finset.sum_union (choiceVertices_disjoint ps A p hps)]
    congr 1
    · exact ih _ (hps.2.2.2.mono (by intro x hx; simp only [Set.mem_insert_iff] at hx ⊢; tauto))
    · exact ih _ (hps.2.2.2.mono (Set.subset_insert _ _))

lemma mem_choiceVertices_iff (ps : List (Γ × Γ)) (A S : Set Γ) (hps : SlotsFresh ps A) :
    S ∈ choiceVertices ps A ↔
      A ⊆ S ∧ S ⊆ A ∪ pairSupport ps ∧ PlainState ps S := by
  induction ps generalizing A with
  | nil => simp [choiceVertices,pairSupport_nil,PlainState,Set.Subset.antisymm_iff,and_comm]
  | cons p ps ih =>
    have hf₁ : SlotsFresh ps (insert p.1 A) := hps.2.2.2.mono (by
      intro x hx; simp only [Set.mem_insert_iff] at hx ⊢; tauto)
    have hf₂ : SlotsFresh ps (insert p.2 A) := hps.2.2.2.mono (Set.subset_insert _ _)
    rw [choiceVertices,Finset.mem_union,ih _ hf₁,ih _ hf₂]
    have hnot₁ : p.1 ∉ pairSupport ps := by
      rintro ⟨r,hr,h⟩
      have hh := hps.2.2.2.elements_fresh r hr
      rcases h with he | he
      · exact hh.1 (Or.inl he.symm)
      · exact hh.2 (Or.inl he.symm)
    have hnot₂ : p.2 ∉ pairSupport ps := by
      rintro ⟨r,hr,h⟩
      have hh := hps.2.2.2.elements_fresh r hr
      rcases h with he | he
      · exact hh.1 (Or.inr (Or.inl he.symm))
      · exact hh.2 (Or.inr (Or.inl he.symm))
    constructor
    · rintro (⟨hfix,hsupp,hsing⟩ | ⟨hfix,hsupp,hsing⟩)
      · refine ⟨(Set.subset_insert _ _).trans hfix,?_,?_⟩
        · intro x hx
          have hh := hsupp hx
          rw [pairSupport_cons]
          simp only [Set.mem_union,Set.mem_insert_iff] at hh ⊢
          tauto
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · left
            refine ⟨hfix (Set.mem_insert _ _),?_⟩
            intro hbad
            have hh := hsupp hbad
            rcases hh with hh | hh
            · rcases hh with hh | hh
              · exact hps.1 hh.symm
              · exact hps.2.2.1 hh
            · exact hnot₂ hh
          · exact hsing r hr
      · refine ⟨(Set.subset_insert _ _).trans hfix,?_,?_⟩
        · intro x hx
          have hh := hsupp hx
          rw [pairSupport_cons]
          simp only [Set.mem_union,Set.mem_insert_iff] at hh ⊢
          tauto
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · right
            refine ⟨hfix (Set.mem_insert _ _),?_⟩
            intro hbad
            have hh := hsupp hbad
            rcases hh with hh | hh
            · rcases hh with hh | hh
              · exact hps.1 hh
              · exact hps.2.1 hh
            · exact hnot₁ hh
          · exact hsing r hr
    · rintro ⟨hfix,hsupp,hsing⟩
      have hp := hsing p List.mem_cons_self
      have hrest : PlainState ps S := fun r hr => hsing r (List.mem_cons_of_mem _ hr)
      rcases hp with hp | hp
      · left
        refine ⟨Set.insert_subset hp.1 hfix,?_,hrest⟩
        intro x hx
        have hh := hsupp hx
        rw [pairSupport_cons] at hh
        simp only [Set.mem_union,Set.mem_insert_iff] at hh ⊢
        rcases hh with hh | rfl | rfl | hh
        · exact Or.inl (Or.inr hh)
        · exact Or.inl (Or.inl rfl)
        · exact False.elim (hp.2 hx)
        · exact Or.inr hh
      · right
        refine ⟨Set.insert_subset hp.1 hfix,?_,hrest⟩
        intro x hx
        have hh := hsupp hx
        rw [pairSupport_cons] at hh
        simp only [Set.mem_union,Set.mem_insert_iff] at hh ⊢
        rcases hh with hh | rfl | rfl | hh
        · exact Or.inl (Or.inr hh)
        · exact False.elim (hp.2 hx)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr hh

lemma choiceVertices_plain (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) :
    choiceVertices gs ∅ = Finset.univ.filter (PlainState gs) := by
  ext S
  rw [mem_choiceVertices_iff gs ∅ S hgs]
  simp [hcover]

lemma slotTotal_eq_plain_sum (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ) :
    slotTotal gs f ∅ = ∑ S ∈ Finset.univ.filter (PlainState gs), f S := by
  rw [slotTotal_eq_choice_sum gs ∅ f hgs,choiceVertices_plain gs hgs hcover]

end ChoiceEnumeration

section DefectEnumeration
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance46 : Fintype Γ] [sectionInstance47 : DecidableEq Γ]

omit sectionInstance46 sectionInstance47 in
lemma pairSupport_perm [Fintype Γ] [DecidableEq Γ] {ps qs : List (Γ × Γ)} (hp : ps.Perm qs) : pairSupport ps = pairSupport qs := by
  ext x
  simp only [pairSupport,Set.mem_ofPred_eq,hp.mem_iff]

lemma SlotsFresh.support_disjoint {ps : List (Γ × Γ)} {A : Set Γ} (h : SlotsFresh ps A) :
    Disjoint (pairSupport ps) A := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p,hp,hx⟩ hxA
  rcases hx with rfl | rfl
  · exact (h.elements_fresh p hp).1 hxA
  · exact (h.elements_fresh p hp).2 hxA

lemma choiceVertices_defect (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (p r : Γ × Γ)
    (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r) :
    choiceVertices ((gs.erase p).erase r) {r.1,r.2} =
      Finset.univ.filter (DefectState gs p r) := by
  let ps := (gs.erase p).erase r
  have hperm : gs.Perm (p::r::ps) := slots_perm_two hp hr hpr
  have hslots := (SlotsFresh.perm hperm ∅).mp hgs
  have htail : SlotsFresh ps {r.1,r.2} := hslots.2.2.2.2.2.2.mono (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false] at hx ⊢
    tauto)
  have hno : p.1 ∉ pairSupport (r::ps) ∧ p.2 ∉ pairSupport (r::ps) := by
    exact ⟨fun hx => Set.disjoint_left.mp hslots.2.2.2.support_disjoint hx (Or.inl rfl),
      fun hx => Set.disjoint_left.mp hslots.2.2.2.support_disjoint hx (Or.inr (Or.inl rfl))⟩
  have htailSupport : ({r.1,r.2} : Set Γ) ∪ pairSupport ps = pairSupport (r::ps) := by
    rw [pairSupport_cons]
    ext x
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hcover' : pairSupport (p::r::ps) = Set.univ := (pairSupport_perm hperm).symm.trans hcover
  ext S
  rw [mem_choiceVertices_iff _ _ _ htail,Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hfix,hsupp,hsing⟩
    refine ⟨hp,hr,hpr,⟨?_,?_⟩,⟨hfix (Or.inl rfl),hfix (Or.inr rfl)⟩,?_⟩
    · intro hx; exact hno.1 (htailSupport ▸ hsupp hx)
    · intro hx; exact hno.2 (htailSupport ▸ hsupp hx)
    · intro t ht htp htr
      have ht' : t ∈ p::r::ps := hperm.mem_iff.mp ht
      simp only [List.mem_cons] at ht'
      exact hsing t (ht'.resolve_left htp |>.resolve_left htr)
  · intro hdef
    refine ⟨?_,?_,?_⟩
    · intro x hx
      rcases hx with rfl | hx
      · exact hdef.2.2.2.2.1.1
      · exact hx ▸ hdef.2.2.2.2.1.2
    · intro x hx
      have hh : x ∈ pairSupport (p::r::ps) := hcover' ▸ Set.mem_univ x
      rw [pairSupport_cons] at hh
      rcases hh with rfl | rfl | hh
      · exact False.elim (hdef.2.2.2.1.1 hx)
      · exact False.elim (hdef.2.2.2.1.2 hx)
      · exact htailSupport ▸ hh
    · intro t ht
      exact hdef.2.2.2.2.2 t (hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))
        (hslots.pair_ne_of_mem (List.mem_cons_of_mem _ ht)).symm
        (hslots.2.2.2.pair_ne_of_mem ht).symm

lemma slotDefect_eq_defect_sum (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ) (p r : Γ × Γ)
    (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r) :
    slotDefect gs f ∅ p r = ∑ S ∈ Finset.univ.filter (DefectState gs p r), f S := by
  have hslots := (SlotsFresh.perm (slots_perm_two hp hr hpr) ∅).mp hgs
  have htail : SlotsFresh ((gs.erase p).erase r) {r.1,r.2} := hslots.2.2.2.2.2.2.mono (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false] at hx ⊢
    tauto)
  unfold slotDefect
  simp only [insert_empty_eq]
  rw [slotTotal_eq_choice_sum _ _ f htail,choiceVertices_defect gs hgs hcover p r hp hr hpr]

end DefectEnumeration

section DefectTransport
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance48 : Fintype Γ] [sectionInstance49 : DecidableEq Γ]

def SamePair (p q : Γ × Γ) : Prop := q = p ∨ q = p.swap

end DefectTransport

section DefectMeans
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance50 : Fintype Γ] [sectionInstance51 : DecidableEq Γ]

def orientPair (p : Γ × Γ) (b : Bool) : Γ × Γ := if b then p.swap else p

end DefectMeans

section Observable
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance52 : Fintype Γ] [DecidableEq Γ]

noncomputable def chainStates (gs : List (Γ × Γ)) : Finset (Set Γ) :=
  Finset.univ.filter (ChainState gs)
noncomputable def defectTypes (gs : List (Γ × Γ)) : Finset ((Γ × Γ) × (Γ × Γ)) :=
  gs.toFinset.offDiag
noncomputable def chainWeight (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (S : Set Γ) : ℝ :=
  chainMultiplier gs w S * f S
noncomputable def chainTotal (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) : ℝ :=
  ∑ S ∈ chainStates gs, chainWeight gs w f S
noncomputable def plainMean (gs : List (Γ × Γ)) (f H : Set Γ → ℝ) : ℝ :=
  slotTotal gs (fun S => f S*H S) ∅/slotTotal gs f ∅
noncomputable def defectMean (gs : List (Γ × Γ)) (f H : Set Γ → ℝ) (p r : Γ × Γ) : ℝ :=
  slotDefect gs (fun S => f S*H S) ∅ p r/slotDefect gs f ∅ p r
noncomputable def observableProjection (gs : List (Γ × Γ)) (f H : Set Γ → ℝ) (S : Set Γ) : ℝ :=
  if h : ∃ p r, DefectState gs p r S then defectMean gs f H h.choose h.choose_spec.choose else H S

omit sectionInstance52 in
lemma mem_defectTypes [Fintype Γ] (gs : List (Γ × Γ)) (pr : (Γ × Γ) × (Γ × Γ)) :
    pr ∈ defectTypes gs ↔ pr.1 ∈ gs ∧ pr.2 ∈ gs ∧ pr.1 ≠ pr.2 := by
  simp [defectTypes,Finset.mem_offDiag]

lemma chain_sum_decomposition (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (g : Set Γ → ℝ) :
    (∑ S ∈ chainStates gs, chainMultiplier gs w S*g S) =
      (∑ S ∈ Finset.univ.filter (PlainState gs),g S) +
      ∑ pr ∈ defectTypes gs, w pr.1 pr.2 *
        ∑ S ∈ Finset.univ.filter (DefectState gs pr.1 pr.2),g S := by
  simp only [chainStates,Finset.sum_filter,Finset.mul_sum]
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hp : PlainState gs S
  · have hd : ∀ p r, ¬ DefectState gs p r S := fun p r hh => hh.not_plain hp
    simp [hp,ChainState,chainMultiplier_plain gs w S hp,hd]
  · by_cases hd : ∃ p r, DefectState gs p r S
    · obtain ⟨p,r,hpr⟩ := hd
      have hmem : (p,r) ∈ defectTypes gs := (mem_defectTypes gs _).mpr ⟨hpr.1,hpr.2.1,hpr.2.2.1⟩
      have hu : ∀ pr ∈ defectTypes gs, pr ≠ (p,r) → ¬ DefectState gs pr.1 pr.2 S := by
        intro pr _ hn hh
        have he := hh.unique hpr
        exact hn (Prod.ext he.1 he.2)
      rw [ite_eq_left (show ChainState gs S from Or.inr ⟨p,r,hpr⟩),ite_eq_right hp,zero_add,
        Finset.sum_eq_single (p,r)]
      · simp [hpr,chainMultiplier_defect gs w S hpr]
      · intro pr hm hn
        simp [hu pr hm hn]
      · exact fun hn => False.elim (hn hmem)
    · have hd' : ∀ p r, ¬ DefectState gs p r S := fun p r hh => hd ⟨p,r,hh⟩
      simp [ChainState,hp,hd']

lemma chainTotal_eq (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) :
    chainTotal gs w f = slotTotal gs f ∅ +
      ∑ pr ∈ defectTypes gs, w pr.1 pr.2*slotDefect gs f ∅ pr.1 pr.2 := by
  unfold chainTotal chainWeight
  rw [chain_sum_decomposition,← slotTotal_eq_plain_sum gs hgs hcover f]
  congr 1
  apply Finset.sum_congr rfl
  intro pr hm
  obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hm
  rw [slotDefect_eq_defect_sum gs hgs hcover f pr.1 pr.2 hp hr hpr]

lemma chainTotal_ge_plain (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hf : ∀ S, 0 < f S) (hw : ∀ p r, 0 < w p r) :
    slotTotal gs f ∅ ≤ chainTotal gs w f := by
  rw [chainTotal_eq gs hgs hcover w f]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro pr hm
  obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hm
  exact mul_nonneg (hw _ _).le (slotDefect_pos gs f hf ∅ hgs pr.1 pr.2 hp hr hpr).le

lemma chainTotal_pos (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hf : ∀ S, 0 < f S) (hw : ∀ p r, 0 < w p r) :
    0 < chainTotal gs w f :=
  (slotTotal_pos gs f hf ∅ hgs).trans_le (chainTotal_ge_plain gs hgs hcover w f hf hw)

lemma finite_center_sum {X : Type*} (s : Finset X) (w H : X → ℝ) (a : ℝ) :
    (∑ x ∈ s, w x*(H x-a)^2) = (∑ x ∈ s, w x*(H x)^2) -
      2*a*(∑ x ∈ s,w x*H x)+a^2*(∑ x ∈ s,w x) := by
  have he (x : X) : w x*(H x-a)^2 = w x*(H x)^2 - 2*a*(w x*H x)+a^2*w x := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]

lemma finite_center_at_mean {X : Type*} (s : Finset X) (w H : X → ℝ)
    (hz : (∑ x ∈ s,w x) ≠ 0) :
    (∑ x ∈ s, w x*(H x-(∑ y ∈ s,w y*H y)/(∑ y ∈ s,w y))^2) =
      (∑ x ∈ s,w x*(H x)^2) - (∑ x ∈ s,w x*H x)^2/(∑ x ∈ s,w x) := by
  rw [finite_center_sum]
  field_simp
  ; ring

lemma finite_center_min {X : Type*} (s : Finset X) (w H : X → ℝ) (a : ℝ)
    (hz : 0 < ∑ x ∈ s,w x) :
    (∑ x ∈ s, w x*(H x-(∑ y ∈ s,w y*H y)/(∑ y ∈ s,w y))^2) ≤
      ∑ x ∈ s,w x*(H x-a)^2 := by
  rw [finite_center_at_mean s w H (ne_of_gt hz),finite_center_sum]
  have hsq : 0 ≤ ((∑ x ∈ s,w x*H x)-a*(∑ x ∈ s,w x))^2 := sq_nonneg _
  apply (mul_le_mul_iff_left₀ hz).mp
  field_simp
  nlinarith

noncomputable def chainMean (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f H : Set Γ → ℝ) : ℝ :=
  (∑ S ∈ chainStates gs,chainWeight gs w f S*H S)/chainTotal gs w f
noncomputable def chainVariance (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f H : Set Γ → ℝ) : ℝ :=
  (∑ S ∈ chainStates gs,chainWeight gs w f S*(H S-chainMean gs w f H)^2)/chainTotal gs w f
noncomputable def chainDirichlet (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f H : Set Γ → ℝ) : ℝ :=
  restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅/
    (2*(gs.length:ℝ)^2*chainTotal gs w f)

end Observable

section ChainGeometry
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance54 : Fintype Γ] [sectionInstance55 : DecidableEq Γ]

lemma pairSupport_ncard (ps : List (Γ × Γ)) (A : Set Γ) (hps : SlotsFresh ps A) :
    (A ∪ pairSupport ps).ncard = A.ncard+2*ps.length := by
  induction ps generalizing A with
  | nil => simp
  | cons p ps ih =>
    have he : A ∪ pairSupport (p::ps) = (insert p.1 (insert p.2 A)) ∪ pairSupport ps := by
      rw [pairSupport_cons]
      ext x
      simp only [Set.mem_union,Set.mem_insert_iff]
      tauto
    rw [he,ih _ hps.2.2.2,Set.ncard_insert_of_notMem (by
      simpa only [Set.mem_insert_iff,not_or] using And.intro hps.1 hps.2.1),
      Set.ncard_insert_of_notMem hps.2.2.1,List.length_cons]
    omega

lemma slots_ground_card (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : Fintype.card Γ = 2*gs.length := by
  have h := pairSupport_ncard gs ∅ hgs
  simpa [hcover,Set.ncard_univ,Nat.card_eq_fintype_card] using h

lemma choiceVertices_ncard (ps : List (Γ × Γ)) (A S : Set Γ) (hps : SlotsFresh ps A)
    (hS : S ∈ choiceVertices ps A) : S.ncard = A.ncard+ps.length := by
  induction ps generalizing A with
  | nil =>
    simp only [choiceVertices,Finset.mem_singleton] at hS
    subst S
    simp
  | cons p ps ih =>
    rw [choiceVertices,Finset.mem_union] at hS
    rcases hS with hS | hS
    · have ht : SlotsFresh ps (insert p.1 A) := hps.2.2.2.mono (by
        intro x hx
        simp only [Set.mem_insert_iff] at hx ⊢
        tauto)
      rw [ih _ ht hS,Set.ncard_insert_of_notMem hps.2.1,List.length_cons]
      omega
    · have ht : SlotsFresh ps (insert p.2 A) := hps.2.2.2.mono (Set.subset_insert _ _)
      rw [ih _ ht hS,Set.ncard_insert_of_notMem hps.2.2.1,List.length_cons]
      omega

lemma PlainState.ncard {gs : List (Γ × Γ)} (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) {S : Set Γ} (hS : PlainState gs S) : S.ncard = gs.length := by
  have hm : S ∈ choiceVertices gs ∅ := by rw [choiceVertices_plain gs hgs hcover]; simp [hS]
  simpa using choiceVertices_ncard gs ∅ S hgs hm

lemma DefectState.ncard {gs : List (Γ × Γ)} (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) {p r : Γ × Γ} {S : Set Γ} (hS : DefectState gs p r S) :
    S.ncard = gs.length := by
  let ps := (gs.erase p).erase r
  have hperm : gs.Perm (p::r::ps) := slots_perm_two hS.1 hS.2.1 hS.2.2.1
  have hs := (SlotsFresh.perm hperm ∅).mp hgs
  have ht : SlotsFresh ps {r.1,r.2} := hs.2.2.2.2.2.2.mono (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false] at hx ⊢
    tauto)
  have hm : S ∈ choiceVertices ps {r.1,r.2} := by
    rw [choiceVertices_defect gs hgs hcover p r hS.1 hS.2.1 hS.2.2.1]
    simp [hS]
  have hc := choiceVertices_ncard ps {r.1,r.2} S ht hm
  have hpair : ({r.1,r.2} : Set Γ).ncard = 2 := Set.ncard_pair hs.2.2.2.1
  rw [hpair] at hc
  have hl := hperm.length_eq
  simp only [List.length_cons] at hl
  omega

lemma ChainState.ncard {gs : List (Γ × Γ)} (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) {S : Set Γ} (hS : ChainState gs S) : S.ncard = gs.length := by
  rcases hS with hS | ⟨p,r,hS⟩
  · exact hS.ncard hgs hcover
  · exact hS.ncard hgs hcover

omit sectionInstance54 sectionInstance55 in
lemma ExchangeAdjacent.symm [Fintype Γ] [DecidableEq Γ] {S T : Set Γ} (h : ExchangeAdjacent S T) : ExchangeAdjacent T S := by
  obtain ⟨A,a,b,hab,ha,hb,hS,hT⟩ := h
  exact ⟨A,b,a,hab.symm,hb,ha,hT,hS⟩
omit sectionInstance54 sectionInstance55 in
lemma ExchangeAdjacent.ne [Fintype Γ] [DecidableEq Γ] {S T : Set Γ} (h : ExchangeAdjacent S T) : S ≠ T := by
  obtain ⟨A,a,b,hab,ha,hb,rfl,rfl⟩ := h
  intro he
  have hh : a ∈ insert b A := he ▸ Set.mem_insert a A
  exact (Set.mem_insert_iff.mp hh).elim hab ha

omit sectionInstance54 sectionInstance55 in
lemma ExchangeAdjacent.move [Fintype Γ] [DecidableEq Γ] {S T : Set Γ} (h : ExchangeAdjacent S T) :
    ∃ a ∈ S, ∃ b ∈ Sᶜ, T = insert b (S\{a}) := by
  obtain ⟨A,a,b,hab,ha,hb,rfl,rfl⟩ := h
  refine ⟨a,Set.mem_insert _ _,b,?_,?_⟩
  · simpa only [Set.mem_compl_iff,Set.mem_insert_iff,not_or] using And.intro hab.symm hb
  · congr 1
    ext x
    simp only [Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨Or.inr hx,fun he => ha (he ▸ hx)⟩
    · rintro ⟨hh,hn⟩
      exact hh.resolve_left hn

lemma exchange_neighbors_card (S : Set Γ) :
    (Finset.univ.filter (ExchangeAdjacent S)).card ≤ S.ncard*Sᶜ.ncard := by
  have hsub : Finset.univ.filter (ExchangeAdjacent S) ⊆
      (S.toFinset ×ˢ Sᶜ.toFinset).image (fun ab => insert ab.2 (S\{ab.1})) := by
    intro T hT
    obtain ⟨a,ha,b,hb,rfl⟩ := (Finset.mem_filter.mp hT).2.move
    exact Finset.mem_image.mpr ⟨(a,b),by simpa only [Finset.mem_product,Set.mem_toFinset] using And.intro ha hb,rfl⟩
  calc
    _ ≤ ((S.toFinset ×ˢ Sᶜ.toFinset).image (fun ab => insert ab.2 (S\{ab.1}))).card := Finset.card_le_card hsub
    _ ≤ (S.toFinset ×ˢ Sᶜ.toFinset).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product,← Set.ncard_eq_toFinset_card',← Set.ncard_eq_toFinset_card']

abbrev ChainIndex (gs : List (Γ × Γ)) := {S : Set Γ // ChainState gs S}

lemma chain_neighbors_card (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (S : ChainIndex gs) :
    (Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).card ≤ gs.length^2 := by
  let e : ChainIndex gs → Set Γ := Subtype.val
  have he : Function.Injective e := Subtype.val_injective
  have hsub : (Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).image e ⊆
      Finset.univ.filter (ExchangeAdjacent S.val) := by
    intro T hT
    obtain ⟨U,hU,hUT⟩ := Finset.mem_image.mp hT
    subst T
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hU).2⟩
  have hcompl : S.valᶜ.ncard = gs.length := by
    have hc := S.val.ncard_add_ncard_compl
    rw [Nat.card_eq_fintype_card,slots_ground_card gs hgs hcover,S.property.ncard hgs hcover] at hc
    omega
  calc
    _ = ((Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).image e).card :=
      (Finset.card_image_of_injective _ he).symm
    _ ≤ (Finset.univ.filter (ExchangeAdjacent S.val)).card := Finset.card_le_card hsub
    _ ≤ S.val.ncard*S.valᶜ.ncard := exchange_neighbors_card _
    _ = gs.length^2 := by rw [S.property.ncard hgs hcover,hcompl,pow_two]

end ChainGeometry

open scoped BigOperators Classical

structure FiniteChain (X : Type*) [Fintype X] where
  P : X → X → ℝ
  π : X → ℝ
  positive : ∀ x, 0 < π x
  normalized : ∑ x, π x = 1
  nonnegative : ∀ x y, 0 ≤ P x y
  stochastic : ∀ x, ∑ y, P x y = 1
  reversible : ∀ x y, π x*P x y = π y*P y x
  lazy : ∀ x, 1/2 ≤ P x x

namespace FiniteChain
variable {X : Type*} [sectionInstance56 : Fintype X] (C : FiniteChain X)

noncomputable def inner (f g : X → ℝ) : ℝ := ∑ x, C.π x*f x*g x
noncomputable def apply (f : X → ℝ) (x : X) : ℝ := ∑ y, C.P x y*f y
noncomputable def energy (f : X → ℝ) : ℝ := C.inner f (fun x => f x-C.apply f x)
noncomputable def iterate (k : ℕ) (f : X → ℝ) : X → ℝ := Nat.iterate C.apply k f

lemma inner_symm (f g : X → ℝ) : C.inner f g = C.inner g f := by
  unfold inner
  apply Finset.sum_congr rfl
  intro x _
  ring
lemma inner_sub_right (f g h : X → ℝ) : C.inner f (fun x => g x-h x) = C.inner f g-C.inner f h := by
  simp [inner,mul_sub,Finset.sum_sub_distrib]
lemma inner_nonneg (f : X → ℝ) : 0 ≤ C.inner f f := by
  apply Finset.sum_nonneg
  intro x _
  nlinarith [C.positive x,sq_nonneg (f x)]
lemma apply_const (a : ℝ) : C.apply (fun _ => a) = fun _ => a := by
  funext x
  simp [apply,← Finset.sum_mul,C.stochastic]

lemma stationary (y : X) : ∑ x, C.π x*C.P x y = C.π y := by
  simp_rw [C.reversible]
  rw [← Finset.mul_sum,C.stochastic,mul_one]
lemma apply_selfAdjoint (f g : X → ℝ) : C.inner f (C.apply g) = C.inner (C.apply f) g := by
  unfold inner apply
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have h := C.reversible x y
  calc
    _ = (C.π x*C.P x y)*(f x*g y) := by ring
    _ = (C.π y*C.P y x)*(f x*g y) := by rw [h]
    _ = _ := by ring

lemma energy_eq (f : X → ℝ) : C.energy f =
    (∑ x, ∑ y, C.π x*C.P x y*(f x-f y)^2)/2 := by
  have h₁ : (∑ x,∑ y,C.π x*C.P x y*(f x)^2) = C.inner f f := by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul,C.stochastic,one_mul]
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h₂ : (∑ x,∑ y,C.π x*C.P x y*(f y)^2) = C.inner f f := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,C.stationary]
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h₃ : (∑ x,∑ y,C.π x*C.P x y*(f x*f y)) = C.inner f (C.apply f) := by
    unfold inner apply
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have he (x y : X) : C.π x*C.P x y*(f x-f y)^2 =
      C.π x*C.P x y*(f x)^2+C.π x*C.P x y*(f y)^2-2*(C.π x*C.P x y*(f x*f y)) := by ring
  simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [h₁,h₂,h₃,energy,inner_sub_right]
  ring

lemma energy_nonneg (f : X → ℝ) : 0 ≤ C.energy f := by
  rw [C.energy_eq]
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (mul_nonneg (C.positive x).le (C.nonnegative x y)) (sq_nonneg _)

lemma energy_le_inner (f : X → ℝ) : C.energy f ≤ C.inner f f := by
  classical
  have ho (x : X) : ∑ y ∈ Finset.univ.erase x,C.P x y ≤ 1/2 := by
    have h := Finset.sum_erase_add Finset.univ (fun y => C.P x y) (Finset.mem_univ x)
    rw [C.stochastic] at h
    linarith [C.lazy x]
  have hbound : (∑ x,∑ y,C.π x*C.P x y*(f x-f y)^2) ≤
      ∑ x,∑ y ∈ Finset.univ.erase x,2*(C.π x*C.P x y*(f x)^2+C.π x*C.P x y*(f y)^2) := by
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
    simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero]
    apply Finset.sum_le_sum
    intro y _
    have h := mul_le_mul_of_nonneg_left (show (f x-f y)^2 ≤ 2*((f x)^2+(f y)^2) by nlinarith [sq_nonneg (f x+f y)])
      (mul_nonneg (C.positive x).le (C.nonnegative x y))
    nlinarith
  have hs (x : X) : (∑ y ∈ Finset.univ.erase x,C.π x*C.P x y*(f x)^2) ≤ (C.π x*(f x)^2)/2 := by
    calc
      _ = (C.π x*(f x)^2)*(∑ y ∈ Finset.univ.erase x,C.P x y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (ho x) (mul_nonneg (C.positive x).le (sq_nonneg (f x)))]
  have hswap : (∑ x,∑ y ∈ Finset.univ.erase x,C.π x*C.P x y*(f y)^2) =
      ∑ x,∑ y ∈ Finset.univ.erase x,C.π x*C.P x y*(f x)^2 := by
    simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [C.reversible]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hs x)
  have heq : (∑ x,C.π x*(f x)^2/2) = C.inner f f/2 := by
    rw [← Finset.sum_div]
    congr 1
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq] at hsum
  simp_rw [← Finset.mul_sum,Finset.sum_add_distrib] at hbound
  rw [hswap] at hbound
  rw [C.energy_eq]
  linarith

lemma apply_positive (f : X → ℝ) : 0 ≤ C.inner f (C.apply f) := by
  have h := C.energy_le_inner f
  rw [energy,inner_sub_right] at h
  linarith

@[simp] lemma iterate_zero (f : X → ℝ) : C.iterate 0 f = f := rfl
lemma iterate_succ (k : ℕ) (f : X → ℝ) : C.iterate (k+1) f = C.apply (C.iterate k f) := by
  exact Function.iterate_succ_apply' C.apply k f

noncomputable def partialResolvent (N : ℕ) (f : X → ℝ) (x : X) : ℝ :=
  ∑ k ∈ Finset.range N,C.iterate k f x

noncomputable def pathExpectation : ℕ → X → (List X → ℝ) → ℝ
  | 0,x,F => F [x]
  | N+1,x,F => ∑ y,C.P x y*pathExpectation N y (fun l => F (x::l))

noncomputable def pathSum (g : X → ℝ) (l : List X) : ℝ := (l.map g).sum
noncomputable def squareMoment (g : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  if N=0 then 0 else C.pathExpectation (N-1) x (fun l => (pathSum g l)^2)

variable [DecidableEq X]

noncomputable def ofMoves (π : X → ℝ) (m : X → X → ℝ)
    (hπ : ∀ x,0 < π x) (hπsum : ∑ x,π x = 1)
    (hm : ∀ x y,0 ≤ m x y) (hrow : ∀ x,∑ y,m x y ≤ 1/2)
    (hrev : ∀ x y,π x*m x y = π y*m y x) : FiniteChain X where
  P x y := m x y+if x=y then 1-∑ z,m x z else 0
  π := π
  positive := hπ
  normalized := hπsum
  nonnegative x y := by
    split_ifs
    · linarith [hm x y,hrow x]
    · simpa using hm x y
  stochastic x := by simp [Finset.sum_add_distrib]
  reversible x y := by
    by_cases h : x=y
    · subst y; rfl
    · simp [h,Ne.symm h,hrev]
  lazy x := by simp only [ite_true, if_true]; linarith [hm x x,hrow x]

lemma ofMoves_energy (π : X → ℝ) (m : X → X → ℝ)
    (hπ : ∀ x,0 < π x) (hπsum : ∑ x,π x = 1)
    (hm : ∀ x y,0 ≤ m x y) (hrow : ∀ x,∑ y,m x y ≤ 1/2)
    (hrev : ∀ x y,π x*m x y = π y*m y x) (f : X → ℝ) :
    (ofMoves π m hπ hπsum hm hrow hrev).energy f =
      (∑ x,∑ y,π x*m x y*(f x-f y)^2)/2 := by
  rw [energy_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change π x*(m x y+if x=y then _ else _)*(f x-f y)^2 = _
  by_cases h : x=y
  · subst y; simp
  · simp [h]

end FiniteChain
section Metropolis
open scoped BigOperators Classical
variable {Γ : Type*} [Fintype Γ] [sectionInstance59 : DecidableEq Γ]

lemma chainWeight_pos (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) (S : Set Γ) :
    0 < chainWeight gs w f S := mul_pos (chainMultiplier_pos gs w hw S) (hf S)

omit sectionInstance59 in
lemma chain_sum_subtype [DecidableEq Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℝ) :
    (∑ S ∈ chainStates gs,g S) = ∑ S : ChainIndex gs,g S.val := by
  exact Finset.sum_subtype _ (by intro S; simp [chainStates]) g

noncomputable def metropolisMove (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (S T : ChainIndex gs) : ℝ :=
  if ExchangeAdjacent S.val T.val then
    min (chainWeight gs w f S.val) (chainWeight gs w f T.val)/
      (2*(gs.length:ℝ)^2*chainWeight gs w f S.val) else 0

lemma metropolisMove_nonneg (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ)
    (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) (S T : ChainIndex gs) :
    0 ≤ metropolisMove gs w f S T := by
  have hS := chainWeight_pos gs w f hw hf S.val
  unfold metropolisMove
  split_ifs
  · exact div_nonneg (le_min (chainWeight_pos gs w f hw hf _).le (chainWeight_pos gs w f hw hf _).le)
      (by positivity)
  · rfl

lemma metropolisMove_row (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) (S : ChainIndex gs) :
    ∑ T,metropolisMove gs w f S T ≤ 1/2 := by
  have hS := chainWeight_pos gs w f hw hf S.val
  have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hinc (T : ChainIndex gs) : metropolisMove gs w f S T ≤
      if ExchangeAdjacent S.val T.val then 1/(2*(gs.length:ℝ)^2) else 0 := by
    unfold metropolisMove
    split_ifs
    · apply (div_le_iff₀ (by positivity : 0 < 2*(gs.length:ℝ)^2*chainWeight gs w f S.val)).mpr
      have he : 1/(2*(gs.length:ℝ)^2)*(2*(gs.length:ℝ)^2*chainWeight gs w f S.val) = chainWeight gs w f S.val := by
        field_simp
      rw [he]
      exact min_le_left _ _
    · rfl
  have hs := Finset.sum_le_sum (fun T (_ : T ∈ Finset.univ) => hinc T)
  have hc : ((Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).card:ℝ) ≤ (gs.length:ℝ)^2 := by
    exact_mod_cast chain_neighbors_card gs hgs hcover S
  have he : (gs.length:ℝ)^2*(1/(2*(gs.length:ℝ)^2)) = 1/2 := by field_simp
  calc
    _ ≤ _ := hs
    _ = ((Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).card:ℝ)*(1/(2*(gs.length:ℝ)^2)) := by
      rw [← Finset.sum_filter]; simp
    _ ≤ (gs.length:ℝ)^2*(1/(2*(gs.length:ℝ)^2)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := he

lemma metropolisMove_balanced (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) (S T : ChainIndex gs) :
    (chainWeight gs w f S.val/chainTotal gs w f)*metropolisMove gs w f S T =
    (chainWeight gs w f T.val/chainTotal gs w f)*metropolisMove gs w f T S := by
  have hs := (chainWeight_pos gs w f hw hf S.val).ne'
  have ht := (chainWeight_pos gs w f hw hf T.val).ne'
  by_cases h : ExchangeAdjacent S.val T.val
  · simp only [metropolisMove,ite_eq_left h,ite_eq_left h.symm]
    rw [min_comm (chainWeight gs w f T.val)]
    field_simp
  · have hh : ¬ ExchangeAdjacent T.val S.val := fun hh => h hh.symm
    simp [metropolisMove,h,hh]

noncomputable def metropolisChain (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) : FiniteChain (ChainIndex gs) :=
  FiniteChain.ofMoves (fun S => chainWeight gs w f S.val/chainTotal gs w f) (metropolisMove gs w f)
    (fun S => div_pos (chainWeight_pos gs w f hw hf S.val) (chainTotal_pos gs hgs hcover w f hf hw))
    (by rw [← Finset.sum_div,← chain_sum_subtype]; exact div_self (chainTotal_pos gs hgs hcover w f hf hw).ne')
    (metropolisMove_nonneg gs w f hw hf)
    (metropolisMove_row gs hgs hne hcover w f hw hf)
    (metropolisMove_balanced gs w f hw hf)

end Metropolis

namespace FiniteChain
variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma inner_cauchy (f g : X → ℝ) : (C.inner f g)^2 ≤ C.inner f f*C.inner g g := by
  have he (f g : X → ℝ) : (∑ x,(Real.sqrt (C.π x)*f x)*(Real.sqrt (C.π x)*g x)) = C.inner f g := by
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    have hs := Real.sq_sqrt (C.positive x).le
    calc
      _ = (Real.sqrt (C.π x))^2*f x*g x := by ring
      _ = _ := by rw [hs]
  have hf (f : X → ℝ) : (∑ x,(Real.sqrt (C.π x)*f x)^2) = C.inner f f := by
    simpa only [pow_two] using he f f
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (C.π x)*f x) (fun x => Real.sqrt (C.π x)*g x)
  rwa [he,hf,hf] at h

noncomputable def mean (f : X → ℝ) : ℝ := ∑ x,C.π x*f x
noncomputable def variance (f : X → ℝ) : ℝ := C.inner (fun x => f x-C.mean f) (fun x => f x-C.mean f)

end FiniteChain
section ProjectionBridge
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance61 : Fintype Γ] [sectionInstance62 : DecidableEq Γ]

def ClassObservable (gs : List (Γ × Γ)) (G : Set Γ → ℝ) : Prop :=
  ∀ p r S T, DefectState gs p r S → DefectState gs p r T → G S = G T

noncomputable def extendChainFun (gs : List (Γ × Γ)) (H : ChainIndex gs → ℝ) (S : Set Γ) : ℝ :=
  if h : ChainState gs S then H ⟨S,h⟩ else 0

end ProjectionBridge

structure KilledKernel (B : Type*) [Fintype B] where
  Q : B → B → ℝ
  r : ℝ
  nonnegative : ∀ x y,0 ≤ Q x y
  rnonneg : 0 ≤ r
  rlt : r < 1
  rowbound : ∀ x,∑ y,Q x y ≤ r

namespace KilledKernel
open scoped BigOperators Classical
open Filter
variable {B : Type*} [Fintype B] (Q : KilledKernel B)
noncomputable def apply (f : B → ℝ) (x : B) : ℝ := ∑ y,Q.Q x y*f y
noncomputable def iterate (k : ℕ) (f : B → ℝ) : B → ℝ := Nat.iterate Q.apply k f
@[simp] lemma iterate_zero (f : B → ℝ) : Q.iterate 0 f = f := rfl
lemma iterate_succ (k : ℕ) (f : B → ℝ) : Q.iterate (k+1) f = Q.apply (Q.iterate k f) :=
  Function.iterate_succ_apply' Q.apply k f
lemma iterate_succ' (k : ℕ) (f : B → ℝ) : Q.iterate (k+1) f = Q.iterate k (Q.apply f) :=
  Function.iterate_succ_apply Q.apply k f
lemma apply_sub (f g : B → ℝ) : Q.apply (fun x => f x-g x) = fun x => Q.apply f x-Q.apply g x := by
  funext x
  simp [apply,mul_sub,Finset.sum_sub_distrib]
lemma apply_sum {J : Type*} (s : Finset J) (f : J → B → ℝ) :
    Q.apply (fun x => ∑ j ∈ s,f j x) = fun x => ∑ j ∈ s,Q.apply (f j) x := by
  funext x
  simp only [apply,Finset.mul_sum]
  exact Finset.sum_comm
lemma apply_nonneg (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) : 0 ≤ Q.apply f x :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (Q.nonnegative x y) (hf y))
lemma iterate_nonneg (k : ℕ) (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) : 0 ≤ Q.iterate k f x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih =>
    rw [Q.iterate_succ]
    exact Q.apply_nonneg _ ih x

lemma apply_abs_bound (f : B → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ x,|f x| ≤ M) (x : B) :
    |Q.apply f x| ≤ Q.r*M := by
  calc
    _ ≤ ∑ y,|Q.Q x y*f y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y,Q.Q x y*|f y| := by simp_rw [abs_mul,abs_of_nonneg (Q.nonnegative x _) ]
    _ ≤ ∑ y,Q.Q x y*M := Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hf y) (Q.nonnegative x y))
    _ = (∑ y,Q.Q x y)*M := (Finset.sum_mul _ _ _).symm
    _ ≤ Q.r*M := mul_le_mul_of_nonneg_right (Q.rowbound x) hM

lemma iterate_abs_bound (k : ℕ) (f : B → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ x,|f x| ≤ M) (x : B) :
    |Q.iterate k f x| ≤ Q.r^k*M := by
  induction k generalizing x with
  | zero => simpa using hf x
  | succ k ih =>
    rw [Q.iterate_succ,pow_succ']
    simpa only [mul_assoc] using Q.apply_abs_bound (Q.iterate k f) (Q.r^k*M)
      (mul_nonneg (pow_nonneg Q.rnonneg _) hM) ih x

lemma summable_iterate (f : B → ℝ) (x : B) : Summable (fun k => Q.iterate k f x) := by
  let M := ∑ y,|f y|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun y _ => abs_nonneg _)
  have hf : ∀ y,|f y| ≤ M := fun y => Finset.single_le_sum (f := fun z => |f z|) (fun z _ => abs_nonneg _) (Finset.mem_univ y)
  exact (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => Q.iterate_abs_bound k f M hM hf x)
    ((summable_geometric_of_lt_one Q.rnonneg Q.rlt).mul_right M)).of_abs

lemma iterate_tendsto_zero (f : B → ℝ) (x : B) : Tendsto (fun k => Q.iterate k f x) atTop (nhds 0) := by
  let M := ∑ y,|f y|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun y _ => abs_nonneg _)
  have hf : ∀ y,|f y| ≤ M := fun y => Finset.single_le_sum (f := fun z => |f z|) (fun z _ => abs_nonneg _) (Finset.mem_univ y)
  have ht : Tendsto (fun k => Q.r^k*M) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Q.rnonneg Q.rlt).mul_const M
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr (squeeze_zero (fun k => abs_nonneg _)
    (fun k => Q.iterate_abs_bound k f M hM hf x) ht)

noncomputable def green (f : B → ℝ) (x : B) : ℝ := ∑' k,Q.iterate k f x
lemma green_nonneg (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) : 0 ≤ Q.green f x :=
  tsum_nonneg (fun k => Q.iterate_nonneg k f hf x)

lemma green_firstStep (f : B → ℝ) (x : B) : Q.green f x = f x+Q.apply (Q.green f) x := by
  unfold green
  rw [(Q.summable_iterate f x).tsum_eq_zero_add]
  simp only [Q.iterate_zero,Q.iterate_succ,apply]
  congr 1
  rw [Summable.tsum_finsetSum (fun y (_ : y ∈ Finset.univ) => (Q.summable_iterate f y).mul_left (Q.Q x y))]
  simp_rw [tsum_mul_left]

lemma iterate_sub (k : ℕ) (f g : B → ℝ) :
    Q.iterate k (fun x => f x-g x) = fun x => Q.iterate k f x-Q.iterate k g x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Q.iterate_succ,ih,Q.apply_sub,← Q.iterate_succ,← Q.iterate_succ]
lemma iterate_sum {J : Type*} (s : Finset J) (f : J → B → ℝ) (k : ℕ) :
    Q.iterate k (fun x => ∑ j ∈ s,f j x) = fun x => ∑ j ∈ s,Q.iterate k (f j) x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Q.iterate_succ,ih,Q.apply_sum]; simp_rw [← Q.iterate_succ]

lemma green_sum {J : Type*} (s : Finset J) (f : J → B → ℝ) (x : B) :
    Q.green (fun x => ∑ j ∈ s,f j x) x = ∑ j ∈ s,Q.green (f j) x := by
  unfold green
  simp_rw [Q.iterate_sum]
  exact Summable.tsum_finsetSum (fun j _ => Q.summable_iterate (f j) x)

lemma iterate_residual_sum (f : B → ℝ) (N : ℕ) (x : B) :
    (∑ k ∈ Finset.range N,Q.iterate k (fun y => f y-Q.apply f y) x) = f x-Q.iterate N f x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Q.iterate_sub,← Q.iterate_succ']
    simp only
    ring

lemma green_residual (f : B → ℝ) (x : B) : Q.green (fun y => f y-Q.apply f y) x = f x := by
  have hs := (Q.summable_iterate (fun y => f y-Q.apply f y) x).tendsto_sum_tsum_nat
  simp_rw [Q.iterate_residual_sum] at hs
  have ht : Tendsto (fun N => f x-Q.iterate N f x) atTop (nhds (f x)) := by
    simpa using tendsto_const_nhds.sub (Q.iterate_tendsto_zero f x)
  exact tendsto_nhds_unique hs ht

end KilledKernel
namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance66 : Fintype X] (C : FiniteChain X) (A : X → Prop)

abbrev Inside := {x : X // A x}
abbrev Outside := {x : X // ¬ A x}

noncomputable def mergeFun (h : Inside A → ℝ) (b : Outside A → ℝ) (x : X) : ℝ :=
  if hx : A x then h ⟨x,hx⟩ else b ⟨x,hx⟩
omit sectionInstance66 in
@[simp] lemma mergeFun_inside [Fintype X] (h : Inside A → ℝ) (b : Outside A → ℝ) (x : Inside A) :
    mergeFun A h b x.val = h x := by simp [mergeFun,x.property]
omit sectionInstance66 in
@[simp] lemma mergeFun_outside [Fintype X] (h : Inside A → ℝ) (b : Outside A → ℝ) (x : Outside A) :
    mergeFun A h b x.val = b x := by simp [mergeFun,x.property]

variable (Q : KilledKernel (Outside A)) (hQ : ∀ x y : Outside A,Q.Q x y = C.P x.val y.val)

noncomputable def hitKernel (x : Outside A) (y : Inside A) : ℝ :=
  Q.green (fun z => C.P z.val y.val) x
lemma hitKernel_nonneg (x : Outside A) (y : Inside A) : 0 ≤ C.hitKernel A Q x y :=
  Q.green_nonneg _ (fun z => C.nonnegative z.val y.val) x

include hQ in
lemma exitRow (x : Outside A) : (∑ y : Inside A,C.P x.val y.val) = 1-Q.apply (fun _ => 1) x := by
  have hh := Fintype.sum_subtype_add_sum_subtype A (fun y => C.P x.val y)
  rw [C.stochastic] at hh
  have he : Q.apply (fun _ => 1) x = ∑ y : Outside A,C.P x.val y.val := by
    simp [KilledKernel.apply,hQ]
  rw [he]
  linarith

include hQ in
lemma hitKernel_row (x : Outside A) : ∑ y : Inside A,C.hitKernel A Q x y = 1 := by
  unfold hitKernel
  rw [← Q.green_sum Finset.univ]
  have he : (fun z : Outside A => ∑ y : Inside A,C.P z.val y.val) =
      fun z => 1-Q.apply (fun _ => 1) z := by
    funext z
    exact C.exitRow A Q hQ z
  rw [he,Q.green_residual]

include hQ in
lemma hitKernel_firstStep (x : Outside A) (y : Inside A) :
    C.hitKernel A Q x y = C.P x.val y.val+∑ z : Outside A,C.P x.val z.val*C.hitKernel A Q z y := by
  unfold hitKernel
  rw [Q.green_firstStep]
  simp only [KilledKernel.apply,hQ]

noncomputable def traceMatrix (x y : Inside A) : ℝ :=
  C.P x.val y.val+∑ z : Outside A,C.P x.val z.val*C.hitKernel A Q z y
noncomputable def traceApply (h : Inside A → ℝ) (x : Inside A) : ℝ :=
  ∑ y,C.traceMatrix A Q x y*h y

lemma traceMatrix_nonneg (x y : Inside A) : 0 ≤ C.traceMatrix A Q x y :=
  add_nonneg (C.nonnegative _ _) (Finset.sum_nonneg (fun z _ => mul_nonneg
    (C.nonnegative _ _) (C.hitKernel_nonneg A Q z y)))
lemma traceMatrix_lazy (x : Inside A) : 1/2 ≤ C.traceMatrix A Q x x := by
  exact (C.lazy x.val).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun z _ =>
    mul_nonneg (C.nonnegative _ _) (C.hitKernel_nonneg A Q z x))))
include hQ in
lemma traceMatrix_stochastic (x : Inside A) : ∑ y,C.traceMatrix A Q x y = 1 := by
  unfold traceMatrix
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,C.hitKernel_row A Q hQ,mul_one]
  rw [Fintype.sum_subtype_add_sum_subtype A,C.stochastic]

noncomputable def offExtension (h : Inside A → ℝ) (x : Outside A) : ℝ :=
  ∑ y : Inside A,C.hitKernel A Q x y*h y
noncomputable def harmonicExtension (h : Inside A → ℝ) : X → ℝ := mergeFun A h (C.offExtension A Q h)
@[simp] lemma harmonicExtension_inside (h : Inside A → ℝ) (x : Inside A) :
    C.harmonicExtension A Q h x.val = h x := mergeFun_inside _ _ _ _
@[simp] lemma harmonicExtension_outside (h : Inside A → ℝ) (x : Outside A) :
    C.harmonicExtension A Q h x.val = C.offExtension A Q h x := mergeFun_outside _ _ _ _

include hQ in
lemma offExtension_firstStep (h : Inside A → ℝ) (x : Outside A) :
    C.offExtension A Q h x = (∑ y : Inside A,C.P x.val y.val*h y)+
      ∑ z : Outside A,C.P x.val z.val*C.offExtension A Q h z := by
  unfold offExtension
  calc
    _ = ∑ y : Inside A,(C.P x.val y.val+∑ z : Outside A,C.P x.val z.val*C.hitKernel A Q z y)*h y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [C.hitKernel_firstStep A Q hQ]
    _ = _ := ?_
  simp only [add_mul,Finset.sum_mul,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [mul_assoc,← Finset.mul_sum]

include hQ in
lemma harmonicExtension_harmonic (h : Inside A → ℝ) (x : Outside A) :
    C.apply (C.harmonicExtension A Q h) x.val = C.harmonicExtension A Q h x.val := by
  unfold apply
  rw [← Fintype.sum_subtype_add_sum_subtype A]
  simp only [C.harmonicExtension_inside,C.harmonicExtension_outside]
  exact (C.offExtension_firstStep A Q hQ h x).symm

lemma apply_harmonicExtension_inside (h : Inside A → ℝ) (x : Inside A) :
    C.apply (C.harmonicExtension A Q h) x.val = C.traceApply A Q h x := by
  unfold apply
  rw [← Fintype.sum_subtype_add_sum_subtype A]
  simp only [C.harmonicExtension_inside,C.harmonicExtension_outside]
  unfold traceApply traceMatrix offExtension
  simp_rw [add_mul,Finset.sum_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

include hQ in
lemma harmonic_inner_residual (h g : Inside A → ℝ) :
    C.inner (C.harmonicExtension A Q h)
      (fun x => C.harmonicExtension A Q g x-C.apply (C.harmonicExtension A Q g) x) =
    ∑ x : Inside A,C.π x.val*h x*(g x-C.traceApply A Q g x) := by
  unfold inner
  rw [← Fintype.sum_subtype_add_sum_subtype A]
  simp only [C.harmonicExtension_inside,C.apply_harmonicExtension_inside,
    C.harmonicExtension_harmonic A Q hQ,sub_self,mul_zero,Finset.sum_const_zero,add_zero]

end
section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
variable (Q : KilledKernel (Outside A)) (hQ : ∀ x y : Outside A,Q.Q x y = C.P x.val y.val)

lemma residual_symmetric (f g : X → ℝ) :
    C.inner f (fun x => g x-C.apply g x) = C.inner g (fun x => f x-C.apply f x) := by
  rw [C.inner_sub_right,C.inner_sub_right,C.apply_selfAdjoint,C.inner_symm f g,
    C.inner_symm (C.apply f) g]

include hQ in
lemma traceMatrix_reversible (x y : Inside A) :
    C.π x.val*C.traceMatrix A Q x y = C.π y.val*C.traceMatrix A Q y x := by
  by_cases hxy : x = y
  · subst y; rfl
  have h := C.residual_symmetric (C.harmonicExtension A Q (fun z => if z=x then 1 else 0))
    (C.harmonicExtension A Q (fun z => if z=y then 1 else 0))
  rw [C.harmonic_inner_residual A Q hQ,C.harmonic_inner_residual A Q hQ] at h
  simp [traceApply,hxy,Ne.symm hxy] at h
  linarith

noncomputable def insideMass : ℝ := ∑ x : Inside A,C.π x.val
lemma insideMass_pos [Nonempty (Inside A)] : 0 < C.insideMass A := by
  apply Finset.sum_pos
  · intro x _; exact C.positive _
  · exact Finset.univ_nonempty

noncomputable def traceChain [Nonempty (Inside A)] : FiniteChain (Inside A) where
  P := C.traceMatrix A Q
  π := fun x => C.π x.val/C.insideMass A
  positive := fun x => div_pos (C.positive _) (C.insideMass_pos A)
  normalized := by rw [← Finset.sum_div]; exact div_self (C.insideMass_pos A).ne'
  nonnegative := C.traceMatrix_nonneg A Q
  stochastic := C.traceMatrix_stochastic A Q hQ
  reversible := by
    intro x y
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,C.traceMatrix_reversible A Q hQ]
  lazy := C.traceMatrix_lazy A Q

lemma mean_apply (f : X → ℝ) : C.mean (C.apply f) = C.mean f := by
  unfold mean apply
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,C.stationary]

noncomputable def duration (x : Outside A) : ℝ := Q.green (fun _ => 1) x
noncomputable def returnCost (x : Inside A) : ℝ :=
  1+∑ y : Outside A,C.P x.val y.val*duration A Q y
end
section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
variable (hExit : ∀ x : Outside A,∃ y : Inside A,0 < C.P x.val y.val)
noncomputable def exitProbability (x : Outside A) : ℝ := ∑ y : Inside A,C.P x.val y.val
lemma exitProbability_nonneg (x : Outside A) : 0 ≤ C.exitProbability A x :=
  Finset.sum_nonneg (fun y _ => C.nonnegative x.val y.val)
include hExit in
lemma exitProbability_pos (x : Outside A) : 0 < C.exitProbability A x := by
  obtain ⟨y,hy⟩ := hExit x
  exact hy.trans_le (Finset.single_le_sum (fun z _ => C.nonnegative _ _) (Finset.mem_univ y))
lemma exitProbability_le_one (x : Outside A) : C.exitProbability A x ≤ 1 := by
  have h := Fintype.sum_subtype_add_sum_subtype A (fun y => C.P x.val y)
  rw [C.stochastic] at h
  have hn : 0 ≤ ∑ y : Outside A,C.P x.val y.val := Finset.sum_nonneg (fun y _ => C.nonnegative _ _)
  change (∑ y : Inside A,C.P x.val y.val) ≤ 1
  linarith
noncomputable def killedChain : KilledKernel (Outside A) where
  Q := fun x y => C.P x.val y.val
  r := 1-∏ x : Outside A,C.exitProbability A x
  nonnegative := fun x y => C.nonnegative _ _
  rnonneg := sub_nonneg.mpr (Finset.prod_le_one (fun x _ => C.exitProbability_nonneg A x)
    (fun x _ => C.exitProbability_le_one A x))
  rlt := by
    have h : 0 < ∏ x : Outside A,C.exitProbability A x := Finset.prod_pos (fun x _ => C.exitProbability_pos A hExit x)
    linarith
  rowbound := by
    intro x
    have hprod : (∏ z : Outside A,C.exitProbability A z) ≤ C.exitProbability A x := by
      have h := Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr (Finset.mem_univ x))
        (fun z (_ : z ∈ Finset.univ) => C.exitProbability_nonneg A z)
        (fun z _ _ => C.exitProbability_le_one A z)
      simpa only [Finset.prod_singleton] using h
    have hs := Fintype.sum_subtype_add_sum_subtype A (fun y => C.P x.val y)
    rw [C.stochastic] at hs
    change (∑ y : Inside A,C.P x.val y.val)+(∑ y : Outside A,C.P x.val y.val) = 1 at hs
    unfold exitProbability at hprod ⊢
    linarith
end
open scoped Classical BigOperators
variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma apply_cauchy (f g : X → ℝ) :
    (C.inner f (C.apply g))^2 ≤ C.inner f (C.apply f)*C.inner g (C.apply g) := by
  let B : LinearMap.BilinForm ℝ (X → ℝ) := Matrix.toBilin' (fun x y => C.π x*C.P x y)
  have he (u v : X → ℝ) : B u v = C.inner u (C.apply v) := by
    simp only [B,inner,apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    change v y*(u x*(C.π x*C.P x y))=C.π x*u x*(C.P x y*v y)
    ring
  have hs : LinearMap.IsSymm B := by
    constructor
    intro u v
    simp only [he,RingHom.id_apply]
    rw [C.apply_selfAdjoint,C.inner_symm]
  simpa only [he] using B.apply_sq_le_of_symm (fun u => by rw [he]; exact C.apply_positive u) hs f g

lemma inner_sub_left (f g h : X → ℝ) :
    C.inner (fun x => f x-g x) h = C.inner f h-C.inner g h := by
  rw [C.inner_symm,C.inner_sub_right,C.inner_symm h f,C.inner_symm h g]
lemma apply_sub (f g : X → ℝ) : C.apply (fun x => f x-g x) = fun x => C.apply f x-C.apply g x := by
  funext x
  simp [apply,mul_sub,Finset.sum_sub_distrib]
lemma mean_const (a : ℝ) : C.mean (fun _ => a) = a := by
  simp [mean,← Finset.sum_mul,C.normalized]
lemma mean_sub (f g : X → ℝ) : C.mean (fun x => f x-g x) = C.mean f-C.mean g := by
  simp [mean,mul_sub,Finset.sum_sub_distrib]
lemma variance_eq_inner (f : X → ℝ) (hf : C.mean f = 0) : C.variance f = C.inner f f := by
  simp [variance,hf]

lemma apply_contraction (r : ℝ) (hr : 0 ≤ r)
    (hgap : ∀ f : X → ℝ,C.mean f = 0 → C.inner f (C.apply f) ≤ r*C.inner f f)
    (f : X → ℝ) (hf : C.mean f = 0) :
    C.inner (C.apply f) (C.apply f) ≤ r^2*C.inner f f := by
  have hg : C.mean (C.apply f) = 0 := by rw [C.mean_apply,hf]
  have hcs := C.apply_cauchy (C.apply f) f
  have h₁ := hgap f hf
  have h₂ := hgap (C.apply f) hg
  have hp₁ := C.apply_positive f
  have hp₂ := C.apply_positive (C.apply f)
  have hn := C.inner_nonneg (C.apply f)
  have hm := C.inner_nonneg f
  have hb := mul_le_mul h₂ h₁ hp₁ (mul_nonneg hr hn)
  by_cases hz : C.inner (C.apply f) (C.apply f) = 0
  · rw [hz]; positivity
  · have hpos : 0 < C.inner (C.apply f) (C.apply f) := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

lemma iterate_mean (k : ℕ) (f : X → ℝ) : C.mean (C.iterate k f) = C.mean f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [C.iterate_succ,C.mean_apply,ih]
lemma iterate_contraction (r : ℝ) (hr : 0 ≤ r)
    (hgap : ∀ f : X → ℝ,C.mean f = 0 → C.inner f (C.apply f) ≤ r*C.inner f f)
    (k : ℕ) (f : X → ℝ) (hf : C.mean f = 0) :
    C.inner (C.iterate k f) (C.iterate k f) ≤ r^(2*k)*C.inner f f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [C.iterate_succ]
    calc
      _ ≤ r^2*C.inner (C.iterate k f) (C.iterate k f) :=
        C.apply_contraction r hr hgap _ (by rw [C.iterate_mean,hf])
      _ ≤ r^2*(r^(2*k)*C.inner f f) := mul_le_mul_of_nonneg_left ih (sq_nonneg r)
      _ = _ := by rw [show 2*(k+1)=2+2*k by omega,pow_add]; ring

noncomputable def pointDensity (x : X) (y : X) : ℝ := if y=x then 1/C.π x else 0
noncomputable def centeredPoint (x : X) (y : X) : ℝ := C.pointDensity x y-1
lemma pointDensity_mean (x : X) : C.mean (C.pointDensity x) = 1 := by
  simp [mean,pointDensity,(C.positive x).ne']
lemma centeredPoint_mean (x : X) : C.mean (C.centeredPoint x) = 0 := by
  change C.mean (fun z => C.pointDensity x z-1) = 0
  rw [C.mean_sub,C.pointDensity_mean,C.mean_const,sub_self]
lemma pointDensity_inner (x : X) (f : X → ℝ) : C.inner (C.pointDensity x) f = f x := by
  simp [inner,pointDensity,(C.positive x).ne']
lemma centeredPoint_norm (x : X) : C.inner (C.centeredPoint x) (C.centeredPoint x) ≤ 1/C.π x := by
  unfold centeredPoint
  rw [C.inner_sub_left,C.inner_sub_right,C.inner_sub_right,C.pointDensity_inner,
    C.pointDensity_inner,C.inner_symm (fun _ => 1),C.pointDensity_inner]
  have h₁ : C.inner (fun _ => 1) (fun _ => 1) = 1 := by simp [inner,C.normalized]
  rw [h₁]
  simp only [pointDensity,ite_true, if_true]
  linarith

lemma iterate_const (k : ℕ) (a : ℝ) : C.iterate k (fun _ => a) = fun _ => a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [C.iterate_succ,ih,C.apply_const]
lemma iterate_sub (k : ℕ) (f g : X → ℝ) :
    C.iterate k (fun x => f x-g x) = fun x => C.iterate k f x-C.iterate k g x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [C.iterate_succ,ih,C.apply_sub,C.iterate_succ,C.iterate_succ]

lemma point_mixing_squared (r : ℝ) (hr : 0 ≤ r)
    (hgap : ∀ f : X → ℝ,C.mean f = 0 → C.inner f (C.apply f) ≤ r*C.inner f f)
    (k : ℕ) (x y : X) :
    (C.iterate k (C.pointDensity y) x-1)^2 ≤ r^(2*k)/(C.π x*C.π y) := by
  have he : C.inner (C.centeredPoint x) (C.iterate k (C.centeredPoint y)) =
      C.iterate k (C.pointDensity y) x-1 := by
    change C.inner (fun z => C.pointDensity x z-1) (C.iterate k (C.centeredPoint y)) = _
    rw [C.inner_sub_left,C.pointDensity_inner]
    have hm : C.inner (fun _ => 1) (C.iterate k (C.centeredPoint y)) = 0 := by
      have hz := C.iterate_mean k (C.centeredPoint y)
      rw [C.centeredPoint_mean] at hz
      simpa only [inner,mean,mul_one] using hz
    rw [hm,sub_zero]
    change C.iterate k (fun z => C.pointDensity y z-1) x = _
    rw [C.iterate_sub,C.iterate_const]
  have hcs := C.inner_cauchy (C.centeredPoint x) (C.iterate k (C.centeredPoint y))
  rw [he] at hcs
  have hcon := C.iterate_contraction r hr hgap k (C.centeredPoint y) (C.centeredPoint_mean y)
  have hny := C.centeredPoint_norm y
  have hnx := C.centeredPoint_norm x
  have hb := mul_le_mul hnx (hcon.trans (mul_le_mul_of_nonneg_left hny (pow_nonneg hr _)))
    (C.inner_nonneg _) (div_nonneg (by norm_num) (C.positive x).le)
  calc
    _ ≤ _ := hcs.trans hb
    _ = _ := by field_simp

lemma poincare_rayleigh (K : ℝ) (hK : 0 < K)
    (hp : ∀ f : X → ℝ,C.variance f ≤ K*C.energy f)
    (f : X → ℝ) (hf : C.mean f = 0) :
    C.inner f (C.apply f) ≤ (1-1/K)*C.inner f f := by
  have h := hp f
  rw [C.variance_eq_inner f hf,energy,C.inner_sub_right] at h
  apply (mul_le_mul_iff_right₀ hK).mp
  field_simp
  nlinarith

lemma point_mixing (r m : ℝ) (hr : 0 ≤ r) (hm : 0 < m) (hπ : ∀ x,m ≤ C.π x)
    (hgap : ∀ f : X → ℝ,C.mean f = 0 → C.inner f (C.apply f) ≤ r*C.inner f f)
    (k : ℕ) (x y : X) :
    |C.iterate k (C.pointDensity y) x-1| ≤ r^k/m := by
  have hs := C.point_mixing_squared r hr hgap k x y
  have hd : m^2 ≤ C.π x*C.π y := by simpa only [pow_two] using mul_le_mul (hπ x) (hπ y) hm.le (C.positive x).le
  have hb : r^(2*k)/(C.π x*C.π y) ≤ (r^k/m)^2 := by
    calc
      _ ≤ r^(2*k)/m^2 := div_le_div_of_nonneg_left (pow_nonneg hr _) (sq_pos_of_pos hm) hd
      _ = _ := by rw [mul_comm 2 k,pow_mul,div_pow]
  have ha : (|C.iterate k (C.pointDensity y) x-1|)^2 ≤ (r^k/m)^2 := by
    rw [sq_abs]
    exact hs.trans hb
  exact (sq_le_sq₀ (abs_nonneg _) (div_nonneg (pow_nonneg hr _) hm.le)).mp ha

lemma point_mixing_exp (K m : ℝ) (hK : 1 ≤ K) (hm : 0 < m) (hπ : ∀ x,m ≤ C.π x)
    (hp : ∀ f : X → ℝ,C.variance f ≤ K*C.energy f)
    (k : ℕ) (x y : X) :
    |C.iterate k (C.pointDensity y) x-1| ≤ Real.exp (-(k:ℝ)/K)/m := by
  have hKp : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hr : 0 ≤ 1-1/K := sub_nonneg.mpr ((div_le_one hKp).mpr hK)
  have hpow : (1-1/K)^k ≤ Real.exp (-(k:ℝ)/K) := by
    have hle : 1-1/K ≤ Real.exp (-1/K) := by
      have hh := Real.add_one_le_exp (-1/K)
      convert hh using 1 <;> first | rfl | ring
    calc
      _ ≤ (Real.exp (-1/K))^k := pow_le_pow_left₀ hr hle k
      _ = Real.exp ((k:ℝ)*(-1/K)) := (Real.exp_nat_mul _ _).symm
      _ = _ := by congr 1; ring
  exact (C.point_mixing _ m hr hm hπ (C.poincare_rayleigh K hKp hp) k x y).trans
    (div_le_div_of_nonneg_right hpow hm.le)
end FiniteChain
section TraceGeometry
open scoped Classical BigOperators
variable {Γ : Type*} [Fintype Γ] [sectionInstance71 : DecidableEq Γ]

lemma SlotsFresh.cross_ne {gs : List (Γ × Γ)} {A : Set Γ} (hgs : SlotsFresh gs A)
    {p r : Γ × Γ} (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r)
    {x y : Γ} (hx : x=p.1 ∨ x=p.2) (hy : y=r.1 ∨ y=r.2) : x ≠ y := by
  intro hxy
  have := hgs.pair_contains_unique hp hr hx (hxy ▸ hy)
  exact hpr this

lemma DefectState.plain_neighbor {gs : List (Γ × Γ)} (hgs : SlotsFresh gs ∅)
    {p r : Γ × Γ} {S : Set Γ} (hS : DefectState gs p r S) :
    ∃ T,PlainState gs T ∧ ExchangeAdjacent S T := by
  obtain ⟨hp,hr,hpr,he,hf,ht⟩ := hS
  let T := insert p.1 (S\{r.1})
  have hpne : p.1 ≠ p.2 := ((SlotsFresh.perm (List.perm_cons_erase hp) ∅).mp hgs).1
  have hrne : r.1 ≠ r.2 := ((SlotsFresh.perm (List.perm_cons_erase hr) ∅).mp hgs).1
  have hpr11 : p.1 ≠ r.1 := hgs.cross_ne hp hr hpr (Or.inl rfl) (Or.inl rfl)
  have hpr21 : p.2 ≠ r.1 := hgs.cross_ne hp hr hpr (Or.inr rfl) (Or.inl rfl)
  have hpr12 : p.1 ≠ r.2 := hgs.cross_ne hp hr hpr (Or.inl rfl) (Or.inr rfl)
  refine ⟨T,?_,?_⟩
  · intro t htm
    by_cases htp : t=p
    · subst t
      simp [PairSingle,T,hpne.symm,he.1,he.2]
    by_cases htr : t=r
    · subst t
      simp [PairSingle,T,hpr11.symm,hpr12.symm,hrne.symm,hf.2]
    have h₁ : t.1 ≠ p.1 := hgs.cross_ne htm hp htp (Or.inl rfl) (Or.inl rfl)
    have h₂ : t.2 ≠ p.1 := hgs.cross_ne htm hp htp (Or.inr rfl) (Or.inl rfl)
    have h₃ : t.1 ≠ r.1 := hgs.cross_ne htm hr htr (Or.inl rfl) (Or.inl rfl)
    have h₄ : t.2 ≠ r.1 := hgs.cross_ne htm hr htr (Or.inr rfl) (Or.inl rfl)
    simpa only [PairSingle,T,Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff,
      h₁,h₂,h₃,h₄,false_or,not_false_eq_true,and_true] using ht t htm htp htr
  · refine ⟨S\{r.1},r.1,p.1,hpr11.symm,by simp,?_,?_,rfl⟩
    · exact fun h => he.1 h.1
    · ext x
      simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
      constructor
      · intro hx
        by_cases h : x=r.1
        · exact Or.inl h
        · exact Or.inr ⟨hx,h⟩
      · rintro (rfl|⟨hx,_⟩)
        · exact hf.1
        · exact hx

abbrev PlainIndex (gs : List (Γ × Γ)) :=
  FiniteChain.Inside (fun S : ChainIndex gs => PlainState gs S.val)

omit sectionInstance71 in
lemma plainIndex_sum [DecidableEq Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℝ) :
    (∑ S : PlainIndex gs,g S.val.val) = ∑ S ∈ Finset.univ.filter (PlainState gs),g S := by
  let e : PlainIndex gs ≃ {S : Set Γ // PlainState gs S} :=
    { toFun := fun S => ⟨S.val.val,S.property⟩
      invFun := fun S => ⟨⟨S.val,Or.inl S.property⟩,S.property⟩
      left_inv := by intro; rfl
      right_inv := by intro; rfl }
  calc
    _ = ∑ S : {S : Set Γ // PlainState gs S},g S.val :=
      Fintype.sum_equiv e _ _ (by intro S; rfl)
    _ = _ := (Finset.sum_subtype _ (by intro S; simp) g).symm

lemma plainIndex_nonempty (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : Nonempty (PlainIndex gs) := by
  have hz := slotTotal_pos gs (fun _ => (1:ℝ)) (by intro; norm_num) ∅ hgs
  rw [slotTotal_eq_plain_sum gs hgs hcover,← plainIndex_sum] at hz
  by_contra h
  have : IsEmpty (PlainIndex gs) := not_nonempty_iff.mp h
  simp at hz

lemma metropolis_plain_exit (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (S : FiniteChain.Outside (fun S : ChainIndex gs => PlainState gs S.val)) :
    ∃ T : PlainIndex gs,0 < (metropolisChain gs hgs hne hcover w f hw hf).P S.val T.val := by
  obtain ⟨p,r,hS⟩ := S.val.property.resolve_left S.property
  obtain ⟨T,hT,hST⟩ := hS.plain_neighbor hgs
  let t : PlainIndex gs := ⟨⟨T,Or.inl hT⟩,hT⟩
  refine ⟨t,?_⟩
  have hneST : S.val ≠ t.val := by intro h; exact hST.ne (congrArg Subtype.val h)
  change 0 < metropolisMove gs w f S.val t.val+if S.val=t.val then _ else _
  rw [ite_eq_right hneST,add_zero]
  unfold metropolisMove
  rw [ite_eq_left hST]
  have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  exact div_pos (lt_min (chainWeight_pos gs w f hw hf _) (chainWeight_pos gs w f hw hf _))
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hn)) (chainWeight_pos gs w f hw hf _))
end TraceGeometry
section TracePoincare
open scoped Classical BigOperators
variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
  (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
  (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)

abbrev plainPredicate (gs : List (Γ × Γ)) (S : ChainIndex gs) := PlainState gs S.val
noncomputable def metropolisKilled : KilledKernel (FiniteChain.Outside (plainPredicate gs)) :=
  (metropolisChain gs hgs hne hcover w f hw hf).killedChain (plainPredicate gs)
    (metropolis_plain_exit gs hgs hne hcover w f hw hf)

noncomputable def metropolisTrace : FiniteChain (PlainIndex gs) := by
  letI := plainIndex_nonempty gs hgs hcover
  exact (metropolisChain gs hgs hne hcover w f hw hf).traceChain (plainPredicate gs)
    (metropolisKilled gs hgs hne hcover w f hw hf) (by intro _ _; rfl)

end TracePoincare

namespace KilledKernel
open scoped BigOperators Classical
variable {B : Type*} [Fintype B] (Q : KilledKernel B)
noncomputable def partialGreen (N : ℕ) (f : B → ℝ) (x : B) : ℝ :=
  ∑ k ∈ Finset.range N,Q.iterate k f x
end KilledKernel

namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
  (Q : KilledKernel (Outside A)) (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)

noncomputable def cappedTrace (N : ℕ) (x y : Inside A) : ℝ :=
  C.P x.val y.val + ∑ z : Outside A,C.P x.val z.val*
    Q.partialGreen N (fun t => C.P t.val y.val) z
end FiniteChain

structure FiniteKernel (X Y : Type*) [Fintype Y] where
  P : X → Y → ℝ
  nonnegative : ∀ x y,0 ≤ P x y
  substochastic : ∀ x,∑ y,P x y ≤ 1
namespace FiniteKernel
open scoped BigOperators Classical
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
noncomputable def identity : FiniteKernel X X where
  P x y := if x=y then 1 else 0
  nonnegative := by intros; split_ifs <;> norm_num
  substochastic := by intro x; simp
noncomputable def comp (K : FiniteKernel X Y) (L : FiniteKernel Y Z) : FiniteKernel X Z where
  P x z := ∑ y,K.P x y*L.P y z
  nonnegative := by intros; exact Finset.sum_nonneg (fun y _ => mul_nonneg (K.nonnegative _ _) (L.nonnegative _ _))
  substochastic := by
    intro x
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ y,K.P x y*1 := Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (L.substochastic y) (K.nonnegative x y))
      _ ≤ 1 := by simp only [mul_one]; exact K.substochastic x
noncomputable def push (K : FiniteKernel X Y) (ν : X → ℝ) (y : Y) := ∑ x,ν x*K.P x y
lemma push_nonneg (K : FiniteKernel X Y) (ν : X → ℝ) (hν : ∀ x,0 ≤ ν x) (y : Y) :
    0 ≤ K.push ν y := Finset.sum_nonneg (fun x _ => mul_nonneg (hν x) (K.nonnegative x y))
lemma push_mass (K : FiniteKernel X Y) (ν : X → ℝ) :
    ∑ y,K.push ν y = ∑ x,ν x*(∑ y,K.P x y) := by
  unfold push; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
lemma push_mass_le (K : FiniteKernel X Y) (ν : X → ℝ) (hν : ∀ x,0 ≤ ν x) :
    ∑ y,K.push ν y ≤ ∑ x,ν x := by
  rw [K.push_mass]
  exact Finset.sum_le_sum (fun x _ => by simpa using mul_le_mul_of_nonneg_left (K.substochastic x) (hν x))
noncomputable def power (K : FiniteKernel X X) : ℕ → FiniteKernel X X
  | 0 => identity
  | n+1 => (K.power n).comp K
end FiniteKernel

namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
noncomputable def kernel : FiniteKernel X X where
  P := C.P
  nonnegative := C.nonnegative
  substochastic := fun x => (C.stochastic x).le
lemma kernel_power_stochastic (n : ℕ) (x : X) : ∑ y,(C.kernel.power n).P x y=1 := by
  induction n with
  | zero => simp [FiniteKernel.power,FiniteKernel.identity]
  | succ n ih =>
    change (∑ y,∑ z,(C.kernel.power n).P x z*C.P z y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,C.stochastic,mul_one]
    exact ih
end

section
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance81 : Fintype X] (C : FiniteChain X)

noncomputable def pathProbability (ν : X → ℝ) (N : ℕ) (E : List X → Prop) : ℝ :=
  ∑ x,ν x*C.pathExpectation N x (fun l => if E l then 1 else 0)
end

open scoped BigOperators Classical
end FiniteChain

section SamplingObservables
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance85 : Fintype Γ] [DecidableEq Γ]
noncomputable def plainObservable (gs : List (Γ × Γ)) (g : Set Γ → ℝ) (S : Set Γ) : ℝ :=
  if PlainState gs S then g S else 0
noncomputable def defectIndicator (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) : ℝ :=
  if DefectState gs p r S then 1 else 0

abbrev PhaseObservables (gs : List (Γ × Γ)) := Option {pr // pr∈defectTypes gs} ⊕ Unit
noncomputable def phaseObservable (gs : List (Γ × Γ)) (g : Set Γ → ℝ) :
    PhaseObservables gs → Set Γ → ℝ
  | .inl none => plainObservable gs (fun _ => 1)
  | .inl (some pr) => defectIndicator gs pr.val.1 pr.val.2
  | .inr _ => plainObservable gs g
end SamplingObservables

open Set

open scoped BigOperators Classical

namespace FiniteExperiment
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance89 : Fintype X]

noncomputable def expect (K : List X → X → ℝ) : ℕ → List X → (List X → ℝ) → ℝ
  | 0,h,φ => φ h
  | t+1,h,φ => ∑ x,K h x*expect K t (h++[x]) φ
noncomputable def mass (K : List X → X → ℝ) (t : ℕ) (h : List X) : ℝ :=
  expect K t h (fun _ => 1)

noncomputable def restrict (P : List X → X → ℝ) (Good : List X → Prop) (h : List X) (x : X) : ℝ :=
  if Good (h++[x]) then P h x else 0
end FiniteExperiment
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
lemma kernel_power_action (k : ℕ) (f : X → ℝ) (x : X) :
    ∑ y,(C.kernel.power k).P x y*f y=C.iterate k f x := by
  induction k generalizing f with
  | zero => simp [FiniteKernel.power,FiniteKernel.identity]
  | succ k ih =>
    change (∑ y,(∑ z,(C.kernel.power k).P x z*C.P z y)*f y)=_
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    change (∑ z,(C.kernel.power k).P x z*C.apply f z)=_
    rw [ih]
    exact congrFun (Function.iterate_succ_apply C.apply k f).symm x
lemma kernel_power_density (k : ℕ) (x y : X) :
    (C.kernel.power k).P x y/C.π y=C.iterate k (C.pointDensity y) x := by
  rw [← C.kernel_power_action]
  simp [pointDensity,div_eq_mul_inv]
end FiniteChain

section ActualAnnealing
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance93 : Fintype Γ] [sectionInstance94 : DecidableEq Γ]

structure GoodMultipliers (gs : List (Γ × Γ)) (f : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) : Prop where
  positive : ∀ p r,0<w p r
  lower : ∀ p∈gs,∀ r∈gs,p≠r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r
  upper : ∀ p∈gs,∀ r∈gs,p≠r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r

noncomputable def empirical (H : Set Γ → ℝ) (l : List (Set Γ)) : ℝ :=
  (l.map H).sum/(l.length:ℝ)
noncomputable def learnedMultipliers (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (l : List (Set Γ)) (p r : Γ × Γ) : ℝ :=
  if p∈gs ∧ r∈gs ∧ p≠r then
    w p r*(empirical (plainObservable gs (fun _ => 1)) l/empirical (defectIndicator gs p r) l)
  else w p r
noncomputable def empiricalRatio (gs : List (Γ × Γ)) (g : Set Γ → ℝ) (l : List (Set Γ)) : ℝ :=
  empirical (plainObservable gs g) l/empirical (plainObservable gs (fun _ => 1)) l

def AccuratePhase (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (η : ℝ) (l : List (Set Γ)) : Prop :=
  ∀ j : PhaseObservables gs,
    |empirical (phaseObservable gs g j) l-chainMean gs w f (phaseObservable gs g j)| ≤
      η*chainMean gs w f (phaseObservable gs g j)
end ActualAnnealing
section WarmLift
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance102 : Fintype Γ] [sectionInstance103 : DecidableEq Γ]
noncomputable def plainLift (gs : List (Γ × Γ)) (ν : PlainIndex gs → ℝ) (S : ChainIndex gs) : ℝ :=
  if h : PlainState gs S.val then ν ⟨S,h⟩ else 0
end WarmLift
open scoped BigOperators Classical

end

section

open scoped BigOperators Classical
noncomputable def uniformAverage {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x,f x)/(Fintype.card X:ℝ)
namespace DrawTree

section
open scoped BigOperators Classical
variable {A : Type*}

def optionValue (φ : A → ℝ) : Option A → ℝ
  | none => 0
  | some a => φ a
end
open scoped BigOperators Classical
end DrawTree

section MetropolisSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance110 : Fintype Γ] [sectionInstance111 : DecidableEq Γ]
abbrev ExchangeChoice (S : Set Γ) := ↥S × ↥(Sᶜ)
def exchangedSet (S : Set Γ) (a : ExchangeChoice S) : Set Γ := insert a.2.val (S\{a.1.val})
end MetropolisSampling
section RationalSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance112 : Fintype Γ] [sectionInstance113 : DecidableEq Γ]
noncomputable def rationalMultiplier (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (S : Set Γ) : ℚ :=
  if h : ∃ p r,DefectState gs p r S then w h.choose h.choose_spec.choose else 1
noncomputable def rationalEmpirical (H : Set Γ → ℚ) (l : List (Set Γ)) : ℚ :=
  (l.map H).sum/(l.length:ℚ)
noncomputable def rationalPlain (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (S : Set Γ) : ℚ :=
  if PlainState gs S then g S else 0
noncomputable def rationalDefect (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) : ℚ :=
  if DefectState gs p r S then 1 else 0
noncomputable def rationalLearn (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (l : List (Set Γ)) (p r : Γ × Γ) : ℚ :=
  if p∈gs ∧ r∈gs ∧ p≠r then
    w p r*(rationalEmpirical (rationalPlain gs (fun _ => 1)) l/rationalEmpirical (rationalDefect gs p r) l)
  else w p r
end RationalSampling

open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

def rationalMedian (l : List ℚ) : ℚ := (l.mergeSort (· ≤ ·)).getD (l.length/2) 0

def outsideInterval (a b x : ℚ) : Bool := decide (¬(a≤x ∧ x≤b))

def repetitionCount (δ : ℚ) : ℕ := 64*(δ.den.bits.length+1)

open scoped BigOperators Classical

def sampleCount (n L : ℕ) (ε : ℚ) : ℕ := 10^14*(L+1)^3*n^14*⌈ε⁻¹⌉₊^2+1

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

end CommonBasesFPRAS

open CommonBasesFPRAS

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FactorialSignatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorial congruence for the two binary lifts

The integer-to-binary signature transfer in paper 200-02,
Lemma `lem:binary-signatures`. Coordinates with zero remaining copies
are allowed; a single remaining copy gives an invalid repeated removal.
The copy matrix is proved to be dominated by the integer form compressed
to group means. The difference is the nonnegative within-group variance.
-/

namespace ContingencyTables.FactorialSignatures

open scoped BigOperators Classical Matrix
open LinearMap (BilinForm)
open CommonBasesFPRAS

variable {G : Type*} [Fintype G] [DecidableEq G]

def removeOne (n : G → ℕ) (u : G) : G → ℕ := fun v => n v - if v = u then 1 else 0

def removeTwo (n : G → ℕ) (u v : G) : G → ℕ := removeOne (removeOne n u) v

def ValidPair (n : G → ℕ) (u v : G) : Prop :=
  0 < n u ∧ 0 < n v - if v = u then 1 else 0

omit [Fintype G] in
lemma validPair_symm (n : G → ℕ) (u v : G) : ValidPair n u v ↔ ValidPair n v u := by
  by_cases huv : u = v
  · subst v
    rfl
  · simp [ValidPair, huv, Ne.symm huv, and_comm]

omit [Fintype G] in
lemma removeTwo_comm (n : G → ℕ) (u v : G) : removeTwo n u v = removeTwo n v u := by
  funext w
  dsimp [removeTwo, removeOne]
  omega

noncomputable def integerRemovalMatrix (h : (G → ℕ) → ℝ) (n : G → ℕ) : Matrix G G ℝ :=
  fun u v => if ValidPair n u v then h (removeTwo n u v) else 0

end ContingencyTables.FactorialSignatures

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Balanced marginalization of actual integer two-removal matrices

The new pair is summed subject to its exact total M. We identify every
old, fresh and cross entry with the balanced summation theorem; thus the
signature of the marginal is derived from signatures of the actual unsummed
integer matrices, rather than assumed for a binary encoding.
-/

namespace ContingencyTables.IntegerMarginal

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures
open LinearMap (BilinForm)

variable {I : Type*} [Fintype I] [DecidableEq I]

def profile (z : I → ℕ) (a b : ℕ) : I ⊕ Bool → ℕ :=
  Sum.elim z (fun t => if t then b else a)

noncomputable def marginal (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), F (profile z j (M-j))

omit [Fintype I] in
lemma profile_removeOld (z : I → ℕ) (a b : ℕ) (i k : I) :
    removeTwo (profile z a b) (.inl i) (.inl k) = profile (removeTwo z i k) a b := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]

omit [Fintype I] in
lemma profile_removeAA (z : I → ℕ) (a b : ℕ) :
    removeTwo (profile z a b) (.inr false) (.inr false) = profile z (a-2) b := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]
  omega

omit [Fintype I] in
lemma profile_removeBB (z : I → ℕ) (a b : ℕ) :
    removeTwo (profile z a b) (.inr true) (.inr true) = profile z a (b-2) := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]
  omega

omit [Fintype I] in
lemma profile_removeAB (z : I → ℕ) (a b : ℕ) :
    removeTwo (profile z a b) (.inr false) (.inr true) = profile z (a-1) (b-1) := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]

omit [Fintype I] in
lemma profile_removeOldA (z : I → ℕ) (a b : ℕ) (i : I) :
    removeTwo (profile z a b) (.inl i) (.inr false) = profile (removeOne z i) (a-1) b := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]

omit [Fintype I] in
lemma profile_removeOldB (z : I → ℕ) (a b : ℕ) (i : I) :
    removeTwo (profile z a b) (.inl i) (.inr true) = profile (removeOne z i) a (b-1) := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]

noncomputable def old : (I → ℝ) →ₗ[ℝ] (I ⊕ Bool → ℝ) where
  toFun v := Sum.elim v (fun _ => 0)
  map_add' _ _ := by ext t; cases t <;> simp
  map_smul' _ _ := by ext t; cases t <;> simp

noncomputable def pairMatrix (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) : Matrix (I ⊕ Bool) (I ⊕ Bool) ℝ :=
  integerRemovalMatrix F (profile z j (M-j))

noncomputable def innerWeight (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) : ℝ :=
  if 0 < j ∧ j < M then F (profile z (j-1) (M-1-j)) else 0

noncomputable def cross (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) : (I → ℝ) →ₗ[ℝ] ℝ :=
  if 0 < j ∧ j ≤ M then
    (pairMatrix F M z j).toBilin' |>.flip (Pi.single (.inr false) 1) |>.comp old
  else 0

omit [Fintype I] in
lemma integerRemoval_symm (F : (I → ℕ) → ℝ) (z : I → ℕ) (i k : I) :
    integerRemovalMatrix F z i k = integerRemovalMatrix F z k i := by
  simp only [integerRemovalMatrix, validPair_symm z i k, removeTwo_comm z i k]

omit [Fintype I] in
lemma pairMatrix_aa (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (hj : j ≤ M) :
    pairMatrix F M z j (.inr false) (.inr false) = innerWeight F M z (j-1) := by
  have hv : ValidPair (profile z j (M-j)) (.inr false) (.inr false) ↔ 2 ≤ j := by
    simp [ValidPair,profile]; omega
  unfold pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeAA]
  unfold innerWeight
  by_cases h : 2 ≤ j
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    congr 1; omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

omit [Fintype I] in
lemma pairMatrix_bb (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (hj : j ≤ M) :
    pairMatrix F M z j (.inr true) (.inr true) = innerWeight F M z (j+1) := by
  have hv : ValidPair (profile z j (M-j)) (.inr true) (.inr true) ↔ j+2 ≤ M := by
    simp [ValidPair,profile]; omega
  unfold pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeBB]
  unfold innerWeight
  by_cases h : j+2 ≤ M
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    congr 1; omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

omit [Fintype I] in
lemma pairMatrix_ab (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (_hj : j ≤ M) :
    pairMatrix F M z j (.inr false) (.inr true) = innerWeight F M z j := by
  have hv : ValidPair (profile z j (M-j)) (.inr false) (.inr true) ↔ 0 < j ∧ j < M := by
    simp [ValidPair,profile]
  unfold pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeAB]
  unfold innerWeight
  split_ifs
  · congr 1; congr 1; omega
  · rfl

lemma old_single (B : Matrix (I ⊕ Bool) (I ⊕ Bool) ℝ) (v : I → ℝ) (t : Bool) :
    B.toBilin' (old v) (Pi.single (.inr t) 1) = ∑ i, v i * B (.inl i) (.inr t) := by
  simp [Matrix.toBilin'_apply, old, Fintype.sum_sum_type, Pi.single_apply]

lemma old_old (B : Matrix (I ⊕ Bool) (I ⊕ Bool) ℝ) (v w : I → ℝ) :
    B.toBilin' (old v) (old w) = (B.submatrix Sum.inl Sum.inl).toBilin' v w := by
  simp [Matrix.toBilin'_apply, old, Fintype.sum_sum_type]

lemma cross_a (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (hj : j ≤ M) (v : I → ℝ) :
    (pairMatrix F M z j).toBilin' (old v) (Pi.single (.inr false) 1) = cross F M z j v := by
  unfold cross
  by_cases h : 0 < j
  · rw [ite_eq_left ⟨h,hj⟩]; rfl
  · rw [ite_eq_right (by omega)]
    rw [old_single]
    apply Finset.sum_eq_zero
    intro i _
    have hv : ¬ValidPair (profile z j (M-j)) (.inl i) (.inr false) := by
      simp [ValidPair,profile]; omega
    simp [pairMatrix,integerRemovalMatrix,hv]

lemma cross_b (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (hj : j ≤ M) (v : I → ℝ) :
    (pairMatrix F M z j).toBilin' (old v) (Pi.single (.inr true) 1) = cross F M z (j+1) v := by
  unfold cross
  by_cases h : j < M
  · rw [ite_eq_left (by omega)]
    change _ = (pairMatrix F M z (j+1)).toBilin' (old v) (Pi.single (.inr false) 1)
    rw [old_single,old_single]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hv : ValidPair (profile z j (M-j)) (.inl i) (.inr true) ↔ 0 < z i := by
      simp [ValidPair,profile]; omega
    have hv' : ValidPair (profile z (j+1) (M-(j+1))) (.inl i) (.inr false) ↔ 0 < z i := by
      simp [ValidPair,profile]
    unfold pairMatrix integerRemovalMatrix
    rw [if_congr hv rfl rfl,if_congr hv' rfl rfl,profile_removeOldB,profile_removeOldA]
    simp only [Nat.add_sub_cancel,Nat.sub_sub]
  · rw [ite_eq_right (by omega),old_single]
    apply Finset.sum_eq_zero
    intro i _
    have hv : ¬ValidPair (profile z j (M-j)) (.inl i) (.inr true) := by
      simp [ValidPair,profile]; omega
    simp [pairMatrix,integerRemovalMatrix,hv]

omit [Fintype I] in
lemma pairMatrix_old (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (i k : I) :
    pairMatrix F M z j (.inl i) (.inl k) =
      if ValidPair z i k then F (profile (removeTwo z i k) j (M-j)) else 0 := by
  have hv : ValidPair (profile z j (M-j)) (.inl i) (.inl k) ↔ ValidPair z i k := by
    simp [ValidPair,profile]
  unfold pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl,profile_removeOld]

omit [Fintype I] in
lemma marginal_old_matrix (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) :
    integerRemovalMatrix (marginal F M) z =
      ∑ j ∈ Finset.range (M+1), (pairMatrix F M z j).submatrix Sum.inl Sum.inl := by
  ext i k
  simp only [Matrix.sum_apply,Matrix.submatrix_apply,pairMatrix_old,integerRemovalMatrix,marginal]
  split_ifs <;> simp

lemma marginal_old_block (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) :
    (integerRemovalMatrix (marginal F M) z).toBilin' =
      ∑ j ∈ Finset.range (M+1), (pairMatrix F M z j).toBilin'.compl₁₂ old old := by
  rw [marginal_old_matrix]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  exact (old_old _ v w).symm

/-- Exact balanced marginal closure for the paper's raw integer matrices. -/
theorem marginal_removal_onePositive
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) (hM : 2 ≤ M)
    (hsig : ∀ j ≤ M, OnePositiveDirection (integerRemovalMatrix F (profile z j (M-j))).toBilin')
    (hpos : ∀ j, 0 < j → j < M → 0 < F (profile z (j-1) (M-1-j))) :
    OnePositiveDirection (integerRemovalMatrix (marginal F M) z).toBilin' := by
  rw [marginal_old_block]
  apply balancedPair_sum_onePositive M hM
    (fun j => (pairMatrix F M z j).toBilin') old
    (Pi.single (.inr false) 1) (Pi.single (.inr true) 1) (cross F M z) (innerWeight F M z)
  · intro j _ x y
    exact (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y
  · exact hsig
  · simp [innerWeight]
  · simp [innerWeight]
  · simp [innerWeight]
  · intro j hj0 hjM; simp [innerWeight,hj0,hjM,hpos j hj0 hjM]
  · simp [cross]
  · simp [cross]
  · intro j hj; simpa using pairMatrix_aa F M z j hj
  · intro j hj; simpa using pairMatrix_bb F M z j hj
  · intro j hj; simpa using pairMatrix_ab F M z j hj
  · exact cross_a F M z
  · exact cross_b F M z

end ContingencyTables.IntegerMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-total, finite-box balanced marginal closure

The display and positivity hypotheses of integer marginalization follow
from the box-valid total slice. Positivity of the marginal permits induction
over every finite family of balanced pairs before the equality limit.
-/

namespace ContingencyTables.BalancedBox

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

def InBox (m z : I → ℕ) : Prop := ∀ i, z i ≤ m i

def PositiveSlice (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ) : Prop :=
  ∀ z, InBox m z → (∑ i, z i)=R → 0 < f z

def RemovalSlice (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ) : Prop :=
  ∀ z, InBox m z → (∑ i, z i)=R+2 →
    OnePositiveDirection (integerRemovalMatrix f z).toBilin'

omit [Fintype I] [DecidableEq I] in
lemma profile_inBox (m z : I → ℕ) (M a b : ℕ) (hz : InBox m z) (ha : a ≤ M) (hb : b ≤ M) :
    InBox (profile m M M) (profile z a b) := by
  intro i
  rcases i with i | (_ | _) <;> simp only [profile,Sum.elim_inl,Sum.elim_inr,ite_true, if_true]
  · exact hz i
  · exact ha
  · exact hb

omit [DecidableEq I] in
lemma profile_total (z : I → ℕ) (a b : ℕ) :
    (∑ i, profile z a b i)=(∑ i, z i)+a+b := by
  simp [profile,Fintype.sum_sum_type]
  omega

/-- One balanced pair preserves the exact box-valid integer signature. -/
theorem marginal_removal_slice (F : ((I ⊕ Bool) → ℕ) → ℝ) (m : I → ℕ) (R M : ℕ)
    (hM : 2 ≤ M) (hpos : PositiveSlice F (profile m M M) (R+M))
    (hsig : RemovalSlice F (profile m M M) (R+M)) :
    RemovalSlice (marginal F M) m R := by
  intro z hz htotal
  apply marginal_removal_onePositive F M z hM
  · intro j hj
    apply hsig _ (profile_inBox m z M j (M-j) hz hj (Nat.sub_le _ _))
    rw [profile_total,htotal]
    omega
  · intro j hj0 hjM
    apply hpos _ (profile_inBox m z M (j-1) (M-1-j) hz (by omega) (by omega))
    rw [profile_total,htotal]
    omega

omit [DecidableEq I] in
/-- The finite sum stays strictly positive on precisely its required total
slice. This is the induction input for the next balanced pair. -/
theorem marginal_positive_slice (F : ((I ⊕ Bool) → ℕ) → ℝ) (m : I → ℕ) (R M : ℕ)
    (hpos : PositiveSlice F (profile m M M) (R+M)) :
    PositiveSlice (marginal F M) m R := by
  intro z hz htotal
  unfold marginal
  apply Finset.sum_pos'
  · intro j hj
    have hjM : j ≤ M := by simpa using Finset.mem_range.mp hj
    apply le_of_lt
    apply hpos _ (profile_inBox m z M j (M-j) hz hjM (Nat.sub_le _ _))
    rw [profile_total,htotal]
    omega
  · refine ⟨0,by simp,?_⟩
    apply hpos _ (profile_inBox m z M 0 (M-0) hz (Nat.zero_le _) (by simp))
    rw [profile_total,htotal]
    omega

end ContingencyTables.BalancedBox

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All finite balanced-pair eliminations

The coordinates are the retained small coordinates followed by the actual
finite list of large-cell pairs. The recursion performs their finite
balanced sums and proves the total-slice positivity and removal signature
at every step.
-/

namespace ContingencyTables.BalancedFamily

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox

universe u

@[reducible] def Coordinates (I : Type u) : List ℕ → Type u
  | [] => I
  | _ :: Ms => Coordinates I Ms ⊕ Bool

@[reducible] instance coordinatesFintype {I : Type*} [Fintype I] (Ms : List ℕ) :
    Fintype (Coordinates I Ms) := by
  induction Ms with
  | nil => exact inferInstanceAs (Fintype I)
  | cons M Ms ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Coordinates I Ms ⊕ Bool))

@[reducible] instance coordinatesDecidableEq {I : Type*} [DecidableEq I] (Ms : List ℕ) :
    DecidableEq (Coordinates I Ms) := by
  induction Ms with
  | nil => exact inferInstanceAs (DecidableEq I)
  | cons M Ms ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Coordinates I Ms ⊕ Bool))

def bounds {I : Type*} (m : I → ℕ) : (Ms : List ℕ) → Coordinates I Ms → ℕ
  | [] => m
  | M :: Ms => profile (bounds m Ms) M M

noncomputable def eliminate {I : Type*} : (Ms : List ℕ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → ℝ
  | [], F => F
  | M :: Ms, F => eliminate Ms (marginal F M)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every actual large-cell pair has width at least two; eliminating all
of them preserves precisely the required box-valid total slice. -/
theorem eliminate_slices (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M)
    (hpos : PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : RemovalSlice F (bounds m Ms) (R+Ms.sum)) :
    PositiveSlice (eliminate Ms F) m R ∧ RemovalSlice (eliminate Ms F) m R := by
  induction Ms with
  | nil => simpa only [List.sum_nil,add_zero,eliminate,bounds] using And.intro hpos hsig
  | cons M Ms ih =>
    have htotal : R+(M::Ms).sum = (R+Ms.sum)+M := by simp only [List.sum_cons]; omega
    rw [htotal] at hpos hsig
    have hp := marginal_positive_slice F (bounds m Ms) (R+Ms.sum) M hpos
    have hs := marginal_removal_slice F (bounds m Ms) (R+Ms.sum) M
      (hwidth M (by simp)) hpos hsig
    exact ih (marginal F M) (fun N hN => hwidth N (by simp [hN])) hp hs

omit [DecidableEq I] in
/-- Only the paper's finite box and required total slice are ever read
by a balanced marginal. In particular its zero extension is harmless. -/
theorem eliminate_congr_slice (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (F f : (Coordinates I Ms → ℕ) → ℝ)
    (heq : ∀ x, InBox (bounds m Ms) x → (∑ i, x i)=R+Ms.sum → F x=f x)
    (z : I → ℕ) (hz : InBox m z) (htotal : (∑ i, z i)=R) :
    eliminate Ms F z=eliminate Ms f z := by
  induction Ms with
  | nil => exact heq z hz (by simpa using htotal)
  | cons M Ms ih =>
    apply ih (marginal F M) (marginal f M)
    intro x hx hxtotal
    apply Finset.sum_congr rfl
    intro j hj
    have hjM : j ≤ M := by simpa using Finset.mem_range.mp hj
    apply heq _ (profile_inBox (bounds m Ms) x M j (M-j) hx hjM (Nat.sub_le _ _))
    rw [profile_total,hxtotal]
    simp only [List.sum_cons]
    omega

omit [Fintype I] [DecidableEq I] in
theorem eliminate_nonnegative (Ms : List ℕ) (F : (Coordinates I Ms → ℕ) → ℝ)
    (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) : 0 ≤ eliminate Ms F z := by
  induction Ms with
  | nil => exact hF z
  | cons M Ms ih =>
    apply ih (marginal F M)
    intro x
    apply Finset.sum_nonneg
    intro j _
    exact hF (profile x j (M-j))

omit [Fintype I] [DecidableEq I] in
/-- All balanced eliminations are finite sums, so their actual values
commute with the equality-softening limit. -/
theorem eliminate_tendsto {K : Type*} {l : Filter K} (Ms : List ℕ)
    (F : K → (Coordinates I Ms → ℕ) → ℝ) (f : (Coordinates I Ms → ℕ) → ℝ)
    (hlim : ∀ z, Filter.Tendsto (fun t => F t z) l (nhds (f z))) (z : I → ℕ) :
    Filter.Tendsto (fun t => eliminate Ms (F t) z) l (nhds (eliminate Ms f z)) := by
  induction Ms with
  | nil => exact hlim z
  | cons M Ms ih =>
    apply ih (fun t => marginal (F t) M) (marginal f M)
    intro x
    unfold marginal
    apply tendsto_finsetSum
    intro j _
    exact hlim (profile x j (M-j))

end ContingencyTables.BalancedFamily

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Balanced elimination as a finite assignment sum

The recursive integer marginal equals the finite sum over the choices in
all eliminated large-cell pairs. This identifies the signature marginal
with the completion count.
-/

namespace ContingencyTables.BalancedEnumeration

open scoped BigOperators Classical
open BalancedFamily IntegerMarginal BalancedBox

@[reducible] def Assignments : List ℕ → Type
  | [] => PUnit
  | M::Ms => Assignments Ms × Fin (M+1)

@[reducible] instance assignmentsFintype (Ms : List ℕ) : Fintype (Assignments Ms) := by
  induction Ms with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons M Ms ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Assignments Ms × Fin (M+1)))

def embedding {I : Type*} : (Ms : List ℕ) → (I → ℕ) → Assignments Ms → Coordinates I Ms → ℕ
  | [],z,_ => z
  | M::Ms,z,a => profile (embedding Ms z a.1) a.2.val (M-a.2.val)

theorem eliminate_eq_sum {I : Type*} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    eliminate Ms F z=∑ a : Assignments Ms, F (embedding Ms z a) := by
  induction Ms with
  | nil => simp only [eliminate,Assignments,embedding,Fintype.sum_unique]
  | cons M Ms ih =>
    change eliminate Ms (marginal F M) z=
      ∑ a : Assignments Ms × Fin (M+1), F (profile (embedding Ms z a.1) a.2.val (M-a.2.val))
    rw [ih,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    unfold marginal
    exact (Fin.sum_univ_eq_sum_range (fun j => F (profile (embedding Ms z a) j (M-j))) (M+1)).symm

lemma embedding_inBox {I : Type*} (Ms : List ℕ) (m : I → ℕ) (z : I → ℕ)
    (hz : InBox m z) (a : Assignments Ms) : InBox (bounds m Ms) (embedding Ms z a) := by
  induction Ms with
  | nil => exact hz
  | cons M Ms ih =>
    apply profile_inBox (bounds m Ms) (embedding Ms z a.1) M a.2.val (M-a.2.val)
    · exact ih a.1
    · have ha := a.2.isLt; omega
    · exact Nat.sub_le _ _

lemma embedding_total {I : Type*} [Fintype I] (Ms : List ℕ) (z : I → ℕ)
    (a : Assignments Ms) :
    (∑ i, embedding Ms z a i)=(∑ i, z i)+Ms.sum := by
  induction Ms with
  | nil => simp only [embedding,List.sum_nil,add_zero]
  | cons M Ms ih =>
    change (∑ i, profile (embedding Ms z a.1) a.2.val (M-a.2.val) i)=_
    rw [profile_total,ih]
    have ha := a.2.isLt
    simp only [List.sum_cons]
    omega

end ContingencyTables.BalancedEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargePairEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical indexing of all balanced large-cell pairs

The recursively added pairs are identified with the actual finite cells,
and their assignments with the dependent product of the physical finite
intervals. No extra coordinate or assignment multiplicity is introduced.
-/

namespace ContingencyTables.LargePairEnumeration

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

variable {C : Type*}

@[reducible] def SmallView (small : C → Bool) := {c : C // small c=true}×Bool

@[reducible] def LargeCell (small : C → Bool) := {c : C // small c=false}

end ContingencyTables.LargePairEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalLargeProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the arbitrary enumeration from the physical large-cell sum -/

namespace ContingencyTables.PhysicalLargeProfiles

open scoped BigOperators Classical
open LargePairEnumeration

variable {C : Type*}

@[reducible] def PhysicalAssignments (small : C → Bool) (M : C → ℕ) :=
  (l : LargeCell small) → Fin (M l.val+1)

end ContingencyTables.PhysicalLargeProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_GuardMachineBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.MachineCost
open Turing

def advance {α : Type*} (f : α → Option α) (x : α) : α := (f x).getD x
def run {α : Type*} (f : α → Option α) : ℕ → α → α
  | 0,x => x
  | n+1,x => run f n (advance f x)

lemma run_add {α : Type*} (f : α → Option α) (n m : ℕ) (x : α) :
    run f (n+m) x=run f m (run f n x) := by
  induction n generalizing x with
  | zero => simp only [Nat.zero_add,run]
  | succ n ih => simpa only [Nat.succ_add,run] using ih (advance f x)

end MatchingFPRAS.MachineCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_BinaryAddition
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackAddition
open Turing MachineCost

abbrev Stacks := Fin 3 → List Bool
abbrev Store := Option Bool × Option Bool
def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs
def digit (c a b : Bool) : Bool := xor (xor c a) b
def carry (c a b : Bool) : Bool := (c && a) || (c && b) || (a && b)
lemma digit_identity (c a b : Bool) :
    (digit c a b).toNat+2*(carry c a b).toNat=c.toNat+a.toNat+b.toNat := by
  cases c <;> cases a <;> cases b <;> rfl

def addDigits (c : Bool) (A B : List Bool) : List Bool :=
  match A,B with
  | [],[] => if c then [true] else []
  | a::A,[] => digit c a false::addDigits (carry c a false) A []
  | [],b::B => digit c false b::addDigits (carry c false b) [] B
  | a::A,b::B => digit c a b::addDigits (carry c a b) A B
termination_by A.length+B.length

lemma addDigits_value (A B : List Bool) (c : Bool) :
    value (addDigits c A B)=value A+value B+c.toNat := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => cases c <;> simp [addDigits,value]
    | cons b B ih =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c false b
      simp only [Bool.toNat_false,Nat.add_zero] at h
      simp only [value]
      omega
  | cons a A ih =>
    cases B with
    | nil =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c a false
      simp only [Bool.toNat_false,Nat.add_zero] at h
      simp only [value]
      omega
    | cons b B =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c a b
      omega
lemma addDigits_length (A B : List Bool) (c : Bool) :
    (addDigits c A B).length ≤ max A.length B.length+1 := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => cases c <;> simp [addDigits]
    | cons b B ih =>
      rw [addDigits,List.length_cons]
      have h:=ih (carry c false b)
      simp only [List.length_nil,Nat.zero_max,List.length_cons] at h ⊢
      omega
  | cons a A ih =>
    cases B with
    | nil =>
      rw [addDigits,List.length_cons]
      have h:=ih [] (carry c a false)
      simp only [List.length_nil,Nat.max_zero,List.length_cons] at h ⊢
      omega
    | cons b B =>
      rw [addDigits,List.length_cons]
      have h:=ih B (carry c a b)
      simp only [List.length_cons]
      omega

def program (c : Bool) : TM2.Stmt (fun _ : Fin 3=>Bool) Bool Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.branch (fun _=>c) (.push 2 (fun _=>true) (.load (fun _=>default) .halt))
        (.load (fun _=>default) .halt))
      (.push 2 (fun v=>digit c (v.1.getD false) (v.2.getD false))
        (.goto (fun v=>carry c (v.1.getD false) (v.2.getD false))))))
def stackData (A B L : List Bool) : Stacks := ![A,B,L]
@[simp] lemma stackData_zero (A B L : List Bool) : stackData A B L 0=A := rfl
@[simp] lemma stackData_one (A B L : List Bool) : stackData A B L 1=B := rfl
@[simp] lemma stackData_two (A B L : List Bool) : stackData A B L 2=L := rfl
def cfg (c : Option Bool) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Bool Store := ⟨c,v,stackData A B L⟩
lemma update_zero (A B L X : List Bool) :
    Function.update (stackData A B L) 0 X=stackData X B L := by
  funext i
  fin_cases i <;> simp [stackData]
lemma update_one (A B L X : List Bool) :
    Function.update (stackData A B L) 1 X=stackData A X L := by
  funext i
  fin_cases i <;> simp [stackData]
lemma update_two (A B L X : List Bool) :
    Function.update (stackData A B L) 2 X=stackData A B X := by
  funext i
  fin_cases i <;> simp [stackData]
lemma step_empty (c : Bool) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=
      cfg none [] [] ((addDigits c [] []).reverse++L) default := by
  cases c <;> simp [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two,addDigits]
lemma step_digits (c : Bool) (A B L : List Bool) (v : Store)
    (h : A≠[] ∨ B≠[]) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (carry c (A.headD false) (B.headD false))) A.tail B.tail
        (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two]
lemma addDigits_step (c : Bool) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    addDigits c A B=digit c (A.headD false) (B.headD false)::
      addDigits (carry c (A.headD false) (B.headD false)) A.tail B.tail := by
  cases A <;> cases B <;> simp_all [addDigits]

theorem run_addition (A B L : List Bool) (c : Bool) (v : Store) :
    ∃ t ≤ A.length+B.length+1,
      MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] ((addDigits c A B).reverse++L) default := by
  have aux : ∀ n (A B : List Bool), A.length+B.length=n →
      ∀ (c : Bool) (L : List Bool) (v : Store),
      ∃ t ≤ A.length+B.length+1,
        MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
          cfg none [] [] ((addDigits c A B).reverse++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        exact ⟨1,by simp,step_empty c L v⟩
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (carry c (A.headD false) (B.headD false))
          (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,addDigits_step c A B hne]
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  exact aux _ A B rfl c L v
lemma value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [value,ih]
    cases b <;> simp [Nat.bit,Bool.toNat]
    omega

lemma addition_numerals (m n : ℕ) : value (addDigits false m.bits n.bits)=m+n := by
  simp only [addDigits_value,value_bits,Bool.toNat_false,Nat.add_zero]
end MatchingFPRAS.StackAddition

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_BinaryCompare
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackCompare
open Turing MachineCost StackAddition

def updateOrder (c : Ordering) (a b : Bool) : Ordering :=
  if a=b then c else if a then .gt else .lt

def compareDigits (c : Ordering) (A B : List Bool) : Ordering :=
  match A,B with
  | [],[] => c
  | a::A,[] => compareDigits (updateOrder c a false) A []
  | [],b::B => compareDigits (updateOrder c false b) [] B
  | a::A,b::B => compareDigits (updateOrder c a b) A B
termination_by A.length+B.length

def result (c : Ordering) (m n : ℕ) : Ordering := if m=n then c else compare m n
lemma result_digits (c : Ordering) (a b : Bool) (m n : ℕ) :
    result (updateOrder c a b) m n=result c (a.toNat+2*m) (b.toNat+2*n) := by
  rcases lt_trichotomy m n with h|h|h
  · have hb : a.toNat+2*m < b.toNat+2*n := by
      cases a <;> cases b <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
    simp [result,ne_of_lt h,ne_of_lt hb,compare_lt_iff_lt.mpr h,compare_lt_iff_lt.mpr hb]
  · subst n
    cases a <;> cases b <;> cases c <;>
      simp [result,updateOrder,eq_comm]
    all_goals first
    | exact (compare_lt_iff_lt.mpr (by omega)).symm
    | exact (compare_gt_iff_gt.mpr (by omega)).symm
  · have hb : b.toNat+2*n < a.toNat+2*m := by
      cases a <;> cases b <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
    simp [result,ne_of_gt h,ne_of_gt hb,compare_gt_iff_gt.mpr h,compare_gt_iff_gt.mpr hb]
lemma compareDigits_result (A B : List Bool) (c : Ordering) :
    compareDigits c A B=result c (value A) (value B) := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [compareDigits,result,value]
    | cons b B ih =>
      rw [compareDigits,ih]
      simpa only [value,Bool.toNat_false,Nat.zero_add,Nat.mul_zero] using result_digits c false b 0 (value B)
  | cons a A ih =>
    cases B with
    | nil =>
      rw [compareDigits,ih]
      simpa only [value,Bool.toNat_false,Nat.zero_add,Nat.mul_zero,Nat.add_zero] using result_digits c a false (value A) 0
    | cons b B =>
      rw [compareDigits,ih]
      exact result_digits c a b (value A) (value B)
lemma compares_values (A B : List Bool) :
    compareDigits .eq A B=compare (value A) (value B) := by
  rw [compareDigits_result]
  unfold result
  split_ifs with h
  · simp [h]
  · rfl
def flags (c : Ordering) : List Bool := [decide (c=.lt),decide (c=.gt)]
def program (c : Ordering) : TM2.Stmt (fun _ : Fin 3=>Bool) Ordering Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.push 2 (fun _=>decide (c=.gt)) (.push 2 (fun _=>decide (c=.lt))
         (.load (fun _=>default) .halt)))
      (.goto (fun v=>updateOrder c (v.1.getD false) (v.2.getD false)))))
def cfg (c : Option Ordering) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Ordering Store := ⟨c,v,stackData A B L⟩
lemma step_empty (c : Ordering) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=
      cfg none [] [] (flags c++L) default := by
  cases c <;> simp [advance,TM2.step,program,TM2.stepAux,cfg,flags,
    update_zero,update_one,update_two]
lemma step_digits (c : Ordering) (A B L : List Bool) (v : Store)
    (h : A≠[] ∨ B≠[]) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (updateOrder c (A.headD false) (B.headD false))) A.tail B.tail L (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two,List.headD]
lemma compareDigits_step (c : Ordering) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    compareDigits c A B=
      compareDigits (updateOrder c (A.headD false) (B.headD false)) A.tail B.tail := by
  cases A <;> cases B <;> simp_all [compareDigits,List.headD]
theorem run_comparison (A B L : List Bool) (c : Ordering) (v : Store) :
    ∃ t ≤ A.length+B.length+1,
      MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] (flags (compareDigits c A B)++L) default := by
  have aux : ∀ n (A B : List Bool), A.length+B.length=n →
      ∀ (c : Ordering) (L : List Bool) (v : Store),
      ∃ t ≤ A.length+B.length+1,
        MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
          cfg none [] [] (flags (compareDigits c A B)++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        refine ⟨1,by simp,?_⟩
        simpa only [MachineCost.run,compareDigits] using step_empty c L v
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (updateOrder c (A.headD false) (B.headD false)) L (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,compareDigits_step c A B hne]
  exact aux _ A B rfl c L v
end MatchingFPRAS.StackCompare

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_ArithmeticSize
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackComposition
open Turing MachineCost

variable {K Λ P σ : Type*} {Γ : K → Type*} [DecidableEq K]
def relabel (f : Λ → P) (h : Option P) : TM2.Stmt Γ Λ σ → TM2.Stmt Γ P σ
  | .push k a q => .push k a (relabel f h q)
  | .peek k a q => .peek k a (relabel f h q)
  | .pop k a q => .pop k a (relabel f h q)
  | .load a q => .load a (relabel f h q)
  | .branch p q r => .branch p (relabel f h q) (relabel f h r)
  | .goto l => .goto (fun a=>f (l a))
  | .halt => match h with | none=>.halt | some k=>.goto (fun _=>k)
def mapCfg (f : Λ → P) (h : Option P) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ P σ :=
  ⟨c.l.bind (fun l=>some (f l)) |>.or h,c.var,c.stk⟩
omit [DecidableEq K] in
lemma mapCfg_some (f : Λ → P) (h : Option P) (l : Λ) (v : σ) (S : ∀ k,List (Γ k)) :
    mapCfg f h ⟨some l,v,S⟩=⟨some (f l),v,S⟩ := rfl
lemma relabel_eval (f : Λ → P) (h : Option P) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k,List (Γ k)) :
    TM2.stepAux (relabel f h q) v S=mapCfg f h (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k a q ih => exact ih v _
  | peek k a q ih => exact ih _ S
  | pop k a q ih => exact ih _ _
  | load a q ih => exact ih (a v) S
  | branch p q r ihq ihr =>
    cases hp:p v <;> simp only [relabel,TM2.stepAux,hp,Bool.cond_false,Bool.cond_true] <;>
      first | apply ihr | apply ihq
  | goto l => rfl
  | halt => cases h <;> rfl
lemma run_halted (M : Λ → TM2.Stmt Γ Λ σ) (n : ℕ)
    (v : σ) (S : ∀ k,List (Γ k)) :
    MachineCost.run (TM2.step M) n ⟨none,v,S⟩=⟨none,v,S⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [MachineCost.run,advance,TM2.step,Option.getD_none] using ih
lemma run_relabel_to_halt (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ)
    (f : Λ → P) (h : Option P) (hN : ∀ l,N (f l)=relabel f h (M l))
    (n : ℕ) (c : TM2.Cfg Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (he : MachineCost.run (TM2.step M) n c=⟨none,v,S⟩) :
    ∃ k≤n,MachineCost.run (TM2.step N) k (mapCfg f h c)=⟨h,v,S⟩ := by
  induction n generalizing c with
  | zero =>
    have hc : c=⟨none,v,S⟩:=he
    subst c
    exact ⟨0,le_rfl,rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v',S'⟩
    cases l with
    | none =>
      rw [run_halted] at he
      cases he
      exact ⟨0,Nat.zero_le _,rfl⟩
    | some l =>
      have he' : MachineCost.run (TM2.step M) n (TM2.stepAux (M l) v' S')=⟨none,v,S⟩ := he
      obtain ⟨k,hk,hh⟩:=ih _ he'
      refine ⟨k+1,by omega,?_⟩
      rw [MachineCost.run,mapCfg_some]
      have hs : advance (TM2.step N) ⟨some (f l),v',S'⟩=
          mapCfg f h (TM2.stepAux (M l) v' S') := by
        simp only [advance,TM2.step,Option.getD_some,hN,relabel_eval]
      rw [hs,hh]
variable [Inhabited Λ] [Inhabited P]
def sequence (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ) :
    Λ⊕P → TM2.Stmt Γ (Λ⊕P) σ
  | .inl l => relabel Sum.inl (some (Sum.inr default)) (M l)
  | .inr k => relabel Sum.inr none (N k)
omit [Inhabited Λ] in
lemma sequence_run (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ)
    (c : TM2.Cfg Γ Λ σ) (m n : ℕ) (v v' : σ) (S S' : ∀ k,List (Γ k))
    (hM : MachineCost.run (TM2.step M) m c=⟨none,v,S⟩)
    (hN : MachineCost.run (TM2.step N) n ⟨some default,v,S⟩=⟨none,v',S'⟩) :
    ∃ k ≤ m+n,MachineCost.run (TM2.step (sequence M N)) k
      (mapCfg Sum.inl (some (Sum.inr default)) c)=⟨none,v',S'⟩ := by
  obtain ⟨i,hi,hei⟩:=run_relabel_to_halt M (sequence M N) Sum.inl
    (some (Sum.inr default)) (fun _=>rfl) m c v S hM
  obtain ⟨j,hj,hej⟩:=run_relabel_to_halt N (sequence M N) Sum.inr
    none (fun _=>rfl) n ⟨some default,v,S⟩ v' S' hN
  refine ⟨i+j,by omega,?_⟩
  rw [run_add,hei]
  exact hej

open Turing MachineCost

end MatchingFPRAS.StackComposition

namespace MatchingFPRAS.StackReverse
open Turing MachineCost StackAddition

abbrev S := Option Bool
abbrev Γ := fun _ : Fin 3 => Bool
def program : Unit → TM2.Stmt Γ Unit S := fun _ =>
  .pop 0 (fun _ a=>a)
    (.branch Option.isNone (.load (fun _=>none) .halt)
      (.push 1 (fun v=>v.getD false) (.goto (fun _=>()))))
def cfg (l : Option Unit) (A B C : List Bool) (v : S) : TM2.Cfg Γ Unit S :=
  ⟨l,v,stackData A B C⟩
lemma next_empty (B C : List Bool) (v : S) :
    advance (TM2.step program) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero]
lemma next_cons (a : Bool) (A B C : List Bool) (v : S) :
    advance (TM2.step program) (cfg (some ()) (a::A) B C v)=
      cfg (some ()) A (a::B) C (some a) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one]
theorem run_reverse (A B C : List Bool) (v : S) :
    MachineCost.run (TM2.step program) (A.length+1) (cfg (some ()) A B C v)=
      cfg none [] (A.reverse++B) C none := by
  induction A generalizing B v with
  | nil => simpa only [List.length_nil,List.reverse_nil,List.nil_append,MachineCost.run] using next_empty B C v
  | cons a A ih =>
    rw [List.length_cons,show A.length+1+1=(A.length+1)+1 by rfl,MachineCost.run,next_cons,ih]
    simp [List.reverse_cons,List.append_assoc]
end MatchingFPRAS.StackReverse

namespace MatchingFPRAS.ForwardAddition
open Turing MachineCost StackAddition

local instance initialControl : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
abbrev Γ := fun _ : Fin 3 => Bool
def reverseProgram : Unit → TM2.Stmt Γ Unit Store := fun _ =>
  .pop 2 (fun v a=>(a,v.2))
    (.branch (fun v=>v.1.isNone) (.load (fun _=>default) .halt)
      (.push 0 (fun v=>v.1.getD false) (.goto (fun _=>()))))
def rcfg (l : Option Unit) (A B C : List Bool) (v : Store) : TM2.Cfg Γ Unit Store :=
  ⟨l,v,stackData A B C⟩
lemma next_empty (A B : List Bool) (v : Store) :
    advance (TM2.step reverseProgram) (rcfg (some ()) A B [] v)=rcfg none A B [] default := by
  simp [advance,TM2.step,reverseProgram,TM2.stepAux,rcfg,update_two]
lemma next_cons (a : Bool) (A B C : List Bool) (v : Store) :
    advance (TM2.step reverseProgram) (rcfg (some ()) A B (a::C) v)=
      rcfg (some ()) (a::A) B C (some a,v.2) := by
  simp [advance,TM2.step,reverseProgram,TM2.stepAux,rcfg,update_zero,update_two]
lemma run_reverse (A B C : List Bool) (v : Store) :
    MachineCost.run (TM2.step reverseProgram) (C.length+1) (rcfg (some ()) A B C v)=
      rcfg none (C.reverse++A) B [] default := by
  induction C generalizing A v with
  | nil => simpa only [List.length_nil,List.reverse_nil,List.nil_append,MachineCost.run] using next_empty A B v
  | cons c C ih =>
    rw [List.length_cons,MachineCost.run,next_cons,ih]
    simp [List.reverse_cons,List.append_assoc]
def program : Bool⊕Unit → TM2.Stmt Γ (Bool⊕Unit) Store :=
  StackComposition.sequence StackAddition.program reverseProgram
lemma run_add (A B : List Bool) :
    ∃ k≤2*(A.length+B.length)+3,
      MachineCost.run (TM2.step program) k ⟨some default,default,stackData A B []⟩=
        ⟨none,default,stackData (addDigits false A B) [] []⟩ := by
  obtain ⟨n,hn,he⟩:=run_addition A B [] false default
  have he' : MachineCost.run (TM2.step StackAddition.program) n
      (cfg (some false) A B [] default)=cfg none [] [] (addDigits false A B).reverse default := by
    simpa only [List.append_nil] using he
  have hr := run_reverse [] [] (addDigits false A B).reverse default
  have hr' : MachineCost.run (TM2.step reverseProgram) ((addDigits false A B).length+1)
      ⟨some default,default,stackData [] [] (addDigits false A B).reverse⟩=
      ⟨none,default,stackData (addDigits false A B) [] []⟩ := by
    simpa only [rcfg,List.length_reverse,List.reverse_reverse,List.append_nil] using hr
  obtain ⟨k,hk,hkrun⟩:=StackComposition.sequence_run StackAddition.program reverseProgram
    (cfg (some false) A B [] default) n ((addDigits false A B).length+1)
    (default : Store) (default : Store) (stackData [] [] (addDigits false A B).reverse)
      (stackData (addDigits false A B) [] []) he' hr'
  refine ⟨k,?_,?_⟩
  · have hl:=addDigits_length A B false
    omega
  · exact hkrun
end MatchingFPRAS.ForwardAddition

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_StackEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackEmbedding
open Turing MachineCost

variable {K J α Λ σ τ : Type*} [DecidableEq K] [DecidableEq J]
open scoped Classical

noncomputable def extend (e : K ↪ J) (S : K → List α) (R : J → List α) (j : J) : List α :=
  if h : ∃ k,e k=j then S (Classical.choose h) else R j
omit [DecidableEq K] [DecidableEq J] in
@[simp] lemma extend_on (e : K ↪ J) (S : K → List α) (R : J → List α) (k : K) :
    extend e S R (e k)=S k := by
  have h : ∃ l,e l=e k := ⟨k,rfl⟩
  rw [extend,dite_eq_left h,e.injective (Classical.choose_spec h)]
omit [DecidableEq K] [DecidableEq J] in
lemma extend_off (e : K ↪ J) (S : K → List α) (R : J → List α) (j : J)
    (h : ¬∃ k,e k=j) : extend e S R j=R j := by rw [extend,dite_eq_right h]
lemma extend_update (e : K ↪ J) (S : K → List α) (R : J → List α) (k : K) (w : List α) :
    Function.update (extend e S R) (e k) w=extend e (Function.update S k w) R := by
  funext j
  by_cases h : ∃ l,e l=j
  · obtain ⟨l,rfl⟩:=h
    by_cases hl : l=k
    · subst l; simp
    · have hne : e l≠e k := fun h=>hl (e.injective h)
      simp [Function.update_of_ne hne,Function.update_of_ne hl]
  · have hne : j≠e k := fun h'=>h ⟨k,h'.symm⟩
    rw [Function.update_of_ne hne,extend_off e _ _ j h,extend_off e _ _ j h]

end MatchingFPRAS.StackEmbedding

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_StackLens
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackLens
open Turing MachineCost StackEmbedding

structure Lens (σ τ : Type*) where
  get : τ → σ
  put : τ → σ → τ
  get_put : ∀ v s,get (put v s)=s
  put_get : ∀ v,put v (get v)=v
  put_put : ∀ v s t,put (put v s) t=put v t

def Lens.identity (σ : Type*) : Lens σ σ :=
  ⟨id,fun _ s=>s,fun _ _=>rfl,fun _=>rfl,fun _ _ _=>rfl⟩
variable {K J α Λ σ τ : Type*} [DecidableEq K] [DecidableEq J]

def stmt (e : K ↪ J) (L : Lens σ τ) :
    TM2.Stmt (fun _ : K=>α) Λ σ → TM2.Stmt (fun _ : J=>α) Λ τ
  | .push k a q => .push (e k) (fun v=>a (L.get v)) (stmt e L q)
  | .peek k a q => .peek (e k) (fun v x=>L.put v (a (L.get v) x)) (stmt e L q)
  | .pop k a q => .pop (e k) (fun v x=>L.put v (a (L.get v) x)) (stmt e L q)
  | .load a q => .load (fun v=>L.put v (a (L.get v))) (stmt e L q)
  | .branch p q r => .branch (fun v=>p (L.get v)) (stmt e L q) (stmt e L r)
  | .goto l => .goto (fun v=>l (L.get v))
  | .halt => .halt
noncomputable def cfg (e : K ↪ J) (L : Lens σ τ) (R : J → List α) (u : τ)
    (c : TM2.Cfg (fun _ : K=>α) Λ σ) : TM2.Cfg (fun _ : J=>α) Λ τ :=
  ⟨c.l,L.put u c.var,extend e c.stk R⟩
lemma stmt_eval (e : K ↪ J) (L : Lens σ τ) (R : J → List α) (u : τ)
    (q : TM2.Stmt (fun _ : K=>α) Λ σ) (v : σ) (S : K → List α) :
    TM2.stepAux (stmt e L q) (L.put u v) (extend e S R)=
      cfg e L R u (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,extend_on,extend_update] using ih v (Function.update S k (a v::S k))
  | peek k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,L.put_put,extend_on] using ih (a v (S k).head?) S
  | pop k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,L.put_put,extend_on,extend_update] using ih (a v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => simpa only [stmt,TM2.stepAux,L.get_put,L.put_put] using ih (a v) S
  | branch p q r ihq ihr =>
    cases h : p v <;> simp only [stmt,TM2.stepAux,L.get_put,h,Bool.cond_false,Bool.cond_true] <;>
      first | apply ihr | apply ihq
  | goto l => simp only [stmt,TM2.stepAux,cfg,L.get_put]
  | halt => rfl
def program (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ) :=
  fun l=>stmt e L (M l)
lemma advance_cfg (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ)
    (R : J → List α) (u : τ) (c : TM2.Cfg (fun _ : K=>α) Λ σ) :
    advance (TM2.step (program e L M)) (cfg e L R u c)=cfg e L R u (advance (TM2.step M) c) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stmt_eval e L R u (M l) v S

theorem run_cfg (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ)
    (R : J → List α) (u : τ) (n : ℕ) (c : TM2.Cfg (fun _ : K=>α) Λ σ) :
    MachineCost.run (TM2.step (program e L M)) n (cfg e L R u c)=
      cfg e L R u (MachineCost.run (TM2.step M) n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [MachineCost.run,advance_cfg,ih,MachineCost.run]
end MatchingFPRAS.StackLens

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeTransfer
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
inductive Data where
  | nil
  | cons (head tail : Data)
  deriving DecidableEq, Inhabited
open Data

def encode : Data → List Bool
  | .nil => [false]
  | .cons a b => true::(encode a++encode b)
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeTransfer
open Turing MachineCost TreeData

abbrev Store := Option Bool
abbrev Stacks := Fin 3 → List Bool
def program : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .peek 2 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.pop 2 (fun v _=>v) (.pop 0 (fun _ b=>b)
      (.push 1 (fun v=>v.getD false) (.branch (fun v=>v.getD false)
        (.push 2 (fun _=>false) (.push 2 (fun _=>false) (.goto (fun _=>()))))
        (.goto (fun _=>())))))))
def stackData (A B D : List Bool) : Stacks := ![A,B,D]
def cfg (l : Option Unit) (A B D : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Unit Store := ⟨l,v,stackData A B D⟩
@[simp] lemma stacks_zero (A B D : List Bool) : stackData A B D 0=A := rfl
@[simp] lemma stacks_one (A B D : List Bool) : stackData A B D 1=B := rfl
@[simp] lemma stacks_two (A B D : List Bool) : stackData A B D 2=D := rfl
lemma update_zero (A B D X : List Bool) : Function.update (stackData A B D) 0 X=stackData X B D := by
  funext i; fin_cases i <;> simp [stackData]
lemma update_one (A B D X : List Bool) : Function.update (stackData A B D) 1 X=stackData A X D := by
  funext i; fin_cases i <;> simp [stackData]
lemma update_two (A B D X : List Bool) : Function.update (stackData A B D) 2 X=stackData A B X := by
  funext i; fin_cases i <;> simp [stackData]
lemma step_nil (A B D : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) (false::A) B (false::D) v)=
      cfg (some ()) A (false::B) D (some false) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one,update_two]
lemma step_cons (A B D : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) (true::A) B (false::D) v)=
      cfg (some ()) A (true::B) (false::false::D) (some true) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one,update_two]
lemma step_stop (A B : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) A B [] v)=cfg none A B [] none := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg]

theorem run_tree (x : Data) (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step program) (encode x).length
      (cfg (some ()) (encode x++A) B (false::D) v)=
      cfg (some ()) A ((encode x).reverse++B) D (some false) := by
  induction x generalizing A B D v with
  | nil => simpa [encode,MachineCost.run] using step_nil A B D v
  | cons x y ihx ihy =>
    simp only [encode,List.length_cons,List.length_append,List.cons_append]
    rw [MachineCost.run,step_cons]
    rw [show (encode x++encode y)++A=encode x++(encode y++A) by simp only [List.append_assoc]]
    rw [run_add,ihx,ihy]
    simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]

theorem run_transfer (x : Data) (A B : List Bool) (v : Store) :
    MachineCost.run (TM2.step program) ((encode x).length+1)
      (cfg (some ()) (encode x++A) B [false] v)=
      cfg none A ((encode x).reverse++B) [] none := by
  rw [run_add,run_tree]
  exact step_stop A ((encode x).reverse++B) (some false)
end MatchingFPRAS.TreeTransfer

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_WordOps
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.WordOps
open Turing MachineCost TreeTransfer

def duplicate : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .pop 0 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.push 1 (fun v=>v.getD false) (.push 2 (fun v=>v.getD false) (.goto (fun _=>())))))
lemma duplicate_nil (B D : List Bool) (v : Store) :
    advance (TM2.step duplicate) (cfg (some ()) [] B D v)=cfg none [] B D none := by
  simp [advance,TM2.step,duplicate,TM2.stepAux,cfg,update_zero]
lemma duplicate_cons (b : Bool) (A B D : List Bool) (v : Store) :
    advance (TM2.step duplicate) (cfg (some ()) (b::A) B D v)=
      cfg (some ()) A (b::B) (b::D) (some b) := by
  simp [advance,TM2.step,duplicate,TM2.stepAux,cfg,update_zero,update_one,update_two]
theorem run_duplicate (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step duplicate) (A.length+1) (cfg (some ()) A B D v)=
      cfg none [] (A.reverse++B) (A.reverse++D) none := by
  induction A generalizing B D v with
  | nil => simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append,MachineCost.run] using duplicate_nil B D v
  | cons b A ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,duplicate_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

def clear : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .pop 0 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt) (.goto (fun _=>())))
lemma clear_nil (B D : List Bool) (v : Store) :
    advance (TM2.step clear) (cfg (some ()) [] B D v)=cfg none [] B D none := by
  simp [advance,TM2.step,clear,TM2.stepAux,cfg,update_zero]
lemma clear_cons (b : Bool) (A B D : List Bool) (v : Store) :
    advance (TM2.step clear) (cfg (some ()) (b::A) B D v)=cfg (some ()) A B D (some b) := by
  simp [advance,TM2.step,clear,TM2.stepAux,cfg,update_zero]
theorem run_clear (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step clear) (A.length+1) (cfg (some ()) A B D v)=cfg none [] B D none := by
  induction A generalizing v with
  | nil => exact clear_nil B D v
  | cons b A ih => rw [List.length_cons,Nat.add_right_comm,MachineCost.run,clear_cons,ih]
end MatchingFPRAS.WordOps

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_RegisterProc
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing MachineCost

abbrev Store := Option Bool
abbrev Stack (K : Type) := K → List Bool
structure Proc (K : Type) where
  Label : Type
  [labels : Fintype Label]
  [entry : Inhabited Label]
  code : Label → TM2.Stmt (fun _ : K=>Bool) Label Store
attribute [instance] Proc.labels Proc.entry
variable {K : Type} [DecidableEq K]

def Exec (P : Proc K) (S T : Stack K) (bound : ℕ) : Prop :=
  ∃ n≤bound,MachineCost.run (TM2.step P.code) n ⟨some default,none,S⟩=⟨none,none,T⟩
lemma Exec.mono {P : Proc K} {S T : Stack K} {n m : ℕ}
    (h : Exec P S T n) (hn : n ≤ m) : Exec P S T m := by
  obtain ⟨k,hk,he⟩:=h; exact ⟨k,hk.trans hn,he⟩

def seq (P Q : Proc K) : Proc K :=
  { Label := P.Label ⊕ Q.Label
    entry := ⟨Sum.inl default⟩
    code := StackComposition.sequence P.code Q.code }
lemma Exec.seq {P Q : Proc K} {S T U : Stack K} {n m : ℕ}
    (hP : Exec P S T n) (hQ : Exec Q T U m) : Exec (seq P Q) S U (n+m) := by
  obtain ⟨i,hi,he⟩:=hP
  obtain ⟨j,hj,hf⟩:=hQ
  obtain ⟨k,hk,hg⟩:=StackComposition.sequence_run P.code Q.code
    ⟨some default,none,S⟩ i j none none T U he hf
  exact ⟨k,hk.trans (Nat.add_le_add hi hj),hg⟩

def atom (s : TM2.Stmt (fun _ : K=>Bool) Unit Store) : Proc K := ⟨Unit,fun _=>s⟩
lemma exec_atom (s : TM2.Stmt (fun _ : K=>Bool) Unit Store) (S T : Stack K)
    (h : TM2.stepAux s none S=⟨none,none,T⟩) : Exec (atom s) S T 1 := ⟨1,le_rfl,h⟩

def reindex (P : Proc (Fin 3)) (e : Fin 3 ↪ K) : Proc K :=
  ⟨P.Label,StackLens.program e (StackLens.Lens.identity Store) P.code⟩
noncomputable def frame (e : Fin 3 ↪ K) (A B C : List Bool) (S : Stack K) : Stack K :=
  StackEmbedding.extend e ![A,B,C] S
lemma exec_reindex (P : Proc (Fin 3)) (e : Fin 3 ↪ K) (S : Stack K)
    (A B C A' B' C' : List Bool) (n : ℕ)
    (h : Exec P ![A,B,C] ![A',B',C'] n) :
    Exec (reindex P e) (frame e A B C S) (frame e A' B' C' S) n := by
  obtain ⟨k,hk,he⟩:=h
  refine ⟨k,hk,?_⟩
  have hh := StackLens.run_cfg e (StackLens.Lens.identity Store) P.code S none k
    ⟨some default,none,![A,B,C]⟩
  rw [he] at hh
  exact hh

def triple (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) : Fin 3 ↪ K :=
  ⟨![a,b,c],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
omit [DecidableEq K] in
@[simp] lemma triple_zero (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 0=a := rfl
omit [DecidableEq K] in
@[simp] lemma triple_one (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 1=b := rfl
omit [DecidableEq K] in
@[simp] lemma triple_two (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 2=c := rfl

def put3 (S : Stack K) (a b c : K) (A B C : List Bool) : Stack K :=
  Function.update (Function.update (Function.update S a A) b B) c C
lemma frame_triple (S : Stack K) (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (A B C : List Bool) : frame (triple a b c hab hac hbc) A B C S=put3 S a b c A B C := by
  funext j
  by_cases hja : j=a
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 0
    simpa [frame,put3,hab,hac,hbc,hab.symm,hac.symm,hbc.symm] using hh
  by_cases hjb : j=b
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 1
    simpa [frame,put3,hab,hac,hbc,hab.symm,hac.symm,hbc.symm] using hh
  by_cases hjc : j=c
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 2
    simpa [frame,put3] using hh
  have he : ¬∃ k,triple a b c hab hac hbc k=j := by
    rintro ⟨k,hk⟩; fin_cases k <;> simp_all
  rw [frame,StackEmbedding.extend_off _ _ _ j he]
  simp [put3,hja,hjb,hjc]
lemma put3_same (S : Stack K) (a b c : K) (_ : a≠b) (hac : a≠c) (hbc : b≠c) :
    put3 S a b c (S a) (S b) (S c)=S := by
  funext j
  by_cases hja : j=a <;> by_cases hjb : j=b <;> by_cases hjc : j=c <;> simp_all [put3]

def clearRaw : Proc (Fin 3) := ⟨Unit,WordOps.clear⟩
def reverseRaw : Proc (Fin 3) := ⟨Unit,StackReverse.program⟩
def duplicateRaw : Proc (Fin 3) := ⟨Unit,WordOps.duplicate⟩
def transferRaw : Proc (Fin 3) := ⟨Unit,TreeTransfer.program⟩
lemma clearRaw_exec (A B C : List Bool) :
    Exec clearRaw ![A,B,C] ![[],B,C] (A.length+1) :=
  ⟨_,le_rfl,WordOps.run_clear A B C none⟩
lemma reverseRaw_exec (A B C : List Bool) :
    Exec reverseRaw ![A,B,C] ![[],A.reverse++B,C] (A.length+1) :=
  ⟨_,le_rfl,StackReverse.run_reverse A B C none⟩
lemma duplicateRaw_exec (A B C : List Bool) :
    Exec duplicateRaw ![A,B,C] ![[],A.reverse++B,A.reverse++C] (A.length+1) :=
  ⟨_,le_rfl,WordOps.run_duplicate A B C none⟩
lemma transferRaw_exec (x : TreeData.Data) (A B : List Bool) :
    Exec transferRaw ![TreeData.encode x++A,B,[false]] ![A,(TreeData.encode x).reverse++B,[]]
      ((TreeData.encode x).length+1) :=
  ⟨_,le_rfl,TreeTransfer.run_transfer x A B none⟩
end MatchingFPRAS.RegisterProc

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_RegisterTree
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing MachineCost TreeData

lemma exec_perm (P : Proc (Fin 3)) (e : Fin 3 ≃ Fin 3) (S T : Stack (Fin 3))
    (n : ℕ) (h : Exec P (S ∘ e) (T ∘ e) n) : Exec (reindex P e.toEmbedding) S T n := by
  have hf (S : Stack (Fin 3)) : frame e.toEmbedding (S (e 0)) (S (e 1)) (S (e 2)) S=S := by
    funext j
    obtain ⟨i,rfl⟩:=e.surjective j
    have hh:=StackEmbedding.extend_on e.toEmbedding ![S (e 0),S (e 1),S (e 2)] S i
    fin_cases i <;> exact hh
  have hs : S ∘ e=![S (e 0),S (e 1),S (e 2)] := by funext i; fin_cases i <;> rfl
  have ht : T ∘ e=![T (e 0),T (e 1),T (e 2)] := by funext i; fin_cases i <;> rfl
  rw [hs,ht] at h
  have hh:=exec_reindex P e.toEmbedding S _ _ _ _ _ _ n h
  rw [hf] at hh
  have hf' : frame e.toEmbedding (T (e 0)) (T (e 1)) (T (e 2)) S=T := by
    funext j
    obtain ⟨i,rfl⟩:=e.surjective j
    have he:=StackEmbedding.extend_on e.toEmbedding ![T (e 0),T (e 1),T (e 2)] S i
    fin_cases i <;> exact he
  rwa [hf'] at hh

def p02 : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
def p01 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
def p12 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
def p201 : Fin 3 ≃ Fin 3 := p02.trans p01

def p120 : Fin 3 ≃ Fin 3 := p201.symm
@[simp] lemma vector_p01 (A B C : List Bool) : ![A,B,C] ∘ p01=![B,A,C] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p02 (A B C : List Bool) : ![A,B,C] ∘ p02=![C,B,A] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p12 (A B C : List Bool) : ![A,B,C] ∘ p12=![A,C,B] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p201 (A B C : List Bool) : ![A,B,C] ∘ p201=![C,A,B] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p120 (A B C : List Bool) : ![A,B,C] ∘ p120=![B,C,A] := by
  funext i; fin_cases i <;> rfl

def reverse02 : Proc (Fin 3) := reindex reverseRaw p12.toEmbedding
def reverse10 : Proc (Fin 3) := reindex reverseRaw p01.toEmbedding
def reverse20 : Proc (Fin 3) := reindex reverseRaw p201.toEmbedding
def reverse21 : Proc (Fin 3) := reindex reverseRaw p02.toEmbedding
lemma reverse02_exec (A B C : List Bool) :
    Exec reverse02 ![A,B,C] ![[],B,A.reverse++C] (A.length+1) := by
  apply exec_perm
  simpa only [vector_p12] using reverseRaw_exec A C B
lemma reverse10_exec (A B C : List Bool) :
    Exec reverse10 ![A,B,C] ![B.reverse++A,[],C] (B.length+1) := by
  apply exec_perm
  simpa only [vector_p01] using reverseRaw_exec B A C
lemma reverse20_exec (A B C : List Bool) :
    Exec reverse20 ![A,B,C] ![C.reverse++A,B,[]] (C.length+1) := by
  apply exec_perm
  simpa only [vector_p201] using reverseRaw_exec C A B
lemma reverse21_exec (A B C : List Bool) :
    Exec reverse21 ![A,B,C] ![A,C.reverse++B,[]] (C.length+1) := by
  apply exec_perm
  simpa only [vector_p02] using reverseRaw_exec C B A

def finishCons : Proc (Fin 3) := atom (.push 0 (fun _=>false) (.push 1 (fun _=>true) .halt))
lemma finishCons_exec (A : List Bool) : Exec finishCons ![[],A,[]] ![[false],true::A,[]] 1 := by
  apply exec_atom
  simp only [TM2.stepAux]
  congr 1
  funext i; fin_cases i <;> simp

def cons : Proc (Fin 3) := seq reverse02 (seq reverse21 finishCons)
lemma cons_exec (x y : Data) :
    Exec cons ![encode x,encode y,[]] ![encode .nil,encode (.cons x y),[]]
      (2*(encode x).length+3) := by
  have h₁:=reverse02_exec (encode x) (encode y) []
  have h₂:=reverse21_exec [] (encode y) (encode x).reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h₁ h₂
  have hh:=h₁.seq (h₂.seq (finishCons_exec (encode x++encode y)))
  exact hh.mono (by omega)

def clear1 : Proc (Fin 3) := reindex clearRaw p01.toEmbedding
lemma clear1_exec (A B C : List Bool) : Exec clear1 ![A,B,C] ![A,[],C] (B.length+1) := by
  apply exec_perm
  simpa only [vector_p01] using clearRaw_exec B A C

def copy : Proc (Fin 3) := seq clear1 (seq duplicateRaw (seq reverse10 reverse21))
lemma copy_exec (A B : List Bool) : Exec copy ![A,B,[]] ![A,A,[]]
    (B.length+3*A.length+4) := by
  have h₁:=clear1_exec A B []
  have h₂:=duplicateRaw_exec A [] []
  have h₃:=reverse10_exec [] A.reverse A.reverse
  have h₄:=reverse21_exec A [] A.reverse
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h₂ h₃ h₄
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  exact hh.mono (by omega)

def startSplit : Proc (Fin 3) := atom (.pop 1 (fun v _=>v) (.push 0 (fun _=>false) .halt))
lemma startSplit_exec (A : List Bool) : Exec startSplit ![[],true::A,[]] ![[false],A,[]] 1 := by
  apply exec_atom
  simp only [TM2.stepAux]
  congr 1
  funext i; fin_cases i <;> simp
def transfer12 : Proc (Fin 3) := reindex transferRaw p120.toEmbedding
lemma transfer12_exec (x : Data) (A B : List Bool) :
    Exec transfer12 ![[false],encode x++A,B] ![[],A,(encode x).reverse++B]
      ((encode x).length+1) := by
  apply exec_perm
  simpa only [vector_p120] using transferRaw_exec x A B

def split : Proc (Fin 3) := seq clearRaw (seq startSplit (seq transfer12 reverse20))
lemma split_exec (A : List Bool) (x y : Data) :
    Exec split ![A,encode (.cons x y),[]] ![encode x,encode y,[]]
      (A.length+2*(encode x).length+4) := by
  have h₁:=clearRaw_exec A (encode (.cons x y)) []
  have h₂:=startSplit_exec (encode x++encode y)
  have h₃:=transfer12_exec x (encode y) []
  have h₄:=reverse20_exec [] (encode y) (encode x).reverse
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h₃ h₄
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  exact hh.mono (by omega)
end MatchingFPRAS.RegisterProc

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeMachine
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing TreeData

def makeNil : Proc (Fin 3) := seq clearRaw (atom (.push 0 (fun _=>false) .halt))
lemma makeNil_exec (A B C : List Bool) : Exec makeNil ![A,B,C] ![[false],B,C] (A.length+2) := by
  have h₁:=clearRaw_exec A B C
  have h₂ : Exec (atom (.push 0 (fun _=>false) .halt)) ![[],B,C] ![[false],B,C] 1 := by
    apply exec_atom
    simp only [TM2.stepAux]
    congr 1
    funext i; fin_cases i <;> simp
  exact (h₁.seq h₂).mono (by omega)

variable {K : Type} [DecidableEq K]
lemma exec_on (P : Proc (Fin 3)) (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (S : Stack K) (A B C : List Bool) (n : ℕ)
    (h : Exec P ![S a,S b,S c] ![A,B,C] n) :
    Exec (reindex P (triple a b c hab hac hbc)) S (put3 S a b c A B C) n := by
  have hh:=exec_reindex P (triple a b c hab hac hbc) S _ _ _ _ _ _ n h
  simpa only [frame_triple,put3_same S a b c hab hac hbc] using hh
end MatchingFPRAS.RegisterProc

namespace MatchingFPRAS.TreeMachine
open TreeData RegisterProc Turing MachineCost

variable {R Λ : Type} [DecidableEq R]
abbrev K (R : Type) := R⊕Fin 2
abbrev Env (R : Type) := R→Data

def encodeEnv (E : Env R) : Stack (K R)
  | .inl r => encode (E r)
  | .inr _ => []
def pairEmbedding (i j : R) (hij : i≠j) : Fin 3 ↪ K R :=
  triple (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
def singleEmbedding (i : R) : Fin 3 ↪ K R :=
  triple (.inl i) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)

def putPair (E : Env R) (i j : R) (x y : Data) : Env R :=
  Function.update (Function.update E i x) j y
lemma encode_putPair (E : Env R) (i j : R) (hij : i≠j) (x y : Data) :
    put3 (encodeEnv E) (.inl i) (.inl j) (.inr 0) (encode x) (encode y) []=
      encodeEnv (putPair E i j x y) := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,encodeEnv]
  | inl k =>
    by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,encodeEnv,putPair]
lemma encode_putSingle (E : Env R) (i : R) (x : Data) :
    put3 (encodeEnv E) (.inl i) (.inr 0) (.inr 1) (encode x) [] []=
      encodeEnv (Function.update E i x) := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,encodeEnv]
  | inl k => by_cases hi : k=i <;> simp_all [put3,encodeEnv]

inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | nil (i : R) (next : Λ)
  | copy (i j : R) (distinct : i≠j) (next : Λ)
  | cons (i j : R) (distinct : i≠j) (next : Λ)
  | split (i j : R) (distinct : i≠j) (next : Λ)

def procedure : Instr R Λ → Proc (K R)
  | .nil i _ => reindex makeNil (singleEmbedding i)
  | .copy i j h _ => reindex RegisterProc.copy (pairEmbedding i j h)
  | .cons i j h _ => reindex RegisterProc.cons (pairEmbedding i j h)
  | .split i j h _ => reindex RegisterProc.split (pairEmbedding i j h)
  | _ => atom .halt

lemma nil_exec (E : Env R) (i : R) (l : Λ) :
    Exec (procedure (.nil i l)) (encodeEnv E) (encodeEnv (Function.update E i .nil))
      ((encode (E i)).length+2) := by
  have hh:=exec_on (K:=K R) makeNil (.inl i) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (encodeEnv E) [false] [] [] _ (makeNil_exec (encode (E i)) [] [])
  have he:=encode_putSingle E i .nil
  simp only [encode] at he
  rwa [he] at hh
lemma copy_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) :
    Exec (procedure (.copy i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j (E i) (E i)))
      ((encode (E j)).length+3*(encode (E i)).length+4) := by
  have hh:=exec_on (K:=K R) RegisterProc.copy (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode (E i)) (encode (E i)) [] _ (RegisterProc.copy_exec (encode (E i)) (encode (E j)))
  rwa [encode_putPair E i j hij] at hh
lemma cons_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) :
    Exec (procedure (.cons i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j .nil (.cons (E i) (E j))))
      (2*(encode (E i)).length+3) := by
  have hh:=exec_on (K:=K R) RegisterProc.cons (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode .nil) (encode (.cons (E i) (E j))) [] _ (RegisterProc.cons_exec (E i) (E j))
  rwa [encode_putPair E i j hij] at hh
lemma split_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) (x y : Data) (he : E j=.cons x y) :
    Exec (procedure (.split i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j x y))
      ((encode (E i)).length+2*(encode x).length+4) := by
  have h:=RegisterProc.split_exec (encode (E i)) x y
  rw [←he] at h
  have hh:=exec_on (K:=K R) RegisterProc.split (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode x) (encode y) [] _ h
  rwa [encode_putPair E i j hij] at hh
end MatchingFPRAS.TreeMachine

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_BinaryNormalize
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BinaryNormalize
open Turing MachineCost RegisterProc TreeTransfer
open StackAddition (value value_bits)

def normalize (A : List Bool) : List Bool := (A.reverse.dropWhile Bool.not).reverse
lemma normalize_cons (b : Bool) (A : List Bool) :
    normalize (b::A)=if normalize A=[] ∧ b=false then [] else b::normalize A := by
  simp only [normalize,List.reverse_cons,List.dropWhile_append]
  have hh (B : List Bool) :
      (if B.isEmpty then [b].dropWhile Bool.not else B++[b]).reverse=
        if B.reverse=[] ∧ b=false then [] else b::B.reverse := by
    cases B <;> cases b <;> simp
  exact hh _
lemma normalize_bits (A : List Bool) : normalize A=(value A).bits := by
  induction A with
  | nil => rfl
  | cons b A ih =>
    rw [normalize_cons,ih]
    cases b with
    | false =>
      by_cases hz : value A=0
      · simp [hz,value]
      · have hne : (value A).bits≠[] := by
          intro emptyBits
          exact hz ((value_bits (value A)).symm.trans (congrArg value emptyBits))
        simp only [value,Bool.toNat_false,Nat.zero_add, Nat.bit0_bits _ hz,hne,false_and,↓reduceIte]
    | true =>
      simp only [Bool.true_eq_false,and_false,↓reduceIte,value,Bool.toNat_true]
      rw [Nat.add_comm 1 (2*value A),Nat.bit1_bits]
lemma normalize_length (A : List Bool) : (normalize A).length≤A.length := by
  simpa only [normalize,List.length_reverse] using List.length_dropWhile_le Bool.not A.reverse

def stripProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .peek 0 (fun _ x=>x) (.branch (fun x=>x.isNone || x.getD false)
    (.load (fun _=>none) .halt)
    (.pop 0 (fun v _=>v) (.goto (fun _=>()))))
lemma strip_nil (B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg]
lemma strip_true (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) (true::A) B C v)=cfg none (true::A) B C none := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg]
lemma strip_false (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) (false::A) B C v)=cfg (some ()) A B C (some false) := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg,update_zero]
lemma run_strip (A B C : List Bool) (v : Option Bool) :
    ∃ n≤A.length+1,MachineCost.run (TM2.step stripProgram) n (cfg (some ()) A B C v)=
      cfg none (A.dropWhile Bool.not) B C none := by
  induction A generalizing v with
  | nil => exact ⟨1,le_rfl,strip_nil B C v⟩
  | cons a A ih => cases a with
    | false =>
      obtain ⟨n,hn,he⟩:=ih (some false)
      refine ⟨n+1,by simp only [List.length_cons]; omega,?_⟩
      rw [MachineCost.run,strip_false,he]
      rfl
    | true => exact ⟨1,by simp,strip_true A B C v⟩
def stripRaw : Proc (Fin 3) := ⟨Unit,stripProgram⟩
lemma stripRaw_exec (A B C : List Bool) :
    Exec stripRaw ![A,B,C] ![A.dropWhile Bool.not,B,C] (A.length+1) := run_strip A B C none

def swap01 : Fin 3 ↪ Fin 3 := triple 1 0 2 (by decide) (by decide) (by decide)
lemma reindex_swap (P : Proc (Fin 3)) (A B C A' B' C' : List Bool) (n : ℕ)
    (h : Exec P ![A,B,C] ![A',B',C'] n) :
    Exec (reindex P swap01) ![B,A,C] ![B',A',C'] n := by
  have hh:=exec_on P (1 : Fin 3) 0 2 (by decide) (by decide) (by decide) ![B,A,C] A' B' C' n h
  have hout : put3 ![B,A,C] (1 : Fin 3) 0 2 A' B' C'=![B',A',C'] := by
    funext i; fin_cases i <;> simp [put3]
  rw [hout] at hh
  exact hh

def program : Proc (Fin 3) := seq reverseRaw (seq (reindex stripRaw swap01) (reindex reverseRaw swap01))
theorem exec (A C : List Bool) : Exec program ![A,[],C] ![normalize A,[],C] (3*A.length+3) := by
  have h₁:=reverseRaw_exec A [] C
  simp only [List.append_nil] at h₁
  have h₂:=reindex_swap stripRaw A.reverse [] C _ [] C _ (stripRaw_exec A.reverse [] C)
  have h₃:=reindex_swap reverseRaw (A.reverse.dropWhile Bool.not) [] C [] _ C _
    (reverseRaw_exec (A.reverse.dropWhile Bool.not) [] C)
  simp only [List.append_nil] at h₃
  have hh:=h₁.seq (h₂.seq h₃)
  apply hh.mono
  have hl:=List.length_dropWhile_le Bool.not A.reverse
  simp only [List.length_reverse] at hl ⊢
  omega
end MatchingFPRAS.BinaryNormalize

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_FiniteStore
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteStore
open Turing MachineCost RegisterProc

variable {K Λ σ : Type} [DecidableEq K]

def stmt : TM2.Stmt (fun _ : K=>Bool) Λ σ → σ →
    TM2.Stmt (fun _ : K=>Bool) (Λ×σ) (Option Bool)
  | .push k f q,v => .push k (fun _=>f v) (stmt q v)
  | .peek k f q,v => .peek k (fun _ x=>x)
      (.branch Option.isNone (stmt q (f v none))
        (.branch (fun x=>x.getD false) (stmt q (f v (some true))) (stmt q (f v (some false)))))
  | .pop k f q,v => .pop k (fun _ x=>x)
      (.branch Option.isNone (stmt q (f v none))
        (.branch (fun x=>x.getD false) (stmt q (f v (some true))) (stmt q (f v (some false)))))
  | .load f q,v => stmt q (f v)
  | .branch f q r,v => if f v then stmt q v else stmt r v
  | .goto f,v => .load (fun _=>none) (.goto (fun _=>(f v,v)))
  | .halt,_ => .load (fun _=>none) .halt

def cfg (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    TM2.Cfg (fun _ : K=>Bool) (Λ×σ) (Option Bool) :=
  ⟨c.l.map (fun l=>(l,c.var)),none,c.stk⟩

theorem stmt_eval (q : TM2.Stmt (fun _ : K=>Bool) Λ σ) (v : σ) (u : Option Bool)
    (S : K→List Bool) : TM2.stepAux (stmt q v) u S=cfg (TM2.stepAux q v S) := by
  induction q generalizing v u S with
  | push k f q ih => simpa only [stmt,TM2.stepAux] using ih v u (Function.update S k (f v::S k))
  | peek k f q ih =>
    cases hh : (S k).head? with
    | none => simpa only [stmt,TM2.stepAux,hh,Option.isNone_none,Bool.cond_true] using ih (f v none) none S
    | some b => cases b <;> simpa only [stmt,TM2.stepAux,hh,Option.isNone_some,Bool.cond_false,
      Option.getD_some,Bool.cond_true] using ih (f v (S k).head?) (S k).head? S
  | pop k f q ih =>
    cases hh : (S k).head? with
    | none => simpa only [stmt,TM2.stepAux,hh,Option.isNone_none,Bool.cond_true] using ih (f v none) none (Function.update S k (S k).tail)
    | some b => cases b <;> simpa only [stmt,TM2.stepAux,hh,Option.isNone_some,Bool.cond_false,
      Option.getD_some,Bool.cond_true] using ih (f v (S k).head?) (S k).head? (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) u S
  | branch f q r ihq ihr =>
    cases hh : f v with
    | false => simpa only [stmt,TM2.stepAux,hh,Bool.false_eq_true,↓reduceIte,Bool.cond_false] using ihr v u S
    | true => simpa only [stmt,TM2.stepAux,hh,↓reduceIte,Bool.cond_true] using ihq v u S
  | goto f => rfl
  | halt => rfl

def program (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) :
    Λ×σ→TM2.Stmt (fun _ : K=>Bool) (Λ×σ) (Option Bool) := fun p=>stmt (M p.1) p.2
lemma advance_cfg (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ)
    (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    advance (TM2.step (program M)) (cfg c)=cfg (advance (TM2.step M) c) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stmt_eval (M l) v none S
lemma run_cfg (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (n : ℕ)
    (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    MachineCost.run (TM2.step (program M)) n (cfg c)=cfg (MachineCost.run (TM2.step M) n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [MachineCost.run,advance_cfg,ih,MachineCost.run]

def procedure [Fintype Λ] [DecidableEq Λ] [Inhabited Λ] [Fintype σ] [DecidableEq σ]
    (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (v : σ) : Proc K :=
  { Label := Λ×σ
    labels := inferInstance
    entry := ⟨(default,v)⟩
    code := program M }

theorem exec [Fintype Λ] [DecidableEq Λ] [Inhabited Λ] [Fintype σ] [DecidableEq σ]
    (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (v w : σ) (A B : Stack K) (n : ℕ)
    (h : MachineCost.run (TM2.step M) n ⟨some default,v,A⟩=⟨none,w,B⟩) :
    Exec (procedure M v) A B n := by
  refine ⟨n,le_rfl,?_⟩
  exact (run_cfg M n ⟨some default,v,A⟩).trans (congrArg cfg h)
end MatchingFPRAS.FiniteStore

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
open Data

def ofList : List Data → Data
  | [] => .nil
  | x::xs => .cons x (ofList xs)
end MatchingFPRAS.TreeData

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TableLookup
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
open Data

def bit (b : Bool) : Data := if b then .cons .nil .nil else .nil
def nat (n : ℕ) : Data := ofList (n.bits.map bit)
@[simp] lemma nat_zero : nat 0=.nil := by simp [nat,Nat.bits,ofList]
end MatchingFPRAS.TreeData

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TreeBits
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData

def bits (A : List Bool) : Data := ofList (A.map bit)
@[simp] lemma bits_nil : bits []=.nil := rfl
@[simp] lemma bits_cons (b : Bool) (A : List Bool) : bits (b::A)=.cons (bit b) (bits A) := rfl
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeBits
open Turing MachineCost RegisterProc TreeData TreeTransfer

def decodeProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .pop 0 (fun _ x=>x) (.branch (fun x=>x.getD false)
    (.pop 0 (fun _ x=>x) (.branch (fun x=>x.getD false)
      (.pop 0 (fun v _=>v) (.pop 0 (fun v _=>v) (.push 1 (fun _=>true) (.goto (fun _=>())))))
      (.push 1 (fun _=>false) (.goto (fun _=>())))))
    (.load (fun _=>none) .halt))
lemma decode_nil (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step decodeProgram) (cfg (some ()) (false::A) B C v)=cfg none A B C none := by
  simp [advance,TM2.step,decodeProgram,TM2.stepAux,cfg,update_zero]
lemma decode_cons (b : Bool) (bs A B C : List Bool) (v : Option Bool) :
    advance (TM2.step decodeProgram) (cfg (some ()) (encode (bits (b::bs))++A) B C v)=
      cfg (some ()) (encode (bits bs)++A) (b::B) C (some b) := by
  cases b <;> simp [advance,TM2.step,decodeProgram,TM2.stepAux,cfg,update_zero,update_one,encode,bit]
lemma run_decode (bs A B C : List Bool) (v : Option Bool) :
    MachineCost.run (TM2.step decodeProgram) (bs.length+1)
      (cfg (some ()) (encode (bits bs)++A) B C v)=cfg none A (bs.reverse++B) C none := by
  induction bs generalizing B v with
  | nil => simpa only [bits_nil,encode,List.singleton_append,List.length_nil,List.reverse_nil,List.nil_append,Nat.zero_add,MachineCost.run] using decode_nil A B C v
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,decode_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
def decodeRaw : Proc (Fin 3) := ⟨Unit,decodeProgram⟩
lemma decodeRaw_exec (bs A B C : List Bool) :
    Exec decodeRaw ![encode (bits bs)++A,B,C] ![A,bs.reverse++B,C] (bs.length+1) :=
  ⟨_,le_rfl,run_decode bs A B C none⟩

def encodeProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .pop 0 (fun _ x=>x) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.branch (fun x=>x.getD false)
      (.push 1 (fun _=>false) (.push 1 (fun _=>false) (.push 1 (fun _=>true) (.push 1 (fun _=>true) (.goto (fun _=>()))))))
      (.push 1 (fun _=>false) (.push 1 (fun _=>true) (.goto (fun _=>()))))))
lemma encode_nil (B C : List Bool) (v : Option Bool) :
    advance (TM2.step encodeProgram) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,encodeProgram,TM2.stepAux,cfg,update_zero]
lemma encode_cons (b : Bool) (bs C : List Bool) (x : Data) (v : Option Bool) :
    advance (TM2.step encodeProgram) (cfg (some ()) (b::bs) (encode x) C v)=
      cfg (some ()) bs (encode (.cons (bit b) x)) C (some b) := by
  cases b <;> simp [advance,TM2.step,encodeProgram,TM2.stepAux,cfg,update_zero,update_one,encode,bit]
def prepend (bs : List Bool) (x : Data) : Data := bs.foldr (fun b x=>.cons (bit b) x) x
lemma prepend_append (A B : List Bool) (x : Data) : prepend (A++B) x=prepend A (prepend B x) := by
  simp [prepend,List.foldr_append]
lemma run_encode (bs C : List Bool) (x : Data) (v : Option Bool) :
    MachineCost.run (TM2.step encodeProgram) (bs.length+1)
      (cfg (some ()) bs (encode x) C v)=cfg none [] (encode (prepend bs.reverse x)) C none := by
  induction bs generalizing x v with
  | nil => exact encode_nil (encode x) C v
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,encode_cons,ih,List.reverse_cons,prepend_append]
    rfl
lemma prepend_bits (bs : List Bool) : prepend bs .nil=bits bs := by
  induction bs <;> simp_all [prepend,bits,ofList]
def encodeRaw : Proc (Fin 3) := ⟨Unit,encodeProgram⟩
lemma encodeRaw_exec (bs C : List Bool) :
    Exec encodeRaw ![bs.reverse,[false],C] ![[],encode (bits bs),C] (bs.length+1) := by
  refine ⟨_,le_rfl,?_⟩
  have h:=run_encode bs.reverse C .nil none
  simpa only [List.length_reverse,List.reverse_reverse,prepend_bits,encode,encodeRaw,cfg,stackData] using h
end MatchingFPRAS.TreeBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeNumberOps
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeBits
open Turing MachineCost RegisterProc BinaryNormalize TreeData

def decodeForward : Proc (Fin 3) := seq decodeRaw (reindex reverseRaw swap01)
lemma decodeForward_exec (A C : List Bool) :
    Exec decodeForward ![encode (bits A),[],C] ![A,[],C] (2*A.length+2) := by
  have h₁:=decodeRaw_exec A [] [] C
  simp only [List.append_nil] at h₁
  have h₂:=reindex_swap reverseRaw A.reverse [] C [] _ C _ (reverseRaw_exec A.reverse [] C)
  simp only [List.reverse_reverse,List.append_nil] at h₂
  apply (h₁.seq h₂).mono
  simp only [List.length_reverse]; omega

def encodeForward : Proc (Fin 3) := seq reverseRaw
  (seq (atom (.push 0 (fun _=>false) .halt)) (reindex encodeRaw swap01))
lemma encodeForward_exec (A C : List Bool) :
    Exec encodeForward ![A,[],C] ![encode (bits A),[],C] (2*A.length+3) := by
  have h₁:=reverseRaw_exec A [] C
  simp only [List.append_nil] at h₁
  have h₂ : Exec (atom (.push (0 : Fin 3) (fun _=>false) .halt))
      ![[],A.reverse,C] ![[false],A.reverse,C] 1 := by
    apply exec_atom
    simp only [TM2.stepAux]
    congr 1
    funext i; fin_cases i <;> simp
  have h₃:=reindex_swap encodeRaw A.reverse [false] C [] _ C _ (encodeRaw_exec A C)
  apply (h₁.seq (h₂.seq h₃)).mono
  omega
end MatchingFPRAS.TreeBits

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc Turing MachineCost

local instance addEntry : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
def add : Proc (Fin 3) := FiniteStore.procedure ForwardAddition.program (default : StackAddition.Store)
lemma add_exec (A B : List Bool) :
    Exec add ![A,B,[]] ![StackAddition.addDigits false A B,[],[]] (2*(A.length+B.length)+3) := by
  obtain ⟨n,hn,he⟩:=ForwardAddition.run_add A B
  exact (FiniteStore.exec ForwardAddition.program default default _ _ n he).mono hn

local instance compareEntry : Inhabited Ordering := ⟨.eq⟩
def compare : Proc (Fin 3) := FiniteStore.procedure StackCompare.program (default : StackAddition.Store)
lemma compare_exec (A B : List Bool) :
    Exec compare ![A,B,[]] ![[],[],StackCompare.flags (Ord.compare (StackAddition.value A) (StackAddition.value B))]
      (A.length+B.length+1) := by
  obtain ⟨n,hn,he⟩:=StackCompare.run_comparison A B [] .eq default
  have h:=FiniteStore.exec StackCompare.program default default _ _ n he
  simp only [StackCompare.compares_values,List.append_nil] at h
  exact h.mono hn
end MatchingFPRAS.BinaryArithmeticProc

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def decode (i : R) : Proc (K R) := reindex TreeBits.decodeForward (singleEmbedding i)
def encode (i : R) : Proc (K R) := reindex TreeBits.encodeForward (singleEmbedding i)
def normalize (i : R) : Proc (K R) := reindex BinaryNormalize.program (singleEmbedding i)
def add (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j)
    (seq (reindex BinaryArithmeticProc.add (pairEmbedding i j hij))
      (seq (normalize i) (seq (encode i) (atom (.push (.inl j) (fun _=>false) .halt))))))

def rawPair (E : Env R) (i j : R) (A B : List Bool) : Stack (K R) :=
  Function.update (Function.update (encodeEnv E) (.inl i) A) (.inl j) B
lemma rawPair_scratch (E : Env R) (i j : R) (A B : List Bool) (k : Fin 2) :
    rawPair E i j A B (.inr k)=[] := by simp [rawPair,encodeEnv]
lemma rawPair_left (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool) :
    rawPair E i j A B (.inl i)=A := by simp [rawPair,hij]
lemma rawPair_right (E : Env R) (i j : R) (A B : List Bool) :
    rawPair E i j A B (.inl j)=B := by simp [rawPair]
lemma rawPair_encode (E : Env R) (i j : R) (x y : Data) :
    rawPair E i j (TreeData.encode x) (TreeData.encode y)=encodeEnv (putPair E i j x y) := by
  funext k
  cases k with
  | inr k => simp [rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [rawPair,encodeEnv,putPair]
lemma rawPair_same (E : Env R) (i j : R) :
    rawPair E i j (TreeData.encode (E i)) (TreeData.encode (E j))=encodeEnv E := by
  funext k
  cases k with
  | inr k => simp [rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [rawPair,encodeEnv]
lemma put3_raw_left (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) :
    put3 (rawPair E i j A B) (.inl i) (.inr 0) (.inr 1) F [] []=rawPair E i j F B := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
lemma put3_raw_right (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) :
    put3 (rawPair E i j A B) (.inl j) (.inr 0) (.inr 1) F [] []=rawPair E i j A F := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
lemma on_left (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) (n : ℕ)
    (h : Exec P ![A,[],[]] ![F,[],[]] n) :
    Exec (reindex P (singleEmbedding i)) (rawPair E i j A B) (rawPair E i j F B) n := by
  have hh:=exec_on P (.inl i : K R) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (rawPair E i j A B) F [] [] n
  rw [rawPair_left E i j hij,rawPair_scratch,rawPair_scratch] at hh
  simpa only [singleEmbedding,put3_raw_left E i j hij] using hh h
lemma on_right (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) (n : ℕ)
    (h : Exec P ![B,[],[]] ![F,[],[]] n) :
    Exec (reindex P (singleEmbedding j)) (rawPair E i j A B) (rawPair E i j A F) n := by
  have hh:=exec_on P (.inl j : K R) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (rawPair E i j A B) F [] [] n
  rw [rawPair_right,rawPair_scratch,rawPair_scratch] at hh
  simpa only [singleEmbedding,put3_raw_right E i j hij] using hh h
lemma on_pair (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F G : List Bool) (n : ℕ)
    (h : Exec P ![A,B,[]] ![F,G,[]] n) :
    Exec (reindex P (pairEmbedding i j hij)) (rawPair E i j A B) (rawPair E i j F G) n := by
  have hh:=exec_on P (.inl i : K R) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (rawPair E i j A B) F G [] n
  rw [rawPair_left E i j hij,rawPair_right,rawPair_scratch] at hh
  have he : put3 (rawPair E i j A B) (.inl i) (.inl j) (.inr 0) F G []=rawPair E i j F G := by
    funext k
    cases k with
    | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
    | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
  exact he ▸ hh h

theorem add_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hm : E i=nat m) (hn : E j=nat n) :
    Exec (add i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (m+n)) .nil))
      (9*(m.bits.length+n.bits.length)+20) := by
  let A:=m.bits
  let B:=n.bits
  let S:=StackAddition.addDigits false A B
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.add E i j hij A B S [] _ (BinaryArithmeticProc.add_exec A B)
  have h₄:=on_left BinaryNormalize.program E i j hij S [] (BinaryNormalize.normalize S) _
    (BinaryNormalize.exec S [])
  have h₅:=on_left TreeBits.encodeForward E i j hij (BinaryNormalize.normalize S) []
    (TreeData.encode (bits (BinaryNormalize.normalize S))) _ (TreeBits.encodeForward_exec _ [])
  have h₆ : Exec (atom (.push (.inl j) (fun _=>false) .halt))
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [])
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [false]) 1 := by
    apply exec_atom
    simp only [TM2.stepAux,rawPair_right]
    congr 1
    simp [rawPair]
  have hh:=h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  have hS : BinaryNormalize.normalize S=(m+n).bits := by
    rw [BinaryNormalize.normalize_bits,StackAddition.addition_numerals]
  rw [hS] at hh
  have hstart : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    change rawPair E i j (TreeData.encode (nat m)) (TreeData.encode (nat n))=encodeEnv E
    rw [←hm,←hn]
    exact rawPair_same E i j
  have hend : rawPair E i j (TreeData.encode (bits (m+n).bits)) [false]=
      encodeEnv (putPair E i j (nat (m+n)) .nil) := rawPair_encode E i j (nat (m+n)) .nil
  rw [hstart,hend] at hh
  apply hh.mono
  have hl:=StackAddition.addDigits_length A B false
  have hl' := BinaryNormalize.normalize_length S
  rw [hS] at hl'
  dsimp only [A,B,S] at hl hl' ⊢
  omega
end MatchingFPRAS.TreeArithmetic

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeCompare
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc TreeData Turing

def pickLt : Proc (Fin 3) := atom
  (.pop 2 (fun _ x=>x) (.pop 2 (fun x _=>x)
    (.branch (fun x=>x.getD false)
      (.push 0 (fun _=>false) (.push 0 (fun _=>false) (.push 0 (fun _=>true)
        (.load (fun _=>none) .halt))))
      (.push 0 (fun _=>false) (.load (fun _=>none) .halt)))))
lemma pickLt_exec (c : Ordering) :
    Exec pickLt ![[],[],StackCompare.flags c] ![encode (bit (decide (c=.lt))),[],[]] 1 := by
  apply exec_atom
  cases c <;> simp [TM2.stepAux,StackCompare.flags,encode,bit]
  all_goals funext k; fin_cases k <;> simp

def less : Proc (Fin 3) := seq compare pickLt
lemma less_exec (A B : List Bool) :
    Exec less ![A,B,[]] ![encode (bit (decide (StackAddition.value A<StackAddition.value B))),[],[]]
      (A.length+B.length+2) := by
  have hh:=(compare_exec A B).seq (pickLt_exec (Ord.compare (StackAddition.value A) (StackAddition.value B)))
  simp only [compare_lt_iff_lt] at hh
  exact hh.mono (by omega)
end MatchingFPRAS.BinaryArithmeticProc

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def less (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j) (seq (reindex BinaryArithmeticProc.less (pairEmbedding i j hij))
    (atom (.push (.inl j) (fun _=>false) .halt))))

theorem less_bits_exec (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool)
    (hi : E i=bits A) (hj : E j=bits B) :
    Exec (less i j hij) (encodeEnv E)
      (encodeEnv (putPair E i j (bit (decide (StackAddition.value A<StackAddition.value B))) .nil))
      (3*(A.length+B.length)+7) := by
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.less E i j hij A B _ [] _ (BinaryArithmeticProc.less_exec A B)
  have h₄ : Exec (atom (.push (.inl j) (fun _=>false) .halt))
      (rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [])
      (rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [false]) 1 := by
    apply exec_atom
    simp only [TM2.stepAux,rawPair_right]
    congr 1
    simp [rawPair]
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  have hs : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    rw [←hi,←hj]; exact rawPair_same E i j
  have he : rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [false]=
      encodeEnv (putPair E i j (bit (decide (StackAddition.value A<StackAddition.value B))) .nil) :=
    rawPair_encode E i j _ .nil
  rw [hs,he] at hh
  exact hh.mono (by omega)

lemma less_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hi : E i=nat m) (hj : E j=nat n) :
    Exec (less i j hij) (encodeEnv E) (encodeEnv (putPair E i j (bit (decide (m<n))) .nil))
      (3*(m.bits.length+n.bits.length)+7) := by
  simpa only [StackAddition.value_bits] using less_bits_exec E i j hij m.bits n.bits hi hj
end MatchingFPRAS.TreeArithmetic

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_RegisterControl
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterControl
open TreeData TreeMachine RegisterProc Turing MachineCost

variable {R Λ : Type} [DecidableEq R]
inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | call (P : Proc (K R)) (next : Λ)

def procedure : Instr R Λ → Proc (K R)
  | .call P _ => P
  | _ => atom .halt
def successor : Instr R Λ → Option Λ
  | .call _ l => some l
  | _ => none
abbrev Label (M : Λ → Instr R Λ) := Λ ⊕ ((l : Λ) × (procedure (M l)).Label)
instance instFintypeLabel (M : Λ → Instr R Λ) [Fintype Λ] : Fintype (Label M) := by unfold Label; infer_instance

def code (M : Λ → Instr R Λ) : Label M → TM2.Stmt (fun _ : K R=>Bool) (Label M) Store
  | .inl l => match M l with
    | .halt => .halt
    | .go k => .goto (fun _=>.inl k)
    | .branch i a b => .peek (.inl i) (fun _ x=>x) (.branch (fun x=>x.getD false)
        (.load (fun _=>none) (.goto (fun _=>.inl b)))
        (.load (fun _=>none) (.goto (fun _=>.inl a))))
    | .call _ _ => .goto (fun _=>.inr ⟨l,default⟩)
  | .inr ⟨l,u⟩ => StackComposition.relabel (fun u=>.inr ⟨l,u⟩)
      ((successor (M l)).map Sum.inl) ((procedure (M l)).code u)
def compile [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) : Proc (K R) :=
  { Label := Label M
    entry := ⟨.inl default⟩
    code := code M }
def cfg (M : Λ → Instr R Λ) (l : Option Λ) (E : Env R) : TM2.Cfg (fun _ : K R=>Bool) (Label M) Store :=
  ⟨l.map Sum.inl,none,encodeEnv E⟩

inductive Effect : Instr R Λ → Env R → Option Λ → Env R → ℕ → Prop
  | halt (E) : Effect .halt E none E 1
  | go (E l) : Effect (.go l) E (some l) E 1
  | nilBranch (E i l r) (h : E i=.nil) : Effect (.branch i l r) E (some l) E 1
  | consBranch (E i l r x y) (h : E i=.cons x y) : Effect (.branch i l r) E (some r) E 1
  | call (P E F l n) (h : Exec P (encodeEnv E) (encodeEnv F) n) : Effect (.call P l) E (some l) F (n+1)

lemma effect_compiles (M : Λ → Instr R Λ) (l : Λ) (I : Instr R Λ) (hI : M l=I)
    (E F : Env R) (next : Option Λ) (n : ℕ) (h : Effect I E next F n) :
    ∃ k≤n,MachineCost.run (TM2.step (code M)) k (cfg M (some l) E)=cfg M next F := by
  cases h with
  | halt E =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      Option.getD_some,Option.map_none]
  | go E a =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,Option.getD_some]
  | nilBranch E i a b hi =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_false]
  | consBranch E i a b x y hi =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_true]
  | call P E F a n hp =>
    have hp' : Exec (procedure (M l)) (encodeEnv E) (encodeEnv F) n := by simpa only [hI,procedure] using hp
    obtain ⟨j,hj,he⟩:=hp'
    obtain ⟨k,hk,hs⟩:=StackComposition.run_relabel_to_halt (procedure (M l)).code (code M)
      (fun u=>Sum.inr ⟨l,u⟩) ((successor (M l)).map Sum.inl) (fun _=>rfl)
      j ⟨some default,none,encodeEnv E⟩ none (encodeEnv F) he
    refine ⟨k+1,by omega,?_⟩
    rw [MachineCost.run]
    have ha : advance (TM2.step (code M)) (cfg M (some l) E)=
        StackComposition.mapCfg (fun u=>Sum.inr ⟨l,u⟩) ((successor (M l)).map Sum.inl)
          ⟨some default,none,encodeEnv E⟩ := by
      simp only [advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,Option.getD_some,
        StackComposition.mapCfg_some]
    rw [ha,hs]
    simp only [cfg,hI,successor,Option.map_some]

inductive Runs (M : Λ → Instr R Λ) : Option Λ → Env R → Env R → ℕ → Prop
  | done (E) : Runs M none E E 0
  | step (l E next F G n k) (h : Effect (M l) E next F k)
      (rest : Runs M next F G n) : Runs M (some l) E G (k+n)
  | weaken (l : Option Λ) (E F : Env R) (n b : ℕ) (h : Runs M l E F n) (hn : n ≤ b) : Runs M l E F b
lemma runs_compiles (M : Λ → Instr R Λ) (n : ℕ) (l : Option Λ) (E F : Env R)
    (h : Runs M l E F n) :
    ∃ k≤n,MachineCost.run (TM2.step (code M)) k (cfg M l E)=cfg M none F := by
  induction h with
  | done E => exact ⟨0,le_rfl,rfl⟩
  | step l E next F G n k h rest ih =>
    obtain ⟨i,hi,he⟩:=effect_compiles M l (M l) rfl E F next k h
    obtain ⟨j,hj,hf⟩:=ih
    exact ⟨i+j,Nat.add_le_add hi hj,by rw [run_add,he,hf]⟩
  | weaken l E F n m h hnm ih => obtain ⟨k,hk,he⟩:=ih; exact ⟨k,hk.trans hnm,he⟩
lemma compile_exec [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) (n : ℕ) (E F : Env R)
    (h : Runs M (some default) E F n) : Exec (compile M) (encodeEnv E) (encodeEnv F) n :=
  runs_compiles M n (some default) E F h
end MatchingFPRAS.RegisterControl

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_RegisterStructured
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterStructured
open RegisterProc TreeData TreeMachine RegisterControl

variable {R : Type} [DecidableEq R]

inductive Select where | test | left | right | halt deriving DecidableEq, Inhabited
instance instFintypeSelect : Fintype Select := ⟨{.test,.left,.right,.halt},by intro s; cases s <;> simp⟩
def selectCode (i : R) (P Q : Proc (K R)) : Select → RegisterControl.Instr R Select
  | .test => .branch i .left .right
  | .left => .call P .halt
  | .right => .call Q .halt
  | .halt => .halt
def select (i : R) (P Q : Proc (K R)) : Proc (K R) := compile (selectCode i P Q)
lemma select_nil (i : R) (P Q : Proc (K R)) (E F : Env R) (n : ℕ)
    (hi : E i=.nil) (h : Exec P (encodeEnv E) (encodeEnv F) n) :
    Exec (select i P Q) (encodeEnv E) (encodeEnv F) (n+3) := by
  have hh : RegisterControl.Runs (selectCode i P Q) (some Select.halt) F F 1 :=
    Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
  have hl : RegisterControl.Runs (selectCode i P Q) (some Select.left) E F ((n+1)+1) :=
    Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ n h) hh
  have ht : RegisterControl.Runs (selectCode i P Q) (some Select.test) E F (1+((n+1)+1)) :=
    Runs.step _ _ _ _ _ _ _ (Effect.nilBranch E i _ _ hi) hl
  exact (compile_exec _ _ _ _ ht).mono (by omega)
lemma select_cons (i : R) (P Q : Proc (K R)) (E F : Env R) (n : ℕ) (x y : Data)
    (hi : E i=.cons x y) (h : Exec Q (encodeEnv E) (encodeEnv F) n) :
    Exec (select i P Q) (encodeEnv E) (encodeEnv F) (n+3) := by
  have hh : RegisterControl.Runs (selectCode i P Q) (some Select.halt) F F 1 :=
    Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
  have hr : RegisterControl.Runs (selectCode i P Q) (some Select.right) E F ((n+1)+1) :=
    Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ n h) hh
  have ht : RegisterControl.Runs (selectCode i P Q) (some Select.test) E F (1+((n+1)+1)) :=
    Runs.step _ _ _ _ _ _ _ (Effect.consBranch E i _ _ x y hi) hr
  exact (compile_exec _ _ _ _ ht).mono (by omega)

end MatchingFPRAS.RegisterStructured

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFunction
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFunction
open TreeData TreeMachine RegisterProc

abbrev Reg := Fin 10
def env (x y s : Data) : Env Reg := fun i=>if i=0 then x else if i=1 then y else if i=2 then s else .nil
@[simp] lemma env0 (x y s : Data) : env x y s 0=x := rfl
@[simp] lemma env1 (x y s : Data) : env x y s 1=y := rfl
@[simp] lemma env2 (x y s : Data) : env x y s 2=s := rfl
def size (x : Data) : ℕ := (TreeData.encode x).length
@[simp] lemma size_nil : size .nil=1 := rfl
@[simp] lemma size_cons (x y : Data) : size (.cons x y)=size x+size y+1 := by
  simp [size,TreeData.encode]

lemma env_update0 (x y s a : Data) : Function.update (env x y s) 0 a=env a y s := by
  funext i; fin_cases i <;> simp [env]
lemma env_update1 (x y s a : Data) : Function.update (env x y s) 1 a=env x a s := by
  funext i; fin_cases i <;> simp [env]
lemma env_update2 (x y s a : Data) : Function.update (env x y s) 2 a=env x y a := by
  funext i; fin_cases i <;> simp [env]
attribute [simp] env_update0 env_update1 env_update2

def clear (i : Reg) : Proc (K Reg) := procedure (.nil i ())
def copy (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.copy i j h ())
def cons (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.cons i j h ())
def split (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.split i j h ())

lemma copy01 (x y s : Data) :
    Exec (copy 0 1 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env x x s)) (size y+3*size x+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,copy] using copy_exec (env x y s) 0 1 (by decide) ()
lemma copy10 (x y s : Data) :
    Exec (copy 1 0 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env y y s)) (size x+3*size y+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,copy] using copy_exec (env x y s) 1 0 (by decide) ()
lemma cons12 (x y s : Data) :
    Exec (cons 1 2 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env x .nil (.cons y s))) (2*size y+3) := by
  simpa only [putPair,env_update1,env_update2,env1,env2,size,cons] using cons_exec (env x y s) 1 2 (by decide) ()
lemma cons02 (x y s : Data) :
    Exec (cons 0 2 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env .nil y (.cons x s))) (2*size x+3) := by
  simpa only [putPair,env_update0,env_update2,env0,env2,size,cons] using cons_exec (env x y s) 0 2 (by decide) ()
lemma cons10 (x y s : Data) :
    Exec (cons 1 0 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env (.cons y x) .nil s)) (2*size y+3) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,cons] using cons_exec (env x y s) 1 0 (by decide) ()
lemma split12 (x y a s : Data) :
    Exec (split 1 2 (by decide)) (encodeEnv (env x y (.cons a s))) (encodeEnv (env x a s)) (size y+2*size a+4) := by
  simpa only [putPair,env_update1,env_update2,env1,env2,size,split] using split_exec (env x y (.cons a s)) 1 2 (by decide) () a s rfl
lemma split10 (x y z s : Data) :
    Exec (split 1 0 (by decide)) (encodeEnv (env (.cons x y) z s)) (encodeEnv (env y x s)) (size z+2*size x+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,split] using split_exec (env (.cons x y) z s) 1 0 (by decide) () x y rfl
lemma clear0 (x y s : Data) :
    Exec (clear 0) (encodeEnv (env x y s)) (encodeEnv (env .nil y s)) (size x+2) := by
  simpa only [env_update0,env0,size,clear] using nil_exec (env x y s) 0 ()
lemma clear1 (x y s : Data) :
    Exec (clear 1) (encodeEnv (env x y s)) (encodeEnv (env x .nil s)) (size y+2) := by
  simpa only [env_update1,env1,size,clear] using nil_exec (env x y s) 1 ()

def pair (P Q : Proc (K Reg)) : Proc (K Reg) :=
  seq (copy 0 1 (by decide)) (seq (cons 1 2 (by decide)) (seq P
    (seq (split 1 2 (by decide)) (seq (cons 0 2 (by decide))
      (seq (copy 1 0 (by decide)) (seq (clear 1) (seq Q
        (seq (split 1 2 (by decide)) (cons 1 0 (by decide))))))))))

end MatchingFPRAS.TreeFunction

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeTyped
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

class Codec (A : Type) where
  encode : A → Data
export Codec (encode)
instance instCodecData : Codec Data := ⟨id⟩
instance instCodecNat : Codec ℕ := ⟨nat⟩
instance instCodecBool : Codec Bool := ⟨bit⟩
instance instCodecProd {A B : Type} [Codec A] [Codec B] : Codec (A×B) := ⟨fun x=>.cons (encode x.1) (encode x.2)⟩
instance instCodecList {A : Type} [Codec A] : Codec (List A) := ⟨fun x=>ofList (x.map encode)⟩
@[simp] lemma encode_prod {A B : Type} [Codec A] [Codec B] (a : A) (b : B) :
    encode (a,b)=.cons (encode a) (encode b) := rfl
@[simp] lemma encode_list_nil {A : Type} [Codec A] : encode ([] : List A)=.nil := rfl
@[simp] lemma encode_list_cons {A : Type} [Codec A] (a : A) (as : List A) :
    encode (a::as)=.cons (encode a) (encode as) := rfl

def Realizes {A B : Type} [Codec A] [Codec B] (P : Proc (K Reg)) (f : A → B) (t : A → ℕ) : Prop :=
  ∀ a s,Exec P (encodeEnv (env (encode a) .nil s)) (encodeEnv (env (encode (f a)) .nil s)) (t a)
structure Realizer {A B : Type} [Codec A] [Codec B] (f : A → B) where
  program : Proc (K Reg)
  cost : A → ℕ
  correct : Realizes program f cost

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def composition {f : A → B} {g : B → C} (F : Realizer f) (G : Realizer g) : Realizer (g ∘ f) :=
  ⟨seq F.program G.program,fun a=>F.cost a+G.cost (f a),fun a s=>(F.correct a s).seq (G.correct (f a) s)⟩

def pair {f : A → B} {g : A → C} (F : Realizer f) (G : Realizer g) : Realizer (fun a=>(f a,g a)) where
  program := TreeFunction.pair F.program G.program
  cost := fun a=>F.cost a+G.cost a+11*TreeFunction.size (encode a)+6*TreeFunction.size (encode (f a))+31
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split12 (encode (f a)) .nil (encode a) s
    have h5:=cons02 (encode (f a)) (encode a) s
    have h6:=copy10 .nil (encode a) (.cons (encode (f a)) s)
    have h7:=clear1 (encode a) (encode a) (.cons (encode (f a)) s)
    have h8:=G.correct a (.cons (encode (f a)) s)
    have h9:=split12 (encode (g a)) .nil (encode (f a)) s
    have h10:=cons10 (encode (g a)) (encode (f a)) s
    apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq h10))))))))).mono
    simp only [size_nil]
    omega

def identity : Realizer (id : A → A) :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def first : Realizer (Prod.fst : A×B → A) where
  program := seq (TreeFunction.split 1 0 (by decide))
    (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1))
  cost := fun ab=>6*TreeFunction.size (encode ab.1)+TreeFunction.size (encode ab.2)+11
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (encode a) (encode b) .nil s
    have h2:=copy10 (encode b) (encode a) s
    have h3:=clear1 (encode a) (encode a) s
    apply (h1.seq (h2.seq h3)).mono
    simp only [size_nil]; omega

def second : Realizer (Prod.snd : A×B → B) where
  program := seq (TreeFunction.split 1 0 (by decide)) (TreeFunction.clear 1)
  cost := fun ab=>3*TreeFunction.size (encode ab.1)+7
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (encode a) (encode b) .nil s
    have h2:=clear1 (encode b) (encode a) s
    apply (h1.seq h2).mono
    simp only [size_nil]; omega

def add : Realizer (fun ab : ℕ×ℕ=>ab.1+ab.2) where
  program := seq (TreeFunction.split 1 0 (by decide)) (TreeArithmetic.add 0 1 (by decide))
  cost := fun ab=>2*TreeFunction.size (nat ab.1)+5+9*(ab.1.bits.length+ab.2.bits.length)+20
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (nat a) (nat b) .nil s
    have h2:=TreeArithmetic.add_exec (env (nat b) (nat a) s) 0 1 (by decide) b a rfl rfl
    rw [putPair,env_update0,env_update1,Nat.add_comm b a] at h2
    apply (h1.seq h2).mono
    simp only [size_nil]
    omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeChoice
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFunction
open TreeData TreeMachine RegisterProc

lemma split02 (x y a s : Data) :
    Exec (split 0 2 (by decide)) (encodeEnv (env x y (.cons a s)))
      (encodeEnv (env a y s)) (size x+2*size a+4) := by
  simpa only [putPair,env_update0,env_update2,env0,env2,size,split] using
    split_exec (env x y (.cons a s)) 0 2 (by decide) () a s rfl
end MatchingFPRAS.TreeFunction

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def choose {f : A → Bool} {g h : A → B} (F : Realizer f) (G : Realizer g) (H : Realizer h) :
    Realizer (fun a=>if f a then g a else h a) where
  program := seq (TreeFunction.copy 0 1 (by decide)) (seq (TreeFunction.cons 1 2 (by decide))
    (seq F.program (RegisterStructured.select 0
      (seq (TreeFunction.split 0 2 (by decide)) H.program)
      (seq (TreeFunction.split 0 2 (by decide)) G.program))))
  cost := fun a=>F.cost a+(if f a then G.cost a else H.cost a)+7*TreeFunction.size (encode a)+18
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split02 (encode (f a)) .nil (encode a) s
    have hs : TreeFunction.size (encode (f a)) ≤ 3 := by
      cases f a <;> simp [Codec.encode,bit]
    cases hf : f a
    · have h5:=H.correct a s
      have hh:=RegisterStructured.select_nil 0 _ (seq (TreeFunction.split 0 2 (by decide)) G.program) (env (encode (f a)) .nil (.cons (encode a) s))
        (env (encode (h a)) .nil s) _ (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,Bool.false_eq_true,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh))).mono
      simp only [hf]
      simp only [size_nil]
      rw [hf] at hs
      omega
    · have h5:=G.correct a s
      have hh:=RegisterStructured.select_cons 0 (seq (TreeFunction.split 0 2 (by decide)) H.program) _ (env (encode (f a)) .nil (.cons (encode a) s))
        (env (encode (g a)) .nil s) _ .nil .nil (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh))).mono
      simp only [hf]
      simp only [size_nil]
      rw [hf] at hs
      omega

def less : Realizer (fun ab : ℕ×ℕ=>decide (ab.1<ab.2)) where
  program := seq (TreeFunction.split 1 0 (by decide))
    (seq (TreeArithmetic.less 1 0 (by decide))
      (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1)))
  cost := fun ab=>2*TreeFunction.size (nat ab.1)+3*(ab.1.bits.length+ab.2.bits.length)+31
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (nat a) (nat b) .nil s
    have h2:=TreeArithmetic.less_exec (env (nat b) (nat a) s) 1 0 (by decide) a b rfl rfl
    simp only [putPair,env_update0,env_update1] at h2
    have h3:=copy10 .nil (bit (decide (a<b))) s
    have h4:=clear1 (bit (decide (a<b))) (bit (decide (a<b))) s
    apply (h1.seq (h2.seq (h3.seq h4))).mono
    have hs : TreeFunction.size (bit (decide (a<b))) ≤ 3 := by
      cases decide (a<b) <;> simp [bit]
    simp only [size_nil]; omega

def constantData (x : Data) : Realizer (fun _ : A => x) :=
  match x with
  | .nil => ⟨TreeFunction.clear 0,fun a=>TreeFunction.size (encode a)+2,fun a s=>clear0 (encode a) .nil s⟩
  | .cons x y =>
    let P : Realizer (fun _ : A => (x,y)) := pair (constantData x) (constantData y)
    ⟨P.program,P.cost,P.correct⟩

def constant (b : B) : Realizer (fun _ : A=>b) :=
  let P : Realizer (fun _ : A=>encode b) := constantData (encode b)
  ⟨P.program,P.cost,P.correct⟩
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]
namespace Fold
open RegisterControl (Instr Runs Effect)

inductive Point where | loop | check | splitHead | pushTail | pushArgs | body | popTail | rebuild | halt
  deriving DecidableEq, Inhabited
instance instFintypePoint : Fintype Point := ⟨{.loop,.check,.splitHead,.pushTail,.pushArgs,.body,.popTail,.rebuild,.halt},by
  intro p; cases p <;> simp⟩
def code (P : Proc (K Reg)) : Point → RegisterControl.Instr Reg Point
  | .loop => .call (TreeFunction.split 1 0 (by decide)) .check
  | .check => .branch 1 .halt .splitHead
  | .splitHead => .call (TreeFunction.split 3 1 (by decide)) .pushTail
  | .pushTail => .call (TreeFunction.cons 1 2 (by decide)) .pushArgs
  | .pushArgs => .call (TreeFunction.cons 3 0 (by decide)) .body
  | .body => .call P .popTail
  | .popTail => .call (TreeFunction.split 1 2 (by decide)) .rebuild
  | .rebuild => .call (TreeFunction.cons 1 0 (by decide)) .loop
  | .halt => .halt

def heads (a b r s : Data) : Env Reg := Function.update (env b r s) 3 a
lemma splitHeads (a b r s : Data) :
    Exec (TreeFunction.split 3 1 (by decide)) (encodeEnv (env b (.cons a r) s)) (encodeEnv (heads a b r s))
      (2*TreeFunction.size a+5) := by
  have hh := split_exec (env b (.cons a r) s) 3 1 (by decide) () a r rfl
  have he : putPair (env b (.cons a r) s) 3 1 a r=heads a b r s := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  simp [TreeFunction.size,env,TreeData.encode]
  omega
lemma pushTail (a b r s : Data) :
    Exec (TreeFunction.cons 1 2 (by decide)) (encodeEnv (heads a b r s)) (encodeEnv (heads a b .nil (.cons r s)))
      (2*TreeFunction.size r+3) := by
  have hh := cons_exec (heads a b r s) 1 2 (by decide) ()
  have he : putPair (heads a b r s) 1 2 .nil (.cons (heads a b r s 1) (heads a b r s 2))=
      heads a b .nil (.cons r s) := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  exact hh
lemma pushArgs (a b r s : Data) :
    Exec (TreeFunction.cons 3 0 (by decide)) (encodeEnv (heads a b .nil (.cons r s)))
      (encodeEnv (env (.cons a b) .nil (.cons r s))) (2*TreeFunction.size a+3) := by
  have hh := cons_exec (heads a b .nil (.cons r s)) 3 0 (by decide) ()
  have he : putPair (heads a b .nil (.cons r s)) 3 0 .nil
      (.cons (heads a b .nil (.cons r s) 3) (heads a b .nil (.cons r s) 0))=
      env (.cons a b) .nil (.cons r s) := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  exact hh

def cost (f : A×B → B) (t : A×B → ℕ) : List A → B → ℕ
  | [],_ => 10
  | a::as,b => t (a,b)+6*TreeFunction.size (encode a)+8*TreeFunction.size (encode as)+34+cost f t as (f (a,b))

lemma runs {f : A×B → B} (F : Realizer f) (as : List A) (b : B) (s : Data) :
    Runs (code F.program) (some Point.loop) (env (encode (as,b)) .nil s)
      (env (encode (as.foldl (fun b a=>f (a,b)) b)) .nil s) (cost f F.cost as b) := by
  induction as generalizing b with
  | nil =>
    have hh : Runs (code F.program) (some Point.halt) (env (encode b) .nil s) (env (encode b) .nil s) 1 :=
      Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
    have hc : Runs (code F.program) (some Point.check) (env (encode b) .nil s) (env (encode b) .nil s) 2 :=
      Runs.step _ _ _ _ _ 1 1 (Effect.nilBranch _ 1 _ _ rfl) hh
    have hs:=split10 .nil (encode b) .nil s
    have hs' : Exec (TreeFunction.split 1 0 (by decide)) (encodeEnv (env (encode (([] : List A),b)) .nil s))
        (encodeEnv (env (encode b) .nil s)) 7 := by simpa [size_nil,encode_prod,encode_list_nil] using hs
    exact Runs.step _ _ _ _ _ 2 8 (Effect.call _ _ _ _ 7 hs') hc
  | cons a as ih =>
    let z:=as.foldl (fun b a=>f (a,b)) (f (a,b))
    let sa:=TreeFunction.size (encode a)
    let sr:=TreeFunction.size (encode as)
    let rest:=cost f F.cost as (f (a,b))
    have hr := ih (f (a,b))
    have h1:=cons10 (encode (f (a,b))) (encode as) s
    have hreb : Runs (code F.program) (some Point.rebuild) (env (encode (f (a,b))) (encode as) s)
        (env (encode z) .nil s) ((2*sr+4)+rest) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h1) hr
    have h2 := (split12 (encode (f (a,b))) .nil (encode as) s).mono
      (show TreeFunction.size Data.nil+2*TreeFunction.size (encode as)+4 ≤ 2*sr+5 by
        change 1+2*sr+4 ≤ 2*sr+5
        omega)
    have hpop : Runs (code F.program) (some Point.popTail) (env (encode (f (a,b))) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((2*sr+6)+((2*sr+4)+rest)) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h2) hreb
    have h3:=F.correct (a,b) (.cons (encode as) s)
    have hbody : Runs (code F.program) (some Point.body) (env (encode (a,b)) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h3) hpop
    have h4:=pushArgs (encode a) (encode b) (encode as) s
    have ha : Runs (code F.program) (some Point.pushArgs) (heads (encode a) (encode b) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h4) hbody
    have h5:=pushTail (encode a) (encode b) (encode as) s
    have ht : Runs (code F.program) (some Point.pushTail) (heads (encode a) (encode b) (encode as) s)
        (env (encode z) .nil s) ((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h5) ha
    have h6:=splitHeads (encode a) (encode b) (encode as) s
    have hsh : Runs (code F.program) (some Point.splitHead) (env (encode b) (encode (a::as)) s)
        (env (encode z) .nil s) ((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h6) ht
    have hc : Runs (code F.program) (some Point.check) (env (encode b) (encode (a::as)) s)
        (env (encode z) .nil s) (1+((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))))))) :=
      Runs.step _ _ _ _ _ _ 1 (Effect.consBranch _ 1 _ _ (encode a) (encode as) rfl) hsh
    have h7 := (split10 (encode (a::as)) (encode b) .nil s).mono
      (show TreeFunction.size Data.nil+2*TreeFunction.size (encode (a::as))+4 ≤ 2*TreeFunction.size (encode (a::as))+5 by
        change 1+2*TreeFunction.size (encode (a::as))+4 ≤ 2*TreeFunction.size (encode (a::as))+5
        omega)
    have hl : Runs (code F.program) (some Point.loop) (env (encode (a::as,b)) .nil s)
        (env (encode z) .nil s) ((2*TreeFunction.size (encode (a::as))+6)+(1+((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h7) hc
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try rfl
    simp only [cost,encode_list_cons,size_cons,sa,sr,rest]
    ring
end Fold

def fold {f : A×B → B} (F : Realizer f) : Realizer (fun ab : List A×B=>ab.1.foldl (fun b a=>f (a,b)) ab.2) where
  program := RegisterControl.compile (Fold.code F.program)
  cost := fun ab=>Fold.cost f F.cost ab.1 ab.2
  correct := fun ab s=>RegisterControl.compile_exec _ _ _ _ (Fold.runs F ab.1 ab.2 s)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeList
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def Realizer.congr {f g : A → B} (F : Realizer f) (h : ∀ a,f a=g a) : Realizer g :=
  ⟨F.program,F.cost,fun a s=>by simpa only [h a] using F.correct a s⟩

def listCons : Realizer (fun ab : A×List A=>ab.1::ab.2) :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def reverse : Realizer (List.reverse : List A → List A) :=
  (composition (pair identity (constant ([] : List A))) (fold listCons)).congr (by
    intro as
    change as.foldl (fun x y=>y::x) []=as.reverse
    simp)

def toBits : Realizer Nat.bits :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def double : Realizer (fun n : ℕ=>2*n) :=
  (composition (pair identity identity) add).congr (fun value=>by
    change value+value=2*value
    omega)

def mulStep (x : Bool×(ℕ×ℕ)) : ℕ×ℕ :=
  (x.2.1,2*x.2.2+(if x.1 then x.2.1 else 0))

def mulStepRealizer : Realizer mulStep := by
  let bitP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.1) := first
  let nP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.2.1) := composition second first
  let cP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.2.2) := composition second second
  let vP:=choose bitP nP (constant 0)
  let sumP:=composition (pair (composition cP double) vP) add
  exact (pair nP sumP).congr (fun _=>rfl)

lemma mulStep_fold (A : List Bool) (n c : ℕ) :
    A.reverse.foldl (fun z b=>mulStep (b,z)) (n,c)=
      (n,c*2^A.length+StackAddition.value A*n) := by
  induction A generalizing c with
  | nil => simp [StackAddition.value]
  | cons b A ih =>
    simp only [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil,List.length_cons]
    cases b <;> simp only [mulStep,Bool.false_eq_true,↓reduceIte,StackAddition.value,
      Bool.toNat_false,Bool.toNat_true,Nat.zero_add,pow_succ] <;> congr 1 <;> ring

def multiply : Realizer (fun ab : ℕ×ℕ=>ab.1*ab.2) := by
  let bitsP : Realizer (fun ab : ℕ×ℕ=>ab.1.bits.reverse) := composition (composition first toBits) reverse
  let startP : Realizer (fun ab : ℕ×ℕ=>(ab.2,0)) := pair second (constant 0)
  let foldP:=composition (pair bitsP startP) (fold mulStepRealizer)
  exact (composition foldP second).congr (by
    intro ab
    change (ab.1.bits.reverse.foldl (fun z b=>mulStep (b,z)) (ab.2,0)).2=ab.1*ab.2
    rw [mulStep_fold]
    simp [StackAddition.value_bits])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_BinarySubtract
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackSubtract
open Turing MachineCost StackAddition

def borrow (c a b : Bool) : Bool := decide (a.toNat < b.toNat+c.toNat)
lemma digit_balance (c a b : Bool) :
    a.toNat+2*(borrow c a b).toNat=(digit c a b).toNat+b.toNat+c.toNat := by
  cases c <;> cases a <;> cases b <;> decide

def subDigits (c : Bool) (A B : List Bool) : Bool × List Bool :=
  match A,B with
  | [],[] => (c,[])
  | a::A,[] => let r:=subDigits (borrow c a false) A []; (r.1,digit c a false::r.2)
  | [],b::B => let r:=subDigits (borrow c false b) [] B; (r.1,digit c false b::r.2)
  | a::A,b::B => let r:=subDigits (borrow c a b) A B; (r.1,digit c a b::r.2)
termination_by A.length+B.length

lemma subDigits_length (A B : List Bool) (c : Bool) :
    (subDigits c A B).2.length=max A.length B.length := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [subDigits]
    | cons b B ih => simp [subDigits,ih]
  | cons a A ih =>
    cases B with
    | nil => simp [subDigits,ih]
    | cons b B => simp [subDigits,ih,max_add_add_right]

lemma value_lt (A : List Bool) : value A<2^A.length := by
  induction A with
  | nil => simp [value]
  | cons a A ih =>
    have ha : a.toNat≤1 := by cases a <;> decide
    simp only [value,List.length_cons,pow_succ]
    omega

def program (c : Bool) : TM2.Stmt (fun _ : Fin 3=>Bool) Bool Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.load (fun _=>default) .halt)
      (.push 2 (fun v=>digit c (v.1.getD false) (v.2.getD false))
        (.goto (fun v=>borrow c (v.1.getD false) (v.2.getD false))))))
def cfg (c : Option Bool) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Bool Store := ⟨c,v,stackData A B L⟩
lemma step_empty (c : Bool) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=cfg none [] [] L default := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one]
lemma step_digits (c : Bool) (A B L : List Bool) (v : Store) (h : A ≠ [] ∨ B ≠ []) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (borrow c (A.headD false) (B.headD false))) A.tail B.tail
        (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two]
lemma subDigits_step (c : Bool) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    (subDigits c A B).2 = digit c (A.headD false) (B.headD false)::
      (subDigits (borrow c (A.headD false) (B.headD false)) A.tail B.tail).2 := by
  cases A <;> cases B <;> simp_all [subDigits]

theorem run_subtraction (A B L : List Bool) (c : Bool) (v : Store) :
    ∃ t≤A.length+B.length+1,MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
      cfg none [] [] ((subDigits c A B).2.reverse++L) default := by
  have aux : ∀ n (A B : List Bool),A.length+B.length=n → ∀ (c : Bool) (L : List Bool) (v : Store),
      ∃ t≤A.length+B.length+1,MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] ((subDigits c A B).2.reverse++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        refine ⟨1,by simp,?_⟩
        simpa only [MachineCost.run,subDigits,List.reverse_nil,List.nil_append] using step_empty c L v
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (borrow c (A.headD false) (B.headD false))
          (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,subDigits_step c A B hne]
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  exact aux _ A B rfl c L v
end MatchingFPRAS.StackSubtract

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_SubtractProc
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ForwardSubtract
open Turing MachineCost StackAddition StackSubtract

local instance initialControl : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
abbrev Γ := fun _ : Fin 3 => Bool
def program : Bool⊕Unit → TM2.Stmt Γ (Bool⊕Unit) Store :=
  StackComposition.sequence StackSubtract.program ForwardAddition.reverseProgram
lemma run_sub (A B : List Bool) :
    ∃ k≤2*(A.length+B.length)+2,
      MachineCost.run (TM2.step program) k ⟨some default,default,stackData A B []⟩=
        ⟨none,default,stackData ((subDigits false A B).2) [] []⟩ := by
  obtain ⟨n,hn,he⟩:=run_subtraction A B [] false default
  have he' : MachineCost.run (TM2.step StackSubtract.program) n
      (StackSubtract.cfg (some false) A B [] default)=StackSubtract.cfg none [] [] ((subDigits false A B).2).reverse default := by
    simpa only [List.append_nil] using he
  have hr := ForwardAddition.run_reverse [] [] ((subDigits false A B).2).reverse default
  have hr' : MachineCost.run (TM2.step ForwardAddition.reverseProgram) (((subDigits false A B).2).length+1)
      ⟨some default,default,stackData [] [] ((subDigits false A B).2).reverse⟩=
      ⟨none,default,stackData ((subDigits false A B).2) [] []⟩ := by
    simpa only [ForwardAddition.rcfg,List.length_reverse,List.reverse_reverse,List.append_nil] using hr
  obtain ⟨k,hk,hkrun⟩:=StackComposition.sequence_run StackSubtract.program ForwardAddition.reverseProgram
    (StackSubtract.cfg (some false) A B [] default) n (((subDigits false A B).2).length+1)
    (default : Store) (default : Store) (stackData [] [] ((subDigits false A B).2).reverse)
      (stackData ((subDigits false A B).2) [] []) he' hr'
  refine ⟨k,?_,?_⟩
  · have hl:=subDigits_length A B false
    omega
  · exact hkrun
end MatchingFPRAS.ForwardSubtract

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc Turing

local instance subEntry : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
def sub : Proc (Fin 3) := FiniteStore.procedure ForwardSubtract.program (default : StackAddition.Store)
lemma sub_exec (A B : List Bool) :
    Exec sub ![A,B,[]] ![(StackSubtract.subDigits false A B).2,[],[]] (2*(A.length+B.length)+2) := by
  obtain ⟨n,hn,he⟩:=ForwardSubtract.run_sub A B
  exact (FiniteStore.exec ForwardSubtract.program default default _ _ n he).mono hn
end MatchingFPRAS.BinaryArithmeticProc

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeSubtract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def sub (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j)
    (seq (reindex BinaryArithmeticProc.sub (pairEmbedding i j hij))
      (seq (normalize i) (seq (encode i) (atom (.push (.inl j) (fun _=>false) .halt))))))

end MatchingFPRAS.TreeArithmetic

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreePartialChoice
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]

def choosePartial (f : A → Bool) (g h : A → B) (F : Realizer f)
    (G H : Proc (K Reg)) (t u : A → ℕ)
    (hg : ∀ a s,f a=true → Exec G (encodeEnv (env (encode a) .nil s))
      (encodeEnv (env (encode (g a)) .nil s)) (t a))
    (hh : ∀ a s,f a=false → Exec H (encodeEnv (env (encode a) .nil s))
      (encodeEnv (env (encode (h a)) .nil s)) (u a)) :
    Realizer (fun a=>if f a then g a else h a) where
  program := seq (TreeFunction.copy 0 1 (by decide)) (seq (TreeFunction.cons 1 2 (by decide))
    (seq F.program (RegisterStructured.select 0
      (seq (TreeFunction.split 0 2 (by decide)) H)
      (seq (TreeFunction.split 0 2 (by decide)) G))))
  cost := fun a=>F.cost a+(if f a then t a else u a)+7*TreeFunction.size (encode a)+18
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split02 (encode (f a)) .nil (encode a) s
    have hs : TreeFunction.size (encode (f a)) ≤ 3 := by
      cases f a <;> simp [Codec.encode,bit]
    cases hf : f a
    · have h5:=hh a s hf
      have hh':=RegisterStructured.select_nil 0 _ (seq (TreeFunction.split 0 2 (by decide)) G)
        (env (encode (f a)) .nil (.cons (encode a) s)) (env (encode (h a)) .nil s) _
        (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,Bool.false_eq_true,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh'))).mono
      simp only [hf,size_nil]
      rw [hf] at hs
      omega
    · have h5:=hg a s hf
      have hh':=RegisterStructured.select_cons 0 (seq (TreeFunction.split 0 2 (by decide)) H) _
        (env (encode (f a)) .nil (.cons (encode a) s)) (env (encode (g a)) .nil s) _
        .nil .nil (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh'))).mono
      simp only [hf,size_nil]
      rw [hf] at hs
      omega

def subProgram : Proc (K Reg) := seq (TreeFunction.split 1 0 (by decide))
  (seq (TreeArithmetic.sub 1 0 (by decide))
    (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1)))
def subCost (ab : ℕ×ℕ) : ℕ := 2*TreeFunction.size (nat ab.1)+
  9*(ab.1.bits.length+ab.2.bits.length)+4*TreeFunction.size (nat (ab.1-ab.2))+32
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeNatDivision
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def digitValue : Realizer Bool.toNat :=
  (choose identity (constant 1) (constant 0)).congr (fun b=>by cases b <;> rfl)

def divStep (x : Bool×(ℕ×(ℕ×ℕ))) : ℕ×(ℕ×ℕ) :=
  let n:=x.2.1
  let q:=x.2.2.1
  let r:=2*x.2.2.2+x.1.toNat
  (n,if r<n then (2*q,r) else (2*q+1,r-n))

lemma divStep_first (b : Bool) (n q r : ℕ) : (divStep (b,(n,q,r))).1=n := rfl
lemma divStep_lt (b : Bool) (n q r : ℕ) (_ : 0<n) (hr : r<n) :
    (divStep (b,(n,q,r))).2.2<n := by
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  simp only [divStep]
  split_ifs <;> simp only
  · assumption
  · omega
lemma divStep_mass (b : Bool) (n q r : ℕ) :
    n*(divStep (b,(n,q,r))).2.1+(divStep (b,(n,q,r))).2.2=
      2*(n*q+r)+b.toNat := by
  simp only [divStep]
  split_ifs with h
  · simp only; ring
  · simp only
    have hh : n ≤ 2*r+b.toNat := by omega
    have hs:=Nat.sub_add_cancel hh
    nlinarith

lemma divFold_first (A : List Bool) (n q r : ℕ) :
    (A.foldl (fun z b=>divStep (b,z)) (n,q,r)).1=n := by
  induction A generalizing q r with
  | nil => rfl
  | cons b A ih =>
    change (A.foldl _ (divStep (b,(n,q,r)))).1=n
    rw [←Prod.eta (divStep (b,(n,q,r))),divStep_first]
    rw [←Prod.eta (divStep (b,(n,q,r))).2]
    exact ih _ _

lemma divFold_lt (A : List Bool) (n q r : ℕ) (hn : 0<n) (hr : r<n) :
    (A.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2<n := by
  induction A generalizing q r with
  | nil => exact hr
  | cons b A ih =>
    change (A.foldl _ (divStep (b,(n,q,r)))).2.2<n
    rw [←Prod.eta (divStep (b,(n,q,r))),divStep_first]
    rw [←Prod.eta (divStep (b,(n,q,r))).2]
    exact ih _ _ (divStep_lt b n q r hn hr)

lemma divFold_mass (A : List Bool) (n q r : ℕ) :
    n*(A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.1+
      (A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2=
      (n*q+r)*2^A.length+StackAddition.value A := by
  induction A with
  | nil => simp [StackAddition.value]
  | cons b A ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    let z := A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)
    have hz : z=(n,z.2.1,z.2.2) := by
      apply Prod.ext
      · exact divFold_first A.reverse n q r
      · rfl
    change n*(divStep (b,z)).2.1+(divStep (b,z)).2.2=_
    rw [hz,divStep_mass]
    change n*z.2.1+z.2.2=_ at ih
    rw [ih]
    simp only [StackAddition.value,List.length_cons,pow_succ]
    ring

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def weight (a : A) : ℕ := TreeFunction.size (encode a)
@[simp] lemma weight_prod (a : A) (b : B) : weight (a,b)=1+weight a+weight b := by simp [weight]; omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScaledWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded quotient draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def scaledWordValue (x : ℕ×List Bool) : ℕ :=
  x.1*StackAddition.value x.2/2^x.2.length

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SignedPairProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary signed arithmetic used to prepare the forest evaluator

A pair stores a difference of naturals. Arithmetic never iterates through
the represented integer value, and normalization returns the exact
positive/negative parts expected by the affine penalty program.
-/

namespace ContingencyTables.SignedPairProgram

open MatchingFPRAS.TreeTyped
open scoped BigOperators

abbrev Signed := ℕ×ℕ

def value (a : Signed) : ℤ := (a.1:ℤ)-a.2

def normalize (a : Signed) : Signed := (a.1-a.2,a.2-a.1)

end ContingencyTables.SignedPairProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SignedFloorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary floor of a signed rational

Two natural quotients and the comparison of their remainders compute
the exact floor. No loop depends on the numeric numerator or denominator.
-/

namespace ContingencyTables.SignedFloorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram

abbrev Input := Signed×ℕ

def numeratorQuotient (z : Input) : ℕ := z.1.1/z.2

def negativeQuotient (z : Input) : ℕ := z.1.2/z.2

def carry (z : Input) : Bool := decide (z.1.1%z.2<z.1.2%z.2)

def carryValue (z : Input) : ℕ := if carry z then 1 else 0

def raw (z : Input) : Signed := (numeratorQuotient z,negativeQuotient z+carryValue z)

def floorCode (z : Input) : Signed := if z.2=0 then (0,0) else raw z

end ContingencyTables.SignedFloorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinIntervalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary evaluation of a bin interval and its bounded quotient draw

The lower endpoint is computed as the negative floor of a negative
rational. Thus the executed arithmetic uses natural quotient/remainder,
without enumerating any of the integers in the interval.
-/

namespace ContingencyTables.BinIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram ProfilePrograms

/-- `(number of bins, range size, bin index)`. -/
abbrev Input := (ℕ×ℕ)×ℕ

def negativeInput (z : Input) : SignedFloorProgram.Input :=
  ((0,z.2*z.1.2),z.1.1)
def negativeInputRealizer : Realizer negativeInput :=
  pair (pair (constant 0)
    (composition (f := fun z : Input => (z.2,z.1.2))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair second (composition first second)) multiply)) (composition first first)

def endpoint (z : Input) : ℕ :=
  (SignedPairProgram.normalize (SignedFloorProgram.floorCode (negativeInput z))).2

def next (z : Input) : Input := (z.1,z.2+1)

def intervalSize (z : Input) : ℕ := endpoint (next z)-endpoint z

def draw (z : Input×List Bool) : ℕ :=
  endpoint z.1+scaledWordValue (intervalSize z.1,z.2)

end ContingencyTables.BinIntervalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Parse
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial

def numStep (x : Symbol×List ℕ) : List ℕ :=
  if x.1=3 then 0::x.2
  else if x.1=1 then (2*x.2.headD 0)::x.2.tail
  else if x.1=2 then (2*x.2.headD 0+1)::x.2.tail
  else x.2

def parse (as : List Symbol) : List ℕ := as.foldr (fun a ns=>numStep (a,ns)) []
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The public matrix encoding uniquely identifies a fixed-shape table -/

namespace ContingencyTables.Algorithms
open MatchingFPRAS MatchingFPRAS.LiteralParse Turing

lemma parse_blank_extension (as : List Symbol) (n : ℕ) :
    parse (as++List.replicate n (0:Symbol))=parse as := by
  have hz : (List.replicate n (0:Symbol)).foldr (fun a ns => numStep (a,ns)) []=[] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ,List.foldr_cons,ih]
      rfl
  unfold parse
  rw [List.foldr_append,hz]

/-- Parsing natural-number fields is unchanged by trailing tape blanks. -/
def blankNumbers (tape : ListBlank Symbol) : List ℕ :=
  tape.liftOn parse (by
    rintro as _ ⟨n,rfl⟩
    exact (parse_blank_extension as n).symm)

end ContingencyTables.Algorithms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedCellFibres
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact one-cell fibres of the physical balanced profile sum -/

namespace ContingencyTables.BalancedCellFibres

open scoped BigOperators Classical

variable {C : Type*} [Fintype C] [DecidableEq C]

abbrev Profiles (M : C → ℕ) := (c : C) → Fin (M c+1)
abbrev Others (M : C → ℕ) (t : C) := (c : {c : C // c≠t}) → Fin (M c.val+1)

def profile (M : C → ℕ) (a : Profiles M) : C×Bool → ℕ :=
  fun p => if p.2 then M p.1-(a p.1).val else (a p.1).val

noncomputable def fibre (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ)
    (t : C) (k : Fin (M t+1)) : ℝ :=
  ∑ a : Profiles M,if a t=k then F (profile M a) else 0

noncomputable def join (M : C → ℕ) (t : C)
    (k : Fin (M t+1)) (a : Others M t) : Profiles M :=
  (Equiv.piSplitAt t (fun c => Fin (M c+1))).symm (k,a)

end ContingencyTables.BalancedCellFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedPhysicalPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partitioning actual balanced profiles into small and large cells -/

namespace ContingencyTables.BalancedCellFibres

open scoped BigOperators Classical
open PhysicalLargeProfiles LargePairEnumeration

variable {C : Type*}

abbrev SmallProfiles (small : C → Bool) (M : C → ℕ) :=
  (s : {c : C // small c=true}) → Fin (M s.val+1)

noncomputable def partition (small : C → Bool) (M : C → ℕ) :
    Profiles M ≃ SmallProfiles small M×PhysicalAssignments small M where
  toFun a := (fun s => a s.val,fun l => a l.val)
  invFun a c := if hs : small c=true then a.1 ⟨c,hs⟩
    else a.2 ⟨c,Bool.eq_false_iff.mpr hs⟩
  left_inv a := by funext c; dsimp only; split_ifs <;> rfl
  right_inv a := by
    apply Prod.ext
    · funext s
      simp only [s.property,dite_eq_left]
    · funext l
      simp only [l.property,Bool.false_eq_true,dite_false]

def smallDisplay (small : C → Bool) (M : C → ℕ) (a : SmallProfiles small M) : SmallView small → ℕ :=
  fun p => if p.2 then M p.1.val-(a p.1).val else (a p.1).val

end ContingencyTables.BalancedCellFibres

end OAI
end


