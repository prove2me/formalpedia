-- Prove2me | Definitions.Def_OAIQ053K034
-- name    : OAIQ053K034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:00:32.794719+00:00
-- url     : https://prove2.me/theorems/4204f2c9-04b3-436c-be24-af97a58953ec
-- title:
--   Definitions bundle OAIQ053K034 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 46 definitions, 4 inductive types or structures and 27 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Context`, `OAI.MetricKMedian.LPBinary.Input.iterate`, `OAI.MetricKMedian.LPBinary.Input.vector`, `OAI.MetricKMedian.LPBinary.Input.zeroOutput`, `OAI.MetricKMedian.LPBinary.Repair.assignments`, `OAI.MetricKMedian.LPBinary.Repair.encodeData`, `OAI.MetricKMedian.LPBinary.Repair.finish`, `OAI.MetricKMedian.LPBinary.Repair.nearestRows`, `OAI.MetricKMedian.LPBinary.Repair.valid`, `OAI.MetricKMedian.LPBinary.Repair.value`, `OAI.MetricKMedian.LPBinary.Scale.guesses`, `OAI.MetricKMedian.LPBinary.State`, `OAI.MetricKMedian.LPBinary.Truncated.component`, `OAI.MetricKMedian.LPBinary.Truncated.gradient`, `OAI.MetricKMedian.LPBinary.Truncated.matrix`, `OAI.MetricKMedian.LPBinary.Truncated.next`, `OAI.MetricKMedian.LPBinary.Truncated.objective`, `OAI.MetricKMedian.LPBinary.choose`, `OAI.MetricKMedian.LPBinary.rawContext`, `OAI.MetricKMedian.LPBinary.rawGrad`, `OAI.MetricKMedian.LPBinary.rawInitial`, `OAI.MetricKMedian.LPBinary.rawPenalty`, `OAI.MetricKMedian.LPBinary.rawRate`, `OAI.MetricKMedian.LPBinary.rawSteps`, `OAI.MetricKMedian.LPBinary.update`, `OAI.MetricKMedian.LPBinary.value`, `OAI.MetricKMedian.PCP.PortCSP.Satisfies`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.supplierView`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Input.rep`, `OAI.MetricKMedian.RoundingProgram.SignedRound.emptyInput`, `OAI.MetricKMedian.RoundingProgram.Terminal.bernoulliInput`, `OAI.MetricKMedian.SparseBundles.Program.QInput.encode`, `OAI.MetricKMedian.SparseBundles.Program.eqi`, `OAI.MetricKMedian.SparseBundles.Program.qr`, `OAI.MetricKMedian.SparseBundles.Program.qt`, `OAI.MetricKMedian.SparseCounts.ListOperation.er`, `OAI.MetricKMedian.SparseCounts.ListOperation.et`, `OAI.MetricKMedian.SparseCounts.Program.Context`, `OAI.MetricKMedian.SparseCounts.Program.Input`, `OAI.MetricKMedian.SparseCounts.Program.T` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_PoweringObjects`, `KMedian_Expanders_GraphExtend`, `KMedian_Geometry_NearestFillingFormula`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_DualListOperations`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_GradientDenominator`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPBinaryTrajectory`, `KMedian_Optimization_LPMinimumSelection`, `KMedian_Optimization_SubgradientTrajectoryHeight`, `KMedian_Optimization_TruncatedListOperations`, `KMedian_Optimization_TruncatedRepair`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Process_CountListOperations`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_ScaleListProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedRoundProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Rounding_TargetSubsetProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K014`, `OAIQ053K015`, `OAIQ053K016`, `OAIQ053K017`, `OAIQ053K018`, `OAIQ053K019`, `OAIQ053K020`, `OAIQ053K021`, `OAIQ053K022` and `OAIQ053K023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K041` and `OAIQ053K042`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K014
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K016
import Definitions.Def_OAIQ053K017
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K019
import Definitions.Def_OAIQ053K020
import Definitions.Def_OAIQ053K021
import Definitions.Def_OAIQ053K022
import Definitions.Def_OAIQ053K023

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringObjects
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D}
variable [DecidableEq A] (C : PortCSP G A)

def Satisfies (x : V → A) : Prop := ∀ v d, (x v,x (G.step v d)) ∈ C.allowed (v,d)

end PortCSP

end MetricKMedian.PCP

end Inline_PCPPoweringObjects

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphExtend
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphExtend

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V W D A : Type} [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D]
  [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) (e : V ↪ W)

omit [DecidableEq A] in
@[simp] lemma extendedAllowed_image (p : V × D) :
    C.extendedAllowed e (e p.1,p.2)=C.allowed p := by
  change C.extendedAllowed e (PortGraph.portEmbed e p)=_
  simp only [extendedAllowed,Set.mem_range_self,dite_eq_left,
    Function.Embedding.toEquivRange_symm_apply_self]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPGraphExtend

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPMinimumSelection
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

variable {α : Type}

 theorem selectMinimum_ofFn {n : ℕ} [NeZero n] (f : Fin n → α) (d : α → ℚ) (a0 : α) :
    selectMinimum d (List.ofFn f) a0=
      f (Preparation.firstNearest univ (fun i => d (f i)) univ_nonempty) := by
  let a := Preparation.firstNearest univ (fun i => d (f i)) univ_nonempty
  have hval : minimum ((List.ofFn f).map d)=d (f a) := by
    apply Eq.trans _ (firstNearest_value univ (fun i => d (f i)) univ_nonempty).symm
    apply minimum_eq_finset
    intro q
    simp only [List.mem_map,List.mem_ofFn,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨x,⟨i,rfl⟩,h⟩
      exact ⟨i,h⟩
    · rintro ⟨i,h⟩
      exact ⟨f i,⟨i,rfl⟩,h⟩
  have hfind : (List.ofFn f).find? (fun x => decide (d x=minimum ((List.ofFn f).map d)))=some (f a) := by
    apply List.find?_ofFn_eq_some.mpr
    refine ⟨by rw [hval]; simp, a,rfl,?_⟩
    intro j hj hp
    have he : d (f j)=d (f a) := by simpa only [decide_eq_true_eq,hval] using hp
    have hh := firstNearest_le univ (fun i => d (f i)) univ_nonempty j (mem_univ j) he
    exact (not_le_of_gt hj) hh
  unfold selectMinimum
  rw [List.head?_filter,hfind]
  rfl

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_NearestFillingFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

theorem first_before (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (i : Fin n) (hi : i∈U) (hne : i≠firstNearest U d hU) : before d (firstNearest U d hU) i := by
  have hd := (firstNearest_spec U d hU).2 i hi
  rcases hd.lt_or_eq with h|h
  · exact Or.inl h
  · exact Or.inr ⟨h,lt_of_le_of_ne (LPBinary.firstNearest_le U d hU i hi h.symm) hne.symm⟩

theorem not_before_first (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (i : Fin n) (hi : i∈U) : ¬before d i (firstNearest U d hU) := by
  rintro (h|⟨h,hi'⟩)
  · exact (not_lt_of_ge ((firstNearest_spec U d hU).2 i hi)) h
  · exact (not_lt_of_ge (LPBinary.firstNearest_le U d hU i hi h)) hi'

theorem priorMass_first (U : Finset (Fin n)) (y d : Fin n → ℚ) (hU : U.Nonempty) :
    priorMass U y d (firstNearest U d hU)=0 := by
  apply sum_eq_zero
  intro j hj
  exact (not_before_first U d hU j (mem_filter.mp hj).1 (mem_filter.mp hj).2).elim

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem repaired_spec (d x : κ → ι → ℚ) (y : ι → ℚ) (H ρ k : ℚ)
    (hH : 1 ≤ H) (hρ : ρ < 1) (hkρ : ρ*(k+1) ≤ 1)
    (hd : ∀ j i, 0 ≤ d j i) (hy : ∀ i, 0 ≤ y i)
    (hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ y i)
    (hs : ∀ j, ∑ i, x j i=1) (hybudget : ∑ i, y i ≤ k)
    (hcost : (∑ j, ∑ i, x j i*truncated d H j i) ≤ ρ*H) :
    (∀ i, 0 ≤ repairedOpening y ρ i ∧ repairedOpening y ρ i ≤ 1) ∧
    (∀ j i, 0 ≤ repairedAssignment d x j i ∧
      repairedAssignment d x j i ≤ repairedOpening y ρ i) ∧
    (∀ j, ∑ i, repairedAssignment d x j i=1) ∧
    (∑ i, repairedOpening y ρ i) ≤ k+1 ∧
    (∑ j, ∑ i, repairedAssignment d x j i*d j i) ≤
      (∑ j, ∑ i, x j i*truncated d H j i)/(1-ρ) := by
  classical
  have hρp : 0 < 1-ρ := sub_pos.mpr hρ
  have hx0 : ∀ j i, 0 ≤ x j i := fun j i => (hx j i).1
  have hm : ∀ j, 1-ρ ≤ nearMass d x j := nearMass_lower d x H ρ hH hd hx0 hs hcost
  have hmp : ∀ j, 0 < nearMass d x j := fun j => hρp.trans_le (hm j)
  have hw : ∀ j i, 0 ≤ nearWeight d x j i := nearWeight_nonneg d x hx0
  have hwy : ∀ j i, nearWeight d x j i ≤ y i := fun j i =>
    (nearWeight_le d x hx0 j i).trans (hx j i).2
  have hwm : ∀ j i, nearWeight d x j i ≤ nearMass d x j := fun j i =>
    single_le_sum (fun a _ => hw j a) (mem_univ i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨le_min (by norm_num) (div_nonneg (hy i) hρp.le),min_le_left _ _⟩
  · intro j i
    refine ⟨div_nonneg (hw j i) (hmp j).le,le_min ?_ ?_⟩
    · exact (div_le_one (hmp j)).mpr (hwm j i)
    · calc
        _ ≤ nearWeight d x j i/(1-ρ) := div_le_div_of_nonneg_left (hw j i) hρp (hm j)
        _ ≤ _ := div_le_div_of_nonneg_right (hwy j i) hρp.le
  · intro j
    simp only [repairedAssignment,← sum_div]
    exact div_self (hmp j).ne'
  · calc
      _ ≤ ∑ i, y i/(1-ρ) := sum_le_sum (fun _ _ => min_le_right _ _)
      _ = (∑ i, y i)/(1-ρ) := (sum_div _ _ _).symm
      _ ≤ k/(1-ρ) := div_le_div_of_nonneg_right hybudget hρp.le
      _ ≤ k+1 := (div_le_iff₀ hρp).mpr (by nlinarith)
  · have hterm : ∀ j i, repairedAssignment d x j i*d j i ≤ x j i*truncated d H j i/(1-ρ) := by
      intro j i
      have hc : nearWeight d x j i*d j i ≤ x j i*truncated d H j i := by
        unfold nearWeight truncated
        split_ifs
        · exact le_rfl
        · simpa only [zero_mul] using mul_nonneg (hx0 j i) (by linarith : 0 ≤ H)
      calc
        _ = (nearWeight d x j i*d j i)/nearMass d x j := by unfold repairedAssignment; ring
        _ ≤ (nearWeight d x j i*d j i)/(1-ρ) :=
          div_le_div_of_nonneg_left (mul_nonneg (hw j i) (hd j i)) hρp (hm j)
        _ ≤ _ := div_le_div_of_nonneg_right hc hρp.le
    calc
      _ ≤ ∑ j, ∑ i, x j i*truncated d H j i/(1-ρ) :=
        sum_le_sum (fun j _ => sum_le_sum (fun i _ => hterm j i))
      _ = _ := by simp only [← sum_div]

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_GradientDenominator
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.TruncatedLP
open Finset RationalGrid
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem threshold_grid (d y : ι → ℚ) (D H : ℤ) (hD : D ≠ 0)
    (hd : ∀ i, At D (d i)) : At D (FractionalDual.bestThreshold d y H) := by
  have hh := (FractionalDual.bestThreshold_spec d y H).1
  obtain he | hh := mem_insert.mp hh
  · rw [he]; exact RationalGrid.zero D
  · obtain he | hh := mem_insert.mp hh
    · rw [he]; exact RationalGrid.integer D H hD
    · obtain ⟨i,_,he⟩ := mem_image.mp hh
      rw [← he]
      exact hd i

theorem gradient_grid (d : κ → ι → ℚ) (y : ι → ℚ) (D H : ℤ) (hD : D ≠ 0)
    (hd : ∀ j i, At D (d j i)) (i : ι) : At D (gradient d y H i) := by
  apply RationalGrid.sum
  intro j _
  unfold FractionalDual.gradient
  exact RationalGrid.neg (RationalGrid.max (RationalGrid.zero D)
    (RationalGrid.sub (threshold_grid _ _ D H hD (truncated_grid d D H hD hd j))
      (truncated_grid d D H hD hd j i)))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SubgradientTrajectoryHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient Binary
variable {n m : ℕ} [NeZero n] [NeZero m]

theorem trajectory_height (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0<k) (hH : 0<H)
    (R : ℤ) (hR : 0<R) (hd : ∀ j i, RationalGrid.At R (d j i))
    (L : ℕ) (hbase : rateDen (n:=n) (m:=m) r H*R*(n:ℤ) ≤ 2^L)
    (hkL : (k:ℤ) ≤ 2^L) (t : ℕ) (i : Fin n) :
    HasHeight (point (trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
      (fun y => gradient d y H) (initial (k:ℚ)) t) i) (L*(t+1)) := by
  let b := rateDen (n:=n) (m:=m) r H
  have hb : 0<b := rateDen_pos r H hr hH
  obtain ⟨Q,hQ,hBQ,hv⟩ := trajectory_denominator (n:=n) (k:ℤ) b R hb hR
    (fun y => gradient d y H) (fun y j => by
      exact_mod_cast gradient_grid d y R (H:ℤ) hR.ne' hd j) t
  let q := point (trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
      (fun y => gradient d y H) (initial (k:ℚ)) t) i
  have hqgrid : RationalGrid.At Q q := by
    dsimp only [q]
    rw [rate_eq]
    exact hv i
  have hkq : (0:ℚ)<k := by exact_mod_cast hk
  have hf := trajectory_feasible (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ)) hkq (initial_feasible _ hkq.le) t
  have hq0 : 0≤q := hf.1 i
  have hqk : q≤(k:ℚ) := (single_le_sum (fun j _ => hf.1 j) (mem_univ i)).trans_eq hf.2
  obtain ⟨A,hA⟩ := hqgrid
  change q=(A:ℚ)/(Q:ℚ) at hA
  have hQq : (0:ℚ)<Q := by exact_mod_cast hQ
  have hA0 : (0:ℤ)≤A := by
    have hh : (0:ℚ)≤A := by
      have hmul := mul_nonneg (hA ▸ hq0) hQq.le
      rwa [div_mul_cancel₀ _ hQq.ne'] at hmul
    exact_mod_cast hh
  have hAk : A≤(k:ℤ)*Q := by
    have hh := (div_le_iff₀ hQq).mp (hA ▸ hqk)
    exact_mod_cast hh
  have hQP : Q≤(2:ℤ)^(L*t) := by
    apply hBQ.trans
    rw [pow_mul]
    apply pow_le_pow_left₀ (le_of_lt (mul_pos (mul_pos hb hR) (by exact_mod_cast NeZero.pos n))) hbase
  have hAP : |A|≤(2:ℤ)^(L*(t+1)) := by
    rw [abs_of_nonneg hA0]
    calc
      _ ≤ (k:ℤ)*Q := hAk
      _ ≤ (2:ℤ)^L*(2:ℤ)^(L*t) := mul_le_mul hkL hQP hQ.le (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hQP' : |Q|≤(2:ℤ)^(L*(t+1)) := by
    rw [abs_of_pos hQ]
    exact hQP.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left L (Nat.le_succ _)))
  change HasHeight q _
  rw [hA]
  exact Gaussian.ratio_num_den_bound A Q hQ.ne' _ hAP hQP'
end MetricKMedian.TruncatedLP
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input

def vector (I : Input) (r : ℕ) (t : ℕ) : Vector ℚ I.n :=
  ProjectedSubgradient.trajectory (I.k:ℚ) (TruncatedLP.rate (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k))
    (fun y => TruncatedLP.gradient I.distance y (TruncatedLP.penalty r I.k))
    (ProjectedSubgradient.initial (I.k:ℚ)) t

def iterate (I : Input) (r : ℕ) (t : ℕ) : Row := List.ofFn (ProjectedSubgradient.point (I.vector r t))
end Input

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_DualListOperations
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

namespace Dual

 theorem best_ofFn {n : ℕ} (d y : Fin n → ℚ) (H : ℚ) :
    best (List.ofFn d) (List.ofFn y) H=FractionalDual.bestThreshold d y H := by
  have hU : ((FractionalDual.thresholds d H).filter (fun t => FractionalDual.affine d y t=FractionalDual.value d y H)).Nonempty := by
    obtain ⟨ht,he⟩ := FractionalDual.bestThreshold_spec d y H
    exact ⟨_,mem_filter.mpr ⟨ht,he⟩⟩
  unfold best FractionalDual.bestThreshold
  rw [dite_eq_left hU]
  apply maximum_eq_finset
  intro q
  simp only [List.mem_filter,mem_filter,decide_eq_true_eq,mem_candidates,affine_ofFn,value_ofFn]

end Dual
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedListOperations
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Finset

namespace Truncated

def matrix (ds : Rows) (H : ℚ) : Rows := ds.map (fun d => row d H)
def objective (ds : Rows) (ys : Row) (H : ℚ) : ℚ := ((matrix ds H).map (fun d => Dual.value d ys H)).sum

def component (ds : Rows) (ys : Row) (H : ℚ) (i : ℕ) : ℚ :=
  ((matrix ds H).map (fun d => -max 0 (Dual.best d ys H-d[i]?.getD 0))).sum

def gradient (ds : Rows) (ys : Row) (H : ℚ) : Row :=
  (List.range ys.length).map (component ds ys H)

def next (ds : Rows) (ys : Row) (H k rate : ℚ) : Row :=
  project ((ys.zip (gradient ds ys H)).map (fun p => p.1-rate*p.2)) k

 theorem matrix_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (H : ℚ) :
    matrix (List.ofFn (fun j => List.ofFn (d j))) H=List.ofFn (fun j => List.ofFn (TruncatedLP.truncated d H j)) := by
  simp only [matrix,List.map_ofFn]
  congr 1
  funext j
  exact row_ofFn d H j
 theorem objective_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) :
    objective (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H=TruncatedLP.objective d y H := by
  simp only [objective,matrix_ofFn,List.map_ofFn,List.sum_ofFn,TruncatedLP.objective]
  apply sum_congr rfl
  intro j _
  exact Dual.value_ofFn _ _ _
 theorem component_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) (i : Fin n) :
    component (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H i.val=TruncatedLP.gradient d y H i := by
  simp only [component,matrix_ofFn,List.map_ofFn,List.sum_ofFn,TruncatedLP.gradient]
  apply sum_congr rfl
  intro j _
  simp only [Function.comp_apply,Dual.best_ofFn,Gaussian.ListOperation.get_ofFn,FractionalDual.gradient]
 theorem gradient_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) :
    gradient (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H=List.ofFn (TruncatedLP.gradient d y H) := by
  simp only [gradient,List.length_ofFn]
  rw [range_ofFn,List.map_ofFn]
  congr 1
  funext i
  exact component_ofFn d y H i
 theorem next_ofFn {n m : ℕ} [NeZero n] (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H k rate : ℚ) :
    next (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H k rate=
      List.ofFn (ProjectedSubgradient.point (ProjectedSubgradient.next k rate (fun y => TruncatedLP.gradient d y H) (Vector.ofFn y))) := by
  simp only [next,gradient_ofFn,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,project_ofFn]
  congr 1
  funext i
  simp only [ProjectedSubgradient.next_apply,ProjectedSubgradient.point_ofFn]
  simp only [ProjectedSubgradient.point_ofFn_apply,Function.comp_def]
end Truncated
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryStart
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function
abbrev Context := Rows × (ℚ × (ℚ × ℚ))
abbrev State := Context × Row

def rawPenalty (r : ℕ) (x : Rows × ℕ) : ℕ := 4*r*(x.2+1)
def rawGrad (r : ℕ) (x : Rows × ℕ) : ℕ := (x.1.head?.getD []).length*(x.1.length*rawPenalty r x)^2
def rawRate (r : ℕ) (x : Rows × ℕ) : ℚ := 1/(2*(r:ℚ)*(rawGrad r x:ℚ))
def rawSteps (r : ℕ) (x : Rows × ℕ) : ℕ := 8*r^2*rawGrad r x*x.2^2
def rawContext (r : ℕ) (x : Rows × ℕ) : Context := (x.1,(rawPenalty r x,(x.2,rawRate r x)))
def rawInitial (x : Rows × ℕ) : Row := (List.range (x.1.head?.getD []).length).map (fun i => if i=0 then (x.2:ℚ) else 0)
def update (s : State) : State := (s.1,Truncated.next s.1.1 s.2 s.1.2.1 s.1.2.2.1 s.1.2.2.2)

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryTrajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Polynomial Function

def value (s : State) : ℚ := Truncated.objective s.1.1 s.2 s.1.2.1
def choose (ss : List State) : State := selectMinimum value ss (([],(0,(0,0))),[])
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest

theorem entries_ofFn {n : ℕ} (y d : Fin n → ℚ) :
    entries (List.ofFn y) (List.ofFn d)=List.ofFn (fun i => (i.val,(y i,d i))) := by
  simp only [entries,Gaussian.ListOperation.zip_ofFn,List.length_ofFn,range_ofFn]

end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximationListProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.TruncatedLP.instDecidableValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
def assignments (ds xs : Rows) : Rows := (ds.zip xs).map (fun p => assignment p.1 p.2)
def nearestRows (ds : Rows) (ys : Row) : Rows := ds.map (Nearest.filling ys)
def finish (ds : Rows) (ys : Row) (H ρ : ℚ) : Output :=
  (opening ys ρ,assignments ds (nearestRows (Truncated.matrix ds H) ys))
theorem assignments_ofFn {n m : ℕ} (d x : Fin m → Fin n → ℚ) :
    assignments (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn (fun j => List.ofFn (x j)))=
      List.ofFn (fun j => List.ofFn (TruncatedLP.repairedAssignment d x j)) := by
  simp only [assignments,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,assignment,weights_ofFn,List.sum_ofFn]
  rfl

def encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) : Output :=
  (List.ofFn (ProjectedSubgradient.point a.opening),List.ofFn (fun j => List.ofFn (ProjectedSubgradient.point a.assignment[j.val])))

end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalListChecks
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Binary Binary.PolyProgram Function Finset

def valid (a : Output) (k : ℕ) : Bool :=
  a.1.all bounded && a.2.all (fun xs => dominated xs a.1) &&
    a.2.all (fun xs => decide (xs.sum=1)) && decide (a.1.sum ≤ (k:ℚ)+1)
def value (a : Output) (ds : Rows) : ℚ := ((a.2.zip ds).map (fun p => dot p.1 p.2)).sum

theorem valid_encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) (k : ℕ) :
    valid (encodeData a) k=decide (a.Valid k) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [valid,encodeData,Bool.and_eq_true,all_ofFn,bounded,dominated,Gaussian.ListOperation.zip_ofFn,
    decide_eq_true_eq,List.sum_ofFn,TruncatedLP.FractionalData.Valid,ProjectedSubgradient.point]
  tauto

theorem value_encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) (d : Fin m → Fin n → ℚ) :
    value (encodeData a) (List.ofFn (fun j => List.ofFn (d j)))=a.value d := by
  simp only [value,encodeData,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,dot,List.sum_ofFn,
    TruncatedLP.FractionalData.value,ProjectedSubgradient.point]

end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

 theorem state_iterate (x : Input) (t : ℕ) : State.step^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih]
    change (⟨x,advance x ((advance x)^[t] (x.U,∅))⟩ : State)=_
    simp only [Input.state,Function.iterate_succ_apply']

 theorem select_empty {n : ℕ} (t : ℕ) (R : Fin n → ℚ) (d : Fin n → Fin n → ℚ) (M : ℚ) : select d R M t ∅=∅ := by
  cases t <;> simp [select,Finset.not_nonempty_empty]
 theorem advance_result (x : Input) (t : ℕ) (s : Cut x) :
    ((advance x)^[t] s).2=s.2 ∪ select x.d x.R x.M t s.1 := by
  induction t generalizing s with
  | zero => simp only [Function.iterate_zero,Function.id_def,select,union_empty]
  | succ t ih =>
    rw [Function.iterate_succ_apply,ih]
    by_cases h : s.1.Nonempty
    · simp only [advance,dite_eq_left h,select]
      ext i
      simp only [mem_union,mem_insert]
      tauto
    · have he : s.1=∅ := not_nonempty_iff_eq_empty.mp h
      simp [advance,he,select_empty]

end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
def supplierView {f n : ℕ} (S : Data f n) : SupplierRaw :=
  (List.ofFn S.y,(List.ofFn (fun t => setView (S.P t)),(List.ofFn (fun t => setView (S.A t)),
    (List.ofFn S.p,(List.ofFn S.c,S.γ)))))

theorem ofFn_star {f n : ℕ} {α : Type} (F : SupplierStars.Star (Fin f) (Fin n) → α) :
    List.ofFn (fun i => F (index i)) =
    List.ofFn (fun i => F (.inl i)) ++
      ((List.ofFn (fun s => List.ofFn (fun t => F (.inr (.inl (s,t)))))).flatten ++
        List.ofFn (fun t => F (.inr (.inr t)))) := by
  conv_lhs => rw [List.ofFn_add]
  simp only [index,Equiv.trans_apply,Equiv.sumCongr_apply,finSum_symm_castLE,
    finSumFinEquiv_symm_apply_natAdd,Sum.map_inl,Sum.map_inr,Equiv.refl_apply]
  conv_lhs => arg 2; rw [List.ofFn_add]
  simp only [finSum_symm_castLE,
    finSumFinEquiv_symm_apply_natAdd,Sum.map_inl,Sum.map_inr,Equiv.refl_apply]
  rw [RoundingList.ofFn_product]

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_TargetSubsetProgram
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)

def Input.weighted (x : Input) : RoundingProgram.Input false :=
  ⟨x.n,fun _ => 1,initial x.D x.q,fun _ _ => by norm_num,initial_unit x.D x.feasible⟩
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedTerminalProgram
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

 theorem point_toList {n : ℕ} (p : Vector ℚ n) : p.toList=List.ofFn (RationalWeightedStep.point p) := by
  apply List.ext_getElem <;> intros <;> simp [RationalWeightedStep.point]

def bernoulliInput (x : Input true) : BInput := ⟨x.n,RationalWeightedStep.point x.p,x.feasible⟩

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedRoundProgram
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

def emptyInput : Input true := ⟨0,Fin.elim0,#v[],by simp,fun i => Fin.elim0 i⟩

end SignedRound
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
structure KernelInput where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  p : Vector ℚ m
  feasible : ∀ e, 0≤RationalWeightedStep.point p e ∧ RationalWeightedStep.point p e≤1

def KernelInput.star (x : KernelInput) : SparseStarActivation.Program.Input :=
  ⟨x.n,x.m,x.D,RationalWeightedStep.point x.p,x.feasible⟩
def KernelInput.bernoulli (x : KernelInput) : SparseBernoulli.Program.Input :=
  ⟨x.m,RationalWeightedStep.point x.p,x.feasible⟩
 theorem point_list {m : ℕ} (p : Vector ℚ m) : List.ofFn (RationalWeightedStep.point p)=p.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp [RationalWeightedStep.point]

structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  p : Vector ℚ m
  feasible : ∀ e, 0≤RationalWeightedStep.point p e ∧ RationalWeightedStep.point p e≤1
  c_unit : ∀ e, 0 ≤ c e ∧ c e≤1

def Input.signed (x : Input) : RoundingProgram.Input true :=
  ⟨x.m,SparseSignedPreparation.signed x.D x.c,x.p,by simp,x.feasible⟩

def dummy : KernelInput := ⟨0,0,Fin.elim0,#v[],fun i => Fin.elim0 i⟩

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseCounts.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev er := encodeList Nat.bits
abbrev et := encodeList er

end MetricKMedian.SparseCounts.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

structure Input where
  n : ℕ
  m : ℕ
  columns : Fin m → SparseIntegerLaw ((Fin n → ℕ))
structure Context where
  input : Input
  t : ℕ
abbrev T (c : Context) := SparseCounts.Table c.input.n c.input.m

def column (c : Context) : SparseIntegerLaw (Fin c.input.n → ℕ) :=
  if h : c.t < c.input.m then c.input.columns ⟨c.t,h⟩ else .dirac (fun _ => 0)
def update (c : Context) (G : T c) (S : (Fin c.input.n → ℕ)) : T c :=
  fun i => if i.val=c.t then S else G i

end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseCounts.Program
abbrev qr := encodeList Ratio.encode
abbrev qt := encodeList qr
abbrev eqi := encodePair (encodeList (fun _ : Unit => [])) qt

abbrev QInput.encode (x : QInput) := eqi x.raw

end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
def Input.signed (x : Input) : SparseSignedPreparation.Program.Input :=
  ⟨x.n,x.m,x.D,x.c,SparseGridRounding.fraction x.q,SparseGridRounding.fraction_unit x.q x.q_nonnegative,x.c_unit⟩
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
open SparseIntegerLaw.BinarySparse
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)

theorem index_inl {f n : ℕ} (i : Fin f) : (index (f:=f) (n:=n)).symm (.inl i)=Fin.castAdd (n*n+n) i := by
  apply (index (f:=f) (n:=n)).injective
  simp only [Equiv.apply_symm_apply,index,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply,Sum.map_inl,Equiv.refl_apply]

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_ScaleListProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

def guesses (ds : Rows) : Row :=
  ds.flatten.flatMap (fun q => if 0 < q then (Dyadic.powers ds.length).map (fun t => q*t) else [])

theorem guesses_mem {n m : ℕ} (d : Fin m → Fin n → ℚ) (q : ℚ) :
    q ∈ guesses (List.ofFn (fun j => List.ofFn (d j))) ↔ q ∈ Normalization.matrixGuesses d := by
  unfold guesses Normalization.matrixGuesses
  simp only [List.mem_flatMap,List.mem_flatten,mem_biUnion,mem_univ,true_and]
  constructor
  · rintro ⟨v,⟨xs,hxs,hv⟩,hq⟩
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    by_cases h : 0 < d j i
    · simp only [ite_eq_left h,List.length_ofFn,Dyadic.powers_eq,List.mem_map,List.mem_range] at hq
      obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hq
      exact ⟨(j,i),by simp only [ite_eq_left h,mem_image,mem_range]; exact ⟨t,ht,he⟩⟩
    · simp only [ite_eq_right h,List.not_mem_nil] at hq
  · rintro ⟨⟨j,i⟩,hq⟩
    by_cases h : 0 < d j i
    · simp only [ite_eq_left h,mem_image,mem_range] at hq
      obtain ⟨t,ht,rfl⟩ := hq
      refine ⟨d j i,⟨List.ofFn (d j),List.mem_ofFn.mpr ⟨j,rfl⟩,List.mem_ofFn.mpr ⟨i,rfl⟩⟩,?_⟩
      simp only [ite_eq_left h,List.length_ofFn,Dyadic.powers_eq,List.mem_map,List.mem_range]
      exact ⟨(2:ℚ)^t,⟨t,ht,rfl⟩,rfl⟩
    · simp only [ite_eq_right h,notMem_empty] at hq

end Scale
namespace Input

def zeroOutput (I : Input) : Repair.Output :=
  (List.replicate I.n 0,List.replicate I.m (List.replicate I.n 0))

end Input
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitRepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

def Input.rep (M : ℚ) (x : Input) : RationalRepresentatives.Program.Input :=
  ⟨x.j,x.U.V,x.U.dd,M,univ⟩

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end


