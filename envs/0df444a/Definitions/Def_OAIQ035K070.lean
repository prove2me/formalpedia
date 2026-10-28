-- Prove2me | Definitions.Def_OAIQ035K070
-- name    : OAIQ035K070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:21:12.503183+00:00
-- url     : https://prove2.me/theorems/e595083a-b205-4939-baca-4f7a6b88125d
-- title:
--   Definitions bundle OAIQ035K070 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 18 definitions and 15 theorems. The definitions and types are `OAI.MetricKMedian.InstanceProgram.zeroOutputProgram`, `OAI.MetricKMedian.InstanceProgram.zeroTestProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.supplierInputProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.suppliersProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.unitProgram`, `OAI.MetricKMedian.RoundingProgram.SignedRound.boundProgram`, `OAI.MetricKMedian.RoundingProgram.SignedRound.partialInputsProgram`, `OAI.MetricKMedian.RoundingProgram.SignedRound.program`, `OAI.MetricKMedian.RoundingProgram.Terminal.program`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.program`, `OAI.MetricKMedian.SparseSignedPreparation.Program.bernoulliProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.kernelProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.kernelsProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.program`, `OAI.MetricKMedian.SparseSignedPreparation.Program.weightsProgram`, `OAI.MetricKMedian.SparseStarActivation.Program.graphProgram`, `OAI.MetricKMedian.SparseStarActivation.Program.program`, `OAI.MetricKMedian.SparseTargetSubset.Program.program`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Programs_InstanceZeroProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitGeometryProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedRoundProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Rounding_TargetSubsetProgram`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparseOuterReal`, `KMedian_Sparse_SparseSignedBudget`, `KMedian_Sparse_SparseStarActivation`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K065`, `OAIQ035K066` and `OAIQ035K067` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K073` and `OAIQ035K074`; the proofs of `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all` and `OAI.MetricKMedian.Taper.physical_sparse_graph`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K065
import Definitions.Def_OAIQ035K066
import Definitions.Def_OAIQ035K067

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

theorem round_mean (p : Vector ℚ n) (i : Fin n) :
    (round p).moment (fun q => point q i)=point p i :=
  SparseWeightedPartial.run_mean _ _ p n i

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseStarActivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

theorem error (D : Fin m → Finset (Fin n)) (q c : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (hsmall : (univ.filter (fun e => 0 < q e ∧ q e < 1)).card ≤ 1)
    (a : Fin (law D q).length) :
    (∑ e, (c e*(upper (q e)-q e)+((D e).card:ℚ)*q e-
      (((law D q).states[a.val] e).card:ℚ))) ≤ 2 := by
  have hq0 : ∀ e, (0:ℝ) ≤ (q e:ℝ) := fun e => by exact_mod_cast (hq e).1
  have hq1 : ∀ e, (q e:ℝ) ≤ 1 := fun e => by exact_mod_cast (hq e).2
  have hc0 : ∀ e, (0:ℝ) ≤ (c e:ℝ) := fun e => by exact_mod_cast (hc e).1
  have hc1 : ∀ e, (c e:ℝ) ≤ 1 := fun e => by exact_mod_cast (hc e).2
  have hs : (MarginalRounding.fractional (fun e => (q e:ℝ))).card ≤ 1 := by
    unfold MarginalRounding.fractional
    have he : (univ.filter (fun e => 0 < (q e:ℝ) ∧ (q e:ℝ)<1))=
        univ.filter (fun e => 0 < q e ∧ q e<1) := by
      apply filter_congr
      intro e _
      norm_cast
    rwa [he]
  have hh := Preparation.exceptional_raw_error D (fun e => (q e:ℝ)) (fun e => (c e:ℝ))
    (law D q).states[a.val] hq0 hq1 hc0 hc1 hs (fun e => ⟨by
      exact_mod_cast (columns D q hq a e).2.1,
      fun he => (columns D q hq a e).2.2.1 (by exact_mod_cast he),
      fun he => (columns D q hq a e).2.2.2 (by exact_mod_cast he)⟩)
  have hu : ∀ e, Preparation.upperBit (q e:ℝ)=(upper (q e):ℝ) := by
    intro e
    simp only [Preparation.upperBit,upper]
    norm_cast
  simp_rw [hu] at hh
  exact_mod_cast hh

end MetricKMedian.SparseStarActivation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

theorem kernel_budget (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (q : Vector ℚ m) (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hsmall : (fractional q).card ≤ 1) :
    ∀ a : Fin (kernel D q hq).length,
      BudgetSpec D c b ((∑ e, signed D c e*((b e:ℚ)+point q e))+2)
        (kernel D q hq).states[a.val] := by
  unfold kernel
  apply SparseIntegerLaw.prod_property (SparseStarActivation.law D (point q))
    (SparseBernoulli.run (d := 2) (point q) hq m) (fun S ω => (q,S,ω))
    (BudgetSpec D c b _)
  intro a d
  dsimp only [BudgetSpec]
  refine ⟨fun e => (SparseStarActivation.columns D (point q) hq a e).1,?_,?_,?_,?_,?_⟩
  · intro e
    dsimp only [outside,SparseStarActivation.upper]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (add_zero _)
  · intro e
    dsimp only [nominalCount,SparseBernoulli.flag]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (add_zero _)
  · intro e
    dsimp only [nominalCount,outside]
    rw [add_le_add_iff_left]
    by_cases he : 0 < point q e
    · simp only [SparseStarActivation.upper,ite_eq_left he,SparseBernoulli.flag]
      split_ifs <;> norm_num
    · have hz : point q e=0 := le_antisymm (le_of_not_gt he) (hq e).1
      have hh := SparseBernoulli.fixed (point q) hq d e (Or.inl hz)
      rw [hh,hz]
      simp only [SparseStarActivation.upper,lt_self_iff_false,ite_false,le_refl]
  · intro e i
    dsimp only [outside]
    rw [add_le_add_iff_left]
    exact SparseStarActivation.upper_domination D (point q) hq a e i
  · have hh := SparseStarActivation.error D (point q) c hq hc hsmall a
    have he : raw D c b (q,(SparseStarActivation.law D (point q)).states[a.val],
        (SparseBernoulli.run (d := 2) (point q) hq m).states[d.val])=
        (∑ e, signed D c e*((b e:ℚ)+point q e))+
        ∑ e, (c e*(SparseStarActivation.upper (point q e)-point q e)+
          ((D e).card:ℚ)*point q e-
          (((SparseStarActivation.law D (point q)).states[a.val] e).card:ℚ)) := by
      unfold raw
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro e _
      dsimp only [raw,outside,signed]
      ring
    rw [he]
    linarith only [hh]

theorem law_budget (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (p : Vector ℚ m) (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) :
    ∀ a : Fin (law D c p hp hc).length,
      BudgetSpec D c b ((∑ e, signed D c e*((b e:ℚ)+point p e))+3)
        (law D c p hp hc).states[a.val] := by
  unfold law
  apply SparseIntegerLaw.bindIndexed_property _ _ (BudgetSpec D c b _)
  intro a d
  let hu : ∀ e, 0 < signed D c e → signed D c e ≤ 1 := fun e _ =>
    (sub_le_self _ (Nat.cast_nonneg _)).trans (hc e).2
  have ha := SparseSignedRounding.round_invariants (signed D c) p hp hu a
  have hh := kernel_budget D c b (SparseSignedRounding.round (signed D c) p hp).states[a.val]
    ha.1 hc ha.2.1 d
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,?_⟩
  have hb : (∑ e, signed D c e*((b e:ℚ)+point (SparseSignedRounding.round (signed D c) p hp).states[a.val] e)) ≤
      (∑ e, signed D c e*((b e:ℚ)+point p e))+1 := by
    simp only [mul_add,sum_add_distrib]
    linarith only [ha.2.2]
  exact hh.2.2.2.2.2.trans (by linarith only [hb])

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem budget (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) :
    ∀ a : Fin (law D c q hc hq).length,
      SparseSignedPreparation.BudgetSpec D c (base q)
        ((∑ e,SparseSignedPreparation.signed D c e*q e)+3) (law D c q hc hq).states[a.val] := by
  have hh := SparseSignedPreparation.law_budget D c (base q) (fraction q)
    (SparseGridRounding.fraction_unit q hq) hc
  simpa only [fraction_identity] using hh

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activationCount_support (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) (hi : i∉D e) :
    activationCount D q (law D c q hc hq).states[a.val] e i=0 := by
  have hh : i∉(law D c q hc hq).states[a.val].2.1 e := fun hh => hi ((budget D c q hc hq a).1 e hh)
  simp only [activationCount,ite_eq_right hi,ite_eq_right hh,Nat.add_zero]

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem nominalMass_cap (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) {g : ℝ} (hg : 0 ≤ g)
    (a : Fin (law D c q hc hq).length) (e : Fin m) :
    nominalMass q g (law D c q hc hq).states[a.val] e ≤
      g * (outsideCount q (law D c q hc hq).states[a.val] e : ℝ) := by
  apply mul_le_mul_of_nonneg_left _ hg
  have h := (budget D c q hc hq a).2.2.2.1 e
  rw [← outsideCount_cast] at h
  exact_mod_cast h

end MetricKMedian.SparseOuterLaw
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitGeometryProgram
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

 theorem geometryData_view {f j : ℕ} (U : RationalUnitInput f j) (M : ℚ) :
    geometryData (view U,setView (U.representatives M))=
      RationalBundles.Program.view (fun t u => U.dd (U.ridx M t) (U.ridx M u))
        (fun t a => U.dc (U.ridx M t) a) (fun t => U.F (U.ridx M t)) U.y := by
  unfold geometryData
  rw [ranks_view]
  simp only [view,ridx,pullbackMatrix_view,pickRows_view,setView,RationalBundles.Program.view]
  rfl

 theorem suppliersData_view {f j : ℕ} (U : RationalUnitInput f j) {X : Type} [PseudoMetricSpace X]
    (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ) :
    suppliersData p.δ p.γ (geometryData (view U,setView (U.representatives p.M)))=
      RationalSuppliers.Program.supplierView (U.suppliers R p) := by
  rw [geometryData_view]
  unfold suppliersData
  rw [RationalBundles.Program.bundlesData_view,RationalBundles.Program.missingData_view]
  simp only [RationalBundles.Program.view,RationalBundles.Program.massData_view]
  rfl

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceZeroProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
open Completion.Rational.BestProgram (card card_view)
 theorem subsetRaw_view {n : ℕ} (S T : Finset (Fin n)) : subsetRaw (setView S,setView T)=decide (S⊆T) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subsetRaw,setView,Gaussian.ListOperation.zip_ofFn,List.all_eq_true,List.mem_ofFn,Bool.or_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_true_eq]
  constructor
  · intro h i hi
    have hh : i∉S ∨ i∈T := by simpa only [decide_eq_false_iff_not,decide_eq_true_eq] using h _ ⟨i,rfl⟩
    exact hh.resolve_left (not_not_intro hi)
  · intro h z hz
    obtain ⟨i,rfl⟩ := hz
    by_cases hi : i∈S
    · exact Or.inr (by simpa only [decide_eq_true_eq] using h hi)
    · exact Or.inl (by simpa only [decide_eq_false_iff_not] using hi)

 theorem zeroTestData_view (I : Instance) : zeroTestData (view I)=decide I.zeroTest := by
  apply Bool.eq_iff_iff.mpr
  simp only [zeroTestData,view,subsetRaw_view,card_view,Bool.and_eq_true,decide_eq_true_eq]
  rfl
noncomputable def zeroTestProgram : PolyProgram encode encodeBool (fun I => decide I.zeroTest) :=
  zeroTestData_poly.program.recode view (fun _ => rfl) (fun I => congrArg encodeBool (zeroTestData_view I))

 theorem singletonRaw_view {n : ℕ} (S : Finset (Fin n)) (a : Fin n) : singletonRaw (setView S,a.val)=setView {a} := by
  simp only [singletonRaw,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,mem_singleton,Fin.ext_iff]
 theorem singletonData_view (I : Instance) : singletonData (view I)=setView {I.facilities.min' I.facilities_nonempty} := by
  unfold singletonData view
  rw [first_view,singletonRaw_view]
 theorem zeroOutputData_view (I : Instance) : zeroOutputData (view I)=setView I.zeroOutput := by
  unfold zeroOutputData Instance.zeroOutput
  change (if (setView I.clients).any id then setView I.clients else singletonData (view I))=_
  rw [Completion.Rational.PackingProgram.any_view]
  simp only [decide_eq_true_eq]
  split_ifs
  · rfl
  · exact singletonData_view I
noncomputable def zeroOutputProgram : PolyProgram encode (enc : Row → List Bool) (fun I => setView I.zeroOutput) :=
  zeroOutputData_poly.program.recode view (fun _ => rfl) (fun I => congrArg enc (zeroOutputData_view I))
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_LastFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

noncomputable def program : PolyProgram Input.encode RoundingProgram.State.encode result :=
  (runProgram false |>.comp lastProgram |>.comp (compressProgram false)).congr _ (fun _ => rfl)
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_TargetSubsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.er) Input.result := by
  let p : PolyProgram Input.encode RoundingProgram.Input.encode Input.weighted :=
    prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepare_input x))
  let get : PolyProgram RoundingProgram.State.encode (ed RoundingProgram.erow)
      (fun x : RoundingProgram.State false => RoundingProgram.vectorData x.μ) :=
    (snd RoundingProgram.erow (ed RoundingProgram.erow)).recode RoundingProgram.State.raw
      RoundingProgram.State.encode_raw (fun _ => rfl)
  let post : PolyProgram (ed RoundingProgram.erow) (ed SparseGraph.ListOperation.er)
      (fun x : Data (List ℚ) => (x.1,x.2.map SparseCardinalRounding.Program.selectedRow)) := by
    apply Poly.program
    apply pair
    · fun_prop
    · apply list_map <;> fun_prop
  exact (p.comp RoundingProgram.WeightedRound.program |>.comp get |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,Input.result,law,SparseGraph.Program.columnRaw,SparseIntegerLaw.map,RoundingProgram.vectorData,
      Vector.toList_map,List.map_map,SparseCardinalRounding.Program.selectedRow_eq]
    rfl)
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)
noncomputable def graphProgram : PolyProgram Input.encode SparseGraph.Program.Input.encode Input.graph := by
  let n : PolyProgram Input.encode enc (fun x : Input => x.raw.1) :=
    (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let columns := columnsProgram.comp (SparseTargetSubset.Program.program.listMap dummy)
  exact (n.fanout columns).recode id (fun _ => rfl) (fun x => by
    change SparseGraph.Program.ei (x.raw.1,x.columns.map SparseTargetSubset.Program.Input.result)=_
    simp only [Input.columns,List.map_ofFn,Function.comp_def]
    rfl)

noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et) Input.result := by
  let get : PolyProgram SparseGraph.Program.State.encode (ed SparseGraph.ListOperation.et)
      (fun x : SparseGraph.Program.State => (x.raw SparseGraph.Program.view).2) :=
    (snd SparseGraph.Program.Context.encode (ed SparseGraph.ListOperation.et)).recode
      (SparseIntegerLaw.DependentProgram.Bundle.raw SparseGraph.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (graphProgram.comp SparseGraph.Program.runStateProgram |>.comp get).congr _ (fun _ => rfl)
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedTerminalProgram
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

noncomputable def program : PolyProgram Input.encode (ed erow) result := by
  let bs := bernoulliInputProgram.comp (SparseBernoulli.Program.runStateProgram 2)
  let bl := bs.comp (SparseIntegerLaw.DependentProgram.lawProgram
    SparseBernoulli.Program.Context.encode ber SparseBernoulli.Program.view)
  let rows := bs.comp (SparseIntegerLaw.DependentProgram.statesProgram
    SparseBernoulli.Program.Context.encode ber SparseBernoulli.Program.view)
  let ctx : PolyProgram Input.encode (encodePair erow erow) (@Input.raw true) :=
    (PolyProgram.identity _).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  let mapped := (ctx.fanout rows).comp (boolState_poly.program.listMapWith [] [])
  exact (bl.fanout mapped).congr _ (fun x => by
    simp only [result,RationalSignedTerminal.terminal,SparseIntegerLaw.map,Vector.toList_map,List.map_map]
    dsimp only [Function.comp_def,bernoulliInput,SparseBernoulli.Program.Input.state,
      SparseBernoulli.Program.view,Input.raw]
    simp only [List.map_map,Function.comp_def,boolState_list])

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

noncomputable def partialInputsProgram : PolyProgram Input.encode (encodeList Input.encode) partialInputs := by
  let inputctx := (fst erow erow).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  let part :=  runProgram true
  let rows := part.comp (statesProgram true)
  let raw := (inputctx.fanout rows).comp ((PolyProgram.identity (encodePair erow erow)).listMapWith [] ([],[]))
  exact raw.recode id (fun _ => rfl) (fun x => by
    change encodeList (encodePair erow erow)
      (((x.run x.n).μ.states.toList.map Vector.toList).map (fun p => (List.ofFn x.β,p)))=_
    simp only [states_list,List.map_ofFn,Function.comp_def]
    change encodeList (encodePair erow erow) (List.ofFn fun i =>
      (Input.raw (partialInput x i)))=encodeList Input.encode (List.ofFn (partialInput x))
    rw [List.ofFn_comp',encodeList_map])

noncomputable def boundProgram : PolyProgram Input.encode State.encode boundState := by
  let part :=  runProgram true
  let law := part.comp ((snd erow (ed erow)).comp (fst el (encodeList erow)) |>.recode (@State.raw true) State.encode_raw (fun _ => rfl))
  let kernels := partialInputsProgram.comp (Terminal.program.listMap emptyInput)
  let bound := (law.fanout kernels).comp SparseIntegerLaw.BinarySparse.bindData_poly.program
  let β := (fst erow erow).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  exact (β.fanout bound).recode id (fun _ => rfl) (fun x => by
    rw [← State.encode_raw]
    change encodePair erow (ed erow) (List.ofFn x.β,
      bindData (((SparseSignedPartial.run x.β x.p x.n).law.denominator,
        List.ofFn (SparseSignedPartial.run x.β x.p x.n).law.numerator),
        (partialInputs x).map Terminal.result))=_
    simp only [partialInputs,List.map_ofFn,Function.comp_def]
    change encodePair erow (ed erow) (List.ofFn x.β,
      bindData ((raw (SparseSignedPartial.run x.β x.p x.n)).1,
        List.ofFn (fun i => ((raw (SparseSignedRounding.kernel x.β x.p x.feasible i)).1,
          (SparseSignedRounding.kernel x.β x.p x.feasible i).states.toList.map Vector.toList))))=_
    rw [bindData_raw]
    rfl)

noncomputable def program : PolyProgram Input.encode State.encode result :=
  (boundProgram.comp (compressProgram true)).congr _ (fun _ => rfl)

end SignedRound
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
noncomputable def bernoulliProgram : PolyProgram KernelInput.encode (ed SparseBernoulli.Program.er)
    (fun x => (((SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.denominator,
      List.ofFn (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.numerator),
      (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).states.toList.map List.ofFn)) := by
  let get : PolyProgram SparseBernoulli.Program.State.encode (ed SparseBernoulli.Program.er)
      (fun x : SparseBernoulli.Program.State => (x.raw SparseBernoulli.Program.view).2) :=
    (snd SparseBernoulli.Program.Context.encode (ed SparseBernoulli.Program.er)).recode
      (SparseIntegerLaw.DependentProgram.Bundle.raw SparseBernoulli.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (bernoulliInputProgram.comp (SparseBernoulli.Program.runStateProgram 2) |>.comp get).congr _ (fun _ => rfl)

noncomputable def kernelProgram : PolyProgram KernelInput.encode (enc : Data StateRaw → List Bool) KernelInput.result := by
  let p : PolyProgram KernelInput.encode enc (fun x : KernelInput => x.p.toList) :=
    ((snd enc enc).comp (snd enc enc)).recode KernelInput.raw (fun _ => rfl) (fun _ => rfl)
  exact (p.fanout ((starInputProgram.comp SparseStarActivation.Program.program).fanout bernoulliProgram
    |>.comp prodData_poly.program) |>.comp attach_poly.program).congr _ kernel_raw

noncomputable def kernelsProgram : PolyProgram Input.encode (encodeList KernelInput.encode) Input.kernels := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let s := signedInputProgram.comp RoundingProgram.SignedRound.program
  let sr : PolyProgram RoundingProgram.State.encode enc (RoundingProgram.State.raw (s:=true)) :=
    (identity enc).recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun _ => rfl)
  exact (r.fanout (s.comp sr) |>.comp inputRows_poly.program).recode id (fun _ => rfl) (fun x => by
    change encodeList enc (inputRows (x.raw,(RoundingProgram.SignedRound.result x.signed).raw))=_
    simp only [inputRows,RoundingProgram.State.raw,states_list,List.map_ofFn,
      Function.comp_def]
    change encodeList enc (List.ofFn (fun i => (x.ker i).raw))=encodeList KernelInput.encode x.kernels
    rw [List.ofFn_comp',encodeList_map]; rfl)

noncomputable def weightsProgram : PolyProgram Input.encode el (fun x => (SparseIntegerLaw.BinarySparse.raw x.μ).1) := by
  let weights : PolyProgram RoundingProgram.State.encode el (fun x : RoundingProgram.State true => (x.raw).2.1) :=
    ((snd enc enc).comp (fst enc enc)).recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun _ => rfl)
  exact (signedInputProgram.comp RoundingProgram.SignedRound.program |>.comp weights).congr _ (fun _ => rfl)
noncomputable def program : PolyProgram Input.encode (enc : Data StateRaw → List Bool) Input.result :=
  (weightsProgram.fanout (kernelsProgram.comp (kernelProgram.listMap dummy)) |>.comp bindData_poly.program).congr _ bind_result

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Preparation.RationalUnitInput.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open Program
variable {η τ : ℝ} (p : RationalAllParameters η τ)
 theorem postData_view (x : Input) :
    postData (x.raw,suppliersData p.δ p.γ (geometryData (view x.U,setView (x.U.representatives p.M))))=(x.sup p).raw := by
  let := x.metric
  unfold postData
  rw [suppliersData_view x.U x.R p]
  rfl
noncomputable def unitProgram : PolyProgram Input.encode Program.Input.encode Input.unit :=
  (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def suppliersProgram : PolyProgram Input.encode enc
    (fun x => suppliersData p.δ p.γ (geometryData (view x.U,setView (x.U.representatives p.M)))) :=
  (unitProgram.comp (Program.supplierRawProgram p)).congr _ (fun _ => rfl)
noncomputable def supplierInputProgram : PolyProgram Input.encode RationalSuppliers.Program.ScanInput.encode (Input.sup p) :=
  (((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.fanout (suppliersProgram p)).comp postData_poly.program).recode
    id (fun _ => rfl) (fun x => congrArg enc (postData_view p x))
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end


