-- Prove2me | Definitions.Def_OAIQ035K073
-- name    : OAIQ035K073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:24:47.579091+00:00
-- url     : https://prove2.me/theorems/f6f2edd6-b6ed-4ee7-b910-74650a61c82d
-- title:
--   Definitions bundle OAIQ035K073 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 18 definitions and 8 theorems. The definitions and types are `OAI.MetricKMedian.InstanceProgram.nonzeroPseudoProgram`, `OAI.MetricKMedian.InstanceProgram.nonzeroRoundProgram`, `OAI.MetricKMedian.InstanceProgram.pseudoProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.masksProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.program`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanInputProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanRawPairProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanRawProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanTablesProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.tablesProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.program`, `OAI.MetricKMedian.Reduction.Program.valuesData`, `OAI.MetricKMedian.SparseOuterLaw.Program.program`, `OAI.MetricKMedian.SparsePrepared.Program.kernelsProgram`, `OAI.MetricKMedian.SparsePrepared.Program.outerInputProgram`, `OAI.MetricKMedian.SparsePrepared.Program.program`, `OAI.MetricKMedian.SparsePrepared.Program.weightsProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Preparation_SupplierScanProgram`, `KMedian_Programs_InstanceRoundProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Reduction_DeletionProgram`, `KMedian_Sparse_SparseBundleEncoding`, `KMedian_Sparse_SparseBundleLaw`, `KMedian_Sparse_SparseCardinalFixed`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseOuterReal`, `KMedian_Sparse_SparsePreparedBudget`, `KMedian_Sparse_SparsePreparedProbability`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K069`, `OAIQ035K070` and `OAIQ035K071` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K075`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K069
import Definitions.Def_OAIQ035K070
import Definitions.Def_OAIQ035K071

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalFixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.SparseCardinalRounding
open RationalWeightedStep

theorem zero_fixed {n : ℕ} (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) (hi : point p i=0)
    (a : Fin (round p).length) : point (round p).states[a.val] i=0 := by
  apply SparseIntegerLaw.zero_nonnegative (round p) (fun q => point q i)
    (fun b => ((SparseWeightedPartial.run_invariants (fun _ => 1)
      (fun _ => by norm_num) p hp n b).1 i).1)
    ((round_mean p i).trans hi) a
    (SparseWeightedPartial.run_positive _ _ _ _ a)

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
open RationalWeightedStep (point)
variable {n : ℕ}

theorem law_invariants (q : Fin n → ℚ) (K L : ℕ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ L) (hs : (∑ i, q i)=(K:ℚ)) :
    ∀ a : Fin (law q).length,
      (∑ i, (law q).states[a.val] i)=K ∧
      (∀ i, (law q).states[a.val] i ≤ L) ∧
      (∀ i, (law q).states[a.val] i=base q i ∨ (law q).states[a.val] i=base q i+1) := by
  intro a
  change Fin (SparseCardinalRounding.round (fraction q)).length at a
  have he := SparseIntegerLaw.map_states (SparseCardinalRounding.round (fraction q)) (count q) a
  change (law q).states[a.val]=_ at he
  rw [he]
  have hh := SparseCardinalRounding.round_invariants (fraction q) (fraction_unit q (fun i => (hq i).1))
    (K-∑ i,base q i) (fraction_sum q (fun i => (hq i).1) K hs) a
  refine ⟨?_,?_,?_⟩
  · have heq : (∑ i, (count q (SparseCardinalRounding.round (fraction q)).states[a.val] i:ℚ))=(K:ℚ) := by
      simp only [count_cast _ _ hh.1,sum_add_distrib,hh.2,
        Nat.cast_sub (base_sum_le q (fun i => (hq i).1) K hs),Nat.cast_sum]
      ring
    exact_mod_cast heq
  · intro i
    have hb : base q i ≤ L := by exact_mod_cast (Nat.floor_le (hq i).1).trans (hq i).2
    by_cases hi : point (SparseCardinalRounding.round (fraction q)).states[a.val] i=1
    · have hl : base q i < L := by
        by_contra hn
        have heq : base q i=L := le_antisymm hb (le_of_not_gt hn)
        have hz : point (fraction q) i=0 := by
          simp only [fraction,point,Vector.getElem_ofFn]
          have hh := Nat.floor_le (hq i).1
          change (base q i:ℚ) ≤ q i at hh
          have hh' := (hq i).2
          rw [heq] at hh ⊢
          linarith only [hh,hh']
        have hfixed := SparseCardinalRounding.zero_fixed (fraction q)
          (fraction_unit q (fun i => (hq i).1)) i hz a
        rw [hi] at hfixed
        norm_num at hfixed
      simpa only [count,ite_eq_left hi] using Nat.add_one_le_iff.mpr hl
    · simpa only [count,ite_eq_right hi,Nat.add_zero] using hb
  · intro i
    unfold count
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (Nat.add_zero _)

end MetricKMedian.SparseGridRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBundleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBundles
open Finset
variable {n m : ℕ}

theorem invariants (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ)) :
    ∀ a : Fin (law q).length, ∀ j,
      (∑ i,(law q).states[a.val] j i)=K j ∧
      (∀ i,(law q).states[a.val] j i ≤ L) ∧
      (∀ i,(law q).states[a.val] j i=SparseGridRounding.base (fun i => q i j) i ∨
        (law q).states[a.val] j i=SparseGridRounding.base (fun i => q i j) i+1) := by
  intro a j
  exact SparseCounts.run_columns (fun j => SparseGridRounding.law (fun i => q i j))
    (fun j S => (∑ i,S i)=K j ∧ (∀ i,S i ≤ L) ∧
      (∀ i,S i=SparseGridRounding.base (fun i => q i j) i ∨
        S i=SparseGridRounding.base (fun i => q i j) i+1))
    (fun j => SparseGridRounding.law_invariants (fun i => q i j) (K j) L (fun i => hq i j) (hs j))
    m le_rfl a j j.isLt

end MetricKMedian.SparseBundles
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBundleEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBundleEncoding
open Finset
variable {n m : ℕ}

theorem expectation (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (v : SparseCounts.Table n m → ℝ) :
    (law q).expect (fun ξ => v (decode q ξ)) =
      (SparseBundles.law q).realIndex.expect (fun a => v (SparseBundles.law q).states[a.val]) := by
  rw [law, FiniteLaw.expect_map]
  congr 1
  funext a
  rw [decode_encode q _ (fun j => (SparseBundles.invariants q K L hq hs a j).2.2)]

end MetricKMedian.SparseBundleEncoding

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

theorem activationCount_le (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) :
    activationCount D q (law D c q hc hq).states[a.val] e i ≤
      outsideCount q (law D c q hc hq).states[a.val] e := by
  by_cases hi : i∈D e
  · have hh := (budget D c q hc hq a).2.2.2.2.1 e i
    have he : (activationCount D q (law D c q hc hq).states[a.val] e i:ℚ) ≤
        (outsideCount q (law D c q hc hq).states[a.val] e:ℚ) := by
      rw [activationCount_cast,outsideCount_cast]
      simpa only [activation,ite_eq_left hi] using hh
    exact_mod_cast he
  · rw [activationCount_support D c q hc hq a e i hi]
    exact Nat.zero_le _

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

theorem nominalMass_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℝ) (e : Fin m) :
    (law D c q hc hq).realIndex.variance
      (fun a => nominalMass q g (law D c q hc hq).states[a.val] e) ≤ g * (g * (q e : ℝ)) := by
  have hv : (law D c q hc hq).realIndex.variance
      (fun a => (SparseSignedPreparation.nominalCount (base q) (law D c q hc hq).states[a.val] e : ℝ)) ≤
      (q e : ℝ) := by
    apply FiniteLaw.adjacent_variance _ _ (m := (base q e : ℝ)) (Nat.cast_nonneg _) ?_ ?_
    · intro a _
      rcases (budget D c q hc hq a).2.2.1 e with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    · rw [SparseIntegerLaw.realIndex_expect _ (fun z => SparseSignedPreparation.nominalCount (base q) z e), nominal_mean]
  simp only [nominalMass, FiniteLaw.variance_mul]
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hv (sq_nonneg g)

end MetricKMedian.SparseOuterLaw
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw SparseGridRounding
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem opening_le (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e)
    (a : Fin (SparseOuterLaw.law D c q hc hq).length) :
    opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] ≤
      (n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e)+3+
       ∑ j,discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j := by
  rw [raw_identity]
  have hh := (SparseOuterLaw.budget D c q hc hq a).2.2.2.2.2
  linarith only [hh]

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem opening_probability (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (g : ℚ)
    (δ : Fin n → ℝ) {γ B : ℝ} (hg : 0 < g) (hγ : 0 < γ)
    (heven : Even Δ) (hunit : g*(Δ:ℚ)=1) (hδ : ∀ j,0 ≤ δ j)
    (hmean : ∀ j,(g:ℝ)*(targetMean D q j:ℝ)=(1+γ)*δ j)
    (hsmall : ∀ j,(1+γ)*δ j ≤ 1/4)
    (hplan : (g:ℝ)*(((n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e):ℚ):ℝ)=
      B-γ*∑ j,δ j) :
    1-4*(g:ℝ)*(1+γ)/γ ≤ (SparseOuterLaw.law D c q hc hq).realIndex.prob (fun a =>
      (g:ℝ)*(opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val]:ℝ) ≤ B+3*(g:ℝ)) := by
  classical
  apply (SparseOuterLaw.clipping_budget D c q g hc hq δ hg.le hγ hδ hmean hsmall).trans
  apply FiniteLaw.prob_mono
  intro a ha
  have hh0 := opening_le D c q Δ hc hq a
  have hh : (opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val]:ℝ) ≤
      (((n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e):ℚ):ℝ)+3+
      ∑ j,(discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ) := by
    exact_mod_cast hh0
  have hhg := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ g by exact_mod_cast hg.le)
  have hdiscard : (g:ℝ)*(∑ j,(discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ))=
      ∑ j,((deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ)-
        min (deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ) (1/2)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun j _ => discarded_mass D q Δ _ j hg heven hunit)
  rw [mul_add,mul_add,hplan,hdiscard] at hhg
  linarith only [hhg,ha]

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
noncomputable def program : PolyProgram Input.encode (enc : Data SparseSignedPreparation.Program.StateRaw → List Bool) Input.result :=
  (signedProgram.comp SparseSignedPreparation.Program.program).congr _ (fun _ => rfl)
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)
noncomputable def outerInputProgram : PolyProgram Input.encode SparseOuterLaw.Program.Input.encode Input.outer :=
  outerData_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [outerData,Input.raw,Input.base,List.map_const',List.length_ofFn,
      SparseOuterLaw.Program.Input.encode,SparseOuterLaw.Program.Input.raw,Input.outer])
noncomputable def kernelsProgram : PolyProgram Input.encode (encodeList KernelInput.encode) Input.kernels := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (r.fanout (outerInputProgram.comp SparseOuterLaw.Program.program) |>.comp kernelRows_poly.program).recode id
    (fun _ => rfl) (fun x => by
      change encodeList enc (kernelRows (x.raw,SparseOuterLaw.Program.Input.result x.outer))=_
      simp only [kernelRows,SparseOuterLaw.Program.Input.result,states_list,List.map_ofFn,Function.comp_def]
      change encodeList enc (List.ofFn (fun i => (x.ker i).raw))=encodeList KernelInput.encode x.kernels
      rw [List.ofFn_comp',RoundingProgram.encodeList_map]; rfl)
noncomputable def weightsProgram : PolyProgram Input.encode el (fun x => (SparseIntegerLaw.BinarySparse.raw x.μ).1) :=
  (outerInputProgram.comp SparseOuterLaw.Program.program |>.comp (fst el (encodeList enc))).congr _ (fun _ => rfl)
noncomputable def program : PolyProgram Input.encode (enc : Data PreparedRaw → List Bool) Input.result :=
  (weightsProgram.fanout (kernelsProgram.comp (kernelProgram.listMap dummy)) |>.comp bindData_poly.program).congr _ bind_result
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierPreparationProgram
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
noncomputable def tablesProgram : PolyProgram Input.encode (enc : List (List ℕ) → List Bool)
    (fun x => (x.S.tables qR).map List.ofFn) := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let states := preparedInputProgram qR |>.comp SparsePrepared.Program.program |>.comp (snd el (encodeList enc))
  exact (r.fanout states |>.comp (tablesData_poly qR).program).congr _ (fun x => by
    simp only [Function.comp_def,tablesData,SparsePrepared.Program.Input.result,List.map_map]
    change ((x.S.law qR).states.toList.map (fun z => countsData qR (x.raw,SparsePrepared.Program.view z)))=_
    simp only [countsData_view,Data.tables,List.map_map,Function.comp_def])
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
noncomputable def scanTablesProgram : PolyProgram ScanInput.encode (enc : List (List ℕ) → List Bool)
    (fun x => (x.S.tables qR).map List.ofFn) :=
  (scanPrepProgram.comp (tablesProgram qR)).congr _ (by intro x; simp only [Function.comp_def,ScanInput.prep])
noncomputable def scanRawPairProgram : PolyProgram ScanInput.encode (enc : ScanRaw × List (List ℕ) → List Bool)
    (fun x => (x.raw,(x.S.tables qR).map List.ofFn)) :=
  ((identity enc).recode ScanInput.raw (fun _ => rfl) (fun _ => rfl)).fanout (scanTablesProgram qR)
noncomputable def scanRawProgram : PolyProgram ScanInput.encode enc
    (fun x => scanData (x.raw,(x.S.tables qR).map List.ofFn)) :=
  scanRawPairProgram qR |>.comp scanData_poly.program
noncomputable def scanInputProgram : PolyProgram ScanInput.encode FixedBatch.RationalParameters.PreparedScanProgram.Input.encode (ScanInput.scan qR) :=
  (scanRawProgram qR).recode id (fun _ => rfl) (fun x => congrArg enc (scanData_view qR x))
noncomputable def scanProgram : PolyProgram ScanInput.encode (enc : Table → List Bool)
    (fun x => ((x.S.scan qR x.df x.dc x.budget).map setView).toList) :=
  (scanInputProgram qR |>.comp (FixedBatch.RationalParameters.PreparedScanProgram.program qR)).congr _ (by
    intro x
    simp only [Function.comp_def,FixedBatch.RationalParameters.PreparedScanProgram.Input.result,ScanInput.scan,Data.scan]
    rfl)
end MetricKMedian.Preparation.RationalSuppliers.Program
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
noncomputable def program : PolyProgram Input.encode (enc : Table → List Bool) (Input.result p) :=
  (supplierInputProgram p |>.comp (RationalSuppliers.Program.scanProgram p.round)).congr _ (by
    intro x
    simp only [Function.comp_def,Input.result,Input.sup,RationalUnitInput.scan])
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.FractionalRefinement.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
attribute [local irreducible] RationalUnitInput.ScanProgram.Input.result
variable {η τ : ℝ} (p : RationalAllParameters η τ)
noncomputable def masksProgram : PolyProgram Input.encode (enc : Table → List Bool)
    (fun z => RationalUnitInput.ScanProgram.Input.result p z.unit) :=
  @PolyProgram.comp Input RationalUnitInput.ScanProgram.Input Table Input.encode
    RationalUnitInput.ScanProgram.Input.encode enc Input.unit (RationalUnitInput.ScanProgram.Input.result p)
    unitProgram (RationalUnitInput.ScanProgram.program p)
noncomputable def program : PolyProgram Input.encode (enc : Table → List Bool) (Input.result p) :=
  (PolyProgram.comp (g:=imageData)
    (((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.comp (fst enc enc)).fanout (masksProgram p))
    imageData_poly.program).congr _ (imageData_view p)
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceRoundProgram
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
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ)
attribute [local irreducible] FractionalRefinement.scan Instance.computedFractional
noncomputable def nonzeroRoundProgram : PolyProgram nzEncode (enc : Table → List Bool)
    (fun I => ((I.val.nonzeroRound I.property r hr p C).map setView).toList) :=
  ((((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl)).fanout
    ((scanInputProgram r hr C).comp (FractionalRefinement.ScanProgram.program p))).comp imageData_poly.program).congr
      _ (imageData_view r hr p C)

noncomputable def nonzeroPseudoProgram : PolyProgram nzEncode (enc : Row → List Bool)
    (fun I => setView ((I.val.nonzeroRound I.property r hr p C).getD {I.val.facilities.min' I.val.facilities_nonempty})) :=
  ((((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl)).fanout
    (nonzeroRoundProgram r hr p C)).comp fallbackData_poly.program).congr _ (by
      intro I
      simp only [Function.comp_def,fallbackData,id_eq,singletonData_view]
      cases I.val.nonzeroRound I.property r hr p C <;> rfl)
noncomputable def pseudoProgram : PolyProgram encode (enc : Row → List Bool)
    (fun I => setView (I.computedPseudo r hr p C)) :=
  (dependentIfTotal Instance.zeroTest zeroTestProgram
    (fun I h => setView ((I.nonzeroRound h r hr p C).getD {I.facilities.min' I.facilities_nonempty}))
    (fun I _ => setView I.zeroOutput) (nonzeroPseudoProgram r hr p C)
    (zeroOutputProgram.recode Subtype.val (fun _ => rfl) (fun _ => rfl))).congr _ (by
      intro I
      unfold Instance.computedPseudo
      split_ifs <;> rfl)
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration

def valuesData (c : ℕ) (x : Raw × Row) : List ℚ :=
  (choicesRaw c x.2).flatMap (fun D => (Preparation.RationalUnitInput.Program.ranks x.2).map (fun i =>
    costData (x.1,erase (i,diff (x.2,D)))-costData (x.1,diff (x.2,D))))
end MetricKMedian.Reduction.Program
end

end OAI
end


