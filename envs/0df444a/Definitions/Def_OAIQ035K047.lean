-- Prove2me | Definitions.Def_OAIQ035K047
-- name    : OAIQ035K047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:06:10.319265+00:00
-- url     : https://prove2.me/theorems/416f411d-9022-43e5-be01-cc9ff72e8093
-- title:
--   Definitions bundle OAIQ035K047 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 45 definitions and 8 theorems. The definitions and types are `OAI.MetricKMedian.Binary.MatrixList.transposeProgram`, `OAI.MetricKMedian.Binary.PolyProgram.listEraseIdx`, `OAI.MetricKMedian.Binary.PolyProgram.listInsertAt`, `OAI.MetricKMedian.Binary.PolyProgram.listMapTotal`, `OAI.MetricKMedian.Binary.PolyProgram.listZipWith`, `OAI.MetricKMedian.FixedBatch.RationalParameters.countCandidates`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundList`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted`, `OAI.MetricKMedian.FixedBatch.RationalParameters.tree`, `OAI.MetricKMedian.Gaussian.ListOperation.pivotProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.encode`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.countProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.dimProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.ed`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.featuresProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.lawProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.rawProgram`, `OAI.MetricKMedian.LPBinary.Program.maxFold`, `OAI.MetricKMedian.LPBinary.Program.minFold`, `OAI.MetricKMedian.LPBinary.Program.minimumProgram`, `OAI.MetricKMedian.MaskProgram.maxFold`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.law`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.law`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.inputs`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.law`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.ctxInputs`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.ctxLaw`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.law`, `OAI.MetricKMedian.RationalPhysicalKernel.graphLaw`, `OAI.MetricKMedian.RationalPhysicalKernel.histories`, `OAI.MetricKMedian.RationalPhysicalKernel.step`, `OAI.MetricKMedian.RoundingProgram.Input.run`, `OAI.MetricKMedian.RoundingProgram.State.compress`, `OAI.MetricKMedian.RoundingProgram.State.encode`, `OAI.MetricKMedian.RoundingProgram.State.step`, `OAI.MetricKMedian.SparseBernoulli.Program.State`, `OAI.MetricKMedian.SparseEnumeratedGraph.law`, `OAI.MetricKMedian.SparseGraph.Program.Input.start`, `OAI.MetricKMedian.SparseGraph.Program.Input.state` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_BinaryListIndex`, `KMedian_Binary_BinaryListMapTotal`, `KMedian_Binary_BinaryListZip`, `KMedian_Binary_BinaryMatrix`, `KMedian_Compression_CompressionBinaryProgram`, `KMedian_Compression_CompressionBounds`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_ComputedCompression`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Geometry_RationalGridRound`, `KMedian_Geometry_RationalHistorySelection`, `KMedian_Geometry_RationalParameterizedHistory`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_LPMinimumSelection`, `KMedian_Preparation_RationalPreparedScan`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_MaximumProgram`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Sparse_SparseEnumeratedGraph`, `KMedian_Sparse_SparseGraphLaw`, `KMedian_Sparse_SparseIterationHeight`, `KMedian_Sparse_SparseListTrim`, `KMedian_Sparse_SparseSignedPartial`.
--
--   **Imports.** It imports the bundles `OAIQ035K038`, `OAIQ035K039`, `OAIQ035K040` and `OAIQ035K041` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K050`, `OAIQ035K051`, `OAIQ035K052`, `OAIQ035K053`, `OAIQ035K058` and `OAIQ035K062`; the statements `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_certificate`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_mass`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival` and `OAI.MetricKMedian.Taper.physical_sparse_graph`; the proofs of `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_certificate`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_mass`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift` and `OAI.MetricKMedian.RationalPhysicalKernel.step_survival`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K038
import Definitions.Def_OAIQ035K039
import Definitions.Def_OAIQ035K040
import Definitions.Def_OAIQ035K041

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listEraseIdx : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2++(x.1.drop x.2).tail) :=
  (((listSplitAt ea a0).comp ((listTail ea a0).second (encodeList ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
noncomputable def listInsertAt : PolyProgram (encodePair (encodePair (encodeList ea) Nat.bits) ea)
    (encodeList ea) (fun x : (List α × ℕ) × α => x.1.1.take x.1.2++x.2::x.1.1.drop x.1.2) := by
  let sp := (fst (encodePair (encodeList ea) Nat.bits) ea).comp (listSplitAt ea a0)
  let pre := sp.comp (fst (encodeList ea) (encodeList ea))
  let suf := sp.comp (snd (encodeList ea) (encodeList ea))
  let elem := snd (encodePair (encodeList ea) Nat.bits) ea
  exact ((pre.fanout ((elem.fanout suf).comp (listCons ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListMapTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
noncomputable def listMapTotal (P : PolyProgram ea eb f) :
    PolyProgram (encodeList ea) (encodeList eb) (List.map f) := by
  classical
  by_cases h : Nonempty α
  · exact P.listMap h.some
  · exact (constant (encodeList ea) (encodeList eb) []).congr _ (by
      intro xs
      cases xs with
      | nil => rfl
      | cons a xs => exact False.elim (h ⟨a⟩))
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListZip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
noncomputable def listZipWith {ec : γ → List Bool} {f : α × β → γ}
    (P : PolyProgram (encodePair ea eb) ec f) :
    PolyProgram (encodePair (encodeList ea) (encodeList eb)) (encodeList ec) (fun x : List α × List β => (x.1.zip x.2).map f) :=
  ((listZip ea eb a0 b0).comp (P.listMap (a0,b0))).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Binary
open PolyProgram Function
namespace MatrixList
variable {α β : Type}

noncomputable def transposeProgram (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β) :
    PolyProgram (encodePair (encodeList eb) (encodeList (encodeList ea)))
      (encodeList (encodeList ea)) (transpose a0) := by
  let er := encodeList ea
  let em := encodeList er
  let get := (exchange Nat.bits er).comp (listGetD ea a0)
  let col := get.listMapWith [] a0
  let go := (exchange em Nat.bits).comp col
  let inds := (fst (encodeList eb) em).comp (listIndices eb b0)
  exact (((snd (encodeList eb) em).fanout inds).comp (go.listMapWith 0 [])).congr _ (fun _ => rfl)
end MatrixList
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def pivotProgram : PolyProgram er Nat.bits pivot :=
  (ratNonzero.listFindIdx 0).congr _ (fun _ => rfl)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem compressSteps_spec {n d : ℕ} (v : Fin n → Fin d → ℤ) (L : ℕ)
    (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (t : ℕ) (μ : IntegerLaw (Fin n))
    (hμ : μ.support.card ≤ t+(d+1)) :
    let ν := compressSteps v L hv t μ
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L))*(n+1))*t) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*(v i j:ℚ))=∑ i, μ.rational.weight i*(v i j:ℚ) := by
  induction t generalizing μ with
  | zero =>
    dsimp only [compressSteps]
    refine ⟨?_,Subset.rfl,by omega,fun _ => rfl⟩
    simp only [Nat.mul_zero,pow_zero,mul_one,le_refl]
  | succ t ih =>
    dsimp only
    by_cases h : d+1 < μ.support.card
    · rw [compressSteps,dite_eq_left h]
      let ν := compressionStep μ v L hv h
      have hs := compressionStep_spec μ v L hv h
      have hν : ν.support.card ≤ t+(d+1) := by
        dsimp only [ν]
        have hh := hs.2.2.1
        omega
      have hi := ih ν hν
      refine ⟨?_,hi.2.1.trans hs.2.1,hi.2.2.1,fun j => (hi.2.2.2 j).trans (hs.2.2.2 j)⟩
      let Z := ((2*(d+1)*(d+1+L))*(n+1))
      calc
        _ ≤ ν.denominator*(2:ℤ)^(Z*t) := hi.1
        _ ≤ (μ.denominator*(2:ℤ)^Z)*(2:ℤ)^(Z*t) :=
          mul_le_mul_of_nonneg_right hs.1 (by positivity)
        _ = μ.denominator*(2:ℤ)^(Z*(t+1)) := by
          rw [mul_assoc,← pow_add]
          congr 2
          ring
    · rw [compressSteps,dite_eq_right h]
      refine ⟨?_,Subset.rfl,by omega,fun _ => rfl⟩
      exact le_mul_of_one_le_right μ.denominator_pos.le (one_le_pow₀ (by norm_num))

theorem computedCompress_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) :
    let ν := computedCompress μ v L hv
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L))*(n+1))*n) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*(v i j:ℚ))=∑ i, μ.rational.weight i*(v i j:ℚ) := by
  apply compressSteps_spec
  exact (card_le_univ _).trans ((Fintype.card_fin n).trans_le (Nat.le_add_right _ _))

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPListFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset

namespace Program
open Binary Binary.PolyProgram
noncomputable def maxFold : PolyProgram (encodePair er Ratio.encode) Ratio.encode (fun x : Row × ℚ => x.1.foldl max x.2) :=
  (listChoose ratLT 0).congr _ (fun x => by
    congr 1
    funext a b
    by_cases h : a<b
    · simp [h,max_eq_right h.le]
    · simp [h,max_eq_left (le_of_not_gt h)])
end Program
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPMinimumSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

variable {α : Type}

namespace Program
open Binary Binary.PolyProgram
noncomputable def minFold : PolyProgram (encodePair er Ratio.encode) Ratio.encode (fun x : Row × ℚ => x.1.foldl min x.2) :=
  (listChoose ((exchange Ratio.encode Ratio.encode).comp ratLT) 0).congr _ (fun x => by
    congr 1
    funext a b
    by_cases h : b<a
    · simp [h,min_eq_right h.le]
    · simp [h,min_eq_left (le_of_not_gt h)])
noncomputable def minimumProgram : PolyProgram er Ratio.encode minimum :=
  (((identity er).fanout (listHead Ratio.encode 0)).comp minFold).congr _ (fun _ => rfl)
end Program
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionListStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
abbrev ed := encodePair es (encodePair el em)

abbrev Input.encode (I : Input) := ed I.raw

noncomputable def rawProgram : PolyProgram Input.encode ed Input.raw :=
  (identity ed).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def lawProgram : PolyProgram Input.encode el Input.lawData :=
  ((rawProgram.comp (snd es (encodePair el em))).comp (fst el em)).congr _ (fun _ => rfl)
noncomputable def featuresProgram : PolyProgram Input.encode em Input.features :=
  ((rawProgram.comp (snd es (encodePair el em))).comp (snd el em)).congr _ (fun _ => rfl)
noncomputable def dimProgram : PolyProgram Input.encode es (fun I => List.replicate I.d ()) :=
  (rawProgram.comp (fst es (encodePair el em))).congr _ (fun _ => rfl)

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset Polynomial

theorem lawStep_denominator {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j|≤(2:ℤ)^L) :
    (lawStep v μ).denominator ≤ μ.denominator*(2:ℤ)^((2*(d+1)*(d+1+L))*(n+1)) := by
  unfold lawStep
  split_ifs with h
  · rw [compressionStepAuto_eq μ v L hv h]
    exact (compressionStep_spec μ v L hv h).1
  · exact le_mul_of_one_le_right μ.denominator_pos.le (one_le_pow₀ (by norm_num))

theorem input_bounds (I : Input) :
    I.n≤I.encode.length ∧ I.d≤I.encode.length ∧
    I.μ.denominator≤(2:ℤ)^I.encode.length ∧ ∀ i j, |I.v i j|≤(2:ℤ)^I.encode.length := by
  let L := I.encode.length
  have hl : L=2*I.d+1+2*(ListPivot.el I.lawData).length+1+(em I.features).length := by
    simp only [L,Input.raw,encodePair_length,Gaussian.ListOperation.slots_size]
    omega
  have hn := EncodedList.length_le Signed.encode (List.ofFn I.μ.numerator)
  simp only [List.length_ofFn] at hn
  have hlaw : (ListPivot.el I.lawData).length=2*(Signed.encode I.μ.denominator).length+1+(er (List.ofFn I.μ.numerator)).length := by
    simp only [Input.lawData,ListPivot.el,encodePair_length]
  refine ⟨by change I.n≤L; change I.n≤(er (List.ofFn I.μ.numerator)).length at hn; omega,by change I.d≤L; omega,?_,?_⟩
  · have hlen : (Signed.encode I.μ.denominator).length≤L := by omega
    exact (le_abs_self _).trans ((Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) hlen))
  · intro i j
    have hrow : List.ofFn (I.v i)∈I.features := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hcol : I.v i j∈List.ofFn (I.v i) := List.mem_ofFn.mpr ⟨j,rfl⟩
    have h1 := EncodedList.member_length Signed.encode (List.ofFn (I.v i)) _ hcol
    have h2 := EncodedList.member_length er I.features _ hrow
    change (Signed.encode (I.v i j)).length≤(er (List.ofFn (I.v i))).length at h1
    change (er (List.ofFn (I.v i))).length≤(em I.features).length at h2
    exact (Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) (by omega))

theorem Input.encode_length (I : Input) : I.encode.length =
    2*I.d+1+(2*(2*(Signed.encode I.μ.denominator).length+1+
      (er (List.ofFn I.μ.numerator)).length)+1+(em I.features).length) := by
  simp only [Input.encode,Input.raw,Input.lawData,ed,el,ListPivot.el,encodePair_length,
    Gaussian.ListOperation.slots_size]

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionBinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Polynomial

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n :=
  ((lawProgram.comp (snd Signed.encode er)).comp (listLength Signed.encode 0)).congr _
    (fun I => by simp only [Function.comp_apply,Input.lawData,List.length_ofFn])

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

def law (q : Fin n → Fin m → ℚ) : SparseIntegerLaw (Graph n m) := run (columns q) m

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedGraph
open Finset
variable {I : Type} [DecidableEq I] {n : ℕ}

def law (enum : Fin n ≃ I) (q : I → I → ℚ) : SparseIntegerLaw (I → Finset I) :=
  (SparseGraph.law (fun h i => q (enum h) (enum i))).map (lift enum)

end MetricKMedian.SparseEnumeratedGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy
def graphLaw (d : F → F → ℚ) (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ)) :
    SparseIntegerLaw (A → Finset A) :=
  SparseEnumeratedGraph.law (enumeration A)
    (fun h i => Taper.sourceMarginals g P (fun a : A => d i.val.1 a.val.1) (own A i) Δ h)

def step (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) : SparseIntegerLaw (State F Δ g β) :=
  (RationalBatchData.events (graphLaw d g P s.1) Δ g β p φ hp hφ hupper).map
    (updateEvent g β s.1)

def histories (d : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ) :
    SparseIntegerLaw (SparseHistories.History (State F Δ g β)) :=
  SparseHistories.tree (fun t => step d g β p φ (P t) hp hφ hupper) (A,none) T

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

def tree (d₀ : F → F → ℚ) (A : Finset (Copy (F := F) q.Δ)) :=
  histories d₀ q.g q.β q.probabilityQ q.φ q.taperAt q.probabilityQ_pos.le
    (by exact_mod_cast q.φpos.le) q.probabilityQ_le A q.T

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistorySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

def selectCompleted (d₀ : F → F → ℚ) (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (hB : ∀ c, (B c).Nonempty) : Option (Finset F) :=
  (SparseSelect.choose (q.tree d₀ A) (q.completedGood d R A B hB)
    (fun z => score d (completed d R B hB q.g q.β z))).map
      (completed d R B hB q.g q.β)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalGridRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}

variable [Fintype F]

def roundCounts (d₀ : F → F → ℚ) (d : Fin j → F → ℚ) (n : F → ℕ) : Option (Finset F) :=
  if hn : ∀ a, n a ≤ q.Δ then
    let A := activeSlots n hn
    if hA : q.Δ ≤ A.card then
      q.selectCompleted d₀ d (q.radius d A hA) A (q.nearest d A) (q.nearest_nonempty d A hA)
    else none
  else none

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalPreparedScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F H X : Type} [LinearOrder F] [Fintype F] [DecidableEq H]
  [PseudoMetricSpace X] {j : ℕ}

def countCandidates (d₀ : H → H → ℚ) (d : Fin j → H → ℚ) (orig : F → H)
    (ns : List (F → ℕ)) : List (Finset H) :=
  ns.flatMap (fun n => ((q.roundCounts (fun a b => d₀ (orig a) (orig b))
    (fun c a => d c (orig a)) n).map (fun O => O.image orig)).toList)

def roundList (d₀ : H → H → ℚ) (d : Fin j → H → ℚ) (orig : F → H)
    (ns : List (F → ℕ)) (B : ℚ) : Option (Finset H) :=
  SparseSelect.best (candidateGood B) (score d) (q.countCandidates d₀ d orig ns)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseListTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}
abbrev encode (ea : α → List Bool) (μ : SparseIntegerLaw α) := ed ea (raw μ)

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

def State.encode {s : Bool} (x : State s) : List Bool :=
  encodePair erow (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList)) (List.ofFn x.β,x.μ)
def State.compress {s : Bool} (x : State s) : State s :=
  { x with μ := x.μ.compressAuto SparseWeightedPartial.features }
def State.step {s : Bool} (x : State s) : State s := x.branch.compress

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram
abbrev State := Bundle T

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseIterationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.SparseIntegerLaw
open Binary
variable {α : Type} {d : ℕ}

theorem encode_length_bound (ea : α → List Bool) (μ : SparseIntegerLaw α) (N H A : ℕ)
    (hn : μ.length≤N) (hd : μ.law.denominator≤(2:ℤ)^H)
    (ha : ∀ i : Fin μ.length, (ea μ.states[i.val]).length≤A) :
    (BinarySparse.encode ea μ).length≤2*(2*(H+4)+1+N*(2*(H+4)+1))+1+N*(2*A+1) := by
  have hd' := Binary.Signed.length_height (by rwa [abs_of_pos μ.law.denominator_pos] : |μ.law.denominator|≤(2:ℤ)^H)
  have hn' : (Binary.encodeList Binary.Signed.encode (List.ofFn μ.law.numerator)).length≤N*(2*(H+4)+1) := by
    apply (Binary.EncodedList.length_bound _ _ (H+4) ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*(H+4)+1) hn
    · intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact Binary.Signed.length_height (by rw [abs_of_nonneg (μ.law.numerator_nonneg i)]; exact (μ.law.numerator_le i).trans hd)
  have hs : (Binary.encodeList ea μ.states.toList).length≤N*(2*A+1) := by
    rw [BinarySparse.states_list]
    apply (Binary.EncodedList.length_bound _ _ A ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*A+1) hn
    · intro a hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ha i
  simp only [BinarySparse.encode,BinarySparse.ed,BinarySparse.raw,BinarySparse.el,IntegerLaw.ListPivot.el,Binary.encodePair_length]
  change 2*(2*(Binary.Signed.encode μ.law.denominator).length+1+
    (Binary.encodeList Binary.Signed.encode (List.ofFn μ.law.numerator)).length)+1+
    (Binary.encodeList ea μ.states.toList).length≤_
  omega

end MetricKMedian.SparseIntegerLaw
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchProposalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ProposalProgram
open Finset FixedBatch Binary Binary.PolyProgram
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

variable {I}

def Input.law (x : Input I) := proposal x.G x.Δ x.g x.b x.p x.φ x.hp x.hφ x.hupper x.enumActions
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

 def step (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) : SparseIntegerLaw (Vector ℚ n) :=
  μ.step features (probability β) (probability_unit β) (endpoint β)

 def run (β : Fin n → ℚ) (p : Vector ℚ n) :
    ℕ → SparseIntegerLaw (Vector ℚ n)
  | 0 => .dirac p
  | t+1 => step β (run β p t)

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

def Input.run {s : Bool} (x : Input s) (t : ℕ) : State s :=
  ⟨x.n,x.β,x.positive,if hs : s=true then SparseSignedPartial.run x.β x.p t
    else SparseWeightedPartial.run x.β (x.positive (by simpa using hs)) x.p t⟩

theorem input_iterate {s : Bool} (x : Input s) (t : ℕ) :
    State.step^[t] x.start=x.run t := by
  cases s <;> induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih]
    rfl

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)

def Input.state (x : Input) (t : ℕ) : State := ⟨⟨x,t⟩,run x.columns t⟩
def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ => ∅)⟩

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram
def QInput.input (x : QInput) : Input := ⟨x.n,x.m,SparseGraph.columns x.q⟩
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

def Input.law (x : Input) := graphLaw x.d x.g x.P x.A

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchUpdateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.RationalPhysicalKernel.UpdateProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
def Input.law (x : Input) := x.proposal.law.map x.update

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel.RoundProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram

def ctxInputs (x : Context) : List UpdateProgram.Input := x.toInput.law.states.toList.map (fun G => ⟨x,G⟩)

def ctxLaw (x : Context) : SparseIntegerLaw (Finset (CopyState.Copy (F:=Fin x.f) x.Δ)) := x.toInput.law.bindIndexed
  (fun i => (UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law)

 local instance instLinearOrderCopyFin_rbb1733_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_rbb1733_1 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
theorem law_step (x : Context) (s : State (Fin x.f) x.Δ x.g x.β) (hs : s.1=x.A) :
    (ctxLaw x)=(step x.d x.g x.β x.p x.φ x.P x.hp x.hφ x.hupper s).map Prod.fst := by
  unfold step
  erw [SparseIntegerLaw.map_map]
  unfold RationalBatchData.events
  erw [SparseIntegerLaw.map_bindIndexed]
  cases s with
  | mk A payload =>
    dsimp only at hs
    subst A
    unfold ctxLaw
    congr 1
    funext i
    erw [SparseIntegerLaw.map_map]
    rfl
end MetricKMedian.RationalPhysicalKernel.RoundProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalHistoriesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalPhysicalKernel.HistoryProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram
def law (P : ℕ → ℚ) (T : ℕ) (x : Context) := histories x.d x.g x.β x.p x.φ P x.hp x.hφ x.hupper x.A T

def inputs (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) : List Context :=
  (law P T x).states.toList.map (fun z => nextCtx x (P T) hP z.1.1)
end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_MaximumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
noncomputable def maxFold : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode) Ratio.encode
    (fun x : List ℚ × ℚ => x.1.foldl max x.2) :=
  (listChoose ratLT 0).congr _ (fun x => by
    congr 1
    funext a b
    by_cases h : a<b
    · simp [h,max_eq_right h.le]
    · simp [h,max_eq_left (le_of_not_gt h)])
end MetricKMedian.MaskProgram
end

end OAI
end


