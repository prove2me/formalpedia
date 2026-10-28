-- Prove2me | Definitions.Def_OAIQ035K040
-- name    : OAIQ035K040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:02:48.208294+00:00
-- url     : https://prove2.me/theorems/57d2bb30-c50c-4003-bb10-7b96bcc9642a
-- title:
--   Definitions bundle OAIQ035K040 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 29 definitions, 4 inductive types or structures and 9 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.ctx`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.encode`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.el`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.em`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.eqd`, `OAI.MetricKMedian.IntegerLaw.ListPivot.el`, `OAI.MetricKMedian.IntegerLaw.ListPivot.er`, `OAI.MetricKMedian.IntegerLaw.compressRational`, `OAI.MetricKMedian.IntegerLaw.compressSteps`, `OAI.MetricKMedian.IntegerLaw.compressionStep`, `OAI.MetricKMedian.IntegerLaw.computedCompress`, `OAI.MetricKMedian.RationalBatchData.transition`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.update`, `OAI.MetricKMedian.RationalPhysicalKernel.updateEvent`, `OAI.MetricKMedian.RoundingProgram.Input.start`, `OAI.MetricKMedian.RoundingProgram.State`, `OAI.MetricKMedian.RoundingProgram.State.branch`, `OAI.MetricKMedian.SparseBernoulli.Program.Input.encode`, `OAI.MetricKMedian.SparseCardinalRounding.Program.encodeInput`, `OAI.MetricKMedian.SparseGraph.ListOperation.et`, `OAI.MetricKMedian.SparseGraph.Program.Context`, `OAI.MetricKMedian.SparseGraph.Program.Input`, `OAI.MetricKMedian.SparseGraph.Program.State`, `OAI.MetricKMedian.SparseGraph.Program.T`, `OAI.MetricKMedian.SparseHistories.branch`, `OAI.MetricKMedian.SparseHistories.tree`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.ed`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.el`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.er`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle.encode`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle.raw`, `OAI.MetricKMedian.SparseSelect.choose`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_CompressionListStep`, `KMedian_Compression_ComputedCompression`, `KMedian_Compression_ComputedCompressionStep`, `KMedian_Compression_IntegerRationalCompression`, `KMedian_Geometry_BoundFreeCompression`, `KMedian_Geometry_GraphListOperations`, `KMedian_Geometry_RationalParameterizedHistory`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Rounding_RationalCopyTransition`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Sparse_SparseHistories`, `KMedian_Sparse_SparseListTrim`, `KMedian_Sparse_SparseMapBind`, `KMedian_Sparse_SparseMarginalTools`, `KMedian_Sparse_SparseSelect`.
--
--   **Imports.** It imports the bundles `OAIQ035K027`, `OAIQ035K028`, `OAIQ035K029`, `OAIQ035K030` and `OAIQ035K031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K047`, `OAIQ035K048` and `OAIQ035K049`; the statements `OAI.MetricKMedian.RationalBatchData.proposal_count_tail`, `OAI.MetricKMedian.SparseHistories.accumulated_drift_up_to`, `OAI.MetricKMedian.SparseHistories.count_tail_up_to` and `OAI.MetricKMedian.SparseHistories.history_contraction`; the proofs of `OAI.MetricKMedian.RationalBatchData.proposal_count_tail`, `OAI.MetricKMedian.SparseHistories.accumulated_drift_up_to`, `OAI.MetricKMedian.SparseHistories.count_tail_up_to` and `OAI.MetricKMedian.SparseHistories.history_contraction`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K027
import Definitions.Def_OAIQ035K028
import Definitions.Def_OAIQ035K029
import Definitions.Def_OAIQ035K030
import Definitions.Def_OAIQ035K031

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedCompressionStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressionStep {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (hsize : d+1 < μ.support.card) :
    IntegerLaw (Fin n) :=
  let z := computedAffineKernel μ v
  have hz := computedAffineKernel_spec μ v L hv hsize
  have hP := positiveSet_nonempty z hz.2.1 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  eliminateAt μ z p hp.1 hp.2 hz.2.1

theorem compressionStep_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L)
    (hsize : d+1 < μ.support.card) :
    let ν := compressionStep μ v L hv hsize
    ν.denominator ≤ μ.denominator*(2:ℤ)^((2*(d+1)*(d+1+L))*(n+1)) ∧
      ν.support ⊆ μ.support ∧ ν.support.card < μ.support.card ∧
      ∀ j, (∑ i, ν.rational.weight i*(v i j:ℚ))=∑ i, μ.rational.weight i*(v i j:ℚ) := by
  let z := computedAffineKernel μ v
  have hz := computedAffineKernel_spec μ v L hv hsize
  have hP := positiveSet_nonempty z hz.2.1 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  have he := eliminateAt_preserves μ (fun i j => (v i j:ℚ)) z p hp.1 hp.2
    hz.2.1 hz.2.2.1 hz.2.2.2.1
  change (eliminateAt μ z p hp.1 hp.2 hz.2.1).denominator ≤ _ ∧ _
  refine ⟨?_,he.2.2.2.1.trans (erase_subset _ _),?_,he.2.2.2.2⟩
  · change μ.denominator*z p ≤ _
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hz.2.2.2.2 p)) μ.denominator_pos.le
  · change (eliminateAt μ z p hp.1 hp.2 hz.2.1).support.card < μ.support.card
    have hh := card_le_card he.2.2.2.1
    rw [card_erase_of_mem ((μ.mem_support p).mpr he.2.1)] at hh
    omega

end MetricKMedian.IntegerLaw

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

def compressSteps {n d : ℕ} (v : Fin n → Fin d → ℤ) (L : ℕ)
    (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) : ℕ → IntegerLaw (Fin n) → IntegerLaw (Fin n)
  | 0, μ => μ
  | t+1, μ =>
    if h : d+1 < μ.support.card then
      compressSteps v L hv t (compressionStep μ v L hv h)
    else μ

def computedCompress {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) : IntegerLaw (Fin n) :=
  compressSteps v L hv n μ

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerRationalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressRational {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℚ)
    (L : ℕ) (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) : IntegerLaw (Fin n) :=
  μ.computedCompress (RationalLaw.scaledFeatures v) (L*(n+1))
    (RationalLaw.scaledFeatures_bound v L hnum hden)

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_BoundFreeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem compressionStepAuto_eq {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L)
    (hsize : d+1 < μ.support.card) :
    compressionStepAuto μ v hsize=compressionStep μ v L hv hsize := rfl

theorem compressStepsAuto_eq {n d : ℕ} (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (t : ℕ) (μ : IntegerLaw (Fin n)) :
    compressStepsAuto v t μ=compressSteps v L hv t μ := by
  induction t generalizing μ with
  | zero => rfl
  | succ t ih =>
    simp only [compressStepsAuto,compressSteps]
    split_ifs with h
    · rw [compressionStepAuto_eq μ v L hv h,ih]
    · rfl

theorem compressAuto_eq {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    μ.compressAuto v=μ.compressRational v L hnum hden :=
  compressStepsAuto_eq _ _ (RationalLaw.scaledFeatures_bound v L hnum hden) n μ

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
abbrev er := Binary.IntegerList.er
abbrev el := encodePair Signed.encode er

end MetricKMedian.IntegerLaw.ListPivot
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
abbrev em := Binary.IntegerList.em
abbrev el := ListPivot.el

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RationalFeatureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function
abbrev eqd := encodePair es (encodePair el eqm)

abbrev RationalInput.encode (I : RationalInput) := eqd I.raw

end MetricKMedian.IntegerLaw.BinaryCompression
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
abbrev el := IntegerLaw.ListPivot.el
abbrev er := IntegerLaw.ListPivot.er
variable {α : Type}
abbrev ed (ea : α → List Bool) := encodePair el (encodeList ea)

theorem states_list (μ : SparseIntegerLaw α) : μ.states.toList=List.ofFn (fun i : Fin μ.length => μ.states[i.val]) := by
  apply List.ext_getElem <;> intros <;> simp

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMarginalTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

 theorem dirac_states (a : α) (i : Fin (dirac a).length) : (dirac a).states[i.val]=a := by
  simp [dirac]

end MetricKMedian.SparseIntegerLaw

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

structure State (signed : Bool) where
  n : ℕ
  β : Fin n → ℚ
  positive : signed=false → ∀ i, 0<β i
  μ : SparseIntegerLaw (Vector ℚ n)

def State.branch {s : Bool} (x : State s) : State s :=
  { x with μ := (if hs : s=true then
      x.μ.branch (RationalSignedStep.probability x.β) (RationalSignedStep.probability_unit x.β) (RationalSignedStep.endpoint x.β)
      else x.μ.branch (RationalWeightedStep.probability x.β)
        (RationalWeightedStep.probability_unit x.β (x.positive (by simpa using hs))) (RationalWeightedStep.endpoint x.β)) }

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev et := encodeList er

end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalCopyTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {F : Type} [DecidableEq F] [Fintype F] {Δ : ℕ}

def transition (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset (CopyState.Copy (F := F) Δ) :=
  CopyState.next Δ A (erased A G H Z) (opened A G H Z)

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

def branch (κ : α → SparseIntegerLaw α) (h : History α) : SparseIntegerLaw (History α) :=
  (κ h.1).map (extend h)

def tree (κ : ℕ → α → SparseIntegerLaw α) (a : α) : ℕ → SparseIntegerLaw (History α)
  | 0 => .dirac (a,[])
  | t+1 => (tree κ a t).bindIndexed (fun i => branch (κ t) (tree κ a t).states[i.val])

end MetricKMedian.SparseHistories
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

def updateEvent (g β : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (e : RationalBatchData.Event A g β) : State F Δ g β := by
  obtain ⟨G,Z⟩ := e
  exact (RationalBatchData.transition A G
    (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z,
    some ⟨A,⟨G,Z⟩⟩)

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

theorem taperAt_pos (t : ℕ) : 0 < (q.taperAt t:ℝ) := by
  unfold taperAt
  split_ifs with ht
  · exact q.taper_pos _
  · norm_num

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_DependentSparseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparseIntegerLaw.DependentProgram
open Binary Binary.PolyProgram Function BinarySparse
variable {C A : Type} (T : C → Type)

structure Bundle where
  ctx : C
  law : SparseIntegerLaw (T ctx)

variable {T} (ec : C → List Bool) (ea : A → List Bool) (view : ∀ c, T c → A)

def Bundle.raw (x : Bundle T) : C × Data A :=
  (x.ctx,((x.law.law.denominator,List.ofFn x.law.law.numerator),x.law.states.toList.map (view x.ctx)))
def Bundle.encode (x : Bundle T) : List Bool := encodePair ec (ed ea) (x.raw view)

end MetricKMedian.SparseIntegerLaw.DependentProgram
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
abbrev Input.encode (x : Input) := qr (List.ofFn x.p)

end MetricKMedian.SparseBernoulli.Program
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

def Input.start {s : Bool} (x : Input s) : State s := ⟨x.n,x.β,x.positive,.dirac x.p⟩

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

structure Input where
  n : ℕ
  m : ℕ
  columns : Fin m → SparseIntegerLaw (Finset (Fin n))
structure Context where
  input : Input
  t : ℕ
abbrev T (c : Context) := Graph c.input.n c.input.m
abbrev State := Bundle T
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
abbrev encodeInput := SparseBernoulli.Program.Input.encode
end MetricKMedian.SparseCardinalRounding.Program
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

abbrev Input.update (x : Input) (Z) := RationalBatchData.transition x.ctx.A x.G
  (RationalBatchData.heavySet (RationalBatchData.graphMass x.G x.ctx.g) x.ctx.β) Z

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSelect
variable {α : Type}

def choose (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ) : Option α :=
  best P cost μ.states.toList

end MetricKMedian.SparseSelect
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMapBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.SparseIntegerLaw
variable {α β γ : Type}
 theorem map_map (μ : SparseIntegerLaw α) (f : α → β) (g : β → γ) :
    (μ.map f).map g=μ.map (g ∘ f) := by
  unfold map
  simp only [Vector.map_map]
 theorem map_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β) (f : β → γ) :
    (μ.bindIndexed κ).map f=μ.bindIndexed (fun i => (κ i).map f) := by
  unfold map bindIndexed
  congr 1
  ext i hi
  simp only [Vector.getElem_map,Vector.getElem_ofFn]
end MetricKMedian.SparseIntegerLaw
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_HistorySelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel
variable {τ : ℝ} (q : RationalParameters τ)

def Input.ctx (x : Input q) : UpdateProgram.Context where
  f := x.f
  Δ := q.Δ
  d := x.d₀
  g := q.g
  P := 1
  positive := by norm_num
  A := x.A
  β := q.β
  p := q.probabilityQ
  φ := q.φ
  hp := q.probabilityQ_pos.le
  hφ := by exact_mod_cast q.φpos.le
  hupper := q.probabilityQ_le

end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end


