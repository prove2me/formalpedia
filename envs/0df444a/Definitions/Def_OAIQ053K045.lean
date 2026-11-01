-- Prove2me | Definitions.Def_OAIQ053K045
-- name    : OAIQ053K045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:04:47.803198+00:00
-- url     : https://prove2.me/theorems/1931b98c-3ee6-4903-975b-a4dd76fe96ae
-- title:
--   Definitions bundle OAIQ053K045 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 17 definitions and 14 theorems. The definitions and types are `OAI.MetricKMedian.Binary.MatrixList.transposeProgram`, `OAI.MetricKMedian.Binary.PolyProgram.intEQ`, `OAI.MetricKMedian.Binary.PolyProgram.listEraseIdx`, `OAI.MetricKMedian.Binary.PolyProgram.listInsertAt`, `OAI.MetricKMedian.Binary.PolyProgram.listMapTotal`, `OAI.MetricKMedian.Binary.PolyProgram.listZipWith`, `OAI.MetricKMedian.Binary.PolyProgram.ratNonzero`, `OAI.MetricKMedian.LPBinary.Nearest.beforeProgram`, `OAI.MetricKMedian.LPBinary.Nearest.entriesProgram`, `OAI.MetricKMedian.LPBinary.Program.maxFold`, `OAI.MetricKMedian.LPBinary.Program.minFold`, `OAI.MetricKMedian.LPBinary.Program.minimumProgram`, `OAI.MetricKMedian.LPBinary.Program.positivePart`, `OAI.MetricKMedian.MaskProgram.maxFold`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.el`, `OAI.MetricKMedian.SparseSignedRounding.kernel`, `OAI.MetricKMedian.SparseSignedRounding.round`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_BinaryListIndex`, `KMedian_Binary_BinaryListMapTotal`, `KMedian_Binary_BinaryListZip`, `KMedian_Binary_BinaryMatrix`, `KMedian_Binary_BinaryPredicates`, `KMedian_Binary_BinaryRational`, `KMedian_Compression_ComputedCompression`, `KMedian_Compression_IntegerRationalCompression`, `KMedian_Geometry_BoundFreeCompression`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_LPMinimumSelection`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Programs_MaximumProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseBernoulliRun`, `KMedian_Sparse_SparseBernoulliSupport`, `KMedian_Sparse_SparseListTrim`, `KMedian_Sparse_SparseSignedPartial`, `KMedian_Sparse_SparseSignedRounding`, `KMedian_Sparse_SparseSupport`.
--
--   **Imports.** It imports the bundles `OAIQ053K038`, `OAIQ053K039` and `OAIQ053K040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K048`, `OAIQ053K049`, `OAIQ053K050`, `OAIQ053K051`, `OAIQ053K052` and `OAIQ053K053`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K038
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K040

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListIndex
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListMapTotal
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListZip
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryRational
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram
noncomputable def intEQ : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1=x.2)) :=
  ((intSub.comp intAbs).comp natZero).congr _ (fun _ => by simp only [Function.comp_apply,Int.natAbs_eq_zero,sub_eq_zero])

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryMatrix
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryPredicates
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
noncomputable def ratNonzero : PolyProgram Ratio.encode encodeBool (fun q => decide (q≠0)) :=
  (ratZero.comp boolNot).congr _ (fun q => by simp)
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedCompression
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight _root_.OAI.MetricKMedian.RationalLaw.integer_numerator_zero _root_.OAI.MetricKMedian.RationalLaw.integer_weight _root_.OAI.MetricKMedian.RationalLaw.real_expect
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerRationalCompression
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem compressRational_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    let ν := μ.compressRational v L hnum hden
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L*(n+1)))*(n+1))*n) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  have hh := μ.computedCompress_spec (RationalLaw.scaledFeatures v) (L*(n+1))
    (RationalLaw.scaledFeatures_bound v L hnum hden)
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_⟩
  intro j
  let D := RationalScaling.denominator (fun i => v i j)
  have hD : (D:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos (fun i => v i j)).ne'
  have hcast : ∀ i, (RationalLaw.scaledFeatures v i j:ℚ)=v i j*(D:ℚ) := by
    intro i
    rw [RationalLaw.scaledFeatures_eq]
    exact RationalScaling.numerator_cast _ i
  have hm := hh.2.2.2 j
  simp only [hcast,← mul_assoc,← sum_mul] at hm
  exact mul_right_cancel₀ hD hm

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_BoundFreeCompression
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem compressAuto_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    let ν := μ.compressAuto v
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L*(n+1)))*(n+1))*n) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  rw [compressAuto_eq μ v L hnum hden]
  exact compressRational_spec μ v L hnum hden

theorem compressAuto_correct {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) :
    let ν := μ.compressAuto v
    ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  obtain ⟨L,hnum,hden⟩ := exists_rational_feature_bound v
  exact (compressAuto_spec μ v L hnum hden).2

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPListFacts
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPMinimumSelection
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexListProgram
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
noncomputable def positivePart : PolyProgram Ratio.encode Ratio.encode (fun q => max 0 q) :=
  (((constant Ratio.encode Ratio.encode 0).fanout (identity Ratio.encode)).comp ratMax).congr _ (fun _ => rfl)
end Program
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseAlgorithm
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem compressAuto_correct {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ) :
    let ν := μ.compressAuto v
    ν.length ≤ d+1 ∧
      (∀ i : Fin ν.length, ∃ j : Fin μ.length, ν.states[i.val]=μ.states[j.val]) ∧
      ∀ j, ν.moment (fun a => v a j)=μ.moment (fun a => v a j) := by
  let ξ : SparseIntegerLaw α := ⟨μ.length,μ.states,
    μ.law.compressAuto (fun i => v μ.states[i.val])⟩
  have hh := μ.law.compressAuto_correct (fun i => v μ.states[i.val])
  refine ⟨hh.2.1,?_,?_⟩
  · intro i
    refine ⟨ξ.law.support.orderEmbOfFin rfl i,?_⟩
    change (Vector.ofFn (fun k => μ.states[(ξ.law.support.orderEmbOfFin rfl k).val]))[i.val] = _
    simp only [Vector.getElem_ofFn]
    congr 2
  · intro j
    change ξ.trim.moment (fun a => v a j)=_
    rw [trim_moment]
    exact hh.2.2 j

theorem step_moment {d : ℕ} (v : α → Fin d → ℚ) (μ : SparseIntegerLaw α)
    (p : α → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α)
    (j : Fin d) :
    (step v μ p hp next).moment (fun a => v a j)=
      μ.moment (fun a => p a*v (next a 0) j+(1-p a)*v (next a 1) j) :=
  ((μ.branch p hp next).compressAuto_correct v).2.2 j |>.trans
    (μ.branch_moment p hp next _)

theorem step_property {d : ℕ} (v : α → Fin d → ℚ) (μ : SparseIntegerLaw α)
    (p : α → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α)
    (P : α → Prop) (hP : ∀ i : Fin μ.length, ∀ b, P (next μ.states[i.val] b)) :
    ∀ i : Fin (step v μ p hp next).length, P (step v μ p hp next).states[i.val] := by
  intro i
  obtain ⟨j,hj⟩ := ((μ.branch p hp next).compressAuto_correct v).2.1 i
  change P ((μ.branch p hp next).compressAuto v).states[i.val]
  rw [hj]
  change P ((Vector.ofFn (fun k => next
    μ.states[(finProdFinEquiv.symm k).1.val] (finProdFinEquiv.symm k).2))[j.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseListTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
abbrev el := IntegerLaw.ListPivot.el
end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_MaximumProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_NearestListProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest

noncomputable def entriesProgram : PolyProgram (encodePair er er) ees (fun x : Row × Row => entries x.1 x.2) := by
  let ez := encodePair Ratio.encode Ratio.encode
  let zip := listZip Ratio.encode Ratio.encode 0 0
  let ids := listIndices ez (0,0)
  exact (zip.comp ((ids.fanout (identity (encodeList ez))).comp (listZip Nat.bits ez 0 (0,0)))).congr _ (fun _ => rfl)
noncomputable def beforeProgram : PolyProgram (encodePair ee ee) encodeBool (fun x : Entry × Entry => before x.1 x.2) := by
  let a := fst ee ee
  let b := snd ee ee
  let idx := fst Nat.bits (encodePair Ratio.encode Ratio.encode)
  let dist := (snd Nat.bits (encodePair Ratio.encode Ratio.encode)).comp (snd Ratio.encode Ratio.encode)
  let dst := (a.comp dist).fanout (b.comp dist)
  let ilt := ((a.comp idx).fanout (b.comp idx)).comp natLT
  exact (((dst.comp ratLT).fanout (((dst.comp ratEQ).fanout ilt).comp boolAnd)).comp boolOr).congr _ (fun _ => by simp only [Function.comp_apply,before,Bool.decide_or,Bool.decide_and])
end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliRun
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem run_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) (ht : t ≤ n) (f : Fin d → Fin (n+1)) :
    (run (d := d) p hp t).moment (fun q => monomial q f)=target p t f := by
  induction t generalizing f with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,monomial,flag,target]
  | succ t ih =>
    have htn : t<n := by omega
    have hh := (run (d := d) p hp t).step_moment (features (d := d))
      (fun _ => p ⟨t,htn⟩) (fun _ => hp ⟨t,htn⟩)
      (fun q b => endpoint q ⟨t,htn⟩ b) (finFunctionFinEquiv f)
    simp only [features_code] at hh
    rw [run,dite_eq_left htn]
    refine hh.trans ?_
    rw [target_succ p t htn f]
    by_cases hi : (⟨t,htn⟩ : Fin n) ∈ used f
    · rw [ite_eq_left hi]
      calc
        _ = (run (d := d) p hp t).moment
            (fun q => p ⟨t,htn⟩*monomial q (without f ⟨t,htn⟩)) := by
          apply SparseIntegerLaw.moment_congr
          intro a
          simp [monomial_endpoint,hi]
        _ = _ := by rw [SparseIntegerLaw.moment_mul,ih (by omega)]
    · rw [ite_eq_right hi]
      calc
        _ = (run (d := d) p hp t).moment (fun q => monomial q f) := by
          apply SparseIntegerLaw.moment_congr
          intro a
          simp only [monomial_endpoint,ite_eq_right hi]
          ring
        _ = _ := ih (by omega) f

theorem run_length (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) : (run (d := d) p hp t).length ≤ (n+1)^d+1 := by
  induction t with
  | zero => change 1 ≤ _; omega
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · exact ((run (d := d) p hp t).branch (fun _ => p ⟨t,ht⟩)
        (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)).compressAuto_correct
          (features (d := d)) |>.1
    · exact ih

theorem run_spec (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    let μ := run (d := d) p hp n
    μ.length ≤ (n+1)^d+1 ∧ ∀ f : Fin d → Fin (n+1),
      μ.moment (fun q => monomial q f)=∏ i ∈ used f, p i := by
  refine ⟨run_length p hp n,fun f => ?_⟩
  rw [run_moment p hp n (le_refl n) f]
  simp only [target,Fin.isLt,ite_eq_left]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSupport
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem compressAuto_positive {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ)
    (a : Fin (μ.compressAuto v).length) : 0 < (μ.compressAuto v).law.rational.weight a := by
  exact (⟨μ.length,μ.states,μ.law.compressAuto (fun i => v μ.states[i.val])⟩ :
    SparseIntegerLaw α).trim_positive a

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliSupport
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem run_positive (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) (a : Fin (run (d := d) p hp t).length) :
    0 < (run (d := d) p hp t).law.rational.weight a := by
  induction t with
  | zero =>
    change 0 < (SparseIntegerLaw.dirac (fun _ : Fin n => false)).law.rational.weight a
    change (0:ℚ) < 1/1
    norm_num
  | succ t ih =>
    let inv : SparseIntegerLaw (Fin n → Bool) → Prop := fun μ =>
      ∀ a : Fin μ.length, 0 < μ.law.rational.weight a
    suffices hs : inv (run (d := d) p hp (t+1)) from hs a
    rw [run]
    split_ifs with ht
    · exact ((run (d := d) p hp t).branch (fun _ => p ⟨t,ht⟩)
        (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)).compressAuto_positive _
    · exact ih

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPartial
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

theorem run_invariants (β : Fin n → ℚ)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (t : ℕ) :
    ∀ a : Fin (run β p t).length,
      let q := (run β p t).states[a.val]
      (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
      (∑ i, β i*point q i)=∑ i, β i*point p i ∧
      ((fractional q).card ≤ n-t ∨ ¬Active β q) := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    dsimp only
    rw [he]
    refine ⟨hp,rfl,Or.inl ?_⟩
    have hh := card_le_card (filter_subset (fun i : Fin n => 0 < point p i ∧ point p i < 1) univ)
    simpa only [fractional,card_univ,Fintype.card_fin,Nat.sub_zero] using hh
  | succ t ih =>
    apply (run β p t).step_property features (probability β)
      (probability_unit β) (endpoint β)
      (fun q => (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
        (∑ i, β i*point q i)=∑ i, β i*point p i ∧
        ((fractional q).card ≤ n-(t+1) ∨ ¬Active β q))
    intro a b
    obtain ⟨ha0,ha1,ha2⟩ := ih a
    refine ⟨endpoint_feasible β _ ha0 b,(endpoint_weighted β _ b).trans ha1,?_⟩
    by_cases h : Active β (run β p t).states[a.val]
    · have hh := endpoint_smaller β _ h b
      rcases ha2 with ha2 | ha2
      · exact Or.inl (by omega)
      · exact False.elim (ha2 h)
    · simp only [endpoint,dite_eq_right h]
      exact Or.inr h

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

def kernel (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (a : Fin (SparseSignedPartial.run u p n).length) : SparseIntegerLaw (Vector ℚ n) :=
  RationalSignedTerminal.terminal u (SparseSignedPartial.run u p n).states[a.val]
    (SparseSignedPartial.run_invariants u p hp n a).1

def round (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) : SparseIntegerLaw (Vector ℚ n) :=
  (SparseSignedPartial.run u p n).bindCompress (kernel u p hp) features

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end


