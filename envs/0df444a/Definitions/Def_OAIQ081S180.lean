-- Prove2me | Definitions.Def_OAIQ081S180
-- name    : OAIQ081S180
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:35:43.099565+00:00
-- url     : https://prove2.me/theorems/9edbef01-f348-4749-a527-62f503404776
-- title:
--   Definitions bundle OAIQ081S180 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 12 definitions and 10 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.numerator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.exportModelBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.nativeCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.activeCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.cost`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.cost`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.encodeRow`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.encodeTerm`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.factorCode`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.inputSize`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.productCode`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTermProgram.cost`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_InterpolationCacheProgram`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramPairs`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramRows`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryReplay`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramDefinitions`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExports`, `SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds`, `SubexponentialSAT_Subexp_UniversalRowDataProgram`, `SubexponentialSAT_Subexp_UniversalRowExecution`, `SubexponentialSAT_Subexp_UniversalRowLoop`, `SubexponentialSAT_Subexp_UniversalRowProgram`, `SubexponentialSAT_Subexp_UniversalRowTermProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S173` and `OAIQ081S174` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S186` and `OAIQ081S188`; the statement `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S173
import Definitions.Def_OAIQ081S174

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scans for inverse nodes, negative nodes, and a complete row of
pairwise difference inverses. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

theorem negativeScan_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hready : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 257=[]) (harg : s 213=[]) (hresult : s 208=[]) :
    Runs negativeScan (nodeScanBudget (negativeBudget t d) (d*baseWidth 3 t) xs.length) s
      (Function.update s 260 ((xs.flatMap fun x => RingProgram.flat (negativeValue t a M cache minusOne x)).reverse++s 260)) := by
  apply scanMaster_run RingProgram.flat (negativeValue t a M cache minusOne) _ _ hW
    RingProgram.flat_length 257 260 213 (by unfold MapPorts; decide) (by decide) negativeCommand
    (Ready t a M cache minusOne) ?_ ?_ s xs hready hm hsrc harg hresult hready.width
    (hready.scratch 270 (by decide)) (hready.scratch 271 (by decide))
  · intro s i v h hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact h.update_controller _ v (by decide)
  · intro s x h hx hr
    exact h.negative_run hz x hx hr

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramPairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Nested native scans producing the full row-major difference-inverse
array. Every diagonal cell is computed by the same total inverse routine. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines
open SubexpLiftRing
local infixr:55 " ;; " => seq_p1

theorem pairLoop_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (xs ys : List (Coeff t d))
    (s : Store) (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 257=ys.flatMap RingProgram.flat)
    (hclean : ∀i∈([208,213,218,258] : List (Fin 320)),s i=[])
    (r : Fin 16 → Bool) :
    ∃n rf,n ≤ ys.length*(nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length+16*(d*baseWidth 3 t)+16)+1 ∧
      Eval pairLoop n (⟨readRegs r 0 15 (s 257).head?,s⟩ : Data)
        ⟨rf,Function.update (Function.update s 257 []) 261
          ((ys.flatMap (rowBytes t a M cache minusOne xs)).reverse++s 261)⟩ := by
  induction ys generalizing s r with
  | nil =>
      have hs : s 257=[] := hsrc
      have hu : Function.update s 257 []=s := by simpa only [hs] using Function.update_eq_self 257 s
      refine ⟨1,readRegs r 0 15 none,by simp,?_⟩
      simp only [List.flatMap_nil,List.reverse_nil,List.nil_append,hu,Function.update_eq_self]
      simpa only [pairLoop, hs,List.head?_nil] using
        (Eval.while_false (body := pairStep ;; peek 257)
          (a := (⟨readRegs r 0 15 none,s⟩ : Data)) (by simp [readRegs]))
  | cons x ys ih =>
      let mid := Function.update (Function.update s 257 (ys.flatMap RingProgram.flat)) 261
        ((rowBytes t a M cache minusOne xs x).reverse++s 261)
      obtain ⟨n,rm,hn,he⟩ := pairStep_run t a M cache hz minusOne x hW s xs
        (ys.flatMap RingProgram.flat) hr hm hsrc hclean (readRegs r 0 15 (s 257).head?)
      have hrm : Ready t a M cache minusOne mid :=
        (hr.update_controller 257 _ (by decide)).update_controller 261 _ (by decide)
      obtain ⟨m,rf,hmb,het⟩ := ih mid hrm (by simpa [mid] using hm) (by simp [mid])
        (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl|rfl|rfl|rfl <;> simpa [mid] using hclean _ (by simp)) rm
      have hg : (readRegs r 0 15 (s 257).head?) 15=true := by
        have hne : RingProgram.flat x≠[] := by
          intro hh
          have h := RingProgram.flat_length x
          rw [hh,List.length_nil] at h
          omega
        rw [hsrc,List.flatMap_cons]
        cases hh : RingProgram.flat x with
        | nil => exact (hne hh).elim
        | cons b bs => simp [readRegs]
      have hc := Eval.while_true hg (he.seq (peek_eval mid rm 257)) het
      refine ⟨n+1+m+1,rf,?_,?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega
      · have hfinal : Function.update (Function.update mid 257 []) 261
            ((ys.flatMap (rowBytes t a M cache minusOne xs)).reverse++mid 261) =
            Function.update (Function.update s 257 []) 261
              (((x::ys).flatMap (rowBytes t a M cache minusOne xs)).reverse++s 261) := by
          funext i
          by_cases hi : i=261
          · subst i; simp [mid,List.reverse_append,List.append_assoc]
          · by_cases hj : i=257
            · subst i; simp [mid]
            · simp [mid,hi,hj]
        rw [hfinal] at hc
        exact hc

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete ordered native tables; all working streams are empty again. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

theorem inverseTable_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈([208,213,218,257,259] : List (Fin 320)),s i=[]) :
    Runs inverseTable (inverseTableBudget t d xs.length) s
      (Function.update s 259 (inverseBytes t a M cache minusOne xs)) := by
  let ni := inverseBytes t a M cache minusOne xs
  let s1 := Function.update s 218 (s 104)
  let s2 := Function.update s1 259 ni.reverse
  let s3 := Function.update s 259 ni.reverse
  have h1 : Runs (copy 104 218) (7*(d*baseWidth 3 t)+5) s s1 := by
    simpa only [s1,hc 218 (by simp),List.append_nil,hr.width] using
      copy_run s 104 218 (by decide) (by decide) (by decide) (hr.scratch 270 (by decide))
  have hr1 := hr.update_controller 218 (s 104) (by decide)
  have h2 : Runs inverseScan (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length) s1 s2 := by
    simpa [s2,s1,ni,inverseBytes,hc 259 (by simp)] using
      inverseScan_run t a M cache hz minusOne hW s1 xs hr1 (by simpa [s1] using hm)
        (by simpa [s1] using hc 257 (by simp)) (by simpa [s1] using hc 213 (by simp))
        (by simpa [s1] using hc 208 (by simp)) (by simpa [s1] using hr.zero)
  have h3 : Runs (clear 218) (2*(d*baseWidth 3 t)+3) s2 s3 := by
    have he : Function.update s2 218 []=s3 := by
      funext i
      by_cases hi : i=218 <;> simp [s3,s2,s1,Function.update_apply,hi,hc 218 (by simp)]
    simpa only [he,s2,s1,Function.update_of_ne (by decide : (218:Fin 320)≠259),
      Function.update_same,hr.width] using clear_run s2 218
  have hlen : ni.length=xs.length*(d*baseWidth 3 t) :=
    flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs
  have h4 : Runs (reverse 259) (9*(xs.length*(d*baseWidth 3 t))+7) s3
      (Function.update s 259 ni) := by
    simpa [s3,hlen] using reverse_run s3 259 (by decide) (by decide)
      (by simpa [s3] using hr.scratch 270 (by decide))
      (by simpa [s3] using hr.scratch 271 (by decide))
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by unfold inverseTableBudget; omega)

theorem negativeTable_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈([208,213,257,260] : List (Fin 320)),s i=[]) :
    Runs negativeTable (negativeTableBudget t d xs.length) s
      (Function.update s 260 (negativeBytes t a M cache minusOne xs)) := by
  let nn := negativeBytes t a M cache minusOne xs
  let mid := Function.update s 260 nn.reverse
  have h1 : Runs negativeScan (nodeScanBudget (negativeBudget t d) (d*baseWidth 3 t) xs.length) s mid := by
    simpa only [mid,nn,negativeBytes,hc 260 (by simp),List.append_nil] using
      negativeScan_run t a M cache hz minusOne hW s xs hr hm (hc 257 (by simp))
        (hc 213 (by simp)) (hc 208 (by simp))
  have hlen : nn.length=xs.length*(d*baseWidth 3 t) :=
    flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs
  have h2 : Runs (reverse 260) (9*(xs.length*(d*baseWidth 3 t))+7) mid (Function.update s 260 nn) := by
    simpa [mid,hlen] using reverse_run mid 260 (by decide) (by decide)
      (by simpa [mid] using hr.scratch 270 (by decide))
      (by simpa [mid] using hr.scratch 271 (by decide))
  exact (h1.seq h2).mono (by unfold negativeTableBudget; omega)

theorem pairScan_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈([208,213,218,257,258] : List (Fin 320)),s i=[]) :
    Runs pairScan
      (xs.length*(nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length+23*(d*baseWidth 3 t)+16)+7) s
      (Function.update s 261 ((differenceBytes t a M cache minusOne xs).reverse++s 261)) := by
  let mid := Function.update s 257 (xs.flatMap RingProgram.flat)
  have h1 : Runs (copy 256 257) (7*(xs.length*(d*baseWidth 3 t))+5) s mid := by
    simpa only [mid,hm,hc 257 (by simp),List.append_nil,flatMap_length _ _ RingProgram.flat_length] using
      copy_run s 256 257 (by decide) (by decide) (by decide) (hr.scratch 270 (by decide))
  intro r
  obtain ⟨n,rm,hn,he⟩ := h1 r
  obtain ⟨m,rf,hmb,het⟩ := pairLoop_run t a M cache hz minusOne hW xs xs mid
    (hr.update_controller 257 _ (by decide)) (by simpa [mid] using hm) (by simp [mid])
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl <;> simpa [mid] using hc _ (by simp)) rm
  have hend : Function.update (Function.update mid 257 []) 261
      ((xs.flatMap (rowBytes t a M cache minusOne xs)).reverse++mid 261) =
      Function.update s 261 ((differenceBytes t a M cache minusOne xs).reverse++s 261) := by
    simp [mid,differenceBytes,Function.update_idem,←hc 257 (by simp)]
  rw [hend] at het
  exact ⟨n+(1+m),rf,by nlinarith only [hn,hmb],he.seq ((peek_eval mid rm 257).seq het)⟩

theorem differenceTable_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈([208,213,218,257,258,261] : List (Fin 320)),s i=[]) :
    Runs differenceTable (differenceTableBudget t d xs.length) s
      (Function.update s 261 (differenceBytes t a M cache minusOne xs)) := by
  let nd := differenceBytes t a M cache minusOne xs
  let mid := Function.update s 261 nd.reverse
  have h1 : Runs pairScan
      (xs.length*(nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length+23*(d*baseWidth 3 t)+16)+7) s mid := by
    simpa only [mid,nd,hc 261 (by simp),List.append_nil] using
      pairScan_run t a M cache hz minusOne hW s xs hr hm (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl <;> exact hc _ (by simp))
  have hlen : nd.length=xs.length*(xs.length*(d*baseWidth 3 t)) := by
    apply flatMap_length
    intro x
    exact flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs
  have h2 : Runs (reverse 261) (9*(xs.length*(xs.length*(d*baseWidth 3 t)))+7) mid
      (Function.update s 261 nd) := by
    simpa [mid,hlen] using reverse_run mid 261 (by decide) (by decide)
      (by simpa [mid] using hr.scratch 270 (by decide))
      (by simpa [mid] using hr.scratch 271 (by decide))
  exact (h1.seq h2).mono (by unfold differenceTableBudget; omega)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single fixed native interpolation-cache producer. The only data
inputs are the actual node stream and already prepared ring constants.
No inverse, negative, or pairwise table is supplied to this program. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

theorem command_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈inputEmpty,s i=[]) :
    Runs command (budget t d xs.length) s (finalStore t a M cache minusOne xs s) := by
  let s1 := Function.update s 259 (inverseBytes t a M cache minusOne xs)
  let s2 := Function.update s1 260 (negativeBytes t a M cache minusOne xs)
  let s3 := Function.update s2 261 (differenceBytes t a M cache minusOne xs)
  let s4 := Function.update s3 262 (List.replicate (xs.length*(d*baseWidth 3 t)) true)
  have h1 : Runs inverseTable (inverseTableBudget t d xs.length) s s1 :=
    inverseTable_run t a M cache hz minusOne hW s xs hr hm (by
      intro i hi
      apply hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide)
  have hr1 := hr.update_controller 259 (inverseBytes t a M cache minusOne xs) (by decide)
  have h2 : Runs negativeTable (negativeTableBudget t d xs.length) s1 s2 :=
    negativeTable_run t a M cache hz minusOne hW s1 xs hr1 (by simpa [s1] using hm) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> simpa [s1] using hc _ (by decide))
  have hr2 := hr1.update_controller 260 (negativeBytes t a M cache minusOne xs) (by decide)
  have h3 : Runs differenceTable (differenceTableBudget t d xs.length) s2 s3 :=
    differenceTable_run t a M cache hz minusOne hW s2 xs hr2 (by simpa [s2,s1] using hm) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> simpa [s2,s1] using hc _ (by decide))
  have hlen : (s3 256).length=xs.length*(d*baseWidth 3 t) := by
    simp only [s3,s2,s1,Function.update_of_ne (by decide : (256:Fin 320)≠259),
      Function.update_of_ne (by decide : (256:Fin 320)≠260),
      Function.update_of_ne (by decide : (256:Fin 320)≠261),hm]
    exact flatMap_length _ _ RingProgram.flat_length xs
  have h4 : Runs (countCopy 256 262) (11*(xs.length*(d*baseWidth 3 t))+9) s3 s4 := by
    simpa only [hlen,s4] using countCopy_run 256 262 s3 (by decide) (by decide) (by decide)
      (by simpa [s3,s2,s1] using hr.scratch 270 (by decide))
      (by simpa [s3,s2,s1] using hc 272 (by decide))
      (by simpa [s3,s2,s1] using hc 262 (by decide))
  have h5 : Runs (countCopy 104 263) (11*(d*baseWidth 3 t)+9) s4
      (finalStore t a M cache minusOne xs s) := by
    have hwidth : (s4 104).length=d*baseWidth 3 t := by simpa [s4,s3,s2,s1] using hr.width
    simpa only [hwidth,finalStore,s4,s3,s2,s1] using
      countCopy_run 104 263 s4 (by decide) (by decide) (by decide)
        (by simpa [s4,s3,s2,s1] using hr.scratch 270 (by decide))
        (by simpa [s4,s3,s2,s1] using hc 272 (by decide))
        (by simpa [s4,s3,s2,s1] using hc 263 (by decide))
  exact (h1.seq (h2.seq (h3.seq (h4.seq h5)))).mono (by unfold budget; omega)

theorem program_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈inputEmpty,s i=[]) (r : Fin 16 → Bool) :
    ∃n rf,n ≤ budget t d xs.length+1 ∧ Trace program n
      ((⟨r,s⟩ : Data).withPC (some program.entry))
      ((⟨rf,finalStore t a M cache minusOne xs s⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_run t a M cache hz minusOne hW s xs hr hm hc r
  exact ⟨n+1,rf,Nat.add_le_add_right hn 1,compiled_halt_trace he 256 261⟩

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay of the complete denominator call. The three opaque
outer accumulators are never inspected, including by storage subroutines. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage ProgramTapeReplay

theorem localCommand_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden localCommand := by
  refine ⟨avoids_copyMany LeafProgram.OuterCarried.hidden 460 pairs (by decide) ?_,
    avoids_call_lift_of_range LeafProgram.OuterCarried.hidden LayoutDenominatorProgram.program id port port_not_hidden,
    avoids_copyCmd LeafProgram.OuterCarried.hidden 592 728 460 (by decide) (by decide) (by decide),
    avoids_clearMany LeafProgram.OuterCarried.hidden bank ?_⟩
  · simp [pairs,LeafProgram.OuterCarried.hidden]
  · intro i hi
    exact not_hidden_of_high i ((mem_bank i).mp hi).1

/-- This is a syntactic no-read/no-write certificate for the actual fixed
40-register denominator program, not just a final-state preservation fact. -/
theorem command_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden command :=
  avoids_liftProgram LeafProgram.OuterCarried.hidden localProgram registers id
    (avoids_compiled LeafProgram.OuterCarried.hidden localCommand localCommand_avoids 740 728)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramDefinitions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed source-value table program. Its definitions and structural
interfaces are independent of the full integer numerator execution proof. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open IntegerRingLiftProgram

def numerator : Code := liftCommand LayoutProgram.Numerator.command 23 50
  numeratorRegs numeratorPorts

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def exportModelBudget (m : Model) : ℕ := ((List.finRange 16).map (exportFieldBound m)).sum

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-only closure of the physical parameter/cache/export costs, including
the exact binary word lengths used by the subsequent offset producer. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BinaryArithmetic Bank Circuit Asymptotic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def nativeCost (a : Args) := Execute.runtimeBound a.1 a.2

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan )

def encodeTerm (t : Term Word) : Word :=
  Encoding.frame t.value ++ Encoding.frame t.inverseNode ++ Encoding.encodeList encodeFactor t.factors

def encodeRow (r : Row Word) : Word :=
  Encoding.frame r.delta ++ Encoding.encodeList encodeTerm r.terms

def factorCode (x : Word) (f : Factor Word) : Word :=
  pushWord f.inverseDifference ++ pushWord x ++ pushWord f.negativeNode ++
    operator false ++ operator true

def productCode (one x : Word) (fs : List (Factor Word)) : Word :=
  (fs.map (factorCode x)).flatten ++ pushWord one ++ operators true fs.length

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual correction-term iteration, from packed tables to a row record. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

def cost (values inverses negatives differences : List Word)
    (width rowWidth : Word) (positions : List ℕ) (i : ℕ) : ℕ :=
  i * (28 * width.length + 14 * rowWidth.length + 51) +
    30 * width.length + 15 * rowWidth.length + 63 +
    7 * (indices positions).length +
    RecordPrograms.budget (UniversalRowFactorLoop.callbackCost width.length i)
      (positions.reverse.map indexWord) +
    UniversalRowTermFraming.termCost (values.getD i []) (inverses.getD i [])
      (Encoding.encodeList UniversalRowProgram.encodeFactor
        (UniversalRowFactorLoop.factors differences negatives i positions)) +
    2 * rowWidth.length + 2 * i + 20

end SubexponentialSAT.Subexp.UniversalRowTermProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

def cost (t : Tables) (width rowWidth : Word) (positions : List ℕ) (bits : Word) : ℕ :=
  UniversalRowTermProgram.cost t.values t.inverses t.negatives (t.differences.getD bits.length [])
    width rowWidth positions bits.length

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowDataProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assemble a complete raw row from runtime scalar/cache tables. -/

namespace SubexponentialSAT.Subexp.UniversalRowDataProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)
open UniversalRowFactorLoop (indexWord)

def activeCost (t : Tables) (width rowWidth : Word) (positions : List ℕ) : ℕ :=
  7 * (UniversalRowTermProgram.indices positions).length + 8 +
    RecordPrograms.budget (UniversalRowLoop.cost t width rowWidth positions)
      (positions.reverse.map indexWord)

def cost (t : Tables) (width rowWidth : Word) (positions : List ℕ) (delta limit : Word) : ℕ :=
  10 * (UniversalRowTermProgram.indices positions).length + 13 * limit.length +
    6 * positions.length + 40 + activeCost t width rowWidth positions + 8 * delta.length + 11

end SubexponentialSAT.Subexp.UniversalRowDataProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan )

def inputSize (zero one : Word) (r : Row Word) : ℕ :=
  zero.length + one.length + (encodeRow r).length + 1

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end


