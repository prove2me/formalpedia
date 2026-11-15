-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesTM
-- name    : QMAPerfectCompleteness_Proof_RecountGatesTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:02:48.663774+00:00
-- url     : https://prove2.me/theorems/2a46b527-e17e-4a6d-a38e-e362cecb1b28
-- title:
--   Finite parsing with a provisional gate count
-- statement:
--   Defines the source format and execution bound for running the finite-plan gate parser when the initial gate-count field is only a placeholder. The complete execution recounts the actual body rather than trusting that field.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecountGatesTM.lean, retained declaration span lines 10–43.

/- Generated from Solutions.RecountGatesTM by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic


/-! Recount literal generated gate bodies with the existing finite-plan parser. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.FinitePlanCompiler
open QAlgorithms.Complexity (Str encNat)
variable (C : Config)

def sourceWithCount (m a o : ℕ) (rs : List Recipe) (discardedCount : ℕ) : Str :=
  sourceHeader m a o++encNat discardedCount++sourceBody rs

def fullTimeWithCount (m a o : ℕ) (rs : List Recipe) (discardedCount : ℕ) : ℕ :=
  2*(sourceHeader m a o).length+discardedCount+bodyTime C rs+(targetBody C rs).length+targetCount C rs+(m+a)+headerDelta C+9

lemma full_run_with_count (m a o : ℕ) (rs : List Recipe) (discardedCount : ℕ)
    (hv : ∀ r ∈ rs, r.Valid ∧ r.2 3 = m+a) :
    (transition C)^[fullTimeWithCount C m a o rs discardedCount] (some (initList (machine C) (sourceWithCount m a o rs discardedCount))) =
      some (haltList (machine C) (targetCode C m a o rs)) := by
  have hi : initList (machine C) (sourceWithCount m a o rs discardedCount) = cfg C (.headerStart 0) none {input := sourceWithCount m a o rs discardedCount} := by
    simp only [initList,cfg,machine,Data.stacks]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hh := header_all_run C m a o (encNat discardedCount++sourceBody rs)
  have hd := discard_run C (some false) {header := (targetHeader C m a o).reverse,wires := baseWires (m+a)} discardedCount (sourceBody rs)
  have hb := body_run C (m+a) rs (some false) {header := (targetHeader C m a o).reverse,wires := baseWires (m+a)} [] rfl rfl hv
  simp only [List.append_nil,List.nil_append] at hh hd hb
  have he := gate_nil_step C (if rs = [] then some false else none)
    {header := (targetHeader C m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount C rs) true,body := (targetBody C rs).reverse}
  change (transition C)^[1] (some (cfg C .gate (if rs = [] then some false else none)
    {header := (targetHeader C m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount C rs) true,body := (targetBody C rs).reverse})) = _ at he
  have hc := clear_actual_run C 3 none
    {header := (targetHeader C m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount C rs) true,body := (targetBody C rs).reverse}
    (m+a) (by simp [baseWires])
  have hz : Function.update (baseWires (m+a)) 3 [] = fun _ => [] := by
    funext j
    fin_cases j <;> simp [baseWires]
  simp only [hz,nextClear,Fin.isValue,Fin.reduceFinMk,Fin.reduceEq,ite_false] at hc
  have hf := finish_all_run C (targetHeader C m a o) (targetBody C rs) (targetCount C rs) none
  have h := run_trans C (run_trans C (run_trans C (run_trans C (run_trans C hh hd) hb) he) hc) hf
  rw [hi]
  convert h using 1 <;> simp only [fullTimeWithCount,sourceWithCount,targetCode,List.append_assoc,targetHeader_length C] <;> congr 1 <;> omega

end QMAPerfectCompleteness.Uniformity.FinitePlanCompiler


