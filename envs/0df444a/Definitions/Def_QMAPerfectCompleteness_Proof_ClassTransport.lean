-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
-- name    : QMAPerfectCompleteness_Proof_ClassTransport
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:54:29.247899+00:00
-- url     : https://prove2.me/theorems/67d564a2-6ba6-47c3-85f3-5d798d490c77
-- title:
--   Uniform continuation on valid verifier encodings
-- statement:
--   Defines the compiler runtime property used in class reductions: every polynomial-time generator producing valid G-verifier encodings on every input remains polynomial-time after the compiler code map. The condition includes inputs outside the promise and requires no behavior specification for malformed codes.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ClassTransport.lean, lines 13–17.

/- Generated from Solutions.ClassTransport by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
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
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Class assembly needs only continuations of generators whose outputs are verifier codes.
No general polynomial-time composition theorem, nor a runtime specification on malformed
compiler inputs, is required by these reductions. The runtime hypotheses below remain explicit. -/
namespace QMAPerfectCompleteness.Main.ClassTransport
open QAlgorithms.Complexity (Str PolyTimeComputable)

/-- The precise runtime property needed in a class reduction. The incoming generator produces
a valid verifier on every input, including inputs outside the promise. -/
def UniformOnVerifierCodes (G : GateSet) (code : Str → Str) : Prop :=
  ∀ (gen : Str → Str) (V : Str → Verifier G), PolyTimeComputable gen →
    (∀ x, gen x = (V x).encode) → PolyTimeComputable (fun x => code (gen x))









end QMAPerfectCompleteness.Main.ClassTransport


