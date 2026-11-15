-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
-- name    : QMAPerfectCompleteness_Proof_DyadicPreservation
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:50:18.165211+00:00
-- url     : https://prove2.me/theorems/486ef7b3-4210-400d-aba7-12ab47975895
-- title:
--   Density-matrix embedding for the real simulation
-- statement:
--   Defines the honest simulated proof density matrix by taking one half of the complex embedding of the real representation and reindexing its simulation bit and original proof bits. The factor one half accounts for the two copies of the source spectrum and is used to preserve normalization and acceptance probability.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/DyadicPreservation.lean, lines 27–32.

/- Generated from Solutions.DyadicPreservation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



open Matrix
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.DyadicCompiler
open VerifierAnalysis CyclicProof







/-- The honest source density matrix becomes R(ρ)/2. Both copies of its spectrum have half
weight, so its trace is exactly one and acceptance probability is unchanged. -/
noncomputable def simulatedDensity (V : Verifier gatesHP) (ρ : Matrix V.Proof V.Proof ℂ) :
    Matrix (compileVerifier V).Proof (compileVerifier V).Proof ℂ :=
  (((1 / 2 : ℂ) • complexRealRep ρ)).submatrix
    (splitProof V.proofQubits) (splitProof V.proofQubits)

















end QMAPerfectCompleteness.Main.DyadicCompiler


