-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
-- name    : QMAPerfectCompleteness_Proof_CertificateLogicalSelect
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:10:01.812907+00:00
-- url     : https://prove2.me/theorems/bcb3acf6-abc7-49df-81e6-40a0df3985c4
-- title:
--   Certificate-diagonal logical SELECT factors
-- statement:
--   Extends the fixed-certificate middle and post-call basis actions to the product with the retained certificate register. The certificate values control the logical branch actions and the active-range sign, while every operation preserves the certificate label.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateLogicalSelect.lean, lines 12–19.

/- Generated from Solutions.CertificateLogicalSelect by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers



/-! Certificate-diagonal logical assembly of the coherent block SELECT. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CertificateLogicalSelect
open BlockImplements BlockLogicalSelect CertificateMixture
variable (V : Verifier gatesG2)
abbrev Logical := CoherentCertificate.ComputationReg V

noncomputable def middle (p : Logical V) : Logical V :=
  (BlockImplements.midLogical V p.2.2.1.val p.2.2.2.val p.1,p.2)
noncomputable def post (p : Logical V) : Logical V :=
  (BlockImplements.postLogical V p.2.1 p.2.2.1.val p.2.2.2.val p.1,p.2)
def sign (p : Logical V) : ℂ :=
  if BlockCompiler.Layout.rangeTruth p.2.2.1.val p.2.2.2.val p.1.1.val 5 then -1 else 1

















end QMAPerfectCompleteness.Main.CertificateLogicalSelect


