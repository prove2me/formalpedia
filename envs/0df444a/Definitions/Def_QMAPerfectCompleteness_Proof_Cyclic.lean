-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
-- name    : QMAPerfectCompleteness_Proof_Cyclic
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:46:22.3072+00:00
-- url     : https://prove2.me/theorems/28495162-e79e-47ad-8498-366e30ce6775
-- title:
--   Hermiticity of the acceptance operator
-- statement:
--   Provides the retained Hermitian acceptance-operator fact used by the cyclic-constraint analysis. This is an operator-theoretic auxiliary for applying spectral and quadratic-form arguments to the verifier acceptance matrix.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Section 3.2, the cyclic-constraint analysis. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/Cyclic.lean, retained declaration span lines 14–22.

/- Generated from Solutions.Cyclic by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates



open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CyclicProof

variable {G : GateSet}



theorem acceptance_hermitian (V : Verifier G) : V.acceptanceOperator.IsHermitian := by
  have hP : V.acceptProjector.IsHermitian := by
    unfold Verifier.acceptProjector
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext w
    simp only [Pi.star_apply]
    split <;> simp
  have h := Matrix.isHermitian_conjTranspose_mul_mul (V.unitary * V.ancillaZero) hP
  simpa only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h



















open VerifierAnalysis











open scoped ComplexOrder





open scoped Matrix.Norms.L2Operator







end QMAPerfectCompleteness.Main.CyclicProof


