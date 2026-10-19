-- Prove2me | Definitions.Def_QAlgorithms_Defs_MatrixQSVTCircuits
-- name    : QAlgorithms_Defs_MatrixQSVTCircuits
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:30.146192+00:00
-- url     : https://prove2.me/theorems/07cbf1a2-39cc-4552-aff1-8462f4e179b0
-- title:
--   MatrixQSVTCircuits
-- statement:
--   MatrixQSVTCircuits
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MatrixQSVTCircuits.lean

import Definitions.Def_QAlgorithms_Defs_MatrixQSVTCompletion
import Definitions.Def_QAlgorithms_Defs_FiniteOraclePrograms
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.MatrixQSVT

/-- QAlgorithms.MatrixQSVT.embeddingProjector: arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8. Source domains are explicit below. -/
def embeddingProjector {I K : Type*} [Fintype I] [DecidableEq K] (e : I ↪ K) : Matrix K K ℂ :=
  ∑ i, Matrix.single (e i) (e i) 1

/-- QAlgorithms.MatrixQSVT.projectorMixer: arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8. Source domains are explicit below. -/
def projectorMixer {K : Type*} [DecidableEq K] (q : ℕ)
    (R : Matrix (Qubits q) (Qubits q) ℂ) (Pi : Matrix K K ℂ) :
    Matrix (Qubits q × K) (Qubits q × K) ℂ :=
  Matrix.kronecker R Pi + Matrix.kronecker (1 : Matrix (Qubits q) (Qubits q) ℂ) (1-Pi)

/-- QAlgorithms.MatrixQSVT.SynthesisData: arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8. Source domains are explicit below. -/
structure SynthesisData (I O K : Type) [Fintype I] [Fintype O] [Fintype K] [Nonempty I] [Nonempty O] [Nonempty K] [DecidableEq K]
    (q d : ℕ) where
  input : I ↪ K
  output : O ↪ K
  mixers : Fin (d+1) → Matrix.unitaryGroup (Qubits q) ℂ
  known : Fin (d+1) → Matrix.unitaryGroup (Qubits q × K) ℂ
  known_eq : ∀ j, (known j : Matrix _ _ ℂ) = projectorMixer q (mixers j)
    (if j.val%2 = 0 then embeddingProjector input else embeddingProjector output)

/-- QAlgorithms.MatrixQSVT.SynthesisData.circuit: arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8. Source domains are explicit below. -/
def SynthesisData.circuit {I O K : Type} [Fintype I] [Fintype O] [Fintype K] [Nonempty I] [Nonempty O] [Nonempty K] [DecidableEq K]
    {q d : ℕ} (S : SynthesisData I O K q d) :
    FiniteOracleCircuit (fun _ : Fin 1 => K) (fun _ => false) (Qubits q × K) :=
  let layout : (Qubits q × K) ≃ K × Fin (2^q) :=
    (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl K) (bitsEquivFin q))
  [.known (S.known 0)] ++ (List.ofFn fun j : Fin d =>
    [FiniteOracleStep.query 0 (decide (j.val%2 = 1)) (2^q) layout,
      .known (S.known j.succ)]).flatten


/-- Parity-dependent output signal layout, arxiv-2408.01439v4 PDF pp.3,7-8. -/
def outputSignalEmbedding {I O K : Type} [Fintype I] [Fintype O] [Fintype K] [Nonempty I] [Nonempty O] [Nonempty K] [DecidableEq K]
    {q d : ℕ} (S : SynthesisData I O K q d) : OutputIndex d I O ↪ K :=
  if h : d%2 = 0 then by simpa only [OutputIndex,if_pos h] using S.input
  else by simpa only [OutputIndex,if_neg h] using S.output

/-- Complete flag-zero branch in equation (38), with input/row/column/signal embeddings computed
from the source's known layouts; arxiv-2408.01439v4 PDF pp.7-8. -/
def IsFlaggedRealization {I O K : Type} [Fintype I] [Fintype O] [Fintype K] [Nonempty I] [Nonempty O] [Nonempty K]
    [DecidableEq I] [DecidableEq K] {r c d q : ℕ}
    (P : PolynomialData r c d) (S : SynthesisData I O K q d)
    (mixingLayout : Qubits q ≃ Bool × Qubits P.mixingQubits)
    (U : Matrix K K ℂ) (A : Matrix O I ℂ) : Prop :=
  ∀ psi : EuclideanSpace ℂ (Fin c × I),
    let input := fun i : Fin c × I => (mixingLayout.symm (false,P.cols i.1), S.input i.2)
    let output := fun i : Fin r × OutputIndex d I O =>
      (mixingLayout.symm (false,P.rows i.1),outputSignalEmbedding S i.2)
    let start : EuclideanSpace ℂ (Qubits q × K) := WithLp.toLp 2 fun z =>
      ∑ i, if input i = z then psi i else 0
    let good := (matrixTransform P A).mulVec (WithLp.ofLp psi)
    ∀ z, (mixingLayout z.1).1 = false →
      act (S.circuit.unitary (fun _ => U)) start z = ∑ i, if output i = z then good i else 0

example {I O K : Type} [Fintype I] [Fintype O] [Fintype K] [Nonempty I] [Nonempty O] [Nonempty K] [DecidableEq K]
    {q : ℕ} (S : SynthesisData I O K q 0) (U V : Matrix K K ℂ) :
    S.circuit.unitary (fun _ => U) = S.circuit.unitary (fun _ => V) := rfl

end QAlgorithms.MatrixQSVT


