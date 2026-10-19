-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapO03_Model
-- name    : QAlgorithms_Papers_RoadmapO03_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:15.258851+00:00
-- url     : https://prove2.me/theorems/36bbfbda-9cef-495a-ba51-8d8bb195200c
-- title:
--   Quantum SDP Solvers: Large Speed-ups, Optimality, and Applications to Quantum Learning: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Quantum SDP Solvers: Large Speed-ups, Optimality, and Applications to Quantum Learning, arXiv:1710.02581v3, https://arxiv.org/abs/1710.02581v3. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_JointLowRankGibbsContracts
noncomputable section

open scoped Matrix ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapO03

open QAlgorithms.LowRankGibbs

/-- Source D.1 register encoding: index j, then the two binary trace answers.
Each factor uses the frozen most-significant-bit convention (PDF p.21, Eq. (D.1)). -/
def traceInputEmbedding (m : ℕ) (F : TraceBinaryFormat) :
    Matrix (Qubits (Nat.clog 2 m + F.width + F.width))
      (Fin m × (Qubits F.width × Qubits F.width)) ℂ :=
  Matrix.of fun z p =>
    if z = Fin.append (Fin.append (natToBits (Nat.clog 2 m) p.1) p.2.1) p.2.2 then 1 else 0

/-- Source D.2 register encoding: j and the four n-valued purification registers.
Each finite label is encoded separately, preserving the tensor factors (PDF p.21, Eq. (D.2)). -/
def prepInputEmbedding (n m : ℕ) :
    Matrix (Qubits (Nat.clog 2 m + Nat.clog 2 n + Nat.clog 2 n + Nat.clog 2 n + Nat.clog 2 n))
      (Fin m × ((Fin n × Fin n) × (Fin n × Fin n))) ℂ :=
  Matrix.of fun z p =>
    if z = Fin.append
        (Fin.append (Fin.append (Fin.append (natToBits (Nat.clog 2 m) p.1)
          (natToBits (Nat.clog 2 n) p.2.1.1)) (natToBits (Nat.clog 2 n) p.2.1.2))
          (natToBits (Nat.clog 2 n) p.2.2.1)) (natToBits (Nat.clog 2 n) p.2.2.2)
    then 1 else 0

/-- A supplied qubit unitary represents the source oracle on its encoded register.
Its action outside the embedding is unrestricted; no known identity sector is supplied. -/
def IsEncodedInput {I : Type} [Fintype I] {a : ℕ}
    (J : Matrix (Qubits a) I ℂ) (O : Matrix I I ℂ)
    (U : Matrix (Qubits a) (Qubits a) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup _ ℂ ∧ U * J = J * O

/-- Qubit widths of D.1 and D.2, encoding each source tensor factor separately.
Source: arXiv:1710.02581v3, PDF p.21, Eqs. (D.1) and (D.2). -/
def inputArities (n m : ℕ) (F : TraceBinaryFormat) : Fin 2 → ℕ :=
  Fin.cases (Nat.clog 2 m + F.width + F.width)
    (fun _ => Nat.clog 2 m + Nat.clog 2 n + Nat.clog 2 n + Nat.clog 2 n + Nat.clog 2 n)

/-- The supplied qubit oracles restrict to D.1 and D.2, respectively.
Finite-register completions and unused-qubit-label completions remain arbitrary.
Source: arXiv:1710.02581v3, PDF p.21, Eqs. (D.1) and (D.2). -/
def IsInputOracles {n m : ℕ} {F : TraceBinaryFormat}
    (Otr : Matrix (Fin m × (Qubits F.width × Qubits F.width))
      (Fin m × (Qubits F.width × Qubits F.width)) ℂ)
    (Oprep : Matrix (Fin m × ((Fin n × Fin n) × (Fin n × Fin n)))
      (Fin m × ((Fin n × Fin n) × (Fin n × Fin n))) ℂ)
    (O : (k : Fin 2) → Matrix (Qubits (inputArities n m F k))
      (Qubits (inputArities n m F k)) ℂ) : Prop :=
  IsEncodedInput (traceInputEmbedding m F) Otr (O 0) ∧
    IsEncodedInput (prepInputEmbedding n m) Oprep (O 1)


end QAlgorithms.Papers.RoadmapO03


