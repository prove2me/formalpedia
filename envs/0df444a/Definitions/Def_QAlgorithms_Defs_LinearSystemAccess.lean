-- Prove2me | Definitions.Def_QAlgorithms_Defs_LinearSystemAccess
-- name    : QAlgorithms_Defs_LinearSystemAccess
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:12.953093+00:00
-- url     : https://prove2.me/theorems/81233162-7030-4ba7-8df4-5b6756bcc544
-- title:
--   LinearSystemAccess
-- statement:
--   LinearSystemAccess
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\LinearSystemAccess.lean

import Definitions.Def_QAlgorithms_Defs_LinearSystems
import Definitions.Def_QAlgorithms_Defs_CircuitResources
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.LinearSystemAccess

/-- QAlgorithms.LinearSystemAccess.IsWorkspaceStatePrep: arxiv-1511.02306v2 PDF p.3, arxiv-1511.02306v2 PDF p.8. Source domains are explicit below. -/
def IsWorkspaceStatePrep {N w : ℕ} (b : EuclideanSpace ℂ (Fin N))
    (O : Matrix (Qubits (Nat.clog 2 N+w)) (Qubits (Nat.clog 2 N+w)) ℂ) : Prop :=
  0 < N ∧ b ≠ 0 ∧ O ∈ Matrix.unitaryGroup _ ℂ ∧
    ∃ garbage : EuclideanSpace ℂ (Qubits w), IsState garbage ∧
      ∀ z, act O (zeroKet _) z =
        padState (Nat.clog 2 N) (normalizedVec b) (qubitsAppendEquiv (Nat.clog 2 N) w z).1 *
          garbage (qubitsAppendEquiv (Nat.clog 2 N) w z).2

/-- QAlgorithms.LinearSystemAccess.BinaryComplexFormat: arxiv-1511.02306v2 PDF p.3, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
structure BinaryComplexFormat where
  integerBits : ℕ
  fractionBits : ℕ

/-- QAlgorithms.LinearSystemAccess.BinaryComplexFormat.componentBits: arxiv-1511.02306v2 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def BinaryComplexFormat.componentBits (F : BinaryComplexFormat) : ℕ :=
  F.integerBits+F.fractionBits+1

/-- QAlgorithms.LinearSystemAccess.BinaryComplexFormat.width: arxiv-1511.02306v2 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def BinaryComplexFormat.width (F : BinaryComplexFormat) : ℕ := F.componentBits+F.componentBits

/-- QAlgorithms.LinearSystemAccess.BinaryComplexFormat.realValue: arxiv-1511.02306v2 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def BinaryComplexFormat.realValue (F : BinaryComplexFormat) (z : Qubits F.componentBits) : ℝ :=
  (if z (Fin.last (F.integerBits+F.fractionBits)) then -1 else 1)*((bitsToNat (Fin.init z) : ℝ)/(2 : ℝ)^F.fractionBits)

/-- QAlgorithms.LinearSystemAccess.BinaryComplexFormat.decode: arxiv-1511.02306v2 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def BinaryComplexFormat.decode (F : BinaryComplexFormat) (z : Qubits F.width) : ℂ :=
  (F.realValue (qubitsAppendEquiv F.componentBits F.componentBits z).1 : ℂ)+
    Complex.I*(F.realValue (qubitsAppendEquiv F.componentBits F.componentBits z).2 : ℂ)

example (F : BinaryComplexFormat) : F.decode 0 = 0 := by
  simp [BinaryComplexFormat.decode, BinaryComplexFormat.realValue, qubitsAppendEquiv, bitsToNat, Fin.init, Pi.zero_apply]

end QAlgorithms.LinearSystemAccess


