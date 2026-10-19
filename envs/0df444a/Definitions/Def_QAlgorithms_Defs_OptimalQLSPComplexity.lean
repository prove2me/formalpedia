-- Prove2me | Definitions.Def_QAlgorithms_Defs_OptimalQLSPComplexity
-- name    : QAlgorithms_Defs_OptimalQLSPComplexity
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:26:05.653857+00:00
-- url     : https://prove2.me/theorems/35088816-0105-418d-8c18-8fe28752616d
-- title:
--   OptimalQLSPComplexity
-- statement:
--   OptimalQLSPComplexity
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\OptimalQLSPComplexity.lean

import Definitions.Def_QAlgorithms_Defs_TwoSidedSparseAccess
import Definitions.Def_QAlgorithms_Defs_HeraldedLinearSystems
import Definitions.Def_QAlgorithms_Defs_RetainedQueryPrograms
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.OptimalQLSP

/-- QAlgorithms.OptimalQLSP.oracleWidths: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.2, arxiv-2609.35660v1 PDF p.16, arxiv-2609.35660v1 PDF p.15, arxiv-2609.35660v1 PDF p.17. Source domains are explicit below. -/
def oracleWidths (N b w : ℕ) : Fin 5 → ℕ :=
  ![Nat.clog 2 N+Nat.clog 2 N,Nat.clog 2 N+Nat.clog 2 N+b,
    Nat.clog 2 N+Nat.clog 2 N,Nat.clog 2 N+Nat.clog 2 N+b,Nat.clog 2 N+w]

/-- QAlgorithms.OptimalQLSP.OracleRegisters: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.2, arxiv-2609.35660v1 PDF p.16, arxiv-2609.35660v1 PDF p.15, arxiv-2609.35660v1 PDF p.17. Source domains are explicit below. -/
abbrev OracleRegisters (N b w : ℕ) (k : Fin 5) := Qubits (oracleWidths N b w k)

/-- QAlgorithms.OptimalQLSP.IsUniversalSolver: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.2, arxiv-2609.35660v1 PDF p.16. Source domains are explicit below. -/
def IsUniversalSolver {N b w I work : ℕ} (hN : 0 < N) (d : ℕ) (kappa eps : ℝ)
    (decode : Qubits b → ℂ) (layout : Fin I ≃ Fin N × Fin work)
    (start : EuclideanSpace ℂ (Fin I)) (normalized : IsState start)
    (P : RetainedOracle.QueryProgram (OracleRegisters N b w) (fun _ => true) (Fin I)) (budget : ℕ) : Prop :=
  1 ≤ d ∧ d ≤ N ∧ 1 ≤ kappa ∧ 0 < eps ∧ eps < 1 ∧
    ∀ A : Matrix (Fin N) (Fin N) ℂ, ∀ hA : IsUnit A,
    IsSparse A d → specNorm A ≤ 1 → specNorm A⁻¹ ≤ kappa →
    ∀ bvec : EuclideanSpace ℂ (Fin N), ∀ hb : bvec ≠ 0,
    ∀ O : (k : Fin 5) → Matrix (OracleRegisters N b w k) (OracleRegisters N b w k) ℂ,
      LinearSystemAccess.IsTwoSidedSparseAccess A d decode (O 0) (O 2) (O 1) (O 3) →
      LinearSystemAccess.IsWorkspaceStatePrep bvec (O 4) →
        IsTraceHeraldedSolution hN A hA bvec hb
          (RetainedOracle.retainedOutput layout P O (pureDensity start) true)
          (RetainedOracle.retainedOutput layout P O (pureDensity start) false) eps ∧
        RetainedOracle.worstCaseQueries P O (fun k => if k = 4 then 0 else 1) (pureDensity start) ≤ budget

/-- QAlgorithms.OptimalQLSP.queryComplexity: arxiv-2609.35660v1 PDF p.2, arxiv-2609.35660v1 PDF p.15, arxiv-2609.35660v1 PDF p.16, arxiv-2609.35660v1 PDF p.17. Source domains are explicit below. -/
def queryComplexity (d : ℕ) (hd : 1 ≤ d) (kappa eps : ℝ)
    (hkappa : 1 ≤ kappa) (heps : 0 < eps ∧ eps < 1) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ hN : 0 < N, ⨆ hd : d ≤ N, ⨆ b : ℕ, ⨆ w : ℕ, ⨆ decode : Qubits b → ℂ,
    sInf {q : ℝ≥0∞ | ∃ budget : ℕ, q = budget ∧ ∃ I work : ℕ,
      ∃ layout : Fin I ≃ Fin N × Fin work, ∃ start : EuclideanSpace ℂ (Fin I),
      ∃ normalized : IsState start,
      ∃ P : RetainedOracle.QueryProgram (OracleRegisters N b w) (fun _ => true) (Fin I),
        IsUniversalSolver hN d kappa eps decode layout start normalized P budget}

example (N b w : ℕ) : oracleWidths N b w 4 = Nat.clog 2 N+w := rfl

end QAlgorithms.OptimalQLSP


