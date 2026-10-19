-- Prove2me | Definitions.Def_QAlgorithms_Defs_AQCLinearSystemData
-- name    : QAlgorithms_Defs_AQCLinearSystemData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:16.789308+00:00
-- url     : https://prove2.me/theorems/9ae5451b-11df-49a5-9054-905f2e903cb8
-- title:
--   AQCLinearSystemData
-- statement:
--   AQCLinearSystemData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\AQCLinearSystemData.lean

import Definitions.Def_QAlgorithms_Defs_LinearSystemTargets
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_Information
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.AQCP

/-- QAlgorithms.AQCP.complementProjector: arxiv-1909.05500v3 PDF p.3. Source domains are explicit below. -/
def complementProjector {I : Type*} [Fintype I] [DecidableEq I] (b : EuclideanSpace ℂ I)
    (hb : IsState b) : Matrix I I ℂ := 1-pureDensity b

/-- QAlgorithms.AQCP.initialHamiltonian: arxiv-1909.05500v3 PDF p.3. Source domains are explicit below. -/
def initialHamiltonian {I : Type*} [Fintype I] [DecidableEq I] (b : EuclideanSpace ℂ I)
    (hb : IsState b) : Matrix (Bool × I) (Bool × I) ℂ := Matrix.kronecker pauliX (complementProjector b hb)

/-- QAlgorithms.AQCP.finalHamiltonian: arxiv-1909.05500v3 PDF p.3. Source domains are explicit below. -/
def finalHamiltonian {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : A.PosDef) (b : EuclideanSpace ℂ I) (hb : IsState b) : Matrix (Bool × I) (Bool × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then 0
    else if p.1 then (complementProjector b hb*A) p.2 q.2 else (A*complementProjector b hb) p.2 q.2

/-- QAlgorithms.AQCP.gapLowerBound: arxiv-1909.05500v3 PDF p.4. Source domains are explicit below. -/
def gapLowerBound (kappa : ℝ) (hk : 1 ≤ kappa) (u : ℝ) : ℝ := 1-u+u/kappa

example (u : ℝ) : gapLowerBound 1 le_rfl u = 1 := by simp [gapLowerBound]

example {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (hA : A.PosDef)
    (b : EuclideanSpace ℂ I) (hb : IsState b) (i j : I) :
    finalHamiltonian A hA b hb (false,i) (true,j) = (A*complementProjector b hb) i j := by
  simp [finalHamiltonian]

end QAlgorithms.AQCP


