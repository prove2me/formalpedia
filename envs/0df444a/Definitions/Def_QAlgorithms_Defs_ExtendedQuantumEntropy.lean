-- Prove2me | Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
-- name    : QAlgorithms_Defs_ExtendedQuantumEntropy
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:21:00.399034+00:00
-- url     : https://prove2.me/theorems/006cc6c0-6a11-4d92-b529-e898cd91f602
-- title:
--   ExtendedQuantumEntropy
-- statement:
--   ExtendedQuantumEntropy
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ExtendedQuantumEntropy.lean

import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_SDP
noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.QuantumLoss

/-- Umegaki relative entropy on normalized states, using natural logs and infinity on
support violations (2305.18519 p.11, Def.2.28; p.6 boundary convention).
The kernel guard is the support-inclusion condition supp(rho) ⊆ supp(sigma). -/
def umegakiEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (_hrho : IsDensityMatrix rho) (_hsigma : IsDensityMatrix sigma) :
    ℝ≥0∞ :=
  if LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin then
    ENNReal.ofReal
      (cfc (fun x : ℝ => x*Real.log x) rho-rho*cfc Real.log sigma).trace.re
  else ⊤

example {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (h : ¬ LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    umegakiEntropy rho sigma hrho hsigma = ⊤ := by
  simp [umegakiEntropy, h]

example (h : IsDensityMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    umegakiEntropy 1 1 h h = 0 := by
  simp [umegakiEntropy, cfc_one]

end QAlgorithms.QuantumLoss


