-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullOperatorEvaluation
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullOperatorEvaluation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:05.888913+00:00
-- url     : https://prove2.me/theorems/9bd5e6f4-402f-45a6-884d-ec53397e6c9d
-- title:
--   Null Operator Evaluation
-- statement:
--   Definitions and structural lemmas for Null Operator Evaluation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
namespace PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
def Qv (c : ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) : PX m n :=
  ∑ k, C (crd k v) * (pderiv k P + P * pderiv k (Sg c))
def ev1 (k : Fin m × Fin n × Bool) (z : ℂ) : Fin m → Fin n → ℂ := fun a i => if a = k.1 ∧ i = k.2.1 then z else 0
end PositivityTheory.Rg.Sw.LC.NullS


