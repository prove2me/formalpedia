-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:46.814817+00:00
-- url     : https://prove2.me/theorems/5c08ab83-4de0-47e2-b79b-1b595d770daf
-- title:
--   Sum Pderiv XMem
-- statement:
--   Definitions and structural lemmas for Sum Pderiv XMem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
def dPhi (c : ℝ) (k : Fin m × Fin n × Bool) (P : PX m n) : PX m n := pderiv k P - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * P
def fE (i j : Fin n) (R : PX m n) : PX m n := ∑ a, X (a, j, false) * pderiv (a, i, false) R
def fA (i j : Fin n) (R : PX m n) : PX m n := ∑ a, X (a, i, true) * pderiv (a, j, true) R
def Bf (ε : Fin m → Bool) (i j : Fin n) (U V : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * (pderiv (a, j, true) U * pderiv (a, i, false) V + pderiv (a, i, false) U * pderiv (a, j, true) V)
def fL (ε : Fin m → Bool) (i j : Fin n) (R : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * pderiv (a, j, true) (pderiv (a, i, false) R)
end PositivityTheory.Rg.Sw.LC.NullS


