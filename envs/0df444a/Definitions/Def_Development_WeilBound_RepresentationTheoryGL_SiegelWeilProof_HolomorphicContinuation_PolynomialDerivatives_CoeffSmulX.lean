-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:36.605887+00:00
-- url     : https://prove2.me/theorems/38841a6b-fd38-49ea-ae00-e02e6576b723
-- title:
--   Coeff Smul X
-- statement:
--   Definitions and structural lemmas for Coeff Smul X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
namespace PositivityTheory.Rg.Sw.LC
namespace CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
def symW (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) : ℂ := ∏ k ∈ u.support, ((u k).factorial : ℂ)
end CoreC
end PositivityTheory.Rg.Sw.LC


