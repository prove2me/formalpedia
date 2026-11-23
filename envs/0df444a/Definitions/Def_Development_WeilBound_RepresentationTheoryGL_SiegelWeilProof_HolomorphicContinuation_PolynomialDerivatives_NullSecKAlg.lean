-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullSecKAlg
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullSecKAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:09:33.716386+00:00
-- url     : https://prove2.me/theorems/8e5a8288-2a12-46b0-9e18-00e42b96f4d0
-- title:
--   Null Sec KAlg
-- statement:
--   Definitions and structural lemmas for Null Sec KAlg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullSecKAlg.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
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
namespace PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
def MomLin : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (P Q : PX m n) (r : ℂ), mom c (P + Q) = mom c P + mom c Q ∧ mom c (r • P) = r * mom c P
end PositivityTheory.Rg.Sw.LC


