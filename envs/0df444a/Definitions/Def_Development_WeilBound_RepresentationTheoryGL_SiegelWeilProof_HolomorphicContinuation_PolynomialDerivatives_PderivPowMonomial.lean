-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:21.027991+00:00
-- url     : https://prove2.me/theorems/1452b774-8328-46d1-a70c-cebfe45f9d28
-- title:
--   Pderiv Pow Monomial
-- statement:
--   Definitions and structural lemmas for Pderiv Pow Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
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
namespace PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
variable (ε : Fin m → Bool)
def GoodT (t : σ ⊕ σ →₀ ℕ) : Prop := ∀ k, (t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0) → inF1 ε k
end PositivityTheory.Rg.Sw.LC.B1
namespace PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.B1
end PositivityTheory.Rg.Sw.LC


