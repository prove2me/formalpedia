-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:23.618844+00:00
-- url     : https://prove2.me/theorems/2c4bb096-feca-41a6-871d-4939b4721fcd
-- title:
--   Unramified Quotient Card
-- statement:
--   Definitions and structural lemmas for Unramified Quotient Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuotientCard.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.UnrDens
def mulPow {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : R →+ R ⧸ lev ϖ (k + 1) :=
  ((Ideal.Quotient.mk (lev ϖ (k + 1))).toAddMonoidHom).comp (AddMonoidHom.mulLeft (ϖ ^ k))
end GlobalTheory.CompanionTheory.UnrDens


