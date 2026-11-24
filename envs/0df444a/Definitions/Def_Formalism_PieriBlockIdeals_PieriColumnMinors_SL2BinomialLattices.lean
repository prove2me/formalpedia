-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:51:17.606841+00:00
-- url     : https://prove2.me/theorems/4e018b0b-6af0-48b5-a4de-eaf993e04d2a
-- title:
--   SL2 Binomial Lattices
-- statement:
--   Definitions and structural lemmas for SL2 Binomial Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
def embedFinFirst {N k : ℕ} (hk : k ≤ N) : Fin k ↪ Fin N := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
def embedFinLast (N k : ℕ) : Fin (N - k) ↪ Fin N :=
  ⟨fun a => ⟨k + a.val, by have := a.isLt; omega⟩, fun a b h => by
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)⟩
end Formalism.CohomologicalDescent.SL2BinomialLattices


