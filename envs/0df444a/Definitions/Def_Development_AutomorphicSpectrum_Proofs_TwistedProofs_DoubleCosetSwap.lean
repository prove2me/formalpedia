-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DoubleCosetSwap
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_DoubleCosetSwap
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:34:14.315431+00:00
-- url     : https://prove2.me/theorems/de885c4f-63ab-4ff7-a0a2-c07df0937cc0
-- title:
--   Double Coset Swap
-- statement:
--   Definitions and structural lemmas for Double Coset Swap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_UG_P_finite_cosets_in_doset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertZeta
variable {G : Type} [Group G] {K : Subgroup G}
def cosetsIn (hK : IsCommensurated K) (g : G) : Finset (G ⧸ K) :=
  (P.finite_cosets_in_doset hK g).toFinset
def dosetOf (x : G ⧸ K) : Set G := DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)
end GlobalTheory.CompanionTheory.InertZeta


