-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_VandermondeEqVandermondeOf
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_VandermondeEqVandermondeOf
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:05:25.172742+00:00
-- url     : https://prove2.me/theorems/9aa2dd08-6e8e-4db8-8288-3d62e82b223b
-- title:
--   Vandermonde Eq Vandermonde Of
-- statement:
--   Definitions and structural lemmas for Vandermonde Eq Vandermonde Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/VandermondeEqVandermondeOf.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
def LemmaBLast.Statement : Prop :=
  ∀ (r a : ℕ), ∃ κ : ℚ,
    (κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) ∧
    ∀ lam : Fin r → ℕ, Antitone lam →
      dividedDifference 1 (r + a)
          (aeval (yRoot 1 r a SmallBlock.last 0) (schur (Fin r) lam) *
            vandermondeOf (yRoot 1 r a SmallBlock.last 0) *
              vandermondeOf (zRoot 1 r a SmallBlock.last 0)) =
        if ∀ i, a ≤ lam i then
          algebraMap (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
            (C κ * aeval (fun i : Fin (r + a) => C SmallBlock.last.sign * X ((0 : Fin 1), i))
              (schur (Fin (r + a)) (fun i => lam i - a)))
        else 0
namespace VandermondePushforward
def emb (j k : ℕ) : Fin (j + k) → Fin 1 × Fin (k + j) :=
  fun i => (0, Fin.cast (Nat.add_comm j k) i)
end VandermondePushforward
end
end GroundTheory.Heights₂.Heights.RestTerms


