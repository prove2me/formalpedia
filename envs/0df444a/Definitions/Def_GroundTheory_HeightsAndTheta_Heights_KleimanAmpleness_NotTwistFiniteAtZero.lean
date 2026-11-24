-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:36.764127+00:00
-- url     : https://prove2.me/theorems/53d0118e-c81b-4230-a81a-0283f88880ea
-- title:
--   Not Twist Finite At Zero
-- statement:
--   Definitions and structural lemmas for Not Twist Finite At Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/NotTwistFiniteAtZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealXgen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
def TwistFiniteNe.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (G B : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x) (r : ℕ) (η : Fin (r + 1) → Ω),
    x ≠ 0 → IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy S x B.mods η →
    ∃ (n : ℕ) (bk : Fin n → ℕ) (s : Fin n → Ω),
      (∀ k, s k ∈ IndefiniteRowSideFullHecke.Kleiman.secs S x
        (IndefiniteRowSideFullHecke.Kleiman.lmul S G.mods (IndefiniteRowSideFullHecke.Kleiman.lpow S B.mods (bk k)))) ∧
      ∀ b : ℕ, IndefiniteRowSideFullHecke.Kleiman.secs S x (IndefiniteRowSideFullHecke.Kleiman.lmul S G.mods (IndefiniteRowSideFullHecke.Kleiman.lpow S B.mods b)) =
        ⨆ k, Submodule.span S (Set.image2 (· * ·) (IndefiniteRowSideFullHecke.Kleiman.secZ S η ((b : ℤ) - bk k) : Set Ω) {s k})
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


