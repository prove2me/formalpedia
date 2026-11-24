-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsKrullHeightOne
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsKrullHeightOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:36.525432+00:00
-- url     : https://prove2.me/theorems/e3a632ce-b7ce-4ea2-93fb-49f31e71003a
-- title:
--   Statements Krull Height One
-- statement:
--   Definitions and structural lemmas for Statements Krull Height One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/StatementsKrullHeightOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
def KrullHeightOne.Hyp {A : Type*} [CommRing A] (p q : A) : Prop :=
  q ≠ 0 ∧ ¬ q ∣ p
def KrullHeightOne.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (p q : A),
    KrullHeightOne.Hyp p q →
      ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧ ∃ c ∉ P, ∃ t ∈ P, c * q = t * p
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB


