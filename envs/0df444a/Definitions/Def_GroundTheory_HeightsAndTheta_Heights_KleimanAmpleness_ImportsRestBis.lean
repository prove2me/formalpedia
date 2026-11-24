-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestBis
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:16.320179+00:00
-- url     : https://prove2.me/theorems/dee509b8-75a2-4983-a08d-2428b35348dc
-- title:
--   Imports Rest Bis
-- statement:
--   Definitions and structural lemmas for Imports Rest Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ImportsRestBis.lean

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
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
def PolyOfDiffsExact.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (h : (K → ℤ) → ℚ),
    (∀ k, ∃ q : MvPolynomial K ℚ, ∀ m : K → ℤ, h m - h (m - Pi.single k 1) = eval (fun j => (m j : ℚ)) q) →
    ∃ p : MvPolynomial K ℚ, ∀ m : K → ℤ, h m = eval (fun j => (m j : ℚ)) p
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


