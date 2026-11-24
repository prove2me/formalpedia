-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevB
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZLevB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:10.858249+00:00
-- url     : https://prove2.me/theorems/24af4193-61ec-483b-b706-b11b69616d5d
-- title:
--   NZLev B
-- statement:
--   Definitions and structural lemmas for NZLev B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevB.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Definitions.Def_Lemmata_GeneralBFactRightBisForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.BasicNotions.Examples₂.NZ
open Formalism.GradedWeylDivisibility
section HW
variable (R : Type) [CommRing R] {r n : ℕ}
def hwScal (hn : n ≤ r) (ν : Fin n → ℕ) (h : Matrix (Fin r) (Fin r) R) : R :=
  ∏ s : Fin n, (∏ a : Fin (s.val + 1), h (Fin.castLE (by omega) a) (Fin.castLE (by omega) a)) ^ (ν s - nuNext ν s)
end HW
section ML
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {A : Type*} [CommRing A] [Algebra R A]
end ML
end Formalism.BasicNotions.Examples₂.NZ


