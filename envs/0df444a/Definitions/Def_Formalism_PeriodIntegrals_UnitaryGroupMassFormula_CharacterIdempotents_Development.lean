-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:52.789596+00:00
-- url     : https://prove2.me/theorems/5336b20b-eeff-4853-98b5-1f25874fd34a
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
namespace PI.CharIdemW
open PI.CharIdem
def Central : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V : FDRep ℂ G) (x : MonoidAlgebra ℂ G),
    charIdem V * x = x * charIdem V
def Scalar : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    (Nonempty (V ≅ W) → act W (charIdem V) = 1) ∧
    (IsEmpty (V ≅ W) → act W (charIdem V) = 0)
def MulEq : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    (Nonempty (V ≅ W) → charIdem V * charIdem W = charIdem W) ∧
    (IsEmpty (V ≅ W) → charIdem V * charIdem W = 0)
end PI.CharIdemW


