-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgFin
-- name    : Formalism_LocalToGlobal_Columns_GoodXgFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:29.347839+00:00
-- url     : https://prove2.me/theorems/57faa75b-7cef-4737-a147-2ed09f47cf26
-- title:
--   Good Xg Fin
-- statement:
--   Definitions and structural lemmas for Good Xg Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgFin.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.L2.Col
open Formalism.L2.DIV
section Fin
variable {G : Type} [Group G] [Fintype G]
def gxIrrSet (k : Type) [Field k] : Set (G → k) :=
  {ψ | ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧ ρ.character = ψ}
end Fin
end Formalism.L2.Col


