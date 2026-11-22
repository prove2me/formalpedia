-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
-- name    : Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:17.092797+00:00
-- url     : https://prove2.me/theorems/2be5ba59-c940-42cd-b6cf-e87fb1568f9c
-- title:
--   Finrank Int Self
-- statement:
--   Definitions and structural lemmas for Finrank Int Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
namespace IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
def eAlg {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) :
    MonoidAlgebra K G :=
  ∑ x : G, MonoidAlgebra.single x (charOf τ 1 / (Fintype.card G : K) * charOf τ x⁻¹)
end IdempotentLemmas
open IdempotentLemmas
end Formalism.IndefR.LatticeTransfer


