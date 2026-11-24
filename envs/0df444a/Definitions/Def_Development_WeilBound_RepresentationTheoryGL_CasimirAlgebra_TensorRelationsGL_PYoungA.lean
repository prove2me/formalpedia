-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:46.863807+00:00
-- url     : https://prove2.me/theorems/29e80b62-46ec-4ac3-a4f8-72a5845b1bcf
-- title:
--   PYoung A
-- statement:
--   Definitions and structural lemmas for PYoung A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
namespace YoungTableau
section Gen
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]
def ColInj (col : X → C) (J : X → Fin n) : Prop := ∀ p q, col p = col q → J p = J q → p = q
def sg (col : X → C) (b : X → Fin n) (v : X → Fin n) : ℤ :=
  ∑ π ∈ colG col, if b ∘ π = v then (Equiv.Perm.sign π : ℤ) else 0
end Gen
end YoungTableau
end PositivityTheory.Rg.Cz
end


