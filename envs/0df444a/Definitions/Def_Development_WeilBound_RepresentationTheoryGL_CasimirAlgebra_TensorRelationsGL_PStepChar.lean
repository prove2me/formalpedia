-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:26.957868+00:00
-- url     : https://prove2.me/theorems/2f1e41e6-97d9-4680-80e4-a58a3203f79e
-- title:
--   PStep Char
-- statement:
--   Definitions and structural lemmas for PStep Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepChar.lean

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
open Formalism.REAL Polynomial
namespace PositivityTheory.Rg.Cz
namespace CharacterRelations
section poly
variable {A : Type*} [Ring A] [Algebra ℂ A]
set_option linter.unusedSectionVars false
end poly
section rel
variable {V N : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup N] [Module ℂ N]
  (W : Submodule ℂ V) (q : W →ₗ[ℂ] N)
def Rel (X : Module.End ℂ V) (Y : Module.End ℂ N) : Prop := ∀ w : W, ∃ h : X w ∈ W, q ⟨X w, h⟩ = Y (q w)
variable {W q}
variable {n : ℕ}
end rel
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
end CharacterRelations
end PositivityTheory.Rg.Cz
end


