-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallQuot
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallQuot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:38.462824+00:00
-- url     : https://prove2.me/theorems/b0727e0c-5732-4731-abda-2c47483f7d52
-- title:
--   PWall Quot
-- statement:
--   Definitions and structural lemmas for PWall Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallQuot.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
namespace PositivityTheory.Rg.Cz
namespace WQ
section Alg
variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
end Alg
section Quot
variable {M : Type} [AddCommGroup M] [Module ℂ M]
def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {X | ∀ y ∈ N, X y ∈ N}
  mul_mem' hX hY y hy := hX _ (hY y hy)
  add_mem' hX hY y hy := N.add_mem (hX y hy) (hY y hy)
  algebraMap_mem' c y hy := by simpa [Module.algebraMap_end_apply] using N.smul_mem c hy
def qmap (N : Submodule ℂ M) : stab N →ₐ[ℂ] Module.End ℂ (M ⧸ N) where
  toFun X := N.mapQ N X.1 (fun y hy => X.2 y hy)
  map_one' := by ext y; simp
  map_mul' X Y := by ext y; simp
  map_zero' := by ext y; simp
  map_add' X Y := by ext y; simp
  commutes' c := by ext y; simp [Module.algebraMap_end_apply]
end Quot
end WQ
open WQ
end PositivityTheory.Rg.Cz
end


