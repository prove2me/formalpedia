-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:00.87903+00:00
-- url     : https://prove2.me/theorems/e0f4e102-50c0-464b-9c57-1508d5829e7e
-- title:
--   PCol Anti
-- statement:
--   Definitions and structural lemmas for PCol Anti, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
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
namespace ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}
def Q (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (σ : Equiv.Perm (Fin m)) : Prop :=
  L ∘ₗ pm σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) • L
end ColumnAntisymmetry
end PositivityTheory.Rg.Cz
end


