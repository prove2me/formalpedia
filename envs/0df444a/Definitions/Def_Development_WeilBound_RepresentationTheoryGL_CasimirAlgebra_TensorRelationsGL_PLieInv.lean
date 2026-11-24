-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:04.071908+00:00
-- url     : https://prove2.me/theorems/7450962e-3e41-45f5-9919-46d3a1af5a09
-- title:
--   PLie Inv
-- statement:
--   Definitions and structural lemmas for PLie Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PLieInv.lean

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
namespace LieInverse
def Sop {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ M :=
  ∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)
end LieInverse
end PositivityTheory.Rg.Cz
end


