-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoung
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoung
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:29.302992+00:00
-- url     : https://prove2.me/theorems/a81ab6d5-088e-4de2-964f-2aaf420ed0e1
-- title:
--   PYoung
-- statement:
--   Definitions and structural lemmas for PYoung, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoung.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
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
section Main
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [DecidableEq ι]
  {Q : Type} [Fintype Q] [DecidableEq Q] {N : ℕ} {C : Type} [DecidableEq C]
def inF (Q : Type) (N : ℕ) : Fin N → Q ⊕ (Fin N ⊕ Fin N) := fun k => .inr (.inl k)
def inS (Q : Type) (N : ℕ) : Fin N → Q ⊕ (Fin N ⊕ Fin N) := fun k => .inr (.inr k)
end Main
end YoungTableau
end PositivityTheory.Rg.Cz
end


