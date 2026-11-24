-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:23.478659+00:00
-- url     : https://prove2.me/theorems/b4e31395-7d22-4ddc-9538-2afb129f209a
-- title:
--   PTrans Of
-- statement:
--   Definitions and structural lemmas for PTrans Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean

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
namespace TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
def rl (e : P ≃ Q) : TV n M P ≃ₗ[ℂ] TV n M Q :=
  LinearEquiv.funCongrLeft ℂ M (e.symm.arrowCongr (Equiv.refl (Fin n)))
def cI {C : Type} [DecidableEq C] (col : P → C) (p : P) : ℕ :=
  (Fintype.equivFin (Set.range col) ⟨col p, p, rfl⟩ : ℕ)
end TrOf
end PositivityTheory.Rg.Cz
end


