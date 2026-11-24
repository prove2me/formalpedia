-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:01.933257+00:00
-- url     : https://prove2.me/theorems/50f8dd13-e55a-40b9-9742-23b1973c0e1c
-- title:
--   PCol Anti B
-- statement:
--   Definitions and structural lemmas for PCol Anti B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAntiB.lean

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
namespace ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
def npairs {m : ℕ} (col : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin m × Fin m => x.1 < x.2 ∧ col x.1 = col x.2).card
def ColInj {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) : Prop :=
  ∀ p q, col p = col q → I p = I q → p = q
def rk {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) (p : Fin m) : ℕ :=
  (Finset.univ.filter fun q => col q = col p ∧ I p < I q).card
end ColumnAntisymmetry
end PositivityTheory.Rg.Cz
end


