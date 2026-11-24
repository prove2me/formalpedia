-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:36.168259+00:00
-- url     : https://prove2.me/theorems/e9afa233-742a-462e-bd91-c6d4ae4663ec
-- title:
--   PPi Qdet
-- statement:
--   Definitions and structural lemmas for PPi Qdet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean

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
namespace QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
def sg (σ : Equiv.Perm (Fin n)) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)
def IsAnti (g : TV n M (Fin n)) : Prop := ∀ σ : Equiv.Perm (Fin n), pm σ g = sg σ • g
def X (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) : Module.End ℂ (TV n M (Fin n)) :=
  algebraMap ℂ _ u + xJ E j
def T (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) : Module.End ℂ (TV n M (Fin n)) :=
  algebraMap ℂ _ (u - (j : ℂ)) + Om E j
def ev (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) : List (Fin n) → (Fin n → Fin n) → TV n M (Fin n) → M
  | [], I, h => h I
  | k :: l, I, h => ∑ a, Tm E (u - (k : ℂ)) a (I k) (ev E u l (Function.update I k a) h)
end QuantumDeterminantProducts
end PositivityTheory.Rg.Cz
end


