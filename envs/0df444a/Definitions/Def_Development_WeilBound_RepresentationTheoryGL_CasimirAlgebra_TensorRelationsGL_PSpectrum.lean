-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:37.174999+00:00
-- url     : https://prove2.me/theorems/12b0c625-946f-48dc-8534-56c840231b53
-- title:
--   PSpectrum
-- statement:
--   Definitions and structural lemmas for PSpectrum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean

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
open Formalism.REAL
namespace PositivityTheory.Rg.Cz
namespace SpecA
variable {n : ℕ}
def Kl {V : Type} [AddCommGroup V] [Module ℂ V] (X : Module.End ℂ V) (s : ℂ) : Prop :=
  ∃ L : List ℕ, (L.map fun r : ℕ => X - algebraMap ℂ _ (s + r)).prod = 0
def Cl (k : ℕ) : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (l : Fin n → ℂ) (s : ℂ), HasChar E l → (∀ k, ∃ r : ℕ, l k = s + r) → ∀ j : Fin k, Kl (xJ E j) s
end SpecA
end PositivityTheory.Rg.Cz
end


