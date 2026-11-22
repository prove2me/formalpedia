-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:02.898067+00:00
-- url     : https://prove2.me/theorems/dd9ab99f-5e15-43f3-a948-f5bc33903382
-- title:
--   Finrank Le Of Map Le
-- statement:
--   Definitions and structural lemmas for Finrank Le Of Map Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
section Lattices
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
noncomputable def eig (A : FI E) (s : ℕ) : Submodule ℤ E :=
  zsub E A ⊓ LinearMap.ker (LinearMap.id - ((-1 : ℤ) ^ s) • conjZ E)
end Lattices
section Ranks
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
instance finite_zsub (A : FI E) : Module.Finite ℤ (zsub E A) :=
  inferInstanceAs (Module.Finite ℤ A)
theorem finite_of_le (N : Submodule ℤ E) (A : FI E) (h : N ≤ zsub E A) : Module.Finite ℤ N := by
  have : IsNoetherian ℤ (zsub E A) := inferInstance
  have := isNoetherian_of_le h
  infer_instance
instance finite_eig (A : FI E) (s : ℕ) : Module.Finite ℤ (eig E A s) :=
  finite_of_le E _ A inf_le_left
end Ranks
section Index
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
end Index
end Formalism.FourierDecayAlt.P.S6x3
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x3
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
end Formalism.FourierDecayAlt.P


