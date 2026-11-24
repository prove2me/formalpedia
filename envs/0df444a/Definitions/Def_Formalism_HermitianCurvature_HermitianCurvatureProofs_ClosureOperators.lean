-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:31:51.037693+00:00
-- url     : https://prove2.me/theorems/c97abb0f-a6aa-4e46-96c1-4f85572e3d01
-- title:
--   Closure Operators
-- statement:
--   Definitions and structural lemmas for Closure Operators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def Cl {N : ℕ} (E : Fin N → Fin N → Module.End ℂ V) (L : Fin N → Fin N → Prop) (M : Submodule ℂ V) :
    Submodule ℂ V :=
  sInf {P | M ≤ P ∧ ∀ a b, L a b → ∀ q ∈ P, E a b q ∈ P}
def MS {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun a : Fin n → ℕ => mono f a v)
end Formalism.FourierDecayAlt.P.ClosureOperators
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr ClosureOperators
end Formalism.FourierDecayAlt.P


