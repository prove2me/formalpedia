-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
-- name    : Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:48.605034+00:00
-- url     : https://prove2.me/theorems/7efb7415-c398-4b60-99a0-0f3bc92a09d8
-- title:
--   Cartesian Bound On Curves
-- statement:
--   Definitions and structural lemmas for Cartesian Bound On Curves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Cart
variable (X : Cart V d I J)
def remL (L : (I ⊕ J → C) → ℕ → I ⊕ J → C) (x : ℕ → I ⊕ J → C) : ℕ → (ℕ → I ⊕ J → C)
  | 0 => x
  | s + 1 => remL L x s - Vpow s (L (remL L x s s))
variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}
end Cart
namespace Sys
variable {X : Cart V d I J} (S : Sys X)
def U : Matrix I I C := Matrix.of S.tan
def co (h : I ⊕ J → C) (b : I) : C := ∑ k, h (Sum.inl k) * S.U⁻¹ k b
def lift (h : I ⊕ J → C) : ℕ → I ⊕ J → C :=
  (∑ b, teich V.l (S.co h b) (S.cur b)) + const0 (Sum.elim (0 : I → C) (fun j => h (Sum.inr j)))
end Sys
end Formalism.L2.FormalSeriesBounds


