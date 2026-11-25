-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
-- name    : Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:28.601329+00:00
-- url     : https://prove2.me/theorems/6a3dc081-6356-4c81-a81e-ce33cde9178b
-- title:
--   Is WHLetter Minor K
-- statement:
--   Definitions and structural lemmas for Is WHLetter Minor K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IsWHLetterMinorK.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
namespace WeightHomogeneousLetters
open WeightHomogeneousMinors
section WH
variable {R : Type} [CommRing R]
end WH
section Block
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X) (idx : ∀ g, I g → ℕ) (std : ∀ g t (c : Fin (X.rkF g t)), idx g (F.en g t c) = c.val)
def wRowG {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (x : Fin N × WV I) : ℕ :=
  if x.2.1 = g0 ∧ (X.G x.2.1).ty (Sum.inl x.2.2) = t0 ∧ idx x.2.1 x.2.2 = c0 then 1 else 0
end Block
end WeightHomogeneousLetters
end Formalism.L2.FormalSeriesBounds.RF


