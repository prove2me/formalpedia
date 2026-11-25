-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:14:07.455479+00:00
-- url     : https://prove2.me/theorems/372e5f2d-7016-491a-b564-375680e4690e
-- title:
--   Row Tie PSplit Def
-- statement:
--   Definitions and structural lemmas for Row Tie PSplit Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitDef.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.FormalSeriesBounds
namespace RowTiePSplit
open Polynomial
def SplitSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : O →+* Matrix (Fin n) (Fin n) C) (P : Matrix (Fin n) (Fin n) C) (em : ι → (O →+* C)),
    P * P = P → (∀ x, P * M x = M x * P) → Function.Injective em →
    (∀ x, Polynomial.aeval (M x) (∏ c, (X - Polynomial.C (em c x))) * P = 0) →
    ∀ v : Fin n → C, ∃ w : ι → (Fin n → C), Matrix.mulVec P v = ∑ c, w c ∧ ∀ c x, Matrix.mulVec (M x) (w c) = em c x • w c
end RowTiePSplit
end Formalism.L2.FormalSeriesBounds


