-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePPTFBSt
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePPTFBSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:56:30.397551+00:00
-- url     : https://prove2.me/theorems/1619e812-d3b5-42e0-aa6b-9bd0267411ee
-- title:
--   Row Tie PPTFBSt
-- statement:
--   Definitions and structural lemmas for Row Tie PPTFBSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePPTFBSt.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartTop
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
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
def PTExFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, ∀ c, x 0 (Sum.inl c) = w c
def PTAvgFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (x : ℕ → I g ⊕ JJ I g → C), x ∈ X.TySet V g →
    (∀ n, X.tyC g n ≠ a → x 0 n = 0) →
    ∃ x' ∈ X.TySet V g, x' 0 = x 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x' i n = 0
end Formalism.L2.FormalSeriesBounds


