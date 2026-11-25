-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:11.730026+00:00
-- url     : https://prove2.me/theorems/1595a298-fd80-4bd3-a165-ff1fc8a51c6f
-- title:
--   Row Tie Cart FB
-- statement:
--   Definitions and structural lemmas for Row Tie Cart FB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
section Rename
variable {dd : ℕ}
end Rename
def PTFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0
def AddCvFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => X.AddCvSt V
def HStabFBSt : Prop :=
  AllFB fun _ _ V _ I _ _ X => ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))
section Inst
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)
end Inst
end Formalism.L2.FormalSeriesBounds


