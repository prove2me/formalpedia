-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
-- name    : Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:40.936265+00:00
-- url     : https://prove2.me/theorems/9fba7045-a28b-40ae-bb91-ccd55de4f217
-- title:
--   Independence Bound Raw
-- statement:
--   Definitions and structural lemmas for Independence Bound Raw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
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
namespace ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
end ValuationNonnegativity
section Closed
variable {C : Type} [Field C]
def CoefficientIdentityCondition : Prop :=
  AllFB fun C _ V _ I _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, X.AltC → ∀ g a, X.big g a →
    ∃ M : JJ I g → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ c1 : JJ I g → C, (∀ q, X.ty (1 - g) q ≠ a + 2 → c1 q = 0) ∧
        ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', c1 q' * M q' q)
def IndependenceSpanCondition : Prop :=
  AllFB fun C _ V _ I _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, X.AltC → ∀ g a, X.big g a →
    ∃ e : Fin X.j' → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ b : Fin X.j' → C, ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ r, b r * e r q)
end Closed
end Formalism.L2.FormalSeriesBounds


