-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoefficientIdentitySelfConjugate
-- name    : Formalism_LocalToGlobal_CharacterGerms_CoefficientIdentitySelfConjugate
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:21:10.85981+00:00
-- url     : https://prove2.me/theorems/55f3e396-59c2-4104-b4f4-6d7bb41de9d9
-- title:
--   Coefficient Identity Self Conjugate
-- statement:
--   Definitions and structural lemmas for Coefficient Identity Self Conjugate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoefficientIdentitySelfConjugate.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
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
namespace IndependenceBoundPlain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
  [Fintype κ] (X : RawChart C d I κ)
def PlainCoefficientIdentity (H : ∀ g, X.CartHyp V g) : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∃ M : JJ I g → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ c1 : JJ I g → C, (∀ q, X.ty (1 - g) q ≠ a + 2 → c1 q = 0) ∧
        ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', c1 q' * M q' q)
end IndependenceBoundPlain
section Closed
def CoefficientIdentitySelfConjugate : Prop :=
  AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, IndependenceBoundPlain.PlainCoefficientIdentity X H
end Closed
end Formalism.L2.FormalSeriesBounds


