-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
-- name    : Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:53.182873+00:00
-- url     : https://prove2.me/theorems/f5c6219f-e69a-481b-a0eb-2db9482e26da
-- title:
--   Fin Two Ne One Sub
-- statement:
--   Definitions and structural lemmas for Fin Two Ne One Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
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
open Formalism.IncomingBounds Formalism.L2.Pj
section One
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
variable (X : RowData C V d I J) (F : Flag X)
end One
section Fam
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}
end Fam
end Formalism.L2.FormalSeriesBounds.RF


