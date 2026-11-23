-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:37.596275+00:00
-- url     : https://prove2.me/theorems/336de581-ceef-4afe-9543-1f8b6be36725
-- title:
--   Qdet Top Three Orders
-- statement:
--   Definitions and structural lemmas for Qdet Top Three Orders, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}
def oprod (S : Finset (Fin n)) (e : Fin n → A) : A :=
  (List.ofFn fun k => if k ∈ S then e k else 1).prod
def subdet (E : Fin n → Fin n → A) (S : Finset (Fin n)) : A :=
  ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ S → σ k = k),
    ((Equiv.Perm.sign σ : ℤ) : A) * oprod S (fun k => E (σ k) k)
end GlobalTheory.CapelliTop
namespace GlobalTheory
open CapelliTop
end GlobalTheory


