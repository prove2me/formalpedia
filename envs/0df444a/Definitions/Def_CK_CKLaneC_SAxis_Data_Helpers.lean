-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Helpers
-- name    : CK_CKLaneC_SAxis_Data_Helpers
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:58:25.104271+00:00
-- url     : https://prove2.me/theorems/f85011b3-a4c8-461f-8423-ad375c296d47
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Helpers` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Helpers` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Helpers` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Helpers (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Helpers.lean)

import Definitions.Def_CK_CKLaneC_S3_SlopeChain

-- ===== source module CKLaneC.SAxis.Data.Helpers =====
section

set_option autoImplicit false

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain

namespace CKLaneC.SAxis.Data

theorem forall_mem_cons_of {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a)
    (hl : ∀ x ∈ l, P x) : ∀ x ∈ a :: l, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h
  · exact ha
  · exact hl x h

theorem forall_mem_nil_of {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by
  intro x hx
  simp at hx

theorem forall_mem_append_of {α : Type} {P : α → Prop} {A B : List α} (hA : ∀ x ∈ A, P x)
    (hB : ∀ x ∈ B, P x) : ∀ x ∈ A ++ B, P x := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hA x h
  · exact hB x h

theorem tableValid_nil : TableValid [] := by
  intro c hc
  simp at hc

theorem tableValid_cons {c : List Piece} {T : List (List Piece)}
    (hc : ∀ p ∈ c, p.check = true) (hT : TableValid T) : TableValid (c :: T) := by
  intro c' hc' p hp
  rcases List.mem_cons.mp hc' with rfl | h
  · exact hc p hp
  · exact hT c' h p hp

end CKLaneC.SAxis.Data

end


