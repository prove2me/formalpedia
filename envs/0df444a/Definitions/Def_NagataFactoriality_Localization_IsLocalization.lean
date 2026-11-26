-- Prove2me | Definitions.Def_NagataFactoriality_Localization_IsLocalization
-- name    : NagataFactoriality_Localization_IsLocalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:47:39.893919+00:00
-- url     : https://prove2.me/theorems/b1edc1f3-5a4f-4e2e-9380-ad4c80ed8438
-- title:
--   Is Localization
-- statement:
--   Definitions and structural lemmas for Is Localization, from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz (Arthur742Ramos/NagataFactoriality; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Prime-generated Nagata factoriality theorem for Noetherian integral domains development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
set_option autoImplicit false
namespace NagataFactoriality
namespace IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
section Nonzero
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
end Nonzero
end IsLocalization
end NagataFactoriality


