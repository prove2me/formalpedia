-- Prove2me | Definitions.Def_DeletionCode_SpectrumLocalization
-- name    : DeletionCode_SpectrumLocalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:22:23.914042+00:00
-- url     : https://prove2.me/theorems/9ce9be36-ed66-4236-8765-3259e59991ad
-- title:
--   Spectrum Localization
-- statement:
--   Definitions and structural lemmas for Spectrum Localization, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit true
namespace DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
noncomputable def windowSum (x : Letters) (L start count : ℕ) (g : Gram L) : ℤ := by
  classical
  exact ∑ i ∈ Finset.range count, if gram x L (start + i) = g then 1 else 0
end DeletionCode.SpectrumLocalization


