-- Prove2me | Definitions.Def_DeletionCode_SpectrumPrefixChange
-- name    : DeletionCode_SpectrumPrefixChange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:25:55.348714+00:00
-- url     : https://prove2.me/theorems/6ad86789-74a4-4610-be56-81d6e6d57a8e
-- title:
--   Spectrum Prefix Change
-- statement:
--   Definitions and structural lemmas for Spectrum Prefix Change, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean

import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
namespace DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization
noncomputable def spectrum (word : List Bool) (L : ℕ) : Gram L → ℤ :=
  wordSpectrum (listLetters word) word.length L
end DeletionCode.SpectrumPrefixChange


