-- Prove2me | Definitions.Def_DeletionCode_BubbleContextGeometry
-- name    : DeletionCode_BubbleContextGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:24:45.902616+00:00
-- url     : https://prove2.me/theorems/b63105b2-dafe-4130-bf60-8f84ae41dbec
-- title:
--   Bubble Context Geometry
-- statement:
--   Definitions and structural lemmas for Bubble Context Geometry, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
set_option autoImplicit true
namespace DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization
structure Geometry {k : ℕ} (bubble : BubbleWord k) : Prop where
  long_simple : Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
    SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val)
  short_simple : Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
    SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val)
  endpoints : ∀ a b, a ≤ windowLength k - bubble.rho + 1 →
    b ≤ windowLength k - bubble.rho →
    Agree (listLetters bubble.longWord) a (listLetters bubble.shortWord) b
      (windowLength k - 1) →
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho)
end DeletionCode.BubbleContextGeometry


