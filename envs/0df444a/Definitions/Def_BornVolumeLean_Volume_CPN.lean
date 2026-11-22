-- Prove2me | Definitions.Def_BornVolumeLean_Volume_CPN
-- name    : BornVolumeLean_Volume_CPN
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:57:29.413472+00:00
-- url     : https://prove2.me/theorems/1f26d5a2-dd74-4b3c-9264-e0eb0949d30a
-- title:
--   CPN
-- statement:
--   Definitions and structural lemmas for CPN, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CPN.lean

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudyUnique
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
namespace BornVolume
variable {N : ℕ} [NeZero N]
abbrev CPN (N : ℕ) := ℙ ℂ (EuclideanSpace ℂ (Fin N))
instance instNonemptyCPN : Nonempty (CPN N) := by
  have : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  have : Nontrivial (EuclideanSpace ℂ (Fin N)) := inferInstance
  infer_instance
end BornVolume


