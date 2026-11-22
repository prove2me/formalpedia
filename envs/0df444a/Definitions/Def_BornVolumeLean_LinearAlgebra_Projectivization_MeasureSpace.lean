-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
-- name    : BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:49.399852+00:00
-- url     : https://prove2.me/theorems/e715affa-4d5b-4faf-aea1-79b8863d6137
-- title:
--   Measure Space
-- statement:
--   Definitions and structural lemmas for Measure Space, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MeasureSpace.lean

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Topology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Topology
open scoped LinearAlgebra.Projectivization
namespace Projectivization
variable {K V : Type*}
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
instance instSecondCountableTopology : SecondCountableTopology (ℙ K V) := by
  have : ProperSpace V := FiniteDimensional.proper_rclike K V
  exact isQuotientMap_mk'.secondCountableTopology isOpenMap_mk'
instance instMeasurableSpace : MeasurableSpace (ℙ K V) := borel _
instance instBorelSpace : BorelSpace (ℙ K V) := ⟨rfl⟩
end Projectivization


