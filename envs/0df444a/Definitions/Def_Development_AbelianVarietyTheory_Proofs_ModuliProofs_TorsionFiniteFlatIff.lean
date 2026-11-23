-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionFiniteFlatIff
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionFiniteFlatIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:11.535023+00:00
-- url     : https://prove2.me/theorems/d9309928-2cab-4f50-9d60-8e82a88ba1ce
-- title:
--   Torsion Finite Flat Iff
-- statement:
--   Definitions and structural lemmas for Torsion Finite Flat Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionFiniteFlatIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
namespace GlobalTheory.TorsionRepresent
section
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ)
noncomputable def incl : GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k ⟶ G :=
  pullback.fst ((𝟙 G : G ⟶ G) ^ k) η[G]
instance : Mono (incl G k) := by
  have : Mono η[G] := ⟨fun _ _ _ => toUnit_unique _ _⟩
  exact pullback.fst_of_mono
end
end GlobalTheory.TorsionRepresent


