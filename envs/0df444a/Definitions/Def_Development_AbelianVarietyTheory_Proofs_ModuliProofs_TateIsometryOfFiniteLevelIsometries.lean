-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsometryOfFiniteLevelIsometries
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsometryOfFiniteLevelIsometries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:39.250844+00:00
-- url     : https://prove2.me/theorems/40af5838-5017-4fc0-a530-f9f71de0aff1
-- title:
--   Tate Isometry Of Finite Level Isometries
-- statement:
--   Definitions and structural lemmas for Tate Isometry Of Finite Level Isometries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TateIsometryOfFiniteLevelIsometries.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.TateTower
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def LevelIso (D : Datum H) {K : Type} [Field K] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → Kˣ → Prop) (N : ℕ) (p : Kˣ × (D.La → Q)) : Prop :=
  IsPrimitiveRoot p.1 N ∧ (∀ a c, p.2 (a + c) = p.2 a * p.2 c) ∧ (∀ (c : 𝓞 E) a, p.2 (c • a) = act c (p.2 a)) ∧
    (∀ a, p.2 a = 1 ↔ ∃ c, a = N • c) ∧ (∀ x, x ^ N = 1 ↔ ∃ a, p.2 a = x) ∧
    ∀ a c, e N (p.2 a) (p.2 c) (p.1 ^ D.EF a c)
variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}
end GlobalTheory.TateTower


