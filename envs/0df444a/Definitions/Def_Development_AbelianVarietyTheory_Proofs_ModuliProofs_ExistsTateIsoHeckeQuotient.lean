-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoHeckeQuotient
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoHeckeQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:45.693074+00:00
-- url     : https://prove2.me/theorems/e97307fd-b768-4346-8eae-7713712d19e1
-- title:
--   Exists Tate Iso Hecke Quotient
-- statement:
--   Definitions and structural lemmas for Exists Tate Iso Hecke Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsTateIsoHeckeQuotient.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.HeckeTate
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
def form (D : Datum H) : D.La →+ D.La →+ ℤ :=
  AddMonoidHom.mk' (fun x => (D.EF x).toAddMonoidHom) fun a b => by rw [map_add]; rfl
variable {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
def evHom (I : TateIso D k Q act e) (n : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev n a)) fun a b => by rw [I.add]; rfl
end
end GlobalTheory.HeckeTate
namespace GlobalTheory
open HeckeTate
end GlobalTheory


