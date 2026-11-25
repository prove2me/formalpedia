-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsCharacterPairSer
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsCharacterPairSer
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T18:33:36.301227+00:00
-- url     : https://prove2.me/theorems/0f7dfab6-7278-5027-9530-8ea9e534544f
-- title:
--   Exists Character Pair Ser
-- statement:
--   Definitions and structural lemmas for Exists Character Pair Ser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsCharacterPairSer.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AbelianFunctorNilChartNsmulAndKilledByPPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesOfNaturalNilpotentPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSeriesEqOfEvalAtNilpotentPointsEqStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
section Local
variable {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
end Local
section Pair
variable {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {p : ℕ} {τ : ℕ → B.G O}
def PVal (p : ℕ) (τ : ℕ → B.G O) {R : LAlg R₀} (s : LHom O R) (x : B.G R) (z : (R : Type)ˣ) : Prop :=
  ∃ n, B.IsPairing (p ^ (n + 1)) x (B.map s (τ n)) z
def LocO (O : LAlg R₀) (S : Type) [CommRing S] [Algebra (O : Type) S] : Prop :=
  IsLocalRing S ∧ IsLocalHom (algebraMap (O : Type) S)
abbrev mkL (O : LAlg R₀) (S : Type) [CommRing S] [Algebra (O : Type) S] (h : LocO O S) : LAlg R₀ :=
  @LAlg.mk R₀ _ S _ ((algebraMap (O : Type) S).comp (algebraMap R₀ (O : Type))).toAlgebra h.1
def mkH (R R' : LAlg R₀) (f : (R : Type) →+* (R' : Type))
    (h : ∀ r, f (algebraMap R₀ (R : Type) r) = algebraMap R₀ (R' : Type) r) (hl : IsLocalHom f) : LHom R R' :=
  ⟨{ f with commutes' := h }, hl⟩
def mkS (O : LAlg R₀) (S : Type) [CommRing S] [Algebra (O : Type) S] (h : LocO O S) : LHom O (mkL O S h) :=
  mkH O (mkL O S h) (algebraMap (O : Type) S) (fun _ => rfl) h.2
end Pair
end GlobalTheory.ChF


