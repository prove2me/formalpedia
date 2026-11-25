-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:32:34.343742+00:00
-- url     : https://prove2.me/theorems/1c0b5495-120b-4d64-a2d9-803e0ac549de
-- title:
--   Covering And Smoothness Iff Of Separable Splitting
-- statement:
--   Definitions and structural lemmas for Covering And Smoothness Iff Of Separable Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoveringAndSmoothnessIffOfSeparableSplitting.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoveringCompare
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke
section Fibres
def SplitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (x : S) (k : Type) [Field k] [Algebra (S.residueField x) k] :
    Prop :=
  ∃ T : SplitExt (Sp k), T.IsGt ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x)).obj G)
def SeparableSplitting : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
      Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G))
end Fibres
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
section One
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
end One
def CoveringForSplitFibres : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, (Y i).SplitFibres → ∀ x : (Y i).X, UniformizationBase.CovAt (Y i) p x
end GlobalTheory.CoveringCompare


