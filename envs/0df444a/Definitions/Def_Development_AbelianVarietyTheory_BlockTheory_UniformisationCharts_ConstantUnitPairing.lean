-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_ConstantUnitPairing
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_ConstantUnitPairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:44.11135+00:00
-- url     : https://prove2.me/theorems/4439bc2c-4cac-4599-a1c1-7ac8de36fb9c
-- title:
--   Constant Unit Pairing
-- statement:
--   Definitions and structural lemmas for Constant Unit Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/ConstantUnitPairing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
def constUnit (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (ζ : Fˣ) : Γ((TFK (R := R) F).left, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ
def MapCarriesPairing : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I →
    ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
      (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
      (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
      ∀ (p p' : QkPt D.toPre F k) (x x' : TFK (R := R) F ⟶ A.A),
        QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' →
        ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' (ζ : F) ↔
          WeilIs A.A A.L (k : ℤ) x x' (constUnit R F ζ)
end GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing


