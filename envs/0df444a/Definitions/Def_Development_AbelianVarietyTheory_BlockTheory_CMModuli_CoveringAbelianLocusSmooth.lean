-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:22.836214+00:00
-- url     : https://prove2.me/theorems/7f842be6-8a95-4025-89b9-6be32a93499a
-- title:
--   Covering Abelian Locus Smooth
-- statement:
--   Definitions and structural lemmas for Covering Abelian Locus Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAbelianLocusSmooth.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section OneModel
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def IsChartAt (Y : Model Xo c β) (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) :
    Prop :=
  CharZero R ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
    ξ (IsLocalRing.closedPoint R) = x ∧ (ξ ⁻¹' abLocus Y.t.G).Nonempty ∧
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ) (S : SplitExt (Sp (IsLocalRing.ResidueField R))),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)
def CoveredByCharts (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ x : Y.X, ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDomain (R i))
    (_ : ∀ i, IsLocalRing (R i)) (ξ : ∀ i, Sp (R i) ⟶ Y.X),
    (∀ i, IsChartAt Y x (R i) (ξ i)) ∧
    ∀ (V C : Type) [CommRing V] [IsLocalRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
      [IsAlgClosed C] [CharZero C] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 →
      ∀ y : Sp V ⟶ Y.X, y (IsLocalRing.closedPoint V) = x →
        Set.range (spMap (algebraMap V C) ≫ y) ⊆ abLocus Y.t.G →
        ∃ (i : Fin n) (f : R i →+* V), IsLocalHom f ∧ spMap f ≫ ξ i = y
def AbLocusSmooth (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s)
end OneModel
def GoodPrime (l : Level H) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) ∧ ¬ p ∣ l.M'
def CoveringLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, (Y i).SplitFibres → CoveredByCharts (Y i) p
def SmoothnessLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, GoodPrime i.l p → AbLocusSmooth (Y i)
def CoveringAndSmoothness : Prop := CoveringLemma ∧ SmoothnessLemma
end GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth


