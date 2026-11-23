-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:14.618547+00:00
-- url     : https://prove2.me/theorems/29149afb-2703-4682-a478-0845d0878dc3
-- title:
--   Covering And Smoothness
-- statement:
--   Definitions and structural lemmas for Covering And Smoothness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAndSmoothness.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
section One
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def IsUnifBase (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) : Prop :=
  CharZero R ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
    (ξ ⁻¹' abLocus Y.t.G).Nonempty ∧
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ) (S : SplitExt (Sp (IsLocalRing.ResidueField R))),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)
def CovAt (Y : Model Xo c β) (p : ℕ) (x : Y.X) : Prop :=
  ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDomain (R i)) (_ : ∀ i, IsLocalRing (R i))
    (ξ : ∀ i, Sp (R i) ⟶ Y.X),
    (∀ i, IsUnifBase Y (R i) (ξ i) ∧ ξ i (IsLocalRing.closedPoint (R i)) = x) ∧
    ∀ (C V : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [CommRing V] [IsLocalRing V] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 →
      ∀ y : Sp V ⟶ Y.X, y (IsLocalRing.closedPoint V) = x →
        Set.range (spMap (algebraMap V C) ≫ y) ⊆ abLocus Y.t.G →
        ∃ (i : Fin n) (φ : R i →+* V), IsLocalHom φ ∧ spMap φ ≫ ξ i = y
def AbLocusSmooth (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s)
end One
def GoodPrime (l : Level H) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) ∧ ¬ p ∣ l.M'
def CoveringLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ (i : Idx H p) (x : (Y i).X), CovAt (Y i) p x
def SmoothnessLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, GoodPrime i.l p → AbLocusSmooth (Y i)
def CoveringAndSmoothness : Prop := CoveringLemma ∧ SmoothnessLemma
end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase


