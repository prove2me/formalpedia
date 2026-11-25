-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FieldFixesCurve
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FieldFixesCurve
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:37.677698+00:00
-- url     : https://prove2.me/theorems/de9308e3-679a-40a5-805d-e0e98c3ead8c
-- title:
--   Field Fixes Curve
-- statement:
--   Definitions and structural lemmas for Field Fixes Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/FieldFixesCurve.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Statements_PrincipalLattices_FiniteDimensionalBase
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.FieldFixesCMCurve
def conjPt (τ : ℂ ≃+* ℂ) {X : Scheme.{0}} (y : Sp ℂ ⟶ X) : Sp ℂ ⟶ X := spMap τ.toRingHom ≫ y
def IsConjIdent (τ : ℂ ≃+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (n : ℕ) (φ : A.left ⟶ A.left) : Prop :=
  IsGrpPullback A A (spMap τ.toRingHom) φ ∧
    ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ^ n = 1 → x.left ≫ φ = conjPt τ x.left
def IsEndLinear (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ A.left) : Prop :=
  ∀ f : A ⟶ A, IsMonHom f → f.left ≫ φ = φ ≫ f.left
def IsCMCurve (d : ℕ) (P : Out.PolAV (Sp ℂ)) : Prop :=
  P.g = 1 ∧ ∃ u : HolUnif P.A P.L P.g, PureType.IsQuadLattice u.Λ d 1
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def FixesCurve (H : Host E) (n : ℕ) (τ : ℂ ≃+* ℂ) : Prop :=
  ∃ P : Out.PolAV (Sp ℂ), IsCMCurve H.d P ∧ ∃ φ, IsConjIdent τ P.A n φ ∧ IsEndLinear P.A φ
def FixesCurvePlain (H : Host E) (n : ℕ) (τ : ℂ ≃+* ℂ) : Prop :=
  ∃ P : Out.PolAV (Sp ℂ), IsCMCurve H.d P ∧ ∃ φ, IsConjIdent τ P.A n φ
def FieldFixesCurve (H : Host E) (n : ℕ) (F : IntermediateField ℚ ℂ) : Prop :=
  ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F, τ x = x) → FixesCurve H n τ
variable {H : Host E}
def IsSplitting (D : Datum H) (L₁ L₂ : Submodule (𝓞 E) D.La) : Prop :=
  IsCompl L₁ L₂ ∧ Module.finrank (𝓞 E) L₁ = D.p ∧ Module.finrank (𝓞 E) L₂ = D.q ∧
    (∀ x ∈ L₁, ∀ y ∈ L₂, D.EF x y = 0) ∧
    (∀ x ∈ L₁, x ≠ 0 → 0 < H.rt0.im * (D.EF (H.rt • x) x : ℝ)) ∧
    ∀ y ∈ L₂, y ≠ 0 → H.rt0.im * (D.EF (H.rt • y) y : ℝ) < 0
def IsSplit (D : Datum H) : Prop := ∃ L₁ L₂, IsSplitting D L₁ L₂
def periodPts {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) : Set (Sp ℂ ⟶ Xo.X) :=
  {y | ∃ P, IsPeriod (FU.Di i) ty P ∧ FU.u i P = y}
def ActsOnPeriodSpaces {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (τ : ℂ ≃+* ℂ) (π : Fin FU.n → Fin FU.n) : Prop :=
  ∀ i, Set.MapsTo (conjPt τ) (periodPts FU i) (periodPts FU (π i))
end GlobalTheory.IndefiniteRowSideFullHecke.FieldFixesCMCurve


