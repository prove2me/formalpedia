-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CubicWedgeNormPeriods
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_CubicWedgeNormPeriods
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:12.955573+00:00
-- url     : https://prove2.me/theorems/a42871f2-5bea-4941-998e-6a9e63cb794c
-- title:
--   Cubic Wedge Norm Periods
-- statement:
--   Definitions and structural lemmas for Cubic Wedge Norm Periods, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CubicWedgeNormPeriods.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PolarizationCorrespondence
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
open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence
open scoped Real
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicWedgeNormPeriods
abbrev Rule : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyInput K → Kˣ
def IsMultiple {R : Type} [CommRing R] (A : Over (Sp R)) {L : LB A.left} (c : R) (s s' : LB.Sec L) : Prop :=
  ∀ i, s'.f i =
    (A.hom.appLE ⊤ (L.U i) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * s.f i
def reframe {R : Type} [CommRing R] (x : KeyInput R) (th : LB.Sec x.P.L) (hth : NonzeroOnFibres x.P.A th)
    (b : Fin x.P.g → Tan x.P.A) (hb : IsLieBasis b) : KeyInput R :=
  { x with th := th, th_ne := hth, b := b, b_basis := hb }
example {R : Type} [CommRing R] (x : KeyInput R) : reframe x x.th x.th_ne x.b x.b_basis = x := rfl
example {R : Type} [CommRing R] (A : Over (Sp R)) {L : LB A.left} (s : LB.Sec L) : IsMultiple A 1 s s := by
  intro i
  simp
def Homogeneous (ka : Rule) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (x : KeyInput K)
    (th : LB.Sec x.P.L) (hth : NonzeroOnFibres x.P.A th) (b : Fin x.P.g → Tan x.P.A) (hb : IsLieBasis b)
    (c : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K),
    IsMultiple x.P.A c x.th th → (∀ i, b i = linComb (M i) x.b) →
    (ka K (reframe x th hth b hb) : K) * c ^ 8 = (ka K x : K) * M.det ^ 4
def Functorial (ka : Rule) : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K')
    (x : KeyInput K) (x' : KeyInput K'), IsBaseChange f x x' → (ka K' x' : K') = f (ka K x : K)
def Integral (ka : Rule) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (y : KeyInput R) (x : KeyInput K),
    IsBaseChange (algebraMap R K) y x →
    ∃ u : Rˣ, algebraMap R K (u : R) = (ka K x : K) ∧
      ∀ (k : Type) [Field k] [CharZero k] (f : R →+* k), IsLocalHom f →
        ∀ x₀ : KeyInput k, IsBaseChange f y x₀ → (ka k x₀ : k) = f (u : R)
def IsImage {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g) (w : Fin g → ℂ) (v : Tan A) : Prop :=
  ∃ v' : EpsPt A, v'.mor = v.1.left ∧ E.IsDiff w v'
def HasPeriods {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g) (τ : Siegel g) : Prop :=
  ∀ z : Fin g → ℂ, z ∈ E.lat ↔
    ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.1.mulVec (fun i => (n i : ℂ))
def IsHalfIntegral {g : ℕ} (a : Fin g → ℝ) : Prop := ∀ i, ∃ n : ℤ, 2 * a i = n
def ThetaValue (ka : Rule) : Prop :=
  ∀ (x : KeyInput ℂ) (F : Unif x.P.A x.P.L x.P.g) (τ : Siegel x.P.g) (a b : Fin x.P.g → ℝ)
    (w : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
    HasPeriods F.toExp τ → IsHalfIntegral a → IsHalfIntegral b →
    F.IsRig x.rig → F.IsSec x.th (fun z => theta a b z τ) →
    (∀ i, IsImage F.toExp (w i) (x.b i)) → (2 * π * Complex.I) ^ x.P.g * w.det = 1 →
    ka ℂ x = 1
def cubNorm_sq {g : ℕ} {La : Submodule ℤ (Fin g → ℂ)} (D : AHDatum La) (θ : (Fin g → ℂ) → ℂ)
    (z : Fin g → ℂ) : ℝ :=
  ‖θ z‖ ^ 2 * Real.exp (-(π * (D.H z z).re))
def wedgeNorm_sq {g : ℕ} {La : Submodule ℤ (Fin g → ℂ)} (D : AHDatum La) (w : Fin g → Fin g → ℂ) : ℝ :=
  (Matrix.of fun i j => (π : ℂ) * D.H (w i) (w j)).det.re
example {La : Submodule ℤ (Fin 1 → ℂ)} (D : AHDatum La) (w : Fin 1 → Fin 1 → ℂ) :
    wedgeNorm_sq D w = π * (D.H (w 0) (w 0)).re := by
  simp [wedgeNorm_sq]
def NormIdentity (ka : Rule) : Prop :=
  ∀ (x : KeyInput ℂ) (F : Unif x.P.A x.P.L x.P.g) (D : AHDatum F.toExp.lat) (θ : (Fin x.P.g → ℂ) → ℂ)
    (w : Fin x.P.g → Fin x.P.g → ℂ) (μ : Measure (Fin x.P.g → ℂ)) [μ.IsAddHaarMeasure]
    (𝓕 : Set (Fin x.P.g → ℂ)),
    F.IsAH D → F.IsRig x.rig → F.IsSec x.th θ → (∀ i, IsImage F.toExp (w i) (x.b i)) →
    IsAddFundamentalDomain F.toExp.lat 𝓕 μ → μ 𝓕 = 1 →
    ‖(ka ℂ x : ℂ)‖ * (∫ z in 𝓕, cubNorm_sq D θ z ∂μ) ^ 4 = (2 * π) ^ (2 * x.P.g) * wedgeNorm_sq D w ^ 2
def IsKeyRule (ka : Rule) : Prop :=
  Homogeneous ka ∧ Functorial ka ∧ Integral ka ∧ ThetaValue ka ∧ NormIdentity ka
def KeyFormula : Prop := ∃ ka : Rule, IsKeyRule ka
end GlobalTheory.IndefiniteRowSideFullHecke.CubicWedgeNormPeriods


