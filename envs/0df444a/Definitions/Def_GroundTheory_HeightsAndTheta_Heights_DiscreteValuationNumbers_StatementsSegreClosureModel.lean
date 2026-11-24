-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureModel
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:29.609066+00:00
-- url     : https://prove2.me/theorems/cdc86628-39a2-4229-99a1-6c6cf85ffea1
-- title:
--   Statements Segre Closure Model
-- statement:
--   Definitions and structural lemmas for Statements Segre Closure Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSegreClosureModel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
section Objects
variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
def pairProjCoord (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ
  | ⟨none, l⟩ => ∑ i, t i * algebraMap Ω Φ (φ' l (e i))
  | ⟨some o, j⟩ => projCoord y e φ t ⟨o, j⟩
def zetaFirst (a : K → ℤ) : Option (Option K) → ℤ
  | none => 0
  | some none => 1
  | some (some k) => -a k
def zetaSecond (a : K → ℤ) : Option (Option K) → ℤ
  | none => 1
  | some none => 0
  | some (some k) => -a k
def liftPairDeg (L : K → ℤ) : Option (Option K) → ℤ
  | some (some k) => L k
  | _ => 0
def liftPairForm {R : Type*} [CommRing R] (M M' : ℕ) (f : MRing ι R) :
    MRing (bundleIdx (bundleIdx ι M) M') R :=
  rename (fun p : Σ k, ι k => (⟨some (some p.1), p.2⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)) f
end Objects
def zetaPowTimes (n m : ℕ) (R : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (1 + n)) ℤ :=
  X (Fin.castAdd n 0) ^ m * rename (Fin.natAdd 1) R
def GenericProjClosureModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∃ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ ∧ IsTwistedDualGens y B' a₀' φ' ∧
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1)) ∧
      ∃ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (pairProjCoord y e φ φ' t)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ ∧
        aeval (pairProjCoord y e φ φ' t) f₀ = aeval (pairProjCoord y e φ φ' t) g₀
section Examples
abbrev GenericCoordField (N : ℕ) : Type := FractionRing (MvPolynomial (Fin N) LineFieldDyadic)
def genericCoords (N : ℕ) : Fin N → GenericCoordField N :=
  fun i => algebraMap (MvPolynomial (Fin N) LineFieldDyadic) (GenericCoordField N) (X i)
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


