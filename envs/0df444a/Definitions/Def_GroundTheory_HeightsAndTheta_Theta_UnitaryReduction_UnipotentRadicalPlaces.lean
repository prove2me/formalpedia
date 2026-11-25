-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
-- name    : GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:45.719902+00:00
-- url     : https://prove2.me/theorems/ff54c4b6-7f82-5b19-9ab3-027b7a2f0e56
-- title:
--   Unipotent Radical Places
-- statement:
--   Definitions and structural lemmas for Unipotent Radical Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/UnitaryReduction/UnipotentRadicalPlaces.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Theta
namespace UnitaryReduction
open NumberField GroundTheory.Automorphic Module TensorProduct FunctionalEquationAlt FunctionalEquationAlt.MetSpace
open scoped InnerProductSpace nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
section Places
variable {S S' : MetSpace E}
variable (S)
def hsInner {τ : InfinitePlace E} (X Y : S.FibSp τ →ₗ[ℂ] S'.FibSp τ) : ℝ :=
  (LinearMap.trace ℂ (S'.FibSp τ) (X ∘ₗ LinearMap.adjoint Y)).re
def eucl (T T' : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) : ℝ :=
  ∑ τ, hsInner S (T τ) (T' τ)
def euclNorm (T : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) : ℝ :=
  Real.sqrt (eucl S T T)
end Places
section Frame
variable (S : MetSpace E) (B : HermitianForm F E S.V)
  (θ : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S.FibSp τ)
def formAt (τ : InfinitePlace E) (u v : S.FibSp τ) : ℂ := ⟪θ τ u, v⟫_ℂ
def rPrime (W : Submodule E S.V) (τ : InfinitePlace E) : Submodule ℂ (S.FibSp τ) :=
  (S.fibSub W τ).map (θ τ)
def mPrime (W : Submodule E S.V) (τ : InfinitePlace E) : Submodule ℂ (S.FibSp τ) :=
  ((S.fibSub W τ ⊔ rPrime S θ W τ).map (θ τ))ᗮ
def nnAt (W : Submodule E S.V) (τ : InfinitePlace E) : Set (S.FibSp τ →ₗ[ℂ] S.FibSp τ) :=
  {X | (∀ u v, formAt S θ τ (X u) v + formAt S θ τ u (X v) = 0) ∧
    (∀ y, X y ∈ S.fibSub (perp B W) τ) ∧ (∀ y ∈ S.fibSub (perp B W) τ, X y ∈ S.fibSub W τ) ∧
    ∀ y ∈ S.fibSub W τ, X y = 0}
def zzAt (W : Submodule E S.V) (τ : InfinitePlace E) : Set (S.FibSp τ →ₗ[ℂ] S.FibSp τ) :=
  {X | X ∈ nnAt S B θ W τ ∧ ∀ y ∈ S.fibSub (perp B W) τ, X y = 0}
def nrAt (W : Submodule E S.V) (τ : InfinitePlace E) : Set (S.FibSp τ →ₗ[ℂ] S.FibSp τ) :=
  {g | Function.Bijective g ∧ (∀ u v, formAt S θ τ (g u) (g v) = formAt S θ τ u v) ∧
    (∀ y, g y - y ∈ S.fibSub (perp B W) τ) ∧ (∀ y ∈ S.fibSub (perp B W) τ, g y - y ∈ S.fibSub W τ) ∧
    ∀ y ∈ S.fibSub W τ, g y = y}
def expAt {τ : InfinitePlace E} (X : S.FibSp τ →ₗ[ℂ] S.FibSp τ) : S.FibSp τ →ₗ[ℂ] S.FibSp τ :=
  1 + X + (2⁻¹ : ℂ) • (X * X)
def vvAt (W : Submodule E S.V) (τ : InfinitePlace E) : Set (S.FibSp τ →ₗ[ℂ] S.FibSp τ) :=
  {A | (∀ y ∈ S.fibSub (perp B W) τ, A y = 0) ∧ ∀ y, A y ∈ S.fibSub W τ}
def plusAt {τ : InfinitePlace E} (A : S.FibSp τ →ₗ[ℂ] S.FibSp τ) : S.FibSp τ →ₗ[ℂ] S.FibSp τ :=
  θ τ ∘ₗ LinearMap.adjoint A ∘ₗ θ τ
def sgAt {τ : InfinitePlace E} (A : S.FibSp τ →ₗ[ℂ] S.FibSp τ) : S.FibSp τ →ₗ[ℂ] S.FibSp τ :=
  -plusAt S θ A
end Frame
section Lattices
variable {S S' : MetSpace E}
def homSpace (A : Submodule E S.V) (B' : Submodule E S'.V) :
    Set (∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) :=
  {T | ∀ τ, (∀ y ∈ (S.fibSub A τ)ᗮ, T τ y = 0) ∧ ∀ y, T τ y ∈ S'.fibSub B' τ}
def homImage (A : Submodule (𝓞 E) S.V) (B' : Submodule (𝓞 E) S'.V) :
    Set (∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) :=
  {T | T ∈ homSpace (espan A) (espan B') ∧ ∃ U : S.V →ₗ[E] S'.V, (∀ a ∈ A, U a ∈ B') ∧
    ∀ τ, ∀ a ∈ A, T τ (S.pt τ a) = S'.pt τ (U a)}
variable (S)
def euclDual (𝕍 Γ : Set (∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ)) :
    Set (∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) :=
  {v | v ∈ 𝕍 ∧ ∀ γ ∈ Γ, ∃ z : ℤ, eucl S v γ = z}
end Lattices
def invDiff (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ 1
section Statements
def hsNorm (S : MetSpace E) {τ : InfinitePlace E} (X : S.FibSp τ →ₗ[ℂ] S.FibSp τ) : ℝ :=
  Real.sqrt (hsInner S X X)
def WittDecomp.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (X : SelfDualFrame F E) (R : Submodule (𝓞 E) X.S.V), SatIn R X.L → IsIsotropic X.B R →
  let S := X.S
  let B := X.B
  let θ := X.θ
  ∀ τ : InfinitePlace E,
    let Rτ := S.fibSub (espan R) τ
    let Pτ := S.fibSub (perp B (espan R)) τ
    let R' := rPrime S θ (espan R) τ
    let M' := mPrime S θ (espan R) τ
    ((∀ u ∈ R', ∀ v ∈ R', formAt S θ τ u v = 0) ∧ Pτᗮ = R' ∧ Pτ ⊓ Rτᗮ = M' ∧
      Rτ ⟂ M' ∧ Rτ ⟂ R' ∧ M' ⟂ R' ∧ Rτ ⊔ M' ⊔ R' = ⊤ ∧
      Rτ ⊔ M' = Pτ ∧ Rτ ⊓ M' = ⊥ ∧ (∀ m ∈ M', Metric.infDist m (Rτ : Set (S.FibSp τ)) = ‖m‖) ∧
      R' ⊔ Pτ = ⊤ ∧ R' ⊓ Pτ = ⊥ ∧ (∀ y ∈ R', Metric.infDist y (Pτ : Set (S.FibSp τ)) = ‖y‖)) ∧
    ((∀ (j : ℕ) (r : OrthonormalBasis (Fin j) ℂ Rτ),
        Orthonormal ℂ (fun i => θ τ (r i : S.FibSp τ)) ∧
        Submodule.span ℂ (Set.range fun i => θ τ (r i : S.FibSp τ)) = R' ∧
        ∀ i l, formAt S θ τ (θ τ (r l : S.FibSp τ)) (r i : S.FibSp τ) = if i = l then 1 else 0) ∧
      ∀ y ∈ R', ‖(innerSL ℂ (θ τ y)).comp Rτ.subtypeL‖ = ‖y‖) ∧
    M'.map (θ τ) = M'
def BlocksAt.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (X : SelfDualFrame F E) (R : Submodule (𝓞 E) X.S.V), SatIn R X.L → IsIsotropic X.B R →
  let S := X.S
  let B := X.B
  let θ := X.θ
  ∀ τ : InfinitePlace E,
    let PR : S.FibSp τ →ₗ[ℂ] S.FibSp τ := (S.fibSub (espan R) τ).starProjection
    let PM : S.FibSp τ →ₗ[ℂ] S.FibSp τ := (mPrime S θ (espan R) τ).starProjection
    let PR' : S.FibSp τ →ₗ[ℂ] S.FibSp τ := (rPrime S θ (espan R) τ).starProjection
    (∀ X ∈ nnAt S B θ (espan R) τ,
      X = X ∘ₗ PM + PR ∘ₗ X ∘ₗ PR' + PM ∘ₗ X ∘ₗ PR' ∧
      PM ∘ₗ X ∘ₗ PR' = -(θ τ ∘ₗ LinearMap.adjoint (X ∘ₗ PM) ∘ₗ θ τ) ∧
      hsNorm S (PM ∘ₗ X ∘ₗ PR') = hsNorm S (X ∘ₗ PM) ∧
      hsNorm S X ^ 2 = 2 * hsNorm S (X ∘ₗ PM) ^ 2 + hsNorm S (PR ∘ₗ X ∘ₗ PR') ^ 2) ∧
    (∀ X, X ∈ zzAt S B θ (espan R) τ ↔ X ∈ nnAt S B θ (espan R) τ ∧ X ∘ₗ PM = 0) ∧
    ∀ X ∈ nnAt S B θ (espan R) τ,
      (∀ Z ∈ zzAt S B θ (espan R) τ, hsInner S X Z = 0) ↔ PR ∘ₗ X ∘ₗ PR' = 0
def WW {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (L : Submodule (𝓞 E) V) (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {A | (∀ y ∈ perp B W, A y = 0) ∧ (∀ y, A y ∈ W) ∧ IsIntegralMul L 1 A}
def SkewCentre.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (X : SelfDualFrame F E) (R : Submodule (𝓞 E) X.S.V), SatIn R X.L → IsIsotropic X.B R →
  let S := X.S
  let B := X.B
  let θ := X.θ
  (∀ τ : InfinitePlace E,
      (∀ A ∈ vvAt S B (espan R) τ, sgAt S θ A ∈ vvAt S B (espan R) τ ∧ sgAt S θ (sgAt S θ A) = A) ∧
      (∀ A ∈ vvAt S B (espan R) τ, ∀ A' ∈ vvAt S B (espan R) τ,
        hsInner S (sgAt S θ A) (sgAt S θ A') = hsInner S A A') ∧
      (∀ A, A ∈ zzAt S B θ (espan R) τ ↔ A ∈ vvAt S B (espan R) τ ∧ sgAt S θ A = A) ∧
      ∀ (j : ℕ) (r : OrthonormalBasis (Fin j) ℂ (S.fibSub (espan R) τ)),
        ∀ A ∈ vvAt S B (espan R) τ, ∀ i l,
          ⟪(r i : S.FibSp τ), plusAt S θ A (θ τ (r l : S.FibSp τ))⟫_ℂ =
            starRingEnd ℂ ⟪(r l : S.FibSp τ), A (θ τ (r i : S.FibSp τ))⟫_ℂ) ∧
    (∀ A : S.V →ₗ[E] S.V, (∀ y ∈ perp B (espan R), A y = 0) → (∀ y, A y ∈ espan R) →
      (A ∈ WW B X.L (espan R) ↔ ∀ u ∈ X.L, ∀ u' ∈ X.L, B.toSesq u' (A u) ∈ Set.range (algebraMap (𝓞 E) E))) ∧
    ∀ A ∈ WW B X.L (espan R), ∃ A' ∈ WW B X.L (espan R), ∀ τ, sgAt S θ (S.fibMap S A τ) = S.fibMap S A' τ
def DualHom.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (S S' : MetSpace E) (A : Submodule (𝓞 E) S.V) (B' : Submodule (𝓞 E) S'.V), A.FG → B'.FG →
    euclDual S (homSpace (espan A) (espan B')) (homImage A B') =
      {T | ∃ U : S'.V →ₗ[E] S.V,
        (∀ b ∈ B', U b ∈ smulIdeal (FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E) A) ∧
        ∀ τ, T τ = LinearMap.adjoint
          (S'.fibMap S U τ ∘ₗ ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ))}
end Statements
end UnitaryReduction
end GroundTheory.Heights₂.Theta


