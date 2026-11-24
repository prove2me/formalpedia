-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:05.806599+00:00
-- url     : https://prove2.me/theorems/0dc2ecd5-faf3-45a9-8995-550d20ae9231
-- title:
--   Statements Bundles
-- statement:
--   Definitions and structural lemmas for Statements Bundles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
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
def NumericalSegre.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (n : ℕ) (Y : List (K → ℤ)), n + Y.length = N - 1 + e →
      intNumL F (projIdeal F y w φ t) (List.replicate n zetaDeg ++ Y.map liftDeg) =
        if N - 1 ≤ n then
          ∑ α ∈ Finset.Nat.antidiagonalTuple N (n - (N - 1)),
            intNumL F (pointIdeal F y) (rootList (fun i => a - b i) α ++ Y)
        else 0
def FlagIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' v v' : Module.Basis (Fin N) Ω E) (x x' u u' : Fin N → K → ℤ)
      (f g f₂ g₂ : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B B' v v' u u' f₂ g₂ →
    ∀ (m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m → G.IsSymmetric →
    ∀ (Gs Hs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ), IsPairExpansion m G Gs →
      IsPairExpansion m G Hs →
    ∀ Q : List (K → ℤ), Q.length + m = d + 1 →
      pairNum (pointIdeal O y) x x' f g Gs Q = pairNum (pointIdeal O y) u u' f₂ g₂ Hs Q
def PairNumberPullback.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (d r : ℕ),
      IsModelOver (pointIdeal O y) d → IsModelOver (pointIdeal O (joinCoords y y')) (d + r) →
    ∀ (N : ℕ) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      (∀ i, IsVerticalDivisor (pointIdeal O y) ϖ (x i - x' i) (f i) (g i)) →
    ∀ (m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m →
    ∀ Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ, IsPairExpansion m G Gs →
    ∀ Q : List (K → ℤ), Q.length + m = d + r + 1 →
      (0 < r → pairNum (pointIdeal O (joinCoords y y')) (fun i => joinDeg (x i))
        (fun i => joinDeg (x' i)) (fun i => joinForm (f i)) (fun i => joinForm (g i)) Gs
        (Q.map joinDeg) = 0) ∧
      (IsBirationalJoin O y y' → pairNum (pointIdeal O (joinCoords y y')) (fun i => joinDeg (x i))
        (fun i => joinDeg (x' i)) (fun i => joinForm (f i)) (fun i => joinForm (g i)) Gs
        (Q.map joinDeg) = pairNum (pointIdeal O y) x x' f g Gs Q)
def PairCocycle.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' B'' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' → SameGenericFibre ϖ B' B'' →
    ∀ (w w' w'' : Module.Basis (Fin N) Ω E) (x x' x'' : Fin N → K → ℤ)
      (f g f' g' f'' g'' : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B' B'' w' w'' x' x'' f' g' →
      IsFlagPair ϖ y B B'' w w'' x x'' f'' g'' →
    ∀ (k : ℕ) (Gs Gs' Gs'' : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ),
      IsPairExpansion k (psum (Fin N) ℤ k) Gs → IsPairExpansion k (psum (Fin N) ℤ k) Gs' →
      IsPairExpansion k (psum (Fin N) ℤ k) Gs'' →
    ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
      pairNum (pointIdeal O y) x x'' f'' g'' Gs'' Q =
          pairNum (pointIdeal O y) x x' f g Gs Q + pairNum (pointIdeal O y) x' x'' f' g' Gs' Q ∧
        ∀ (fr gr : Fin N → MRing ι O) (Gr : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ),
          IsFlagPair ϖ y B' B w' w x' x fr gr → IsPairExpansion k (psum (Fin N) ℤ k) Gr →
          pairNum (pointIdeal O y) x' x fr gr Gr Q = -pairNum (pointIdeal O y) x x' f g Gs Q
def SubQuotient.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N r : ℕ) (E U V : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup U] [Module Ω U]
      [AddCommGroup V] [Module Ω V]
      (B B' : ChartBundle O (segreVec y) N E) (BU BU' : ChartBundle O (segreVec y) r U)
      (BV BV' : ChartBundle O (segreVec y) (N - r) V) (j : U →ₗ[Ω] E) (π : E →ₗ[Ω] V),
      Function.Injective j → Function.Surjective π → LinearMap.range j = LinearMap.ker π →
      SameGenericFibre ϖ B B' →
      (∀ c, segreVec y c ≠ 0 →
        (∀ z, z ∈ BU.lat c ↔ j z ∈ B.lat c) ∧ (∀ z, z ∈ BU'.lat c ↔ j z ∈ B'.lat c) ∧
        (∀ q, q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, π z = q) ∧
        (∀ q, q ∈ BV'.lat c ↔ ∃ z ∈ B'.lat c, π z = q)) →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (wU wU' : Module.Basis (Fin r) Ω U) (xU xU' : Fin r → K → ℤ) (fU gU : Fin r → MRing ι O),
      IsFlagPair ϖ y BU BU' wU wU' xU xU' fU gU →
    ∀ (wV wV' : Module.Basis (Fin (N - r)) Ω V) (xV xV' : Fin (N - r) → K → ℤ)
      (fV gV : Fin (N - r) → MRing ι O),
      IsFlagPair ϖ y BV BV' wV wV' xV xV' fV gV →
    ∀ (k : ℕ) (Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ)
      (GsU : Fin r → MvPolynomial (Fin r ⊕ Fin r) ℤ)
      (GsV : Fin (N - r) → MvPolynomial (Fin (N - r) ⊕ Fin (N - r)) ℤ),
      IsPairExpansion k (psum (Fin N) ℤ k) Gs → IsPairExpansion k (psum (Fin r) ℤ k) GsU →
      IsPairExpansion k (psum (Fin (N - r)) ℤ k) GsV →
    ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
      pairNum (pointIdeal O y) x x' f g Gs Q =
        pairNum (pointIdeal O y) xU xU' fU gU GsU Q + pairNum (pointIdeal O y) xV xV' fV gV GsV Q
def ScalarQuotient.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E)
      (n : ℕ) (u : Oˣ),
      (∀ c, segreVec y c ≠ 0 → ∀ z, z ∈ B'.lat c ↔
        ∃ z₀ ∈ B.lat c, z = algebraMap O Ω ((u : O) * ϖ ^ n) • z₀) →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (k : ℕ) (Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ),
      IsPairExpansion k (psum (Fin N) ℤ k) Gs →
    ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
      pairNum (pointIdeal O y) x x' f g Gs Q =
        (k : ℤ) * n * cycEval (fun W => classNum x (psum (Fin N) ℤ (k - 1)) Q W)
          (divCycle (pointIdeal O y) (C ϖ))
section Examples
abbrev LineIdx : Unit → Type := fun _ => Fin 2
def psumExpansion (N k : ℕ) : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ :=
  fun i => ∑ j ∈ Finset.range k, X (Sum.inl i) ^ j * X (Sum.inr i) ^ (k - 1 - j)
abbrev LineFieldTwoElement : Type := FractionRing (MRing LineIdx (ZMod 2))
end Examples
section ExamplesDVR
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
instance pointIdeal_isPrime (y : (Σ k, ι k) → Ω) : (pointIdeal O y).IsPrime :=
  RingHom.ker_isPrime _
def firstLine (Ω : Type*) [Field Ω] : (Fin 1 → Ω) →ₗ[Ω] (Fin 2 → Ω) :=
  LinearMap.pi fun q : Fin 2 => if q = 0 then LinearMap.proj 0 else 0
def secondCoord (Ω : Type*) [Field Ω] : (Fin 2 → Ω) →ₗ[Ω] (Fin 1 → Ω) :=
  LinearMap.pi fun _ : Fin 1 => LinearMap.proj 1
end ExamplesDVR
section ExamplesZ2
abbrev LineFieldDyadic : Type := FractionRing (MRing LineIdx ℤ_[2])
abbrev scaledTrivialBundleDyadicLine (r : ℕ) {s : LineFieldDyadic} (hs : s ≠ 0) :
    ChartBundle ℤ_[2] (segreVec (genericPt ℤ_[2] LineIdx)) r (Fin r → LineFieldDyadic) :=
  scaledTrivBundle ℤ_[2] (segreVec (genericPt ℤ_[2] LineIdx)) r hs
abbrev PointIdx : Unit → Type := fun _ => Fin 1
end ExamplesZ2
section ExamplesEuler
variable {Ω : Type*} [Field Ω] {R : Type*} [CommRing R] [Algebra R Ω]
abbrev LinePt (Ω : Type*) := (Σ k : Unit, LineIdx k) → Ω
def eulerEquiv (y0 y1 s : Ω) (h0 : y0 ≠ 0) (hs : s ≠ 0) : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω) where
  toFun v := ![-(v 1) / (s * y0), (y0 * v 0 + y1 * v 1) / s]
  map_add' u v := by
    funext i; fin_cases i <;> simp <;> field_simp <;> ring
  map_smul' a v := by
    funext i; fin_cases i <;> simp <;> field_simp
  invFun p := ![s * (p 0 * y1 + p 1 / y0), - (s * p 0 * y0)]
  left_inv v := by
    funext i; fin_cases i <;> simp <;> field_simp <;> ring
  right_inv p := by
    funext i; fin_cases i <;> simp <;> field_simp <;> ring
def eulerBasis (y0 y1 s : Ω) (h0 : y0 ≠ 0) (hs : s ≠ 0) : Module.Basis (Fin 2) Ω (Fin 2 → Ω) :=
  Module.Basis.ofEquivFun (eulerEquiv y0 y1 s h0 hs)
def eulerDeg : Fin 2 → Unit → ℤ := ![fun _ => -1, fun _ => 1]
section Pair
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
end Pair
end ExamplesEuler
end
end GroundTheory.Heights₂.Heights.NumbersDVR


