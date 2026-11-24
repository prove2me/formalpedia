-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:59.705269+00:00
-- url     : https://prove2.me/theorems/094cbd14-ace2-4827-a429-c965ebe3c51d
-- title:
--   Statements Segre Flag Closure
-- statement:
--   Definitions and structural lemmas for Statements Segre Flag Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSegreFlagClosure.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureNumber
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
def flagCoord (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (k : ℕ) : Fin N → Φ :=
  fun j => if (j : ℕ) < k then ∑ i, t i * algebraMap Ω Φ (w.repr (e i) j) else 0
def flagClosurePt (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (k : ℕ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ :=
  pairProjCoord y w φ φ' (flagCoord w e t k)
end Objects
def closureDeg {K : Type*} {m : ℕ} (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    Fin (1 + m) → Option (Option K) → ℤ :=
  Fin.append (fun _ : Fin 1 => ζ) (fun j => liftPairDeg (L j))
def closureForm {K : Type*} {ι : K → Type} {R : Type*} [CommRing R] {m : ℕ} (M M' : ℕ)
    (h : MRing (bundleIdx (bundleIdx ι M) M') R) (F : Fin m → MRing ι R) :
    Fin (1 + m) → MRing (bundleIdx (bundleIdx ι M) M') R :=
  Fin.append (fun _ : Fin 1 => h) (fun j => liftPairForm M M' (F j))
def SegreFlagClosureModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t k)) (d + (k - 1)) ∧
      ∃ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t k)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ ∧
        aeval (flagClosurePt y w e φ φ' t k) f₀ = aeval (flagClosurePt y w e φ φ' t k) g₀
def SegreFlagClosureCut.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (f₁ g₁ f₂ g₂ : MRing (bundleIdx (bundleIdx ι M) M') O),
      IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ
        (zetaFirst a₀ - zetaSecond a₀') f₁ g₁ →
      aeval (flagClosurePt y w e φ φ' t (k + 1)) f₁ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₁ →
      (0 < k → IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t k)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₂ g₂ ∧
        aeval (flagClosurePt y w e φ φ' t k) f₂ = aeval (flagClosurePt y w e φ φ' t k) g₂) →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (m : ℕ) (A : MvPolynomial (Fin (1 + (N + n))) ℤ), A.IsHomogeneous m →
    ∀ As Bs : Fin (1 + (N + n)) → MvPolynomial (Fin (1 + (N + n)) ⊕ Fin (1 + (N + n))) ℤ,
      IsPairExpansion (m + 1)
        ((X (Fin.castAdd (N + n) (0 : Fin 1)) + X (Fin.natAdd 1 (Fin.castAdd n ⟨k, hk⟩))) * A) As →
      IsPairExpansion m A Bs →
    ∀ Q : List (K → ℤ), Q.length + (m + 1) = d + k + 1 →
      pairNum (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)))
          (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
          (closureForm M M' f₁ (Fin.append f fz)) (closureForm M M' g₁ (Fin.append g gz)) As
          (Q.map liftPairDeg) =
        if k = 0 then 0 else
          pairNum (pointIdeal O (flagClosurePt y w e φ φ' t k))
            (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
            (closureForm M M' f₂ (Fin.append f fz)) (closureForm M M' g₂ (Fin.append g gz)) Bs
            (Q.map liftPairDeg)
def SegreFlagClosurePullback.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ), 1 ≤ k → k ≤ N → ∀ f₁ g₁ : MRing (bundleIdx (bundleIdx ι M) M') O,
      IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t k)) ϖ
        (zetaFirst a₀ - zetaSecond a₀') f₁ g₁ →
      aeval (flagClosurePt y w e φ φ' t k) f₁ = aeval (flagClosurePt y w e φ φ' t k) g₁ →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (r : ℕ) (Bf : MvPolynomial (Fin (N + n)) ℤ), Bf.IsHomogeneous r →
    ∀ (As : Fin (1 + (N + n)) → MvPolynomial (Fin (1 + (N + n)) ⊕ Fin (1 + (N + n))) ℤ)
      (Bs : Fin (N + n) → MvPolynomial (Fin (N + n) ⊕ Fin (N + n)) ℤ),
      IsPairExpansion r (rename (Fin.natAdd 1) Bf) As → IsPairExpansion r Bf Bs →
    ∀ Q : List (K → ℤ), Q.length + r = d + k →
      pairNum (pointIdeal O (flagClosurePt y w e φ φ' t k))
          (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
          (closureForm M M' f₁ (Fin.append f fz)) (closureForm M M' g₁ (Fin.append g gz)) As
          (Q.map liftPairDeg) =
        if k = 1 then
          pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
            (Fin.append g gz) Bs Q
        else 0
section Examples
def cutExpansion : Fin (1 + (1 + 1)) → MvPolynomial (Fin (1 + (1 + 1)) ⊕ Fin (1 + (1 + 1))) ℤ :=
  fun i => if (i : ℕ) < 2 then 1 else 0
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


