-- Prove2me | Definitions.Def_Formalism_SmithDeterminants_StatementDVR
-- name    : Formalism_SmithDeterminants_StatementDVR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:39.401928+00:00
-- url     : https://prove2.me/theorems/5b6e0720-2336-46c1-8ace-1edb270d057a
-- title:
--   Statement DVR
-- statement:
--   Definitions and structural lemmas for Statement DVR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SmithDeterminants/StatementDVR.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.A
def mulRange {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (c : R) :
    Submodule R M :=
  LinearMap.range (c • (LinearMap.id : M →ₗ[R] M))
structure SmithData {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (y : M →ₗ[R] M) (d : ℕ) where
  b : Module.Basis (Fin d) R M
  b' : Module.Basis (Fin d) R M
  a : Fin d → R
  hy : ∀ i, y (b i) = a i • b' i
open Classical in

def SmithData.nAbove {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {y : M →ₗ[R] M} {d : ℕ} (S : SmithData y d) (ϖ : R) (t : ℕ) : ℕ :=
  (univ.filter fun i => ¬ S.a i ∣ ϖ ^ t).card
open Classical in

def SmithData.nBetween {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {y : M →ₗ[R] M} {d : ℕ} (S : SmithData y d) (ϖ : R) (t E : ℕ) : ℕ :=
  (univ.filter fun i => ¬ S.a i ∣ ϖ ^ t ∧ S.a i ∣ ϖ ^ E).card
def chain {K : Type*} [Field K] {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) : ∀ m, V 0 →ₗ[K] V m
  | 0 => LinearMap.id
  | m + 1 => (θ m).comp (chain θ m)
def TruncHyp (O K : Type) [CommRing O] [Field K] [Algebra O K] (V : ℕ → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module O (V i)]
    [∀ i, IsScalarTower O K (V i)]
    (M : ∀ i, Submodule O (V i)) (E : ∀ i, Submodule K (V i)) (y T : ∀ i, V i →ₗ[K] V i)
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) (ϖ : O) (c : ℕ → O) (e f s' : ℕ → ℤ) : Prop :=
  algebraMap O K ϖ ≠ 0 ∧
  (∀ i, ∀ v ∈ E i, y i v ∈ E i) ∧
  (∀ i, ∀ v ∈ E i, θ i v ∈ E (i + 1)) ∧
  (∀ i, ∀ v ∈ E i, θ i (y i v) = y (i + 1) (θ i v)) ∧

  (∀ i, ∀ v ∈ M i, θ i v ∈ M (i + 1)) ∧

  (∀ i, ∀ v ∈ M i, ∃ w ∈ M (i + 1), θ i (T i v) = (algebraMap O K ϖ) ^ (s' i) • w) ∧
  (∀ i, ∀ v ∈ E i, T i v = (algebraMap O K ϖ) ^ (e i) • y i v +
      ((algebraMap O K ϖ) ^ (f i) * algebraMap O K (c i)) • v) ∧
  (∀ i, s' i ≤ f i)
def LatticeChainBound : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (V : ℕ → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module O (V i)]
    [∀ i, IsScalarTower O K (V i)]
    (M : ∀ i, Submodule O (V i)) (E : ∀ i, Submodule K (V i)) (y T : ∀ i, V i →ₗ[K] V i)
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) (ϖ : O) (c : ℕ → O) (e f s' : ℕ → ℤ),
    TruncHyp O K V M E y T θ ϖ c e f s' →
    ∀ m : ℕ, ∀ φ ∈ M 0, φ ∈ E 0 →
      ∃ w ∈ M m, chain θ m ((y 0 ^ m) φ) =
        (algebraMap O K ϖ) ^ (∑ i ∈ range m, (s' i - e i)) • w
def LatticeChainBoundNonneg : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (V : ℕ → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module O (V i)]
    [∀ i, IsScalarTower O K (V i)]
    (M : ∀ i, Submodule O (V i)) (E : ∀ i, Submodule K (V i)) (y T : ∀ i, V i →ₗ[K] V i)
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) (ϖ : O) (c : ℕ → O) (e f s' : ℕ → ℤ),
    TruncHyp O K V M E y T θ ϖ c e f s' →
    (∀ v ∈ M 0, y 0 v ∈ M 0) →
    ∀ m : ℕ, ∀ φ ∈ M 0, φ ∈ E 0 →
      ∃ w ∈ M m, chain θ m ((y 0 ^ m) φ) =
        (algebraMap O K ϖ) ^ (∑ i ∈ range m, max (s' i - e i) 0) • w
def RangePowGenerators : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (y : M →ₗ[R] M) (π : R)
    (t n : ℕ) (g : Fin n → M),
    mulRange (M := M) (π ^ t) ≤ LinearMap.range y ⊔ Submodule.span R (Set.range g) →
    ∀ j : ℕ, ∃ gj : Fin (j * n) → M,
      mulRange (M := M) (π ^ (j * t)) ≤
        LinearMap.range (y ^ j) ⊔ Submodule.span R (Set.range gj)
def SmithGen : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (y : M →ₗ[R] M) (d : ℕ)
    (Sd : SmithData y d) (ϖ : R) (t : ℕ),
    ∃ g : Fin (Sd.nAbove ϖ t) → M,
      mulRange (M := M) (ϖ ^ t) ≤ LinearMap.range y ⊔ Submodule.span R (Set.range g)
def LengthQuotientBound : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (t n S m : ℕ) (g : Fin n → M),
    mulRange (M := M) (ϖ ^ t) ≤ LinearMap.range y ⊔ Submodule.span R (Set.range g) →
    Module.length R (M ⧸ (LinearMap.range (y ^ m) ⊔ mulRange (M := M) (ϖ ^ S))) ≤
      ((Module.finrank R M * m * t + m * n * S : ℕ) : ℕ∞)
def TruncDet : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) R M) (L : M →ₗ[R] (Fin d → R)) (Λ : Submodule R M)
      (S ℓ : ℕ),
    (∀ v ∈ Λ, ∃ w : Fin d → R, L v = ϖ ^ S • w) →
    Module.length R (M ⧸ Λ) ≤ (ℓ : ℕ∞) →
    ϖ ^ (d * S) ∣ ϖ ^ ℓ * (LinearMap.toMatrix b (Pi.basisFun R (Fin d)) L).det
def TruncFinal : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (d : ℕ) (Sd : SmithData y d) (L : M →ₗ[R] (Fin d → R)) (t S m : ℕ),
    (∀ v : M, ∃ w : Fin d → R, L ((y ^ m) v) = ϖ ^ S • w) →
    ϖ ^ (d * S) ∣ ϖ ^ (d * m * t + m * Sd.nAbove ϖ t * S) *
      (LinearMap.toMatrix Sd.b (Pi.basisFun R (Fin d)) L).det
def TwoTier : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (d : ℕ) (Sd : SmithData y d) (t E G m : ℕ),
    Module.length R (M ⧸ (LinearMap.range (y ^ m) ⊔ mulRange (M := M) (ϖ ^ G))) ≤
      ((m * (d * t + Sd.nBetween ϖ t E * E + Sd.nAbove ϖ E * G) : ℕ) : ℕ∞)
def SatChain : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (d : ℕ) (Sd : SmithData y d) (t r : ℕ),
    ∃ A : Submodule R M, (∀ v : M, ϖ • v ∈ A → v ∈ A) ∧
      Module.finrank R (M ⧸ A) ≤ r * Sd.nAbove ϖ t ∧
      ∀ v ∈ A, ϖ ^ (r * t) • v ∈ LinearMap.range (y ^ r)
def GradedHorn : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (d : ℕ) (Sd : SmithData y d) (m g : ℕ),
    Module.length R (M ⧸ (LinearMap.range (y ^ m) ⊔ mulRange (M := M) (ϖ ^ (m * g)))) ≤
      ((m * ∑ j ∈ range g, min d (m * Sd.nAbove ϖ j) : ℕ) : ℕ∞) ∧
    ∀ t₀ : ℕ,
    Module.length R (M ⧸ (LinearMap.range (y ^ m) ⊔ mulRange (M := M) (ϖ ^ (m * g)))) ≤
      ((m * (d * t₀ + m * ∑ j ∈ Ico t₀ g, Sd.nAbove ϖ j) : ℕ) : ℕ∞)
def SmithExists : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (y : M →ₗ[R] M),
    Nonempty (SmithData y (Module.finrank R M))
end Formalism.A


