-- Prove2me | Definitions.Def_Formalism_HermitianLattices_StatementMass
-- name    : Formalism_HermitianLattices_StatementMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:58.824627+00:00
-- url     : https://prove2.me/theorems/494e315a-d109-4fb9-9f84-26868d4c7882
-- title:
--   Statement Mass
-- statement:
--   Definitions and structural lemmas for Statement Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/StatementMass.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.HermitianLatticesTheory
def mass {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V) :
    ℝ := by
  classical
  exact if hs : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s then
    ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ else 0
def IsOrthoLattice {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (RingOfIntegers K) V) (n : ℕ) : Prop :=
  ∃ e : Fin n → V, LinearIndependent K e ∧ Submodule.span K (Set.range e) = ⊤ ∧
    L = Submodule.span (RingOfIntegers K) (Set.range e) ∧
    ∀ i j, h (e i) (e j) = if i = j then 1 else 0
def fDeg (K : Type*) [Field K] [NumberField K] : ℕ := Fintype.card (InfinitePlace K)
def vInv (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * fDeg K)) / 2
def eulerFac (K : Type*) [Field K] [NumberField K] [StarRing K] (M : ℕ)
    (P : Ideal (RingOfIntegers K)) : ℝ :=
  if conjIdeal (K := K) P = P then
    (1 - (-1 : ℝ) ^ M * (Real.sqrt (Ideal.absNorm P : ℝ)) ^ (-(M : ℤ)))⁻¹
  else
    (1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))) ^ (-(1 : ℝ) / 2)
def lValEta (K : Type*) [Field K] [NumberField K] [StarRing K] (M : ℕ) : ℝ :=
  ∏' P : {P : Ideal (RingOfIntegers K) // P.IsMaximal}, eulerFac K M P.1
def massRatioRightSide (K : Type*) [Field K] [NumberField K] [StarRing K] (M : ℕ) : ℝ :=
  (((Nat.factorial (M - 1) : ℕ) : ℝ) * (vInv K / Real.pi) ^ M) ^ fDeg K /
    Real.sqrt ((2 * vInv K) ^ fDeg K) * lValEta K M
def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P
end Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
open NumberField
def MassBasic : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (RingOfIntegers K) V, Submodule.IsLattice K L →
      (∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s) ∧
      (∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s →
        mass h L = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹) ∧
      0 < mass h L
def SiegelMassRatio : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K →
    ∀ (M : ℕ), 3 ≤ M →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (RingOfIntegers K) V]
      [IsScalarTower (RingOfIntegers K) K V] [AddCommGroup V'] [Module K V']
      [Module (RingOfIntegers K) V'] [IsScalarTower (RingOfIntegers K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (L : Submodule (RingOfIntegers K) V) (L' : Submodule (RingOfIntegers K) V'),
      h.IsSymm → h'.IsSymm → IsOrthoLattice h L M → IsOrthoLattice h' L' (M - 1) →
      mass h L / mass h' L' = massRatioRightSide K M
def MassTelescope : Prop :=
  SiegelMassRatio →
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K →
    ∀ (k r : ℕ), 2 ≤ k → k ≤ r →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (RingOfIntegers K) V]
      [IsScalarTower (RingOfIntegers K) K V] [AddCommGroup V'] [Module K V']
      [Module (RingOfIntegers K) V'] [IsScalarTower (RingOfIntegers K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (L : Submodule (RingOfIntegers K) V) (L' : Submodule (RingOfIntegers K) V'),
      h.IsSymm → h'.IsSymm → IsOrthoLattice h L k → IsOrthoLattice h' L' r →
      mass h' L' = mass h L * ∏ M ∈ Finset.Ico (k + 1) (r + 1), massRatioRightSide K M
end Formalism.HermitianLatticesTheory


