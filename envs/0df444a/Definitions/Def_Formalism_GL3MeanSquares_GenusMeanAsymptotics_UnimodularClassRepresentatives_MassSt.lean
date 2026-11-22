-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:33.406329+00:00
-- url     : https://prove2.me/theorems/fe998af1-21f7-45b1-b1cb-56c43215cb9a
-- title:
--   Mass St
-- statement:
--   Definitions and structural lemmas for Mass St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassSt.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
section Defs
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def IsTotPosDef (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ x : V, x ≠ 0 → ∀ φ : K →+* ℂ, 0 < (φ (h x x)).re
def repCount (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (t : K) : ℕ :=
  Nat.card {x : V // x ∈ L ∧ h x x = t}
def repMass (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (t : K) : ℝ := by
  classical
  exact if hs : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s then
    ∑ M ∈ hs.choose, (repCount h M t : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) else 0
end Defs
def conjO (K : Type*) [Field K] [StarRing K] : 𝓞 K →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (starRingEnd K)
def normRepCount (K : Type*) [Field K] [StarRing K] (Q : Ideal (𝓞 K)) (M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → 𝓞 K ⧸ Q // ∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk Q (y i) = x i) ∧
    Ideal.Quotient.mk Q (∑ i, conjO K (y i) * y i) = Ideal.Quotient.mk Q n}
def etaF (K F : Type*) [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) : ℝ := by
  classical
  exact if (𝔭.map (algebraMap (𝓞 F) (𝓞 K))).IsPrime then -1 else 1
def lValEtaF (K F : Type*) [Field K] [Field F] [NumberField F] [Algebra F K] (M : ℕ) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
    (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹
def SiegelOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (M : ℕ), 3 ≤ M →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
      (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V),
      h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L M →
      Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.massRatioRightSide K M * repMass h L 1
def OrbitCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (M : ℕ), 2 ≤ M →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) V'),
      h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L M →
      Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' (M - 1) →
      repMass h L 1 = Formalism.HermitianLatticesTheory.mass h' L'
def GenusOrtho : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (I : Submodule (𝓞 K) V),
      h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n →
      ∀ L : Submodule (𝓞 K) V, L ∈ Formalism.HermitianLatticesTheory.genus h I ↔
        (Submodule.IsLattice K L ∧
          ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L)
def LandherrUnram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
      h.IsSymm → IsTotPosDef h → finrank K V = n →
      (∃ L : Submodule (𝓞 K) V, Submodule.IsLattice K L ∧
        ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) →
      ∃ L : Submodule (𝓞 K) V, Formalism.HermitianLatticesTheory.IsOrthoLattice h L n
def LocalDensity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (P : Ideal (𝓞 K)), P.IsMaximal → ∀ (M k : ℕ), 1 ≤ M → 1 ≤ k →
    ∀ n : 𝓞 K, conjO K n = n → n ∉ P →
      (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P →
        (normRepCount K (P ^ k) M n : ℝ) =
          Real.sqrt (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) *
            (1 - (-1 : ℝ) ^ M * Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)))) ∧
      (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P →
        (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n : ℝ) =
          (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) *
            (1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))))
def DiscrTower : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → (∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) →
      |(discr K : ℝ)| = (discr F : ℝ) ^ 2 ∧ finrank ℚ F = Formalism.HermitianLatticesTheory.fDeg K ∧
        (discr F : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K
def EulerEta : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → (∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) →
    ∀ M : ℕ, 2 ≤ M →
      Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
      0 < Formalism.HermitianLatticesTheory.lValEta K M ∧ Formalism.HermitianLatticesTheory.lValEta K M = lValEtaF K F M
end Formalism.HermitianLattices.Ext.L3


