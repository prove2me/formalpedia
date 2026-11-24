-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:49.030275+00:00
-- url     : https://prove2.me/theorems/258aad8c-139d-4280-867a-bf9b8c06e7e0
-- title:
--   Std Coord Map Injective
-- statement:
--   Definitions and structural lemmas for Std Coord Map Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
def S6.LineCoordinates.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    ∃ (n : ℕ) (e : Fin n ≃ X) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ)
      (ψ : E.carrier →ₗ[𝓞 K] (Fin n → K)),
      (∀ i, a i ≠ 0) ∧ (∀ σ i, 0 < d σ i) ∧ (∀ σ i, d (conjugate σ) i = d σ i) ∧
      Function.Injective ψ ∧ LinearMap.range ψ = idealLattice a ∧
      Module.finrank (𝓞 K) E.carrier = n ∧
      (∀ i, (L (e i)).map ψ = idealLattice a ⊓
        (Submodule.span K {(Pi.single i 1 : Fin n → K)}).restrictScalars (𝓞 K)) ∧
      ∀ (σ : K →+* ℂ) (v w : E.carrier),
        (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
          star (embVec σ (ψ v)) ⬝ᵥ (diagMetric d σ *ᵥ embVec σ (ψ w))
def S6.CoordinateDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (n : ℕ)
    (H : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (ψ : E.carrier →ₗ[𝓞 K] (Fin n → K)),
    Function.Injective ψ → Submodule.span K (LinearMap.range ψ : Set (Fin n → K)) = ⊤ →
    (∀ (σ : K →+* ℂ) (v w : E.carrier),
        (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
          star (embVec σ (ψ v)) ⬝ᵥ (H σ *ᵥ embVec σ (ψ w))) →
    ∀ (G : Submodule (𝓞 K) E.carrier) (ι : Type) [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K),
      LinearIndependent K u →
      G.map ψ = LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) →
      E.degree G = subDegree (LinearMap.range ψ) H u
def S6.QuotientDegreeSplit.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K))
    (H : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), Λ.FG →
    Submodule.span K (Λ : Set (Fin n → K)) = ⊤ →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
      LinearIndependent K (Sum.elim b c) → m + k = n →
      quotDegree Λ H b c = subDegree Λ H (Sum.elim b c) - subDegree Λ H b
def S6.ExtensionDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E' E E'' : HermitianBundle.{0} K)
    (Y : HermitianExtension E' E E''),
    E''.degree ⊤ = E.degree ⊤ - E.degree (LinearMap.range Y.incl)
def S6.SaturatedSpan.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] (n : ℕ) (ψ : M →ₗ[𝓞 K] (Fin n → K)), Function.Injective ψ →
    ∀ G : Submodule (𝓞 K) M, (∀ (t : 𝓞 K) (x : M), t ≠ 0 → t • x ∈ G → x ∈ G) →
      ∃ b : Fin (Module.finrank (𝓞 K) G) → Fin n → K, LinearIndependent K b ∧
        G.map ψ = LinearMap.range ψ ⊓ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)
def stdCoordMap (K : Type*) [Field K] (n : ℕ) : (Fin n → 𝓞 K) →ₗ[𝓞 K] (Fin n → K) :=
  LinearMap.pi fun i => (Algebra.linearMap (𝓞 K) K).comp (LinearMap.proj i)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


