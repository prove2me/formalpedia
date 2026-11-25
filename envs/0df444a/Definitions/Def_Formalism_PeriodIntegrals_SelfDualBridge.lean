-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SelfDualBridge
-- name    : Formalism_PeriodIntegrals_SelfDualBridge
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T07:36:53.000052+00:00
-- url     : https://prove2.me/theorems/b203d8e8-e3ae-4990-bbab-28a526b08cf9
-- title:
--   Self Dual Bridge
-- statement:
--   Definitions and structural lemmas for Self Dual Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SelfDualBridge.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.SelfDualBridge
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical
def SelfDualHaarExists : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [T2Space K],
    ¬ DiscreteTopology K →
  ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
    [IsModuleTopology K V] [MeasurableSpace V] [BorelSpace V]
    (χ : AddChar K ℂ), Continuous χ → (∀ x, ‖χ x‖ = 1) → (∃ x, χ x ≠ 1) →
    ∀ B : V →ₗ[K] V →ₗ[K] K, (∀ x, (∀ y, B x y = 0) → x = 0) →
      ∃ μ : Measure V, SelfDual μ (fun x y => χ (B x y))
section Meas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))
def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))
def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ
def SdExists (a : ℕ) (ι : Type) [Fintype ι] : Prop :=
  StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) ∧
  ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))
end Meas
end PI.SelfDualBridge


