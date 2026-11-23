-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:19.217381+00:00
-- url     : https://prove2.me/theorems/bb25eb19-221c-47e6-94c6-6750862fd5a0
-- title:
--   Fib Of Tens
-- statement:
--   Definitions and structural lemmas for Fib Of Tens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibOfTens.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
def DensAll {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    Prop :=
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν
def FibOfDens : Prop :=
  ∀ (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    [T2Space V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] (μ : Measure V) (ν : Measure X),
    IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → ν.IsOpenPosMeasure →
    ∀ (f : V → Y) (ι : X → Y) (U : Set V), Continuous f → IsClosedEmbedding ι →
      (∀ v, f v ∈ Set.range ι) → IsOpen U → DensAll μ f ι ν U →
      ∃ fib : X → Measure V, IsFibreFamily μ f ι U ν Set.univ fib
def TensFacts (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : Prop :=
  LocallyCompactSpace (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧
    IsClosed (HermR R σ a : Set (Matrix (Fin a) (Fin a) (R ⊗[F] E))) ∧
    Continuous (gramR R σ J (n := a)) ∧ (∀ X, gramR R σ J (n := a) X ∈ HermR R σ a) ∧
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}
def TensAll : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  TensFacts F E σ M J a (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), TensFacts F E σ M J a (Fv F v)
def DensInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      DensAll μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {X | LinearIndependent (Ainf F ⊗[F] E) X}
def DensV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      DensAll μv (gramR (Fv F v) σ J) Subtype.val νv {X | LinearIndependent (Fv F v ⊗[F] E) X}
end PI.VolStabSW


