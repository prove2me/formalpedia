-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:18.892612+00:00
-- url     : https://prove2.me/theorems/1759ebdf-67cb-4401-8a44-70bf4ef65e73
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OmFibreUniq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OmFibreUniq.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq
open scoped TensorProduct Classical
def SdEx : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a : ℕ), StdHyp σ J ψ →
    (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧
      (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν)
def FibEx : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (a : ℕ), IsCMExt F E σ → IsHermND σ J →
    ∀ (μ : Measure (TupV (E := E) v n a)) (ν : Measure (HermR (Fv F v) σ a)),
      μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ∃ fib, IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) ν
        Set.univ fib
def FibUniq : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
    (μ : Measure (TupV (E := E) v n a)) (ν : Measure (HermR (Fv F v) σ a)),
      ν.IsAddHaarMeasure → ∀ fib fib',
      IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) ν
        Set.univ fib →
      IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) ν
        Set.univ fib' → fib = fib'
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
end
end PI.OmFibreUniq.W


