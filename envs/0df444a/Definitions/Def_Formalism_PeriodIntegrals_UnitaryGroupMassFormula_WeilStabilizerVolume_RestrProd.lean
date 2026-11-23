-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:17.103349+00:00
-- url     : https://prove2.me/theorems/a9e5546f-0ec4-4683-95c6-31bb4f09d735
-- title:
--   Restr Prod
-- statement:
--   Definitions and structural lemmas for Restr Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProd.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
def LocEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    ∃ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
      (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E))
      (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
      SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf ∧ SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf ∧
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) ∧
      (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) ∧
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf ∧
      ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)
def SdUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μ1 μ2, SdW F E σ M J (Ainf F) (psiInf F ψ) a μ1 → SdW F E σ M J (Ainf F) (psiInf F ψ) a μ2 →
      μ1 = μ2) ∧
    (∀ ν1 ν2, SdHerm F E σ (Ainf F) (psiInf F ψ) a ν1 → SdHerm F E σ (Ainf F) (psiInf F ψ) a ν2 →
      ν1 = ν2) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ μ1 μ2, SdW F E σ M J (Fv F v) (psiV F ψ v) a μ1 → SdW F E σ M J (Fv F v) (psiV F ψ v) a μ2 →
        μ1 = μ2) ∧
      (∀ ν1 ν2, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν1 →
        SdHerm F E σ (Fv F v) (psiV F ψ v) a ν2 → ν1 = ν2)
def FibPin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
      ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      ∀ fib1 fib2 : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib1 →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib2 →
      ∀ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf → HasCompactSupport Φinf →
        ∫ X, Φinf X ∂(fib1 (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fib2 (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
      ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      ∀ fib1 fib2 : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib1 →
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib2 →
      ∀ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv →
        ∫ X, Φv X ∂(fib1 (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv X ∂(fib2 (hermOf (Fv F v) σ (gramE σ J X0) hT))
def MultFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))
def RestrProd : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    ∃ νX : Measure (Fin a → Fin M → AF F ⊗[F] E),
      νX {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} = 0 ∧
      ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
        (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
        (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
        Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
        Integrable Φ νX ∧
        ∫ X, Φ X ∂νX = (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) *
          ∏' v, ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
end PI.VolStabW


