-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:08.555229+00:00
-- url     : https://prove2.me/theorems/766d80a4-0e73-4121-b986-af069d807650
-- title:
--   Fib Inf Ex
-- statement:
--   Definitions and structural lemmas for Fib Inf Ex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibInfEx.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
def InCtx (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (X0 : Fin a → Fin M → E)
    (_hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    SWa1 F E σ M J → SWc1 F E σ M J → ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M →
    ∀ (X0 : Fin a → Fin M → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j),
    (gramE σ J X0).det ≠ 0 → P F E σ M J a X0 hT
def IsAdm (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {M a : ℕ}
    (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) : Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf ∧ HasCompactSupport Φinf ∧ IsPureFin b Φf Φv ∧ IsProdInfFin Φ Φinf Φf
def ExChar : Prop := InCtx fun F E _ _ _ _ _ _σ _M _J _a _X0 _hT => ∃ ψ, IsCharAF F ψ
def ExOmT : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∃ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX
def ExStab : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∃ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure ∧ IsCompatT F E σ M J X0 μ μ' νX
def ExFDStab : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 _hT =>
  ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure →
    ∃ 𝓕' : Set (stabT (AF F) σ J X0),
      IsFundamentalDomain (ratIn F E σ M J (stabT (AF F) σ J X0)) 𝓕' μ'
def SWeqOm : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ 𝓕, IsFDH F E σ M J μ 𝓕 →
    ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ Φ, IsAdm F E Φ →
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = gramE σ J X0}) = ∫ X, Φ X ∂νX
def Unfold : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ 𝓕, IsFDH F E σ M J μ 𝓕 →
    ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
    ∀ 𝓕' : Set (stabT (AF F) σ J X0),
      IsFundamentalDomain (ratIn F E σ M J (stabT (AF F) σ J X0)) 𝓕' μ' →
    ∀ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) → IsAdm F E (fun X => (φ X : ℂ)) →
      ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ ≠ 0 →
      μ' 𝓕' ≠ ⊤ ∧
        ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ =
          (μ' 𝓕').toReal • ∫ X, (φ X : ℂ) ∂νX
def PosTest : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
    ∃ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) ∧ IsAdm F E (fun X => (φ X : ℂ)) ∧
      ∫ X, (φ X : ℂ) ∂νX ≠ 0
def Witt : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ X : Fin a → Fin M → E, gramE σ J X = gramE σ J X0 →
    ∃ g ∈ Formalism.UG.UJ (σ : E →+* E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i) = X i
def FinTheta : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ, IsAdm F E Φ → ∀ h : HA (AF F) σ J,
    {X : Fin a → Fin M → E |
      Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) X)) ≠ 0}.Finite
def Unimod : Prop := InCtx fun F E _ _ _ _ _ σ M J _a _X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → μ.IsMulRightInvariant
def UnimodStab : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
      μ'.IsMulRightInvariant
def FibInfEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∃ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf
def FibVEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∃ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV
def DensFibInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (ginf : HermR (Ainf F) σ a → ℂ),
      Continuous Φinf → HasCompactSupport Φinf →
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)).det} Φinf ginf →
      ginf (hermOf (Ainf F) σ (gramE σ J X0) hT) =
        ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))
def DensFibV : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∀ (Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (gv : HermR (Fv F v) σ a → ℂ), IsSB Φv →
      IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
        {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det} Φv gv →
      gv (hermOf (Fv F v) σ (gramE σ J X0) hT) =
        ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT))
end PI.VolStabSW


