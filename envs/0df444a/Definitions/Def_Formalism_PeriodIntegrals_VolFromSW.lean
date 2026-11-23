-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
-- name    : Formalism_PeriodIntegrals_VolFromSW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:46.153477+00:00
-- url     : https://prove2.me/theorems/f152f47a-1fc7-4a84-8277-07777133e717
-- title:
--   Vol From SW
-- statement:
--   Definitions and structural lemmas for Vol From SW, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/VolFromSW.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolFromSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
section SW
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def thetaS {n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (S : Set (Fin n → Fin M → E))
    (h : HA (AF F) σ J) : ℂ :=
  ∑' X : S, Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) (X : Fin n → Fin M → E)))
def SWa1 : Prop :=
  AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 => μ 𝓕 < ⊤
def SWc1 : Prop :=
  ∀ (n : ℕ), n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → RapidDecay b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)
end SW
section Ext
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def ratIn (K : Subgroup (HA (AF F) σ J)) : Subgroup K :=
  ((HFinIn (AF F) σ J) ⊓ K).subgroupOf K
def IsOmT (ψ : AddChar (AF F) ℂ) {a : ℕ} (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (νX : Measure (Fin a → Fin M → AF F ⊗[F] E)) : Prop :=
  νX {X | gramR (AF F) σ J X ≠ T.map (inclR (AF F))} = 0 ∧
  AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) a) fun μinf =>
  AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) a) fun νinf =>
  AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E) =>
    ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) fun μv =>
  AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a) =>
    ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) fun νv =>
  AllSome (fun fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E) =>
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf) fun fibInf =>
  AllSome (fun fibV : ∀ v : HeightOneSpectrum (𝓞 F),
      HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E) =>
    ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) fun fibV =>
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
    (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    Integrable Φ νX ∧
    Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ T hT))) ∧
    ∫ X, Φ X ∂νX = (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ T hT))) *
      ∏' v, ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ T hT))
def IsCompatT {a : ℕ} (X0 : Fin a → Fin M → E) (μ : Measure (HA (AF F) σ J))
    (μ' : Measure (stabT (AF F) σ J X0)) (νX : Measure (Fin a → Fin M → AF F ⊗[F] E)) : Prop :=
  νX {y | ¬ ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y} = 0 ∧
  ∀ f : HA (AF F) σ J → ENNReal, Measurable f →
    ∀ s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J,
      (∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y) → s y • ratTup (AF F) X0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX
def VolStabAt {a : ℕ} (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j) : Prop :=
  AllSome (IsCharAF F) fun ψ =>
  AllSome (IsHaarH F E σ M J) fun μ =>
  AllSome (IsOmT F E σ M J ψ (gramE σ J X0) hT) fun νX =>
  AllSome (fun μ' : Measure (stabT (AF F) σ J X0) =>
    μ'.IsHaarMeasure ∧ IsCompatT F E σ M J X0 μ μ' νX) fun μ' =>
  AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
  AllSome (fun 𝓕' : Set (stabT (AF F) σ J X0) =>
    IsFundamentalDomain (ratIn F E σ M J (stabT (AF F) σ J X0)) 𝓕' μ') fun 𝓕' =>
    μ' 𝓕' = μ 𝓕
def VolStab : Prop :=
  IsHermND σ J → ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j),
    (gramE σ J X0).det ≠ 0 → VolStabAt F E σ M J X0 hT
def VolumeIsotropicTuple : Prop :=
  IsHermND σ J → ∀ (r : ℕ), 2 * (r + 1) + 1 ≤ M → ∀ (X0 : Fin (r + 1) → Fin M → E) (β : F), β ≠ 0 →
    LinearIndependent E X0 →
    (∀ i j, gramE σ J X0 i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E β else 0) →
    ∀ hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j, VolStabAt F E σ M J X0 hT
end Ext
def ForAllCM (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      P F E σ M J
def VolumesFromSW : Prop :=
  ForAllCM fun F E _ _ _ _ σ M J =>
    SWa1 F E σ M J → SWc1 F E σ M J →
      VolStab F E σ M J ∧ VolumeIsotropicTuple F E σ M J
def VolStabFromSW : Prop :=
  ForAllCM fun F E _ _ _ _ σ M J => SWa1 F E σ M J → SWc1 F E σ M J → VolStab F E σ M J
def VolumeDegenerateFromSiegelWeil : Prop :=
  ForAllCM fun F E _ _ _ _ σ M J => SWa1 F E σ M J → SWc1 F E σ M J → VolumeIsotropicTuple F E σ M J
end PI.VolFromSW


