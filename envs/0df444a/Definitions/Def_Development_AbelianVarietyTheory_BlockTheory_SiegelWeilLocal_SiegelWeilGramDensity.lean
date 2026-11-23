-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_SiegelWeilGramDensity
-- name    : Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_SiegelWeilGramDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:36.5876+00:00
-- url     : https://prove2.me/theorems/ad3adc5f-1ac4-4b57-bd4c-d0cb46ce0139
-- title:
--   Siegel Weil Gram Density
-- statement:
--   Definitions and structural lemmas for Siegel Weil Gram Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/SiegelWeilGramDensity.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain MeasureTheory Topology
open HeckeCharacterZeroLocus.SiegelWeilU
namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelWeilGramDensity
section Defs
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def IsSchwartzInf {M n : ℕ} (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) : Prop :=
  ∃ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)),
    Continuous e ∧ Continuous e.symm ∧
      ∃ f : SchwartzMap (Fin N → ℝ) ℂ, ∀ X, Φinf X = f (e X)
def hermInv (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (n : ℕ) : Set (HermR R σ n) :=
  {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
def IsGramDensity (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (dX : Measure (Fin n → Fin M → R ⊗[F] E)) (dS : Measure (HermR R σ n))
    (Φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (g : HermR R σ n → ℂ) : Prop :=
  IsContDensityOn dX (gramR R σ J)
    (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))) dS (hermInv R σ n) Φ g
def gramFibre (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) : Set (Fin n → Fin M → E) :=
  {X | gramE σ J X = T}
def thetaTerm (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (h : HA (AF F) σ J) (X : Fin n → Fin M → E) : ℂ :=
  Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) X))
def ThetaAbsConv (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (S : Set (Fin n → Fin M → E)) : Prop :=
  (∀ h, Summable fun X : S => ‖thetaTerm σ J Φ h X‖) ∧
    (∫⁻ h in 𝓕, ∑' X : S, ‖thetaTerm σ J Φ h X‖ₑ ∂μ) < ⊤ ∧
    IntegrableOn (thetaS F E σ M J Φ S) 𝓕 μ
end Defs
def VolumeFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      AllSome (fun μ : Measure (HA (AF F) σ J) => IsHaarH F E σ M J μ) fun μ =>
        AllSome (fun 𝓕 : Set (HA (AF F) σ J) => IsFDH F E σ M J μ 𝓕) fun 𝓕 =>
          0 < μ 𝓕 ∧ μ 𝓕 < ⊤
def SiegelFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ), 1 ≤ n → 2 * n < M →
    ∀ (T : Matrix (Fin n) (Fin n) E) (hT : IsHermND σ T),
    ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (b : Module.Basis (Fin 2) F E)
      (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
      (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsProdInfFin Φ Φinf Φf → IsSchwartzInf Φinf → IsPureFin b Φf Φv →
      AllSome (fun μ : Measure (HA (AF F) σ J) => IsHaarH F E σ M J μ) fun μ =>
      AllSome (fun 𝓕 : Set (HA (AF F) σ J) => IsFDH F E σ M J μ 𝓕) fun 𝓕 =>
      ThetaAbsConv σ J μ 𝓕 Φ (gramFibre σ J T) ∧
      AllSome (fun dX : Measure (Fin n → Fin M → Ainf F ⊗[F] E) =>
          SdW F E σ M J (Ainf F) (psiInf F ψ) n dX) fun dXinf =>
      AllSome (fun dS : Measure (HermR (Ainf F) σ n) =>
          SdHerm F E σ (Ainf F) (psiInf F ψ) n dS) fun dSinf =>
      AllSome (fun dX : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
          ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (dX v)) fun dXv =>
      AllSome (fun dS : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
          ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (dS v)) fun dSv =>
      AllSome (fun g : HermR (Ainf F) σ n → ℂ =>
          IsGramDensity (Ainf F) σ J dXinf dSinf Φinf g) fun ginf =>
      AllSome (fun g : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ =>
          ∀ v, IsGramDensity (Fv F v) σ J (dXv v) (dSv v) (Φv v) (g v)) fun gv =>
        Summable (fun v => ‖gv v (hermOf (Fv F v) σ T hT.1) - 1‖) ∧
        Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT.1)) ∧
        meanC μ 𝓕 (thetaS F E σ M J Φ (gramFibre σ J T)) =
          ginf (hermOf (Ainf F) σ T hT.1) * ∏' v, gv v (hermOf (Fv F v) σ T hT.1)
def SiegelWeilConvergent : Prop := VolumeFinite ∧ SiegelFormula
example {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) :
    IsHermND σ (1 : Matrix (Fin M) (Fin M) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]
example (M n r : ℕ) (h1 : 1 ≤ n) (h : 2 * n < M) (hr : 2 * r ≤ M) : n + 2 ≤ M ∧ n + r < M := by
  omega
end GlobalTheory.IndefiniteRowSideFullHecke.SiegelWeilGramDensity


