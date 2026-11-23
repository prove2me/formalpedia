-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_GramDensityRealCoordinates
-- name    : Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_GramDensityRealCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:50.848529+00:00
-- url     : https://prove2.me/theorems/6b2359eb-dcdc-4b26-9f4e-40cf9e487d01
-- title:
--   Gram Density Real Coordinates
-- statement:
--   Definitions and structural lemmas for Gram Density Real Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/GramDensityRealCoordinates.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.GramDensityRealCoordinates
open scoped TensorProduct ContDiff
open NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Defs
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def realCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    Fin n → Fin M → Fin d → InfinitePlace F → ℝ :=
  fun a i k w => (InfinitePlace.Completion.extensionEmbedding w
    ((Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k w)).re
def IsSmoothCompact {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) : Prop :=
  ∃ φ : (Fin n → Fin M → Fin d → InfinitePlace F → ℝ) → ℂ,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ∀ X, Φ X = φ (realCoord b X)
omit [NumberField F] in

def IsGramDensityAt (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (Φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (T : HermR R σ n) (c : ℂ) : Prop :=
  ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → ℂ), IsOpen B ∧ T ∈ B ∧
    IsContDensityOn μ (gramR R σ J)
      (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ν B Φ g ∧ g T = c
def thetaTerm (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (h : HA (AF F) σ J) (X : {X : Fin n → Fin M → E // gramE σ J X = T}) : ℂ :=
  Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (F := F) (AF F) X.1))
def theta (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (h : HA (AF F) σ J) : ℂ :=
  ∑' X, thetaTerm σ J T Φ h X
end Defs
def SiegelWeilUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (μ : Measure (HA (AF F) σ J)), IsHaarH F E σ M J μ →
  ∀ (𝓕 : Set (HA (AF F) σ J)), IsFDH F E σ M J μ 𝓕 →
    (μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤) ∧
    ∀ (n : ℕ), 2 * n < M →
    ∀ (T : Matrix (Fin n) (Fin n) E) (hT : IsHermND σ T)
      (d : ℕ) (b : Module.Basis (Fin d) F E)
      (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
      (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsSmoothCompact b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
      (∀ h, Summable (thetaTerm σ J T Φ h)) ∧
      IntegrableOn (theta σ J T Φ) 𝓕 μ ∧
      ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
      ∀ (μinf : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
        (νinf : Measure (HermR (Ainf F) σ n))
        (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
        (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n)),
        SdW F E σ M J (Ainf F) (psiInf F ψ) n μinf →
        SdHerm F E σ (Ainf F) (psiInf F ψ) n νinf →
        (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) →
        (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) →
      ∀ (cinf : ℂ) (cv : HeightOneSpectrum (𝓞 F) → ℂ),
        IsGramDensityAt (Ainf F) σ J μinf νinf Φinf (hermOf (Ainf F) σ T hT.1) cinf →
        (∀ v, IsGramDensityAt (Fv F v) σ J (μv v) (νv v) (Φv v)
          (hermOf (Fv F v) σ T hT.1) (cv v)) →
        Summable (fun v => ‖cv v - 1‖) ∧ Multipliable cv ∧
        meanC μ 𝓕 (theta σ J T Φ) = cinf * ∏' v, cv v
example {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (T : HermR R σ n) :
    IsGramDensityAt R σ J μ ν 0 T 0 :=
  ⟨Set.univ, 0, isOpen_univ, trivial, ⟨continuousOn_const, fun S _ _ => by simp⟩, rfl⟩
example {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (h : HA (AF F) σ J) (X : {X : Fin n → Fin M → E // gramE σ J X = T}) :
    thetaTerm σ J T Φ h X = Φ (h⁻¹ • ratTup (F := F) (AF F) X.1) := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.GramDensityRealCoordinates


