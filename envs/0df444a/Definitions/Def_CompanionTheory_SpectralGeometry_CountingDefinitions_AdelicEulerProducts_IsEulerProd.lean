-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- name    : CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:33.25627+00:00
-- url     : https://prove2.me/theorems/359624e3-5728-4141-8eb9-2646cadf240d
-- title:
--   Is Euler Prod
-- statement:
--   Definitions and structural lemmas for Is Euler Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/CountingDefinitions/AdelicEulerProducts/IsEulerProd.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
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
namespace GlobalTheory.CompanionTheory.SW
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal
section Loc
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def IsLocR (R : Type) [CommRing R] [TopologicalSpace R] : Prop :=
  IsTopologicalRing R ∧ LocallyCompactSpace R ∧ SecondCountableTopology R ∧ T2Space R ∧
    IsArtinianRing R ∧ IsReduced R ∧ IsOpenEmbedding (Units.val : Rˣ → R) ∧
    ∃ U : Subgroup Rˣ, IsOpen (U : Set Rˣ) ∧ IsOpenEmbedding (fun u : U => ((u : Rˣ) ^ 2 : Rˣ))
variable (R : Type) [CommRing R] [Algebra F R]
def actW (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) : Fin n → Fin M → R ⊗[F] E :=
  actTup R (HA.mat R σ J h) X
def rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Fin n → Fin M → R ⊗[F] E :=
  fun a i => ∑ c, X c i * g c a
def hermScal (σ : E →ₐ[F] E) (s : R) : HermR R σ 1 :=
  ⟨fun _ _ => s ⊗ₜ[F] (1 : E), by intro a b; simp [sigR]⟩
def blockOne {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 1)) (Fin (M + 1)) K :=
  Matrix.of (Fin.cons (Fin.cons t (fun _ => 0)) (fun i => Fin.cons 0 (A i)))
def consTup {K : Type} [Zero K] [One K] {M n : ℕ} (X : Fin n → Fin M → K) : Fin (n + 1) → Fin (M + 1) → K :=
  Fin.cons (Fin.cons 1 (fun _ => 0)) (fun a => Fin.cons 0 (X a))
variable [TopologicalSpace R] [MeasurableSpace R]
def coordK {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) : Measure (R ⊗[F] E) :=
  Measure.comap (fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k)
    (Measure.pi fun _ => lam)
def coordW {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (n M : ℕ) :
    Measure (Fin n → Fin M → R ⊗[F] E) :=
  Measure.pi fun _ => Measure.pi fun _ => coordK R b lam
def coordHerm (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (n : ℕ) :
    Measure (HermR R σ n) :=
  Measure.comap (fun S : HermR R σ n =>
      ((fun i : Fin n => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin n × Fin n // p.1 < p.2} => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2)))
    ((Measure.pi fun _ => lam).prod (Measure.pi fun _ => coordK R b lam))
omit [MeasurableSpace R] in

def IsGramFib (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val {X | IsUnit (gramR R σ J X).det} ν
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m
end Loc
section Glob
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def IsStdV (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) : Prop :=
  lam.IsAddHaarMeasure ∧ lam (v.adicCompletionIntegers F : Set (Fv F v)) = 1
def IsStdInf (lam : Measure (Ainf F)) : Prop :=
  lam.IsAddHaarMeasure ∧ ∃ D : Set (Ainf F),
    IsAddFundamentalDomain ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range D lam ∧
      lam D = 1
def IsUnitProd (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0) : Prop :=
  (∀ᶠ v in Filter.cofinite, c v = 1) ∧ cinf * ∏ᶠ v, c v = 1
def thetaMeas (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin n → Fin M → E)) : Measure (Fin n → Fin M → AF F ⊗[F] E) :=
  (μ 𝓕)⁻¹ • Measure.sum fun X : S =>
    (μ.restrict 𝓕).map fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))
def intOff {d M n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (Fin n → Fin M → AF F ⊗[F] E) :=
  {X | ∀ v, v ∉ S → projV v (projFin X) ∈ latV b v}
def pureL {d M n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞)
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (intOff b S).indicator (fun Y => φinf (projInf Y) * ∏ v ∈ S, φ v (projV v (projFin Y))) X
def IsEulerProd {d M n : ℕ} (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  (∀ v, m v (latV b v) < ⊤) ∧ Summable (fun v => |(m v (latV b v)).toReal - 1|) ∧
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
        (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞),
        Measurable φinf → (∀ v, Measurable (φ v)) →
        ∫⁻ X, pureL b S φinf φ X ∂I =
          (c : ℝ≥0∞) * ((∫⁻ X, φinf X ∂minf) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v)) *
            ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal)
def SWMeas (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) : Prop :=
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf →
      (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) →
      IsEulerProd b (thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}) 1 (minf (hermOf (Ainf F) σ T hT))
        (fun v => m v (hermOf (Fv F v) σ T hT))
end Glob
end GlobalTheory.CompanionTheory.SW


