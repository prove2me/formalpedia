-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:22:55.924919+00:00
-- url     : https://prove2.me/theorems/1ac38d0c-a136-4a7b-8315-f56ff3b381f8
-- title:
--   Mean Val
-- statement:
--   Definitions and structural lemmas for Mean Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/BinaryMassMeans/MeanVal.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix Classical
namespace PositivityTheory.Rg.Mass
def Aniso {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  ∀ x : Fin M → E, hE σ J x x = 0 → x = 0
def E1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → Aniso σ J →
  ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT
def Equi : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
  ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
  ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (ι → Ainf F) → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ), Continuous φ → HasCompactSupport φ →
    (∀ v ∈ S, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) →
    Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) *
        ∑' x : {x : ι → F // ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F},
          φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i)) * ∏ v ∈ S, ψ v fun i => algebraMap F (Fv F v) (x.1 i))
      (𝓝[>] 0) (𝓝 ((∫ y, φ y ∂(Measure.pi fun _ => li)) * ∏ v ∈ S, ∫ y, ψ v y ∂(Measure.pi fun _ => lam v)))
def CountBd : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
  ∀ (K : Set (Ainf F)), IsCompact K → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
    {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ θ ε * algebraMap F (Ainf F) x ∈ K}.Finite ∧
    ε ^ Module.finrank ℚ F * ({x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ θ ε * algebraMap F (Ainf F) x ∈ K}.ncard : ℝ) ≤
      C / (Ideal.absNorm I : ℝ)
def MeanVal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
  ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (C : ℝ),
    Continuous G → HasCompactSupport G → (∀ y, 0 ≤ G y) → (∀ v y, 0 ≤ g v y) →
    (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    (∀ v, v ∉ S → ContinuousOn (g v) {0}ᶜ ∧ (∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0) ∧
      (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧
      (∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ∧ ∫ s, g v s ∂(lam v) = 1) →
    Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ Module.finrank ℚ F) *
        ∑' β : {β : F // β ≠ 0}, ENNReal.ofReal (G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))))
def ForBin (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 2) (Fin 2) E) (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 2) (Fin 2) E) (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
    IsCMExt F E σ → IsHermND σ J → Aniso σ J → IsStdInf li → (∀ v, IsStdV v (lam v)) → IsHaarH F E σ 2 J μ → IsFDH F E σ 2 J μ 𝓕 →
    IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
    (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 2) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) →
    P F E σ J d b li lam μ 𝓕 mi m
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {J : Matrix (Fin 2) (Fin 2) E} {d : ℕ}
def sph (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (β : F) : Set (Fin 1 → Fin 2 → E) :=
  {X | gramE σ J X = fun _ _ => algebraMap F E β}
def EP (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)) (β : F) (c : ℝ≥0) : Prop :=
  IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J β)) c (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β))
def IsTest (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E)) : Prop :=
  Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧ tsupport φ ⊆ {X | IsUnit (gramR (Ainf F) σ J X).det} ∧
    (∀ v ∈ S, IsCompact (A v) ∧ IsOpen (A v) ∧ A v ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det}) ∧ ∀ v, v ∉ S → A v = latV b v
def dil (θ : ℝ →+* Ainf F) (ε : ℝ) (X : Fin 1 → Fin 2 → Ainf F ⊗[F] E) : Fin 1 → Fin 2 → Ainf F ⊗[F] E :=
  fun a i => (θ ε ⊗ₜ[F] (1 : E)) * X a i
def vol (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E)) : ℝ≥0∞ :=
  (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 2 (A v)
end
def CoCpt : Prop := ForBin fun F _ _ _ _ _ _ σ J _ _ _ _ μ 𝓕 _ _ =>
  (∃ C : Set (HA (AF F) σ J), IsCompact C ∧ ∀ h, ∃ γ : HFinIn (AF F) σ J, ∃ c ∈ C, h = γ • c) ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤
def LocMass : Prop := ForBin fun F _ _ _ _ _ _ σ _ _ b _ _ _ _ _ m => ∃ C : ℝ, ∀ᶠ v in cofinite,
  (∀ s, s ∉ v.adicCompletionIntegers F → s ≠ 0 → m v (hermScal (Fv F v) σ s) (latV b v) = 0) ∧
  (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 →
    |(m v (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧
  ∀ s : Fv F v, Valued.v s = 1 → |(m v (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2
def Prop1 : Prop := ForBin fun F _ _ _ _ _ _ _ _ _ b _ _ μ 𝓕 mi m => ∀ β : F, β ≠ 0 → ∃ c, EP b μ 𝓕 mi m β c
def Simil : Prop := ForBin fun F _ _ _ _ _ _ σ J _ b _ _ μ 𝓕 mi m => ∀ β β' : F, β ≠ 0 → β' ≠ 0 →
  (sph σ J β).Nonempty → (sph σ J β').Nonempty → ∀ c, EP b μ 𝓕 mi m β c → EP b μ 𝓕 mi m β' c
def Hasse : Prop := ForBin fun F _ _ _ _ _ _ σ J _ _ _ _ _ _ mi _ => ∀ β : F, β ≠ 0 →
  mi (hermScal (Ainf F) σ (algebraMap F _ β)) ≠ 0 → (sph σ J β).Nonempty
def TestEx : Prop := ForBin fun F _ _ _ _ _ _ σ J _ b li lam _ _ _ _ => ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
  ∃ φ A, IsTest σ J b S φ A ∧ vol b li lam S φ A ≠ 0 ∧ vol b li lam S φ A ≠ ⊤
def LSide : Prop := ForBin fun F E _ _ _ _ _ σ J _ b li lam μ 𝓕 _ _ => ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ S φ A,
  IsTest σ J b S φ A → Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) *
      ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X)))
        ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0})) (𝓝[>] 0) (𝓝 (vol b li lam S φ A))
def RSide : Prop := ForBin fun F _ _ _ _ _ _ σ J _ b li lam _ _ mi m => ∀ θ : ℝ →+* Ainf F, Continuous θ →
  ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ φ A, IsTest σ J b S φ A →
    Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) * ∑' β : {β : F // β ≠ 0},
      (∫⁻ X, ENNReal.ofReal (φ (dil θ ε X)) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))) *
        ENNReal.ofReal (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β.1)) (A v)).toReal)) (𝓝[>] 0) (𝓝 (vol b li lam S φ A))
def Cnt : Prop := ForBin fun F _ _ _ _ _ _ _ _ _ b _ _ μ 𝓕 mi m => ∀ κ : ℝ≥0, (∀ β : F, β ≠ 0 → EP b μ 𝓕 mi m β κ) → κ = 1
end PositivityTheory.Rg.Mass
end


