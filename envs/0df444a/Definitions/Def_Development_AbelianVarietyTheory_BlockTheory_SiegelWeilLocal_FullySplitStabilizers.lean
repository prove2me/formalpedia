-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_FullySplitStabilizers
-- name    : Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_FullySplitStabilizers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:15.489175+00:00
-- url     : https://prove2.me/theorems/3f9e431d-742f-41a4-a2f2-9df19997e885
-- title:
--   Fully Split Stabilizers
-- statement:
--   Definitions and structural lemmas for Fully Split Stabilizers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/FullySplitStabilizers.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct ENNReal Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg
namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianGramMatrices
section Gram
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E)
theorem tF_herm (r : ℕ) (T : F) (a b : Fin (r + 1)) :
    σ (TF r (algebraMap F E T) b a) = TF r (algebraMap F E T) a b := by
  unfold TF
  by_cases h : a = b
  · subst h
    by_cases h' : a = Fin.last r <;> simp [h']
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
def gramTwo {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin ((r + 1) + (r + 1))) (Fin ((r + 1) + (r + 1))) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (TF r (algebraMap F E T)) Z (cT (σ : E →+* E) Z) (TF r (algebraMap F E T')))
theorem gramTwo_herm (hσ : ∀ x, σ (σ x) = x) {r : ℕ} (T T' : F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin ((r + 1) + (r + 1))) :
    σ (gramTwo σ T T' Z b a) = gramTwo σ T T' Z a b := by
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  simp only [gramTwo, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b
  · exact tF_herm σ r T a b
  · exact hσ _
  · rfl
  · exact tF_herm σ r T' a b
def hermF (r : ℕ) (T : F) : HermR R σ (r + 1) :=
  hermOf R σ (TF r (algebraMap F E T)) (tF_herm σ r T)
def hermTwo (hσ : ∀ x, σ (σ x) = x) {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    HermR R σ ((r + 1) + (r + 1)) :=
  hermOf R σ (gramTwo σ T T' Z) (gramTwo_herm σ hσ T T' Z)
def IsGramFibre [TopologicalSpace R] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : ℕ)
    (μ : Measure (Fin a → Fin n → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (fib : HermR R σ a → Measure (Fin a → Fin n → R ⊗[F] E)) : Prop :=
  IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ fib
end Gram
theorem invol_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]
section Local
variable {F : Type} (E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
def intV : Subring (Fv F v ⊗[F] E) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}
variable {E}
def latAt {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (intV E v) (Fin n → Fv F v ⊗[F] E) :=
  Submodule.span (intV E v) {y | ∃ x ∈ Λ, y = fun i => (1 : Fv F v) ⊗ₜ[F] x i}
def PrimAt {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) {ι : Type}
    (X : ι → Fin n → Fv F v ⊗[F] E) : Prop :=
  ∃ (κ : Type) (Y : κ → Fin n → Fv F v ⊗[F] E),
    LinearIndependent (intV E v) (Sum.elim X Y) ∧
      Submodule.span (intV E v) (Set.range (Sum.elim X Y)) = latAt v Λ
def IsDiffGen (δ : v.adicCompletionIntegers F) : Prop :=
  Ideal.span {δ} = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
variable (δ : v.adicCompletionIntegers F)
def scal (r : ℕ) (b : Fin (r + 1)) : Fv F v := ((δ : Fv F v)⁻¹) ^ (r - (b : ℕ))
def locFr {n r : ℕ} (P : Fin (r + 1) → Fin n → Fv F v ⊗[F] E) :
    Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => scal v δ r b • P b
def locZ {r : ℕ} (Z : Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E) :
    Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E :=
  fun a b => (scal v δ r a * scal v δ r b) • Z a b
open scoped Classical in

def levAt (g₁ g₂ : ℕ) : Option ℕ :=
  if (g₁ : 𝓞 F) ∈ v.asIdeal then some g₁ else if (g₂ : 𝓞 F) ∈ v.asIdeal then some g₂ else none
variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
  (g₁ g₂ : ℕ) (r : ℕ) (T T' : F)
def Om : Set ((Fin (r + 1) → Fin n → Fv F v ⊗[F] E) × (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) :=
  {p | LinearIndependent (Fv F v ⊗[F] E) p.1 ∧ gramR (Fv F v) σ J p.1 = (hermF (Fv F v) σ r T).1 ∧
    LinearIndependent (Fv F v ⊗[F] E) p.2 ∧ gramR (Fv F v) σ J p.2 = (hermF (Fv F v) σ r T').1 ∧
    PrimAt v Λ (locFr v δ p.1) ∧ PrimAt v Λ (locFr v δ p.2) ∧
    ∀ q, levAt v g₁ g₂ = some q →
      ∀ b, ((q : Fv F v)⁻¹) • (locFr v δ p.2 b - locFr v δ p.1 b) ∈ latAt v Λ}
def OmGen : Set (Fin ((r + 1) + (r + 1)) → Fin n → Fv F v ⊗[F] E) :=
  {X | ((fun a => X (Fin.castAdd (r + 1) a)), (fun b => X (Fin.natAdd (r + 1) b))) ∈
      Om v δ σ J Λ g₁ g₂ r T T' ∧
    (levAt v g₁ g₂ = none →
      PrimAt v Λ (Sum.elim (locFr v δ fun a => X (Fin.castAdd (r + 1) a))
        (locFr v δ fun b => X (Fin.natAdd (r + 1) b)))) ∧
    ∀ q, levAt v g₁ g₂ = some q →
      PrimAt v Λ (Sum.elim (locFr v δ fun a => X (Fin.castAdd (r + 1) a))
        (fun b => ((q : Fv F v)⁻¹) • (locFr v δ (fun b => X (Fin.natAdd (r + 1) b)) b -
          locFr v δ (fun a => X (Fin.castAdd (r + 1) a)) b)))}
def yZero (q : ℕ) (Z : Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E) :
    Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E :=
  fun a b => ((q : Fv F v)⁻¹) • (locZ v δ Z a b - (hermF (Fv F v) σ r T).1 a b)
def ZZ : Set (Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E) :=
  {Z | (levAt v g₁ g₂ = none → ∀ a b, locZ v δ Z a b ∈ intV E v) ∧
    ∀ q, levAt v g₁ g₂ = some q → ∀ a b, yZero v δ σ r T q Z a b ∈ intV E v ∧
      ((q : Fv F v)⁻¹) • (yZero v δ σ r T q Z a b + sigR (Fv F v) σ (yZero v δ σ r T q Z b a) -
        ((q : Fv F v)⁻¹) • ((hermF (Fv F v) σ r T').1 a b - (hermF (Fv F v) σ r T).1 a b)) ∈
          intV E v}
end Local
section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
def stabK (Λ : Submodule (𝓞 E) (Fin n → E)) : Set (HA (Af F) σ J) :=
  {h | ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E), y ∈ latAt v Λ ↔
    (((HA.mat (Af F) σ J h : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map
      (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))).mulVec y ∈ latAt v Λ}
def HasParts (h : HA (AF F) σ J) (x : HA (Ainf F) σ J) (y : HA (Af F) σ J) : Prop :=
  ((HA.mat (AF F) σ J h : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) =
    ((HA.mat (Ainf F) σ J x : GL (Fin n) (Ainf F ⊗[F] E)) : Matrix (Fin n) (Fin n) _) ∧
  ((HA.mat (AF F) σ J h : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) =
    ((HA.mat (Af F) σ J y : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) _)
def IsProdHaar (μi : Measure (HA (Ainf F) σ J)) (μf : Measure (HA (Af F) σ J))
    (μ : Measure (HA (AF F) σ J)) : Prop :=
  μ.IsHaarMeasure ∧ ∀ (A : Set (HA (Ainf F) σ J)) (B : Set (HA (Af F) σ J)),
    MeasurableSet A → MeasurableSet B →
      μ {h | ∃ x ∈ A, ∃ y ∈ B, HasParts σ J h x y} = μi A * μf B
def IsRho {a : ℕ} (μi : Measure (HA (Ainf F) σ J)) (S : HermR (Ainf F) σ a)
    (ω : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (ρ : ℝ) : Prop :=
  AllSome (fun X₀ : Fin a → Fin n → Ainf F ⊗[F] E =>
      LinearIndependent (Ainf F ⊗[F] E) X₀ ∧ gramR (Ainf F) σ J X₀ = S.1) fun X₀ =>
    ∀ Φ : (Fin a → Fin n → Ainf F ⊗[F] E) → ℝ≥0∞, Measurable Φ →
      ∫⁻ X, Φ X ∂ω = ENNReal.ofReal ρ * ∫⁻ g, Φ (g • X₀) ∂μi
def HasSig (p : ℕ) : Prop :=
  ∀ τ : E →+* ℂ, ∃ P : Matrix (Fin n) (Fin n) ℂ,
    P.conjTranspose * J.map τ * P = Matrix.diagonal fun i : Fin n => if (i : ℕ) < p then 1 else -1
def SplitsFully (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E
def OnFinFibres (ψ : AddChar (AF F) ℂ) (a : ℕ)
    (Q : (∀ v : HeightOneSpectrum (𝓞 F),
      HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E)) → Prop) : Prop :=
  AllSome (fun μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin n → Fv F v ⊗[F] E) =>
    ∀ v, SdW F E σ n J (Fv F v) (psiV F ψ v) a (μ v)) fun μ =>
  AllSome (fun ν : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a) =>
    ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (ν v)) fun ν =>
  AllSome (fun fib : ∀ v : HeightOneSpectrum (𝓞 F),
      HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E) =>
    ∀ v, IsGramFibre (Fv F v) σ J a (μ v) (ν v) (fib v)) Q
def OnInfFibres (ψ : AddChar (AF F) ℂ) (a : ℕ)
    (Q : (HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)) → Prop) : Prop :=
  AllSome (SdW F E σ n J (Ainf F) (psiInf F ψ) a) fun μ =>
  AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) a) fun ν =>
  AllSome (IsGramFibre (Ainf F) σ J a μ ν) Q
end Global
def MassFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ), differentIdeal (𝓞 F) (𝓞 E) = ⊤ →
  ∀ (k r : ℕ), 3 ≤ k →
  ∀ (J : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E), IsHermND σ J → HasSig J (k + r) →
  ∀ (Λ : Submodule (𝓞 E) (Fin (k + 2 * r + 1) → E)), GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ →
  ∀ (g₁ g₂ : ℕ), g₁ ≠ g₂ → SplitsFully E g₁ → SplitsFully E g₂ →
  ∀ (T T' : 𝓞 F), GlobalTheory.SgGlob.TotPos (algebraMap F E (T : F)) →
    GlobalTheory.SgGlob.TotPos (algebraMap F E (T' : F)) →
    ((g₁ * g₂ : ℕ) : 𝓞 F) ^ 2 ∣ T - 1 → ((g₁ * g₂ : ℕ) : 𝓞 F) ^ 2 ∣ T' - 1 →
  AllSome (fun δ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F =>
    ∀ v, IsDiffGen v (δ v)) fun δ =>
  AllSome (fun μi : Measure (HA (Ainf F) σ J) => μi.IsHaarMeasure) fun μi =>
  AllSome (fun μf : Measure (HA (Af F) σ J) => μf.IsHaarMeasure) fun μf =>
  AllSome (IsProdHaar σ J μi μf) fun μ =>
  AllSome (IsFDH F E σ (k + 2 * r + 1) J μ) fun 𝓕 =>
  AllSome (IsCharAF F) fun ψ =>
  OnInfFibres σ J ψ ((r + 1) + (r + 1)) fun ωi =>
  OnFinFibres σ J ψ (r + 1) fun ω₁ =>
  OnFinFibres σ J ψ ((r + 1) + (r + 1)) fun ω₂ =>
  AllSome (fun dZ : ∀ v : HeightOneSpectrum (𝓞 F),
      Measure (Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E) =>
    ∀ v, SdW F E σ (r + 1) 1 (Fv F v) (psiV F ψ v) (r + 1) (dZ v)) fun dZ =>
  let hσ : ∀ x, σ (σ x) = x := invol_of_cm hCM
  let t : E := algebraMap F E (T : F)
  let t' : E := algebraMap F E (T' : F)
  let G : Matrix (Fin (r + 1)) (Fin (r + 1)) E → E := fun Z => Gq (σ : E →+* E) t t' Z
  let bigM : HeightOneSpectrum (𝓞 F) → ℝ≥0∞ := fun v =>
    ((ω₁ v (hermF (Fv F v) σ r (T : F))).prod (ω₁ v (hermF (Fv F v) σ r (T' : F))))
      (Om v (δ v) σ J Λ g₁ g₂ r (T : F) (T' : F))
  let volZ : HeightOneSpectrum (𝓞 F) → ℝ≥0∞ := fun v =>
    dZ v (ZZ v (δ v) σ g₁ g₂ r (T : F) (T' : F))
  let m : Matrix (Fin (r + 1)) (Fin (r + 1)) E → HeightOneSpectrum (𝓞 F) → ℝ≥0∞ := fun Z v =>
    ω₂ v (hermTwo (Fv F v) σ hσ (T : F) (T' : F) Z) (OmGen v (δ v) σ J Λ g₁ g₂ r (T : F) (T' : F))
  let dens : Matrix (Fin (r + 1)) (Fin (r + 1)) E → HeightOneSpectrum (𝓞 F) → ℝ := fun Z v =>
    (m Z v).toReal * (volZ v).toReal / (bigM v).toReal
  let admitted : Matrix (Fin (r + 1)) (Fin (r + 1)) E → Prop := fun Z =>
    GlobalTheory.SgGlob.TotPos (G Z) ∧
      ∀ v, (fun a b => (1 : Fv F v) ⊗ₜ[F] Z a b) ∈ ZZ v (δ v) σ g₁ g₂ r (T : F) (T' : F)
  μ 𝓕 ≠ ⊤ ∧ μf (stabK σ J Λ) ≠ 0 ∧ μf (stabK σ J Λ) ≠ ⊤ ∧
  (∀ v, bigM v ≠ 0 ∧ bigM v ≠ ⊤ ∧ volZ v ≠ 0 ∧ volZ v ≠ ⊤) ∧
  Summable (fun v => |(bigM v).toReal / (volZ v).toReal - 1|) ∧
  ∃ C : ℝ, 0 < C ∧
    (∀ Z, GlobalTheory.SgGlob.TotPos (G Z) →
      IsRho σ J μi (hermTwo (Ainf F) σ hσ (T : F) (T' : F) Z)
        (ωi (hermTwo (Ainf F) σ hσ (T : F) (T' : F) Z))
        (C * GlobalTheory.SgGlob.normInf (G Z) ^ (k - 1))) ∧
    ∀ Z, G Z ≠ 0 →
      (¬ admitted Z → GlobalTheory.SgGlob.Mass (σ : E →+* E) J t t' (g₁ * g₂) Z = 0) ∧
      (admitted Z →
        (∀ v, m Z v ≠ ⊤) ∧
        Summable (fun v => |(m Z v).toReal - 1|) ∧ Summable (fun v => |dens Z v - 1|) ∧
        GlobalTheory.SgGlob.Mass (σ : E →+* E) J t t' (g₁ * g₂) Z =
          ENNReal.ofReal ((μ 𝓕).toReal * (C * GlobalTheory.SgGlob.normInf (G Z) ^ (k - 1)) *
            (∏' v, (m Z v).toReal) / (μf (stabK σ J Λ)).toReal) ∧
        GlobalTheory.SgGlob.Mass (σ : E →+* E) J t t' (g₁ * g₂) Z =
          ENNReal.ofReal
            (((μ 𝓕).toReal * C * (∏' v, (bigM v).toReal / (volZ v).toReal) /
                (μf (stabK σ J Λ)).toReal) *
              GlobalTheory.SgGlob.normInf (G Z) ^ (k - 1) * ∏' v, dens Z v))
example {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ} (T T' : F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    gramTwo σ T T' Z (Fin.castAdd (r + 1) a) (Fin.natAdd (r + 1) b) = Z a b := by
  simp only [gramTwo, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂]
end GlobalTheory.IndefiniteRowSideFullHecke.HermitianGramMatrices


