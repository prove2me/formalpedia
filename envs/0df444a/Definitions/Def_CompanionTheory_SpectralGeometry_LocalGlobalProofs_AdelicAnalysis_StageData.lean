-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:24.024868+00:00
-- url     : https://prove2.me/theorems/c1ee0b56-071f-45de-ba42-c36c140307e8
-- title:
--   Stage Data
-- statement:
--   Definitions and structural lemmas for Stage Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/StageData.lean

import Mathlib
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
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
def vec {K : Type} [Zero K] {M n : ℕ} (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 1) → K :=
  Fin.cons (Fin.cons α (fun _ => 0)) (fun j => Fin.cons (c j) (X j))
def scl {K : Type} [Mul K] {N n : ℕ} (u : K) (y : Fin n → Fin N → K) : Fin n → Fin N → K :=
  fun a i => y a i * u
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
def s0 {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S 0 0)
def cvec {n : ℕ} (t : F) (a : R → Rˣ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :
    Fin n → R ⊗[F] E :=
  fun j => ((((a (s0 R S))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * S 0 j.succ
def schurM (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => S i.succ j.succ -
    sigR R σ (cvec R t a S i) * inclR R (algebraMap F E t) * cvec R t a S j
open Classical in

def schur (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1)) : HermR R σ n :=
  if h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n then ⟨_, h⟩ else 0
def Bset (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (B₀ : Set R) : Set (HermR R σ (n + 1)) :=
  {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ ∧
    IsUnit (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
end Alg
section Meas
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
  (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
  (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
  (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
  (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
def fibS (S : HermR R σ (n + 1)) : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  (Bset R σ t a B₀).indicator (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2))) S
def Pint (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ≥0∞ :=
  ∫⁻ y₀, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))
def Preal (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ :=
  ∫ y₀, ∫ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))
def sTil (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : HA R σ (blockOne (algebraMap F E t) J) :=
  s (scl ((((a (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) y)
def chi {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : ℝ≥0∞ :=
  ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
    φ (Fin.cons (y 0) (actW R σ (blockOne (algebraMap F E t) J) (sTil σ J t s a y)
      (fun j => Fin.cons (c j) (X j)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam)
def Uset (B₀ : Set R) (a : R → Rˣ) : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' Bset R σ t a B₀)
def Unt (R : Type) [CommRing R] [Algebra F R] (n : ℕ) : Set (HermR R σ n) :=
  {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
def Mid {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n,
    Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
    ∂(Measure.pi fun _ => coordK R b lam) ∂lam
end Meas
section Data
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
structure StageData (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ)
    {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0) : Prop where
  hCM : IsCMExt F E σ
  hJ : IsHermND σ J
  ht : t ≠ 0
  hR : IsLocR R
  hlam : lam.IsAddHaarMeasure
  hm₁ : IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁
  hm' : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m'
  hs : Measurable s
  hsec : ∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) →
    actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y
  hcpt : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
    ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C'
  hB₀ : IsOpen B₀
  htB : algebraMap F R t ∈ B₀
  hac : ContinuousOn a B₀
  hoff : ∀ x, x ∉ B₀ → a x = 1
  hsq : ∀ x ∈ B₀, x = ((a x : Rˣ) : R) ^ 2 * algebraMap F R t
  ha1 : a (algebraMap F R t) = 1
  hκc : Continuous κ₁
  hκ1 : κ₁ 1 = 1
  hscale : ∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) =
    κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))
  hcmc : Continuous cm
  hmod : ∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam
end Data
end GlobalTheory.CompanionTheory.SW.PiLocalization₂


