-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:00.170303+00:00
-- url     : https://prove2.me/theorems/55e39f9b-5036-4e22-8747-5eab088f2ded
-- title:
--   Inst Borel GL
-- statement:
--   Definitions and structural lemmas for Inst Borel GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InstBorelGL.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL
section Base
variable {F : Type} [Field F]
def IsInt {n : ℕ} (R : Subring F) (Z : Matrix (Fin n) (Fin n) F) : Prop := ∀ a b, Z a b ∈ R
def intMat (O : Subring F) (n a : ℕ) : Set (Matrix (Fin n) (Fin a) F) := {y | ∀ i j, y i j ∈ O}
theorem isInt_mul' (O : Subring F) {a : ℕ} {x y : Matrix (Fin a) (Fin a) F} (hx : IsInt O x)
    (hy : IsInt O y) : IsInt O (x * y) := by
  intro a b
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => O.mul_mem (hx a k) (hy k b)
def GLint (O : Subring F) (a : ℕ) : Subgroup (GL (Fin a) F) where
  carrier := {g | IsInt O (g : Matrix (Fin a) (Fin a) F) ∧
    IsInt O ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)}
  one_mem' := by
    constructor <;> intro i j <;> by_cases h : i = j <;> simp [h, O.one_mem, O.zero_mem]
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simpa using isInt_mul' O hx hy, ?_⟩
    simpa [_root_.mul_inv_rev] using isInt_mul' O hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨by simpa using hx', by simpa using hx⟩
def IIset {a t : ℕ} (O : Subring F) (ϖ : F) : Set (Matrix (Fin t) (Fin a) F) :=
  {y | ∀ i j, ∃ o ∈ O, y i j = ϖ * o}
def Jset {a : ℕ} (J' : Subgroup (GL (Fin a) F)) : Set (Matrix (Fin a) (Fin a) F) :=
  (fun k : GL (Fin a) F => (k : Matrix (Fin a) (Fin a) F)) '' (J' : Set (GL (Fin a) F))
instance instMeasMat {m n F : Type} [MeasurableSpace F] : MeasurableSpace (Matrix m n F) :=
  inferInstanceAs (MeasurableSpace (m → n → F))
instance instMeasGL {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ) :
    MeasurableSpace (GL (Fin n) K) := borel _
instance instBorelGL {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ) :
    BorelSpace (GL (Fin n) K) := ⟨rfl⟩
def omegaS {a : ℕ} {m : Type} [Fintype m] (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (g : GL (Fin a) F)
    (Φ : Matrix m (Fin a) F → ℂ) : Matrix m (Fin a) F → ℂ :=
  fun x => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^ ((Fintype.card m : ℝ) / 2) : ℝ) : ℂ) *
    Φ (x * (g : Matrix (Fin a) (Fin a) F))
def weilIP {a : ℕ} {m : Type} [MeasurableSpace F] (ν : Measure (Matrix m (Fin a) F)) (Φ₁ Φ₂ : Matrix m (Fin a) F → ℂ) : ℂ :=
  ∫ x, Φ₁ x * conj (Φ₂ x) ∂ν
def localZ {a : ℕ} {m : Type} [Fintype m] [MeasurableSpace F] [TopologicalSpace F] [IsTopologicalRing F]
    (μ : Measure (GL (Fin a) F)) (ν : Measure (Matrix m (Fin a) F)) (χ : Fˣ →* ℂˣ)
    (nrm : AbsoluteValue F ℝ) (Φ₁ Φ₂ : Matrix m (Fin a) F → ℂ) (c : GL (Fin a) F → ℂ) : ℂ :=
  ∫ g, weilIP ν (omegaS χ nrm g Φ₁) Φ₂ * conj (c g) ∂μ
end Base
section Local
variable {F : Type} [Field F]
def chi0 (δ : Fˣ →* ℂˣ) (x : F) : ℂ :=
  open Classical in if h : x = 0 then 0 else ((δ (Units.mk0 x h) : ℂˣ) : ℂ)
def bAA {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin r) (Fin r) F :=
  x.submatrix (Fin.castAdd d) (Fin.castAdd c)
def bAD {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin r) (Fin c) F :=
  x.submatrix (Fin.castAdd d) (Fin.natAdd r)
def bDA {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin d) (Fin r) F :=
  x.submatrix (Fin.natAdd r) (Fin.castAdd c)
def bDD {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin d) (Fin c) F :=
  x.submatrix (Fin.natAdd r) (Fin.natAdd r)
variable (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ)
def parJ (r c : ℕ) : Set (GL (Fin (r + c)) F) :=
  {k | k ∈ GLint O (r + c) ∧ bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ IIset O ϖ}
def lamJ (δ : Fˣ →* ℂˣ) {r c : ℕ} (k : GL (Fin (r + c)) F) : ℂ :=
  chi0 δ (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det
def phiQ (δ : Fˣ →* ℂˣ) (r d c : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : ℂ :=
  open Classical in
  if bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c then
    (chi0 δ (bAA x).det)⁻¹ else 0
def IsSphFn {c : ℕ} (χ : Fin c → F → ℂ) (φ : GL (Fin c) F → ℂ) : Prop :=
  ∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ k ∈ GLint O c,
    φ (b * k) = ∏ i : Fin c, χ i ((b : Matrix (Fin c) (Fin c) F) i i) *
      ((nrm ((b : Matrix (Fin c) (Fin c) F) i i) ^ (((c : ℝ) - 1) / 2 - (i : ℕ)) : ℝ) : ℂ)
def satC (ν : ℕ → Fˣ →* ℂˣ) (t c : ℕ) (a : Fin c) (x : F) : ℂ :=
  chi0 (ν ((a : ℕ) / t + 1)) x * ((nrm x ^ ((((a : ℕ) % t : ℕ) : ℝ) - ((t : ℝ) - 1) / 2) : ℝ) : ℂ)
variable [TopologicalSpace F] [IsTopologicalRing F]
structure IsUnrM (r c : ℕ) (χ : Fin c → F → ℂ) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : GL (Fin r) F × GL (Fin c) F →* (V ≃ₗᵢ[ℂ] V)) : Prop where
  smooth : ∀ x : V, IsOpen {m | ρ m x = x}
  irred : ∀ W : Submodule ℂ V, (∀ m, ∀ x ∈ W, ρ m x ∈ W) → W = ⊥ ∨ W = ⊤
  sph : ∃ v₀ : V, ‖v₀‖ = 1 ∧ (∀ k₁ ∈ GLint O r, ∀ k₂ ∈ GLint O c, ρ (k₁, k₂) v₀ = v₀) ∧
    ∃ (φ : GL (Fin c) F → ℂ) (κ : Measure (GL (Fin c) F)), IsSphFn O nrm χ φ ∧ κ.IsMulLeftInvariant ∧
      κ (GLint O c : Set (GL (Fin c) F)) = 1 ∧
      ∀ g : GL (Fin c) F, inner ℂ v₀ (ρ (1, g) v₀) = ∫ k in (GLint O c : Set (GL (Fin c) F)), φ (k * g) ∂κ
def typeSp (δ : Fˣ →* ℂˣ) (r c : ℕ) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : GL (Fin r) F × GL (Fin c) F →* (V ≃ₗᵢ[ℂ] V)) : Submodule ℂ (GL (Fin (r + c)) F → V) where
  carrier := {f | (∀ (p : GL (Fin (r + c)) F) (m₁ : GL (Fin r) F) (m₂ : GL (Fin c) F),
      bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 →
      bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = (m₁ : Matrix (Fin r) (Fin r) F) →
      bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = (m₂ : Matrix (Fin c) (Fin c) F) → ∀ g,
      f (p * g) = (((nrm (m₁ : Matrix (Fin r) (Fin r) F).det ^ ((c : ℝ) / 2) *
          nrm (m₂ : Matrix (Fin c) (Fin c) F).det ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
        ((δ (Matrix.GeneralLinearGroup.det m₂) : ℂˣ) : ℂ)) • ρ (m₁, m₂) (f g)) ∧
    ∀ k ∈ parJ O ϖ r c, ∀ g, f (g * k) = lamJ δ k • f g}
  zero_mem' := ⟨fun _ _ _ _ _ _ _ => by simp, fun _ _ _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun p m₁ m₂ a b c g => ?_, fun k hk g => ?_⟩
    · simp only [Pi.add_apply, h1 p m₁ m₂ a b c g, h3 p m₁ m₂ a b c g, map_add, smul_add]
    · simp only [Pi.add_apply, h2 k hk g, h4 k hk g, smul_add]
  smul_mem' := by
    rintro z f ⟨h1, h2⟩
    refine ⟨fun p m₁ m₂ a b c g => ?_, fun k hk g => ?_⟩
    · simp only [Pi.smul_apply, h1 p m₁ m₂ a b c g, map_smul]
      exact smul_comm _ _ _
    · simp only [Pi.smul_apply, h2 k hk g]
      exact smul_comm _ _ _
def mcoef {n : ℕ} (μ : Measure (GL (Fin n) F)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (f : GL (Fin n) F → V) (g : GL (Fin n) F) : ℂ :=
  ∫ k in (GLint O n : Set (GL (Fin n) F)), inner ℂ (f k) (f (k * g)) ∂μ
def IsTypeDim (δ : Fˣ →* ℂˣ) (ν : ℕ → Fˣ →* ℂˣ) (r t j n : ℕ) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (ρ : GL (Fin r) F × GL (Fin (j * t)) F →* (V ≃ₗᵢ[ℂ] V)),
    IsUnrM O nrm r (j * t) (satC nrm ν t (j * t)) ρ ∧ n = Module.finrank ℂ (typeSp O ϖ nrm δ r (j * t) ρ)
def IsStep [MeasurableSpace F] (δ : Fˣ →* ℂˣ) (ν : ℕ → Fˣ →* ℂˣ) (r t j : ℕ) (z : ℂ) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (ρ : GL (Fin r) F × GL (Fin (j * t)) F →* (V ≃ₗᵢ[ℂ] V)),
    IsUnrM O nrm r (j * t) (satC nrm ν t (j * t)) ρ ∧ ∃ f ∈ typeSp O ϖ nrm δ r (j * t) ρ,
    ∃ (μ : Measure (GL (Fin (r + j * t)) F)) (dx : Measure (Matrix (Fin (r + (j + 1) * t)) (Fin (r + j * t)) F)),
      μ.IsMulLeftInvariant ∧ μ (parJ O ϖ r (j * t)) = 1 ∧ mcoef O μ f 1 = 1 ∧
      dx.IsAddLeftInvariant ∧ dx (intMat O (r + (j + 1) * t) (r + j * t)) = 1 ∧
      z = localZ μ dx (ν (j + 1) * δ) nrm (phiQ O ϖ δ r ((j + 1) * t) (j * t)) (phiQ O ϖ δ r ((j + 1) * t) (j * t))
        (mcoef O μ f)
def om {c : ℕ} (κ : Measure (GL (Fin c) F)) (φ : GL (Fin c) F → ℂ) (g : GL (Fin c) F) : ℂ :=
  ∫ k in (GLint O c : Set (GL (Fin c) F)), φ (k * g) ∂κ
end Local
section More
variable {F : Type} [Field F]
def Mint (O : Subring F) (c : ℕ) : Set (GL (Fin c) F) := {g | IsInt O (g : Matrix (Fin c) (Fin c) F)}
def latI (O : Subring F) (d : ℕ) {c : ℕ} (g : GL (Fin c) F) : Set (Matrix (Fin d) (Fin c) F) :=
  {y | y ∈ intMat O d c ∧ y * (g : Matrix (Fin c) (Fin c) F) ∈ intMat O d c}
def pEl {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) : GL (Fin (r + c)) F where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (m₁ : Matrix (Fin r) (Fin r) F) B 0 (m₂ : Matrix (Fin c) (Fin c) F))
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks ((m₁⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
      (-(((m₁⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B * ((m₂⁻¹ : GL (Fin c) F) : Matrix (Fin c) (Fin c) F))) 0
      ((m₂⁻¹ : GL (Fin c) F) : Matrix (Fin c) (Fin c) F))
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_neg,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      neg_add_cancel, neg_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.neg_mul,
      Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      add_neg_cancel, neg_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
def cellPJ (O : Subring F) (ϖ : F) (r c : ℕ) : Set (GL (Fin (r + c)) F) :=
  {g | ∃ p : GL (Fin (r + c)) F, bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ ∃ j ∈ parJ O ϖ r c, g = p * j}
def iwa (O : Subring F) (ϖ : F) {n : ℕ} (σ : Fin n → ℕ) : Set (GL (Fin n) F) :=
  {k | k ∈ GLint O n ∧ ∀ a b, σ b < σ a → ∃ o ∈ O, (k : Matrix (Fin n) (Fin n) F) a b = ϖ * o}
def UnrChar (nrm : AbsoluteValue F ℝ) (q : ℕ) {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ) : Prop :=
  (∀ i, α i ≠ 0) ∧ ∀ i (x : F) (e : ℤ), nrm x = (q : ℝ) ^ (-e) → χ i x = α i ^ e
structure Del (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) : Prop where
  unitary : ∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1
  tame : ∀ x : Fˣ, nrm ((x : F) - 1) < 1 → δ x = 1
  ram : ∃ x : Fˣ, nrm (x : F) = 1 ∧ δ x ≠ 1
structure Nu (nrm : AbsoluteValue F ℝ) (ν : Fˣ →* ℂˣ) : Prop where
  unitary : ∀ x, ‖((ν x : ℂˣ) : ℂ)‖ = 1
  unr : ∀ x : Fˣ, nrm (x : F) = 1 → ν x = 1
structure LF [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ) (q : ℕ) : Prop where
  O_eq : O = 𝒪[F]
  ne : ϖ ≠ 0
  lt_one : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ O, x = ϖ * o
  card : q = Nat.card 𝓀[F]
  nrm_unit : ∀ x : F, ValuativeRel.valuation F x = 1 → nrm x = 1
  nrm_pi : nrm ϖ = (q : ℝ)⁻¹
end More
def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Finset.Icc a c, (1 - q ^ (-(i : ℤ)))
def Lpair (q : ℝ) (t : ℕ) (x : ℂ) : ℂ :=
  (∏ s ∈ Finset.Icc 1 t, ((1 - x * ((q : ℂ) ^ (-(s : ℤ)))) * (1 - x⁻¹ * ((q : ℂ) ^ (-(s : ℤ))))))⁻¹
def zVal (q : ℝ) (r t j : ℕ) (x : ℕ → ℂ) : ℂ :=
  ((q ^ (-((j * t * r : ℕ) : ℤ)) * qE q 1 r * qE q (t + 1) (j * t) : ℝ) : ℂ) *
    ∏ i ∈ Finset.Ico 1 j, Lpair q t (x i / x j)
end GlobalTheory.CompanionTheory.QL


