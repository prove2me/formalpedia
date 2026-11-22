-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
-- name    : Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:34.371809+00:00
-- url     : https://prove2.me/theorems/0d762af2-0d37-4c90-bc27-aeb30a7e1535
-- title:
--   Card Submodules And Linear Equiv Bounds
-- statement:
--   Definitions and structural lemmas for Card Submodules And Linear Equiv Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/CardSubmodulesAndLinearEquivBounds.lean

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Formalism.HermitianLatticeCounting.LatticeSumBounds
def hs {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)
def TraceHS : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (J' J'' : Matrix m n ℂ)
    (U : Matrix n n ℂ), U ∈ Matrix.unitaryGroup n ℂ →
    ‖(J' * U * J''ᴴ).trace‖ ≤ hs J' * hs J''
def RankHS : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] (J : Matrix m n ℂ) (c : ℝ), 0 ≤ c →
    (∀ x : n → ℂ, ∑ i, ‖(J *ᵥ x) i‖ ^ 2 ≤ c ^ 2 * ∑ j, ‖x j‖ ^ 2) →
    hs J ^ 2 ≤ min (Fintype.card m : ℝ) (Fintype.card n : ℝ) * c ^ 2
def WeightedAMGM : Prop :=
  ∀ a b La : ℝ, 0 < La → |a * b| ≤ (La * a ^ 2 + b ^ 2 / La) / 2
def CommonLiftExpand : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (r : ℕ)
    (e e' : Fin r → V) (l₁ l₂ : V) (α α' : Fin r → ℂ),
    (∀ b, h l₁ (e' b) = 0) → (∀ a, h (e a) l₂ = 0) →
    h (l₁ + ∑ a, α a • e a) (l₂ + ∑ b, α' b • e' b) =
      h l₁ l₂ + ∑ a, ∑ b, α a * conj (α' b) * h (e a) (e' b)
def AbsA : Prop :=
  ∀ (U₁ U₂ : Type) [NormedAddCommGroup U₁] [InnerProductSpace ℂ U₁]
    [NormedAddCommGroup U₂] [InnerProductSpace ℂ U₂] (r : ℕ) (u : Fin r → U₁) (u' : Fin r → U₂)
    (Z : Matrix (Fin r) (Fin r) ℂ),
    (∀ w₁ w₂, ‖∑ a, ∑ b, inner ℂ (u a) w₁ * conj (inner ℂ (u' b) w₂) * Z a b‖ ≤
      2 * ‖w₁‖ * ‖w₂‖) →
    Real.sqrt ‖(Matrix.gram ℂ u).det‖ * Real.sqrt ‖(Matrix.gram ℂ u').det‖ * ‖Z.det‖ ≤ 2 ^ r
def InverseEntryBound : Prop :=
  ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (B : ℝ), (∀ i j, ‖M i j‖ ≤ B) → M.det ≠ 0 →
    ∀ i j, ‖M⁻¹ i j‖ ≤ ((r - 1).factorial : ℝ) * B ^ (r - 1) / ‖M.det‖
def InverseEntryMinor : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (P : ℝ),
    (∀ i j, ‖(M.submatrix (Fin.succAbove i) (Fin.succAbove j)).det‖ ≤ P) → M.det ≠ 0 →
    ∀ i j, ‖M⁻¹ i j‖ ≤ P / ‖M.det‖
def WedgeHadamard : Prop :=
  ∀ (V₁ V₂ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ),
    (∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) →
    ∀ (j : ℕ) (y : Fin j → V₁) (y' : Fin j → V₂),
      ‖(Matrix.of fun a b => B (y a) (y' b)).det‖ ≤ (∏ a, ‖y a‖) * ∏ b, ‖y' b‖
def LengthLower : Prop :=
  ∀ (r : ℕ) (l l' : Fin r → ℝ) (R Dr : ℝ), (∀ a, 0 < l a ∧ l a ≤ R) → (∀ b, 0 < l' b ∧ l' b ≤ R) →
    Dr ≤ (∏ a, l a) * ∏ b, l' b → ∀ b, Dr ≤ l' b * R ^ (2 * r - 1)
def CramerUpper : Prop :=
  ∀ (R : Type) [CommRing R] (N l : ℕ) (hl : l ≤ N) (Lo W Up : Matrix (Fin N) (Fin N) R),
    (∀ i, Lo i i = 1) → (∀ i j, i < j → Lo i j = 0) → (∀ i, Up i i = 1) →
    (∀ i j, j < i → Up i j = 0) → (∀ i j : Fin N, (i : ℕ) < l → l ≤ (j : ℕ) → W i j = 0) →
    ∀ (c : Fin l) (b : Fin N),
      (∀ c' : Fin l, c < c' → Up (Fin.castLE hl c) (Fin.castLE hl c') = 0) →
      ((Lo * W * Up).submatrix (Fin.castLE hl)
          (fun j => if j = c then b else Fin.castLE hl j)).det =
        ((Lo * W * Up).submatrix (Fin.castLE hl) (Fin.castLE hl)).det * Up (Fin.castLE hl c) b
def VolumeLemma : Prop :=
  ∀ (d r : ℕ) (R y : ℝ), 1 ≤ r → r ≤ d → 0 < R → 0 < y →
    MeasureTheory.volume {a : Fin r → EuclideanSpace ℂ (Fin d) |
        (∀ b, ‖a b‖ ≤ R) ∧ y < Real.sqrt ‖(Matrix.gram ℂ a).det‖ ∧
          Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ 2 * y} ≤
      ENNReal.ofReal ((2 * y) ^ (2 * (d - r)) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        ((d - r).factorial : ℝ) ^ r)
def GramHadamard : Prop :=
  ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (r : ℕ) (a : Fin r → U),
    Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ ∏ b, ‖a b‖ ∧
    ∀ R : ℝ, (∀ b, ‖a b‖ ≤ R) → Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ R ^ r
def SchurAverage : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : MeasureTheory.Measure K) [μ.IsHaarMeasure]
    [MeasureTheory.IsProbabilityMeasure μ]
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (π : K →* (V ≃ₗᵢ[ℂ] V)), (∀ v, Continuous fun h => π h v) →
    (∀ S : Submodule ℂ V, (∀ h, ∀ x ∈ S, π h x ∈ S) → S = ⊥ ∨ S = ⊤) →
    ∀ (S : Submodule ℂ V) (v : V),
      ∫ h, ‖S.starProjection (π h v)‖ ^ 2 ∂μ = (finrank ℂ S : ℝ) / (finrank ℂ V : ℝ) * ‖v‖ ^ 2
def LemmaP : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → ℝ) (Sg : Finset ι), (∀ v, 0 < x v) → 1 ≤ ∏ v, x v →
    ∏ v ∈ Sg, max (x v) (1 / x v) ≤ (∏ v, max 1 (x v)) ^ 2 ∧
    ∏ v ∈ Sg, max 1 (1 / x v) ≤ ∏ v, max 1 (x v)
def PThreshold : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → ℝ) (H : ℝ), 1 ≤ H → (∀ v, 0 ≤ x v) →
    ∏ v, max 1 (x v) ≤ H ^ Fintype.card ι * ∏ v, max 1 (x v / H)
def size {ι l : Type*} [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (H₂ : ℝ) : ℝ :=
  ∏ v, ∏ i ∈ E, max 1 (D i v / H₂)
def LossProd : Prop :=
  ∀ (ι l : Type) [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (G : ι → ℝ) (B H₂ : ℝ) (e₁ e₂ : ℕ)
    (l₀ : l) (Sg : Finset ι), 1 ≤ B → 1 ≤ H₂ → l₀ ∈ E → (∀ i ∈ E, ∀ v, 0 < D i v) →
    (∀ i ∈ E, 1 ≤ ∏ v, D i v) → (∀ v, 0 < G v) → 1 ≤ ∏ v, G v → (∀ v, G v ≤ D l₀ v ^ 2) →
    ∏ v ∈ Sg, (B * max (G v) (1 / G v) ^ e₁ * ∏ i ∈ E, max (D i v) (1 / D i v) ^ e₂) ≤
      B ^ Fintype.card ι * (H₂ ^ Fintype.card ι * size E D H₂) ^ (4 * e₁) *
        (H₂ ^ (Fintype.card ι * E.card) * size E D H₂) ^ (2 * e₂)
def LossPrimeProd : Prop :=
  ∀ (ι l : Type) [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (De : ι → ℝ) (H₁ H₂ : ℝ) (e : ℕ)
    (Sg : Finset ι), 1 ≤ H₁ → 1 ≤ H₂ → (∀ i ∈ E, ∀ v, 0 < D i v) → (∀ i ∈ E, 1 ≤ ∏ v, D i v) →
    (∀ v, 0 ≤ De v) → (∀ v, De v ≤ 1 ∨ ∃ i ∈ E, De v ≤ 1 / D i v) →
    ∏ v ∈ Sg, (H₁ * De v) ^ e ≤
      (H₁ ^ Fintype.card ι * H₂ ^ (Fintype.card ι * E.card) * size E D H₂) ^ e
def nv (k r : ℕ) (G T g v : ℝ) : ℝ :=
  (Real.exp 1 * Real.pi * G * g⁻¹ ^ (2 * r + 2) / (T * k * v)) ^ k
def expo (k r : ℕ) : ℝ := ((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k : ℝ)
def xv (k r : ℕ) (C ν t g : ℝ) : ℝ := ν * t * g⁻¹ ^ (2 * r + 2) * (C / k) ^ expo k r
def MinI : Prop :=
  ∀ (k r : ℕ) (C G T g v t Dr loss loss' JHS Jop dim : ℝ),
    2 * r + 6 ≤ k → 0 < C → 0 < G → 0 < T → 0 < g → 1 ≤ v → 0 < t → 0 < Dr → 1 ≤ loss' →
    0 < dim → 0 ≤ Jop → 0 ≤ JHS → Real.exp 1 * Real.pi ≤ k → Dr ^ (2 * r + 4) ≤ loss →
    nv k r G T g v * JHS ^ 2 / dim ≤ loss * t⁻¹ ^ k →
    Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r) →
    JHS ^ 2 ≤ dim * Jop ^ 2 →
    nv k r G T g v * JHS ^ 2 / dim ≤
      loss * loss' ^ 2 * t⁻¹ ^ k * (min 1 (xv k r C (G / (T * Dr ^ 2)) t g)) ^ k
def MinI' : Prop :=
  ∀ (k r : ℕ) (C G T g v t Dr loss loss' JHS Jop dim : ℝ),
    r + 2 ≤ k → 0 < C → 0 < G → 0 < T → 0 < g → 0 < v → 0 < t → 0 < Dr → 1 ≤ loss' →
    0 < dim → 0 ≤ Jop → 0 ≤ JHS →
    (Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * (k - 2 - r)) ≤ 1 →
    Dr ^ (2 * r + 4) ≤ loss →
    nv k r G T g v * JHS ^ 2 / dim ≤ loss * t⁻¹ ^ k →
    Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r) →
    JHS ^ 2 ≤ dim * Jop ^ 2 →
    nv k r G T g v * JHS ^ 2 / dim ≤
      loss * loss' ^ 2 * t⁻¹ ^ k * (min 1 (xv k r C (G / (T * Dr ^ 2)) t g)) ^ k
def ChShSq : Prop :=
  ∀ sh ch : ℝ, 0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 →
    (1 ≤ sh → ((1 + ch) / sh) ^ 2 ≤ 6) ∧ (sh < 1 → (1 + ch) ^ 2 ≤ 6)
def MinII : Prop :=
  ∀ (k r : ℕ) (C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim : ℝ),
    1 ≤ r → 2 * r + 6 ≤ k → 0 < C → C ≤ k → 0 < G → 0 < T → 0 < T' → 1 ≤ g → 1 ≤ v → 0 < t →
    0 < Dr → 1 ≤ loss' → 0 < dim → 0 ≤ Jop → 0 ≤ JHS → Dr ^ (2 * r + 4) ≤ loss →
    0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → G = T * T' * Dr ^ 2 * sh ^ 2 →
    T' / T ≤ CT → (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t →
    nv k r G T g v * JHS ^ 2 / dim ≤ loss * t⁻¹ ^ k →
    Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r) →
    JHS ^ 2 ≤ dim * Jop ^ 2 →
    nv k r G T g v * JHS ^ 2 * ((1 + ch) / sh) ^ (2 * k) * T⁻¹ ^ k / dim ≤
      loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k
def MinII' : Prop :=
  ∀ (k r : ℕ) (C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim : ℝ),
    1 ≤ r → 2 * r + 6 ≤ k → 0 < C → 0 < G → 0 < T → 0 < T' → 1 ≤ g → 0 < v → 0 < t →
    0 < Dr → 1 ≤ loss' → 0 < dim → 0 ≤ Jop → 0 ≤ JHS →
    v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * (k - 2 - r)) ≤ 1 → Dr ^ (2 * r + 4) ≤ loss →
    0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → G = T * T' * Dr ^ 2 * sh ^ 2 →
    T' / T ≤ CT → (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t →
    nv k r G T g v * JHS ^ 2 / dim ≤ loss * t⁻¹ ^ k →
    Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r) →
    JHS ^ 2 ≤ dim * Jop ^ 2 →
    nv k r G T g v * JHS ^ 2 * ((1 + ch) / sh) ^ (2 * k) * T⁻¹ ^ k / dim ≤
      loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k
def MinIIZero : Prop :=
  ∀ (k r : ℕ) (CT G T T' g v t loss JHS dim : ℝ),
    1 ≤ r → 1 ≤ k → 0 < G → 0 < T → 0 < T' → 1 ≤ g → 0 < v → 0 < t → 0 ≤ loss → 0 < dim →
    T' / T ≤ CT → (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t →
    nv k r G T g v * JHS ^ 2 / dim ≤ loss * t⁻¹ ^ k →
    nv k r G T g v * JHS ^ 2 * T⁻¹ ^ k / dim ≤ loss * (CT / (k * g ^ (2 * r + 2))) ^ k
def XTilde : Prop :=
  ∀ (k r : ℕ) (C ν T' t g : ℝ), r + 2 ≤ k → 1 ≤ C → 0 < ν → 0 < T' → 0 < t → 0 < g →
    (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t →
    min 1 (xv k r C ν t g) ≤ xv k r C (min ν T') t g
def ProdMinX : Prop :=
  ∀ (ι : Type) [Fintype ι] (k r : ℕ) (C C₁ C₂ T' g : ℝ) (ν t : ι → ℝ),
    r + 2 ≤ k → 1 ≤ C → 2 * C ^ 2 ≤ k → ((r : ℝ) + 2) * Real.log k ≤ k / 6 → 0 < T' → 0 < g →
    (∀ v, 0 < ν v) → (∀ v, 0 < t v) →
    (∀ v, (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t v) →
    ∏ v, min (ν v) T' ≤ (C₁ * g) ^ Fintype.card ι → ∏ v, t v ≤ C₂ →
    ∏ v, min 1 (xv k r C (ν v) (t v) g) ≤
      C₂ * (C₁ * g * g⁻¹ ^ (2 * r + 2) * ((k : ℝ) ^ r)⁻¹) ^ Fintype.card ι
def XiIdentity : Prop :=
  ∀ (mass mj : ℕ → ℝ) (k s : ℕ), (∀ j, 0 < mj j) → 0 < mass 2 →
    (∀ j, 3 ≤ j → mass j = mj j * mass (j - 1)) → 2 ≤ s → s + 2 ≤ k →
    mass s * mass (k - s) / mass k =
      mass 2 * (∏ j ∈ Finset.Ioc 2 s, mj j) / ∏ j ∈ Finset.Ioc (k - s) k, mj j
def mJ (f : ℕ) (v : ℝ) (Lv : ℕ → ℝ) (j : ℕ) : ℝ :=
  (((j - 1).factorial : ℝ) * (v / Real.pi) ^ j) ^ f * (Real.sqrt ((2 * v) ^ f))⁻¹ * Lv j
def zetaR (j : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ j
def ZetaLogSum : Prop :=
  ∀ N : ℕ, ∑ j ∈ Finset.Icc 3 N, Real.log (zetaR j) ≤ 0.356
def PiPowFactorial : Prop :=
  ∀ k : ℕ, 3 ≤ k → Real.pi ^ (k - 1) / ((k - 2).factorial : ℝ) < 17
def StirlingInv : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    1 / ((k - 1).factorial : ℝ) ≤ (Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi))
def XiBound : Prop :=
  ∀ (f k s : ℕ) (v mass2 : ℝ) (Lv : ℕ → ℝ), 1 ≤ v → 0 ≤ mass2 → 2 ≤ s → s + 2 ≤ k →
    (∀ j, 3 ≤ j → ((zetaR j) ^ f)⁻¹ ≤ Lv j ∧ Lv j ≤ (zetaR j) ^ f) →
    mass2 * (∏ j ∈ Finset.Ioc 2 s, mJ f v Lv j) / ∏ j ∈ Finset.Ioc (k - s) k, mJ f v Lv j ≤
      mass2 * (2 * v) ^ f * Real.exp (0.72 * f) * 17 ^ f * Real.sqrt (k / (2 * Real.pi)) ^ f *
        Real.pi ^ ((s - 2) * (k - s - 2) * f) * (Real.exp 1 * Real.pi / (k * v)) ^ (k * f)
def InvMk : Prop :=
  ∀ (f k : ℕ) (v : ℝ) (Lv : ℕ → ℝ), 1 ≤ v → 3 ≤ k → ((zetaR k) ^ f)⁻¹ ≤ Lv k →
    (mJ f v Lv k)⁻¹ ≤ (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (k * (2 * v)) ^ f
def Packing : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : AddSubgroup E) (l₀ R : ℝ), 0 < l₀ → 0 ≤ R → (∀ x ∈ Λ, x ≠ 0 → l₀ ≤ ‖x‖) →
    {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}.Finite ∧
      ({x : E | x ∈ Λ ∧ ‖x‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R / l₀) ^ finrank ℝ E
def TraceLower : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℝ), (∀ v, 0 ≤ a v) → 1 ≤ ∏ v, a v →
    (Fintype.card ι : ℝ) ≤ ∑ v, a v
def Phi {n R : Type*} [Fintype n] [CommRing R] [StarRing R] (S Y : Matrix n n R) : Matrix n n R :=
  Y + Yᴴ + Yᴴ * S * Y
def PhiGram : Prop :=
  ∀ (n R : Type) [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] (S Y : Matrix n n R),
    Sᴴ = S → (1 + Y * S)ᴴ * S * (1 + Y * S) - S = S * Phi S Y * S
def DiscKernelCoord : Prop :=
  ∀ (n R : Type) [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] (S γ : Matrix n n R),
    Sᴴ = S → IsUnit S.det → (γᴴ * S * γ = S ↔ Phi S ((γ - 1) * S⁻¹) = 0)
def PhiUnit : Prop :=
  ∀ (n R : Type) [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] (S Y : Matrix n n R),
    (1 + Yᴴ * S) * (1 + Y * S) = 1 + Phi S Y * S
def PhiProduct : Prop :=
  ∀ (n R : Type) [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] (S Y Y' : Matrix n n R),
    Sᴴ = S → Phi S (Y + Y' + Y * S * Y') = (1 + Y'ᴴ * S) * Phi S Y * (1 + S * Y') + Phi S Y'
def PhiInverse : Prop :=
  ∀ (n R : Type) [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] (S Y : Matrix n n R),
    Sᴴ = S → Phi S Y = 0 → Phi S Yᴴ = 0
def PhiDiff : Prop :=
  ∀ (n R : Type) [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] (S Y Z : Matrix n n R),
    Sᴴ = S → Phi S (Y + Z) =
      Phi S Y + ((1 + Yᴴ * S) * Z + ((1 + Yᴴ * S) * Z)ᴴ) + Zᴴ * S * Z
def HermTraceOnto : Prop :=
  ∀ (n R : Type) [Fintype n] [CommRing R] [StarRing R],
    (∀ a : R, star a = a → ∃ x, x + star x = a) →
    ∀ H : Matrix n n R, Hᴴ = H → ∃ Z : Matrix n n R, Z + Zᴴ = H
def PhiBaseChange : Prop :=
  ∀ (n R : Type) [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] (S Y g : Matrix n n R),
    IsUnit g.det → Phi ((g⁻¹)ᴴ * S * g⁻¹) (g * Y * gᴴ) = g * Phi S Y * gᴴ
def RadicalSplitField : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (j : ℕ) (S : Matrix (Fin j) (Fin j) K), Sᴴ = S →
    ∃ (a e : ℕ) (φ : Fin a ⊕ Fin e ≃ Fin j) (g : Matrix (Fin j) (Fin j) K)
      (S₀ : Matrix (Fin a) (Fin a) K), a = S.rank ∧ IsUnit g.det ∧ S₀ᴴ = S₀ ∧ IsUnit S₀.det ∧
      ((g⁻¹)ᴴ * S * g⁻¹).submatrix φ φ = Matrix.fromBlocks S₀ 0 0 0
def RadicalSplitSwap : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [StarRing A] (ε : A ≃+* k × k) (j : ℕ)
    (S : Matrix (Fin j) (Fin j) A), (∀ x, ε (star x) = (ε x).swap) → Sᴴ = S →
    ∃ (a e : ℕ) (φ : Fin a ⊕ Fin e ≃ Fin j) (g : Matrix (Fin j) (Fin j) A)
      (S₀ : Matrix (Fin a) (Fin a) A), a = (S.map fun x => (ε x).1).rank ∧ IsUnit g.det ∧
      S₀ᴴ = S₀ ∧ IsUnit S₀.det ∧
      ((g⁻¹)ᴴ * S * g⁻¹).submatrix φ φ = Matrix.fromBlocks S₀ 0 0 0
def SolCount : Prop :=
  ∀ (A : Type) [CommRing A] [StarRing A] [Finite A] (q : ℕ) (m n : Type) [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (S₀ : Matrix m m A),
    Nat.card A = q ^ 2 → Nat.card {a : A // star a = a} = q →
    (∀ a : A, star a = a → ∃ x, x + star x = a) → S₀ᴴ = S₀ → IsUnit S₀.det →
    Nat.card {Y : Matrix (m ⊕ n) (m ⊕ n) A // Phi (Matrix.fromBlocks S₀ 0 0 0) Y = 0} =
      Nat.card {γ : Matrix m m A // γᴴ * S₀ * γ = S₀} *
        q ^ (2 * Fintype.card m * Fintype.card n + Fintype.card n ^ 2)
def ResidueInert : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [Finite K] (q : ℕ), Nat.card K = q ^ 2 →
    (∀ x : K, star x = x ^ q) →
    Nat.card {a : K // star a = a} = q ∧ ∀ a : K, star a = a → ∃ x, x + star x = a
def ResidueSplit : Prop :=
  ∀ (k A : Type) [Field k] [Finite k] [CommRing A] [StarRing A] (ε : A ≃+* k × k),
    (∀ a, ε (star a) = (ε a).swap) →
    Nat.card A = Nat.card k ^ 2 ∧ Nat.card {a : A // star a = a} = Nat.card k ∧
      ∀ a : A, star a = a → ∃ x, x + star x = a
def UnitaryOrderInert : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [Finite K] (q n : ℕ) (S₀ : Matrix (Fin n) (Fin n) K),
    Nat.card K = q ^ 2 → (∀ x : K, star x = x ^ q) → S₀ᴴ = S₀ → IsUnit S₀.det →
    (Nat.card {γ : Matrix (Fin n) (Fin n) K // γᴴ * S₀ * γ = S₀} : ℝ) =
      (q : ℝ) ^ (n ^ 2) * ∏ l ∈ Finset.Icc 1 n, (1 - (-1 : ℝ) ^ l * ((q : ℝ) ^ l)⁻¹)
def UnitaryOrderSplit : Prop :=
  ∀ (k A : Type) [Field k] [Finite k] [CommRing A] [StarRing A] (e : A ≃+* k × k) (n : ℕ)
    (S₀ : Matrix (Fin n) (Fin n) A), (∀ a, e (star a) = (e a).swap) → S₀ᴴ = S₀ → IsUnit S₀.det →
    (Nat.card {γ : Matrix (Fin n) (Fin n) A // γᴴ * S₀ * γ = S₀} : ℝ) =
      (Nat.card k : ℝ) ^ (n ^ 2) * ∏ l ∈ Finset.Icc 1 n, (1 - ((Nat.card k : ℝ) ^ l)⁻¹)
def theta (j e : ℕ) (η q : ℝ) : ℝ := ∏ i ∈ Finset.Icc (j - e + 1) j, (1 - η ^ i * (q ^ i)⁻¹)
def ThetaRatio : Prop :=
  ∀ (j e : ℕ) (η q : ℝ), e ≤ j → 0 < q →
    q ^ (j ^ 2) * ∏ l ∈ Finset.Icc 1 j, (1 - η ^ l * (q ^ l)⁻¹) =
      theta j e η q * (q ^ ((j - e) ^ 2) * (∏ l ∈ Finset.Icc 1 (j - e), (1 - η ^ l * (q ^ l)⁻¹)) *
        q ^ (2 * (j - e) * e + e ^ 2))
def ThetaBound : Prop :=
  ∀ (j e : ℕ) (η q : ℝ), e ≤ j → 2 ≤ q → (η = 1 ∨ η = -1) →
    0 < theta j e η q ∧ theta j e η q ≤ (3 / 2) ^ e ∧ theta j e η q ≤ 2 ^ e
def ThetaProd : Prop :=
  ∀ (ι : Type) (P : Finset ι) (j e : ℕ) (ep : ι → ℕ) (η q : ι → ℝ),
    (∀ p ∈ P, ep p ≤ e ∧ ep p ≤ j ∧ 2 ≤ q p ∧ (η p = 1 ∨ η p = -1)) →
    0 < ∏ p ∈ P, theta j (ep p) (η p) (q p) ∧
      ∏ p ∈ P, theta j (ep p) (η p) (q p) ≤ 2 ^ (e * P.card)
def hermSub (F K n : Type*) [Field F] [CommRing K] [StarRing K] [Algebra F K] [Fintype n]
    (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) : Submodule F (Matrix n n K) where
  carrier := {A | Aᴴ = A}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.conjTranspose_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c A hA
    simp only [Set.mem_ofPred_eq] at *
    ext i j
    have h1 : star (A j i) = A i j := by
      have := congrFun (congrFun hA i) j
      simpa [Matrix.conjTranspose_apply] using this
    simp [Matrix.conjTranspose_apply, Algebra.smul_def, hF, h1]
def conjMap (F : Type*) {K n : Type*} [Field F] [CommRing K] [StarRing K] [Algebra F K] [Fintype n]
    [DecidableEq n] (g : Matrix n n K) : Matrix n n K →ₗ[F] Matrix n n K :=
  (LinearMap.mulLeft F g) ∘ₗ (LinearMap.mulRight F gᴴ)
def HermConjDet : Prop :=
  ∀ (F K : Type) [Field F] [CommRing K] [StarRing K] [Algebra F K] (j : ℕ)
    (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c), finrank F K = 2 →
    (∀ x : K, star x = x → x ∈ Set.range (algebraMap F K)) →
    ∀ (g : Matrix (Fin j) (Fin j) K), IsUnit g.det →
    ∀ hg : (∀ A ∈ hermSub F K (Fin j) hF, conjMap F g A ∈ hermSub F K (Fin j) hF),
      algebraMap F K (LinearMap.det ((conjMap F g).restrict hg)) = (g.det * star g.det) ^ j
def TwoPowOmega : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (NumberField.RingOfIntegers K)), I ≠ ⊥ →
    2 ^ {P : Ideal (NumberField.RingOfIntegers K) | P.IsPrime ∧ I ≤ P}.ncard ≤ Ideal.absNorm I
def TwoPowOmega' : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (NumberField.RingOfIntegers K)), I ≠ ⊥ →
    {P : Ideal (NumberField.RingOfIntegers K) | P.IsPrime ∧ I ≤ P}.Finite ∧
    2 ^ {P : Ideal (NumberField.RingOfIntegers K) | P.IsPrime ∧ I ≤ P}.ncard ≤ Ideal.absNorm I
def PowSubOneIdentities : Prop :=
  ∀ T k f : ℕ, 2 ≤ T → 1 ≤ k →
    (T : ℝ) ^ (f * k) * (1 - ((T : ℝ) ^ k)⁻¹) ^ f = ((T : ℝ) ^ k - 1) ^ f ∧
    ((T : ℝ) ^ f) ^ (k - 1) ≤ (((T : ℝ) ^ k - 1) / ((T : ℝ) - 1)) ^ f
def IdealNormCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 1 ≤ n →
    {I : Ideal (NumberField.RingOfIntegers K) | Ideal.absNorm I = n}.Finite ∧
    {I : Ideal (NumberField.RingOfIntegers K) | Ideal.absNorm I = n}.ncard ≤
      finrank ℚ K ^ (Nat.primeFactorsList n).length
def IdealNormLeCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : ℝ), 1 ≤ x →
    {I : Ideal (NumberField.RingOfIntegers K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.Finite ∧
    ({I : Ideal (NumberField.RingOfIntegers K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard : ℝ) ≤
      x ^ (1 + Real.logb 2 (finrank ℚ K))
def ClassNumberBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E],
    (NumberField.classNumber E : ℝ) ≤
      |(NumberField.discr E : ℝ)| ^ ((1 + Real.logb 2 (finrank ℚ E)) / 2)
def MeanBoundAssembly : Prop :=
  ∀ (k s : ℕ) (de NT lf massk masss massks massFlagLatticeZero mean nM nS mM mS Gl : ℝ),
    s ≤ k → 1 ≤ k → 1 ≤ de → 1 ≤ NT → 0 ≤ lf → 0 < massk → 0 < masss → 0 < massks → 0 ≤ mean →
    0 ≤ nM → 0 ≤ nS → 0 ≤ mM → 0 ≤ mS → 0 ≤ Gl →
    mean * massFlagLatticeZero ≤ nM * nS * mM * mS * Gl →
    mM ≤ massks * de ^ (k - s) * de ^ (s + 1) → mS ≤ masss * (de * NT) ^ (2 * s) →
    nM ≤ de ^ (1 + lf) → nS ≤ (de * NT) ^ (2 + lf) → Gl ≤ (de * NT) ^ (4 * (2 * s + 1)) →
    massk * NT ^ (k - 1) ≤ massFlagLatticeZero →
    mean ≤ (de / NT) ^ k * (de * NT) ^ ((10 * s + 8 : ℕ) + 2 * lf) * (masss * massks / massk)
def CardSubmodulesOfIndexLePow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (NumberField.RingOfIntegers E) M] [Module.Finite (NumberField.RingOfIntegers E) M]
    [Module.Projective (NumberField.RingOfIntegers E) M] (k j : ℕ), 1 ≤ j →
    finrank (NumberField.RingOfIntegers E) M ≤ k →
    {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.Finite ∧
      ({N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.ncard : ℝ) ≤
        (j : ℝ) ^ ((k : ℝ) + Real.logb 2 (finrank ℚ E))
def CardSubmodulesAndLinearEquivBounds : Prop := Formalism.SLP.SubmoduleCountDed ∧ Formalism.SLP.GlobalBoundRefinements.AutCount
def CardSubgroupsOfIndexLe : Prop := Formalism.SLP.SubgroupIndexCount
def PowPrimeFactorsLengthLe : Prop := Formalism.SLP.OmegaPow
def UnipotentReduce : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (FF : Set E) (N : ℕ) (u : Matrix (Fin N) (Fin N) E),
    (∀ x : E, ∃ a ∈ O, x + a ∈ FF) → (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) →
    ∃ n : Matrix (Fin N) (Fin N) E, (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧
      (∀ i j, n i j ∈ O) ∧ ∀ i j, i < j → (u * n) i j ∈ FF
def LeadingMinorInvariant : Prop :=
  ∀ (R : Type) [CommRing R] (N l : ℕ) (hl : l ≤ N) (Lo W Up : Matrix (Fin N) (Fin N) R),
    (∀ i, Lo i i = 1) → (∀ i j, i < j → Lo i j = 0) → (∀ i, Up i i = 1) →
    (∀ i j, j < i → Up i j = 0) →
    ((Lo * W * Up).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (W.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
def MinorBound : Prop :=
  ∀ (N : ℕ) (A w B : Matrix (Fin N) (Fin N) ℂ) (ρ P : ℝ), 1 ≤ ρ →
    (∀ i j, ‖A i j‖ ≤ ρ) → (∀ i j, ‖B i j‖ ≤ ρ) →
    (∀ (t : ℕ) (I J : Fin t → Fin N), ‖(w.submatrix I J).det‖ ≤ P) →
    ∀ (t : ℕ) (I J : Fin t → Fin N),
      ‖((A * w * B).submatrix I J).det‖ ≤ 4 ^ N * (N.factorial : ℝ) ^ 2 * ρ ^ (2 * N) * P
def MonomialMinor : Prop :=
  ∀ (N : ℕ) (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ) (t : ℕ) (I J : Fin t → Fin N),
    ‖((Matrix.of fun i j => if j = σ i then c i else 0 : Matrix (Fin N) (Fin N) ℂ).submatrix
      I J).det‖ ≤ ∏ i, max 1 ‖c i‖
def BlockScalarBound : Prop :=
  ∀ (t x y : ℝ) (s c : ℕ), 0 < t → 0 < x → 0 < y → c ≤ s → t ^ s = x / y →
    t ^ c ≤ max 1 x * max 1 (1 / y)
def PiProd : Prop :=
  ∀ (ι l : Type) [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (H₂ : ℝ), 1 ≤ H₂ →
    (∀ i ∈ E, ∀ v, 0 < D i v) → (∀ i ∈ E, 1 ≤ ∏ v, D i v) →
    ∏ v, ∏ i ∈ E, (max 1 (D i v) * max 1 (1 / D i v)) ≤
      H₂ ^ (2 * Fintype.card ι * E.card) * size E D H₂ ^ 2
def Transference : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ), 0 < lam →
    (∀ y : E, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → lam ≤ ‖y‖) →
    ∀ x : E, ∃ l ∈ Λ, ‖x - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2
def CoveringO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], (∀ w : NumberField.InfinitePlace E, w.IsComplex) →
    ∀ x : NumberField.InfinitePlace E → ℂ, ∃ a : NumberField.RingOfIntegers E,
      ∀ w, ‖x w - w.embedding (a : E)‖ ≤
        Real.sqrt (finrank ℚ E) * |(NumberField.discr E : ℝ)| ^ (1 / (finrank ℚ E : ℝ))
def DivPowMulPowLe : Prop :=
  ∀ (k : ℕ) (de₀ j₀ t₁ t₂ De NT cf : ℝ), 1 ≤ de₀ → 1 ≤ j₀ → 1 ≤ t₁ → 1 ≤ t₂ → 0 < NT → 0 ≤ cf →
    de₀ * j₀ * t₁ * t₂ ≤ De →
    (de₀ / NT) ^ k * (j₀ * t₁ * t₂) ^ ((k : ℝ) + cf) ≤ (De / NT) ^ k * De ^ cf
def QuadCount : Prop :=
  ∀ De : ℝ, 1 ≤ De →
    {q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De}.Finite ∧
    ({q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De}.ncard : ℝ) ≤ De ^ 4
def EichlerIsometry : Prop :=
  ∀ (R V : Type) [CommRing R] [StarRing R] [AddCommGroup V] [Module R V]
    (h : V →ₗ[R] V →ₗ⋆[R] R), (∀ x y, h y x = star (h x y)) →
    ∀ (u σ : V) (τ : R), h u u = 0 → h u σ = 0 → τ + star τ = h σ σ →
    ∀ x y, h (x - h x σ • u + h x u • σ - (τ * h x u) • u)
        (y - h y σ • u + h y u • σ - (τ * h y u) • u) = h x y
def eichler {R V : Type*} [CommRing R] [StarRing R] [AddCommGroup V] [Module R V]
    (h : V →ₗ[R] V →ₗ⋆[R] R) (u σ : V) (τ : R) (x : V) : V :=
  x - h x σ • u + h x u • σ - (τ * h x u) • u
def EichlerFacts : Prop :=
  ∀ (R V : Type) [CommRing R] [StarRing R] [AddCommGroup V] [Module R V]
    (h : V →ₗ[R] V →ₗ⋆[R] R), (∀ x y, h y x = star (h x y)) →
    ∀ (u σ : V) (τ : R), h u u = 0 → h u σ = 0 → τ + star τ = h σ σ →
    (∀ x, h x u = 0 → h x σ = 0 → eichler h u σ τ x = x) ∧
    (∀ p x', h p u = 0 → h x' u = 0 → h x' σ = 0 →
      eichler h u σ τ (p + x') = p + x' - h p σ • u) ∧
    (∀ x, ∃ c : R, eichler h u σ τ x = x + h x u • σ + c • u) ∧
    (∀ x, eichler h u (-σ) (star τ) (eichler h u σ τ x) = x)
def CentreIsometry : Prop :=
  ∀ (R V : Type) [CommRing R] [StarRing R] [AddCommGroup V] [Module R V]
    (h : V →ₗ[R] V →ₗ⋆[R] R), (∀ x y, h y x = star (h x y)) →
    ∀ (r : ℕ) (e : Fin r → V) (c : Matrix (Fin r) (Fin r) R), (∀ a b, h (e a) (e b) = 0) →
    cᴴ = -c →
    ∀ x y, h (x + ∑ a, ∑ a', (c a a' * h x (e a')) • e a)
        (y + ∑ a, ∑ a', (c a a' * h y (e a')) • e a) = h x y
def CentreFacts : Prop :=
  ∀ (R V : Type) [CommRing R] [StarRing R] [AddCommGroup V] [Module R V]
    (h : V →ₗ[R] V →ₗ⋆[R] R) (r : ℕ) (e : Fin r → V) (c : Matrix (Fin r) (Fin r) R),
    (∀ x, (∀ a, h x (e a) = 0) → x + ∑ a, ∑ a', (c a a' * h x (e a')) • e a = x) ∧
    ∀ (n : ℕ) (f' : Fin n → V) (b : Fin n),
      f' b + ∑ a, ∑ a', (c a a' * h (f' b) (e a')) • e a =
        f' b + ∑ a, ((c * Matrix.of fun a' b' => h (f' b') (e a')) a b) • e a
def HomRestrictIndex : Prop :=
  ∀ (O M X : Type) [CommRing O] [IsDedekindDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (P : Submodule O M), ¬ IsField O → Finite (M ⧸ P) →
    Nat.card ((P →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X P.subtype)) =
      Nat.card (M ⧸ P) ^ finrank O X
def crossGram {K V : Type*} [CommRing K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) {N : ℕ} (f f' : Fin N → V) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b => h (f' b) (f a)
def OmegaNorm : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K), (∀ x y, h y x = star (h x y)) →
    ∀ (r : ℕ) (f f' : Fin (r + 1) → V) (T T' : K) (x w : V) (ζ : K),
    (∀ a b, h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -T else 0) →
    (∀ a b, h (f' a) (f' b) = if a = Fin.last r ∧ b = Fin.last r then -T' else 0) →
    T ≠ 0 → x ∈ Submodule.span K (Set.range fun a : Fin r => f a.castSucc) →
    (∀ a, h w (f a) = 0) →
    ∑ b, (crossGram h f f').adjugate b (Fin.last r) • f' b = x + w + ζ • f (Fin.last r) →
    T * h w w = (crossGram h f f').det * star (crossGram h f f').det -
      T * T' * (((crossGram h f f').submatrix Fin.castSucc Fin.castSucc).det *
        star ((crossGram h f f').submatrix Fin.castSucc Fin.castSucc).det)
def BoxCount : Prop :=
  ∀ (ι : Type) [Fintype ι] (s : ℕ) (Λ : AddSubgroup (ι → EuclideanSpace ℂ (Fin s))) (ν : ℝ)
    (B : ι → ℝ), 0 < ν → (∀ v, 0 < B v) → (∀ x ∈ Λ, x ≠ 0 → ν ≤ ∏ v, ‖x v‖ ^ 2) →
    {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.Finite ∧
      ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.ncard : ℝ) ≤
        9 ^ (s * Fintype.card ι) * (max 1 ((∏ v, B v ^ 2) / ν)) ^ s
def cofVec {R : Type*} [CommRing R] {r : ℕ} (Y : Matrix (Fin r) (Fin (r + 1)) R) (b : Fin (r + 1)) :
    R := (-1) ^ (b : ℕ) * (Y.submatrix id b.succAbove).det
def KernelRowSpace : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Y : Matrix (Fin r) (Fin (r + 1)) R),
    Y *ᵥ cofVec Y = 0 ∧
    ∀ u : Fin (r + 1) → R, ∑ b, u b * cofVec Y b = 0 → ∀ b₀ : Fin (r + 1),
      (Y.submatrix id b₀.succAbove).det • u =
        ((fun c => u (b₀.succAbove c)) ᵥ* (Y.submatrix id b₀.succAbove).adjugate) ᵥ* Y
def MinorExists : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K), Z.det ≠ 0 →
    (Z.submatrix Fin.castSucc id).rank = r ∧
    ∃ b₀ : Fin (r + 1), ((Z.submatrix Fin.castSucc id).submatrix id b₀.succAbove).det ≠ 0
def CofVecAdjugate : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (b : Fin (r + 1)),
    Z.adjugate b (Fin.last r) = (-1) ^ r * cofVec (Z.submatrix Fin.castSucc id) b
def ProjQuotCard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : Type) [AddCommGroup P]
    [Module (NumberField.RingOfIntegers E) P] [Module.Finite (NumberField.RingOfIntegers E) P]
    [Module.Projective (NumberField.RingOfIntegers E) P]
    (I : Ideal (NumberField.RingOfIntegers E)), I ≠ ⊥ →
    Nat.card (P ⧸ (I • (⊤ : Submodule (NumberField.RingOfIntegers E) P))) =
      Ideal.absNorm I ^ finrank (NumberField.RingOfIntegers E) P
def SkewSolution : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (r : ℕ) (Y x : Matrix (Fin r) (Fin (r + 1)) K),
    Y.rank = r →
    (xᴴ * Y + Yᴴ * x = 0 ↔ ∃ Sg : Matrix (Fin r) (Fin r) K, Sgᴴ = -Sg ∧ x = Sg * Y)
def SkewClassCount : Prop :=
  ∀ (A : Type) [AddCommGroup A] (B : AddSubgroup A) (r : ℕ)
    (Sk : AddSubgroup (Matrix (Fin r) (Fin r) A)), B.index ≠ 0 →
    ∃ reps : Finset (Matrix (Fin r) (Fin r) A), (∀ M ∈ reps, M ∈ Sk) ∧
      reps.card ≤ B.index ^ (r ^ 2) ∧ ∀ M ∈ Sk, ∃ M₀ ∈ reps, ∀ i j, (M - M₀) i j ∈ B
def DefiniteAutFinite : Prop :=
  ∀ (N : ℕ) (S : Matrix (Fin N) (Fin N) ℝ), S.PosDef →
    {g : Matrix (Fin N) (Fin N) ℤ |
      (g.map (Int.cast : ℤ → ℝ))ᵀ * S * g.map (Int.cast : ℤ → ℝ) = S}.Finite
def minkowskiNumber (N : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime,
    p ^ (∑ i ∈ Finset.range (N + 1), N / (p ^ i * (p - 1)))
def MinkowskiBound : Prop :=
  ∀ (N : ℕ) (G : Subgroup (GL (Fin N) ℤ)), Finite G → Nat.card G ∣ minkowskiNumber N
def MinkowskiNumberDvd : Prop := ∀ N : ℕ, minkowskiNumber N ∣ (2 * N).factorial
def MinkowskiFactorial : Prop :=
  ∀ (N : ℕ) (G : Subgroup (GL (Fin N) ℤ)), Finite G → Nat.card G ∣ (2 * N).factorial
def ChShBound : Prop :=
  ∀ sh ch : ℝ, 0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → (1 + ch) / sh ≤ 3 * max 1 (1 / sh)
def ShInvPlace : Prop :=
  ∀ sh G T T' Dr : ℝ, 0 < sh → 0 < G → 0 < Dr → 1 ≤ T * T' → G = T * T' * Dr ^ 2 * sh ^ 2 →
    max 1 (1 / sh ^ 2) ≤ T * T' * max 1 (Dr ^ 2) * max 1 (1 / G)
def DegFactorBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (sh ch G Dr : ι → ℝ) (T T' HH : ℝ), 1 ≤ T * T' →
    (∀ v, 0 < sh v ∧ 0 ≤ ch v ∧ ch v ^ 2 = sh v ^ 2 + 1) → (∀ v, 0 < G v) → (∀ v, 0 < Dr v) →
    (∀ v, G v = T * T' * Dr v ^ 2 * sh v ^ 2) → (T * T') ^ Fintype.card ι ≤ HH →
    ∏ v, max 1 (Dr v ^ 2) ≤ HH → ∏ v, max 1 (1 / G v) ≤ HH →
    (∏ v, (1 + ch v) / sh v) ^ 2 ≤ 9 ^ Fintype.card ι * HH ^ 3
def DeNonDegBound : Prop :=
  ∀ (f s : ℕ) (g G₁ G₂ HH₁ HH₂ : ℝ), 2 ≤ g → 0 ≤ G₁ → 0 ≤ G₂ → G₁ ≤ HH₁ → G₂ ≤ HH₂ → 1 ≤ HH₁ →
    1 ≤ HH₂ →
    (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ HH₁ * HH₂ ∧
      (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ (HH₁ * HH₂) ^ 3
def DeDegBound : Prop :=
  ∀ (f s : ℕ) (g T G₁ G₂ K₁ K₂ HH₁ HH₂ : ℝ), 2 ≤ g → 1 ≤ T → 0 ≤ G₁ → 0 ≤ G₂ → G₁ ≤ HH₁ →
    G₂ ≤ HH₂ → 0 ≤ K₁ → 0 ≤ K₂ → K₁ ^ 2 ≤ 9 ^ f * HH₁ ^ 3 → K₂ ^ 2 ≤ 9 ^ f * HH₂ ^ 3 →
    9 ^ f ≤ HH₁ * HH₂ →
    (2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ ≤ (HH₁ * HH₂) ^ 3
def HeightExponentAssembly : Prop :=
  ∀ (s r f : ℕ) (A cf De NT HH : ℝ), 1 ≤ s → 1 ≤ f → 0 ≤ A → 0 ≤ cf → 1 ≤ De → 1 ≤ NT → 1 ≤ HH →
    NT ^ 2 ≤ HH → De ≤ HH ^ 3 →
    (De * NT) ^ (A * (s + cf)) * De ^ (cf + 4) *
        (NT ^ (2 * r) * De ^ r * 9 ^ (s * f) * HH ^ (9 * s + 9 * s * r + 16 * r ^ 2)) ^ 2 *
        ((4 * f * s).factorial : ℝ) ≤
      HH ^ ((4 * A + 60) * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + (4 * A + 60) * cf) *
        (6 * (s : ℝ) * f) ^ (6 * s * f)
def SWArith : Prop :=
  ∀ (k f : ℕ) (de₀ G₀ NT v cf : ℝ), 1 ≤ k → 1 ≤ de₀ → de₀ ≤ G₀ → 1 ≤ NT → 0 < v → 0 ≤ cf →
    (de₀ / NT) ^ (k - 1) * (G₀ / de₀) ^ ((k : ℝ) + cf) *
        (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) ≤
      (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (G₀ / NT) ^ k * NT * G₀ ^ cf
def SublatticeIndex : Prop :=
  ∀ (A : Type) [AddCommGroup A] (M Th La : AddSubgroup A), M ≤ La → Th.relIndex La ≠ 0 →
    Th.relIndex M ≠ 0 ∧ Th.relIndex M ≤ Th.relIndex La
def NProduct : Prop :=
  ∀ (ι : Type) [Fintype ι] (k r : ℕ) (G vt : ι → ℝ) (T g v : ℝ), 1 ≤ k → 0 < T → 0 < g →
    (∀ w, 0 < vt w) → ∏ w, vt w = v ^ Fintype.card ι →
    ∏ w, nv k r (G w) T g (vt w) =
      (Real.exp 1 * Real.pi / (k * v)) ^ (k * Fintype.card ι) *
        ((∏ w, G w) * g⁻¹ ^ ((2 * r + 2) * Fintype.card ι) / T ^ Fintype.card ι) ^ k
def nTot (k f : ℕ) (v G₀ NT : ℝ) : ℝ :=
  (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (G₀ / NT) ^ k
def NonDegRow : Prop :=
  ∀ (k f s : ℕ) (g v NT G₁ G₂ Xi W count A₁ A₂ l₁ l₂ τ : ℝ), 1 ≤ k → 1 ≤ s → 0 < g → 0 < v →
    0 < NT → 0 < G₁ → 0 < G₂ → 0 ≤ Xi → 0 ≤ W → 0 ≤ A₁ → 0 ≤ A₂ → 0 ≤ τ →
    count ≤ ((2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) / NT) ^ k * Xi * W →
    nTot k f v G₁ NT * A₁ ^ 2 ≤ l₁ * τ → nTot k f v G₂ NT * A₂ ^ 2 ≤ l₂ * τ →
    count * A₁ * A₂ ≤ (2 / g) ^ ((s - 1) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
      Xi * W * Real.sqrt (l₁ * l₂) * τ
def DegRow : Prop :=
  ∀ (k f s : ℕ) (g v T NT G₁ G₂ K₁ K₂ Xi W count A₁ A₂ lam₁ lam₂ : ℝ), 1 ≤ k → 2 ≤ s → 0 < g →
    0 < v → 0 < T → 0 < NT → 0 < G₁ → 0 < G₂ → 0 < K₁ → 0 < K₂ → 0 ≤ Xi → 0 ≤ W → 0 ≤ A₁ →
    0 ≤ A₂ →
    count ≤ ((2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT) ^ k * Xi * W →
    nTot k f v G₁ NT * A₁ ^ 2 * K₁ ^ (2 * k) * T⁻¹ ^ (k * f) ≤ lam₁ →
    nTot k f v G₂ NT * A₂ ^ 2 * K₂ ^ (2 * k) * T⁻¹ ^ (k * f) ≤ lam₂ →
    count * A₁ * A₂ ≤ (2 / g) ^ ((s - 2) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
      Xi * W * Real.sqrt (lam₁ * lam₂)
def GainQuadratic : Prop :=
  ∀ (k N : ℕ) (b g : ℝ), 1 ≤ k → 2 ≤ b → ((k : ℝ) * b) ^ 8 ≤ g →
    (2 / g) ^ N ≤ Real.exp (-7 * N * Real.log b)
def NonDegTopRows : Prop :=
  ∀ (C : ℝ) (k m f : ℕ) (b v NT : ℝ), 1 ≤ C → 1 ≤ k → 1 ≤ m → 2 ≤ b → 1 ≤ v → v ≤ b →
    (k : ℝ) ≤ b ^ C → 1 ≤ NT → NT ≤ b ^ (C * (m : ℝ) * f) →
    (C * (k : ℝ) ^ 2 * v) ^ (k * f) * (b ^ (C * (m : ℝ) ^ 2 * f) * NT) ^ (C * k) *
        (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * k * (m : ℝ) ^ 2) ≤
      Real.exp (8 * C ^ 2 * (m : ℝ) ^ 4 * k * f * Real.log b)
def bigH (C : ℝ) (m f : ℕ) (b : ℝ) : ℝ := b ^ (C * (m : ℝ) ^ 2 * f)
def XiHyp (C : ℝ) (k m f : ℕ) (b v NT : ℝ) (Xi : ℕ → ℝ) : Prop :=
  (∀ s, 2 ≤ s → s + 2 ≤ k → 0 ≤ Xi s ∧
    ((k : ℝ) * v) ^ (k * f) * Xi s ≤ bigH C m f b ^ C * C ^ (s * k * f)) ∧
  (∀ s, s + 1 = k ∨ s = k → 0 ≤ Xi s ∧
    Xi s ≤ (C * k) ^ (k * f) * (bigH C m f b ^ (C * m) * NT) ^ (C * k))
def Params (C K₀ : ℝ) (k m f : ℕ) (b g v NT Gam : ℝ) : Prop :=
  4 ≤ m ∧ m ≤ f ∧ f ≤ k ∧ 2 ≤ b ∧ ((k : ℝ) * b) ^ 8 ≤ g ∧
  K₀ * (m : ℝ) ^ 5 * f * Real.log b ≤ k ∧ 1 ≤ v ∧ v ≤ b ∧ 1 ≤ NT ∧ NT ≤ b ^ (C * (m : ℝ) * f) ∧
  1 ≤ Gam ∧ Gam ≤ Real.exp (C * (m : ℝ) ^ 5 * f * Real.log b)
def ndRow (C : ℝ) (k m f s : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) : ℝ :=
  (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
    bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam
def NonDegSum : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ),
    Params C K₀ k m f b g v NT Gam → XiHyp C k m f b v NT Xi →
    ∑ s ∈ Finset.Icc 2 k, ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f)
def degRow (C : ℝ) (k m f s : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) : ℝ :=
  (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
    bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam *
    Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f)
def DegSum : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ),
    Params C K₀ k m f b g v NT Gam → XiHyp C k m f b v NT Xi →
    ∑ s ∈ Finset.Icc 2 k, degRow C k m f s b g v Gam Xi ≤
      Real.exp (-((k : ℝ) * f * Real.log k) / 2) * (Gam ^ 2)⁻¹
def ChShPair : Prop :=
  ∀ sh₁ ch₁ sh₂ ch₂ : ℝ, 0 < sh₁ → 0 ≤ ch₁ → ch₁ ^ 2 = sh₁ ^ 2 + 1 → 0 < sh₂ → 0 ≤ ch₂ →
    ch₂ ^ 2 = sh₂ ^ 2 + 1 → (ch₁ + ch₂) / (sh₁ * sh₂) ≤ 4 / (min 1 sh₁ * min 1 sh₂)
def SmallTerm : Prop :=
  ∀ (ι : Type) [Fintype ι] (sh₁ ch₁ sh₂ ch₂ : ι → ℝ) (T T' g : ℝ), 0 < T → 0 < T' → 0 < g →
    (∀ v, 0 < sh₁ v ∧ 0 ≤ ch₁ v ∧ ch₁ v ^ 2 = sh₁ v ^ 2 + 1) →
    (∀ v, 0 < sh₂ v ∧ 0 ≤ ch₂ v ∧ ch₂ v ^ 2 = sh₂ v ^ 2 + 1) →
    Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤ ∏ v, (ch₁ v + ch₂ v) / (sh₁ v * sh₂ v) →
    ∏ v, min (T' * sh₁ v ^ 2) T' ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι ∨
    ∏ v, min (T' * sh₂ v ^ 2) T' ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι
def MinGeom : Prop := ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → min a b ≤ Real.sqrt (a * b)
def SingleRowBound : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k r f : ℕ) (b g v NT Gam : ℝ),
    Params C K₀ k (2 * r + 2) f b g v NT Gam →
    C ^ f * bigH C (2 * r + 2) f b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ 3) * Gam *
        Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) *
        Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f)) ≤
      Real.exp (-((k : ℝ) * f * Real.log k))
def ExpSumLe : Prop :=
  ∀ x : ℝ, 20 ≤ x → Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x) ≤ Real.exp (-x / 3)
def ExpSumLe' : Prop :=
  ∀ A x : ℝ, 1 ≤ A → 6 * Real.log (3 * A) ≤ x →
    A * (Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x)) ≤ Real.exp (-x / 3)
def GainSqrt : Prop :=
  ∀ (k f : ℕ) (b g : ℝ), 1 ≤ k → 1 ≤ b → ((k : ℝ) * b) ^ 8 ≤ g →
    (Real.sqrt g)⁻¹ ^ (k * f) ≤ Real.exp (-4 * ((k : ℝ) * f * Real.log k))
def Threshold : Prop :=
  ∀ (N p : ℕ) (D : Fin N → ℝ) (H₂ : ℝ) (l : Fin N), 0 < H₂ → (∀ i, 0 ≤ D i) → (∀ i, D i ≤ D l) →
    H₂ < D l →
    (H₂ / D l) ^ (2 * p) ≤ (∏ i, max 1 (D i / H₂)) ^ (-(2 * (p : ℝ) / N))
def ThresholdBelow : Prop :=
  ∀ (N : ℕ) (D : Fin N → ℝ) (H₂ : ℝ), 0 < H₂ → (∀ i, D i ≤ H₂) → ∏ i, max 1 (D i / H₂) = 1
def ThresholdP : Prop :=
  ∀ (k r : ℕ) (A cf : ℝ), 1 ≤ A → 0 ≤ cf → cf ≤ 2 * (r : ℝ) + 2 → (2 * r + 2) ^ 3 ≤ k →
    ((r : ℝ) + 1) * (A * ((k : ℝ) * (2 * r + 2) + (2 * (r : ℝ) + 2) ^ 4 + cf) + 3) ≤
      3 * A * k * (2 * (r : ℝ) + 2) ^ 2
def BoxCountO : Prop :=
  ∀ (ι : Type) [Fintype ι] (Λ : AddSubgroup (ι → ℂ)) (B : ι → ℝ), (∀ v, 0 < B v) →
    (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) →
    {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.Finite ∧
      ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.ncard : ℝ) ≤ ∏ v, (1 + 2 * B v) ^ 2 ∧
      ∏ v, (1 + 2 * B v) ^ 2 ≤ 9 ^ Fintype.card ι * ∏ v, max 1 (B v) ^ 2
def LatticeSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (Λ : AddSubgroup (ι → ℂ)) (H₂ : ℝ), 1 ≤ H₂ →
    (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) →
    Summable (fun D : Λ => ∏ v, ((max 1 (‖(D : ι → ℂ) v‖ / H₂)) ^ 3)⁻¹) ∧
      ∑' D : Λ, ∏ v, ((max 1 (‖(D : ι → ℂ) v‖ / H₂)) ^ 3)⁻¹ ≤ (41 * H₂ ^ 2) ^ Fintype.card ι
def LatticeSumTuple : Prop :=
  ∀ (ι : Type) [Fintype ι] (Λ : AddSubgroup (ι → ℂ)) (H₂ : ℝ) (N : ℕ), 1 ≤ H₂ →
    (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) →
    Summable (fun D : Fin N → Λ => ∏ l, ∏ v, ((max 1 (‖(D l : ι → ℂ) v‖ / H₂)) ^ 3)⁻¹) ∧
      ∑' D : Fin N → Λ, ∏ l, ∏ v, ((max 1 (‖(D l : ι → ℂ) v‖ / H₂)) ^ 3)⁻¹ ≤
        (41 * H₂ ^ 2) ^ (Fintype.card ι * N)
def IntegerProductGeOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : NumberField.RingOfIntegers E), a ≠ 0 →
    1 ≤ ∏ w : NumberField.InfinitePlace E, w (a : E) ^ w.mult
def SizeCancel : Prop :=
  ∀ (sz e q : ℝ), 1 ≤ sz → e + 3 ≤ q → sz ^ e * sz ^ (-q) ≤ sz ^ (-3 : ℝ)
def FiniteOrderCongruence : Prop :=
  ∀ (N n : ℕ) (g : ℤ) (A B : Matrix (Fin N) (Fin N) ℤ), 3 ≤ g → 1 ≤ n → A ^ n = 1 →
    A = 1 + g • B → A = 1
end Formalism.HermitianLatticeCounting.LatticeSumBounds


