-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_SubmoduleGeneratorsBound
-- name    : Formalism_FlagUnipotentLattices_SubmoduleGeneratorsBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:06.100775+00:00
-- url     : https://prove2.me/theorems/f17990b5-eb0e-4aa8-b825-f4db93418265
-- title:
--   Submodule Generators Bound
-- statement:
--   Definitions and structural lemmas for Submodule Generators Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/SubmoduleGeneratorsBound.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
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
def SolveBound' : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (r : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (u w : Fin r → V) (c R₀ : ℝ), M.det ≠ 0 → (∀ b a, ‖M⁻¹ b a‖ ≤ c) →
    (∀ a, u a = ∑ b, M a b • w b) → (∀ a, ‖u a‖ ≤ R₀) → ∀ b, ‖w b‖ ≤ r * c * R₀
def SolveBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u w : Fin (n + 1) → V) (R₀ De : ℝ),
    (∀ i j, ‖(M.submatrix (Fin.succAbove i) (Fin.succAbove j)).det‖ ≤ R₀ ^ (2 * n)) → M.det ≠ 0 →
    1 / ‖M.det‖ ≤ De → (∀ a, u a = ∑ b, M a b • w b) → (∀ a, ‖u a‖ ≤ R₀) →
    ∀ b, ‖w b‖ ≤ ((n : ℝ) + 1) * R₀ ^ (2 * n + 1) * De
def OrthCoeffBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (r : ℕ) (e : Fin r → V)
    (X : Fin r → ℂ) (Dr R₀ De R' : ℝ), 0 < Dr → 1 / Dr ≤ De →
    (∀ c c', c ≠ c' → inner ℂ (e c) (e c') = 0) → (∀ c, Dr ≤ ‖e c‖ * R₀ ^ (2 * r - 1)) →
    ‖∑ c, X c • e c‖ ≤ R' → ∀ c, ‖X c‖ ≤ R' * R₀ ^ (2 * r - 1) * De
def Prop3Multiply : Prop :=
  ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De →
    (Real.pi * R₀ ^ (4 * r) * De ^ 2) ^ (r * (r - 1) / 2) *
        (2 * r * R₀ ^ (4 * r - 2) * De ^ 2) ^ (r ^ 2) *
        (Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) *
        (4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r)) * Real.pi ^ (r ^ 2) ≤
      (4 * (r : ℝ)) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2)
def ZetaLeTwo : Prop := ∀ k : ℕ, 2 ≤ k → zetaR k ≤ 2
def FactorialLower : Prop :=
  ∀ k : ℕ, 1 ≤ k → ((k : ℝ) / Real.exp 1) ^ k / k ≤ ((k - 1).factorial : ℝ)
def InvMk' : Prop :=
  ∀ (f k : ℕ) (v : ℝ) (Lv : ℕ → ℝ), 0 < v → 2 ≤ k → ((zetaR k) ^ f)⁻¹ ≤ Lv k →
    (mJ f v Lv k)⁻¹ ≤
      (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (2 * k * Real.sqrt (2 * v)) ^ f
def InvMkTwo : Prop :=
  ∀ (f k : ℕ) (v : ℝ) (Lv : ℕ → ℝ), 1 ≤ v → 2 ≤ k → ((zetaR k) ^ f)⁻¹ ≤ Lv k →
    (mJ f v Lv k)⁻¹ ≤ (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (2 * k * (2 * v)) ^ f
def SubmoduleGeneratorsBound : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M] [Finite M] (e : ℕ)
    (v : Fin e → M), Submodule.span R (Set.range v) = ⊤ →
    ∀ N : Submodule R M, ∃ t : Fin e → M, Submodule.span R (Set.range t) = N
def HomCountLePowGenerators : Prop :=
  ∀ (R M M' : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [Finite M'] (e : ℕ) (v : Fin e → M), Submodule.span R (Set.range v) = ⊤ →
    Finite (M →ₗ[R] M') ∧ Nat.card (M →ₗ[R] M') ≤ Nat.card M' ^ e
def EndCountLePowGenerators : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (e : ℕ) (v : Fin e → M),
    Submodule.span R (Set.range v) = ⊤ → Nat.card (M →ₗ[R] M) ≤ Nat.card M ^ e
def CoveringO' : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], (∀ w : NumberField.InfinitePlace E, w.IsComplex) →
    ∀ x : NumberField.InfinitePlace E → ℂ, ∃ a : NumberField.RingOfIntegers E,
      ∀ w, ‖x w - w.embedding (a : E)‖ ≤
        Real.sqrt ((finrank ℚ E : ℝ) / 2) / 2 * |(NumberField.discr E : ℝ)| ^ (1 / (finrank ℚ E : ℝ))
def HadamardEntries : Prop :=
  ∀ (t : ℕ) (M : Matrix (Fin t) (Fin t) ℂ) (ρ : ℝ), (∀ i j, ‖M i j‖ ≤ ρ) →
    ‖M.det‖ ≤ (Real.sqrt t * ρ) ^ t
def MinorBoundH : Prop :=
  ∀ (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ) (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ) (ρ P : ℝ),
    1 ≤ ρ → (∀ i j, ‖A i j‖ ≤ ρ) → (∀ i j, ‖B i j‖ ≤ ρ) →
    (∀ (t : ℕ) (I J : Fin t → Fin N),
      ‖((Matrix.of fun i j => if j = σ i then c i else 0 : Matrix (Fin N) (Fin N) ℂ).submatrix
        I J).det‖ ≤ P) →
    ∀ (t : ℕ) (I J : Fin t → Fin N),
      ‖((A * (Matrix.of fun i j => if j = σ i then c i else 0 : Matrix (Fin N) (Fin N) ℂ) *
        B).submatrix I J).det‖ ≤ (2 * N * ρ ^ 2) ^ N * P
def CHSize : Prop :=
  ∀ (r f : ℕ) (rd b C : ℝ), 0 < C → 1 ≤ b → 2 * r + 2 ≤ f → (f : ℝ) ≤ b ^ (2 / C) → 0 < rd →
    Real.log rd ≤ Real.log b / C →
    (2 * ((r : ℝ) + 1) * (Real.sqrt f * rd / 2) ^ 2) ^ (r + 1) =
        ((2 * (r : ℝ) + 2) * f * rd ^ 2 / 4) ^ (r + 1) ∧
      (2 * ((r : ℝ) + 1) * (Real.sqrt f * rd / 2) ^ 2) ^ (r + 1) ≤ b ^ (3 * (2 * (r : ℝ) + 2) / C)
def PRatio : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → ℝ), (∀ v, 0 < x v) →
    ∏ v, max 1 (x v) = (∏ v, x v) * ∏ v, max 1 (1 / x v)
def LemmaHd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], (∀ w : NumberField.InfinitePlace E, w.IsComplex) →
    ∀ x : E, x ≠ 0 → 1 ≤ |(Algebra.norm ℚ x : ℚ)| →
      ∏ w : NumberField.InfinitePlace E, max 1 (w x⁻¹) ≤ ∏ w : NumberField.InfinitePlace E, max 1 (w x)
def LemmaHe : Prop :=
  ∀ (ι l : Type) [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (mu : ι → ℝ) (H₂ cH : ℝ), 1 ≤ H₂ →
    1 ≤ cH → (∀ i ∈ E, ∀ v, 0 < D i v) → (∀ i ∈ E, 1 ≤ ∏ v, D i v) → (∀ v, 0 ≤ mu v) →
    (∀ v, mu v ≤ cH * ∏ i ∈ E, (max 1 (D i v) * max 1 (1 / D i v))) →
    ∏ v, max 1 (mu v) ≤
        cH ^ Fintype.card ι * H₂ ^ (2 * Fintype.card ι * E.card) * size E D H₂ ^ 2 ∧
      ∏ v, mu v ^ 2 ≤
        cH ^ (2 * Fintype.card ι) * H₂ ^ (4 * Fintype.card ι * E.card) * size E D H₂ ^ 4
def BoxCount' : Prop :=
  ∀ (ι : Type) [Fintype ι] (s : ℕ) (Λ : AddSubgroup (ι → EuclideanSpace ℂ (Fin s))) (ν : ℝ)
    (B : ι → ℝ), 0 < ν → (∀ v, 0 < B v) → (∀ x ∈ Λ, x ≠ 0 → ν ≤ ∏ v, ‖x v‖ ^ 2) →
    {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.Finite ∧
      ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.ncard : ℝ) ≤
        (1 + 2 * ((∏ v, B v ^ 2) / ν) ^ (1 / (2 * (Fintype.card ι : ℝ)))) ^
          (2 * s * Fintype.card ι) ∧
      (1 + 2 * ((∏ v, B v ^ 2) / ν) ^ (1 / (2 * (Fintype.card ι : ℝ)))) ^ (2 * s * Fintype.card ι) ≤
        9 ^ (s * Fintype.card ι) * (max 1 ((∏ v, B v ^ 2) / ν)) ^ s
def PackingSphere : Prop :=
  ∀ (ι : Type) [Fintype ι] (s : ℕ) (Λ : AddSubgroup (ι → EuclideanSpace ℂ (Fin s))) (μ ρ : ℝ)
    (ρv : ι → ℝ), 0 < μ → 0 < ρ → (∀ v, 0 < ρv v) → ρ ^ Fintype.card ι = ∏ v, ρv v →
    (∀ x ∈ Λ, x ≠ 0 → μ ^ Fintype.card ι ≤ ∏ v, ‖x v‖ ^ 2) →
    {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ^ 2 = ρv v}.Finite ∧
      ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ^ 2 = ρv v}.ncard : ℝ) ≤
        (max 1 (9 * ρ / μ)) ^ (s * Fintype.card ι)
def LatticeSumTuple' : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ℕ) (Λ : Fin N → AddSubgroup (ι → ℂ)) (H₂ : Fin N → ℝ),
    (∀ l, 1 ≤ H₂ l) → (∀ l, ∀ x ∈ Λ l, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) →
    Summable (fun D : (l : Fin N) → Λ l =>
        ∏ l, ∏ v, ((max 1 (‖(D l : ι → ℂ) v‖ / H₂ l)) ^ 3)⁻¹) ∧
      ∑' D : (l : Fin N) → Λ l, ∏ l, ∏ v, ((max 1 (‖(D l : ι → ℂ) v‖ / H₂ l)) ^ 3)⁻¹ ≤
        ∏ l, (41 * H₂ l ^ 2) ^ Fintype.card ι
def sizeT {ι : Type*} [Fintype ι] {N : ℕ} (H₂ : Fin N → ℝ) (D : Fin N → ι → ℂ) : ℝ :=
  ∏ l, ∏ v, max 1 (‖D l v‖ / H₂ l)
def LemmaSArith : Prop :=
  ∀ (N : ℕ) (H a sz e₁ e₂ q : ℝ), 0 < H → 1 ≤ sz → 4 * (e₁ + (N : ℝ) ^ 2) + e₂ + 3 ≤ q →
    (H ^ a * sz ^ 4) ^ (e₁ + (N : ℝ) ^ 2) * sz ^ (e₂ - q) ≤
      H ^ (a * (e₁ + (N : ℝ) ^ 2)) * sz ^ (-3 : ℝ)
def LemmaS : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ℕ) (Λ : Fin N → AddSubgroup (ι → ℂ)) (H₂ : Fin N → ℝ)
    (H a e₁ e₂ q : ℝ) (Z : Type) (D : Z → (l : Fin N) → Λ l),
    (∀ l, 1 ≤ H₂ l) → (∀ l, ∀ x ∈ Λ l, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) → 0 < H →
    4 * (e₁ + (N : ℝ) ^ 2) + e₂ + 3 ≤ q →
    (∀ d : (l : Fin N) → Λ l, {z | D z = d}.Finite ∧
      ({z | D z = d}.ncard : ℝ) ≤
        (9 ^ Fintype.card ι * (H ^ a * sizeT H₂ (fun l => (d l : ι → ℂ)) ^ 4)) ^ (N ^ 2)) →
    Summable (fun z : Z => (H ^ a * sizeT H₂ (fun l => (D z l : ι → ℂ)) ^ 4) ^ e₁ *
        sizeT H₂ (fun l => (D z l : ι → ℂ)) ^ (e₂ - q)) ∧
      ∑' z : Z, (H ^ a * sizeT H₂ (fun l => (D z l : ι → ℂ)) ^ 4) ^ e₁ *
          sizeT H₂ (fun l => (D z l : ι → ℂ)) ^ (e₂ - q) ≤
        9 ^ (Fintype.card ι * N ^ 2) * H ^ (a * (e₁ + (N : ℝ) ^ 2)) *
          ∏ l, (41 * H₂ l ^ 2) ^ Fintype.card ι
def TailProbabilityTotal : Prop :=
  ∀ (k f m : ℕ) (b : ℝ), 1 ≤ b → 2 ≤ m → 20 ≤ (k : ℝ) * f * Real.log k →
    5 * ((k : ℝ) * b) ^ (-(5 * (k : ℝ) * f)) + 2 * Real.exp (-(1 / 2) * ((k : ℝ) * f * Real.log k)) +
        4 * Real.exp (-2 * ((m : ℝ) - 1) * k * f * (Real.log b + Real.log k)) ≤
      Real.exp (-(1 / 3) * ((k : ℝ) * f * Real.log k))
def ThresholdPChain : Prop :=
  ∀ (k r : ℕ) (A cf : ℝ), 1 ≤ A → 0 ≤ cf → cf ≤ 2 * (r : ℝ) + 2 → (2 * r + 2) ^ 3 ≤ k →
    ((r : ℝ) + 1) * (A * ((k : ℝ) * (2 * r + 2) + (2 * (r : ℝ) + 2) ^ 4 + cf) + 3) ≤
        A * (2 * (r : ℝ) + 2) * ((k : ℝ) * (2 * r + 2) + (2 * (r : ℝ) + 2) ^ 4 + (2 * (r : ℝ) + 2)) +
          3 * (2 * (r : ℝ) + 2) ∧
      A * (2 * (r : ℝ) + 2) * ((k : ℝ) * (2 * r + 2) + (2 * (r : ℝ) + 2) ^ 4 + (2 * (r : ℝ) + 2)) +
          3 * (2 * (r : ℝ) + 2) ≤ 3 * A * k * (2 * (r : ℝ) + 2) ^ 2 + 3 * (2 * (r : ℝ) + 2) ∧
      3 * A * k * (2 * (r : ℝ) + 2) ^ 2 + 3 * (2 * (r : ℝ) + 2) ≤ 4 * A * k * (2 * (r : ℝ) + 2) ^ 2
def ThresholdPFour : Prop :=
  ∀ (k r : ℕ) (A cf : ℝ), 1 ≤ A → 0 ≤ cf → cf ≤ 2 * (r : ℝ) + 2 → (2 * r + 2) ^ 3 ≤ k →
    ((r : ℝ) + 1) * (A * ((k : ℝ) * (2 * r + 2) + (2 * (r : ℝ) + 2) ^ 4 + cf) + 3) ≤
      4 * A * k * (2 * (r : ℝ) + 2) ^ 2
def SkewVolArith : Prop :=
  ∀ (r : ℕ) (X : ℝ), 0 ≤ X →
    (Real.pi * X ^ 2) ^ (r * (r - 1) / 2) * (2 * X) ^ r ≤ (2 * X) ^ (r ^ 2)
def VolumeStirling : Prop :=
  ∀ d r : ℕ, r ≤ d →
    Real.pi ^ (r * d) / ((d - r).factorial : ℝ) ^ r ≤
      Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((d - r : ℕ) : ℝ)) ^ (r * (d - r))
def VolumeExtra : Prop :=
  ∀ (r j : ℕ) (y R' : ℝ), 0 ≤ y → y ≤ R' ^ r → Real.pi ≤ (j : ℝ) + 1 →
    (2 * y) ^ (2 * (j + 1)) * Real.pi ^ (r * (r + j + 1)) / ((j + 1).factorial : ℝ) ^ r =
        (2 * y) ^ (2 * j) * Real.pi ^ (r * (r + j)) / (j.factorial : ℝ) ^ r *
          ((2 * y) ^ 2 * (Real.pi / ((j : ℝ) + 1)) ^ r) ∧
      (2 * y) ^ 2 * (Real.pi / ((j : ℝ) + 1)) ^ r ≤ 4 * R' ^ (2 * r)
def GLLift : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
    ∀ (j : ℕ) (g : Matrix (Fin j) (Fin j) (R ⧸ I)), IsUnit g.det →
      ∃ g' : Matrix (Fin j) (Fin j) R, IsUnit g'.det ∧ g'.map (Ideal.Quotient.mk I) = g
def UnimodularFunctional : Prop :=
  ∀ (R L : Type) [CommRing R] [StarRing R] [AddCommGroup L] [Module R L]
    (h : L →ₗ[R] L →ₗ⋆[R] R), (∀ φ : L →ₗ[R] R, ∃ v, ∀ x, φ x = h x v) →
    ∀ M₀ M₁ : Submodule R L, IsCompl M₀ M₁ →
    ∀ φ : M₀ →ₗ[R] R, ∃ v : L, ∀ x : M₀, φ x = h (x : L) v
def FunctionalIndex : Prop :=
  ∀ (R L : Type) [CommRing R] [StarRing R] [AddCommGroup L] [Module R L]
    (h : L →ₗ[R] L →ₗ⋆[R] R) (M₀ L₀ : Submodule R L) (z : L),
    (∀ φ : M₀ →ₗ[R] R, ∃ v : L, ∀ x : M₀, φ x = h (x : L) v) → (∀ x ∈ M₀, h x z = 0) →
    (L₀ ⊔ Submodule.span R {z}).toAddSubgroup.index ≠ 0 →
    ∃ reps : Finset L, reps.card ≤ (L₀ ⊔ Submodule.span R {z}).toAddSubgroup.index ∧
      ∀ φ : M₀ →ₗ[R] R, ∃ ρ ∈ reps, ∃ v ∈ L₀, ∀ x : M₀, φ x = h (x : L) (v + ρ)
def MonomialLeadingMinor : Prop :=
  ∀ (N l : ℕ) (hl : l ≤ N) (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ),
    ((∃ i : Fin N, (i : ℕ) < l ∧ l ≤ (σ i : ℕ)) →
      ((Matrix.of fun i j => if j = σ i then c i else 0 : Matrix (Fin N) (Fin N) ℂ).submatrix
        (Fin.castLE hl) (Fin.castLE hl)).det = 0) ∧
    ((∀ i : Fin N, (i : ℕ) < l → (σ i : ℕ) < l) →
      ‖((Matrix.of fun i j => if j = σ i then c i else 0 : Matrix (Fin N) (Fin N) ℂ).submatrix
        (Fin.castLE hl) (Fin.castLE hl)).det‖ = ∏ i : Fin l, ‖c (Fin.castLE hl i)‖)
def BlockScalarRatio : Prop :=
  ∀ (N l' l : ℕ) (hl' : l' ≤ l) (hl : l ≤ N) (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ) (t : ℂ),
    (∀ i : Fin N, (i : ℕ) < l' → (σ i : ℕ) < l') → (∀ i : Fin N, (i : ℕ) < l → (σ i : ℕ) < l) →
    (∀ i : Fin N, l' ≤ (i : ℕ) → (i : ℕ) < l → c i = t) →
    ‖((Matrix.of fun i j => if j = σ i then c i else 0 : Matrix (Fin N) (Fin N) ℂ).submatrix
        (Fin.castLE hl) (Fin.castLE hl)).det‖ =
      ‖((Matrix.of fun i j => if j = σ i then c i else 0 : Matrix (Fin N) (Fin N) ℂ).submatrix
        (Fin.castLE (hl'.trans hl)) (Fin.castLE (hl'.trans hl))).det‖ * ‖t‖ ^ (l - l')
def LemmaHf : Prop :=
  ∀ (ι l : Type) [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (G : ι → ℝ) (H₂ : ℝ) (l₀ : l), 1 ≤ H₂ →
    l₀ ∈ E → (∀ v, 0 ≤ D l₀ v) → (∀ v, 0 < G v) → 1 ≤ ∏ v, G v → (∀ v, G v ≤ D l₀ v ^ 2) →
    ∏ v, max 1 (G v) ≤ (∏ v, max 1 (D l₀ v)) ^ 2 ∧
      ∏ v, max 1 (1 / G v) ≤ (∏ v, max 1 (D l₀ v)) ^ 2 ∧
      ∏ v, G v ≤ (∏ v, max 1 (D l₀ v)) ^ 2 ∧
      (∏ v, max 1 (D l₀ v)) ^ 2 ≤ H₂ ^ (2 * Fintype.card ι) * size E D H₂ ^ 2
def SWClassArith : Prop :=
  ∀ (f k m : ℕ) (hE rd b cf A : ℝ), 2 ≤ b → 1 ≤ m → 1 ≤ rd → rd ≤ b → 0 ≤ cf → cf ≤ A * m →
    (k : ℝ) ≤ b → hE ≤ rd ^ ((f : ℝ) * (1 + cf)) →
    hE * 2 ^ f * (2 * k * Real.sqrt rd) ^ f ≤ b ^ ((A + 5) * m * f)
def RhoBound : Prop :=
  ∀ (f : ℕ) (rd b : ℝ), 1 ≤ b → (f : ℝ) ≤ b → 0 ≤ rd → rd ≤ b →
    max 1 (Real.sqrt f * rd / 2) ≤ b ^ 2
def R2iv : Prop :=
  ∀ (ι l : Type) [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (r : ℕ) (b ρ H₂ : ℝ), 1 ≤ H₂ →
    2 * (r : ℝ) + 2 ≤ b → max 1 ρ ≤ b ^ 2 → E.card ≤ r + 1 → (∀ i ∈ E, ∀ v, 0 < D i v) →
    (∀ i ∈ E, 1 ≤ ∏ v, D i v) →
    ∏ v, (max 1 (4 ^ (r + 1) * ((r + 1).factorial : ℝ) ^ 2 * (max 1 ρ) ^ (2 * (r + 1)) *
        ∏ i ∈ E, (max 1 (D i v) * max 1 (1 / D i v)))) ^ 2 ≤
      b ^ (12 * (2 * r + 2) * Fintype.card ι) * H₂ ^ (4 * Fintype.card ι * (r + 1)) *
        size E D H₂ ^ 4
def MatrixBoxCount : Prop :=
  ∀ (ι : Type) [Fintype ι] (Λ : AddSubgroup (ι → ℂ)) (B : ι → ℝ) (N : ℕ), (∀ v, 0 < B v) →
    (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) →
    {Z : Matrix (Fin N) (Fin N) (ι → ℂ) | ∀ a b, Z a b ∈ Λ ∧ ∀ v, ‖Z a b v‖ ≤ B v}.Finite ∧
      ({Z : Matrix (Fin N) (Fin N) (ι → ℂ) | ∀ a b, Z a b ∈ Λ ∧ ∀ v, ‖Z a b v‖ ≤ B v}.ncard : ℝ) ≤
        (9 ^ Fintype.card ι * ∏ v, max 1 (B v) ^ 2) ^ (N ^ 2)
def IsometryInverseAdjugate : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (N : ℕ) (Z a a' : Matrix (Fin N) (Fin N) K), Z.det ≠ 0 →
    aᴴ * Z * a' = Z → (aᴴ)⁻¹ - 1 = (Z.det)⁻¹ • (Z * (a' - 1) * Z.adjugate)
def PowDivFactorial : Prop :=
  ∀ (O : Type) [CommRing O] (aa : Ideal O) (r i n : ℕ) (ξ : Matrix (Fin n) (Fin n) O),
    (∀ a b, ξ a b ∈ Ideal.span {(r.factorial : O)} * aa) → 1 ≤ i → i ≤ r →
    ∃ y : Matrix (Fin n) (Fin n) O, (∀ a b, y a b ∈ Ideal.span {(r.factorial : O)} * aa) ∧
      (i.factorial : O) • y = ξ ^ i
def PowDivIndex : Prop :=
  ∀ (O : Type) [CommRing O] (aa : Ideal O) (r i n : ℕ) (u : Matrix (Fin n) (Fin n) O),
    (∀ a b, u a b ∈ Ideal.span {(r.factorial : O)} * aa) → 1 ≤ i → i ≤ r →
    ∃ y : Matrix (Fin n) (Fin n) O, (∀ a b, y a b ∈ Ideal.span {(r.factorial : O)} * aa) ∧
      (i : O) • y = u ^ i
def IdealNormPowerBound : Prop :=
  ∀ (f N de q : ℕ) (HH c rd Na : ℝ), 1 ≤ HH → 1 ≤ c → 2 ≤ rd → 0 ≤ Na → Na ≤ HH ^ 5 →
    2 * de ≤ N ^ 2 → 2 * q ≤ N ^ 2 →
    (c ^ (2 * f) * Na) ^ de * HH ^ (3 * q) ≤ c ^ (f * N ^ 2) * HH ^ (4 * N ^ 2) ∧
      (c ^ (2 * f) * Na) ^ de * ((rd / 2) ^ (f * de) * HH ^ (3 * q)) ≤
        HH ^ (6 * N ^ 2) * (c ^ 2 * rd) ^ (f * N ^ 2)
end Formalism.HermitianLatticeCounting.LatticeSumBounds


