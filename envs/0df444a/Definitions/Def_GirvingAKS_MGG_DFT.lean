-- Prove2me | Definitions.Def_GirvingAKS_MGG_DFT
-- name    : GirvingAKS_MGG_DFT
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:33.693932+00:00
-- url     : https://prove2.me/theorems/04244e98-0ac2-48cc-9d4b-fbdb3fa39d4e
-- title:
--   AKS sorting networks (Seiferas port) — 2D Discrete Fourier Transform for MGG Spectral Analysis
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/MGG/DFT.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Provides the DFT bridge connecting real-space inner products on `(Z/nZ)²` to Fourier-space bounds, used to prove `mgg_rayleigh_bound` in `Spectral.lean`.
--
--   - `char_ortho_1d`: character orthogonality
--   - `fin_char_delta`: Kronecker delta identity
--   - `parseval_2d`: Parseval's identity `∑_α |f̂(α)|² = n² · ∑_v f(v)²`
--   - `plancherel_2d`: Plancherel's identity (cross terms)
--   - `corr_pair1`, `corr_pair2`: correlation identities
--
--   - Jimbo & Maruoka (1987), discrete Fourier analysis on `(Z/nZ)²`
--   - Boppana's simplification (in Linial–Wigderson lecture notes, Chapter 7)
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/DFT.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_MGG_Defs
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/MGG/DFT.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # 2D Discrete Fourier Transform for MGG Spectral Analysis

  Provides the DFT bridge connecting real-space inner products on `(Z/nZ)²`
  to Fourier-space bounds, used to prove `mgg_rayleigh_bound` in `Spectral.lean`.

  ## Main Results

  - `char_ortho_1d`: character orthogonality
  - `fin_char_delta`: Kronecker delta identity
  - `parseval_2d`: Parseval's identity `∑_α |f̂(α)|² = n² · ∑_v f(v)²`
  - `plancherel_2d`: Plancherel's identity (cross terms)
  - `corr_pair1`, `corr_pair2`: correlation identities

  ## References

  - Jimbo & Maruoka (1987), discrete Fourier analysis on `(Z/nZ)²`
  - Boppana's simplification (in Linial–Wigderson lecture notes, Chapter 7)
-/


set_option maxHeartbeats 3200000

section

open Complex BigOperators Finset Real

/-! **Primitive nth Root of Unity** -/

/-- The primitive nth root of unity `ω = exp(2πi/n)`. -/
noncomputable def ω (n : ℕ) : ℂ := Complex.exp (2 * ↑π * I / ↑n)

theorem ω_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) : IsPrimitiveRoot (ω n) n :=
  Complex.isPrimitiveRoot_exp n hn

theorem ω_norm (n : ℕ) (hn : n ≠ 0) : ‖ω n‖ = 1 :=
  (ω_isPrimitiveRoot n hn).norm'_eq_one hn

theorem ω_ne_zero (n : ℕ) (hn : n ≠ 0) : ω n ≠ 0 := by
  intro h; have := ω_norm n hn; rw [h, norm_zero] at this; exact one_ne_zero this.symm

theorem conj_ω_zpow (n : ℕ) (hn : n ≠ 0) (a : ℤ) :
    starRingEnd ℂ (ω n ^ a) = ω n ^ (-a) := by
  rw [map_zpow₀, ← Complex.inv_eq_conj (ω_norm n hn), zpow_neg, inv_zpow]


/-! **1D Character Orthogonality** -/

/-- Character orthogonality on `Z/nZ`: `∑_{v < n} (ω^a)^v = n` if `n | a`, else `0`. -/
theorem char_ortho_1d (n : ℕ) (hn : n ≠ 0) (a : ℤ) :
    ∑ v : Fin n, (ω n ^ a) ^ (v : ℕ) =
    if (n : ℤ) ∣ a then (n : ℂ) else 0 := by
  split
  · rename_i h
    simp [((ω_isPrimitiveRoot n hn).zpow_eq_one_iff_dvd a).mpr h, Finset.sum_const]
  · rename_i h
    have hne : ω n ^ a ≠ 1 := by
      rwa [Ne, (ω_isPrimitiveRoot n hn).zpow_eq_one_iff_dvd a]
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hne]
    have : (ω n ^ a) ^ n = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          (ω_isPrimitiveRoot n hn).pow_eq_one, one_zpow]
    simp [this]


/-! **Kronecker Delta Identities** -/

/-- `n | (u - v)` as integers iff `u = v` for `u v : Fin n`. -/
theorem fin_dvd_sub_iff (n : ℕ) (u v : Fin n) :
    ((n : ℤ) ∣ (↑u.val - ↑v.val)) ↔ u = v := by
  constructor
  · intro ⟨k, hk⟩
    have hu := u.isLt; have hv := v.isLt; ext
    suffices h : (↑u.val : ℤ) - ↑v.val = 0 by omega
    suffices k = 0 by rw [this] at hk; linarith
    by_contra hk0
    rcases ne_iff_lt_or_gt.mp hk0 with hlt | hgt
    · linarith [show (n : ℤ) * k ≤ -(n : ℤ) from by nlinarith]
    · linarith [show (n : ℤ) ≤ (n : ℤ) * k from by nlinarith]
  · rintro rfl; simp

/-- 1D Kronecker delta: `∑_α ω^{α(u-v)} = n · δ_{u,v}`. -/
theorem fin_char_delta (n : ℕ) (hn : n ≠ 0) (u v : Fin n) :
    ∑ α : Fin n, ω n ^ ((α : ℤ) * ((u : ℤ) - (v : ℤ))) =
    if u = v then (n : ℂ) else 0 := by
  conv_lhs => arg 2; ext α; rw [mul_comm, zpow_mul, zpow_natCast]
  rw [char_ortho_1d n hn]; simp only [fin_dvd_sub_iff]


/-! **2D Discrete Fourier Transform** -/

/-- The 2D DFT: `f̂(α₁,α₂) = ∑_{v₁,v₂} f(v₁,v₂) · ω^{-(α₁·v₁ + α₂·v₂)}`. -/
noncomputable def dft2d (n : ℕ) (g : Fin n → Fin n → ℝ) (α₁ α₂ : Fin n) : ℂ :=
  ∑ v₁ : Fin n, ∑ v₂ : Fin n,
    (g v₁ v₂ : ℂ) * ω n ^ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val) : ℤ)

/-- DFT at `(0,0)` equals the sum of all values. -/
theorem dft2d_zero (n : ℕ) (g : Fin n → Fin n → ℝ) (hn : 0 < n) :
    dft2d n g ⟨0, hn⟩ ⟨0, hn⟩ = ↑(∑ v₁ : Fin n, ∑ v₂ : Fin n, g v₁ v₂) := by
  unfold dft2d; simp [zpow_zero]


/-! **1D DFT and Parseval** -/

/-- 1D DFT for complex-valued functions: `ĉ(α) = ∑_v c(v) · ω^{-αv}`. -/
noncomputable def dft1d (n : ℕ) (c : Fin n → ℂ) (α : Fin n) : ℂ :=
  ∑ v : Fin n, c v * ω n ^ (-(↑α.val * ↑v.val : ℤ))

/-- Equation lemma for folding `dft1d` back from an expanded sum. -/
theorem dft1d_unfold (n : ℕ) (c : Fin n → ℂ) (α : Fin n) :
    dft1d n c α = ∑ v : Fin n, c v * ω n ^ (-(↑α.val * ↑v.val : ℤ)) := rfl

/-- 1D Parseval (complex): `∑_α ĉ(α) · conj(ĉ(α)) = n · ∑_v c(v) · conj(c(v))`. -/
theorem parseval_1d_complex (n : ℕ) (hn : n ≠ 0) (c : Fin n → ℂ) :
    ∑ α : Fin n, dft1d n c α * starRingEnd ℂ (dft1d n c α) =
    ↑n * ∑ v : Fin n, c v * starRingEnd ℂ (c v) := by
  simp only [dft1d, map_sum, map_mul, conj_ω_zpow n hn, neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Rearrange and combine ω powers
  have hrw : ∀ (α v u : Fin n),
    c v * ω n ^ (-(↑α.val * ↑v.val : ℤ)) *
    ((starRingEnd ℂ) (c u) * ω n ^ (↑α.val * ↑u.val : ℤ)) =
    (c v * (starRingEnd ℂ) (c u)) *
    ω n ^ ((↑α.val : ℤ) * (↑u.val - ↑v.val)) := by
    intro α v u
    rw [show (-(↑α.val * ↑v.val : ℤ)) = -(↑α.val : ℤ) * ↑v.val from by ring,
        show (↑α.val * ↑u.val : ℤ) = (↑α.val : ℤ) * ↑u.val from by ring,
        show ((↑α.val : ℤ) * (↑u.val - ↑v.val)) =
          -(↑α.val : ℤ) * ↑v.val + (↑α.val : ℤ) * ↑u.val from by ring,
        zpow_add₀ (ω_ne_zero n hn)]; ring
  simp_rw [hrw]
  -- Swap sums: ∑_α ∑_v ∑_u → ∑_v ∑_u ∑_α
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  -- Factor c(v)*conj(c(u)) out of α-sum, apply character orthogonality
  simp_rw [← Finset.mul_sum]
  simp_rw [fin_char_delta n hn, mul_ite, mul_zero,
           Finset.sum_ite_eq' univ, Finset.mem_univ, if_true]
  -- Factor out n
  simp_rw [show ∀ v : Fin n, c v * starRingEnd ℂ (c v) * (↑n : ℂ) =
    ↑n * (c v * starRingEnd ℂ (c v)) from by intros; ring]
  rw [← Finset.mul_sum]

/-- 1D Plancherel (complex, cross terms): `∑_α ĉ(α) · conj(d̂(α)) = n · ∑_v c(v) · conj(d(v))`. -/
theorem plancherel_1d_complex (n : ℕ) (hn : n ≠ 0) (c d : Fin n → ℂ) :
    ∑ α : Fin n, dft1d n c α * starRingEnd ℂ (dft1d n d α) =
    ↑n * ∑ v : Fin n, c v * starRingEnd ℂ (d v) := by
  simp only [dft1d, map_sum, map_mul, conj_ω_zpow n hn, neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hrw : ∀ (α v u : Fin n),
    c v * ω n ^ (-(↑α.val * ↑v.val : ℤ)) *
    ((starRingEnd ℂ) (d u) * ω n ^ (↑α.val * ↑u.val : ℤ)) =
    (c v * (starRingEnd ℂ) (d u)) *
    ω n ^ ((↑α.val : ℤ) * (↑u.val - ↑v.val)) := by
    intro α v u
    rw [show (-(↑α.val * ↑v.val : ℤ)) = -(↑α.val : ℤ) * ↑v.val from by ring,
        show (↑α.val * ↑u.val : ℤ) = (↑α.val : ℤ) * ↑u.val from by ring,
        show ((↑α.val : ℤ) * (↑u.val - ↑v.val)) =
          -(↑α.val : ℤ) * ↑v.val + (↑α.val : ℤ) * ↑u.val from by ring,
        zpow_add₀ (ω_ne_zero n hn)]; ring
  simp_rw [hrw]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [fin_char_delta n hn, mul_ite, mul_zero,
           Finset.sum_ite_eq' univ, Finset.mem_univ, if_true]
  simp_rw [show ∀ v : Fin n, c v * starRingEnd ℂ (d v) * (↑n : ℂ) =
    ↑n * (c v * starRingEnd ℂ (d v)) from by intros; ring]
  rw [← Finset.mul_sum]

/-- 2D DFT factors as iterated 1D: `f̂(α₁,α₂) = dft1d(v₂ ↦ dft1d(v₁ ↦ g(v₁,v₂), α₁), α₂)`. -/
theorem dft2d_eq_iterated_dft1d (n : ℕ) (hn : n ≠ 0) (g : Fin n → Fin n → ℝ) (α₁ α₂ : Fin n) :
    dft2d n g α₁ α₂ =
    dft1d n (fun v₂ => ∑ v₁ : Fin n, ↑(g v₁ v₂) * ω n ^ (-(↑α₁.val * ↑v₁.val : ℤ))) α₂ := by
  unfold dft2d dft1d
  rw [Finset.sum_comm]
  congr 1; ext v₂
  -- Split ω^{-(α₁v₁ + α₂v₂)} = ω^{-α₁v₁} * ω^{-α₂v₂}
  simp_rw [show ∀ (v₁ : Fin n), (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val) : ℤ) =
    -(↑α₁.val * ↑v₁.val : ℤ) + -(↑α₂.val * ↑v₂.val : ℤ) from by intro; ring]
  simp_rw [zpow_add₀ (ω_ne_zero n hn), ← mul_assoc]
  rw [← Finset.sum_mul]


/-! **Parseval's and Plancherel's Identities (2D)** -/

/-- Parseval's identity (2D): `∑_α ‖f̂(α)‖² = n² · ∑_v f(v)²`.
    Proved by factoring through 1D Parseval twice. -/
theorem parseval_2d (n : ℕ) (hn : n ≠ 0) (g : Fin n → Fin n → ℝ) :
    ∑ α₁ : Fin n, ∑ α₂ : Fin n, Complex.normSq (dft2d n g α₁ α₂) =
    ↑n ^ 2 * ∑ v₁ : Fin n, ∑ v₂ : Fin n, (g v₁ v₂ : ℝ) ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  -- Convert normSq to z * conj z
  simp_rw [(Complex.mul_conj _).symm]
  -- Factor dft2d as iterated dft1d, apply 1D Parseval for α₂ sum
  simp_rw [dft2d_eq_iterated_dft1d n hn]
  simp_rw [parseval_1d_complex n hn]
  -- Factor ↑n out, swap sums
  rw [← Finset.mul_sum]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  -- Fold the inner sums back as dft1d, apply 1D Parseval for α₁ sum
  change (↑n : ℂ) * ∑ y : Fin n, ∑ x : Fin n,
    dft1d n (fun v₁ => (↑(g v₁ y) : ℂ)) x *
    (starRingEnd ℂ) (dft1d n (fun v₁ => (↑(g v₁ y) : ℂ)) x) =
    (↑n : ℂ) ^ 2 * ∑ x : Fin n, ∑ x_1 : Fin n, (↑(g x x_1) : ℂ) ^ 2
  simp_rw [parseval_1d_complex n hn]
  -- Simplify: conj(↑r) = ↑r for real r, ↑r * ↑r = ↑r ^ 2
  simp_rw [Complex.conj_ofReal, ← sq]
  -- Algebra: ↑n * (∑ v₂, ↑n * ∑ v₁, ...) = ↑n² * ∑∑ ...
  conv_lhs => arg 2; rw [← Finset.mul_sum]
  conv_lhs => arg 2; arg 2; rw [Finset.sum_comm]
  ring

/-- Plancherel's identity (2D, cross terms):
    `∑_α f̂(α) · conj(ĝ(α)) = n² · ∑_v f(v) · g(v)`.
    Proved by factoring through 1D Plancherel twice. -/
theorem plancherel_2d (n : ℕ) (hn : n ≠ 0) (f g : Fin n → Fin n → ℝ) :
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      dft2d n f α₁ α₂ * starRingEnd ℂ (dft2d n g α₁ α₂) =
    (↑n : ℂ) ^ 2 * ↑(∑ v₁ : Fin n, ∑ v₂ : Fin n, f v₁ v₂ * g v₁ v₂) := by
  -- Factor dft2d as iterated dft1d, apply 1D Plancherel for α₂
  simp_rw [dft2d_eq_iterated_dft1d n hn]
  simp_rw [plancherel_1d_complex n hn]
  rw [← Finset.mul_sum]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  -- Fold inner sums as dft1d, apply 1D Plancherel for α₁
  change (↑n : ℂ) * ∑ y : Fin n, ∑ x : Fin n,
    dft1d n (fun v₁ => (↑(f v₁ y) : ℂ)) x *
    (starRingEnd ℂ) (dft1d n (fun v₁ => (↑(g v₁ y) : ℂ)) x) =
    (↑n : ℂ) ^ 2 * ↑(∑ v₁ : Fin n, ∑ v₂ : Fin n, f v₁ v₂ * g v₁ v₂)
  simp_rw [plancherel_1d_complex n hn]
  -- Simplify: conj(↑r) = ↑r for real r
  simp_rw [Complex.conj_ofReal]
  -- Algebra: factor ↑n, swap sums, fold casts
  conv_lhs => arg 2; rw [← Finset.mul_sum]
  conv_lhs => arg 2; arg 2; rw [Finset.sum_comm]
  -- LHS = ↑n * (↑n * ∑ v₁, ∑ v₂, ↑(f v₁ v₂) * ↑(g v₁ v₂))
  -- RHS = ↑n ^ 2 * ↑(∑ v₁, ∑ v₂, f v₁ v₂ * g v₁ v₂)
  -- Fold casts on RHS and close with ring
  rw [show (↑(∑ v₁ : Fin n, ∑ v₂ : Fin n, f v₁ v₂ * g v₁ v₂) : ℂ) =
      ∑ v₁ : Fin n, ∑ v₂ : Fin n, ↑(f v₁ v₂) * ↑(g v₁ v₂) from by push_cast; rfl]
  ring


/-! **|1 + ω^{-a}| = 2|cos(πa/n)| Identity** -/

/-- `normSq(1 + z) = 2 + 2·z.re` for `z` on the unit circle. -/
theorem normSq_one_add_of_unit (z : ℂ) (hz : Complex.normSq z = 1) :
    Complex.normSq (1 + z) = 2 + 2 * z.re := by
  rw [Complex.normSq_add, Complex.normSq_one, hz]
  simp [Complex.conj_re]; ring

/-- Real part of `ω^{-a}`: `re(ω^{-a}) = cos(2πa/n)`. -/
theorem re_ω_neg (n : ℕ) (a : ℕ) :
    (ω n ^ (-(a : ℤ))).re = Real.cos (2 * π * ↑a / ↑n) := by
  simp only [ω, zpow_neg, zpow_natCast, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  have h1 : -(↑a * (2 * ↑π * I / ↑n)) = ↑(-(2 * π * ↑a / ↑n)) * I := by
    push_cast; ring
  rw [h1, Complex.exp_mul_I, add_re, mul_re, I_re, I_im, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring_nf; exact Real.cos_neg _

/-- `normSq(ω^a) = 1` for unit-norm `ω`. -/
theorem normSq_ω_zpow (n : ℕ) (hn : n ≠ 0) (a : ℤ) :
    Complex.normSq (ω n ^ a) = 1 := by
  have h1 : ‖ω n ^ a‖ = 1 := by rw [norm_zpow, ω_norm n hn, one_zpow]
  have h2 := Complex.sq_norm (ω n ^ a)
  rw [h1, one_pow] at h2; linarith

/-- `‖1 + ω^{-a}‖² = 4·cos²(πa/n)`. -/
theorem norm_sq_one_add_ω_inv (n : ℕ) (hn : n ≠ 0) (a : ℕ) :
    ‖1 + ω n ^ (-(a : ℤ))‖ ^ 2 = 4 * Real.cos (↑π * ↑a / ↑n) ^ 2 := by
  rw [Complex.sq_norm, normSq_one_add_of_unit _ (normSq_ω_zpow n hn _), re_ω_neg]
  have h := Real.cos_sq (↑π * ↑a / ↑n)
  have heq : 2 * (↑π * ↑a / (↑n : ℝ)) = 2 * π * ↑a / ↑n := by ring
  rw [heq] at h; linarith

/-- `‖1 + ω^{-a}‖ = 2·|cos(πa/n)|`. -/
theorem norm_one_add_ω_inv (n : ℕ) (hn : n ≠ 0) (a : ℕ) :
    ‖1 + ω n ^ (-(a : ℤ))‖ = 2 * |Real.cos (↑π * ↑a / ↑n)| := by
  have h := norm_sq_one_add_ω_inv n hn a
  have hnn : 0 ≤ ‖1 + ω n ^ (-(a : ℤ))‖ := norm_nonneg _
  have habs : 0 ≤ 2 * |Real.cos (↑π * ↑a / ↑n)| := by positivity
  nlinarith [sq_abs (Real.cos (↑π * ↑a / ↑n)),
    sq_nonneg (‖1 + ω n ^ (-(a : ℤ))‖ - 2 * |Real.cos (↑π * ↑a / ↑n)|)]


/-! **Modular Arithmetic Round-Trip** -/

/-- `((a + c) % n + n - c % n) % n = a`. Handles the form produced by `simp`
    in shear composition proofs. -/
theorem mod_add_sub_round (a c n : ℕ) (hn : 0 < n) (ha : a < n) :
    ((a + c) % n + n - c % n) % n = a := by
  have hcn : c % n < n := Nat.mod_lt _ hn
  rw [Nat.add_mod, Nat.mod_eq_of_lt ha]
  by_cases h : a + c % n < n
  · rw [Nat.mod_eq_of_lt h, show a + c % n + n - c % n = a + n from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · push_neg at h
    have hmod : (a + c % n) % n = a + c % n - n := by
      conv_lhs => rw [show a + c % n = (a + c % n - n) + n from by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, show a + c % n - n + n - c % n = a from by omega, Nat.mod_eq_of_lt ha]

/-- `(a + n - c % n + c) % n = a`. Handles the form produced by `simp`
    in reverse shear composition proofs. -/
theorem mod_sub_add_round (a c n : ℕ) (hn : 0 < n) (ha : a < n) :
    (a + n - c % n + c) % n = a := by
  have hcn : c % n < n := Nat.mod_lt _ hn
  have hcle : c % n ≤ c := Nat.mod_le c n
  have step1 : a + n - c % n + c = a + (n - c % n + c) := by omega
  have step2 : n - c % n + c = n + (c - c % n) := by omega
  have step3 : c - c % n = n * (c / n) := by have := Nat.div_add_mod c n; omega
  rw [step1, step2, step3, show a + (n + n * (c / n)) = a + n * (1 + c / n) from by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]


/-! **Shear Bijectivity on `Fin n`** -/

/-- `shearS2` as a function on `Fin n × Fin n`. -/
def shearS2Fin (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) : Fin n × Fin n :=
  (p.1, ⟨(p.2.val + n - (2 * p.1.val) % n) % n, Nat.mod_lt _ hn⟩)

/-- `shearS2Inv` as a function on `Fin n × Fin n`. -/
def shearS2InvFin (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) : Fin n × Fin n :=
  (p.1, ⟨(p.2.val + (2 * p.1.val) % n) % n, Nat.mod_lt _ hn⟩)

/-- `shearS2Fin` is a left inverse of `shearS2InvFin`. -/
theorem shearS2Fin_inv_left (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    shearS2Fin n hn (shearS2InvFin n hn p) = p := by
  ext <;> simp [shearS2Fin, shearS2InvFin]
  exact mod_add_sub_round p.2.val _ n hn p.2.isLt

/-- `shearS2Fin` is a right inverse of `shearS2InvFin`. -/
theorem shearS2Fin_inv_right (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    shearS2InvFin n hn (shearS2Fin n hn p) = p := by
  ext <;> simp [shearS2Fin, shearS2InvFin]
  exact mod_sub_add_round p.2.val _ n hn p.2.isLt

/-- `shearS1` as a function on `Fin n × Fin n`. -/
def shearS1Fin (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) : Fin n × Fin n :=
  (⟨(p.1.val + n - (2 * p.2.val) % n) % n, Nat.mod_lt _ hn⟩, p.2)

/-- `shearS1Inv` as a function on `Fin n × Fin n`. -/
def shearS1InvFin (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) : Fin n × Fin n :=
  (⟨(p.1.val + (2 * p.2.val) % n) % n, Nat.mod_lt _ hn⟩, p.2)

/-- `shearS1Fin` is a left inverse of `shearS1InvFin`. -/
theorem shearS1Fin_inv_left (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    shearS1Fin n hn (shearS1InvFin n hn p) = p := by
  ext <;> simp [shearS1Fin, shearS1InvFin]
  exact mod_add_sub_round p.1.val _ n hn p.1.isLt

/-- `shearS1Fin` is a right inverse of `shearS1InvFin`. -/
theorem shearS1Fin_inv_right (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    shearS1InvFin n hn (shearS1Fin n hn p) = p := by
  ext <;> simp [shearS1Fin, shearS1InvFin]
  exact mod_sub_add_round p.1.val _ n hn p.1.isLt

/-- `shearS2Fin` preserves the first coordinate. -/
theorem shearS2Fin_fst (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    (shearS2Fin n hn p).1 = p.1 := rfl

/-- `shearS1Fin` preserves the second coordinate. -/
theorem shearS1Fin_snd (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    (shearS1Fin n hn p).2 = p.2 := rfl


/-! **DFT Shift Properties** -/

/-- `ω^a = ω^b` when `n ∣ (a - b)`. -/
theorem ω_zpow_congr (n : ℕ) (hn : n ≠ 0) (a b : ℤ) (h : (n : ℤ) ∣ (a - b)) :
    ω n ^ a = ω n ^ b := by
  have h1 : ω n ^ (a - b) = 1 :=
    ((ω_isPrimitiveRoot n hn).zpow_eq_one_iff_dvd (a - b)).mpr h
  rw [show a = (a - b) + b from by ring, zpow_add₀ (ω_ne_zero n hn), h1, one_mul]

/-- `n ∣ ((a + b%n)%n - (a + b))` as integers. Handles the double-mod pattern from
    `Fin n` addition where `k.val = b%n`. -/
theorem nat_add_mod_mod_sub_dvd (a b n : ℕ) :
    (n : ℤ) ∣ ((↑((a + b % n) % n) : ℤ) - (↑a + ↑b)) := by
  have hmn := (Nat.div_add_mod (a + b % n) n).symm
  have hbn := (Nat.div_add_mod b n).symm
  exact ⟨-(↑((a + b % n) / n) + ↑(b / n) : ℤ), by push_cast; nlinarith⟩

/-- `n ∣ ((a + n - c%n)%n - (a - c))` as integers. Key modular identity for shear congruence. -/
theorem mod_sub_int_congr (n a c : ℕ) (hn : 0 < n) :
    (n : ℤ) ∣ ((↑((a + n - c % n) % n) : ℤ) - (↑a - ↑c)) := by
  set β := a + n - c % n
  have hcn : c % n < n := Nat.mod_lt _ hn
  have h_csub : c % n ≤ a + n := by omega
  have h_modβ : (↑(β % n) : ℤ) - ↑β = -(↑n * ↑(β / n)) := by
    have : (↑β : ℤ) = ↑n * ↑(β / n) + ↑(β % n) := by exact_mod_cast (Nat.div_add_mod β n).symm
    linarith
  have h_β_cast : (↑β : ℤ) = ↑a + ↑n - ↑(c % n) := by
    show (↑(a + n - c % n) : ℤ) = _; rw [Nat.cast_sub h_csub]; push_cast; ring
  have h_shift : (↑β : ℤ) - (↑a - ↑c) = ↑n * (1 + ↑(c / n)) := by
    rw [h_β_cast]
    have : (↑c : ℤ) = ↑n * ↑(c / n) + ↑(c % n) := by exact_mod_cast (Nat.div_add_mod c n).symm
    linarith
  rw [show (↑(β % n) : ℤ) - (↑a - ↑c) = (↑(β % n) - ↑β) + (↑β - (↑a - ↑c)) from by ring,
      h_modβ, h_shift]
  exact ⟨-(↑(β / n) : ℤ) + (1 + ↑(c / n)), by ring⟩

/-- DFT of `g ∘ spatialShear₂` equals `ĝ` at the dual-sheared frequency.
    `spatialShear₂(x,y) = ((x + 2y) mod n, y)` → dual `S₂(α₁,α₂) = (α₁, (α₂-2α₁) mod n)`. -/
theorem dft2d_comp_shear2 (n : ℕ) (hn : 0 < n) (g : Fin n → Fin n → ℝ) (α₁ α₂ : Fin n) :
    dft2d n (fun x y => g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ hn⟩ y) α₁ α₂ =
    dft2d n g α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn⟩ := by
  haveI : NeZero n := ⟨by omega⟩
  unfold dft2d; simp only []
  set β : Fin n := ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn⟩
  -- Swap to ∑ v₂ ∑ v₁ so we can reindex v₁ for each fixed v₂
  rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
  congr 1; ext v₂
  -- Reindex v₁ ↦ v₁ + k in Fin n, where k = (2*v₂)%n
  set k : Fin n := ⟨(2 * v₂.val) % n, Nat.mod_lt _ hn⟩
  apply Fintype.sum_equiv (Equiv.addRight k)
  intro v₁
  -- Show: g ⟨(v₁+2v₂)%n,_⟩ v₂ * ω^{-(α₁v₁+α₂v₂)} = g(v₁+k) v₂ * ω^{-(α₁(v₁+k)+β v₂)}
  show (↑(g ⟨(v₁.val + 2 * v₂.val) % n, _⟩ v₂) : ℂ) *
    ω n ^ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val : ℤ)) =
    (↑(g (v₁ + k) v₂) : ℂ) *
    ω n ^ (-(↑α₁.val * ↑(v₁ + k).val + ↑β.val * ↑v₂.val : ℤ))
  -- g values match: ⟨(v₁+2v₂)%n, _⟩ = v₁ + k as Fin n elements
  have hfin : (⟨(v₁.val + 2 * v₂.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = v₁ + k := by
    ext
    show (v₁.val + 2 * v₂.val) % n = (v₁.val + (2 * v₂.val) % n) % n
    rw [Nat.add_mod v₁.val (2 * v₂.val) n, Nat.add_mod v₁.val ((2 * v₂.val) % n) n,
        Nat.mod_mod_of_dvd _ (dvd_refl n)]
  rw [hfin]
  -- ω exponents match: apply ω_zpow_congr
  congr 1
  apply ω_zpow_congr n (by omega)
  -- Phase divisibility: n | (-(α₁v₁+α₂v₂) - (-(α₁(v₁+k)+βv₂)))
  -- (v₁+k).val is definitionally (v₁.val+(2v₂.val)%n)%n
  change (↑n : ℤ) ∣ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val : ℤ) -
    (-(↑α₁.val * ↑((v₁.val + (2 * v₂.val) % n) % n) + ↑β.val * ↑v₂.val)))
  -- Two divisibility facts (keeping ↑(a%n) as opaque Nat casts, no ℤ-level %)
  obtain ⟨d₁, hd₁⟩ := nat_add_mod_mod_sub_dvd v₁.val (2 * v₂.val) n
  obtain ⟨d₂, hd₂⟩ := mod_sub_int_congr n α₂.val (2 * α₁.val) hn
  -- Massage to forms matching linear_combination
  have hm : (↑((v₁.val + (2 * v₂.val) % n) % n) : ℤ) - (↑v₁.val + 2 * ↑v₂.val) =
      ↑n * d₁ := by convert hd₁ using 2 <;> (try push_cast) <;> (try ring)
  have hβ : (↑β.val : ℤ) - (↑α₂.val - 2 * ↑α₁.val) = ↑n * d₂ := by
    convert hd₂ using 2 <;> (try push_cast) <;> (try ring)
  exact ⟨↑α₁.val * d₁ + d₂ * ↑v₂.val, by linear_combination ↑α₁.val * hm + ↑v₂.val * hβ⟩

/-- DFT of `g ∘ spatialShear₂ ∘ translate_e₁` has an extra phase factor `ω^{α₁}`.
    Here `translate_e₁(x,y) = ((x+1)%n, y)` so the combined map is
    `(x,y) ↦ ((x+2y+1)%n, y)`. Direct proof via reindexing with `k = (2v₂+1)%n`. -/
theorem dft2d_comp_shear2_e1 (n : ℕ) (hn : 0 < n) (g : Fin n → Fin n → ℝ) (α₁ α₂ : Fin n) :
    dft2d n (fun x y => g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ hn⟩ y) α₁ α₂ =
    ω n ^ (α₁.val : ℤ) *
    dft2d n g α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn⟩ := by
  haveI : NeZero n := ⟨by omega⟩
  unfold dft2d; simp only []
  set β : Fin n := ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn⟩
  -- Push ω^{α₁} into both sums on RHS, swap both sides to ∑v₂ ∑v₁
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
  congr 1; ext v₂
  -- Reindex v₁ ↦ v₁ + k where k = (2v₂+1)%n
  set k : Fin n := ⟨(2 * v₂.val + 1) % n, Nat.mod_lt _ hn⟩
  apply Fintype.sum_equiv (Equiv.addRight k)
  intro v₁
  show (↑(g ⟨(v₁.val + 2 * v₂.val + 1) % n, _⟩ v₂) : ℂ) *
    ω n ^ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val : ℤ)) =
    ω n ^ (↑α₁.val : ℤ) * ((↑(g (v₁ + k) v₂) : ℂ) *
    ω n ^ (-(↑α₁.val * ↑(v₁ + k).val + ↑β.val * ↑v₂.val : ℤ)))
  have hfin : (⟨(v₁.val + 2 * v₂.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = v₁ + k := by
    ext
    show (v₁.val + 2 * v₂.val + 1) % n = (v₁.val + (2 * v₂.val + 1) % n) % n
    rw [show v₁.val + 2 * v₂.val + 1 = v₁.val + (2 * v₂.val + 1) from by omega]
    rw [Nat.add_mod v₁.val (2 * v₂.val + 1) n,
        Nat.add_mod v₁.val ((2 * v₂.val + 1) % n) n,
        Nat.mod_mod_of_dvd _ (dvd_refl n)]
  rw [hfin, show ω n ^ (↑α₁.val : ℤ) * ((↑(g (v₁ + k) v₂) : ℂ) *
    ω n ^ (-(↑α₁.val * ↑(v₁ + k).val + ↑β.val * ↑v₂.val : ℤ))) =
    (↑(g (v₁ + k) v₂) : ℂ) * (ω n ^ (↑α₁.val : ℤ) *
    ω n ^ (-(↑α₁.val * ↑(v₁ + k).val + ↑β.val * ↑v₂.val : ℤ))) from by ring]
  congr 1
  rw [← zpow_add₀ (ω_ne_zero n (by omega))]
  apply ω_zpow_congr n (by omega)
  change (↑n : ℤ) ∣ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val : ℤ) -
    (↑α₁.val + -(↑α₁.val * ↑((v₁.val + (2 * v₂.val + 1) % n) % n) + ↑β.val * ↑v₂.val)))
  obtain ⟨d₁, hd₁⟩ := nat_add_mod_mod_sub_dvd v₁.val (2 * v₂.val + 1) n
  obtain ⟨d₂, hd₂⟩ := mod_sub_int_congr n α₂.val (2 * α₁.val) hn
  have hm : (↑((v₁.val + (2 * v₂.val + 1) % n) % n) : ℤ) - (↑v₁.val + 2 * ↑v₂.val + 1) =
      ↑n * d₁ := by convert hd₁ using 2 <;> (try push_cast) <;> (try ring)
  have hβ : (↑β.val : ℤ) - (↑α₂.val - 2 * ↑α₁.val) = ↑n * d₂ := by
    convert hd₂ using 2 <;> (try push_cast) <;> (try ring)
  exact ⟨↑α₁.val * d₁ + d₂ * ↑v₂.val, by linear_combination ↑α₁.val * hm + ↑v₂.val * hβ⟩

/-- DFT of `g ∘ spatialShear₁` equals `ĝ` at the dual-sheared frequency.
    `spatialShear₁(x,y) = (x, (2x + y) mod n)` → dual `S₁(α₁,α₂) = ((α₁-2α₂) mod n, α₂)`.
    Symmetric to `dft2d_comp_shear2` with coordinates swapped. -/
theorem dft2d_comp_shear1 (n : ℕ) (hn : 0 < n) (g : Fin n → Fin n → ℝ) (α₁ α₂ : Fin n) :
    dft2d n (fun x y => g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ hn⟩) α₁ α₂ =
    dft2d n g ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn⟩ α₂ := by
  haveI : NeZero n := ⟨by omega⟩
  unfold dft2d; simp only []
  set γ : Fin n := ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn⟩
  -- Here the shear is in the second coordinate, so reindex v₂ for each fixed v₁
  congr 1; ext v₁
  set k : Fin n := ⟨(2 * v₁.val) % n, Nat.mod_lt _ hn⟩
  apply Fintype.sum_equiv (Equiv.addRight k)
  intro v₂
  show (↑(g v₁ ⟨(2 * v₁.val + v₂.val) % n, _⟩) : ℂ) *
    ω n ^ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val : ℤ)) =
    (↑(g v₁ (v₂ + k)) : ℂ) *
    ω n ^ (-(↑γ.val * ↑v₁.val + ↑α₂.val * ↑(v₂ + k).val : ℤ))
  have hfin : (⟨(2 * v₁.val + v₂.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = v₂ + k := by
    ext
    show (2 * v₁.val + v₂.val) % n = (v₂.val + (2 * v₁.val) % n) % n
    rw [show 2 * v₁.val + v₂.val = v₂.val + 2 * v₁.val from by omega]
    rw [Nat.add_mod v₂.val (2 * v₁.val) n, Nat.add_mod v₂.val ((2 * v₁.val) % n) n,
        Nat.mod_mod_of_dvd _ (dvd_refl n)]
  rw [hfin]; congr 1
  apply ω_zpow_congr n (by omega)
  change (↑n : ℤ) ∣ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val : ℤ) -
    (-(↑γ.val * ↑v₁.val + ↑α₂.val * ↑((v₂.val + (2 * v₁.val) % n) % n))))
  obtain ⟨d₁, hd₁⟩ := nat_add_mod_mod_sub_dvd v₂.val (2 * v₁.val) n
  obtain ⟨d₂, hd₂⟩ := mod_sub_int_congr n α₁.val (2 * α₂.val) hn
  have hm : (↑((v₂.val + (2 * v₁.val) % n) % n) : ℤ) - (↑v₂.val + 2 * ↑v₁.val) =
      ↑n * d₁ := by convert hd₁ using 2 <;> (try push_cast) <;> (try ring)
  have hγ : (↑γ.val : ℤ) - (↑α₁.val - 2 * ↑α₂.val) = ↑n * d₂ := by
    convert hd₂ using 2 <;> (try push_cast) <;> (try ring)
  exact ⟨↑α₂.val * d₁ + d₂ * ↑v₁.val, by linear_combination ↑α₂.val * hm + ↑v₁.val * hγ⟩

/-- DFT shift for shear₁ + translate by e₂: `(x,y) ↦ (x, (2x+y+1)%n)`.
    Extra phase factor `ω^{α₂}`. Direct proof via reindexing with `k = (2v₁+1)%n`. -/
theorem dft2d_comp_shear1_e2 (n : ℕ) (hn : 0 < n) (g : Fin n → Fin n → ℝ) (α₁ α₂ : Fin n) :
    dft2d n (fun x y => g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ hn⟩) α₁ α₂ =
    ω n ^ (α₂.val : ℤ) *
    dft2d n g ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn⟩ α₂ := by
  haveI : NeZero n := ⟨by omega⟩
  unfold dft2d; simp only []
  set γ : Fin n := ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn⟩
  -- Push ω^{α₂} into both sums on RHS
  simp_rw [Finset.mul_sum]
  congr 1; ext v₁
  -- Reindex v₂ ↦ v₂ + k where k = (2v₁+1)%n
  set k : Fin n := ⟨(2 * v₁.val + 1) % n, Nat.mod_lt _ hn⟩
  apply Fintype.sum_equiv (Equiv.addRight k)
  intro v₂
  show (↑(g v₁ ⟨(2 * v₁.val + v₂.val + 1) % n, _⟩) : ℂ) *
    ω n ^ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val : ℤ)) =
    ω n ^ (↑α₂.val : ℤ) * ((↑(g v₁ (v₂ + k)) : ℂ) *
    ω n ^ (-(↑γ.val * ↑v₁.val + ↑α₂.val * ↑(v₂ + k).val : ℤ)))
  have hfin : (⟨(2 * v₁.val + v₂.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = v₂ + k := by
    ext
    show (2 * v₁.val + v₂.val + 1) % n = (v₂.val + (2 * v₁.val + 1) % n) % n
    rw [show 2 * v₁.val + v₂.val + 1 = v₂.val + (2 * v₁.val + 1) from by omega]
    rw [Nat.add_mod v₂.val (2 * v₁.val + 1) n,
        Nat.add_mod v₂.val ((2 * v₁.val + 1) % n) n,
        Nat.mod_mod_of_dvd _ (dvd_refl n)]
  rw [hfin, show ω n ^ (↑α₂.val : ℤ) * ((↑(g v₁ (v₂ + k)) : ℂ) *
    ω n ^ (-(↑γ.val * ↑v₁.val + ↑α₂.val * ↑(v₂ + k).val : ℤ))) =
    (↑(g v₁ (v₂ + k)) : ℂ) * (ω n ^ (↑α₂.val : ℤ) *
    ω n ^ (-(↑γ.val * ↑v₁.val + ↑α₂.val * ↑(v₂ + k).val : ℤ))) from by ring]
  congr 1
  rw [← zpow_add₀ (ω_ne_zero n (by omega))]
  apply ω_zpow_congr n (by omega)
  change (↑n : ℤ) ∣ (-(↑α₁.val * ↑v₁.val + ↑α₂.val * ↑v₂.val : ℤ) -
    (↑α₂.val + -(↑γ.val * ↑v₁.val + ↑α₂.val * ↑((v₂.val + (2 * v₁.val + 1) % n) % n))))
  obtain ⟨d₁, hd₁⟩ := nat_add_mod_mod_sub_dvd v₂.val (2 * v₁.val + 1) n
  obtain ⟨d₂, hd₂⟩ := mod_sub_int_congr n α₁.val (2 * α₂.val) hn
  have hm : (↑((v₂.val + (2 * v₁.val + 1) % n) % n) : ℤ) - (↑v₂.val + 2 * ↑v₁.val + 1) =
      ↑n * d₁ := by convert hd₁ using 2 <;> (try push_cast) <;> (try ring)
  have hγ : (↑γ.val : ℤ) - (↑α₁.val - 2 * ↑α₂.val) = ↑n * d₂ := by
    convert hd₂ using 2 <;> (try push_cast) <;> (try ring)
  exact ⟨↑α₂.val * d₁ + d₂ * ↑v₁.val, by linear_combination ↑α₂.val * hm + ↑v₁.val * hγ⟩


/-! **Correlation Identities** -/

/-- Combined correlation for pair 1 (M₁ and M₁+e₁):
    `n² · C₁ = ∑_α ĝ(α) · conj(ĝ(S₂α)) · (1 + ω^{-α₁})`.
    Splits into shear₂ + shear₂_e₁ terms, applies Plancherel + DFT shift to each,
    then recombines using `conj(ω^{α₁} · z) = ω^{-α₁} · conj(z)`. -/
theorem corr_pair1 (n : ℕ) (hn : n ≠ 0) (g : Fin n → Fin n → ℝ)
    (hn3 : 3 ≤ n) :
    (↑n : ℂ) ^ 2 * ↑(∑ x : Fin n, ∑ y : Fin n,
      g x y * (g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ (by omega)⟩ y +
               g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ (by omega)⟩ y)) =
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      dft2d n g α₁ α₂ *
      starRingEnd ℂ (dft2d n g α₁
        ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ (by omega)⟩) *
      (1 + ω n ^ (-(α₁.val : ℤ))) := by
  have hn' : 0 < n := by omega
  set β : Fin n → Fin n → Fin n := fun α₁ α₂ =>
    ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn'⟩
  -- Split g*(h₁+h₂) = g*h₁ + g*h₂
  simp_rw [mul_add, Finset.sum_add_distrib]
  -- Distribute cast ↑(A+B) = ↑A + ↑B, then n²*(↑A+↑B) = n²*↑A + n²*↑B
  have hcast : ∀ (a b : ℝ), (↑(a + b) : ℂ) = ↑a + ↑b := fun a b => by exact_mod_cast rfl
  rw [hcast, mul_add]
  -- Apply Plancherel to each half
  rw [← plancherel_2d n hn g (fun x y => g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ hn'⟩ y)]
  rw [← plancherel_2d n hn g (fun x y => g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ hn'⟩ y)]
  -- Rewrite DFTs using shift properties
  simp_rw [dft2d_comp_shear2 n hn' g, dft2d_comp_shear2_e1 n hn' g]
  -- Conjugate of phase: conj(ω^{α₁} · z) = ω^{-α₁} · conj(z)
  simp_rw [map_mul, conj_ω_zpow n hn]
  -- Combine: ∑ a*conj(b) + ∑ a*ω^{-α₁}*conj(b) = ∑ a*conj(b)*(1+ω^{-α₁})
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α₁ _ => Finset.sum_congr rfl (fun α₂ _ => ?_))
  ring

/-- Combined correlation for pair 2 (M₂ and M₂+e₂):
    `n² · C₂ = ∑_α ĝ(α) · conj(ĝ(S₁α)) · (1 + ω^{-α₂})`.
    Symmetric to `corr_pair1` with coordinates swapped. -/
theorem corr_pair2 (n : ℕ) (hn : n ≠ 0) (g : Fin n → Fin n → ℝ)
    (hn3 : 3 ≤ n) :
    (↑n : ℂ) ^ 2 * ↑(∑ x : Fin n, ∑ y : Fin n,
      g x y * (g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ (by omega)⟩ +
               g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ (by omega)⟩)) =
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      dft2d n g α₁ α₂ *
      starRingEnd ℂ (dft2d n g
        ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ (by omega)⟩ α₂) *
      (1 + ω n ^ (-(α₂.val : ℤ))) := by
  have hn' : 0 < n := by omega
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hcast : ∀ (a b : ℝ), (↑(a + b) : ℂ) = ↑a + ↑b := fun a b => by exact_mod_cast rfl
  rw [hcast, mul_add]
  rw [← plancherel_2d n hn g (fun x y => g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ hn'⟩)]
  rw [← plancherel_2d n hn g (fun x y => g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ hn'⟩)]
  simp_rw [dft2d_comp_shear1 n hn' g, dft2d_comp_shear1_e2 n hn' g]
  simp_rw [map_mul, conj_ω_zpow n hn]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α₁ _ => Finset.sum_congr rfl (fun α₂ _ => ?_))
  ring

end


