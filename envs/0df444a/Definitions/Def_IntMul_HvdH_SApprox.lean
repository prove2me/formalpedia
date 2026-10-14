-- Prove2me | Definitions.Def_IntMul_HvdH_SApprox
-- name    : IntMul_HvdH_SApprox
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T23:45:54.325339+00:00
-- url     : https://prove2.me/theorems/21573a7b-58b6-4584-b1b0-016b4e9093a7
-- title:
--   Truncated fixed-point approximation of the resampling map $\mathcal S'$ (Harvey–van der Hoeven Lemma 4.9)
-- statement:
--   Computable approximation of $\mathcal S'=\mathcal S/2$, where
--   $$(\mathcal S'u)_k=\frac1{2\alpha}\sum_{j\in\mathbb Z}e^{-\pi(j-sk/t)^2/\alpha^2}\,u_{j\bmod s}.$$
--
--   * `ceilSqrt p` $=\lceil\sqrt p\rceil$ and `sWidth p α` $=m=\lceil\sqrt p\rceil\alpha$.
--   * `betaT p α` $=\lfloor2^p/(2\alpha)\rfloor$.
--   * `sTerm p s t α k U j` is the rounded product $\lfloor\tilde\beta\,\tilde x_j\,U_{j\bmod s}/2^{2p}\rceil_0$, where $\tilde x_j$ = `expNeg p (α²t²) ((tj-sk)²)` approximates $2^pe^{-\pi(j-sk/t)^2/\alpha^2}$.
--   * `Sapprox p s t α U k` sums `sTerm` over the $2m+1$ integers $j$ with $|j-c|\le m$, where $c=\lceil sk/t\rceil$.
--   * `Sexact s t α u k` is the exact value $(\mathcal S'u)_k$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 4.9

import Definitions.Def_IntMul_HvdH_RealExp

/-! Fixed-point approximation of the resampling map `S' = S / 2` by truncated Gaussian sums
(Harvey–van der Hoeven Lemma 4.9). Gaussian integers are pairs `(re, im) : ℤ × ℤ`, and a
fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- `⌈√p⌉`. -/
def ceilSqrt (p : ℕ) : ℕ := if Nat.sqrt p * Nat.sqrt p < p then Nat.sqrt p + 1 else Nat.sqrt p

/-- Truncation half-width `m = ⌈√p⌉ α` of Lemma 4.9. -/
def sWidth (p α : ℕ) : ℕ := ceilSqrt p * α

/-- `⌊2^p / (2α)⌋`, the fixed-point value of `β = 1/(2α)`. -/
def betaT (p α : ℕ) : ℤ := ((2 ^ p / (2 * α) : ℕ) : ℤ)

/-- One term `ρ(β̃ x̃_j u_j)` of the truncated sum, where `x̃_j ≈ 2^p e^{-π(j - sk/t)²/α²}`
is computed by `expNeg` (Lemma 2.13) and the product is rounded towards zero. -/
def sTerm (p s t α k : ℕ) (U : ℕ → ℤ × ℤ) (j : ℤ) : ℤ × ℤ :=
  let w := betaT p α * expNeg p (α ^ 2 * t ^ 2) ((t * j - s * k : ℤ).natAbs ^ 2)
  let V := U (j % s).toNat
  ((w * V.1).tdiv (2 ^ (2 * p)), (w * V.2).tdiv (2 ^ (2 * p)))

/-- Lemma 4.9: `(S̃' U)_k = ∑_{|j - c| ≤ m} sTerm j` with `c = ⌈sk/t⌉`, i.e. the sum over
`j = c - m + i` for `i < 2m + 1`. -/
def Sapprox (p s t α : ℕ) (U : ℕ → ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  let m : ℕ := sWidth p α
  let c : ℤ := ((s * k + t - 1) / t : ℕ)
  (∑ i ∈ Finset.range (2 * m + 1), (sTerm p s t α k U (c - m + i)).1,
    ∑ i ∈ Finset.range (2 * m + 1), (sTerm p s t α k U (c - m + i)).2)

/-- The exact map `(S' u)_k = (2α)⁻¹ ∑_{j ∈ ℤ} e^{-π (j - sk/t)² / α²} u_{j mod s}`. -/
noncomputable def Sexact (s t α : ℕ) (u : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑' j : ℤ, (((2 * α : ℝ)⁻¹ * Real.exp (-(Real.pi * (j - (s * k : ℝ) / t) ^ 2 / α ^ 2)) : ℝ) : ℂ) *
    u (j % s).toNat

end IntMul.HvdH


