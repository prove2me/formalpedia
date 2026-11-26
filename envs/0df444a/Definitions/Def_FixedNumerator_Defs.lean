-- Prove2me | Definitions.Def_FixedNumerator_Defs
-- name    : FixedNumerator_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:34:05.216582+00:00
-- url     : https://prove2.me/theorems/d64a2377-846f-517f-ad34-72e6fc31fc3c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from J. S. Farland (jkfarland-bot/FixedNumerator; see pinned Apache-2.0 LICENSE and README.md)'s pinned FixedNumerator: quartic Gauss sums over primes with a fixed numerator development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex Finset
noncomputable section
namespace FixedNumerator
def lam3 : GaussianInt := ⟨-2, 2⟩
def IsPrimary (c : GaussianInt) : Prop := lam3 ∣ c - 1
def C (a c : GaussianInt) : ℤ := ((a.norm - 1) / 4) * ((c.norm - 1) / 4)
def normBall (X : ℕ) : Finset GaussianInt :=
  ((Icc (-(X : ℤ)) X ×ˢ Icc (-(X : ℤ)) X).image fun ab => (⟨ab.1, ab.2⟩ : GaussianInt)).filter
    fun c => c.norm ≤ X
structure QuarticData where
  /-- The quartic residue symbol `(r/c)₄`. -/
  χ : GaussianInt → GaussianInt → ℂ
  /-- The quartic Gauss sum `g₄(μ, c)`. -/
  g : GaussianInt → GaussianInt → ℂ
  /-- The symbol is multiplicative in the numerator. -/
  chi_mul_left : ∀ a b c, χ (a * b) c = χ a c * χ b c
  /-- The symbol is multiplicative in the (primary) denominator. -/
  chi_mul_right : ∀ a c d, IsPrimary c → IsPrimary d → χ a (c * d) = χ a c * χ a d
  /-- On coprime pairs the symbol is a fourth root of unity. -/
  chi_pow_four : ∀ a c, IsCoprime a c → χ a c ^ 4 = 1
  /-- Biquadratic reciprocity, DDHL (3.2). -/
  reciprocity : ∀ a c, IsPrimary a → IsPrimary c → IsCoprime a c →
    χ a c = (-1 : ℂ) ^ C a c * χ c a
  /-- The twist rule, DDHL (3.4). -/
  g_twist : ∀ r μ c, IsPrimary c → IsCoprime r c → g (r * μ) c = starRingEnd ℂ (χ r c) * g μ c
  /-- Twisted multiplicativity, DDHL (3.5). -/
  g_mul : ∀ μ c c', IsPrimary c → IsPrimary c' → IsCoprime c c' →
    g μ (c * c') = χ c c' * χ c' c * g μ c * g μ c'
  /-- `g₄(μ, 1) = 1`, the case `ℓ = 0` of DDHL (3.7). -/
  g_one : ∀ μ, g μ 1 = 1
  /-- The support part of the local formula DDHL (3.7), with (3.4): for a primary prime `π` and
  `μ'` prime to `π`, `g₄(π^e μ', π^k)` vanishes unless `k = 0`, `k = e + 1`, or `4 ∣ k ≤ e`. -/
  g_prime_pow : ∀ π μ' (e k : ℕ), Prime π → IsPrimary π → IsCoprime μ' π →
    g (π ^ e * μ') (π ^ k) ≠ 0 → k = 0 ∨ k = e + 1 ∨ (4 ∣ k ∧ k ≤ e)
open Classical in
/-- `∑_{N(c) ≤ X, c ≡ β (mod 4), (c, γ) = 1} g₄(μ, c) W(c)`: the truncation at norm `X` of DDHL's
series `ψ*_β(s, μ, ℓ; γ)`, with the weight `W(c)` standing for `(c/|c|)^ℓ N(c)^{-s}`. -/
def truncSum (D : QuarticData) (W : GaussianInt → ℂ) (μ β γ : GaussianInt) (X : ℕ) : ℂ :=
  ∑ c ∈ (normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β ∧ IsCoprime c γ), D.g μ c * W c
def countAbs (a : ℕ → ℂ) (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, ‖a n‖
def sharpSum (a : ℕ → ℂ) (X : ℕ) : ℂ := ∑ n ∈ Icc 1 X, a n
def smoothSum (a : ℕ → ℂ) (R : ℝ → ℝ) (X : ℕ) : ℂ := ∑ n ∈ Icc 1 X, a n * (R (n / X) : ℂ)
end FixedNumerator


