-- Prove2me | Definitions.Def_IntMul_HvdH_FixedPoint
-- name    : IntMul_HvdH_FixedPoint
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T20:46:16.760975+00:00
-- url     : https://prove2.me/theorems/3b31a8d2-d8d8-4996-9ffc-4d3d175a83ee
-- title:
--   Fixed-point rounding $\rho$ and scaling (Harvey–van der Hoeven §2.2)
-- statement:
--   Fixed-point rounding used throughout the $O(n\log n)$ integer multiplication algorithm of Harvey and van der Hoeven.
--
--   * $\rho_0:\mathbb R\to\mathbb Z$ rounds towards zero: $\rho_0(x)=\lfloor x\rfloor$ for $x\ge0$ and $\rho_0(x)=\lceil x\rceil$ for $x<0$.
--   * $\rho_0:\mathbb C\to\mathbb Z[i]$ acts on real and imaginary parts: $\rho_0(x+iy)=\rho_0(x)+i\rho_0(y)$.
--   * For a precision $p$, $\rho(u)=2^{-p}\rho_0(2^pu)$, so $\rho$ maps $\mathbb C$ into $2^{-p}\mathbb Z[i]$.
--   * `scaleFP p c ũ` is the scaling procedure of Lemma 2.2: set $w=c\tilde u$; if $|w|\le1$ return $w$, otherwise return $\rho(2^pw/b)$ with $b=\lceil 2^p|w|\rceil$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.2 (definition of rho) and proof of Lemma 2.2

import Mathlib

/-! Fixed-point rounding of Harvey–van der Hoeven, §2.2. -/

namespace IntMul.HvdH

/-- Round towards zero, `ℝ → ℤ`: `⌊x⌋` for `x ≥ 0` and `⌈x⌉` for `x < 0`. -/
noncomputable def rho0 (x : ℝ) : ℤ := if 0 ≤ x then ⌊x⌋ else ⌈x⌉

/-- Componentwise round towards zero on `ℂ`, landing in `ℤ[i]`. -/
noncomputable def rho0C (u : ℂ) : ℂ := ((rho0 u.re : ℤ) : ℂ) + ((rho0 u.im : ℤ) : ℂ) * Complex.I

/-- Round to precision `p`: `ρ(u) = 2^{-p} ρ₀(2^p u)`. -/
noncomputable def rho (p : ℕ) (u : ℂ) : ℂ := ((2 : ℂ) ^ p)⁻¹ * rho0C ((2 : ℂ) ^ p * u)

/-- The scaling step of Lemma 2.2: from an approximation `ũ` of `u`, produce an approximation of
`c u` that stays in the unit disc (renormalising by `⌈2^p |c ũ|⌉ / 2^p` when `c ũ` leaves it). -/
noncomputable def scaleFP (p c : ℕ) (ũ : ℂ) : ℂ :=
  if ‖(c : ℂ) * ũ‖ ≤ 1 then (c : ℂ) * ũ
  else rho p ((2 : ℂ) ^ p * ((c : ℂ) * ũ) / ((⌈(2 : ℝ) ^ p * ‖(c : ℂ) * ũ‖⌉ : ℤ) : ℂ))

end IntMul.HvdH


