-- Prove2me | Definitions.Def_FreeSpencer_Params
-- name    : FreeSpencer_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:04:04.975604+00:00
-- url     : https://prove2.me/theorems/802aed3a-3d7a-4690-a078-a628edcf573a
-- title:
--   The parameters of the algorithm
-- statement:
--   The constants $s=n+D+2$, $M_C=2^{300}s^{60}$, $M_4=2^{1040}s^{200}$, $\mu=2^{-10}s^{-6}$, $\gamma_0=2^{-15}$, $\delta=2^{-13}$, $\epsilon_A=10^{-4}$, $a_0=(16384n)^{-1}$, $t_\ell=4096/\sqrt\ell$, $\alpha_\ell=\min\{\delta/2,t_\ell/(2M_C)\}$. The mode for $m\le n$ is $(q,\theta,\kappa,B,\tau,K)=(1/2,128,0,8,1/8,78)$. For $m>n$, $p$ starts at $2$ and doubles until $2^p\ge D/n$, $q=1/p$, $\theta_0=\sqrt{(1-q)L^qn^{1-q}/(qD^q)}$, $\theta=\min\{44\theta_0,20s\}$, $\kappa=1/D$, $B=2+6L^qn^{1/2-q}/(\theta q)$, $\tau=(B+6)^{-1}$, $K=\lceil16+128/(17\cdot0.99\tau)\rceil+1$. The step size is $h=\min\{a_0/(2\sqrt n),1/2,\sqrt{\tau/100},\sqrt{2^{-40}/M_4}\}$.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, p.50; Appendix C.1, p.77; (C.1), p.77; (D.4), p.82

import Mathlib

namespace FreeSpencer

/-- `s = n + D + 2`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, p.50; Appendix D, p.82. -/
def sDim (n D : ℕ) : ℝ := (n : ℝ) + D + 2

/-- `M_C = 2^300 s^60`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (C.1), p.77; (D.4), p.82. -/
noncomputable def constMC (s : ℝ) : ℝ := 2 ^ 300 * s ^ 60

/-- `M₄ = 2^1040 s^200`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (C.1), p.77; (D.4), p.82. -/
noncomputable def constM4 (s : ℝ) : ℝ := 2 ^ 1040 * s ^ 200

/-- `μ = 2^{-10} s^{-6}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (D.4), p.82. -/
noncomputable def constMu (s : ℝ) : ℝ := 1 / (2 ^ 10 * s ^ 6)

/-- `γ₀ = 2^{-15}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (D.4), p.82. -/
noncomputable def gamma0 : ℝ := 1 / 2 ^ 15

/-- `δ = 2^{-13}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, p.50. -/
noncomputable def deltaC : ℝ := 1 / 2 ^ 13

/-- `ε_A = 10^{-4}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, p.50. -/
noncomputable def epsA : ℝ := 1 / 10000

/-- The rounding margin `a₀ = (16384 n)⁻¹`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, p.50. -/
noncomputable def marginA (n : ℕ) : ℝ := 1 / (16384 * (n : ℝ))

/-- `t_ℓ = L/√ℓ` with `L = 4096`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, p.50. -/
noncomputable def tEll (ℓ : ℕ) : ℝ := 4096 / Real.sqrt ℓ

/-- `α_ℓ = min{δ/2, t_ℓ/(2 M_C)}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, p.50. -/
noncomputable def alphaEll (n m ℓ : ℕ) : ℝ :=
  min (deltaC / 2) (tEll ℓ / (2 * constMC (sDim n (2 * m))))

/-- The parameters of a mode: the potential `(q, θ, κ)`, the curvature constant `B`, the horizon `τ`
and the epoch budget `K`. -/
structure Params where
  q : ℝ
  θ : ℝ
  κ : ℝ
  B : ℝ
  τ : ℝ
  K : ℕ

open Classical in
/-- The exponent `p`: starting from `p = 2`, double until `2^p ≥ D/n`, i.e. the least `2^{j+1}` with
`D ≤ n · 2^{2^{j+1}}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Appendix C.1, p.77; Section 10.1, p.64. -/
noncomputable def expP (n D : ℕ) : ℕ :=
  if h : ∃ j : ℕ, D ≤ n * 2 ^ (2 ^ (j + 1)) then 2 ^ (Nat.find h + 1) else 2

/-- The rectangular parameters for `m > n`: `q = 1/p`,
`θ₀ = √((1-q) L^q n^{1-q} / (q D^q))`, `θ = min{44 θ₀, 20 s}`, `κ = 1/D`,
`B = 2 + 6 L^q n^{1/2-q} / (θ q)`, `τ = (B+6)⁻¹`, `K = ⌈16 + 128/(17 · 0.99 τ)⌉ + 1`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Appendix C.1, p.77; Section 7.2, p.50. -/
noncomputable def rectParams (n m : ℕ) : Params :=
  let D : ℝ := 2 * (m : ℝ)
  let q : ℝ := 1 / (expP n (2 * m) : ℝ)
  let θ₀ : ℝ := Real.sqrt ((1 - q) * (4096 : ℝ) ^ q * (n : ℝ) ^ (1 - q) / (q * D ^ q))
  let θ : ℝ := min (44 * θ₀) (20 * sDim n (2 * m))
  let B : ℝ := 2 + 6 * (4096 : ℝ) ^ q * (n : ℝ) ^ (1 / 2 - q) / (θ * q)
  let τ : ℝ := (B + 6)⁻¹
  { q := q, θ := θ, κ := 1 / D, B := B, τ := τ, K := ⌈16 + 128 / (17 * 0.99 * τ)⌉₊ + 1 }

/-- The mode of Algorithm 3: the square parameters `(q, θ, κ, B, τ, K) = (1/2, 128, 0, 8, 1/8, 78)`
for `m ≤ n`, the rectangular ones for `m > n`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Appendix C.1, p.77; Algorithm 3, p.79. -/
noncomputable def params (n m : ℕ) : Params :=
  if m ≤ n then { q := 1 / 2, θ := 128, κ := 0, B := 8, τ := 1 / 8, K := 78 } else rectParams n m

/-- The step size `h = min{a₀/(2√n), 1/2, √(τ/100), √(2^{-40}/M₄)}`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, p.50; Appendix C.1, p.77. -/
noncomputable def stepH (n m : ℕ) (par : Params) : ℝ :=
  min (min (marginA n / (2 * Real.sqrt n)) (1 / 2))
    (min (Real.sqrt (par.τ / 100)) (Real.sqrt ((1 / 2 ^ 40) / constM4 (sDim n (2 * m)))))

end FreeSpencer


