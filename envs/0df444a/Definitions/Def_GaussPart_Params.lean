-- Prove2me | Definitions.Def_GaussPart_Params
-- name    : GaussPart_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:56.222948+00:00
-- url     : https://prove2.me/theorems/f89846fa-a5c9-4de7-98b4-7bbfe7108455
-- title:
--   The Parameter Choices of Algorithm 1
-- statement:
--   For a universal constant $C_0$ and parameters $k,q,\sigma,\eta,\delta,\Delta$: $\lambda=\varepsilon=\tau_0=\eta/100$, $\sigma_*=\sigma\eta/(400q)$, $H=e\,(4q\log(4eq/\sigma_*))^{k/2}$, $\Lambda_*=2q(k\log(4qk)+\log(64/(\sigma_*\Delta)))$, $b=C_0\sqrt{\Lambda_*}$, $g=\Delta/(100b^k)$, $\kappa=g^2/8$, $M=1/(\sigma^q\tau_0^{q-1})$, $L=1+\lceil\kappa^{-1}\log(100\sqrt M/\eta)\rceil$, $\delta_0=\delta/\sqrt L$, $T=\max\{b,\sqrt{2\log(200L/(\sigma\eta/100)^q)}\}$, $m=\lceil 2T/\delta_0\rceil+3$, $s_0=\kappa/(2(\kappa+\log m))$, $\xi=((\sigma\varepsilon)^q\lambda^{1/2+s_0})^{1/(2s_0)}$, $N_*=(m+1)^{L+1}$, $\beta=1/(1000(N_*+L+1))$, $V=8q(4q-1)^k/(\sigma\xi)$, $n_{\mathrm{CDF}}=\lceil 8g^{-2}\log(2/\beta)\rceil$. The trace knobs are $(L,T,\delta_0,g,\xi,m)$.
--
--   **Formalization Note** Non-integer powers are real powers. On the ranges of Theorem 3.1 every logarithm has argument above $1$, so the ceilings are of positive reals.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Parameter Choices of Algorithm 1, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_GaussPart_Trace

namespace GaussPart

/-- The values of the **Parameter Choices of Algorithm 1**. -/
structure Params where
  lam : ℝ
  eps : ℝ
  τ₀ : ℝ
  σStar : ℝ
  H : ℝ
  ΛStar : ℝ
  b : ℝ
  g : ℝ
  κ : ℝ
  M : ℝ
  L : ℕ
  δ₀ : ℝ
  T : ℝ
  m : ℕ
  s₀ : ℝ
  ξ : ℝ
  NStar : ℕ
  β : ℝ
  V : ℝ
  nCDF : ℕ

/-- The **Parameter Choices of Algorithm 1**, arXiv:2611.05264 (sha256 7e0ca6d4…), p.21 (PDF p.23),
for a universal constant `C₀`: `λ = ε = τ₀ = η/100`, `σ_* = ση/(400q)`,
`H = e (4q log(4eq/σ_*))^{k/2}`, `Λ_* = 2q (k log(4qk) + log(64/(σ_*Δ)))`, `b = C₀ √Λ_*`,
`g = Δ/(100 bᵏ)`, `κ = g²/8`, `M = 1/(σ^q τ₀^{q−1})`, `L = 1 + ⌈κ⁻¹ log(100 √M/η)⌉`,
`δ₀ = δ/√L`, `T = max{b, √(2 log(200L/(ση/100)^q))}`, `m = ⌈2T/δ₀⌉ + 3`,
`s₀ = κ/(2(κ + log m))`, `ξ = ((σε)^q λ^{1/2+s₀})^{1/(2s₀)}`, `N_* = (m + 1)^{L+1}`,
`β = 1/(1000(N_* + L + 1))`, `V = 8q(4q − 1)ᵏ/(σξ)`, `n_CDF = ⌈8g⁻² log(2/β)⌉`.

**Formalization Note.** Non-integer exponents are `Real.rpow`. On the ranges of Theorem 3.1 every
logarithm has argument above `1`, so the ceilings are of positive reals. -/
noncomputable def params (C₀ : ℝ) (k : ℕ) (q σ η δ Δ : ℝ) : Params :=
  let lam := η / 100
  let eps := η / 100
  let τ₀ := η / 100
  let σStar := σ * η / (400 * q)
  let H := Real.exp 1 * (4 * q * Real.log (4 * Real.exp 1 * q / σStar)) ^ ((k : ℝ) / 2)
  let ΛStar := 2 * q * ((k : ℝ) * Real.log (4 * q * k) + Real.log (64 / (σStar * Δ)))
  let b := C₀ * Real.sqrt ΛStar
  let g := Δ / (100 * b ^ k)
  let κ := g ^ 2 / 8
  let M := 1 / (σ ^ q * τ₀ ^ (q - 1))
  let L := 1 + ⌈κ⁻¹ * Real.log (100 * Real.sqrt M / η)⌉₊
  let δ₀ := δ / Real.sqrt L
  let T := max b (Real.sqrt (2 * Real.log (200 * L / (σ * η / 100) ^ q)))
  let m := ⌈2 * T / δ₀⌉₊ + 3
  let s₀ := κ / (2 * (κ + Real.log m))
  let ξ := ((σ * eps) ^ q * lam ^ ((1 : ℝ) / 2 + s₀)) ^ (1 / (2 * s₀))
  let NStar := (m + 1) ^ (L + 1)
  let β := 1 / (1000 * ((NStar : ℝ) + L + 1))
  let V := 8 * q * (4 * q - 1) ^ k / (σ * ξ)
  let nCDF := ⌈8 * g⁻¹ ^ 2 * Real.log (2 / β)⌉₊
  ⟨lam, eps, τ₀, σStar, H, ΛStar, b, g, κ, M, L, δ₀, T, m, s₀, ξ, NStar, β, V, nCDF⟩

/-- The trace parameters of a parameter choice. -/
def Params.knobs (p : Params) : Knobs := ⟨p.L, p.T, p.δ₀, p.g, p.ξ, p.m⟩

end GaussPart


