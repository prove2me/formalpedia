-- Prove2me | Definitions.Def_TentNoise_PhiT
-- name    : TentNoise_PhiT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:08.84605+00:00
-- url     : https://prove2.me/theorems/be035159-5392-4e0d-b1b6-44e6402397ff
-- title:
--   The small-noise path certificate $\Phi_T$
-- statement:
--   Let $\varphi(x)=x-\tfrac12$ and $\psi(x)=\cos(\pi x)$, and let $m\ge1$ be a lag. For a path $x=(x_0,\dots,x_T)$ with $T\ge2m$, the **small-noise path certificate** is
--
--   $$
--   \Phi_T(x):=\frac{1}{(2+\pi)(T-m+1)}\sum_{t=0}^{T-m}\varphi(x_t)\,\psi(x_{t+m}).
--   $$
--
--   It averages a lagged correlation over all starting times, so that each coordinate appears in at most two summands; this keeps its Lipschitz constant for $\rho_{1,T}$ bounded independently of $T$.
--
--   **Formalization Note** The sum runs over $t\in\{0,\dots,T-m\}$; with $T\ge2m$ (Lemma B.7's hypothesis) the natural-number subtraction $T-m$ is the integer one and every index $t+m\le T$. The helper `pathCoord` reads coordinate $i$ of a path ($0$ beyond $T$, never used).
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.7, p.30 (PDF p.30), eq. (72); φ, ψ from pp.27–28

import Mathlib

namespace TentNoise

/-- Coordinate `i` of a path `x : Fin (T+1) → ℝ` (`0` for `i > T`, never used). -/
noncomputable def pathCoord {T : ℕ} (x : Fin (T + 1) → ℝ) (i : ℕ) : ℝ :=
  if h : i < T + 1 then x ⟨i, h⟩ else 0

/-- The small-noise path certificate
`Φ_T(x) := (1/((2 + π)(T − m + 1))) ∑_{t=0}^{T−m} φ(x_t) ψ(x_{t+m})`, with `φ(x) = x − 1/2` and
`ψ(x) = cos(πx)` (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.7, p.30, eq. (72); `φ` and `ψ` from pp.27–28).

**Formalization Note** The sum is over `t ∈ {0, …, T − m}` (`Finset.range (T − m + 1)`); Lemma B.7
assumes `T ≥ 2m`, so the natural-number subtraction is the integer one and every index `t + m ≤ T`.
The normalizing factor uses the real number `T − m + 1`. -/
noncomputable def PhiT (T m : ℕ) (x : Fin (T + 1) → ℝ) : ℝ :=
  1 / ((2 + Real.pi) * ((T : ℝ) - m + 1)) *
    ∑ t ∈ Finset.range (T - m + 1),
      (pathCoord x t - 1 / 2) * Real.cos (Real.pi * pathCoord x (t + m))

end TentNoise


