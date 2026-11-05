-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_dseq
-- name    : BauerleRiederMDP_Indifference_Market_dseq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:52.103379+00:00
-- url     : https://prove2.me/theorems/cb1c8826-1890-4d5e-95d7-348e3c13adf7
-- title:
--   The functions $d_n$ of Theorem 4.9.4
-- statement:
--   For a claim $H$ with maturity $N$ the functions $d_n$ are given by the backward recursion
--   $$
--   d_N(s,\hat s):=e^{\gamma h(s,\hat s)},\qquad
--   d_n(s,\hat s):=\inf_{a\in\mathbb R}\mathbb E\Bigl[e^{-\gamma a(\tilde R_{n+1}-1)}\,d_{n+1}\bigl(s\tilde R_{n+1},\hat s\hat R_{n+1}\bigr)\Bigr].
--   $$
--   They describe the value functions and the indifference prices of Theorem 4.9.4.
--
--   **Formalization Note** The recursion is carried by the number of periods to go, and $d_n$ is the entry with $N-n$ periods to go, so only $n\le N$ carries meaning. Every $d_n$ is positive, so each infimum is over a nonempty family bounded below by $0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.9.4, p.139

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market
import Definitions.Def_BauerleRiederMDP_Indifference_Claim

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace Market

/-- The recursion of Theorem 4.9.4 a) by the number of periods to go (Bäuerle & Rieder, Markov
Decision Processes with Applications to Finance (2011), Theorem 4.9.4, p.139, PDF 153): `dGo H k`
is `d_{N-k}`. -/
noncomputable def dGo (M : Market) (H : Claim) : ℕ → ℝ → ℝ → ℝ
  | 0, s, ŝ => Real.exp (M.γ * H s ŝ)
  | k + 1, s, ŝ =>
      ⨅ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rt ω - 1)) *
        dGo M H k (s * M.Rt ω) (ŝ * M.Rh ω) ∂M.P

/-- The functions `d_n` of Theorem 4.9.4 a) for the claim `H` with maturity `N` (p.139, PDF 153):
`d_N(s, ŝ) := e^{γ h(s, ŝ)}` and
`d_n(s, ŝ) := inf_{a ∈ ℝ} 𝔼[e^{-γ a (R̃_{n+1} - 1)} d_{n+1}(s R̃_{n+1}, ŝ R̂_{n+1})]`.

**Formalization Note.** Only `n ≤ N` carries meaning (the subtraction `N - n` is truncated). The
pairs `(R̃_{n+1}, R̂_{n+1})` all have the law of `(R̃, R̂)` on `Ω`, and each `d_n` depends on them
only through that law. All `d_n` are positive, so each infimum is over a nonempty family bounded
below by `0`. -/
noncomputable def dseq (M : Market) (N : ℕ) (H : Claim) (n : ℕ) (s ŝ : ℝ) : ℝ :=
  M.dGo H (N - n) s ŝ

end Market

end BauerleRiederMDP.Indifference


