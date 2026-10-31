-- Prove2me | Definitions.Def_OgawaNagaoka_E0
-- name    : OgawaNagaoka_E0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:24:18.77693+00:00
-- url     : https://prove2.me/theorems/41e1a5e5-a469-463f-96b8-8ef78ab3f649
-- title:
--   $E_0(s,\pi)=-\log\mathrm{Tr}(\sum_i\pi_i\rho_i^{1/(s+1)})^{s+1}$ (eq. 11)
-- statement:
--   With $s=\beta-1$,
--
--   $$
--   E_0(s,\pi)=-\log\Big(\mathrm{Tr}\Big(\sum_{i=1}^a\pi_i\rho_i^{\frac1{s+1}}\Big)^{s+1}\Big).
--   $$
--
--   This is the quantum analogue of Gallager's function; Theorem 1 bounds the error probability by $1-\exp[-n(-sR+\min_\pi E_0(s,\pi))]$ for $-1<s\le0$.
--
--   **Formalization Note** Natural logarithm. For $-1<s\le0$, a probability vector $\pi$ and density matrices the trace is positive, so Lean's `Real.log` is the true logarithm.
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, eq. (11), p.6

import Mathlib
import Definitions.Def_OgawaNagaoka_traceGallager

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, eq. (11), p.6: with `s = β − 1`,
`E₀(s, π) = − log ( Tr (Σ_{i=1}^a π_i ρ_i^{1/(s+1)})^{s+1} )`.

**Formalization Note.** `E0 ρ s π = −Real.log (traceGallager ρ (s + 1) π)`, natural logarithm.
The paper uses it for `−1 < s ≤ 0` and `π` a probability distribution; for density matrices `ρ_i`
the trace is then positive, so the logarithm is the true one (Lean's `Real.log` would return `0`
at `0`). -/
noncomputable def E0 {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (s : ℝ) (π : A → ℝ) : ℝ :=
  -Real.log (traceGallager ρ (s + 1) π)

end OgawaNagaoka


