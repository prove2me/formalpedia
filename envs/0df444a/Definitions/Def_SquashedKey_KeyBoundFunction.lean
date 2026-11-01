-- Prove2me | Definitions.Def_SquashedKey_KeyBoundFunction
-- name    : SquashedKey_KeyBoundFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:30.039276+00:00
-- url     : https://prove2.me/theorems/a62e40a8-8956-4864-ba20-1bce67fdb3fe
-- title:
--   The binary entropy $h_2$ and the correction function $f_1(\varepsilon,K)$
-- statement:
--   **Binary entropy (p.6).** For $p\in[0,1]$,
--   $$
--   h_2(p)=-p\log_2 p-(1-p)\log_2(1-p),
--   $$
--   with $0\log_2 0=0$.
--
--   **The function $f_1$ ((46), p.8).** For a real $\varepsilon$ and a positive integer $K$,
--   $$
--   f_1(\varepsilon,K)=2\varepsilon\log_2 K+2(1+\varepsilon)\,h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right).
--   $$
--
--   $f_1(\sqrt\varepsilon,K)$ is the correction term of Theorem 2, and $f_1(\varepsilon,d)$ with $d=\min\{\dim H_A,\dim H_B\}$ is the right-hand side of the continuity bound (21) for conditional mutual information.
--
--   **Formalization Note** $h_2$ is Mathlib's binary entropy (in nats) divided by $\ln 2$; $K$ is a natural number cast to $\mathbb R$ and $\log_2$ is `Real.logb 2` (which is $0$ at $K=0$; no statement of the mission uses that value non-vacuously).
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, binary entropy h2 after (20), p.6; f1 (46), p.8

import Mathlib

namespace SquashedKey

/-- **Binary entropy in bits**, Wilde, *Squashed entanglement and approximate private states*,
arXiv:1606.08028v3, p.6 (printed p.6 = PDF p.6), after (20):
`h₂(ε) ≡ −ε log₂ ε − (1 − ε) log₂(1 − ε)`.

**Formalization Note** Mathlib's `Real.binEntropy p = −p log p − (1 − p) log(1 − p)` is in nats
(natural logarithm, with `0 log 0 = 0`); dividing by `log 2` converts it to bits. -/
noncomputable def h₂ (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- **The correction function `f₁`**, arXiv:1606.08028v3, (46), p.8 (PDF p.8):
`f₁(ε, K) ≡ 2ε log₂ K + 2(1 + ε) h₂(ε / [1 + ε])`.

**Formalization Note** `K` is a natural number (the key dimension) cast to `ℝ`, and `log₂` is
`Real.logb 2`. At `K = 0` Mathlib's convention `Real.logb 2 0 = 0` applies; no statement of the
mission uses `f₁` at `K = 0` in a non-vacuous way (the key system `Fin 0` is empty and carries no
state). The same formula with `K` replaced by `min {dim H_A, dim H_B}` is the right-hand side of the
continuity bound (21), p.6. -/
noncomputable def f₁ (x : ℝ) (K : ℕ) : ℝ :=
  2 * x * Real.logb 2 (K : ℝ) + 2 * (1 + x) * h₂ (x / (1 + x))

end SquashedKey


