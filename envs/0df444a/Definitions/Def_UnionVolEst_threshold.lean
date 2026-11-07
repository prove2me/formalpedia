-- Prove2me | Definitions.Def_UnionVolEst_threshold
-- name    : UnionVolEst_threshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:45.201647+00:00
-- url     : https://prove2.me/theorems/b1a39489-7b18-4db8-95ae-a78488243ea3
-- title:
--   Storage threshold $\lceil (576/\varepsilon^2)\log(16M/\delta)\rceil$ (Algorithm 1, line 1)
-- statement:
--   For accuracy $\varepsilon$, confidence $\delta$ and $M$ bodies, Alpona stores at most
--   $$
--   \mathrm{threshold} = \left\lceil \frac{576}{\varepsilon^2}\,\log\frac{16M}{\delta} \right\rceil
--   $$
--   points at any time (line 1 of Algorithm 1).
--
--   **Formalization Note** $\log$ is the natural logarithm (the proof of Claim 17 compares with "$\ln 16M/\delta$"). The value is a natural number (`Nat.ceil`), at least $1$ for $\varepsilon,\delta\in(0,1)$, $M\ge1$. The PDF's text layer drops the numerator $576$; the rendered page shows it.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, Algorithm 1 line 1, p.15 (PDF p.17)

import Mathlib

namespace UnionVolEst

/-- The storage threshold of Algorithm 1, line 1 (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, printed p.15, PDF p.17):
`threshold = ⌈(576/ε²) log(16M/δ)⌉`.

**Formalization Note** `log` is the natural logarithm (the proof of Claim 17, printed p.25,
compares with "ln 16M/δ"); the ceiling is `Nat.ceil`, so the value is a natural number (it is
`≥ 1` for `ε, δ ∈ (0, 1)`, `M ≥ 1`). The text layer of the PDF drops the numerator 576; the
rendered page shows it. -/
noncomputable def threshold (ε δ : ℝ) (M : ℕ) : ℕ :=
  ⌈576 / ε ^ 2 * Real.log (16 * M / δ)⌉₊

end UnionVolEst


