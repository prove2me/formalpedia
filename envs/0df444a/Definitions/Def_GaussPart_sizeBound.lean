-- Prove2me | Definitions.Def_GaussPart_sizeBound
-- name    : GaussPart_sizeBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:30.002397+00:00
-- url     : https://prove2.me/theorems/6b7f3656-c099-4246-a348-6fee585597d0
-- title:
--   The size parameter $B$ of the partitioning theorem
-- statement:
--   For a natural number $C$ (standing for all implicit constants), $k\in\mathbb N$ and reals $q,\sigma,\eta,\delta,\Delta$,
--   $$B=\exp\!\Big(\frac{C\,(qk)^{Ck}}{\Delta^{C}}\,\log^{Ck}\!\frac{2}{\sigma\eta}\,\log\frac2\delta\Big).$$
--
--   This is the quantity $B=\exp\big(O((qk)^{O(k)})/\Delta^{O(1)}\cdot\log^{O(k)}(2/(\sigma\eta))\log(2/\delta)\big)$ of Theorem 3.1: it bounds the number of cells, the inverse mass of a certified cell, and (with factors $d^k$, $d^{O(k)}$) the sample count and the running time.
--
--   **Formalization Note** One constant $C$ replaces the several implicit constants of the $O(\cdot)$ notation. On the ranges of Theorem 3.1 ($qk\ge1$, $1/\Delta>2$, $\log(2/(\sigma\eta))>1$, $\log(2/\delta)>1$) this loses nothing: a larger constant in any place can be absorbed by enlarging $C$. Powers are natural powers; $\log$ is natural.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 3.1, p.14 (PDF p.16)

import Mathlib

namespace GaussPart

/-- The quantity `B` of **Theorem 3.1**, arXiv:2611.05264 (sha256 7e0ca6d4…), p.14 (PDF p.16):
`B = exp( O((qk)^{O(k)}) / Δ^{O(1)} · log^{O(k)}(2/(ση)) · log(2/δ) )`.

**Formalization Note.** All implicit constants are the one natural number `C`, chosen before every
parameter by the theorem: `exp( C (qk)^{Ck} / Δ^C · (log(2/(ση)))^{Ck} · log(2/δ) )`, with natural
powers. One `C` loses nothing, since on the stated ranges `qk ≥ 1`, `1/Δ > 2`,
`log(2/(ση)) > log 4 > 1` and `log(2/δ) > 1`. `Real.log` is the natural logarithm. -/
noncomputable def sizeBound (C k : ℕ) (q σ η δ Δ : ℝ) : ℝ :=
  Real.exp ((C : ℝ) * (q * k) ^ (C * k) / Δ ^ C * Real.log (2 / (σ * η)) ^ (C * k) *
    Real.log (2 / δ))

end GaussPart


