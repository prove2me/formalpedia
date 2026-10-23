-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch07_eisensteinQTrunc
-- name    : RamanujanLostNotebook_PartIII_ch07_eisensteinQTrunc
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:24:31.583974+00:00
-- url     : https://prove2.me/theorems/d73ed257-5cde-49f6-aadb-7c128dcf2565
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 7: eisensteinQTrunc
-- statement:
--   Truncated Eisenstein series `Q`: the polynomial `1 + 240 ∑_{m=1}^{N} σ_3(m) X^m`.
--   Ramanujan's `Q(q) = 1 + 240 ∑_{n ≥ 1} n^3 q^n / (1 - q^n) = 1 + 240 ∑_{m ≥ 1} σ_3(m) q^m`
--   ((5.1.2), p. 94; `E_4(τ)` in modern notation, p. 205); this polynomial is `Q` modulo `q^{N+1}`.
--   Reference: `Q = 1 + 240 q + 2160 q^2 + 6720 q^3 + …`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch07_divisorSigma

namespace RamanujanLostNotebook.PartIII

/-- Truncated Eisenstein series `Q`: the polynomial `1 + 240 ∑_{m=1}^{N} σ_3(m) X^m`.
Ramanujan's `Q(q) = 1 + 240 ∑_{n ≥ 1} n^3 q^n / (1 - q^n) = 1 + 240 ∑_{m ≥ 1} σ_3(m) q^m`
((5.1.2), p. 94; `E_4(τ)` in modern notation, p. 205); this polynomial is `Q` modulo `q^{N+1}`.
Reference: `Q = 1 + 240 q + 2160 q^2 + 6720 q^3 + …`. -/
noncomputable def eisensteinQTrunc (N : ℕ) : Polynomial ℤ :=
  1 + 240 * ∑ m ∈ Finset.Icc 1 N, Polynomial.C (divisorSigma 3 m) * Polynomial.X ^ m

end RamanujanLostNotebook.PartIII


