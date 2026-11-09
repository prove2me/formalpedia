-- Prove2me | Definitions.Def_CodedSorting_Exponent
-- name    : CodedSorting_Exponent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:53.062968+00:00
-- url     : https://prove2.me/theorems/a0a00332-7631-48ab-b3e5-cdff38390fcb
-- title:
--   The exponent $\varepsilon=3/200000$ and $\tau=1-\varepsilon$
-- statement:
--   The exponent of the main sorting bound is the fixed constant
--
--   $$\varepsilon=\frac{3}{200000}=1.5\times10^{-5},\qquad \tau=1-\varepsilon .$$
--
--   The paper takes this value in Theorem 3.1 and verifies $\varepsilon\ln 512<33/338432$ in Lemma B.1, which yields $S/W<512^{\tau}$ for the circuit parameters of Corollary 5.4.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.4 (PDF 5) after Theorem 3.1; §6.1, p.19 (PDF 20); Lemma B.1, p.36 (PDF 37)

import Mathlib

namespace CodedSorting

/-- The exponent `ε = 3/200000 = 1.5 × 10⁻⁵` of Theorem 3.1 (arXiv:2610.20079, held version,
sha256 6e149d97…8850b, p.4: "we take ε = 1.5 × 10⁻⁵"; Lemma B.1, p.36: "ε = 3/200000"). -/
noncomputable def eps : ℝ := 3 / 200000

/-- `τ = 1 − ε` (§6.1, p.19; Corollary 5.4, p.18). -/
noncomputable def tau : ℝ := 1 - eps

end CodedSorting


