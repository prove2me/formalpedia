-- Prove2me | Definitions.Def_HSElemKernel_bitLen
-- name    : HSElemKernel_bitLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:53.185879+00:00
-- url     : https://prove2.me/theorems/7a2ae297-f335-447e-9294-629e7a61610d
-- title:
--   Bit length $|c|$ of an input list
-- statement:
--   The **bit length** of a list $c = [c_1, \dots, c_r]$ of natural numbers is
--   $$|c| = \sum_{i=1}^{r} \big(\mathrm{size}(c_i) + 1\big),$$
--   where $\mathrm{size}(x)$ is the number of binary digits of $x$ ($\mathrm{size}(0) = 0$): each number written in binary, with one separator. Polynomial running times in the mission are polynomials in this length.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3.1, p.6 ("polynomial-time algorithm")

import Mathlib

namespace HSElemKernel

/-- The bit length `|c|` of a list of natural numbers written in binary with one separator per
entry: `∑ (size(x) + 1)` (Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…, Section 3.1,
p.6: "polynomial-time algorithm"). Running times of the mission are polynomials in this length. -/
def bitLen (c : List ℕ) : ℕ :=
  (c.map (fun x => Nat.size x + 1)).sum

end HSElemKernel


