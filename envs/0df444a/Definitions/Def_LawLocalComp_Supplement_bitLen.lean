-- Prove2me | Definitions.Def_LawLocalComp_Supplement_bitLen
-- name    : LawLocalComp_Supplement_bitLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:03:03.011773+00:00
-- url     : https://prove2.me/theorems/f5799172-e645-43b7-a39f-6e7086305ef2
-- title:
--   Bit length of a list of rational (atom, mass) pairs
-- statement:
--   For a finite list $\ell = [(x_1, m_1), \dots, (x_k, m_k)]$ of pairs of rational numbers, its **bit length** is
--   $$
--   \operatorname{bitLen}(\ell) = \sum_{i=1}^{k} \bigl(\operatorname{bits}(x_i) + \operatorname{bits}(m_i)\bigr),
--   $$
--   the total number of bits needed to write all atoms $x_i$ and masses $m_i$, where $\operatorname{bits}(a/b) = 1 + \operatorname{size}(|a|) + \operatorname{size}(b)$ for $a/b$ in lowest terms and $\operatorname{size}(n)$ is the number of binary digits of $n$.
--
--   It is the size of the description of a finite rational law given as a list of atoms with their probabilities.
--
--   **Formalization Note** $\operatorname{bits}$ is the published `WeightedCongestionBR.bitLen` (one sign bit plus the binary lengths of the numerator and the denominator).
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 6.1, p.9; Theorem 6.2, p.10

import Mathlib
import Definitions.Def_WeightedCongestionBR_bitLen

namespace LawLocalComp

namespace Supplement

/-- **The bit length of a list of rational (atom, mass) pairs.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 6.1, p.9; Theorem 6.2, p.10.

`bitLen ℓ = ∑_{(x, m) ∈ ℓ} (ℓ(x) + ℓ(m))`: the total binary length of all atoms and masses written
in the list, where `ℓ(q) = 1 + size|a| + size b` for `q = a/b` in lowest terms is the published
`WeightedCongestionBR.bitLen` (sign bit, numerator and denominator in binary). -/
def bitLen (l : List (ℚ × ℚ)) : ℕ :=
  (l.map fun z => WeightedCongestionBR.bitLen z.1 + WeightedCongestionBR.bitLen z.2).sum

end Supplement

end LawLocalComp


