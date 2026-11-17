-- Prove2me | Definitions.Def_IntADSat_Supplement_level
-- name    : IntADSat_Supplement_level
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:44:16.156275+00:00
-- url     : https://prove2.me/theorems/c4c3c171-a697-4ac4-b99a-f3f45ca0aa26
-- title:
--   Level $\ell(Q)$ of a rational matrix
-- statement:
--   For a rational matrix $Q$, the **level** $\ell(Q)$ is the least positive integer $\ell$ such that $\ell Q$ has integer entries. It equals the least common multiple of the denominators of the entries of $Q$. Theorem S4.2 bounds it by the exponents of the defect groups.
--
--   **Formalization Note** Defined as the infimum of the (nonempty) set of positive $\ell$ for which every entry of $\ell Q$ has denominator $1$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem S4.2, p.39 (PDF 40)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The **level** `ℓ(Q)` of a rational matrix: the least positive integer `ℓ` such that `ℓQ` is integral
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem S4.2, p.39 (PDF 40)).

**Formalization Note** Defined as `sInf` of the set of positive `ℓ` with every entry of `ℓQ` of
denominator `1`. The set is nonempty (the product of the entry denominators lies in it), so the
infimum is attained and is the least such `ℓ` (it equals the lcm of the entry denominators). -/
noncomputable def level {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  sInf {ℓ : ℕ | 0 < ℓ ∧ ∀ i j, ((ℓ : ℚ) * Q i j).den = 1}

end IntADSat.Supplement


