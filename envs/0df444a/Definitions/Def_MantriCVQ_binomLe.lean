-- Prove2me | Definitions.Def_MantriCVQ_binomLe
-- name    : MantriCVQ_binomLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:09.657335+00:00
-- url     : https://prove2.me/theorems/4ed53f12-76d6-49aa-bcf5-c65de6b01b42
-- title:
--   The partial binomial sum $\binom{m}{\le t}$
-- statement:
--   $\binom{m}{\le t}=\sum_{a=0}^{\min\{m,t\}}\binom{m}{a}$ is the number of subsets of $[m]$ of size at most $t$, and also the dimension of the space of multilinear polynomials over $\mathbb F_2$ in $m$ variables of degree at most $t$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 12 (PDF p. 14)

import Mathlib

namespace MantriCVQ

/-- `binom(m, ≤t) = ∑_{a=0}^{min(m,t)} binom(m, a)` (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §3, p. 12 (PDF p. 14)), the number of subsets of `[m]` of size at most `t`. -/
def binomLe (m t : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (min m t + 1), m.choose a

end MantriCVQ


