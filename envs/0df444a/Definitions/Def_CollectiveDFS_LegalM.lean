-- Prove2me | Definitions.Def_CollectiveDFS_LegalM
-- name    : CollectiveDFS_LegalM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:15.260363+00:00
-- url     : https://prove2.me/theorems/99d5c39e-8a96-4783-a33c-9f327846f357
-- title:
--   Legal magnetic number $m$ for spin $J$
-- statement:
--   A magnetic number $m$ is **legal** for spin $J$ when $|m|\le J$ and $J-m$ is an integer, i.e. $m\in\{-J,-J+1,\dots,J\}$.
--
--   **Formalization Note** Spin and magnetic labels are doubled: a natural number $j_2=2J$ and an integer $m_2=2m$, so half-integers are exact. The condition reads $|m_2|\le j_2$ and $j_2-m_2$ even.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (7.11), p.23

import Mathlib

namespace CollectiveDFS

/-- `m = m2/2` is a magnetic number of spin `J = j2/2`: `|m| ≤ J` and `J − m` an integer
(standard angular momentum, used for `m_J` in Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, (7.11), p.23, PDF p.23).

**Formalization Note** Doubled labels: `|m2| ≤ j2` and `j2 − m2` even. -/
def LegalM (j2 : ℕ) (m2 : ℤ) : Prop :=
  |m2| ≤ (j2 : ℤ) ∧ Even ((j2 : ℤ) - m2)

end CollectiveDFS


