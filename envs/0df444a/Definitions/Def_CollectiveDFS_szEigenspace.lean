-- Prove2me | Definitions.Def_CollectiveDFS_szEigenspace
-- name    : CollectiveDFS_szEigenspace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:57.384889+00:00
-- url     : https://prove2.me/theorems/53ada96a-7bbd-4974-9628-0a485b9e3296
-- title:
--   Eigenspace of $s_z$ for magnetic number $m$
-- statement:
--   For a half-integer $m$, this is the eigenspace
--   $$\{\psi:\ s_z\psi=m\,\psi\},\qquad s_z=\tfrac12 S_z=\tfrac12\sum_{j=1}^n\sigma^j_z,$$
--   of the collective spin along $z$.
--
--   **Formalization Note** Spin and magnetic labels are doubled: a natural number $j_2=2J$ and an integer $m_2=2m$, so half-integers are exact. With (5.2), a basis string with $p$ zeros and $q$ ones has $m=(p-q)/2$; §VII calls $|1\rangle$ "up" only symbolically (p.21), which is the mirror image $m\mapsto -m$. Every statement quantifies over all legal $m$.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (5.1), p.12; eqs. (7.10)–(7.11), p.23

import Mathlib
import Definitions.Def_CollectiveDFS_partialS

open QAlgorithms

namespace CollectiveDFS

/-- The eigenspace of the collective spin `s_z = ½ S_z = ½ Σ_j σ_z^j` for the magnetic number
`m = m2/2` (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eqs. (5.1), p.12, and (7.10)–(7.11), p.23, PDF pp.12, 23).

**Formalization Note** Doubled label `m2 = 2m : ℤ`. With (5.2), `σ_z|0⟩ = |0⟩`, a basis string
with `p` zeros and `q` ones has `m = (p − q)/2`. §VII's symbolic convention (p.21) is the
mirror image `m ↦ −m`; statements quantify over all legal `m`. -/
noncomputable def szEigenspace (n : ℕ) (m2 : ℤ) : Submodule ℂ (EuclideanSpace ℂ (Qubits n)) :=
  LinearMap.ker (Matrix.toEuclideanLin
    ((1 / 2 : ℂ) • partialS n n 2 - ((m2 : ℂ) / 2) • (1 : Matrix (Qubits n) (Qubits n) ℂ)))

end CollectiveDFS


