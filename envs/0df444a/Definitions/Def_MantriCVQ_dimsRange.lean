-- Prove2me | Definitions.Def_MantriCVQ_dimsRange
-- name    : MantriCVQ_dimsRange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:19.509004+00:00
-- url     : https://prove2.me/theorems/699e93fb-fbb4-4cd5-8080-fc297fc18066
-- title:
--   Heights and dimensions of an instance
-- statement:
--   For $n\ge1$,
--   $$h_{\max}(n)=\lfloor \log_2 n/8\rfloor,\qquad m_i=8\lfloor n/(8\cdot16^i)\rfloor.$$
--   `dimsRange n u c` lists $m_{u+c-1},\dots,m_u$ from the top down. It gives the dimensions of an instance of height $h$ from the root down (`u = 0`, `c = h`) and of a block of height $j$ with dimensions $m_u,\dots,m_{u+j-1}$ (`c = j`).
--
--   **Formalization Note** $h_{\max}$ is `Nat.log 2 n / 8`, which equals $\lfloor\log_2 n/8\rfloor$ for $n\ge1$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Eq. (4.1), p. 16 (PDF p. 18); §4.2, p. 17 (PDF p. 19)

import Mathlib

namespace MantriCVQ

/-- `h_max(n) = ⌊log n / 8⌋` (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Eq. (4.1), p. 16
(PDF p. 18)), the largest height of an instance of size `n`. Logarithms are to base two. -/
def hmax (n : ℕ) : ℕ := Nat.log 2 n / 8

/-- `m_i = 8 ⌊n / (8 · 16^i)⌋` (Eq. (4.1), p. 16), the dimension of the nodes at level `i`. -/
def dim (n i : ℕ) : ℕ := 8 * (n / (8 * 16 ^ i))

/-- The dimensions `[m_{u+c-1}, …, m_{u+1}, m_u]` from the top down: `dimsRange n 0 h` lists the
dimensions of an instance of height `h` from the root down, and `dimsRange n u j` those of a block of
height `j` with dimensions `m_u, …, m_{u+j-1}` (§4.2, p. 17). -/
def dimsRange (n u c : ℕ) : List ℕ :=
  (List.range c).reverse.map fun p => dim n (u + p)

end MantriCVQ


