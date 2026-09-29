-- Prove2me | Definitions.Def_MurtyKabadi_Reduction_encSize
-- name    : MurtyKabadi_Reduction_encSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:13:25.792674+00:00
-- url     : https://prove2.me/theorems/39d8a49a-f31c-47a7-9805-2cd50e15d0d4
-- title:
--   Encoding size $L$ of an integer square matrix (Lemma 2, p. 122)
-- statement:
--   For an integer square matrix $D = (d_{ij})$ of order $m$, its **size** is
--   $$L = m^2 + \sum_{i=1}^m \sum_{j=1}^m \big(1 + \lceil \log_2(|d_{ij}| + 1) \rceil\big),$$
--   the number of bits needed to write the matrix down, in Schrijver's convention (the size of an integer $a$ is $1 + \lceil\log_2(|a|+1)\rceil$ and the size of an $m \times m$ matrix is $m^2$ plus the sizes of its entries).
--
--   This is the quantity $L$ in Lemma 2: a nonzero optimal value of $\min\{x^{\mathsf T}Dx : 0 \le x \le 1\}$ is at most $-2^{-L}$.
--
--   **Formalization Note** The paper writes "$L$ is the size of $D$" without defining it; it is pinned here to Schrijver's encoding size (Schrijver, *Theory of Linear and Integer Programming*, 1986, §2.1, the paper's reference [9]). `Nat.clog 2 k` is $\lceil \log_2 k \rceil$.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 122, Lemma 2 ('L is the size of D'); size convention from Schrijver, Theory of Linear and Integer Programming (1986), §2.1

import Mathlib

namespace MurtyKabadi.Reduction

/-- The encoding size of an integer square matrix `D` of order `m` (Schrijver, *Theory of Linear
and Integer Programming*, §2.1): `m²` plus the sum over the entries of the size
`1 + ⌈log₂(|a| + 1)⌉` of each entry `a`. Used as `L`, "the size of D", in Lemma 2 (p. 122). -/
def encSize {m : ℕ} (D : Matrix (Fin m) (Fin m) ℤ) : ℕ :=
  m * m + ∑ i, ∑ j, (1 + Nat.clog 2 ((D i j).natAbs + 1))

end MurtyKabadi.Reduction


