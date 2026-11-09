-- Prove2me | Definitions.Def_HybridXorLift_outer
-- name    : HybridXorLift_outer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:44.288515+00:00
-- url     : https://prove2.me/theorems/3c5b5837-b1c4-4208-a510-da852e9180b7
-- title:
--   Outer string $\sigma(x)$ of a physical input
-- statement:
--   A **physical input** is a string $x = (x_{ij})_{i \in [n],\, j \in [r]}$, viewed as $n$ blocks of $r$ bits. Its **outer string** $\sigma(x) \in \{0,1\}^n$ has coordinates
--   $$
--   \sigma(x)_i = \bigoplus_{j=1}^r x_{ij}, \qquad i \in [n],
--   $$
--   the parity of block $i$.
--
--   For every outer string $z$ the **parity fibre** $\sigma^{-1}(z)$ consists of the physical inputs that encode $z$; it has $2^{n(r-1)}$ elements when $r \ge 1$.
--
--   **Formalization Note** A physical input is a function on pairs $(i, j)$ with $i \in \{0,\dots,n-1\}$ and $j \in \{0,\dots,r-1\}$ (block $i+1$, position $j+1$ of the paper).
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.3, Eq. (2.2), p.10 (PDF p.12)

import Definitions.Def_HybridXorLift_blockParity

namespace HybridXorLift

/-- The outer string `σ(x) ∈ {0,1}ⁿ` of a physical input `x = (x_{ij})` with `n` blocks of `r`
bits: `σ(x)_i = ⊕_{j=1}^r x_{ij}` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.3, Eq. (2.2), p.10 (PDF p.12)).

**Formalization Note** A physical input is a function on `Fin n × Fin r`; the pair `(i, j)` is
block `i + 1`, position `j + 1` of the paper (0-based indices). -/
def outer {n r : ℕ} (x : Fin n × Fin r → Bool) : Fin n → Bool :=
  fun i => blockParity r (fun j => x (i, j))

end HybridXorLift


