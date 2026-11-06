-- Prove2me | Definitions.Def_NewtonLCP_Encoding
-- name    : NewtonLCP_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:06.01076+00:00
-- url     : https://prove2.me/theorems/afb1b14b-99ef-4486-b050-1d5fb5edf25e
-- title:
--   Encoding lengths $\mathrm{length}(M)$ and $L=\mathrm{length}(M,q)$
-- statement:
--   For a rational matrix $M\in\mathbb Q^{n\times n}$ and vector $q\in\mathbb Q^n$,
--
--   $$\mathrm{length}(M)=\sum_{i,j}\mathrm{bitSize}(M_{ij}),\qquad L=\mathrm{length}(M,q)=\mathrm{length}(M)+\sum_i\mathrm{bitSize}(q_i),$$
--
--   where $\mathrm{bitSize}(p/r)$ is the number of binary digits of $|p|$ plus that of $r$ plus one, for $p/r$ in lowest terms.
--
--   $L$ is the input size in Theorem 1.2 and Lemma 8.3; $\mathrm{length}(M)$ appears in Theorem 8.6 and in line 18 of Algorithm 3.
--
--   **Formalization Note** bitSize is the published platform definition `ConsensusHalvingItems.Additive.bitSize`. Any standard encoding is within constant factors of this one, which the $O(\cdot)$ statements absorb.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), §2.1, p.6; Theorem 1.2, p.3; Theorem 8.6 and Algorithm 3 lines 17–18, pp.31–32

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_bitSize

namespace NewtonLCP

/-!
# Encoding lengths `length(M)` and `L = length(M, q)`

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), §2.1 "length(A)", p.6; Theorem 1.2, p.3;
Theorem 8.6 and Algorithm 3 lines 17–18, pp.31–32.

**Formalization Note.** The encoding length of a rational is the published
`ConsensusHalvingItems.Additive.bitSize q = size|num q| + size(den q) + 1` (reduced form); the
length of a matrix or vector is the sum over its entries. Any standard encoding of `(M, q)` is
within constant factors of this one, which is what the `O(·)` statements use.
-/

/-- `length(M) = Σᵢⱼ bitSize(Mᵢⱼ)` for a rational `n × n` matrix. -/
def encLenM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  ∑ i, ∑ j, ConsensusHalvingItems.Additive.bitSize (M i j)

/-- `L = length(M, q) = length(M) + Σᵢ bitSize(qᵢ)`, the total encoding length of `(M, q)`. -/
def encLen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (q : Fin n → ℚ) : ℕ :=
  encLenM M + ∑ i, ConsensusHalvingItems.Additive.bitSize (q i)

end NewtonLCP


