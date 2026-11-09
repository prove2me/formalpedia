-- Prove2me | Definitions.Def_IntADSat_probMat
-- name    : IntADSat_probMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:16.465195+00:00
-- url     : https://prove2.me/theorems/456cc0eb-321e-4921-8872-ea731db5350f
-- title:
--   Probability for a uniform random $k\times m$ $\{0,1\}$ matrix
-- statement:
--   Let $B$ be a $k\times m$ matrix with independent uniform $\{0,1\}$ entries. The probability of an event about $B$ is the number of $0/1$ patterns in the event divided by $2^{km}$, the number of all patterns.
--
--   **Formalization Note** A pattern is `b : Fin k → Fin m → Bool`, with $B_{ij}=1$ when `b i j` holds and $0$ otherwise.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.2, p.15 (PDF 16)

import Mathlib

set_option autoImplicit false
open scoped Classical

namespace IntADSat

/-- The probability of an event about a `k × m` matrix `B` with independent uniform `{0, 1}` entries
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.2, p.15 (PDF 16)): the number of `0/1` patterns `b : Fin k → Fin m → Bool` in the
event divided by `2^(k·m)`; the matrix is `B i j = 1` if `b i j` and `0` otherwise. -/
noncomputable def probMat (k m : ℕ) (P : (Fin k → Fin m → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / 2 ^ (k * m)

end IntADSat


