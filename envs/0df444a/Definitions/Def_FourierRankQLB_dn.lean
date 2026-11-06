-- Prove2me | Definitions.Def_FourierRankQLB_dn
-- name    : FourierRankQLB_dn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:08.959031+00:00
-- url     : https://prove2.me/theorems/547c560f-b460-4ef9-b33b-4aedab60aa82
-- title:
--   The hidden-block dimension $d_n=2\lfloor n/2\rfloor$
-- statement:
--   For an ambient dimension $n$, the hidden orthogonal matrix has size
--   $$
--   d_n = 2\lfloor n/2\rfloor .
--   $$
--   Thus $d_n=n$ for even $n$ and $d_n=n-1$ for odd $n$, and $\ell_n=n-d_n\in\{0,1\}$ is the number of padded coordinates.
--
--   The hard family is indexed by $O(d_n)$; the evenness of $d_n$ is what the eigenangle analysis needs.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §4, p.23 and Eq. (36), p.25

import Mathlib

namespace FourierRankQLB

/-- The hidden-block dimension `d_n = 2⌊n/2⌋` of an ambient dimension `n`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §4, p. 23 and Eq. (36), p. 25.

**Formalization Note.** `n / 2` is natural-number division, which is the floor. The second block
has size `ℓ_n = n - dn n ∈ {0, 1}`. -/
def dn (n : ℕ) : ℕ := 2 * (n / 2)

end FourierRankQLB


