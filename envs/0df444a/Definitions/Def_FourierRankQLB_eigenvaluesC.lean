-- Prove2me | Definitions.Def_FourierRankQLB_eigenvaluesC
-- name    : FourierRankQLB_eigenvaluesC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:04.913194+00:00
-- url     : https://prove2.me/theorems/51d472fd-fc9c-46e5-891e-27fbdad1d296
-- title:
--   The complex eigenvalues of an orthogonal matrix
-- statement:
--   The multiset of complex eigenvalues of $Q\in O(d)$, with algebraic multiplicity: the roots over $\mathbb C$ of its characteristic polynomial.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.3, p.20

import Mathlib
import Definitions.Def_FourierRankQLB_Od

namespace FourierRankQLB

/-- The complex eigenvalues of `Q`, with algebraic multiplicity: the roots of its characteristic
polynomial over `ℂ`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.3, p. 20. -/
noncomputable def eigenvaluesC {d : ℕ} (Q : Od d) : Multiset ℂ :=
  (((Q : Matrix (Fin d) (Fin d) ℝ).map (algebraMap ℝ ℂ)).charpoly).roots

end FourierRankQLB


