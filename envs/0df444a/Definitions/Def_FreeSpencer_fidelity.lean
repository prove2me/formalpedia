-- Prove2me | Definitions.Def_FreeSpencer_fidelity
-- name    : FreeSpencer_fidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:24.834794+00:00
-- url     : https://prove2.me/theorems/02537d48-caad-4c67-a8ce-f951eef53a6f
-- title:
--   The unsquared fidelity $F(S,M)$
-- statement:
--   For positive semidefinite real matrices,
--   $$F(S,M)=\mathrm{Tr}\sqrt{S^{1/2}MS^{1/2}}.$$
--   It is the unsquared quantum fidelity. It is jointly concave, and $0\le F(S,M)\le\sqrt{\mathrm{Tr}\,S\,\mathrm{Tr}\,M}$.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.2, p.19; Lemma 4.2, p.27

import Mathlib
import Definitions.Def_MatrixLewis_mpow

namespace FreeSpencer

/-- The unsquared quantum fidelity `F(S, M) = Tr √(S^{1/2} M S^{1/2})` of positive semidefinite
real matrices. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.2, p.19; Lemma 4.2, p.27.

**Formalization Note** `WildeQIT_uhlmannFidelity` on the platform is complex, squared and defined
by purifications, so it is not this object. -/
noncomputable def fidelity {ι : Type*} [Fintype ι] [DecidableEq ι] (S M : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (MatrixLewis.mpow (1 / 2) (MatrixLewis.mpow (1 / 2) S * M * MatrixLewis.mpow (1 / 2) S))

end FreeSpencer


