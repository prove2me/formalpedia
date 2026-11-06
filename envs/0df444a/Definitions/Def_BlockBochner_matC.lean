-- Prove2me | Definitions.Def_BlockBochner_matC
-- name    : BlockBochner_matC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:11.050037+00:00
-- url     : https://prove2.me/theorems/644f9c46-4d21-4eca-b68c-dcaf1960a5ee
-- title:
--   $C=((M^{-1})_T)^{-1}$, $M=I-A$
-- statement:
--   For a $V\times V$ matrix $A$, let $M=I-A$. For a set of sites $T$,
--   $$C=\bigl((M^{-1})_T\bigr)^{-1},$$
--   where $N_T$ is the principal submatrix of $N$ with rows and columns in $T$. $C$ is a Schur complement of $M$.
--
--   **Formalization Note** For admissible $A$, $M$ and $(M^{-1})_T$ are positive definite, so both inverses are genuine.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 3, p.4

import Mathlib
import Definitions.Def_BlockBochner_blockUnion

namespace BlockBochner

/-- **`C = ((M⁻¹)_T)⁻¹` with `M = I − A`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 3, p.4: `M = I − A`, `C = ((M^{−1})_T)^{−1}`,
where `M_α` is the principal submatrix of `M` with rows and columns `α`.

**Formalization Note** Indexed by the sites of `T = blockUnion T`. Matrix inverses are Mathlib's
`⁻¹`; under `λ_max(A) < 1` both `M` and `(M⁻¹)_T` are positive definite, so both inverses are
genuine. -/
noncomputable def matC {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (A : Matrix V V ℝ)
    (T : Fin m → Finset V) : Matrix (blockUnion T) (blockUnion T) ℝ :=
  ((1 - A)⁻¹.submatrix Subtype.val Subtype.val)⁻¹

end BlockBochner


