-- Prove2me | Definitions.Def_ConeLifts_StableSet_HasPSDFactorization
-- name    : ConeLifts_StableSet_HasPSDFactorization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:17:24.816569+00:00
-- url     : https://prove2.me/theorems/e6195b58-23ab-4589-aa40-51abefbd059e
-- title:
--   $\mathcal S^k_+$-factorization of a matrix: $M_{ij} = \mathrm{tr}(A_i B_j)$ with $A_i, B_j$ positive semidefinite
-- statement:
--   Let $M = (M_{ij})$ be a real matrix. An **$\mathcal S^k_+$-factorization** of $M$ is a family of $k\times k$ real symmetric positive semidefinite matrices $A_i$, one for each row, and $B_j$, one for each column, such that
--
--   $$
--   \langle A_i, B_j\rangle = \mathrm{tr}(A_i B_j) = M_{ij} \quad \text{for all } i, j.
--   $$
--
--   This is Definition 3.2 for $K = \mathcal S^k_+$ with the trace inner product, under which $\mathcal S^k_+$ is self-dual, so both families lie in $\mathcal S^k_+$.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef` (which includes symmetry) on `Matrix (Fin k) (Fin k) ℝ`; the pairing is `Matrix.trace (A * B)`. Both factors are required to be positive semidefinite explicitly rather than through a computed dual cone, because in the space of all matrices the dual of $\mathcal S^k_+$ would also contain matrices with skew-symmetric parts.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 9, Definition 3.2 with K = S^k_+ (self-duality of S^k_+: p. 3)

import Mathlib

namespace ConeLifts.StableSet

/-- A **`Sᵏ₊`-factorization** of a matrix `M` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 3.2, p. 9, with `K = Sᵏ₊`): real `k × k` positive semidefinite matrices `Aᵢ` (one per
row) and `Bⱼ` (one per column) with `⟨Aᵢ, Bⱼ⟩ = tr(Aᵢ Bⱼ) = M_ij`. The pairing is the trace
inner product of symmetric matrices, under which `Sᵏ₊` is self-dual (p. 3), so both families are
required to be positive semidefinite. -/
def HasPSDFactorization (k : ℕ) {ι κ : Type*} (M : Matrix ι κ ℝ) : Prop :=
  ∃ (a : ι → Matrix (Fin k) (Fin k) ℝ) (b : κ → Matrix (Fin k) (Fin k) ℝ),
    (∀ i, (a i).PosSemidef) ∧ (∀ j, (b j).PosSemidef) ∧ ∀ i j, (a i * b j).trace = M i j

end ConeLifts.StableSet


