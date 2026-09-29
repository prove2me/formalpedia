-- Prove2me | Definitions.Def_HighDimStat_Pca_Ptilde
-- name    : HighDimStat_Pca_Ptilde
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:11:57.011648+00:00
-- url     : https://prove2.me/theorems/c2d72721-7857-4641-9d4d-70531b8c0e5f
-- title:
--   The transformed perturbation vector p-tilde of Eq. (8.11)
-- statement:
--   This is the **transformed perturbation vector** $\tilde p$ of Wainwright's Eq. (8.11), the
--   piece of the perturbation $P$ that couples the top eigendirection $\theta^*$ to the rest of
--   the space, central to Theorem 8.5's error bound.
--
--   For $P \in \mathbb R^{d\times d}$ and a unit vector $\theta^* \in \mathbb R^d$,
--
--   $$
--   \tilde p \;:=\; P\theta^* - \langle P\theta^*, \theta^*\rangle\,\theta^*,
--   $$
--
--   the component of $P\theta^*$ orthogonal to $\theta^*$.
--
--   **Formalization Note** The book defines $\tilde p \in \mathbb R^{d-1}$ as the off-diagonal
--   block of $P$ transformed into an eigenbasis $U$ of $\Sigma$ with first column $\theta^*$,
--   Eq. (8.11): $\bar P = U^\top P U$ has off-diagonal block $\tilde p = U_2^\top P\theta^*$
--   where $U_2$ is any orthonormal basis of $\theta^{*\perp}$. This formalization instead gives
--   the *basis-independent* representative of that same vector inside $\mathbb R^d$ (its
--   $\ell^2$-norm, the only quantity Theorem 8.5's bound actually uses, is identical to
--   $\|\tilde p\|_2$ for any choice of $U_2$, since $U_2$ is orthonormal).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 242 (PDF p. 262), Eq. (8.11)

import Mathlib

namespace HighDimStat.Pca

/-- The transformed perturbation vector `p̃ ∈ ℝ^{d-1}` of Wainwright, *High-Dimensional
Statistics* (2019), Eq. (8.11), realized basis-independently as the component of `Pθ*`
orthogonal to `θ*` (equivalently, the off-diagonal block `U₂ᵀPθ*` of `P` transformed into any
orthonormal eigenbasis `U` of `Σ` with first column `θ*` — a quantity that does not depend on
the choice of the remaining `d-1` basis vectors `U₂`). -/
def ptilde {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (θstar : Fin d → ℝ) : Fin d → ℝ :=
  fun j => (P.mulVec θstar) j - (∑ i, (P.mulVec θstar) i * θstar i) * θstar j

end HighDimStat.Pca


