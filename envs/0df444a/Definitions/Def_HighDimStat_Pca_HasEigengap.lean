-- Prove2me | Definitions.Def_HighDimStat_Pca_HasEigengap
-- name    : HighDimStat_Pca_HasEigengap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:13.945182+00:00
-- url     : https://prove2.me/theorems/0ffc7d52-7bbe-4414-b712-c02fecfbe9da
-- title:
--   M has eigengap nu at its maximal eigenvector theta-star
-- statement:
--   This predicate says $M$ has **eigengap** $\nu>0$ at its maximal unit eigenvector
--   $\theta^*$: every unit vector orthogonal to $\theta^*$ has Rayleigh quotient at most
--   $\gamma_1(M)-\nu$ — the Courant-Fischer variational form of Wainwright's $\nu :=
--   \gamma_1(\Sigma) - \gamma_2(\Sigma) > 0$.
--
--   For $M \in \mathbb R^{d\times d}$, $\theta^* \in \mathbb R^d$, $\nu \in \mathbb R$,
--
--   $$
--   M \text{ has eigengap } \nu \text{ at } \theta^* \;:\Longleftrightarrow\; \nu>0 \ \wedge\
--   \forall v,\ \|v\|_2=1 \wedge \langle v,\theta^*\rangle=0 \Rightarrow \langle v, Mv\rangle
--   \le \langle \theta^*, M\theta^*\rangle - \nu.
--   $$
--
--   **Formalization Note** This is mathematically equivalent (by the Courant-Fischer min-max
--   theorem) to the book's $\gamma_1(\Sigma)-\gamma_2(\Sigma)>0$ when $\theta^*$ is the true
--   top eigenvector of a symmetric matrix, since $\gamma_2(M)$ is exactly the maximum Rayleigh
--   quotient over the orthogonal complement of the top eigenspace; stated variationally here
--   (rather than via Mathlib's enumerated matrix-eigenvalue API) so it composes directly with
--   `IsMaximalUnitEigenvector`'s own variational definition, with no separate spectral-theorem
--   dependency.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 242 (PDF p. 262), Section 8.2.1

import Mathlib

namespace HighDimStat.Pca

/-- `M` has eigengap `ν > 0` at its maximal eigenvector `θ*`: every unit vector orthogonal to
`θ*` has Rayleigh quotient at most `γ₁(M) − ν`, the variational (Courant–Fischer) form of
Wainwright's `ν := γ₁(Σ) − γ₂(Σ) > 0`, Section 8.2.1, p. 242, used in Theorem 8.5 and
Lemma 8.6. -/
def HasEigengap {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (θstar : Fin d → ℝ) (ν : ℝ) : Prop :=
  0 < ν ∧
  ∀ v : Fin d → ℝ, (∑ j, (v j) ^ 2 = 1) → (∑ j, v j * θstar j = 0) →
    ∑ i, v i * (M.mulVec v) i ≤ (∑ i, θstar i * (M.mulVec θstar) i) - ν

end HighDimStat.Pca


