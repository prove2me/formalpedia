-- Prove2me | Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
-- name    : HighDimStat_Pca_IsMaximalUnitEigenvector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:12:50.209985+00:00
-- url     : https://prove2.me/theorems/2c127e97-9382-4df3-9258-810796bdf0ea
-- title:
--   theta is a maximal unit-norm eigenvector of M
-- statement:
--   This predicate says $\theta$ is a **maximal unit-norm eigenvector** of a symmetric matrix
--   $M$: it lies on the unit sphere and maximizes the Rayleigh quotient $\langle\theta,
--   M\theta\rangle$ over the whole sphere — the variational characterization of "the" top
--   eigenvector/eigenvalue pair used throughout Wainwright's Section 8.2.
--
--   For $M \in \mathbb R^{d\times d}$ and $\theta \in \mathbb R^d$,
--
--   $$
--   \theta \text{ is a maximal unit eigenvector of } M \;:\Longleftrightarrow\;
--   \|\theta\|_2=1 \ \wedge\ \forall v,\ \|v\|_2=1 \Rightarrow \langle v, Mv\rangle \le
--   \langle \theta, M\theta\rangle.
--   $$
--
--   Theorem 8.5 and Lemma 8.6 both instantiate this at $C = \mathcal S^{d-1}$ of Wainwright's
--   Eq. (8.14), the case the chapter's own proof of Theorem 8.5 uses.
--
--   **Formalization Note** This is the variational (not spectral-decomposition) definition of
--   a top eigenvector, matching Eq. (8.14) verbatim, and does not itself assert uniqueness —
--   both this mission's goal and milestone only ever use an *arbitrary* maximizer, matching
--   exactly what their own proofs invoke (see `description.md`'s Formalization scope for the
--   disclosed scope decision this implies for Theorem 8.5's own uniqueness clause).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 243 (PDF p. 263), Eq. (8.14)

import Mathlib

namespace HighDimStat.Pca

/-- `θ` is a maximal unit-norm eigenvector of `M`: `θ ∈ S^{d-1}` and `θ` maximizes the Rayleigh
quotient `⟨θ, Mθ⟩` over the whole unit sphere, the variational characterization of the maximal
eigenvector/eigenvalue pair used throughout Wainwright, *High-Dimensional Statistics* (2019),
Eq. (8.14) (`maxθ∈C ⟨θ, Σθ⟩`, specialized here to `C = S^{d-1}`, the case Theorem 8.5 and
Lemma 8.6 both use). The associated top eigenvalue `γ₁(M)` is `⟨θ, Mθ⟩` itself. -/
def IsMaximalUnitEigenvector {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (θ : Fin d → ℝ) : Prop :=
  (∑ j, (θ j) ^ 2 = 1) ∧
  ∀ v : Fin d → ℝ, (∑ j, (v j) ^ 2 = 1) → ∑ i, v i * (M.mulVec v) i ≤ ∑ i, θ i * (M.mulVec θ) i

end HighDimStat.Pca


