-- Prove2me | Definitions.Def_WainwrightHDS_EigPert_gamma
-- name    : WainwrightHDS_EigPert_gamma
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:25:13.338981+00:00
-- url     : https://prove2.me/theorems/ced07283-9e93-442b-b72d-57469aab59e3
-- title:
--   Eigenvalues of a symmetric matrix in non-increasing order, $\gamma_1(Q) \ge \dots \ge \gamma_d(Q)$
-- statement:
--   Let $Q$ be a real symmetric $d \times d$ matrix. Its eigenvalues, counted with multiplicity and listed in non-increasing order, are
--
--   $$
--   \gamma_{\max}(Q) = \gamma_1(Q) \ge \gamma_2(Q) \ge \cdots \ge \gamma_d(Q) = \gamma_{\min}(Q).
--   $$
--
--   The vector $\gamma(Q) \in \mathbb{R}^d$ is the book's standard notation for the spectrum of a symmetric matrix; the eigengap $\nu = \gamma_1(\Sigma) - \gamma_2(\Sigma)$ of Chapter 8 and the eigenvalue perturbation bounds are stated in terms of it.
--
--   **Formalization Note** Indices are 0-based: `gamma Q hQ 0` is $\gamma_1(Q)$, `gamma Q hQ 1` is $\gamma_2(Q)$, and so on. The value is Mathlib's sorted eigenvalue list `Matrix.IsHermitian.eigenvalues₀` (non-increasing by `eigenvalues₀_antitone`), re-indexed along $|\mathrm{Fin}\,d| = d$; it is not the unsorted `Matrix.IsHermitian.eigenvalues`. For real matrices, `IsHermitian` means $Q^\top = Q$.
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, Section 6.1, p. 160 (PDF p. 180), notation for the ordered eigenvalues

import Mathlib

namespace WainwrightHDS.EigPert

/-- **The eigenvalues of a symmetric matrix in non-increasing order**, `γ₁(Q) ≥ γ₂(Q) ≥ ⋯ ≥ γ_d(Q)`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, Section 6.1, p. 160 (PDF p. 180): "we use `γ(Q) ∈ ℝ^d` to denote its vector of
eigenvalues, ordered as `γ_max(Q) = γ₁(Q) ≥ γ₂(Q) ≥ ⋯ ≥ γ_d(Q) = γ_min(Q)`".

`gamma Q hQ j` is the `(j+1)`-st largest eigenvalue of the symmetric matrix `Q`, counted with
multiplicity.

**Formalization Note.** The index is **0-based**: `gamma Q hQ 0 = γ₁(Q) = γ_max(Q)`,
`gamma Q hQ 1 = γ₂(Q)`, …. The value is Mathlib's `Matrix.IsHermitian.eigenvalues₀`, which is
sorted in non-increasing order (`Matrix.IsHermitian.eigenvalues₀_antitone`), re-indexed along
`Fintype.card (Fin d) = d`. It is *not* `Matrix.IsHermitian.eigenvalues`, which is indexed by the
matrix's index type and is not sorted. For real matrices `Q.IsHermitian` means `Qᵀ = Q`. -/
noncomputable def gamma {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsHermitian)
    (j : Fin d) : ℝ :=
  hQ.eigenvalues₀ (Fin.cast (Fintype.card_fin d).symm j)

end WainwrightHDS.EigPert


