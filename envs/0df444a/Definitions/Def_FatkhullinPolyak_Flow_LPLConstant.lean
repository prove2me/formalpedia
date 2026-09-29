-- Prove2me | Definitions.Def_FatkhullinPolyak_Flow_LPLConstant
-- name    : FatkhullinPolyak_Flow_LPLConstant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:44:09.027705+00:00
-- url     : https://prove2.me/theorems/8a5cd4e5-6f10-4948-baa9-33ff0343f8b6
-- title:
--   Extreme eigenvalues, spectral norm, and the LPL constant $\mu$ of (3.11)
-- statement:
--   The constants of the gradient-domination (Łojasiewicz–Polyak) inequality of Fatkhullin and Polyak for state feedback ($C=I$).
--
--   1. For a real symmetric matrix $M$, $\lambda_1(M)$ and $\lambda_n(M)$ denote its smallest and largest eigenvalue (the paper indexes eigenvalues in increasing order, p. 2).
--   2. $\|M\|=\sqrt{\lambda_{\max}(M^\top M)}$ is the spectral norm (p. 2).
--   3. For $C=I$ (so $r=n$), write $f_S$ for the LQR cost $f$. For gains $K_0$ and $K_*$, the constant of (3.11) is
--   $$\mu = \frac{\lambda_1(R)\,\lambda_1^2(\Sigma)\,\lambda_1(Q)}{8 f_S(K_*)\Big(\|A\| + \dfrac{\|B\|^2 f_S(K_0)}{\lambda_1(\Sigma)\lambda_1(R)}\Big)^2}.$$
--
--   Theorem 3.17 shows that, with $K_*$ a minimizer of $f_S$ on $\mathcal S$, $\mu>0$ and $f_S$ satisfies the LPL inequality with this $\mu$ on $\mathcal S_0$; the exponential rate of the gradient flow in Theorem 4.1 is $\mu$.
--
--   **Formalization Note** $\lambda_1$, $\lambda_n$ are the minimum and maximum of Mathlib's (unsorted) eigenvalue family of a Hermitian matrix; for a non-symmetric argument they return the placeholder $0$, which never occurs here because they are applied only to $Q, R, \Sigma$ (positive definite by hypothesis) and to $M^\top M$ (always symmetric).
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 2, Notation; p. 10, Theorem 3.17, (3.11)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR

namespace FatkhullinPolyak.Flow

open Matrix

open Classical in
/-- `λ₁(M)`, the smallest eigenvalue of a real symmetric matrix (Mathlib's `eigenvalues` are
not sorted, so the minimum is taken over the index). Junk value `0` if `M` is not symmetric. -/
noncomputable def lamMin {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  if h : M.IsHermitian then ⨅ i, h.eigenvalues i else 0

open Classical in
/-- `λ_n(M)`, the largest eigenvalue of a real symmetric matrix. Junk value `0` if `M` is not
symmetric. -/
noncomputable def lamMax {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  if h : M.IsHermitian then ⨆ i, h.eigenvalues i else 0

/-- The spectral norm `‖M‖ = √(λ_max(Mᵀ M))` (p. 2 notation). -/
noncomputable def specNorm {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  Real.sqrt (lamMax (Mᵀ * M))

/-- The LPL constant `µ` of (3.11), for state feedback (`C = I`):
`µ = λ₁(R) λ₁(Σ)² λ₁(Q) / (8 f(K*) (‖A‖ + ‖B‖² f_S(K₀) / (λ₁(Σ) λ₁(R)))²)`. -/
noncomputable def muLPL {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (K₀ Kstar : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  lamMin R * lamMin Sig ^ 2 * lamMin Q /
    (8 * cost A B 1 Q R Sig Kstar *
      (specNorm A + specNorm B ^ 2 * cost A B 1 Q R Sig K₀ / (lamMin Sig * lamMin R)) ^ 2)

end FatkhullinPolyak.Flow


