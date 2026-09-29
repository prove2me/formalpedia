-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_RestrictedEigenvalue
-- name    : HighDimStat_SparseLinear_RestrictedEigenvalue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:07.002603+00:00
-- url     : https://prove2.me/theorems/01884a0f-3b46-469f-be06-8f812059461a
-- title:
--   The restricted eigenvalue (RE) condition (Definition 7.12)
-- statement:
--   **Definition 7.12.** The matrix $X$ satisfies the **restricted eigenvalue (RE) condition**
--   over $S$ with parameters $(\kappa, \alpha)$ if the sample second moment of $X\Delta$ is
--   bounded below by $\kappa\|\Delta\|_2^2$ uniformly over the cone $C_\alpha(S)$.
--
--   For $X \in \mathbb R^{n\times d}$, $S \subseteq \{1,\dots,d\}$, and $\kappa,\alpha \in
--   \mathbb R$,
--
--   $$
--   \mathrm{RE}(X, S, \kappa, \alpha) \;:\Longleftrightarrow\; \frac{1}{n}\|X\Delta\|_2^2 \;\ge\;
--   \kappa\|\Delta\|_2^2 \quad \text{for all } \Delta \in C_\alpha(S).
--   $$
--
--   This is assumption (A2) of Theorem 7.13, a strengthening of the restricted nullspace
--   property (which is recovered, per the book's remark on p. 208, at parameters $(\kappa,1)$
--   for any $\kappa>0$).
--
--   **Formalization Note** `κ` and `α` are left as arbitrary reals (no positivity constraint
--   built into the definition itself, matching the book's own Definition 7.12, which states
--   the condition schematically before Theorem 7.13 adds `κ > 0`, `α = 3` as hypotheses).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 208 (PDF p. 228), Definition 7.12, Eq. (7.22)

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_ConeSet

namespace HighDimStat.SparseLinear

/-- **Definition 7.12.** The matrix `X` satisfies the restricted eigenvalue (RE) condition over
`S` with parameters `(κ, α)` if `(1/n)‖XΔ‖₂² ≥ κ‖Δ‖₂²` for all `Δ ∈ C_α(S)`, Wainwright,
*High-Dimensional Statistics* (2019), Eq. (7.22), p. 208. -/
def RestrictedEigenvalue {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (κ α : ℝ) : Prop :=
  ∀ Δ : Fin d → ℝ, ConeSet S α Δ →
    κ * (∑ j, (Δ j) ^ 2) ≤ (∑ i, (X.mulVec Δ i) ^ 2) / (n : ℝ)

end HighDimStat.SparseLinear


