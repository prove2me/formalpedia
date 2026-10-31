-- Prove2me | Definitions.Def_GuoZhaoADRC_scaledErr
-- name    : GuoZhaoADRC_scaledErr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:28.688672+00:00
-- url     : https://prove2.me/theorems/b263d010-df20-4563-bfe9-fea6d1c5d789
-- title:
--   Scaled observer errors $e^i_j=(x^i_j-\hat x^i_j)/\varepsilon^{n_i+1-j}$ (1.6)
-- statement:
--   The scaled observer errors are
--
--   $$e^i_j(t)=\frac{x^i_j(t)-\hat x^i_j(t)}{\varepsilon^{n_i+1-j}},\qquad 1\le j\le n_i+1,\ 1\le i\le m,$$
--
--   with $e^i=(e^i_1,\dots,e^i_{n_i+1})\in\mathbb R^{n_i+1}$. For $j=n_i+1$ the numerator uses the extended state and there is no power of $\varepsilon$. In these coordinates the observer error dynamics become the $\varepsilon$-independent system of A2, accelerated by the factor $1/\varepsilon$.
--
--   **Formalization Note** 0-based index $j$: the exponent $n_i+1-j$ of the page is `n i - j.val`. The value is a vector of `EuclideanSpace ℝ (Fin (n i + 1))`, so $\|e^i\|$ is Euclidean.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (1.6), p.1730

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_fullState

namespace GuoZhaoADRC

/-- **The scaled observer errors `e^i_j = (x^i_j − x̂^i_j)/ε^{n_i+1−j}`, `1 ≤ j ≤ n_i + 1`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (1.6), p.1730.

`e^i = (e^i_1, …, e^i_{n_i+1}) ∈ ℝ^{n_i+1}`, where `x^i_{n_i+1}` is the extended state, so
`e^i_{n_i+1} = x^i_{n_i+1} − x̂^i_{n_i+1}` carries no power of `ε`.

**Formalization Note.** 0-based `j`: the exponent `n_i + 1 − j` of the page is
`n i - j.val`. The value is a vector of `EuclideanSpace ℝ (Fin (n i + 1))`, so `‖e^i‖` is
Euclidean. -/
noncomputable def scaledErr {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) (ε : ℝ)
    (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) (t : ℝ) (i : Fin m) :
    EuclideanSpace ℝ (Fin (n i + 1)) :=
  WithLp.toLp 2 (fun j : Fin (n i + 1) =>
    (fullState D x ξ xhat i t j - xhat t i j) / ε ^ (n i - j.val))

end GuoZhaoADRC


