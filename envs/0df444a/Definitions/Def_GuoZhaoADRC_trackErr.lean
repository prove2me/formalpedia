-- Prove2me | Definitions.Def_GuoZhaoADRC_trackErr
-- name    : GuoZhaoADRC_trackErr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:43.377373+00:00
-- url     : https://prove2.me/theorems/b17e565c-67d8-46be-b1bb-461e4bc06626
-- title:
--   Tracking errors $\eta^i=x^i-z^i$
-- statement:
--   The tracking error of subsystem $i$ is $\eta^i=x^i-z^i=(x^i_j-z^i_j)_{1\le j\le n_i}\in\mathbb R^{n_i}$, and $\eta=(\eta^1,\dots,\eta^m)$. Theorem 3.1 (3.5) bounds its components.
--
--   **Formalization Note** The value is a vector of `EuclideanSpace ℝ (Fin (n i))` (Euclidean norm); $z^i_j$ is `D.z t i j.castSucc`.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, notation after (1.6), p.1730

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData

namespace GuoZhaoADRC

/-- **The tracking errors `η^i = x^i − z^i = (x^i_j − z^i_j)_{1 ≤ j ≤ n_i}`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), notation after (1.6), p.1730.

**Formalization Note.** 0-based `j : Fin (n i)`; `z^i_j` is `D.z t i j.castSucc`. The value is
a vector of `EuclideanSpace ℝ (Fin (n i))` (Euclidean norm). -/
noncomputable def trackErr {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (t : ℝ) (i : Fin m) :
    EuclideanSpace ℝ (Fin (n i)) :=
  WithLp.toLp 2 (fun j : Fin (n i) => x t ⟨i, j⟩ - D.z t i j.castSucc)

end GuoZhaoADRC


