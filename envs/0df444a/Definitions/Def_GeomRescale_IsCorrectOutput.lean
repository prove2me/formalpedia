-- Prove2me | Definitions.Def_GeomRescale_IsCorrectOutput
-- name    : GeomRescale_IsCorrectOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:49.702022+00:00
-- url     : https://prove2.me/theorems/0a2318a8-6985-4542-99c7-a692147440b4
-- title:
--   The Output list of Algorithm 1
-- statement:
--   A state of Algorithm 1 run with input $\mu$ is a correct output if $\mu' \ge \mu$, $f(W') = -\mu'$, the vectors $g_i$ lie in $B(f_{\mu'})$, and
--
--   $$y = \sum_i x_i \frac{g_i}{\|g_i\|_Q}, \qquad \vec{e}^{\,\mathsf T} x = 1, \qquad x \ge 0, \qquad \|y\|_Q \le \varepsilon.$$
--
--   **Formalization Note** The list holds $g_1, \dots, g_{k-1}$, since line 15 has incremented $k$ when the page returns "$g_1, \dots, g_k$".
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, Output, p.8

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_unitQ
import Definitions.Def_GeomRescale_VN

namespace GeomRescale

/-- The Output list of Algorithm 1 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, p.8), for the input `μ`: `μ′ ≥ μ`,
`f(W′) = −μ′`, the bases `g_i` lie in `B(f_μ′)`, `x ≥ 0`, `eᵀx = 1`, `y = ∑ x_i g_i/‖g_i‖_Q` and
`‖y‖_Q ≤ ε`.

**Formalization Note.** `v.data` holds exactly the `g_i, x_i` of the output. The page's `return`
lists `g₁, …, g_k` after line 15 incremented `k`, so it means `g₁, …, g_{k−1}`. Here `g/‖g‖_Q` is
`unitQ Q g`, which is `0` at `g = 0`. -/
def IsCorrectOutput {n : ℕ} (f : Finset (Fin n) → ℤ) (Q : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (μ : ℤ) (v : VN n) : Prop :=
  μ ≤ v.μ ∧ f v.W = -v.μ ∧
    (∀ p ∈ v.data, p.1 ∈ SchrijverSFM.Alg.baseB (enlarge (fR f) (v.μ : ℝ))) ∧
    (∀ p ∈ v.data, 0 ≤ p.2) ∧
    (v.data.map Prod.snd).sum = 1 ∧
    v.y = (v.data.map (fun p => p.2 • unitQ Q p.1)).sum ∧
    qnorm Q v.y ≤ ε

end GeomRescale


