-- Prove2me | Definitions.Def_GuoZhaoADRC_uStar
-- name    : GuoZhaoADRC_uStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:44.757505+00:00
-- url     : https://prove2.me/theorems/77222d23-fb64-4fa2-b24f-8f0309285fb0
-- title:
--   The virtual control $u^*_i=\varphi_i(\tilde x^i-z^i)+z^i_{n_i+1}-\hat x^i_{n_i+1}$ of ADRC(G) (3.2)
-- statement:
--   For an observer trajectory $\hat x^i=(\hat x^i_1,\dots,\hat x^i_{n_i+1})$ and the reference $z^i$, write $\tilde x^i=(\hat x^i_1,\dots,\hat x^i_{n_i})$. The virtual control of subsystem $i$ at time $t$ is
--
--   $$u^*_i(t)=\varphi_i\bigl(\tilde x^i(t)-z^i(t)\bigr)+z^i_{n_i+1}(t)-\hat x^i_{n_i+1}(t),$$
--
--   where $\tilde x^i-z^i=(\hat x^i_j-z^i_j)_{1\le j\le n_i}$. The term $-\hat x^i_{n_i+1}$ cancels the estimated total disturbance, and $\varphi_i(\tilde x^i-z^i)+z^i_{n_i+1}$ makes the output track the reference.
--
--   **Formalization Note** 0-based indices: `j.castSucc` is the page's $j\le n_i$ and `Fin.last (n i)` the page's $n_i+1$.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.2), p.1737; notation x̃^i of (1.6), p.1730

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData

namespace GuoZhaoADRC

/-- **The virtual control `u*_i = φ_i(x̃^i − z^i) + z^i_{n_i+1} − x̂^i_{n_i+1}` of ADRC(G) (3.2).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.2), p.1737; notation `x̃^i` of (1.6), p.1730.

Here `x̂^i = (x̂^i_1, …, x̂^i_{n_i+1})` is the ESO state, `x̃^i = (x̂^i_1, …, x̂^i_{n_i})` and
`x̃^i − z^i = (x̂^i_j − z^i_j)_{1 ≤ j ≤ n_i}`.

**Formalization Note.** 0-based indices: `j.castSucc` is the page's `j + 1 ≤ n_i`,
`Fin.last (n i)` the page's `n_i + 1`. -/
noncomputable def uStar {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  D.φ i (WithLp.toLp 2 (fun j : Fin (n i) => xhat t i j.castSucc - D.z t i j.castSucc))
    + D.z t i (Fin.last (n i)) - xhat t i (Fin.last (n i))

end GuoZhaoADRC


