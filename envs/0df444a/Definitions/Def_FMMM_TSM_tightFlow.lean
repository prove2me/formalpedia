-- Prove2me | Definitions.Def_FMMM_TSM_tightFlow
-- name    : FMMM_TSM_tightFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:54.222341+00:00
-- url     : https://prove2.me/theorems/94b59f97-e79e-4df3-9059-f564b8f1ca51
-- title:
--   The flow of the tight family: the $6$-cycles
-- statement:
--   The tight family is parameterized by $m \ge 1$ (with $n = 4m$). Its ads are $K \cup U \cup V \cup W$ with $K = \{k_1, \dots, k_m\}$, $U = \{u_1, \dots, u_m\}$, and similarly $V$, $W$; its impression types are $L \cup X \cup Y \cup Z$ with $L = \{l_1, \dots, l_m\}$, $X = \{x_1, \dots, x_m\}$, and similarly $Y$, $Z$.
--
--   The flow found by the algorithm puts unit flow exactly on the edges of the $m$ six-cycles
--
--   $$u_i - x_i - v_i - y_i - w_i - z_i - u_i \qquad (1 \le i \le m),$$
--
--   that is, on the $6m$ edges $(u_i, x_i), (v_i, x_i), (v_i, y_i), (w_i, y_i), (w_i, z_i), (u_i, z_i)$.
--
--   **Formalization Note** Ads and types are both indexed by $\mathrm{Fin}\,4 \times \mathrm{Fin}\,m$: an ad $(\tau, i)$ is $k_i, u_i, v_i, w_i$ for $\tau = 0, 1, 2, 3$, a type $(\tau, i)$ is $l_i, x_i, y_i, z_i$ for $\tau = 0, 1, 2, 3$; indices are $0$-based.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.5, p. 10 (max-flow found during the algorithm: the 6-cycles)

import Mathlib

namespace FMMM.TSM

/-- **The flow of the tight family: the 6-cycles.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.5, p. 10: "The only edges with (unit) flow are the edges of the 6-cycles,
i.e., for i ∈ [1, n/4], {u_i − x_i − v_i − y_i − w_i − z_i − u_i}."

Ads and impression types are both `Fin 4 × Fin m` (`m = n/4`). An ad `(τ, k)` is `k_k, u_k, v_k,
w_k` for `τ = 0, 1, 2, 3`; an impression type `(τ, k)` is `l_k, x_k, y_k, z_k` for
`τ = 0, 1, 2, 3`. `tightFlow m` is the set of the `6m` edges
`(u_k, x_k), (v_k, x_k), (v_k, y_k), (w_k, y_k), (w_k, z_k), (u_k, z_k)`, `k < m`.

**Formalization Note.** The paper's index range `[1, n/4]` is `Fin m`, 0-based. -/
def tightFlow (m : ℕ) : Finset ((Fin 4 × Fin m) × (Fin 4 × Fin m)) :=
  Finset.univ.filter (fun p => p.1.2 = p.2.2 ∧
    ((p.1.1 = 1 ∧ p.2.1 = 1) ∨ (p.1.1 = 2 ∧ p.2.1 = 1) ∨ (p.1.1 = 2 ∧ p.2.1 = 2) ∨
      (p.1.1 = 3 ∧ p.2.1 = 2) ∨ (p.1.1 = 3 ∧ p.2.1 = 3) ∨ (p.1.1 = 1 ∧ p.2.1 = 3)))

end FMMM.TSM


