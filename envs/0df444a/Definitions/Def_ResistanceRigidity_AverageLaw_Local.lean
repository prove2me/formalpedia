-- Prove2me | Definitions.Def_ResistanceRigidity_AverageLaw_Local
-- name    : ResistanceRigidity_AverageLaw_Local
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:05:42.602139+00:00
-- url     : https://prove2.me/theorems/88621645-c668-47d0-986c-478876108d80
-- title:
--   The local quantities $p_v = w_{uv}/\delta_u$, $a_u$ and $t_u$ at a vertex (§2)
-- statement:
--   Let $c$ be the conductance function of a weighted graph on a finite vertex set $V$, with effective resistances $R_{uv}$ (the published `IncrementalER.reff`) and weighted degrees $\delta_u = \sum_x c(u,x)$ (the published `IncrementalER.capDeg`). Fix a vertex $u$ with $\delta_u > 0$. Following §2 of the paper,
--
--   - $p_v = c(u,v)/\delta_u$ (`nbrProb`), a probability vector on the neighbours of $u$ that depends on $u$;
--   - $a_u = \sum_v p_v R_{uv}$ (`avgRes`), the average resistance from $u$ to a random neighbour;
--   - $t_u = \sum_{v,x} p_v p_x R_{vx}$ (`pairRes`), the average resistance between two independent random neighbours of $u$; the sum runs over all ordered pairs $(v,x)$, the diagonal included, where $R_{vv} = 0$.
--
--   The paper's $c_u = \sum_v w_{uv} R_{uv}$ is the published `IncrementalER.levDeg`. These quantities enter the local identity $1/\delta_u = a_u - t_u/2$ (eq. (4)).
--
--   **Formalization Note.** $p_v$ is a division by $\delta_u$; for an isolated vertex ($\delta_u = 0$) Lean's convention $x/0 = 0$ gives $p \equiv 0$. Every statement that uses these quantities assumes a connected graph with at least two vertices, so $\delta_u > 0$.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 6, §2

import Mathlib
import Definitions.Def_IncrementalER_lap

namespace ResistanceRigidity.AverageLaw

/-!
# The local quantities p_v, a_u and t_u at a vertex u

Tianlang Chen, *A Sharp Rigidity Law for Effective Resistance*, STOC 2027 submission
(manuscript, sha256 3846da8c…1e8b), §2, p. 6.

For a vertex `u` with weighted degree `δ_u = IncrementalER.capDeg c u > 0`, `p_v = w_uv/δ_u` is a
probability vector on the neighbours of `u`; `a_u = ∑_v p_v R_uv` and
`t_u = ∑_{v,x} p_v p_x R_vx` (all ordered pairs, diagonal included, where `R_vv = 0`).
The paper's `c_u = ∑_v w_uv R_uv` is the published `IncrementalER.levDeg c u`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `p_v = w_uv / δ_u`, the transition probability from `u` to `v`. -/
noncomputable def nbrProb (c : V → V → ℝ) (u v : V) : ℝ :=
  c u v / IncrementalER.capDeg c u

/-- `a_u = ∑_v p_v R_uv`. -/
noncomputable def avgRes (c : V → V → ℝ) (u : V) : ℝ :=
  ∑ v, nbrProb c u v * IncrementalER.reff c u v

/-- `t_u = ∑_{v,x} p_v p_x R_vx`. -/
noncomputable def pairRes (c : V → V → ℝ) (u : V) : ℝ :=
  ∑ v, ∑ x, nbrProb c u v * nbrProb c u x * IncrementalER.reff c v x

end ResistanceRigidity.AverageLaw


