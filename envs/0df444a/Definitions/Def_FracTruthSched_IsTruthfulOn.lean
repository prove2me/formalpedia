-- Prove2me | Definitions.Def_FracTruthSched_IsTruthfulOn
-- name    : FracTruthSched_IsTruthfulOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:32.646694+00:00
-- url     : https://prove2.me/theorems/78c26342-5229-4f17-8ab6-6369c9eafe17
-- title:
--   Truthful fractional mechanism (inequality (1))
-- statement:
--   A mechanism $(x,P)$ is **truthful** on a domain $\mathcal D$ if no machine gains by misreporting: for every machine $i$, true type $t_i$, report $b_i$ and opposing reports $t_{-i}$ (with $(t_i,t_{-i})$ and $(b_i,t_{-i})$ in $\mathcal D$),
--   $$P_i(t_i,t_{-i})-t_i\cdot x_i(t_i,t_{-i})\;\ge\;P_i(b_i,t_{-i})-t_i\cdot x_i(b_i,t_{-i}).\tag{1}$$
--   The processing cost is always charged at the true type $t_i$.
--
--   **Formalization Note.** $(b_i,t_{-i})$ is the input with machine $i$'s whole row replaced by $b$ (`Function.update t i b`). For the nonnegative domain, true types, reports and opposing reports are all nonnegative.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2.1, eq. (1), p.3

import Mathlib
import Definitions.Def_FracTruthSched_FracMech

set_option autoImplicit false

namespace FracTruthSched

/-- **Truthfulness** (1) of a fractional mechanism on a domain `D` (Anastasiadis et al.,
arXiv:2611.06642v1, §2.1, eq. (1), p.3): for every agent `i`, true type `t_i`, report `b_i` and
opposing reports `t_{-i}`,
`P_i(t_i, t_{-i}) − t_i · x_i(t_i, t_{-i}) ≥ P_i(b_i, t_{-i}) − t_i · x_i(b_i, t_{-i})`.

**Formalization Note.** The input `t` plays `(t_i, t_{-i})` and `Function.update t i b` plays
`(b_i, t_{-i})`: the report replaces machine `i`'s whole row, and the processing cost is charged at
the true row `t i`. True types, reports and opposing reports range over the domain `D` only:
`t ∈ D` and `Function.update t i b ∈ D` (for `D = Nonneg` this says `t ≥ 0` and `b ≥ 0`). -/
def IsTruthfulOn {n : ℕ} {τ : Type*} [Fintype τ] (D : (Fin n → τ → ℝ) → Prop)
    (M : FracMech n τ) : Prop :=
  ∀ t, D t → ∀ (i : Fin n) (b : τ → ℝ), D (Function.update t i b) →
    M.P (Function.update t i b) i - ∑ j, t i j * M.x (Function.update t i b) i j ≤
      M.P t i - ∑ j, t i j * M.x t i j

end FracTruthSched


