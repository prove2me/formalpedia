-- Prove2me | Definitions.Def_OnlineBudgetAlloc_deltaD
-- name    : OnlineBudgetAlloc_deltaD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:41.234701+00:00
-- url     : https://prove2.me/theorems/2cf88a4f-7d36-4552-9d4e-9f72d1f58012
-- title:
--   Change of potential $\Delta_t = p_t - (H/s_t)\,w_t$
-- statement:
--   Fix a deterministic online algorithm, a partition rule and a seed of $D_{N,d}$. For each item $t$, write $p_t$ for the revenue the algorithm collects on item $t$. Let $r$ be the remaining budget, just before item $t$, of the advertiser that receives item $t$, and let
--   $$
--   w_t = v(r) - v(r - p_t)
--   $$
--   be the resulting decrease of its capped budget. With $s_t$ the number of remaining advertisers just before item $t$ and $H = N/e$, display (3) gives the change of the potential $\varphi(t) = \mathrm{ALG}_t + H\cdot\bar v_t$ caused by assigning item $t$:
--   $$
--   \Delta_t = p_t - \frac{H}{s_t}\, w_t .
--   $$
--   The bounds on $\Delta_t$ (Lemmas 4–6) are the core of the proof.
--
--   **Formalization Note** The module defines $p_t$ (`payD`), $w_t$ (`wD`) and $\Delta_t$ (`deltaD`). If the item is left unassigned, $p_t = w_t = 0$.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4, eq. (3)

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_revenue
import Definitions.Def_OnlineBudgetAlloc_DetAlg
import Definitions.Def_OnlineBudgetAlloc_Seed
import Definitions.Def_OnlineBudgetAlloc_PartitionRule
import Definitions.Def_OnlineBudgetAlloc_inputD
import Definitions.Def_OnlineBudgetAlloc_vcap
import Definitions.Def_OnlineBudgetAlloc_Hscale

namespace OnlineBudgetAlloc

/-- `p_t`: the revenue the deterministic online algorithm `A` collects for item `t` on the input
of `D_{N,d}` with seed `s` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4). -/
noncomputable def payD {N d : ℕ} (part : PartitionRule N d) (A : DetAlg N) (s : Seed N d)
    (t : Fin (numItems N d)) : ℝ :=
  payment (inputD part s) (A.assign (inputD part s)) t

/-- `w_t := v(r) − v(r − p_t)`: the decrease of the capped budget of the advertiser that item `t`
is assigned to, whose remaining budget before the assignment is `r` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4).

**Formalization Note** If the item is left unassigned (`none`), `w_t = 0` (and `p_t = 0`). -/
noncomputable def wD {N d : ℕ} (part : PartitionRule N d) (A : DetAlg N) (s : Seed N d)
    (t : Fin (numItems N d)) : ℝ :=
  match A.assign (inputD part s) t with
  | none => 0
  | some j =>
    vcap (remaining (inputD part s) (A.assign (inputD part s)) t.val j) -
      vcap (remaining (inputD part s) (A.assign (inputD part s)) t.val j - payD part A s t)

/-- `∆_t = p_t − (H/s_t)·w_t` of display (3): the change of the potential
`φ(t) = ALG_t + H·v̄_t` caused by the assignment of item `t` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4, eq. (3)), with
`H = N/e` and `s_t` the number of remaining advertisers just before item `t`.

**Formalization Note** `s_t = numAlive part s t` is a natural number cast to `ℝ`; it is positive
for every item of `D_{N,d}`. -/
noncomputable def deltaD {N d : ℕ} (part : PartitionRule N d) (A : DetAlg N) (s : Seed N d)
    (t : Fin (numItems N d)) : ℝ :=
  payD part A s t - Hscale N / (numAlive part s t : ℝ) * wD part A s t

end OnlineBudgetAlloc


