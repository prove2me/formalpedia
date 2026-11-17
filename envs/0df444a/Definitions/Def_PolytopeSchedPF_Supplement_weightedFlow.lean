-- Prove2me | Definitions.Def_PolytopeSchedPF_Supplement_weightedFlow
-- name    : PolytopeSchedPF_Supplement_weightedFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:19:02.800788+00:00
-- url     : https://prove2.me/theorems/7644ca67-e253-42ce-8035-6f5bdd63d457
-- title:
--   Weighted flow time $\sum_j w_j(C_j-r_j)$
-- statement:
--   For a schedule $y$ with processing requirements $p$ and release dates $r$, the **flow time** of job $j$ is $F_j:=C_j-r_j$, the time it spends in the system, where $C_j$ is its completion time. The **weighted flow time** is
--
--   $$\sum_{j\in J} w_jF_j=\sum_{j\in J}w_j\,(C_j-r_j).$$
--
--   A job with $p_j=0$ completes at its release date and contributes nothing.
--
--   This is the objective of the speed-augmented guarantees (Theorems 1.7, 6.3 and 6.6).
--
--   **Formalization Note** $C_j$ is the base mission's completion time. With speed $\kappa$, the paper's $\kappa$-speed feasible schedule for $(p_j)$ is a $1$-speed feasible schedule for $(p_j/\kappa)$ (p.13), so the flow time of PF with speed $\kappa$ is this quantity evaluated at $p/\kappa$.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §3.1, p.13 (PDF p.15), flow time F_j := C_j − r_j and the objective ∑_j w_j F_j

import Mathlib
import Definitions.Def_PolytopeSchedPF_Schedule

namespace PolytopeSchedPF

namespace Supplement

/-- **Weighted flow time** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §3.1, p.13): the flow
time of job `j` is `F_j := C_j − r_j`, and the objective is `∑_j w_j F_j`.

**Formalization Note** `completionTime` is the base mission's (reading R7). The objective of PF with
speed `κ` is `weightedFlow w (fun j => p j / κ) r y`: by p.13 an `s`-speed feasible schedule for
`(p_j)` is a `1`-speed feasible schedule for `(p_j / s)`, with the same completion times. A job with
`p_j = 0` has `C_j = r_j` and contributes `0`. -/
noncomputable def weightedFlow {n : ℕ} (w p r : Fin n → ℝ) (y : ℝ → Fin n → ℝ) : ℝ :=
  ∑ j, w j * (completionTime p r y j - r j)

end Supplement

end PolytopeSchedPF


