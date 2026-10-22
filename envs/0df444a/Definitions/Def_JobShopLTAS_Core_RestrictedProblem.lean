-- Prove2me | Definitions.Def_JobShopLTAS_Core_RestrictedProblem
-- name    : JobShopLTAS_Core_RestrictedProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T06:54:56.642728+00:00
-- url     : https://prove2.me/theorems/706061d5-293d-4aeb-9c11-925eaf407aa2
-- title:
--   Big, small and tiny jobs; intervals of the first type; restricted schedules and the restricted optimum $\widetilde C^*_{\max}$
-- statement:
--   Fix $\varepsilon>0$ and a real $\alpha$. With $P_{\max}$ and the job lengths $l_j$ of the instance, the jobs are split into
--   $$B=\{J_j\mid l_j\ge \alpha P_{\max}\},\quad S=\{J_j\mid \alpha\varepsilon P_{\max}<l_j<\alpha P_{\max}\},\quad T=\{J_j\mid l_j\le\alpha\varepsilon P_{\max}\},$$
--   the **big**, **small** and **tiny** jobs. Operations of big jobs are **big operations**.
--
--   The time interval from $0$ to the **horizon** $H=(1+\mu m\varepsilon)\,mP_{\max}$ is partitioned into $N=\lceil m(1+\mu m\varepsilon)/(\alpha\varepsilon)\rceil$ equal **intervals of the first type** $[rL,(r+1)L)$, $r=0,\dots,N-1$, of length $L=H/N$. A schedule is **restricted** if every big operation starts at the beginning $rL$ ($0\le r<N$) of an interval of the first type.
--
--   The small jobs are removed from the input. The **restricted optimum** $\widetilde C^*_{\max}$ is the infimum of the makespans of the feasible restricted schedules of the jobs $B\cup T$.
--
--   **Formalization Note.** $\mu$ is `maxOps` $=\max_j\mu_j$; $P_{\max}$, $\alpha$ and $\varepsilon$ are those of the full instance. $\widetilde C^*_{\max}$ is `sInf` of a set of reals; that the set is nonempty (restricted schedules exist) is part of the milestone `restrictedOpt_le`, and that the infimum is attained is left to the solver of the goal.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), pp. 290-291, Section 2.1

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

namespace JobShopLTAS.Core

namespace Instance

variable {m n : ℕ} (inst : Instance m n)

/-- Big jobs `B = {J_j | l_j ≥ α P_max}` (§2.1, p. 291). -/
noncomputable def bigJobs (α : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => α * inst.Pmax ≤ inst.jobLength j)

/-- Small jobs `S = {J_j | α ε P_max < l_j < α P_max}` (§2.1, p. 291). -/
noncomputable def smallJobs (ε α : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => α * ε * inst.Pmax < inst.jobLength j ∧
    inst.jobLength j < α * inst.Pmax)

/-- Tiny jobs `T = {J_j | l_j ≤ α ε P_max}` (§2.1, p. 291). -/
noncomputable def tinyJobs (ε α : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => inst.jobLength j ≤ α * ε * inst.Pmax)

/-- The horizon `(1 + µ m ε) m P_max` partitioned by the intervals of the first type
(§2.1, p. 291), with `µ = inst.maxOps`. -/
noncomputable def horizon (ε : ℝ) : ℝ :=
  (1 + (inst.maxOps : ℝ) * m * ε) * m * inst.Pmax

/-- The number `⌈m(1 + µmε)/(αε)⌉` of intervals of the first type (§2.1, p. 291). -/
noncomputable def numIntervals (ε α : ℝ) : ℕ :=
  ⌈(m : ℝ) * (1 + (inst.maxOps : ℝ) * m * ε) / (α * ε)⌉₊

/-- The common length of the intervals of the first type: the horizon divided by their
number. -/
noncomputable def gridLength (ε α : ℝ) : ℝ :=
  inst.horizon ε / inst.numIntervals ε α

/-- `s` is restricted: every big operation starts at the beginning `r · L` of one of the
`N = ⌈m(1+µmε)/(αε)⌉` intervals of the first type `[r L, (r+1) L)`, `r = 0, …, N - 1`
(§2.1, p. 291). -/
def IsRestricted (ε α : ℝ) (s : inst.Op → ℝ) : Prop :=
  ∀ o : inst.Op, o.1 ∈ inst.bigJobs α →
    ∃ r : ℕ, r < inst.numIntervals ε α ∧ s o = r * inst.gridLength ε α

/-- `C̃*_max`: the optimum makespan of the restricted problem, i.e. the infimum of the
makespans of the feasible schedules of the jobs `B ∪ T` (the small jobs removed, §2.1,
p. 291) in which every big operation starts at the beginning of an interval of the first
type. `P_max`, `α`, `ε` are those of the full instance. -/
noncomputable def restrictedOpt (ε α : ℝ) : ℝ :=
  sInf (inst.makespan (inst.bigJobs α ∪ inst.tinyJobs ε α) ''
    {s | inst.IsFeasibleSchedule (inst.bigJobs α ∪ inst.tinyJobs ε α) s ∧
      inst.IsRestricted ε α s})

end Instance

end JobShopLTAS.Core


