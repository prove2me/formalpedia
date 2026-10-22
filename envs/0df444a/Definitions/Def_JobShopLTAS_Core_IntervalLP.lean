-- Prove2me | Definitions.Def_JobShopLTAS_Core_IntervalLP
-- name    : JobShopLTAS_Core_IntervalLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T07:16:13.392842+00:00
-- url     : https://prove2.me/theorems/6b20fa12-23e4-4dff-bb1d-26ddeb5c4530
-- title:
--   Intervals of the second type and the linear program (3)–(5) for the tiny operations
-- statement:
--   Let $\sigma$ give start times $S_{ij}$ to the big operations, with completion times $C_{ij}=S_{ij}+p_{ij}$. Let $A$ be the **set** of all these start and completion times, with elements $a_1<a_2<\dots<a_{|A|}$, and put $a_0=0$, $a_{|A|+1}=C$. The **intervals of the second type** are $[a_k,a_{k+1})$, $k=0,\dots,|A|$, of length $\Delta_k=a_{k+1}-a_k$. For machine $M_t$ let $\Delta_{tk}=0$ if some big operation on $M_t$ is processed in interval $k$ (its execution interval $[S_{ij},C_{ij})$ meets $[a_k,a_{k+1})$ in a set of positive length), and $\Delta_{tk}=\Delta_k$ otherwise.
--
--   For a tiny job $J_j$ let $K_j=\{(k_1,\dots,k_{\mu_j})\in\mathbb Z^{\mu_j}\mid 0\le k_1\le\dots\le k_{\mu_j}\le |A|\}$. The **linear program (3)–(5)** in the variables $x_{jK}$ ($J_j\in T$, $K\in K_j$) is
--   $$\sum_{K\in K_j}x_{jK}=1\ \ (J_j\in T),\qquad \sum_{J_j\in T}\sum_{K\in K_j}\ \sum_{i:\,k_i=k,\ \pi_{ij}=t}p_{ij}\,x_{jK}\le\Delta_{tk}\ \ (t=1,\dots,m,\ k=0,\dots,|A|),\qquad x_{jK}\ge 0.$$
--   The program is considered for $C\in[a_{|A|},(1+\mu m\varepsilon)mP_{\max}]$, and "the LP is feasible" includes this range condition.
--
--   A **feasible restricted schedule for the big operations** is a feasible schedule of the big jobs in which every big operation starts at the beginning of an interval of the first type.
--
--   **Formalization Note.** $a_1<\dots<a_{|A|}$ is `Finset.orderEmbOfFin` of the finite set $A$ (duplicates collapse, as in the paper's set). Tuples $K\in K_j$ are monotone maps `Fin (μ j) → Fin (|A|+1)`; the variable vector $x$ is a real function on all maps, and constraints (3)–(5) only involve its values on monotone ones. Interval indices are 0-based as in the paper ($k=0,\dots,|A|$); machines and operations are 0-based.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 292, Section 2.2, Eqs. (3)-(5)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem

namespace JobShopLTAS.Core

/-- The points `a_0 ≤ a_1 ≤ ⋯ ≤ a_{|A|+1}` of §2.2 (p. 292): `a_0 = 0`, `a_1 < ⋯ < a_{|A|}`
are the elements of the finite set `A` in increasing order (via `Finset.orderEmbOfFin`), and
`a_{|A|+1} = C`. Indices `k > |A| + 1` also return `C` but are never used. -/
noncomputable def breakpoint (A : Finset ℝ) (C : ℝ) (k : ℕ) : ℝ :=
  if hk : k = 0 then 0
  else if h : k ≤ A.card then A.orderEmbOfFin rfl ⟨k - 1, by omega⟩
  else C

/-- The length `Δ_k = a_{k+1} - a_k` of the interval of the second type `[a_k, a_{k+1})`. -/
noncomputable def intervalLength (A : Finset ℝ) (C : ℝ) (k : ℕ) : ℝ :=
  breakpoint A C (k + 1) - breakpoint A C k

namespace Instance

variable {m n : ℕ} (inst : Instance m n)

/-- The set `A` of starting and completion times `S_{ij}`, `C_{ij} = S_{ij} + p_{ij}` of the
big operations under the start times `σ` (§2.2, p. 292). -/
noncomputable def bigTimes (α : ℝ) (σ : inst.Op → ℝ) : Finset ℝ :=
  (Finset.univ.filter (fun o : inst.Op => o.1 ∈ inst.bigJobs α)).image σ ∪
    (Finset.univ.filter (fun o : inst.Op => o.1 ∈ inst.bigJobs α)).image
      (fun o => σ o + inst.proc o)

/-- Operation `o`, run on `[σ o, σ o + p_o)`, is processed in the interval
`[a_k, a_{k+1})`: the two intervals overlap in a set of positive length. -/
def ProcessedIn (A : Finset ℝ) (C : ℝ) (σ : inst.Op → ℝ) (o : inst.Op) (k : ℕ) : Prop :=
  max (σ o) (breakpoint A C k) < min (σ o + inst.proc o) (breakpoint A C (k + 1))

open Classical in
/-- `Δ_{tk}` (§2.2, p. 292): `0` if some big operation is processed in interval `k` on
machine `t`, and `Δ_k` otherwise; here `A = bigTimes α σ` and `a_{|A|+1} = C`. -/
noncomputable def availableLength (α C : ℝ) (σ : inst.Op → ℝ) (t : Fin m) (k : ℕ) : ℝ :=
  if ∃ o : inst.Op, o.1 ∈ inst.bigJobs α ∧ inst.mach o = t ∧
      inst.ProcessedIn (inst.bigTimes α σ) C σ o k then 0
  else intervalLength (inst.bigTimes α σ) C k

open Classical in
/-- `K_j` (§2.2, p. 292): the tuples `(k_1, …, k_{µ_j})` with
`0 ≤ k_1 ≤ ⋯ ≤ k_{µ_j} ≤ |A|`, as monotone maps `Fin (µ_j) → Fin (|A| + 1)`. -/
noncomputable def monotoneTuples (A : Finset ℝ) (j : Fin n) :
    Finset (Fin (inst.μ j) → Fin (A.card + 1)) :=
  Finset.univ.filter (fun K => Monotone K)

/-- `σ` is a feasible restricted schedule for the big operations: a feasible schedule of the
big jobs `B` in which every big operation starts at the beginning of an interval of the
first type (§2.2, p. 292, "Fix some feasible restricted schedule for the big
operations"). -/
def IsBigSchedule (ε α : ℝ) (σ : inst.Op → ℝ) : Prop :=
  inst.IsFeasibleSchedule (inst.bigJobs α) σ ∧ inst.IsRestricted ε α σ

open Classical in
/-- The linear program (3)–(5) of §2.2 (p. 292) for the big-operation schedule `σ` and the
length `C` has a feasible solution. `A = bigTimes α σ`, `T = tinyJobs ε α`. The program is
defined for `C ∈ [a_{|A|}, (1 + µmε) m P_max]`, and that range is part of the predicate.
Variables `x j K` for `J_j ∈ T`, `K ∈ K_j`; constraints
(3) `∑_{K ∈ K_j} x_{jK} = 1` for `J_j ∈ T`;
(4) `∑_{J_j ∈ T} ∑_{K ∈ K_j} ∑_{i : k_i = k, π_{ij} = t} p_{ij} x_{jK} ≤ Δ_{tk}` for every
machine `t` and `k = 0, …, |A|`;
(5) `x_{jK} ≥ 0`. -/
def LPFeasible (ε α : ℝ) (σ : inst.Op → ℝ) (C : ℝ) : Prop :=
  breakpoint (inst.bigTimes α σ) C (inst.bigTimes α σ).card ≤ C ∧
  C ≤ inst.horizon ε ∧
  ∃ x : (j : Fin n) → (Fin (inst.μ j) → Fin ((inst.bigTimes α σ).card + 1)) → ℝ,
    (∀ j ∈ inst.tinyJobs ε α,
      ∑ K ∈ inst.monotoneTuples (inst.bigTimes α σ) j, x j K = 1) ∧
    (∀ t : Fin m, ∀ k : Fin ((inst.bigTimes α σ).card + 1),
      ∑ j ∈ inst.tinyJobs ε α, ∑ K ∈ inst.monotoneTuples (inst.bigTimes α σ) j,
        ∑ i ∈ Finset.univ.filter (fun i => K i = k ∧ inst.π j i = t), inst.p j i * x j K
        ≤ inst.availableLength α C σ t k) ∧
    (∀ j ∈ inst.tinyJobs ε α, ∀ K ∈ inst.monotoneTuples (inst.bigTimes α σ) j, 0 ≤ x j K)

end Instance

end JobShopLTAS.Core


