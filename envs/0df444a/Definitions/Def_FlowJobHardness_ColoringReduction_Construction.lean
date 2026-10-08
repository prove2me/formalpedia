-- Prove2me | Definitions.Def_FlowJobHardness_ColoringReduction_Construction
-- name    : FlowJobHardness_ColoringReduction_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:51.046541+00:00
-- url     : https://prove2.me/theorems/80e65708-0008-4977-a2dc-a224953b2adf
-- title:
--   The generalized flow shop instance S(r, d) built from a properly coloured graph (Section 3.2.1)
-- statement:
--   Let $G=(V,E)$ be a simple graph on $n$ vertices, and let its vertices be partitioned into $d$ independent sets $I_1,\dots,I_d$, given by a proper colouring $c : V \to \{0,\dots,d-1\}$ with $I_f = \{v : c(v)+1 = f\}$. The **frequency** of a vertex $v$ is $f(v) = c(v)+1$, so adjacent vertices have different frequencies. Fix a natural number $r$ and write $R = r^{2d}$.
--
--   The **generalized flow shop instance** $S(r,d)$ (also called a flow shop with jumps: every job visits machines in one fixed global order but may skip machines) is defined as follows.
--
--   1. **Machines.** There are $R$ groups $M_1,\dots,M_R$ of machines; group $M_g$ consists of one machine $m_{g,v}$ for every vertex $v$, so there are $R\,n$ machines. The global order puts $m_{g,u}$ before $m_{h,v}$ if $g<h$, or if $g=h$ and $f(u) > f(v)$.
--   2. **Jobs.** For every vertex $v$ with frequency $f$ there are $r^{2(d-f)}$ groups of jobs $J^v_1,\dots,J^v_{r^{2(d-f)}}$, each consisting of $r^{2f}$ identical copies $j^v_{g,1},\dots,j^v_{g,r^{2f}}$. So each vertex owns $R$ jobs, and there are $R\,n$ jobs in total.
--   3. **Operations.** Job $j^v_{g,i}$ has a **long-operation** of length $r^{2(d-f)}$ on each of the machines
--   $$
--   m_{a+1,v},\ m_{a+2,v},\ \dots,\ m_{a+r^{2f},v}, \qquad a = (g-1)\, r^{2f},
--   $$
--   and a **short-operation** of length $0$ on every machine $m_{a',u}$ with $1 \le a' \le R$ and $\{u,v\}\in E$. It has no other operation. Its operations are processed in the global machine order.
--
--   The instance is the basic object of the paper's reduction from graph colouring to the generalized flow shop problem. Jobs of non-adjacent vertices share no machine on which either has a long-operation, so they can run in parallel. Jobs of adjacent vertices must respect each other's zero-length operations, and this is what makes them conflict.
--
--   **Formalization Note.** The instance is a `JobShopLTAS.Core.Instance` with machine and job types `Fin (r^{2d} n)`. The vertex set is `Fin n` and the colouring is a Mathlib `G.Coloring (Fin d)`. Machine index $p$ is $m_{g,v}$ with $g = \lfloor p/n\rfloor + 1$ and $v = p \bmod n$. Job index $q$ is $j^v_{g,i}$ with $v = \lfloor q/R\rfloor$, local index $t = q \bmod R$, $g = \lfloor t/r^{2f}\rfloor + 1$ and $i = (t \bmod r^{2f}) + 1$. The paper leaves machines of the same group and the same frequency unordered ("in an order so that it results in a generalized flow shop instance"). Here they are ordered by vertex index (`MachBefore`), via the injective key `machKey` $=((g-1)d + d - f(v))\,n + v$. Each job's operation list is its machine set sorted by this key. Under the published model's disjunctive constraint a zero-length operation cannot run strictly inside another operation on its machine, as the paper requires.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, pp. 20:16-20:17, Section 3.2.1 (generalized flow shops: p. 20:2)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-! # The generalized flow shop instance `S(r, d)` of the colouring reduction

Mastrolilli–Svensson, *Hardness of Approximating Flow and Job Shop Scheduling Problems*,
J. ACM 58(5) (2011), Article 20, §3.2.1 (pp. 20:16–20:17), with the notion of good
long-operations of §2.2.2 (p. 20:10) as re-used in §3.2.3 (p. 20:18).

**Input.** A simple graph `G` on the vertex set `Fin n` and a proper colouring
`c : G.Coloring (Fin d)`. The colour classes `I_1, …, I_d` are `I_f = {v | c v + 1 = f}`
(independent sets partitioning the vertices; empty classes are allowed), and vertex `v` has
**frequency** `f(v) = c v + 1 ∈ {1, …, d}` (`freq`). Write `R = r^{2d}` (`R r d`).

**Machines** are `Fin (r^{2d} · n)`. The machine at index `p` is `m_{g,v}` with group
`g = p / n + 1 ∈ {1, …, r^{2d}}` (`machGroup`) and vertex `v = p % n` (`machVtx`), i.e.
`p = (g - 1) · n + v`.

**Jobs** are `Fin (r^{2d} · n)`. Job `q` belongs to vertex `v = q / r^{2d}` (`jobVtx`); with
`f = f(v)` and local index `t = q % r^{2d}` (`jobLocal`) it is the job `j^v_{g,i}` with group
`g = t / r^{2f} + 1 ∈ {1, …, r^{2(d-f)}}` (`jobGroup`) and copy `i = t % r^{2f} + 1`
(`jobCopy`), i.e. `q = v · r^{2d} + (g - 1) · r^{2f} + (i - 1)`.

**Operations.** Job `j^v_{g,i}` has a long-operation of length `r^{2(d-f)}` on each of the
machines `m_{a+1,v}, …, m_{a+r^{2f},v}`, `a = (g-1)·r^{2f}` (`IsLong`), and a short-operation
(length `0`) on every machine `m_{a',u}`, `1 ≤ a' ≤ r^{2d}`, of every neighbour `u` of `v`;
it has no other operation (`jobMachines`). Its operations are these machines listed in the
global machine order of the paper (`opList`): `m_{g,u}` is before `m_{h,v}` if `g < h`, or
`g = h` and `f(u) > f(v)`; machines `m_{g,u}`, `m_{g,v}` of the same group and the same
frequency, which the paper leaves unordered, are ordered by vertex index (`MachBefore`,
implemented by the injective key `machKey`). -/

/-- `R = r^{2d}`: the number of machine groups, the number of jobs per vertex, and `lb`. -/
def R (r d : ℕ) : ℕ := r ^ (2 * d)

/-- The number of machines (and of jobs) of `S(r, d)`: `r^{2d} · n`. -/
def size (r d n : ℕ) : ℕ := R r d * n

/-- The (1-based) frequency `f(v) = c v + 1` of the vertex `v`, i.e. `v ∈ I_{f(v)}`. -/
def freq {n d : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d)) (v : Fin n) : ℕ :=
  (c v : ℕ) + 1

/-- The vertex `v` of the machine `p = m_{g,v}`. -/
def machVtx {r d n : ℕ} (p : Fin (size r d n)) : Fin n :=
  ⟨p.val % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
    rintro rfl
    exact absurd p.isLt (by simp [size])))⟩

/-- The vertex `v` of the job `q ∈ J^v`. -/
def jobVtx {r d n : ℕ} (q : Fin (size r d n)) : Fin n :=
  ⟨q.val / R r d, Nat.div_lt_of_lt_mul q.isLt⟩

/-- The index `t = (g - 1) · r^{2f} + (i - 1)` of the job `q = j^v_{g,i}` inside `J^v`. -/
def jobLocal {r d n : ℕ} (q : Fin (size r d n)) : ℕ := q.val % R r d

/-- The frequency `f` of the job `q`, i.e. the frequency of its vertex. -/
def jobFreq {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (q : Fin (size r d n)) : ℕ :=
  freq c (jobVtx q)

/-- The (1-based) group index `g` of the job `q = j^v_{g,i}`. -/
def jobGroup {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (q : Fin (size r d n)) : ℕ :=
  jobLocal q / r ^ (2 * jobFreq c q) + 1

/-- The (1-based) copy index `i` of the job `q = j^v_{g,i}`. -/
def jobCopy {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (q : Fin (size r d n)) : ℕ :=
  jobLocal q % r ^ (2 * jobFreq c q) + 1

/-- Job `q = j^v_{g,i}` (frequency `f`) has a long-operation on machine `p = m_{h,u}` iff
`u = v` and `a + 1 ≤ h ≤ a + r^{2f}` with `a = (g - 1) · r^{2f}`. -/
def IsLong {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (q p : Fin (size r d n)) : Prop :=
  machVtx p = jobVtx q ∧
    (jobGroup c q - 1) * r ^ (2 * jobFreq c q) + 1 ≤ FlowJobHardness.FlowShopGap.machGroup n p.val ∧
    FlowJobHardness.FlowShopGap.machGroup n p.val ≤ (jobGroup c q - 1) * r ^ (2 * jobFreq c q) + r ^ (2 * jobFreq c q)

open Classical in
/-- The set of machines on which job `q` has an operation: its long machines (`IsLong`) and
all machines `m_{a,u}` of all neighbours `u` of its vertex (short-operations). -/
noncomputable def jobMachines {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (q : Fin (size r d n)) : Finset (Fin (size r d n)) :=
  Finset.univ.filter fun p => IsLong c q p ∨ G.Adj (jobVtx q) (machVtx p)

/-- The global machine order of §3.2.1: `p = m_{g,u}` is before `p' = m_{h,v}` iff `g < h`,
or `g = h` and `f(u) > f(v)`, or (tie-break, not in the paper) `g = h`, `f(u) = f(v)` and
`u < v` as vertex indices. -/
def MachBefore {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (p p' : Fin (size r d n)) : Prop :=
  FlowJobHardness.FlowShopGap.machGroup n p.val < FlowJobHardness.FlowShopGap.machGroup n p'.val ∨
    (FlowJobHardness.FlowShopGap.machGroup n p.val = FlowJobHardness.FlowShopGap.machGroup n p'.val ∧ freq c (machVtx p') < freq c (machVtx p)) ∨
    (FlowJobHardness.FlowShopGap.machGroup n p.val = FlowJobHardness.FlowShopGap.machGroup n p'.val ∧ freq c (machVtx p') = freq c (machVtx p) ∧
      machVtx p < machVtx p')

/-- A natural-number key realising `MachBefore`: for `p = m_{g,v}`,
`key = ((g - 1) · d + (d - f(v))) · n + v`. It is injective and `MachBefore p p'` holds iff
`machKey p < machKey p'`. -/
def machKey {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (p : Fin (size r d n)) : ℕ :=
  ((p.val / n) * d + (d - freq c (machVtx p))) * n + p.val % n

/-- The machines of job `q`, listed in the global machine order (sorted by `machKey`). -/
noncomputable def opList {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (q : Fin (size r d n)) : List (Fin (size r d n)) :=
  (jobMachines c q).toList.mergeSort (fun a b => decide (machKey c a ≤ machKey c b))

open Classical in
/-- Processing time of job `q` on machine `p`: `r^{2(d-f)}` (`f` the frequency of `q`) on its
long machines, `0` otherwise. -/
noncomputable def procTime {r d n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d))
    (q p : Fin (size r d n)) : ℝ :=
  if IsLong c q p then (r : ℝ) ^ (2 * (d - jobFreq c q)) else 0

/-- The generalized flow shop instance `S(r, d)` of §3.2.1, built from the graph `G` with the
proper colouring `c`, as a job shop instance with `r^{2d} n` machines and `r^{2d} n` jobs:
job `q` has `μ q = |opList q|` operations, its `i`-th one (0-based) on the `i`-th machine of
`opList q`, with processing time `procTime`. -/
noncomputable def inst {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ) :
    Instance (size r d n) (size r d n) where
  μ := fun q => (opList c q).length
  π := fun q i => (opList c q).get i
  p := fun q i => procTime c q ((opList c q).get i)
  p_nonneg := by
    intro q i
    unfold procTime
    split_ifs <;> positivity

end FlowJobHardness.ColoringReduction


