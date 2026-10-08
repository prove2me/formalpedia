-- Prove2me | Definitions.Def_FlowJobHardness_FlowShopGap_Construction
-- name    : FlowJobHardness_FlowShopGap_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:33:33.675181+00:00
-- url     : https://prove2.me/theorems/bf47bf87-7e6d-4d66-a9c5-0b04d97b8762
-- title:
--   The flow shop instance $F(r,d)$ (Section 2.2.1)
-- statement:
--   Fix natural numbers $r$ and $d$. The **flow shop instance** $F(r,d)$ of Mastrolilli and Svensson is built as follows.
--
--   1. **Machines.** There are $r^{2d}$ groups of machines $M_1,\dots,M_{r^{2d}}$. Group $M_g$ consists of $d$ machines $m_{g,1},\dots,m_{g,d}$, one for each **frequency** $1,\dots,d$. The machines are totally ordered: $m_{g,i}$ comes before $m_{h,j}$ if $g<h$, or if $g=h$ and $i>j$. Inside a group the order is therefore $m_{g,d},m_{g,d-1},\dots,m_{g,1}$.
--   2. **Jobs.** For each frequency $f=1,\dots,d$ there are $r^{2(d-f)}$ groups of jobs $J^f_1,\dots,J^f_{r^{2(d-f)}}$. Group $J^f_g$ consists of $r^{2f}$ identical copies $j^f_{g,1},\dots,j^f_{g,r^{2f}}$ of a job that must be processed for $r^{2(d-f)}$ time units on each of the machines
--   $$m_{a+1,f},\ m_{a+2,f},\ \dots,\ m_{a+r^{2f},f},\qquad a=(g-1)\,r^{2f},$$
--   and for $0$ time units on every other machine.
--   3. **Flow shop.** Every job has exactly one operation on every machine, and every job visits the machines in the common order of item 1.
--
--   There are $r^{2d}\cdot d$ machines and $r^{2d}\cdot d$ jobs ($r^{2d}$ jobs of each frequency). An operation with positive processing time is a **long-operation**, one with processing time $0$ a **short-operation**. A short-operation still occupies its machine at an instant: in a feasible schedule it cannot be performed strictly inside another operation on the same machine.
--
--   This is the instance whose optimal makespan the paper shows to exceed the trivial lower bound $\mathrm{lb}=\max(C,D)$ (maximal machine load, maximal job length) by a factor $\min(r,d/4)$.
--
--   **Formalization Note** The instance is a `JobShopLTAS.Core.Instance` with $r^{2d}d$ machines and $r^{2d}d$ jobs (`size r d`). Machine position $p\in\{0,\dots,r^{2d}d-1\}$ is $m_{g,i}$ with $g=\lfloor p/d\rfloor+1$ (`machGroup`) and $i=d-(p\bmod d)$ (`machFreq`), i.e. $p=(g-1)d+(d-i)$, so the order of positions is the paper's machine order. Job $q$ is $j^f_{g,a}$ with $f=\lfloor q/r^{2d}\rfloor+1$ (`jobFreq`), $g=\lfloor (q\bmod r^{2d})/r^{2f}\rfloor+1$ (`jobGroup`) and $a=(q\bmod r^{2d})\bmod r^{2f}+1$ (`jobCopy`). Every job has $r^{2d}d$ operations and its $i$-th operation (0-based) runs on machine position $i$. Frequencies, groups and copies are 1-based, as in the paper; the exponent $d-f$ is natural-number subtraction with $f\le d$.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, pp. 20:9-20:10, Section 2.2.1 (Construction)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

open JobShopLTAS.Core

namespace FlowJobHardness.FlowShopGap

/-! # The flow shop instance `F(r, d)`

Mastrolilli–Svensson, *Hardness of Approximating Flow and Job Shop Scheduling Problems*,
J. ACM 58(5) (2011), Article 20, §2.2.1 (pp. 20:9–20:10).

**Encoding.** Write `R = r^{2d}` (the number of machine groups, and `lb`).

* Machines are `Fin (R * d)`. The machine at position `p` is `m_{g,i}` with
  `g = p / d + 1` (`machGroup`) and `i = d - p % d` (`machFreq`), i.e.
  `p = (g - 1) * d + (d - i)`. Position order is exactly the paper's machine order:
  `m_{g,i}` before `m_{h,j}` iff `g < h`, or `g = h` and `i > j`.
* Jobs are `Fin (R * d)`. Job `q` is `j^f_{g,a}` with frequency `f = q / R + 1`
  (`jobFreq`), group `g = (q % R) / r^{2f} + 1` (`jobGroup`) and copy
  `a = (q % R) % r^{2f} + 1` (`jobCopy`), i.e. `q = (f-1) R + (g-1) r^{2f} + (a-1)`.
* Every job has one operation per machine, the `i`-th one (0-based) on machine `i`
  (a flow shop: all jobs visit the machines in the same order).
* Frequencies, groups and copies are 1-based natural numbers, as in the paper. -/

/-- The number of machines (and of jobs) of `F(r, d)`: `r^{2d} · d`. -/
def size (r d : ℕ) : ℕ := r ^ (2 * d) * d

/-- The (1-based) group index `g` of the machine at position `p`: `p = (g-1)·d + (d-i)`. -/
def machGroup (d p : ℕ) : ℕ := p / d + 1

/-- The (1-based) frequency `i` of the machine at position `p` (machine `m_{g,i}`). -/
def machFreq (d p : ℕ) : ℕ := d - p % d

/-- The (1-based) frequency `f` of job `q`. -/
def jobFreq (r d q : ℕ) : ℕ := q / r ^ (2 * d) + 1

/-- The (1-based) index `g` of the job group `J^f_g` containing job `q`. -/
def jobGroup (r d q : ℕ) : ℕ := (q % r ^ (2 * d)) / r ^ (2 * jobFreq r d q) + 1

/-- The (1-based) copy index `a` of job `q = j^f_{g,a}` inside its group. -/
def jobCopy (r d q : ℕ) : ℕ := (q % r ^ (2 * d)) % r ^ (2 * jobFreq r d q) + 1

/-- Job `q = j^f_{g,a}` has a long-operation on machine `p = m_{h,i}` iff `i = f` and
`h ∈ {c+1, …, c + r^{2f}}` with `c = (g - 1) · r^{2f}` (the machines
`m_{c+1,f}, …, m_{c+r^{2f},f}` of §2.2.1). -/
abbrev IsLongPair (r d q p : ℕ) : Prop :=
  machFreq d p = jobFreq r d q ∧
    (jobGroup r d q - 1) * r ^ (2 * jobFreq r d q) + 1 ≤ machGroup d p ∧
    machGroup d p ≤ (jobGroup r d q - 1) * r ^ (2 * jobFreq r d q) + r ^ (2 * jobFreq r d q)

/-- Processing time of job `q` on machine `p`: `r^{2(d-f)}` on its machines
`m_{c+1,f}, …, m_{c+r^{2f},f}` (`f` = frequency of `q`), and `0` on all other machines. -/
noncomputable def procTime (r d q p : ℕ) : ℝ :=
  if IsLongPair r d q p then (r : ℝ) ^ (2 * (d - jobFreq r d q)) else 0

/-- The flow shop instance `F(r, d)` of §2.2.1 as a job shop instance with `r^{2d}·d`
machines and `r^{2d}·d` jobs: job `q` has `r^{2d}·d` operations, its `i`-th operation runs on
machine `i` for `procTime r d q i` time units. -/
noncomputable def inst (r d : ℕ) : Instance (size r d) (size r d) where
  μ := fun _ => size r d
  π := fun _ i => i
  p := fun q i => procTime r d q i
  p_nonneg := by
    intro q i
    unfold procTime
    split_ifs <;> positivity

end FlowJobHardness.FlowShopGap


