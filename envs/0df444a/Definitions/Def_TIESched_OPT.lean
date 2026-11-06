-- Prove2me | Definitions.Def_TIESched_OPT
-- name    : TIESched_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:44:03.556568+00:00
-- url     : https://prove2.me/theorems/3c9ae0ba-55f5-491a-84a5-208c1d7d4bcd
-- title:
--   Makespan $C(p,x)$ and optimal integral makespan $\mathrm{OPT}(p)$
-- statement:
--   There are $m\ge 2$ machines $[m]$ and a finite set $S\subseteq\mathbb N$ of job labels. A report (processing-time matrix) is $p\in\mathbb R^{m\times S}$; it is **nonnegative** if $p_{ij}\ge 0$ for all $i,j$ (zero processing times are allowed). For a matrix $x\in\mathbb R^{m\times S}$ the **makespan** is the maximum machine load
--   $$C(p,x)=\max_{i\in[m]}\sum_{j\in S}p_{ij}x_{ij}.$$
--   An allocation is integral if every job is assigned entirely to one machine, i.e. $x$ is the indicator matrix of an assignment $\sigma:S\to[m]$. The **optimal integral makespan** is
--   $$\mathrm{OPT}(p)=\min_{x\in X_{\mathrm{int}}(S)}C(p,x)=\min_{\sigma:S\to[m]}\max_{i\in[m]}\sum_{j:\,\sigma(j)=i}p_{ij}.$$
--   It is the benchmark of the whole paper; on the empty job set it is $0$.
--
--   **Formalization Note.** Machines are `Fin m` (`m ≠ 0`), job sets are `Finset ℕ`, reports are total functions `Fin m → S → ℝ` and nonnegativity is the predicate `IsNonneg`. Feasible integral allocations are identified with assignments `S → Fin m` via `intAlloc`; maximum and minimum are `Finset.sup'`/`Finset.inf'` over nonempty finite types, so there is no junk value.
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), §2, Instances and allocations, pp.6–7

import Mathlib

set_option autoImplicit false

namespace TIESched

/-- **Nonnegative report** on a finite job set `S ⊆ ℕ`: every processing time `p i j` is `≥ 0`.
Wang, Xu, Zhang, *Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound*,
arXiv:2611.05142, §2, *Instances and allocations*, pp.6–7: `p ∈ ℝ^{m×S}_{≥0}`, "zero processing
times are allowed".

**Formalization Note.** Machines are `Fin m`; a job set is a `Finset ℕ` (p.7: "an arbitrary finite
set of job labels `S ⊆ ℕ`"), and a report is a total function `Fin m → S → ℝ`. The mechanism domain
`ℝ^{m×S}_{≥0}` is carved out by this predicate, which every statement uses as a hypothesis. -/
def IsNonneg {m : ℕ} {S : Finset ℕ} (p : Fin m → S → ℝ) : Prop :=
  ∀ i j, 0 ≤ p i j

/-- **Makespan** `C(p, x) = max_{i ∈ [m]} Σ_{j ∈ S} p_ij x_ij` of an allocation matrix `x` under the
processing times `p` (arXiv:2611.05142, §2, p.7).

**Formalization Note.** The maximum over the nonempty machine set `Fin m` (`m ≠ 0`) is
`Finset.sup'`; it is a genuine maximum, with no junk value. -/
noncomputable def makespan {m : ℕ} [NeZero m] {S : Finset ℕ} (p x : Fin m → S → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, p i j * x i j)

/-- The **integral allocation matrix** of an assignment `σ : S → [m]` of jobs to machines:
`x_ij = 1` if `σ j = i` and `0` otherwise (arXiv:2611.05142, §2, p.7: "An allocation is integral if
`x_ij ∈ {0,1}` for every `i, j`"). Feasible integral allocations are exactly these matrices. -/
def intAlloc {m : ℕ} {S : Finset ℕ} (σ : S → Fin m) : Fin m → S → ℝ :=
  fun i j => if σ j = i then 1 else 0

/-- **Optimal integral makespan** `OPT(p) = min_{x ∈ X_int(S)} C(p, x)` (arXiv:2611.05142, §2, p.7:
"Throughout the paper, our benchmark is the optimal integral makespan").

**Formalization Note.** A feasible integral allocation (entries in `{0,1}`, each column summing to
one) is the indicator matrix `intAlloc σ` of a unique assignment `σ : S → Fin m`, so the minimum is a
`Finset.inf'` over the finite, nonempty type of assignments. On the empty job set the unique
assignment has makespan `0`, so `OPT = 0` there (p.12: "Both values are zero on the empty
instance"). The benchmark is integral, never fractional. -/
noncomputable def OPT {m : ℕ} [NeZero m] {S : Finset ℕ} (p : Fin m → S → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun σ : S → Fin m => makespan p (intAlloc σ))

end TIESched


