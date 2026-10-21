-- Prove2me | Definitions.Def_HochbaumShmoys_Uniform_Packing
-- name    : HochbaumShmoys_Uniform_Packing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:37.552719+00:00
-- url     : https://prove2.me/theorems/3eed3055-87a7-4468-a033-323d4ccfdb3d
-- title:
--   Packings, $\varepsilon$-relaxed decision procedures, and the makespan on uniform machines (§1, p. 539; §2, pp. 540–541)
-- statement:
--   Let $m$ machines have speeds $s_1,\dots,s_m$ and let $n$ jobs have processing times $p_1,\dots,p_n$. If job $j$ is executed on machine $i$ it takes $p_j/s_i$ time units. A **schedule** (equivalently a **packing**) is a map $\sigma:\{1,\dots,n\}\to\{1,\dots,m\}$; its parts $B_i=\sigma^{-1}(i)$ may be empty.
--
--   1. The **load** of bin $i$ under $\sigma$ for piece sizes $p$ is $\sum_{j\in B_i} p_j$.
--   2. For bin sizes $b_1,\dots,b_m$, $\sigma$ is a **truly feasible packing** if $\sum_{j\in B_i}p_j\le b_i$ for every $i$, and an **$\varepsilon$-relaxed feasible packing** if $\sum_{j\in B_i}p_j\le(1+\varepsilon)\,b_i$ for every $i$.
--   3. An **$\varepsilon$-relaxed decision procedure** $D$ maps an instance $(p,b)$ to an optional packing such that, whenever all $p_j>0$ and all $b_i>0$: if $D(p,b)$ is a packing $\sigma$, then $\sigma$ is $\varepsilon$-relaxed feasible; and if $D(p,b)$ is the certificate "none", then no truly feasible packing of $p$ into $b$ exists.
--   4. The completion time of machine $i$ is $\sum_{j\in B_i}p_j/s_i$, and the **makespan** of $\sigma$ is
--   $$C_{\max}(\sigma)=\max_{1\le i\le m}\ \sum_{j:\ \sigma(j)=i}\frac{p_j}{s_i}.$$
--
--   These are the objects of the minimum makespan problem on uniform parallel machines ($Q\|C_{\max}$) and of the bin-packing problem with variable bin sizes used by the dual approximation approach: a schedule has makespan at most $T$ exactly when it is a truly feasible packing of the pieces $p_j$ into bins of sizes $T s_i$.
--
--   **Formalization Note** Jobs and machines are indexed by `Fin n` and `Fin m`; the makespan is a supremum over the finite set of machines (a maximum when $m\ge1$, and $0$ when $m=0$). The decision-procedure property is required on instances with positive sizes, the instances to which the paper applies it. The paper's "certificate that no truly feasible packing exists" is the answer `none`.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 539, §1 (the model) and p. 541, §2 (truly feasible and ε-relaxed feasible packings, ε-relaxed decision procedure)

import Mathlib

namespace HochbaumShmoys.Uniform

open Finset

/-- Total size of the pieces (jobs) that the packing `σ` puts into bin (machine) `i`. -/
def binLoad {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j ∈ univ.filter (fun j => σ j = i), p j

/-- A truly feasible packing of the pieces `p` into bins of sizes `b`: every bin `B_i = σ⁻¹(i)`
holds total size at most `b i` (bins may be empty). -/
def IsTrulyFeasible {m n : ℕ} (p : Fin n → ℝ) (b : Fin m → ℝ) (σ : Fin n → Fin m) : Prop :=
  ∀ i, binLoad p σ i ≤ b i

/-- An `ε`-relaxed feasible packing: every bin holds total size at most `(1 + ε) b i`. -/
def IsRelaxedFeasible {m n : ℕ} (ε : ℝ) (p : Fin n → ℝ) (b : Fin m → ℝ)
    (σ : Fin n → Fin m) : Prop :=
  ∀ i, binLoad p σ i ≤ (1 + ε) * b i

/-- An `ε`-relaxed decision procedure: on every instance with positive piece sizes and positive
bin sizes it outputs either an `ε`-relaxed feasible packing (`some σ`), or the certificate
`none`, which it may output only when no truly feasible packing exists. -/
def IsRelaxedDecisionProcedure {m n : ℕ} (ε : ℝ)
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m)) : Prop :=
  ∀ (p : Fin n → ℝ) (b : Fin m → ℝ), (∀ j, 0 < p j) → (∀ i, 0 < b i) →
    (∀ σ, D p b = some σ → IsRelaxedFeasible ε p b σ) ∧
    (D p b = none → ∀ σ, ¬ IsTrulyFeasible p b σ)

/-- Completion time of machine `i` of speed `s i` under the schedule `σ`: job `j` takes
`p j / s i` time units on machine `i`. -/
noncomputable def machineTime {m n : ℕ} (p : Fin n → ℝ) (s : Fin m → ℝ) (σ : Fin n → Fin m)
    (i : Fin m) : ℝ :=
  ∑ j ∈ univ.filter (fun j => σ j = i), p j / s i

/-- Makespan of the schedule `σ`: the largest machine completion time (a maximum over the finite
set of machines; `0` if there are no machines). -/
noncomputable def makespan {m n : ℕ} (p : Fin n → ℝ) (s : Fin m → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ⨆ i, machineTime p s σ i

end HochbaumShmoys.Uniform


