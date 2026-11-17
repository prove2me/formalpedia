-- Prove2me | Definitions.Def_IntConeFPT_Supplement_Scheduling
-- name    : IntConeFPT_Supplement_Scheduling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:25:40.122598+00:00
-- url     : https://prove2.me/theorems/15197c07-120b-4f4a-9d40-6ca4eef11b55
-- title:
--   Scheduling on uniformly related machines — instances, completion loads, envy, the optima of $Q\|C_{\max}$, $Q\|C_{\min}$, $Q\|C_{\mathrm{envy}}$, and encodings
-- statement:
--   An **instance** of scheduling on uniformly related machines consists of $n\ge1$ jobs with positive rational processing times $p_1,\dots,p_n$ and $m\ge1$ machines with positive rational speeds $s_1,\dots,s_m$. Job $j$ takes time $p_j/s_i$ on machine $i$. A **schedule** is a map $\sigma:[n]\to[m]$: every job goes to exactly one machine, and machines may stay empty.
--
--   1. The **completion load** of machine $i$ is $C_i(\sigma)=\sum_{j\in\sigma^{-1}(i)}p_j/s_i$; an empty machine has load $0$.
--   2. The maximum and minimum completion loads are $\max_i C_i(\sigma)$ and $\min_i C_i(\sigma)$, and the **envy** is $E(\sigma)=\max_i C_i(\sigma)-\min_i C_i(\sigma)$.
--   3. The optima over all $m^n$ schedules are
--   $$
--   \mathrm{OPT}_{\max}=\min_\sigma\max_i C_i(\sigma),\qquad
--   \mathrm{OPT}_{\min}=\max_\sigma\min_i C_i(\sigma),\qquad
--   \mathrm{OPT}_{\mathrm{envy}}=\min_\sigma E(\sigma),
--   $$
--   the optimal values of $Q\|C_{\max}$, $Q\|C_{\min}$ and $Q\|C_{\mathrm{envy}}$.
--   4. $\tau$ is the number of distinct speeds, $p_{\max}=\max_j p_j$ and $s_{\min}=\min_i s_i$.
--   5. The instance is encoded as $n$, $m$ in binary, followed by $p_1,\dots,p_n$ and $s_1,\dots,s_m$ as rationals in lowest terms; $|I|$ is the length of this word. A schedule is encoded as the list $\sigma(1),\dots,\sigma(n)$ of machine indices in binary.
--
--   These are the objects of the additive approximation schemes of Theorems 25 and 26.
--
--   **Formalization Note** Jobs and machines are indexed by `Fin n` and `Fin m` (0-based). Loads are real numbers, computed with the published `HochbaumShmoys.Uniform.machineTime` and `makespan` on the cast data. Maxima and minima are suprema and infima over finite index sets, so they are attained whenever the index set is nonempty, which `Valid` guarantees. The alphabet and number encodings are the published `OnlineCRS.Combine` ones, used by the base mission as well.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Appendix A.8, p.30; §A.8.1, p.31; proof of Theorem 26, p.32

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_HochbaumShmoys_Uniform_Packing

set_option autoImplicit false

namespace IntConeFPT.Supplement

open OnlineCRS.Combine

/-- **Scheduling on uniformly related machines: an instance.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Appendix A.8, p.30 ("n explicitly listed jobs with
positive rational processing times p1, …, pn and m explicitly listed machines") and §A.8.1, p.31
("the speeds si are positive rationals").

`n` jobs with processing times `p : Fin n → ℚ`, `m` machines with speeds `s : Fin m → ℚ`.

**Formalization Note.** Jobs and machines are 0-based (`Fin n`, `Fin m`). Positivity and
`n, m ≥ 1` are in `SchedInstance.Valid`. -/
structure SchedInstance where
  n : ℕ
  m : ℕ
  p : Fin n → ℚ
  s : Fin m → ℚ

namespace SchedInstance

/-- Valid instances: at least one job and one machine, positive rational processing times and
speeds (p.30, p.31). `n ≥ 1` and `m ≥ 1` make `p_max = max_j p_j` and `s_min = min_i s_i`
defined. -/
def Valid (I : SchedInstance) : Prop :=
  1 ≤ I.n ∧ 1 ≤ I.m ∧ (∀ j, 0 < I.p j) ∧ (∀ i, 0 < I.s i)

/-- Processing times as reals. -/
def pR (I : SchedInstance) : Fin I.n → ℝ := fun j => (I.p j : ℝ)

/-- Speeds as reals. -/
def sR (I : SchedInstance) : Fin I.m → ℝ := fun i => (I.s i : ℝ)

/-- `τ`, the number of distinct speeds (p.31, "Let τ denote the number of distinct speeds"). -/
def numSpeeds (I : SchedInstance) : ℕ := (Finset.univ.image I.s).card

/-- `p_max = max_j p_j` (p.30). A maximum over the finite nonempty `Fin n` on valid instances. -/
noncomputable def pmax (I : SchedInstance) : ℝ := ⨆ j, I.pR j

/-- `s_min = min_i s_i` (p.31). A minimum over the finite nonempty `Fin m` on valid instances. -/
noncomputable def smin (I : SchedInstance) : ℝ := ⨅ i, I.sR i

/-- The completion load `C_i(σ) = Σ_{j ∈ σ⁻¹(i)} p_j / s_i` of machine `i` (p.31, p.32), the
published `HochbaumShmoys.Uniform.machineTime`. An empty machine has load `0`. -/
noncomputable def load (I : SchedInstance) (σ : Fin I.n → Fin I.m) (i : Fin I.m) : ℝ :=
  HochbaumShmoys.Uniform.machineTime I.pR I.sR σ i

/-- The maximum completion load `max_i C_i(σ)` (the makespan, published
`HochbaumShmoys.Uniform.makespan`). -/
noncomputable def maxLoad (I : SchedInstance) (σ : Fin I.n → Fin I.m) : ℝ :=
  HochbaumShmoys.Uniform.makespan I.pR I.sR σ

/-- The minimum completion load `min_i C_i(σ)` (an infimum over the finite set of machines,
a minimum when `m ≥ 1`). -/
noncomputable def minLoad (I : SchedInstance) (σ : Fin I.n → Fin I.m) : ℝ :=
  ⨅ i, I.load σ i

/-- The envy `E(σ) = max_i C_i(σ) − min_i C_i(σ)` (p.32, proof of Theorem 26). -/
noncomputable def envy (I : SchedInstance) (σ : Fin I.n → Fin I.m) : ℝ :=
  I.maxLoad σ - I.minLoad σ

/-- `OPT` of `Q||Cmax`: the minimum over all `m^n` schedules `σ : [n] → [m]` of the maximum
completion load (a minimum over a finite nonempty set when `m ≥ 1`). -/
noncomputable def optMax (I : SchedInstance) : ℝ := ⨅ σ : Fin I.n → Fin I.m, I.maxLoad σ

/-- `OPT` of `Q||Cmin`: the maximum over all schedules of the minimum completion load. -/
noncomputable def optMin (I : SchedInstance) : ℝ := ⨆ σ : Fin I.n → Fin I.m, I.minLoad σ

/-- `OPT` of `Q||Cenvy`: the minimum over all schedules of the envy. -/
noncomputable def optEnvy (I : SchedInstance) : ℝ := ⨅ σ : Fin I.n → Fin I.m, I.envy σ

end SchedInstance

/-- **Encoding of a scheduling instance**, `|I| = (encSched I).length`: `n`, `m` in binary, then
`p_1, …, p_n` and `s_1, …, s_m` as rationals in lowest terms (published `encVec`), items
separated by the symbol `3`. -/
def encSched (I : SchedInstance) : List Sym :=
  encNat I.n ++ [3] ++ encNat I.m ++ [3] ++ encVec I.p ++ encVec I.s

/-- **Encoding of a schedule** `σ : [n] → [m]`: the list `σ(1), …, σ(n)` of 0-based machine
indices in binary, each followed by the separator `3`. -/
def encSchedule {n m : ℕ} (σ : Fin n → Fin m) : List Sym :=
  (List.finRange n).flatMap fun j => encNat (σ j : ℕ) ++ [3]

end IntConeFPT.Supplement


