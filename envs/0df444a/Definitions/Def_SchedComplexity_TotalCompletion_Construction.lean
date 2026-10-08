-- Prove2me | Definitions.Def_SchedComplexity_TotalCompletion_Construction
-- name    : SchedComplexity_TotalCompletion_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:13.937166+00:00
-- url     : https://prove2.me/theorems/970183a5-3a81-4978-987d-40bc4befdd04
-- title:
--   The construction of Theorem 4(a): from KNAPSACK to $n|1|r_n\ge0,w_j=1|\sum w_jC_j$
-- statement:
--   **The construction of Theorem 4(a)** (Brucker, Lenstra and Rinnooy Kan, p. 22). Let $a_1,\dots,a_t,b$ be a KNAPSACK instance, $A=\sum_{j\in T}a_j$ and $a_*=\max_{j\in T}a_j$. Define the integers
--
--   $$t'=t(t+1)a_*,\qquad \tau=(t'+1)(b+1)+t',\qquad u=\tfrac12(t+t')(t+t'+1)\tau+(t+1)\tau,$$
--
--   $$\sigma=(t+t')\tau+A+1,\qquad \upsilon=u(\sigma+1),\qquad y=\upsilon+\tfrac12u(u+1)\upsilon .$$
--
--   The scheduling instance has $n=t+t'+u+1$ jobs in four groups:
--
--   1. $T=\{1,\dots,t\}$: $r_j=0$, $p_j=\tau+a_j$;
--   2. $T'=\{t+1,\dots,t+t'\}$: $r_j=0$, $p_j=\tau$;
--   3. $U=\{t+t'+1,\dots,t+t'+u\}$: $r_j=0$, $p_j=\upsilon$;
--   4. the last job $J_n$: $r_n=t\tau+b$, $p_n=1$;
--
--   all with weight $w_j=1$. The threshold is $y$. Also defined are, for a set $S$ of items, the job sets $\{J_j\mid j\in S\}\subseteq T$ and $\{J_{t+j}\mid j\in S\}$; for $S=T-S_0$ the latter is the set $S'$ of the forward direction.
--
--   The number $\sigma$ equals $\sum_{j\notin U}p_j$, the total processing time outside $U$; the definition uses the closed form printed in the paper. The letter $u$ plays two roles in the paper: it is the number of jobs of $U$, and it is the bound $\sum_{j\notin U}C_j\le u$ established in the proof; the paper's forward computation shows that the two coincide.
--
--   **Formalization Note** Jobs are indexed by `Fin n` (0-based), so $T$, $T'$, $U$ are the index ranges $[0,t)$, $[t,t+t')$, $[t+t',t+t'+u)$ and $J_n$ is index $t+t'+u$. The halves are natural-number divisions that are exact, since $(t+t')(t+t'+1)$ and $u(u+1)$ are even. $a_*$ is $0$ when $t=0$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 16 (A, a_*), p. 22, proof of Theorem 4(a) (construction)

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.TotalCompletion

/-! # The construction of Theorem 4(a)

Brucker, Lenstra & Rinnooy Kan 1975, proof of Theorem 4(a), p. 22: from a KNAPSACK instance
`a_1, …, a_t, b` (items indexed by `Fin t`, 0-based) build an instance of
`n|1|r_n≥0,w_j=1|Σw_jC_j` and a threshold `y`. Every constant below is the one printed on p. 22,
with `A = Σ_{j∈T} a_j` and `a_* = max_{j∈T} a_j` (p. 16). -/

variable {t : ℕ}

/-- `A = Σ_{j∈T} a_j` (p. 16). -/
def sumA (a : Fin t → ℕ) : ℕ := ∑ i, a i

/-- `t' = t(t + 1)a_*`. -/
def tPrime (a : Fin t → ℕ) : ℕ := t * (t + 1) * SchedComplexity.Tardiness.aStar a

/-- `τ = (t' + 1)(b + 1) + t'`. -/
def tau (a : Fin t → ℕ) (b : ℕ) : ℕ := (tPrime a + 1) * (b + 1) + tPrime a

/-- `u = ½(t + t')(t + t' + 1)τ + (t + 1)τ`. The product `(t + t')(t + t' + 1)` is even, so the
natural-number division by `2` is exact. The paper uses `u` twice: as the number of jobs in the
group `U`, and as the bound `Σ_{j∉U} C_j ≤ u` in the proof (p. 22 shows that the forward
schedule's bound equals this `u`). -/
def uCount (a : Fin t → ℕ) (b : ℕ) : ℕ :=
  (t + tPrime a) * (t + tPrime a + 1) / 2 * tau a b + (t + 1) * tau a b

/-- `σ = Σ_{j∉U} p_j1 = (t + t')τ + A + 1`; the definition is the closed form printed on p. 22. -/
def sigma (a : Fin t → ℕ) (b : ℕ) : ℕ := (t + tPrime a) * tau a b + sumA a + 1

/-- `υ = u(σ + 1)`. -/
def upsilon (a : Fin t → ℕ) (b : ℕ) : ℕ := uCount a b * (sigma a b + 1)

/-- The threshold `y = υ + ½u(u + 1)υ`; `u(u + 1)` is even, so the division by `2` is exact. -/
def yThreshold (a : Fin t → ℕ) (b : ℕ) : ℕ :=
  upsilon a b + uCount a b * (uCount a b + 1) / 2 * upsilon a b

/-- The number of jobs `n = t + t' + u + 1`. -/
def numJobs (a : Fin t → ℕ) (b : ℕ) : ℕ := t + tPrime a + uCount a b + 1

/-- The four groups of jobs, as ranges of the 0-based index `j` (the paper's `J_{j+1}`):
`T = {1, …, t}` is `j < t`; `T' = {t+1, …, t+t'}` is `t ≤ j < t + t'`;
`U = {t+t'+1, …, t+t'+u}` is `t + t' ≤ j < t + t' + u`; and the last job `J_n` is
`j = t + t' + u`. -/
def groupT (a : Fin t → ℕ) (b : ℕ) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => j.val < t

/-- The group `T' = {t+1, …, t+t'}` (0-based indices `t, …, t + t' - 1`). -/
def groupT' (a : Fin t → ℕ) (b : ℕ) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => t ≤ j.val ∧ j.val < t + tPrime a

/-- The group `U = {t+t'+1, …, t+t'+u}` (0-based indices `t + t', …, t + t' + u - 1`). -/
def groupU (a : Fin t → ℕ) (b : ℕ) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b

/-- The last job `J_n` (0-based index `n - 1 = t + t' + u`). -/
def lastJob (a : Fin t → ℕ) (b : ℕ) : Fin (numJobs a b) :=
  ⟨t + tPrime a + uCount a b, by unfold numJobs; omega⟩

/-- Processing times: `p_j1 = τ + a_j` (`j ∈ T`), `p_j1 = τ` (`j ∈ T'`), `p_j1 = υ` (`j ∈ U`),
`p_n1 = 1`. -/
def procTime (a : Fin t → ℕ) (b : ℕ) (j : Fin (numJobs a b)) : ℕ :=
  if h : j.val < t then tau a b + a ⟨j.val, h⟩
  else if j.val < t + tPrime a then tau a b
  else if j.val < t + tPrime a + uCount a b then upsilon a b
  else 1

/-- Release dates: `r_j = 0` for every job but the last, `r_n = tτ + b`. -/
def release (a : Fin t → ℕ) (b : ℕ) (j : Fin (numJobs a b)) : ℕ :=
  if j.val = t + tPrime a + uCount a b then t * tau a b + b else 0

/-- Weights: `w_j = 1` for every job. -/
def weight (a : Fin t → ℕ) (b : ℕ) (_j : Fin (numJobs a b)) : ℕ := 1

/-- For a set `S` of items, the jobs `{J_j | j ∈ S} ⊆ T`. -/
def jobsT (a : Fin t → ℕ) (b : ℕ) (S : Finset (Fin t)) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => ∃ i ∈ S, j.val = i.val

/-- For a set `S` of items, the jobs `{J_{t+j} | j ∈ S}`; for `S = T − S₀` this is the set `S'`
of the forward direction on p. 22 (a subset of `T'` when `t ≤ t'`). -/
def jobsShift (a : Fin t → ℕ) (b : ℕ) (S : Finset (Fin t)) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => ∃ i ∈ S, j.val = t + i.val

end SchedComplexity.TotalCompletion


