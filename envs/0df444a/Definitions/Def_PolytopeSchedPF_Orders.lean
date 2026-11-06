-- Prove2me | Definitions.Def_PolytopeSchedPF_Orders
-- name    : PolytopeSchedPF_Orders
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:31.861947+00:00
-- url     : https://prove2.me/theorems/e512a1d8-a88d-4888-95c5-0d5d249afac8
-- title:
--   Orders, suffixes $S^\pi_b$, $\mathrm{OPT}(p)$, $\mathrm{OPT}_\pi(p)$ and $\alpha$-greedy schedules
-- statement:
--   In §5 all jobs are released at time $0$. An **order** is a permutation $\pi$ of $J$, and its **suffixes** are $S^\pi_b=\{\pi(b),\dots,\pi(n)\}$ for $b\in[n]$, with $S^\pi_{n+1}=\emptyset$. A schedule **completes the jobs in the order $\pi$** if $C_{\pi(1)}\le C_{\pi(2)}\le\dots\le C_{\pi(n)}$.
--
--   For $p\in\mathbb R^n_{\ge0}$:
--
--   1. $\mathrm{OPT}(p)$ is the infimum of the weighted completion times of all feasible schedules for $p$;
--   2. $\mathrm{OPT}_\pi(p)$ is the infimum over the feasible schedules for $p$ that complete the jobs in the order $\pi$, with $\inf\emptyset=\infty$.
--
--   Given $\alpha\in\mathbb R^n_{\ge0}$ and, for every $U\subseteq J$, a rate vector $y^U\in\mathcal P_U$ with $\langle\alpha,y^U\rangle=H_\alpha(U)$, the **$\alpha$-greedy schedule** for $p$ uses at every time $t$ the rate vector $y^{U(t)}$, where $U(t)$ is its own set of unfinished jobs.
--
--   **Formalization Note** An order is `Equiv.Perm (Fin n)` sending positions to jobs, and positions are 0-based: `suffix π b` $=\{\pi(i) : b\le i\}$ for $b\in\{0,\dots,n\}$, so the paper's $S^\pi_b$ is `suffix π (b-1)` and `suffix π n` $=\emptyset$. $\mathrm{OPT}(p)$ is `opt0`, a real infimum of a nonempty set bounded below by $0$ (for positive weights); $\mathrm{OPT}_\pi(p)$ is `optOrder`, valued in `EReal` so that the empty infimum is $+\infty$. The greedy schedule is a predicate on a schedule and the chosen family $y^U$.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §5.1, p.25 (PDF p.27), S_n, suffixes, OPT(p), OPT_π(p); §5.2, pp.27–28 (PDF pp.29–30), α-greedy schedule

import Mathlib
import Definitions.Def_PolytopeSchedPF_Schedule

namespace PolytopeSchedPF

/-- The suffix `S^π_b = {π(b), …, π(n)}` of an order `π`
(Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.1, p.25), with `S^π_{n+1} = ∅`.

**Formalization Note** An order is `π : Equiv.Perm (Fin n)`, sending a position to a job, and
positions are 0-based (reading R14): `suffix π b = {π(i) | b ≤ i}` for `b ∈ {0, …, n}`, so the
paper's `S^π_b` is `suffix π (b − 1)` and `S^π_{n+1} = suffix π n = ∅`. -/
def suffix {n : ℕ} (π : Equiv.Perm (Fin n)) (b : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => b ≤ i.val)).image π

/-- A schedule **completes the jobs in the order** `π` if `C_{π(1)} ≤ C_{π(2)} ≤ ⋯ ≤ C_{π(n)}`
(§5.1, p.25). -/
def CompletesInOrder {n : ℕ} (p r : Fin n → ℝ) (y : ℝ → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    Prop :=
  ∀ a b : Fin n, a ≤ b → completionTime p r y (π a) ≤ completionTime p r y (π b)

/-- `OPT(p)` of §5 (p.25): the infimum of the weighted completion times of all feasible schedules
for `p`, all jobs released at time `0`. Called `OPT₀` in the proof of Theorem 1.3 (p.29).

**Formalization Note** A real `sInf` (reading R13). Under the instance's hypotheses (`w > 0`) the
set is nonempty (a sequential schedule is feasible) and bounded below by `0`. -/
noncomputable def opt0 {n D : ℕ} (P : RatePolytope n D) (w p : Fin n → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ y, IsFeasible P p 0 y ∧ v = weightedCompletion w p 0 y}

/-- `OPT_π(p)` (p.25): the infimum of the weighted completion times of the feasible schedules for
`p` (release dates `0`) that complete the jobs in the order `π`, with `inf ∅ = ∞`.

**Formalization Note** Valued in `EReal`, so the infimum of the empty family is `⊤` (reading R13). -/
noncomputable def optOrder {n D : ℕ} (P : RatePolytope n D) (w p : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : EReal :=
  ⨅ (y : ℝ → Fin n → ℝ) (_ : IsFeasible P p 0 y ∧ CompletesInOrder p 0 y π),
    ((weightedCompletion w p 0 y : ℝ) : EReal)

/-- The **α-greedy schedule** (§5.2, pp.27–28): given for every `U ⊆ J` a rate vector
`y^U ∈ P_U` with `⟨α, y^U⟩ = H_α(U)`, the α-greedy schedule for `p` uses at every time `t ≥ 0` the
rate vector `y^{U(t)}`, where `U(t)` is its own set of unfinished jobs (release dates `0`).

**Formalization Note** A predicate on the schedule and the chosen family `yU` (reading R12); the
maximizing property of the family is a hypothesis of the theorems that use it. -/
def IsGreedySchedule {n : ℕ} (p : Fin n → ℝ) (yU : Finset (Fin n) → Fin n → ℝ)
    (y : ℝ → Fin n → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → y t = yU (unfinished p 0 y t)

end PolytopeSchedPF


