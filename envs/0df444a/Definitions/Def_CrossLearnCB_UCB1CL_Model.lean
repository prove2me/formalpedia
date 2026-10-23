-- Prove2me | Definitions.Def_CrossLearnCB_UCB1CL_Model
-- name    : CrossLearnCB_UCB1CL_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:38.633809+00:00
-- url     : https://prove2.me/theorems/009bd9d3-79d2-4286-8cb3-14472b447a1c
-- title:
--   §2.2–2.3, Definition 1, Algorithm 1, pp. 9–18 — stochastic rewards, CL graphs, clique covering number, UCB1.CL statistics and selection rule, pseudo-regret, Reg_Pre (1), Reg_Post (2)
-- statement:
--   This file fixes the model of contextual bandits with cross-learning of Balseiro, Golrezaei, Mahdian, Mirrokni and Schneider, the UCB1.CL algorithm, and the quantities used in the analysis of its regret.
--
--   **Rewards.** There are $K$ arms $i\in[K]$ and $C$ contexts $c\in[C]$. On a probability space $(\Omega,\mathbb P)$, the reward of arm $i$ in context $c$ at round $t$ is a random variable $r_{i,t}(c)\in[0,1]$. The reward vectors $(r_{i,t}(c))_{i,c}$ of different rounds are mutually independent (rewards may be arbitrarily correlated within a round), and for each pair $(i,c)$ the rewards $r_{i,t}(c)$ have one and the same law $\mathcal F_i(c)$ in every round. We write
--   $$\mu_i(c)=\mathbb E[r_{i,t}(c)],\qquad \mu^\star(c)=\max_{i\in[K]}\mu_i(c),\qquad \Delta_i(c)=\mu^\star(c)-\mu_i(c)\ \ (\text{the gap}).$$
--
--   **Cross-learning graphs.** For every arm $i$ there is a directed graph $G_i$ on the contexts; an edge $c\to c'$ means that pulling arm $i$ in context $c$ also reveals the reward $r_{i,t}(c')$ of arm $i$ in context $c'$, i.e. $c'\in\mathcal O_i(c)$. Every $G_i$ contains all self-loops $c\to c$.
--
--   **Clique covering number (Definition 1).** For a directed graph $H$ on $[C]$, $\kappa(H)$ is the least $r$ for which the contexts can be partitioned into $r$ subcliques, a subclique being a set $S$ with an edge $u\to v$ for every $u,v\in S$.
--
--   **UCB1.CL (Algorithm 1).** Along a context sequence $c_1,c_2,\dots$, an arm sequence $I_1,I_2,\dots$ and a reward realisation, let $\tau_{i,t}(c)$ be the number of rounds $t'<t$ with $I_{t'}=i$ and $c\in\mathcal O_i(c_{t'})$ (observations of arm $i$ in context $c$ before round $t$), and $\sigma_{i,t}(c)$ the sum of the rewards $r_{i,t'}(c)$ observed in those rounds. With $\omega(s)=\sqrt{2\log T/s}$ and $\omega(0)=+\infty$, the index of arm $j$ in round $t$ is
--   $$U_{j,t}=\frac{\sigma_{j,t}(c_t)}{\tau_{j,t}(c_t)}+\omega\big(\tau_{j,t}(c_t)\big),$$
--   equal to $+\infty$ when $\tau_{j,t}(c_t)=0$. An arm sequence follows UCB1.CL if in every round $t\le T$ the pulled arm $I_t$ maximises $U_{j,t}$ over $j$ (ties broken arbitrarily). A UCB1.CL process is a random arm sequence that follows UCB1.CL along every outcome and whose arm in round $t$ is a measurable function of the rewards of the earlier rounds.
--
--   **Regret and the proof quantities.** The pseudo-regret is $\mathrm{Reg}=\sum_{t=1}^T\Delta_{I_t}(c_t)$. With $m_i(c)=8\log T/\Delta_i(c)^2$ and a threshold $\Delta_{\min}$,
--   $$\mathrm{Reg}_{\mathrm{Pre}}=\sum_{t=1}^T\Delta_{I_t}(c_t)\,\mathbb I\big(\Delta_{I_t}(c_t)\ge\Delta_{\min},\ \tau_{I_t,t}(c_t)\le m_{I_t}(c_t)\big),$$
--   and $\mathrm{Reg}_{\mathrm{Post}}$ is the same sum with $\tau_{I_t,t}(c_t)>m_{I_t}(c_t)$. For a set $S$ of contexts, $\tilde\tau_{i,t}(S)$ counts the pulls of arm $i$ in contexts of $S$ before round $t$, and $X_i(c)$ counts the rounds $t\le T$ with $c_t=c$, $I_t=i$ and $\tilde\tau_{i,t}(S)\le m_i(c)$. Finally $\bar x_{i,n}(c)$ is the average of the first $n$ observed rewards of arm $i$ in context $c$.
--
--   These objects are shared by every statement of the mission: the main theorem bounds the expected pseudo-regret of a UCB1.CL process, and the milestones bound $\mathrm{Reg}_{\mathrm{Pre}}$, $\mathrm{Reg}_{\mathrm{Post}}$ and the deviations of $\bar x_{i,n}(c)$.
--
--   **Formalization Note.** Arms and contexts are `Fin K` and `Fin C`; rounds are 0-based naturals, so Lean's round $t$ is the paper's round $t+1$, and all statistics used in round $t$ count rounds $s<t$. The reward process `R t ω i c` is defined for every $t\in\mathbb N$; only $t<T$ matters. The context sequence is a deterministic (oblivious) sequence. `G i c c'` is the edge $c\to c'$ of $G_i$. The index is an `EReal`, `⊤` when $\tau=0$ (so the paper's convention $\bar r=0$ at $\tau=0$ is never used). $\kappa$ is the least $r$ admitting a labelling $f:[C]\to[r]$ whose classes are subcliques. The regret is the pseudo-regret of p. 17, summed over all $T$ rounds; its expectation equals that of the realised regret of p. 9 because $I_t$ does not depend on round $t$'s rewards. The condition $\Delta_i(c)\ge\Delta_{\min}$ that p. 17 suppresses is explicit in $\mathrm{Reg}_{\mathrm{Pre}}$ and $\mathrm{Reg}_{\mathrm{Post}}$. The 0-based round of the $n$-th observation is the least $t$ with $\tau_{t+1}\ge n$ (it is $0$ if fewer than $n$ observations ever occur, where $\bar x_{i,n}$ is then not the paper's object). The measurability of the arm process with respect to the past rewards is added so that expectations are meaningful and tie-breaking cannot look ahead. Lean's $8\log T/0=0$; every statement using $m_i(c)$ restricts to positive gaps.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, pp. 9–18, §2.2 (p. 9), §2.3 (pp. 11–12), Definition 1 (p. 13), Algorithm 1 (p. 15), Reg(A) (p. 17), m_i(c), (1), (2), X_i(c) (p. 18), x̄_{i,n}(c) (p. 45)

import Mathlib

namespace CrossLearnCB.UCB1CL

open MeasureTheory ProbabilityTheory

/-! ### Stochastic rewards (§2.2, p. 9; footnote 3)

`R t ω i c` is the reward `r_{i,t}(c)` of arm `i : Fin K` in context `c : Fin C` at 0-based
round `t` (the paper's round `t + 1`). -/

/-- The standing stochastic-reward model: measurable round vectors, independent across rounds
(arbitrary correlation inside a round), rewards in `[0, 1]`, and a fixed law `F_i(c)` of each
coordinate across rounds. -/
structure IsStochRewards {K C : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℕ → Ω → Fin K → Fin C → ℝ) : Prop where
  measurable : ∀ t, Measurable (R t)
  indep : iIndepFun (fun t => R t) P
  mem_Icc : ∀ t ω i c, R t ω i c ∈ Set.Icc (0 : ℝ) 1
  identDistrib : ∀ t i c, IdentDistrib (fun ω => R t ω i c) (fun ω => R 0 ω i c) P P

/-- Mean reward `μ_i(c)`, the mean of the law `F_i(c)`. -/
noncomputable def mu {K C : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℕ → Ω → Fin K → Fin C → ℝ) (i : Fin K) (c : Fin C) : ℝ :=
  ∫ ω, R 0 ω i c ∂P

/-- Best mean reward `μ⋆(c) = max_i μ_i(c)`. -/
noncomputable def muStar {K C : ℕ} [NeZero K] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℕ → Ω → Fin K → Fin C → ℝ) (c : Fin C) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => mu P R i c)

/-- Gap `Δ_i(c) = μ⋆(c) - μ_i(c)`. -/
noncomputable def gap {K C : ℕ} [NeZero K] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℕ → Ω → Fin K → Fin C → ℝ) (i : Fin K) (c : Fin C) : ℝ :=
  muStar P R c - mu P R i c

/-! ### Cross-learning graphs (§2.3, pp. 11–12) and Definition 1 (p. 13)

`G i c c'` is the edge `c → c'` of the CL graph `G_i`: playing arm `i` in context `c` reveals
the reward of arm `i` in context `c'`, i.e. `c' ∈ O_i(c)`. -/

/-- Every CL graph contains all self-loops `c → c`. -/
def HasSelfLoops {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) : Prop :=
  ∀ i c, G i c c

/-- Clique covering number `κ(H)` (Definition 1): the least `r` such that the vertices can be
labelled by `Fin r` with any two vertices of the same label joined by an edge `u → v`
(a partition into at most `r` subcliques). -/
noncomputable def cliqueCoverNumber {C : ℕ} (H : Fin C → Fin C → Prop) : ℕ :=
  sInf {r : ℕ | ∃ f : Fin C → Fin r, ∀ u v, f u = f v → H u v}

/-! ### UCB1.CL statistics along a realisation (Algorithm 1, p. 15)

`I : ℕ → Fin K` is an arm sequence, `ctx : ℕ → Fin C` the context sequence and
`r : ℕ → Fin K → Fin C → ℝ` a reward realisation. -/

open Classical in
/-- `τ`: the number of rounds `s < t` in which the reward of arm `i` in context `c` was
observed, i.e. `I s = i` and `c ∈ O_i(ctx s)`. At 0-based round `t` this is the paper's
`τ_{i,t-1}(c)` used to choose the arm. -/
noncomputable def obsCount {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (I : ℕ → Fin K) (t : ℕ) (i : Fin K) (c : Fin C) : ℕ :=
  ((Finset.range t).filter (fun s => I s = i ∧ G i (ctx s) c)).card

open Classical in
/-- `σ`: the total reward of arm `i` in context `c` observed in rounds `s < t`. -/
noncomputable def obsSum {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (I : ℕ → Fin K) (r : ℕ → Fin K → Fin C → ℝ) (t : ℕ) (i : Fin K) (c : Fin C) : ℝ :=
  ∑ s ∈ (Finset.range t).filter (fun s => I s = i ∧ G i (ctx s) c), r s i c

/-- The UCB1.CL index of arm `j` at 0-based round `t`, in the current context `ctx t`:
`r̄ + ω(τ)` with `ω(s) = √(2 log T / s)`, and `+∞` (`⊤`) when `τ = 0`. -/
noncomputable def ucbIndex {K C : ℕ} (T : ℕ) (G : Fin K → Fin C → Fin C → Prop)
    (ctx : ℕ → Fin C) (I : ℕ → Fin K) (r : ℕ → Fin K → Fin C → ℝ) (t : ℕ) (j : Fin K) :
    EReal :=
  if obsCount G ctx I t j (ctx t) = 0 then ⊤
  else ((obsSum G ctx I r t j (ctx t) / (obsCount G ctx I t j (ctx t) : ℝ)
      + Real.sqrt (2 * Real.log T / (obsCount G ctx I t j (ctx t) : ℝ)) : ℝ) : EReal)

/-- The UCB1.CL selection rule: in every round `t < T` the arm pulled maximises the index
(ties broken arbitrarily). -/
def IsUCB1CL {K C : ℕ} (T : ℕ) (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (r : ℕ → Fin K → Fin C → ℝ) (I : ℕ → Fin K) : Prop :=
  ∀ t < T, ∀ j, ucbIndex T G ctx I r t j ≤ ucbIndex T G ctx I r t (I t)

/-- An arm process run by UCB1.CL on the stochastic rewards `R`: along every outcome `ω` the arm
sequence satisfies the selection rule, and the arm of round `t` is a measurable function of the
rewards of rounds `s < t` (the algorithm does not look ahead, also when it breaks ties). -/
structure IsUCB1CLProcess {K C : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (R : ℕ → Ω → Fin K → Fin C → ℝ) (T : ℕ) (G : Fin K → Fin C → Fin C → Prop)
    (ctx : ℕ → Fin C) (I : ℕ → Ω → Fin K) : Prop where
  selects : ∀ ω, IsUCB1CL T G ctx (fun s => R s ω) (fun s => I s ω)
  adapted : ∀ t, Measurable[MeasurableSpace.comap (fun ω (s : Fin t) => R s ω) inferInstance]
    (I t)

/-! ### Regret and the proof objects (pp. 17–19, p. 45) -/

/-- Pseudo-regret `Reg(A) = Σ_{t} Δ_{I_t}(c_t)` over the `T` rounds. -/
def pseudoRegret {K C : ℕ} (gap : Fin K → Fin C → ℝ) (ctx : ℕ → Fin C) (I : ℕ → Fin K)
    (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, gap (I t) (ctx t)

/-- `m_i(c) = 8 log T / Δ_i(c)²`, as a function of the gap `Δ`. -/
noncomputable def mThr (T : ℕ) (Δ : ℝ) : ℝ :=
  8 * Real.log T / Δ ^ 2

open Classical in
/-- Pre-regret (1), with the condition `Δ_i(c) ≥ Δ_min` made explicit. -/
noncomputable def regPre {K C : ℕ} (gap : Fin K → Fin C → ℝ) (G : Fin K → Fin C → Fin C → Prop)
    (ctx : ℕ → Fin C) (I : ℕ → Fin K) (T : ℕ) (Δmin : ℝ) : ℝ :=
  ∑ t ∈ Finset.range T,
    if Δmin ≤ gap (I t) (ctx t) ∧
        (obsCount G ctx I t (I t) (ctx t) : ℝ) ≤ mThr T (gap (I t) (ctx t))
    then gap (I t) (ctx t) else 0

open Classical in
/-- Post-regret (2), with the condition `Δ_i(c) ≥ Δ_min` made explicit. -/
noncomputable def regPost {K C : ℕ} (gap : Fin K → Fin C → ℝ) (G : Fin K → Fin C → Fin C → Prop)
    (ctx : ℕ → Fin C) (I : ℕ → Fin K) (T : ℕ) (Δmin : ℝ) : ℝ :=
  ∑ t ∈ Finset.range T,
    if Δmin ≤ gap (I t) (ctx t) ∧
        mThr T (gap (I t) (ctx t)) < (obsCount G ctx I t (I t) (ctx t) : ℝ)
    then gap (I t) (ctx t) else 0

open Classical in
/-- `τ̃`: the number of pulls of arm `i` in a context of `S` during rounds `s < t`. -/
noncomputable def pullsIn {K C : ℕ} (ctx : ℕ → Fin C) (I : ℕ → Fin K) (t : ℕ) (i : Fin K)
    (S : Finset (Fin C)) : ℕ :=
  ((Finset.range t).filter (fun s => I s = i ∧ ctx s ∈ S)).card

open Classical in
/-- `X_i(c)` (p. 18) for the clique `S ∋ c`: the number of rounds `t < T` with `c_t = c`,
`I_t = i` and `τ̃_{i,t}(S) ≤ m_i(c)`. -/
noncomputable def cliqueX {K C : ℕ} (gap : Fin K → Fin C → ℝ) (ctx : ℕ → Fin C)
    (I : ℕ → Fin K) (T : ℕ) (i : Fin K) (S : Finset (Fin C)) (c : Fin C) : ℕ :=
  ((Finset.range T).filter (fun t => ctx t = c ∧ I t = i ∧
    (pullsIn ctx I t i S : ℝ) ≤ mThr T (gap i c))).card

/-- The 0-based round of the `n`-th observation of arm `i` in context `c`: the least `t` with
`obsCount (t + 1) ≥ n` (it is `0` if there are fewer than `n` observations ever). -/
noncomputable def obsTime {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (I : ℕ → Fin K) (i : Fin K) (c : Fin C) (n : ℕ) : ℕ :=
  sInf {t : ℕ | n ≤ obsCount G ctx I (t + 1) i c}

/-- `x̄_{i,n}(c)` (p. 45): the average of the first `n` observed rewards of arm `i` in context
`c`. Meaningful when at least `n ≥ 1` observations occur. -/
noncomputable def firstNMean {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (I : ℕ → Fin K) (r : ℕ → Fin K → Fin C → ℝ) (i : Fin K) (c : Fin C) (n : ℕ) : ℝ :=
  obsSum G ctx I r (obsTime G ctx I i c n + 1) i c / n

end CrossLearnCB.UCB1CL


