-- Prove2me | Definitions.Def_GoTBandit_Main_Algorithm
-- name    : GoTBandit_Main_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:33.324605+00:00
-- url     : https://prove2.me/theorems/734852b9-4016-4ce6-86cf-325b50b00f45
-- title:
--   Definitions II.1–II.2, Algorithm 1, pp. 3–6 — i.i.d. rewards, private seeds, the Game of Thrones algorithm, its trajectory and the total regret (3)
-- statement:
--   This file defines the stochastic model of the paper and the Game of Thrones algorithm run by every player.
--
--   **Rewards (Definition II.1).** On a probability space $(\Omega,\mathbb P)$, $r_{n,i}(t)$ is the reward of arm $i$ for player $n$ at turn $t$. For each $(n,i)$ the rewards are identically distributed with a continuous (atomless) law, mean $\mu_{n,i}>0$ and variance $\sigma_{n,i}^2$, and satisfy Bernstein's condition with a parameter $b_{n,i}>0$:
--
--   $$
--   \mathbb E\{|r_{n,i}(t)-\mu_{n,i}|^k\}\le\tfrac12k!\,\sigma_{n,i}^2b_{n,i}^{k-2}\quad\text{for all integers } k\ge3.
--   $$
--
--   **Private randomization.** Player $n$ randomizes with her own seeds $\xi_{n,t,j}$, $j=0,\dots,3$, uniform on $[0,1]$. All rewards and all seeds are jointly independent.
--
--   **Algorithm 1.** The parameters $c_1,c_2,c_3,\delta,\varepsilon,c$ are known to every player, and so is the epoch schedule. Each player keeps, per arm, the number $V_{n,i}$ of collision-free exploration visits and the sum $s_{n,i}$ of their rewards, her baseline action and mood, the content counts $F^n_k(i)$ of Eq. (14), and the last action of every GoT phase. In epoch $k$:
--
--   1. *Exploration* ($\lceil c_1k^\delta\rceil$ turns): play a uniform arm $i$; if the received reward is nonzero, add one visit and the reward to $V_{n,i}$, $s_{n,i}$. The estimate is $\mu^k_{n,i}=s_{n,i}/V_{n,i}$.
--   2. *GoT* ($\lceil c_2k^\delta\rceil$ turns): at the start set $S_n=C$ and $\bar a_n$ to the last action of GoT phase $k-\lfloor k/2\rfloor-1$, or a uniform arm if $k=1,2$. Then play the GoT dynamics (5)–(8) with utility $u_n=\mu^k_{n,a_n}$ if the received reward is nonzero and $u_n=0$ otherwise, and $u_{n,\max}=\max_i\mu^k_{n,i}$; count in $F^n_k(i)$ the turns where $i$ was played and the player ended the turn content.
--   3. *Exploitation* ($c_32^k$ turns): play $a^k_n=\arg\max_i\sum_{r=0}^{\lfloor k/2\rfloor}F^n_{k-r}(i)$.
--
--   A player's action and memory update use only her own memory, her own seeds and her own received reward $r_{n,a_n}(t)\eta_{a_n}(a(t))$; she never sees the means, the horizon, or the other players' actions. Running all players together gives the random profile $a(t)$ at every turn and the estimates $\mu^k_{n,i}$ after each exploration phase.
--
--   **Regret (Definition II.2).** For an optimal profile $a^*$ and horizon $T$, the total regret is the random variable
--
--   $$
--   R=\sum_{t=1}^T\sum_{n=1}^N r_{n,a^*_n}(t)\,\eta_{a^*_n}(a^*)-\sum_{t=1}^T\sum_{n=1}^N r_{n,a_n(t)}(t)\,\eta_{a_n(t)}(a(t)),
--   $$
--
--   and the expected total regret is $\bar R=\mathbb E\{R\}$.
--
--   **Formalization Note** Turns are indexed from $0$ (Lean's turn $t$ is the paper's turn $t+1$); epochs from $1$. "Continuous distribution" is formalized as atomless law, and the i.i.d./independence assumptions of Definition II.1 as one joint independence of all rewards and seeds. The players' randomization is realized by private i.i.d. uniform seeds independent of the rewards, each random choice having exactly the law Algorithm 1 prescribes (an arm $\lfloor M\xi\rfloor$ clamped to $M-1$; a content player deviates iff $\xi<\varepsilon^c$, then to a uniform other arm; she becomes content iff $\xi'$ is below the probability of Eq. (8)). Junk value: $\mu^k_{n,i}=0$ when $V_{n,i}=0$. Ties in the argmax of (15) are broken toward the smallest arm index. The GoT starting baseline follows Algorithm 1 (last action of GoT phase $k-\lfloor k/2\rfloor-1$), not the "exploitation phase" of Lemma V.7. With $M=1$ a content player has no other arm and keeps her baseline. Every player starts with baseline arm $0$; this is overwritten by a random arm at the first GoT phase and never influences an action.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, pp. 2–6, Eq. (1), Definition II.1, Eq. (2), Definition II.2 Eqs. (3)–(4), §III, Algorithm 1 Eqs. (14)–(15)

import Mathlib
import Definitions.Def_GoTBandit_Main_Assignment
import Definitions.Def_GoTBandit_Main_GoTChain

open Finset MeasureTheory ProbabilityTheory

namespace GoTBandit.Main

noncomputable section

variable {N M : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Definition II.1. `r n i t` is the reward `r_{n,i}(t + 1)` of arm `i` for player `n` at
(0-based) turn `t`. Each sequence is identically distributed, with atomless (continuous)
law, mean `μ n i > 0`, variance `σ2 n i`, and the Bernstein moment condition with parameter
`b n i > 0`. Independence of all rewards is part of `Seeds`. -/
structure IIDRewards (P : Measure Ω) (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (μ σ2 b : Fin N → Fin M → ℝ) : Prop where
  meas : ∀ n i t, Measurable (r n i t)
  ident : ∀ n i t, IdentDistrib (r n i t) (r n i 0) P P
  continuous : ∀ n i (x : ℝ), P (r n i 0 ⁻¹' {x}) = 0
  memLp : ∀ n i, MemLp (r n i 0) 2 P
  mean : ∀ n i, μ n i = ∫ ω, r n i 0 ω ∂P
  mean_pos : ∀ n i, 0 < μ n i
  var : ∀ n i, variance (r n i 0) P = σ2 n i
  b_pos : ∀ n i, 0 < b n i
  bernstein : ∀ n i (k : ℕ), 3 ≤ k →
    Integrable (fun ω => |r n i 0 ω - μ n i| ^ k) P ∧
    ∫ ω, |r n i 0 ω - μ n i| ^ k ∂P ≤ (k.factorial : ℝ) / 2 * σ2 n i * b n i ^ (k - 2)

/-- The index set of all rewards `(n, i, t)` and all private seeds `(n, t, j)`. -/
abbrev RandIdx (N M : ℕ) := (Fin N × Fin M × ℕ) ⊕ (Fin N × ℕ × Fin 4)

/-- The players' private randomization: `ξ n t j` (`j = 0, …, 3`) are uniform on `[0, 1]`,
and all rewards and all seeds are jointly independent. -/
structure Seeds (P : Measure Ω) (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) : Prop where
  meas : ∀ n t j, Measurable (ξ n t j)
  uniform : ∀ n t j, P.map (ξ n t j) = volume.restrict (Set.Icc (0 : ℝ) 1)
  indep : iIndepFun (fun (x : RandIdx N M) (ω : Ω) =>
    match x with
    | Sum.inl (n, i, t) => r n i t ω
    | Sum.inr (n, t, j) => ξ n t j ω) P

/-- The parameters of Algorithm 1, chosen by the designer and known to every player. -/
structure GoTParams where
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  δ : ℝ
  ε : ℝ
  c : ℝ

namespace GoTParams

variable (p : GoTParams)

/-- Total length of epoch `k`. -/
def epochLen (k : ℕ) : ℕ :=
  expLen p.c1 p.δ k + gotLen p.c2 p.δ k + exploitLen p.c3 k

/-- The (0-based) first turn of epoch `k ≥ 1`. -/
def epochStart (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico 1 k, p.epochLen j

/-- The epoch `k ≥ 1` containing turn `t` (correct whenever every epoch is nonempty, e.g. when
`c1 ≥ 1` or `c3 ≥ 1`). -/
def epochOf (t : ℕ) : ℕ :=
  ((Finset.range (t + 2)).filter (fun k => 1 ≤ k ∧ p.epochStart k ≤ t)).sup id

end GoTParams

/-- The three phases of an epoch; `got o` is the `o`-th (0-based) turn of the GoT phase. -/
inductive Phase
  | explore
  | got (o : ℕ)
  | exploit

/-- The epoch of turn `t` and the phase of turn `t` within it. -/
def phaseOf (p : GoTParams) (t : ℕ) : ℕ × Phase :=
  let k := p.epochOf t
  let o := t - p.epochStart k
  (k, if o < expLen p.c1 p.δ k then Phase.explore
      else if o < expLen p.c1 p.δ k + gotLen p.c2 p.δ k then
        Phase.got (o - expLen p.c1 p.δ k)
      else Phase.exploit)

/-- The private memory of one player. -/
structure PlayerState (M : ℕ) where
  /-- `V_{n,i}`: number of collision-free exploration visits to arm `i`. -/
  V : Fin M → ℕ
  /-- `s_{n,i}`: sum of the rewards of these visits. -/
  s : Fin M → ℝ
  /-- Baseline action `ā_n`. -/
  base : Fin M
  /-- Mood `S_n`. -/
  mood : Mood
  /-- `F k i = F^n_k(i)` of Eq. (14). -/
  F : ℕ → Fin M → ℕ
  /-- `lastGoT k`: the last action played in the GoT phase of epoch `k`. -/
  lastGoT : ℕ → Fin M

/-- The estimate `μ^k_{n,i} = s_{n,i} / V_{n,i}` (junk value `0` when `V_{n,i} = 0`). -/
def PlayerState.estimate {M : ℕ} (st : PlayerState M) (i : Fin M) : ℝ :=
  st.s i / (st.V i : ℝ)

/-- The initial memory: no visits, empty sums and counters, baseline arm `a0`. -/
def initState {M : ℕ} (a0 : Fin M) : PlayerState M :=
  { V := fun _ => 0, s := fun _ => 0, base := a0, mood := Mood.C,
    F := fun _ _ => 0, lastGoT := fun _ => a0 }

/-- A uniformly random arm from a uniform seed `x ∈ [0, 1]`: arm `⌊M x⌋`, clamped to `M − 1`. -/
def unifArm {M : ℕ} (hM : 0 < M) (x : ℝ) : Fin M :=
  ⟨min ⌊(M : ℝ) * x⌋₊ (M - 1), by omega⟩

/-- A uniformly random arm different from `b` from a uniform seed `x` (requires `M ≥ 2`;
returns `b` when `M = 1`). -/
def otherArm {M : ℕ} (b : Fin M) (x : ℝ) : Fin M :=
  if h : 2 ≤ M then
    let j := min ⌊((M : ℝ) - 1) * x⌋₊ (M - 2)
    if j < b.val then ⟨j, by omega⟩ else ⟨j + 1, by omega⟩
  else b

/-- The first index maximizing `f` (ties broken toward the smallest index). -/
def argmaxFirst {M : ℕ} (f : Fin M → ℕ) (a0 : Fin M) : Fin M :=
  (univ.filter (fun i => ∀ j, f j ≤ f i)).min' (by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image univ f ⟨a0, mem_univ _⟩
    exact ⟨i, by simpa using hi⟩)

/-- The player's memory at the start of turn `t`, after the reset of Algorithm 1, step 2 at the
first GoT turn of epoch `k`: `S_n = C`, and `ā_n` is the last action of GoT phase
`k − ⌊k/2⌋ − 1`, or a random arm (seed `3`) if `k = 1, 2`. -/
def preState (p : GoTParams) (t : ℕ) (st : PlayerState M) (seed : Fin 4 → ℝ) :
    PlayerState M :=
  match phaseOf p t with
  | (k, Phase.got 0) =>
      { st with
        mood := Mood.C,
        base := if k ≤ 2 then unifArm st.base.pos (seed 3) else st.lastGoT (k - k / 2 - 1) }
  | _ => st

/-- The action of one player at turn `t`, from her own memory and her own seeds only.
Exploration: a uniform arm (seed `0`). GoT: Eq. (5) if content (deviate iff seed `1` is
`< ε^c`, then a uniform other arm by seed `0`), Eq. (6) if discontent (seed `0`).
Exploitation: Eq. (15). -/
def act (p : GoTParams) (t : ℕ) (st₀ : PlayerState M) (seed : Fin 4 → ℝ) : Fin M :=
  let st := preState p t st₀ seed
  match phaseOf p t with
  | (_, Phase.explore) => unifArm st.base.pos (seed 0)
  | (_, Phase.got _) =>
      match st.mood with
      | Mood.C => if seed 1 < p.ε ^ p.c then otherArm st.base (seed 0) else st.base
      | Mood.D => unifArm st.base.pos (seed 0)
  | (k, Phase.exploit) =>
      argmaxFirst (fun i => ∑ r ∈ Finset.range (k / 2 + 1), st.F (k - r) i) st.base

/-- The memory update of one player at turn `t`, from her own memory, her own seeds, her own
action `a` and her own received reward `obs = r_{n,a}(t) η_a(a(t))`. Exploration:
Algorithm 1, step 1(b)–(c) (a collision is read off `obs = 0`). GoT: step 2(b)–(c), with
utility `u_n = μ^k_{n,a}` if `obs ≠ 0` and `0` otherwise, and `u_{n,max} = max_i μ^k_{n,i}`;
the mood coin is seed `2`. -/
def update (p : GoTParams) (t : ℕ) (st₀ : PlayerState M) (seed : Fin 4 → ℝ) (a : Fin M)
    (obs : ℝ) : PlayerState M :=
  let st := preState p t st₀ seed
  match phaseOf p t with
  | (_, Phase.explore) =>
      if obs ≠ 0 then
        { st with V := Function.update st.V a (st.V a + 1),
                  s := Function.update st.s a (st.s a + obs) }
      else st
  | (k, Phase.got _) =>
      let u : ℝ := if obs ≠ 0 then st.estimate a else 0
      let umax : ℝ := ⨆ i, st.estimate i
      let m : Mood :=
        if st.base = a ∧ 0 < u ∧ st.mood = Mood.C then Mood.C
        else if seed 2 < u / umax * p.ε ^ (umax - u) then Mood.C else Mood.D
      { st with
        base := a,
        mood := m,
        F := Function.update st.F k
          (if m = Mood.C then Function.update (st.F k) a (st.F k a + 1) else st.F k),
        lastGoT := Function.update st.lastGoT k a }
  | (_, Phase.exploit) => st

/-- The seeds of player `n` at turn `t`. -/
def seedsAt (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (n : Fin N) (t : ℕ) (ω : Ω) : Fin 4 → ℝ :=
  fun j => ξ n t j ω

/-- The joint memory of all players at the start of turn `t` when every player runs
Algorithm 1 (`act`/`update` applied player by player). -/
def traj (p : GoTParams) (hNM : N ≤ M) (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) : ℕ → Ω → Fin N → PlayerState M
  | 0 => fun _ n => initState ⟨0, lt_of_lt_of_le n.pos hNM⟩
  | t + 1 => fun ω n =>
      let S := traj p hNM r ξ t ω
      let a : Fin N → Fin M := fun m => act p t (S m) (seedsAt ξ m t ω)
      update p t (S n) (seedsAt ξ n t ω) (a n) (r n (a n) t ω * noColl a (a n))

/-- The profile `a(t)` played at (0-based) turn `t`. -/
def play (p : GoTParams) (hNM : N ≤ M) (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin N → Fin M :=
  fun m => act p t (traj p hNM r ξ t ω m) (seedsAt ξ m t ω)

/-- `μ^k_{n,i}`: player `n`'s estimate of arm `i` after the exploration phase of epoch `k`. -/
def est (p : GoTParams) (hNM : N ≤ M) (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (k : ℕ) (n : Fin N) (i : Fin M) (ω : Ω) : ℝ :=
  (traj p hNM r ξ (p.epochStart k + expLen p.c1 p.δ k) ω n).estimate i

/-- `V_{n,i}` after the exploration phase of epoch `k`. -/
def visitCount (p : GoTParams) (hNM : N ≤ M) (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (k : ℕ) (n : Fin N) (i : Fin M) (ω : Ω) : ℕ :=
  (traj p hNM r ξ (p.epochStart k + expLen p.c1 p.δ k) ω n).V i

/-- The total regret (3) over the turns `0, …, T − 1`. -/
def regret (p : GoTParams) (hNM : N ≤ M) (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (aStar : Fin N → Fin M) (T : ℕ) (ω : Ω) : ℝ :=
  (∑ t ∈ Finset.range T, ∑ n, r n (aStar n) t ω * noColl aStar (aStar n)) -
    ∑ t ∈ Finset.range T, ∑ n,
      r n (play p hNM r ξ t ω n) t ω * noColl (play p hNM r ξ t ω) (play p hNM r ξ t ω n)

/-- The expected total regret `R̄ = E{R}`. -/
def expRegret (P : Measure Ω) (p : GoTParams) (hNM : N ≤ M)
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ)
    (aStar : Fin N → Fin M) (T : ℕ) : ℝ :=
  ∫ ω, regret p hNM r ξ aStar T ω ∂P

end

end GoTBandit.Main


