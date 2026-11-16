-- Prove2me | Definitions.Def_EliasGlobalClock_LowerBound_Supplement_algorithmTwo
-- name    : EliasGlobalClock_LowerBound_Supplement_algorithmTwo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:34:02.773225+00:00
-- url     : https://prove2.me/theorems/b318f7b0-b588-4d20-a90c-91ba602c0c14
-- title:
--   Algorithm 2 (unbounded contention resolution) against an adaptive adversary, and its counts Q, A, D
-- statement:
--   Fix $\varepsilon\in(0,1/e)$, $\delta=\varepsilon/100$, $m=\lceil 64\delta^{-2}\ln(1/\delta)\rceil$, $B=\lceil m/\delta\rceil$ and $c=1/e-6\delta$. Block $j\ge1$ consists of slots $t_j=(j-1)B,\dots,jB-1$; its target is $M=(1+\delta)^{\mathrm{Int}(j)}$, with $\mathrm{Int}$ derived from SmoothCode, and $p_k=(1+\delta)^{-k}$.
--
--   **Players and adversary.** There are $q_0$ initial players; between transmission $t-1$ and transmission $t$ the adversary delivers a finite batch of $a(t)$ new players. The batch may depend on the whole past and on private randomness, but not on the fresh choices of slot $t$ or later. Formally, on a probability space with a filtration $(\mathcal F_t)$, $a(t)$ is $\mathcal F_t$-measurable, and every possible player $u$ has in each slot $t$ a fresh uniform $[0,1]$ variable $U(u,t)$; these are mutually independent across players, independent of $\mathcal F_t$ and $\mathcal F_{t+1}$-measurable. A player told to transmit with probability $p$ transmits iff $U(u,t)<p$.
--
--   **Protocol.** A player waits silently until the first block boundary at or after its arrival and then joins as *stalled*. In the first $m$ slots of block $j$ every surviving participant transmits with probability $1/M$; the test succeeds if at least $(1/e-\delta)m$ of these slots have exactly one transmitter. On success every surviving participant becomes *active* and $p_{\mathrm{active}}\leftarrow 1/M$; on failure all states and the stored probability are kept. In the remaining $B-m$ slots only active players transmit, with probability $p_{\mathrm{active}}$. A slot with exactly one transmitter is a success and that player leaves immediately.
--
--   **Counts.** $Q(t)$ is the number of pending players at the beginning of slot $t$, $A(t)=\sum_{s=1}^t a(s)$, $D(t)$ the number of successful slots among $0,\dots,t-1$, and $N_j=Q(t_j)$. Also $q_n(p)=np(1-p)^{n-1}$, a target $(1+\delta)^k$ is *bad* relative to $N$ if $q_N(p_k)<1/e-3\delta$, $\beta_k(N)=\delta^5\min\{\sqrt{Np_k},(Np_k)^{-1/2}\}$, $\mathrm{prd}(k)=2^{|\mathrm{SmoothCode}(k)|}$, $k_j=\lceil\log_{1+\delta}N_j\rceil$, and a window starting at $t_j$ with $N_j\ge R$ has length $H=B\lceil 16\,\mathrm{prd}(k_j)/\delta\rceil$ and credited progress $D_i+\delta A_i$ over $[t_j,t_j+H)$.
--
--   This is the execution and the bookkeeping on which every result of §5 and Appendix C is stated. The definition contains no test guarantee, drift estimate or delivery property.
--
--   **Formalization Note** The possible players are labelled $\mathbb N\oplus(\mathbb N\times\mathbb N)$: initial player $i<q_0$, or the $k$-th member of the batch at boundary $t\ge1$. The execution is a deterministic recursion over slots of a state (departed set, active set, stored exponent, test-success count), evaluated pathwise.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed pp.1, 13–14, 29 / PDF pp.2, 14–15, 30: §1 (problem), §5 and §5.1 (protocol, Q, A, D, F_t), §5.2 (windows, prd), Appendix C.1 (Algorithm 2) and C.2 (q_n, bad targets, β_k); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_codes

open MeasureTheory ProbabilityTheory

namespace EliasGlobalClock.LowerBound.Supplement

/-! Algorithm 2 (unbounded contention resolution, §5.1 and Appendix C.1, printed pp.13–14,
29 / PDF pp.14–15, 30) against an adaptive arrival adversary, with its counts `Q, A, D`.

Model. Time slots are `0, 1, 2, …`. There are `q₀` initial players. Between transmission
`t−1` and transmission `t` (`t ≥ 1`) the adversary delivers a finite batch of `a t` new
players; this batch is charged to `A(t) − A(t−1)` and is present at the beginning of slot
`t`. Players are labelled `inl i` (initial, `i < q₀`) and `inr (t, k)` (`k`-th player of
the batch delivered at boundary `t ≥ 1`), so there are countably many possible players.

Randomness. On a probability space `(Ω, P)` with filtration `ℱ` (`ℱ t` is the complete
history immediately before the transmission choices of slot `t`), every possible player `u`
has a fresh uniform `[0,1]` variable `U u t` in every slot `t`; a player that the protocol
tells to transmit with probability `p` transmits iff `U u t < p`. The batch `a t` is
`ℱ t`-measurable (it may use the whole past and private adversarial randomness), the
variables `U · t` are `ℱ (t+1)`-measurable, mutually independent, uniform, and independent
of `ℱ t` (the adversary cannot see the current fresh choices or the future tape). -/

/-! ### Parameters -/

/-- `δ = ε/100`. -/
noncomputable def delta (ε : ℝ) : ℝ := ε / 100

/-- `m = ⌈64 δ^{−2} ln(1/δ)⌉`, the number of test slots per block. -/
noncomputable def testLength (ε : ℝ) : ℕ :=
  Nat.ceil (64 / delta ε ^ 2 * Real.log (1 / delta ε))

/-- `B = ⌈m/δ⌉`, the block length. -/
noncomputable def blockLength (ε : ℝ) : ℕ := Nat.ceil ((testLength ε : ℝ) / delta ε)

/-- `c = 1/e − 6δ`. -/
noncomputable def rateC (ε : ℝ) : ℝ := Real.exp (-1) - 6 * delta ε

/-- `t_j = (j−1)B`, the first slot of block `j ≥ 1`. -/
noncomputable def blockStart (ε : ℝ) (j : ℕ) : ℕ := (j - 1) * blockLength ε

/-- The target exponent of block `j`: `Int(j)` for the integer sequence of SmoothCode, so the
target population size is `(1+δ)^{Int(j)}`. -/
noncomputable def targetExp (j : ℕ) : ℕ := decode smoothCode j

/-- `p_k = (1+δ)^{−k}`, the transmission probability of target `(1+δ)^k`. -/
noncomputable def targetProb (ε : ℝ) (k : ℕ) : ℝ := ((1 + delta ε) ^ k)⁻¹

/-! ### Players and the adversary model -/

/-- Possible players: initial players and members of arrival batches. -/
abbrev Player := ℕ ⊕ (ℕ × ℕ)

/-- The boundary at which a player arrives (`0` for initial players). -/
def arrivalTime : Player → ℕ
  | Sum.inl _ => 0
  | Sum.inr (t, _) => t

/-- Whether the possible player `u` actually exists in the execution. -/
def PlayerExists (q₀ : ℕ) (a : ℕ → ℕ) : Player → Prop
  | Sum.inl i => i < q₀
  | Sum.inr (t, k) => 1 ≤ t ∧ k < a t

/-- The adversary model: `a` is predictable for `ℱ`, the fresh uniforms `U · t` are revealed
at `t+1`, are i.i.d. uniform on `[0,1]` across players, and are independent of `ℱ t`. -/
structure IsAdversaryModel {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (U : Player → ℕ → Ω → ℝ) (a : ℕ → Ω → ℕ) : Prop where
  isProbability : IsProbabilityMeasure P
  arrivals_measurable : ∀ t, Measurable[ℱ t] (a t)
  coins_measurable : ∀ u t, Measurable[ℱ (t + 1)] (U u t)
  coins_uniform : ∀ u t, P.map (U u t) = volume.restrict (Set.Icc (0 : ℝ) 1)
  coins_indep : ∀ t, iIndepFun (fun u => U u t) P
  coins_fresh : ∀ t, Indep (⨆ u, MeasurableSpace.comap (U u t) inferInstance) (ℱ t) P

/-! ### The execution of Algorithm 2 -/

/-- State at the beginning of a slot: departed players, players that are active (they took
part in a successful test), the common stored exponent `k` of `p_active = p_k` (if any test
has succeeded), and the number of successful slots so far in the current block's test. -/
structure ExecState where
  departed : Set Player
  active : Set Player
  storedExp : Option ℕ
  testWins : ℕ

/-- Present at the beginning of slot `t`: exists, has arrived (`arrivalTime ≤ t`), has not
departed. -/
def Present (q₀ : ℕ) (a : ℕ → ℕ) (st : ExecState) (t : ℕ) (u : Player) : Prop :=
  PlayerExists q₀ a u ∧ arrivalTime u ≤ t ∧ u ∉ st.departed

/-- A player takes part in the block containing slot `t` iff it arrived at or before the
block's first slot; later arrivals wait silently until the next block boundary. -/
noncomputable def Joined (ε : ℝ) (t : ℕ) (u : Player) : Prop :=
  arrivalTime u ≤ t / blockLength ε * blockLength ε

/-- The transmitters in slot `t`. In the first `m` slots of block `j = ⌊t/B⌋ + 1` every
participating player transmits with probability `1/M`, `M = (1+δ)^{Int(j)}`; in the remaining
`B − m` slots only active players transmit, with the stored probability `p_active`. -/
noncomputable def transmitters (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (coin : Player → ℝ)
    (st : ExecState) (t : ℕ) : Set Player :=
  {u | Present q₀ a st t u ∧ Joined ε t u ∧
    ((t % blockLength ε < testLength ε ∧
        coin u < targetProb ε (targetExp (t / blockLength ε + 1))) ∨
      (testLength ε ≤ t % blockLength ε ∧ u ∈ st.active ∧
        ∃ k, st.storedExp = some k ∧ coin u < targetProb ε k))}

open Classical in
/-- One slot of Algorithm 2. A singleton transmitter succeeds and departs immediately. At the
end of the test (slot `m−1` of the block), if at least `(1/e − δ)m` test slots succeeded,
every surviving participant becomes active and `p_active ← p_test`; otherwise every state and
stored probability is kept. -/
noncomputable def step (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (coin : Player → ℝ)
    (st : ExecState) (t : ℕ) : ExecState :=
  let T := transmitters ε q₀ a coin st t
  let departed' := st.departed ∪ {u | T = {u}}
  let wins := (if t % blockLength ε = 0 then 0 else st.testWins) +
    (if t % blockLength ε < testLength ε ∧ ∃ u, T = {u} then 1 else 0)
  if t % blockLength ε + 1 = testLength ε ∧
      (Real.exp (-1) - delta ε) * testLength ε ≤ (wins : ℝ) then
    { departed := departed'
      active := st.active ∪ {u | PlayerExists q₀ a u ∧ Joined ε t u ∧ u ∉ departed'}
      storedExp := some (targetExp (t / blockLength ε + 1))
      testWins := wins }
  else
    { departed := departed', active := st.active, storedExp := st.storedExp, testWins := wins }

/-- The state at the beginning of every slot, for one realization of arrivals `a t ω` and
uniforms `U u t ω`. -/
noncomputable def execState (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ) :
    ℕ → ExecState
  | 0 => { departed := ∅, active := ∅, storedExp := none, testWins := 0 }
  | t + 1 => step ε q₀ a (fun u => U u t) (execState ε q₀ a U t) t

/-! ### Counts along one realization (`a`, `U` already evaluated at `ω`) -/

/-- Player `u` succeeds in slot `t` (it is the unique transmitter). -/
def SucceedsAt (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ) (u : Player) (t : ℕ) :
    Prop :=
  transmitters ε q₀ a (fun v => U v t) (execState ε q₀ a U t) t = {u}

/-- Slot `t` is successful: exactly one player transmits. -/
def SlotSuccess (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ) (t : ℕ) : Prop :=
  ∃ u, SucceedsAt ε q₀ a U u t

open Classical in
/-- `D(t)`: successes during slots `0, …, t−1`. -/
noncomputable def departures (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun s => SlotSuccess ε q₀ a U s)).card

/-- `A(t)`: arrivals charged to slots `0, …, t−1`, i.e. the batches at boundaries `1, …, t`. -/
def arrivals (a : ℕ → ℕ) (t : ℕ) : ℕ := ∑ s ∈ Finset.Icc 1 t, a s

/-- `Q(t)`: the number of pending players at the beginning of slot `t` (a finite set). -/
noncomputable def population (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ) (t : ℕ) : ℕ :=
  Set.ncard {u | Present q₀ a (execState ε q₀ a U t) t u}

/-- The number of players taking part in slot `t` of its block's test (surviving players that
were present at the block boundary). -/
noncomputable def participants (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ) (t : ℕ) :
    ℕ :=
  Set.ncard {u | Present q₀ a (execState ε q₀ a U t) t u ∧ Joined ε t u}

open Classical in
/-- The number of successful slots among the `m` test slots of block `j`. -/
noncomputable def testWinsOf (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ) (j : ℕ) : ℕ :=
  ((Finset.Ico (blockStart ε j) (blockStart ε j + testLength ε)).filter
    (fun s => SlotSuccess ε q₀ a U s)).card

/-- The test of block `j` succeeds: at least `(1/e − δ)m` of its slots are successful. -/
noncomputable def TestSucceeds (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ) (j : ℕ) :
    Prop :=
  (Real.exp (-1) - delta ε) * testLength ε ≤ testWinsOf ε q₀ a U j

/-! ### Analysis quantities (§5.2, Appendix C.2) -/

/-- `q_n(p) = n p (1−p)^{n−1}`, the probability of exactly one transmission among `n`
independent transmitters with probability `p` (`q₁(p) = p`). -/
noncomputable def singletonProb (n : ℕ) (p : ℝ) : ℝ := n * p * (1 - p) ^ (n - 1)

/-- `β_k(N) = δ⁵ min{√(N p_k), (N p_k)^{−1/2}}`. -/
noncomputable def betaBound (ε : ℝ) (k N : ℕ) : ℝ :=
  delta ε ^ 5 * min (Real.sqrt (N * targetProb ε k)) (1 / Real.sqrt (N * targetProb ε k))

/-- Target `(1+δ)^k` is bad relative to the reference population `N`: `q_N(p_k) < 1/e − 3δ`. -/
noncomputable def IsBadTarget (ε : ℝ) (N k : ℕ) : Prop :=
  singletonProb N (targetProb ε k) < Real.exp (-1) - 3 * delta ε

/-- `k = ⌈log_{1+δ} N⌉`. -/
noncomputable def ceilExp (ε : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (Real.log N / Real.log (1 + delta ε))

/-- `prd(k) = 2^{|SmoothCode(k)|}`, the period in blocks with which target `(1+δ)^k` is
tested. -/
def period (k : ℕ) : ℕ := 2 ^ (smoothCodeNat k).length

/-- `H = B ⌈16 prd(k)/δ⌉` with `k = ⌈log_{1+δ} N⌉`: the length of a window starting at a block
boundary with population `N ≥ R`. -/
noncomputable def windowLength (ε : ℝ) (N : ℕ) : ℕ :=
  blockLength ε * Nat.ceil (16 * (period (ceilExp ε N) : ℝ) / delta ε)

/-- Credited progress `D_i + δA_i` over the window `[t, t + H)` starting at slot `t`. -/
noncomputable def windowProgress (ε : ℝ) (q₀ : ℕ) (a : ℕ → ℕ) (U : Player → ℕ → ℝ)
    (t H : ℕ) : ℝ :=
  ((departures ε q₀ a U (t + H) - departures ε q₀ a U t : ℕ) : ℝ) +
    delta ε * ((arrivals a (t + H) - arrivals a t : ℕ) : ℝ)

end EliasGlobalClock.LowerBound.Supplement


