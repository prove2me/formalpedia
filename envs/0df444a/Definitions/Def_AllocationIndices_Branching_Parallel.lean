-- Prove2me | Definitions.Def_AllocationIndices_Branching_Parallel
-- name    : AllocationIndices_Branching_Parallel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:39.736188+00:00
-- url     : https://prove2.me/theorems/c14148c1-4762-4518-bfc8-0b5826ae6852
-- title:
--   The SFABP on M parallel machines: policies, performance, Aᵖ(S, k), A(S, k), ψ_i and E[a^{T_k^{S_i}/(M−ψ_i)}] (§5.7)
-- statement:
--   The objects of §5.7, the simple family of alternative bandit processes (SFABP) of §5.3 operated on $M$ identical machines working in parallel, in discrete time with discount factor $a \in (0, 1)$.
--
--   **Arms and job types.** There are $n$ arms $b = 1, \dots, n$. Arm $b$ has a finite state space $E_b$; the state spaces are disjoint, and their union $E$ is the set of **job types**. One Markov kernel $P$ on $E$ describes all arms: when arm $b$ is in state $i \in E_b$ and is processed, it moves to state $j$ with probability $P(i, j)$. The family is an **arm family** when every $E_b$ is closed under $P$ (a processed arm stays in its own state space) and $P$ is irreducible on every $E_b$ (from each $i \in E_b$ every $j \in E_b$ is reached with positive probability) — the standing assumption of p. 139. The matrix $A = (A_i^S)$, $S \subseteq E$, $i \in E$, is the matrix (5.3) of §5.3, $A_i^S = E[1 + a + \cdots + a^{T_i^S - 1}]$ for $i \in S$, with $T_i^S \ge 1$ the number of transitions the chain started at $i$ needs to return to $S$, and $A_i^S = 0$ for $i \notin S$ (the published `conservationCoeff`); $A_i^E = 1$.
--
--   **Policies and performance.** At each decision time $t = 0, 1, 2, \dots$ a **policy** $\pi$ chooses, possibly at random and on the basis of the past state-vectors, the past choices and the current state-vector, a set of exactly $M$ distinct arms, one for each machine. Each chosen arm makes one transition according to $P$, independently of the others; the other arms are frozen. From the initial state-vector $k = (k_1, \dots, k_n)$, $k_b \in E_b$, let $I_i(t)$ be the number of machines that process an arm in state $i$ at time $t$. The **performance** and the **return** are
--   $$x_i^\pi(k) = E_\pi\Big[\sum_{t \ge 0} a^t I_i(t) \,\Big|\, k\Big], \qquad R^\pi(k) = \sum_{i \in E} r_i\, x_i^\pi(k),$$
--   for a reward vector $r$, and $R^{\mathrm{opt}}(k) = \sup_\pi R^\pi(k)$. For $S \subseteq E$,
--   $$A^\pi(S, k) = \sum_{i \in E} A_i^S\, x_i^\pi(k), \qquad A(S, k) = \inf_\pi A^\pi(S, k).$$
--
--   **Arms missing a set, and the aggregated entry time.** Write $S_i = \{j \in E : j \le i\}$ for the job types up to $i$ (job types are numbered $1, \dots, N$). $B_i$ is the set of arms with no job type in $S_i$, and $\psi_i = |B_i|$. For an arm $b \notin B_i$, $T_{k_b}^{S_i}$ is the amount of processing needed to move arm $b$ from $k_b$ until it first enters $S_i$ ($0$ if $k_b \in S_i$), and $T_k^{S_i} = \sum_{b \notin B_i} T_{k_b}^{S_i}$, the arms evolving independently. For $m > 0$ the quantity
--   $$E\big[a^{T_k^{S_i}/m}\big]$$
--   is taken with a real exponent and $a^\infty = 0$.
--
--   **Formalization Note** Job types are `Fin (N + 1)`, so the book's $N$ is Lean's `N + 1` and the book's job type $i$ is the Lean index `i - 1`; `S_i` is `Finset.Iic i` and `Set.Iic i`. Arms are `Fin n`, and `arm : Fin (N + 1) → Fin n` assigns each job type to its arm (`IsArmFamily P arm` is the closedness and irreducibility assumption); one kernel on the disjoint union replaces the book's per-arm matrices $P^b$. A set of processed arms is a Boolean vector with exactly $M$ true entries almost surely. The supremum `optimalReturn` and the infimum `minCoeffSum` range over all such policies; the class is nonempty exactly when $M \le n$, and every theorem of the mission assumes $1 \le M \le n$. $E[a^{T_k^{S_i}/m}]$ is an integral against the product of the $n$ single-arm chain laws.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.7 pp. 139–140 (standing assumptions, Aᵖ(S, k), Rᵖ(k), A(S, k), i_b, ψ_i, B_i, T_k^{S_i}); §5.3 p. 119–120 (performance (5.1), matrix (5.3))

import Definitions.Def_AllocationIndices_Achievable

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

/-!
Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices* (2nd ed., Wiley 2011),
§5.7 (pp. 139–142): the simple family of alternative bandit processes (SFABP) of §5.3 operated
on `M` identical parallel machines, in discrete time with discount factor `a`.

* Job types are the states `Fin (N + 1)` (the book's `E = {1, …, N}` with the book's `N`
  equal to `N + 1` here, so the book's `ν_N` is `Fin.last N`; the Lean type `i` is the book's
  job type `i + 1`). A single Markov kernel `P` on job types describes every arm:
  `arm i` is the arm `b` whose state space `E_b` contains `i`. `IsArmFamily P arm` says that each
  `E_b` is closed under `P` (an arm never leaves its own state space) and that `P` is irreducible
  on each `E_b` (the standing assumption of p. 139). The matrix `A = (Aᵢ^S)` is the published
  single-arm `conservationCoeff P a S i` of §5.3 (Eq. (5.3)), which for `i ∈ E_b` only involves
  arm `b`'s chain.
* `ParallelPolicy n N M` — a policy for `n` arms on `M` machines: at each decision time
  `t = 0, 1, 2, …` it chooses, possibly at random and on the basis of the history (past
  state-vectors and past choices, and the current state-vector), a set of exactly `M` distinct
  arms (encoded as a Boolean vector `s : Fin n → Bool`), one for each machine. The chosen arms
  make one transition each, independently, according to `P`; the other arms are frozen.
* `parallelMeasure P π k t` — the law of the history of the first `t` periods, from the initial
  state-vector `k`.
* `parallelPerformance P π a k i` — the performance `xᵢᵖ(k) = Eᵖ[∑_t aᵗ Iᵢ(t) | k]`, where `Iᵢ(t)`
  is the number of machines that process a job of type `i` at time `t` (§5.3, (5.1), with the
  conditioning on the initial state `k` made explicit, p. 139).
* `parallelReturn P π a r k` — `Rᵖ(k) = ∑_{i∈E} rᵢ xᵢᵖ(k)`; `optimalReturn` — `R^opt(k)`, the
  supremum over all policies.
* `coeffSum P π a k S` — `Aᵖ(S, k) = ∑_{i∈E} Aᵢ^S xᵢᵖ(k)` (p. 139); `minCoeffSum` —
  `A(S, k) = min_π Aᵖ(S, k)` (p. 140), the infimum over all policies.
* `missedArms arm i` — the set `B_i` of arms with no job type in `S_i = {j ≤ i}`; `psi arm i` —
  `ψ_i = |B_i|` (p. 140).
* `firstEntryTime S ω` — the first `t ≥ 0` with `ω t ∈ S` (`⊤` if none); `aggregateEntryDiscount
  P a arm k i m` — `E[a^{T_k^{S_i}/m}]` with `T_k^{S_i} = ∑_{b∉B_i} T_{k_b}^{S_i}`, the arms
  evolving independently, each from its initial state `k_b` (p. 140); `a^∞ = 0`.
-/

namespace AllocationIndices.Branching

/-! ### Arms, job types and the matrix `A` -/

section Arms

variable {N n : ℕ}

/-- The standing assumption of §5.7 (p. 139) for the single kernel `P` on job types: every arm's
state space `E_b = {i : arm i = b}` is closed under `P` (a transition of arm `b` stays in `E_b`),
and the chain is irreducible on each `E_b`: from every `i ∈ E_b` it reaches every `j ∈ E_b` with
positive probability. -/
def IsArmFamily (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (arm : Fin (N + 1) → Fin n) : Prop :=
  (∀ i, P i {j | arm j = arm i} = 1) ∧
  (∀ i j, arm i = arm j → markovChainMeasure P i {ω | ∃ t, ω t = j} ≠ 0)

/-- `B_i`: the arms with no job type in `S_i = {j : j ≤ i}`, i.e. every job type of the arm has
index above `i` (p. 140). -/
def missedArms (arm : Fin (N + 1) → Fin n) (i : Fin (N + 1)) : Finset (Fin n) :=
  univ.filter fun b ↦ ∀ j, arm j = b → i < j

/-- `ψ_i = |B_i|`, the number of arms which have no intersection with `S_i` (p. 140). -/
def psi (arm : Fin (N + 1) → Fin n) (i : Fin (N + 1)) : ℕ :=
  (missedArms arm i).card

/-- The first time `t ≥ 0` at which the trajectory `ω` is in `S`, `⊤` if it never is: the amount of
processing needed to bring an arm into `S` (`0` if it starts in `S`). -/
noncomputable def firstEntryTime (S : Set (Fin (N + 1))) (ω : ℕ → Fin (N + 1)) : ℕ∞ :=
  ⨅ t : {t : ℕ // ω t ∈ S}, ((t : ℕ) : ℕ∞)

/-- `E[a^{T_k^{S_i} / m}]` (p. 140), where `T_k^{S_i} = ∑_{b ∉ B_i} T_{k_b}^{S_i}` and
`T_{k_b}^{S_i}` is the amount of processing required to move arm `b` from its initial state `k_b`
until it enters `S_i = {j ≤ i}` for the first time. The arms evolve independently, arm `b` as the
chain `P` from `k_b` (the product measure); `a^∞ = 0`. The exponent `T / m` is real. -/
noncomputable def aggregateEntryDiscount (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (a : ℝ) (arm : Fin (N + 1) → Fin n) (k : Fin n → Fin (N + 1))
    (i : Fin (N + 1)) (m : ℝ) : ℝ :=
  ∫ ω, (match ∑ b ∈ univ \ missedArms arm i, firstEntryTime (Set.Iic i) (ω b) with
    | (T : ℕ) => a ^ ((T : ℝ) / m)
    | ⊤ => 0) ∂Measure.pi (fun b ↦ markovChainMeasure P (k b))

end Arms

/-! ### Policies on `M` parallel machines and their performance -/

section Parallel

variable {N n M : ℕ}

/-- A history of `t` completed periods on `M` parallel machines: for each past period, the
state-vector at its start and the set of arms processed (a Boolean vector); plus the current
state-vector. -/
abbrev ParallelHistory (n N t : ℕ) :=
  (Fin t → (Fin n → Fin (N + 1)) × (Fin n → Bool)) × (Fin n → Fin (N + 1))

/-- The number of arms selected by the Boolean vector `s`. -/
def selCount (s : Fin n → Bool) : ℕ :=
  (univ.filter fun b ↦ s b = true).card

/-- A policy for `n` arms on `M` parallel machines (§5.7): for each period `t`, a Markov kernel
from the observed history to the set of arms processed in that period, which almost surely has
exactly `M` elements (each machine processes one arm per period). -/
structure ParallelPolicy (n N M : ℕ) where
  /-- The conditional law of the set of arms processed in period `t`, given the history. -/
  select : (t : ℕ) → Kernel (ParallelHistory n N t) (Fin n → Bool)
  /-- Each period's selection kernel is a Markov kernel. -/
  markov : ∀ t, IsMarkovKernel (select t)
  /-- Exactly `M` arms are processed in every period. -/
  card_eq : ∀ t h, select t h {s | selCount s = M} = 1

attribute [instance] ParallelPolicy.markov

/-- The transition kernel of one arm in one period: `P` if the arm is processed, frozen
(`Kernel.id`) otherwise. -/
noncomputable def armKernel (P : Kernel (Fin (N + 1)) (Fin (N + 1))) (processed : Bool) :
    Kernel (Fin (N + 1)) (Fin (N + 1)) :=
  if processed then P else Kernel.id

instance armKernel.instIsMarkovKernel (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (processed : Bool) : IsMarkovKernel (armKernel P processed) := by
  unfold armKernel; split <;> infer_instance

/-- One period of the parallel-machine system: given the state-vector `x` and the set `s` of
processed arms, the arms move independently, each processed arm by `P` and every other arm not
at all. -/
noncomputable def parallelMove (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] :
    Kernel ((Fin n → Fin (N + 1)) × (Fin n → Bool)) (Fin n → Fin (N + 1)) where
  toFun p := Measure.pi fun b ↦ armKernel P (p.2 b) (p.1 b)
  measurable' := measurable_of_countable _

instance parallelMove.instIsMarkovKernel (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] : IsMarkovKernel (parallelMove (n := n) P) :=
  ⟨fun p ↦ by simp only [parallelMove, Kernel.coe_mk]; infer_instance⟩

/-- One period under the policy `π`: sample the set of processed arms from `π.select t`, then
the next state-vector from `parallelMove P`. -/
noncomputable def parallelStepKernel (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (t : ℕ) :
    Kernel (ParallelHistory n N t) ((Fin n → Bool) × (Fin n → Fin (N + 1))) :=
  (π.select t).compProd ((parallelMove P).comap (fun q ↦ (q.1.2, q.2)) (measurable_of_countable _))

/-- The law of the history of the first `t` periods under `π` from the initial state-vector `k`. -/
noncomputable def parallelMeasure (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) :
    (t : ℕ) → Measure (ParallelHistory n N t)
  | 0 => Measure.dirac (fun u ↦ u.elim0, k)
  | t + 1 =>
      ((parallelMeasure P π k t).compProd (parallelStepKernel P π t)).map
        (fun p ↦ (Fin.snoc (α := fun _ ↦ (Fin n → Fin (N + 1)) × (Fin n → Bool)) p.1.1
          (p.1.2, p.2.1), p.2.2))

/-- `Eᵖ[Iᵢ(t) | k]`: the expected number of machines processing a job of type `i` in period `t`
(0-indexed), i.e. of processed arms whose state at the start of period `t` is `i`. -/
noncomputable def parallelOccupation (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (i : Fin (N + 1)) (t : ℕ) : ℝ :=
  ∫ h, ((univ.filter fun b ↦ (h.1 (Fin.last t)).2 b = true ∧ (h.1 (Fin.last t)).1 b = i).card : ℝ)
    ∂parallelMeasure P π k (t + 1)

/-- The performance `xᵢᵖ(k) = Eᵖ[∑_{t≥0} aᵗ Iᵢ(t) | k]` (§5.3 (5.1), p. 139): the total discounted
number of times a job of type `i` is processed under `π` from the initial state-vector `k`. -/
noncomputable def parallelPerformance (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (a : ℝ) (k : Fin n → Fin (N + 1)) (i : Fin (N + 1)) : ℝ :=
  ∑' t : ℕ, a ^ t * parallelOccupation P π k i t

/-- The expected return `Rᵖ(k) = ∑_{i∈E} rᵢ xᵢᵖ(k)`. -/
noncomputable def parallelReturn (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (a : ℝ) (r : Fin (N + 1) → ℝ) (k : Fin n → Fin (N + 1)) : ℝ :=
  linearObjective r (parallelPerformance P π a k)

/-- `R^opt(k) = sup_π Rᵖ(k)`, the optimal return over all policies on `M` machines. -/
noncomputable def optimalReturn (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (M : ℕ) (a : ℝ) (r : Fin (N + 1) → ℝ) (k : Fin n → Fin (N + 1)) : ℝ :=
  ⨆ π : ParallelPolicy n N M, parallelReturn P π a r k

/-- `Aᵖ(S, k) = ∑_{i∈E} Aᵢ^S xᵢᵖ(k)` (p. 139), with `A` the matrix (5.3) of §5.3. -/
noncomputable def coeffSum (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (a : ℝ) (k : Fin n → Fin (N + 1)) (S : Finset (Fin (N + 1))) : ℝ :=
  ∑ i, conservationCoeff P a S i * parallelPerformance P π a k i

/-- `A(S, k) = min_π Aᵖ(S, k)` (p. 140), the infimum over all policies on `M` machines. -/
noncomputable def minCoeffSum (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (M : ℕ) (a : ℝ) (k : Fin n → Fin (N + 1)) (S : Finset (Fin (N + 1))) : ℝ :=
  ⨅ π : ParallelPolicy n N M, coeffSum P π a k S

end Parallel

end AllocationIndices.Branching


