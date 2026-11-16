-- Prove2me | Definitions.Def_GMRDiversity_Supplement_MemoryPolicy
-- name    : GMRDiversity_Supplement_MemoryPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:09:21.237205+00:00
-- url     : https://prove2.me/theorems/8dd93ba4-dd94-415c-b473-15dd1807858c
-- title:
--   Policies with $M$ bits of memory for parity learning, and their value
-- statement:
--   Consider the parity-learning instance $\mathfrak G^{\mathrm{par}}_x$ (candidates $(a,b)\in\{0,1\}^n\times\{0,1\}$, generation $\mathrm{Gen}_x$, recombination $\mathrm{XOR}$, utility $U_x(a,b)=\mathbf 1\{a=x\}$, full feedback), with the hidden target $x\sim\mathrm{Unif}(\{0,1\}^n)$ drawn independently of the policy. A **policy with memory $M$** keeps, after every round $t$, its entire persistent state as $S_t\in\{0,1\}^M$, starting from a fixed $S_0$. In round $t$:
--
--   1. it draws its action from a law depending only on $t$ and $S_{t-1}$: either a generation, or the XOR of two candidate values $u,v$ (decoded from $S_{t-1}$);
--   2. it queries the candidate $z_t$ ($z_t\sim\mathrm{Gen}_x$, or $z_t=u\oplus v$) and observes $(z_t,U_x(z_t))$;
--   3. it draws $S_t$ from a law depending only on $t$, $S_{t-1}$, the action, $z_t$ and $U_x(z_t)$.
--
--   Fresh randomness inside a round is free. The **value** of such a policy is
--   $$
--   V^\pi_T(\mathfrak G^{\mathrm{par}}_x):=\mathbb E\Big[\max_{t\in[T]}U_x(z_t)\Big],
--   $$
--   averaged also over $x$; since $U_x\in\{0,1\}$ it is the probability that some $z_t$, $t\le T$, has first coordinate $x$. A policy has **XOR arguments that are previously queried candidates** if, on every positive-probability trajectory, every recombination it can choose combines two candidates queried in earlier rounds.
--
--   These are the objects of Theorem 4 (memory is necessary).
--
--   **Formalization Note** $\{0,1\}^M$ is `Fin M → Bool`. The round index and the randomness shared between the action and the state update (passed through the action) are free, as on p.9. The memory bound holds at every round, which changes no value at time $T$. The XOR arguments of a `MemoryPolicy` are arbitrary values computed from the state; the strict reading ("recoverable from $S_t$", "previous indices") is the predicate `MemoryPolicy.XorOfQueried`. $V^\pi_0=0$. The candidates, $\mathrm{Gen}_x$ and $U_x$ are the published `GMRDiversity.Cand`, `genLaw`, `hit`.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), §6 'Bounded memory policies', p.9; value §2 'Query Complexity', p.4, and §6, p.8

import Mathlib
import Definitions.Def_GMRDiversity_Cand

namespace GMRDiversity.Supplement

open ExtremalForrelation.Nonadaptive

/-- **Policies with memory `M`** for the parity instance `𝔊^par_x` (Brandenberger, Doron-Arad,
Mossel, *Genetic Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript
sha256 f89f4f77…, §6 "Bounded memory policies", p.9): "after every round `t ≤ T`, its entire
persistent state can be represented by a random variable `S_t ∈ {0,1}^M`. Conditional on `S_t` and
`t`, the distribution of all future actions is independent of the earlier history. … a candidate
may be used as an input to a future operator only if its value is recoverable from `S_t`. Fresh
independent randomness is not counted toward the memory bound."

A policy is given by a fixed initial state and two probability kernels.
* `act t S` is the law of the action of round `t` given `S = S_{t−1}`: `none` is a generation
  `Gen_x`, and `some (u, v)` is the recombination `XOR(u, v) = u + v` of the two candidate values
  `u, v` (decoded from `S_{t−1}`).
* `upd t S a z r` is the law of the next state `S_t`, given the round, the old state, the action,
  the queried candidate `z` and the feedback bit `r = U_x(z)` (full feedback `(z, U_x(z))`, p.8).

**Formalization Note.** `{0,1}^M` is `Fin M → Bool`. The round index `t` and the fresh randomness
inside a round (shared by `act` and `upd` through the action `a`) are free, as on p.9. The memory
bound is imposed at every round; the value at time `T` depends only on rounds `≤ T`, so this changes
no instance. The XOR arguments are arbitrary values computed from the state; that they be
previously queried candidates (p.4, "previous indices") is the separate predicate
`MemoryPolicy.XorOfQueried`. The policy never sees `x` and is fixed before `x` is drawn. -/
structure MemoryPolicy (n M : ℕ) where
  /-- The initial state `S₀`. -/
  init : Fin M → Bool
  /-- Law of the action of round `t` given `S_{t−1}`. -/
  act : ℕ → (Fin M → Bool) → PMF (Option (Cand n × Cand n))
  /-- Law of `S_t` given the round, `S_{t−1}`, the action, the candidate and its feedback bit. -/
  upd : ℕ → (Fin M → Bool) → Option (Cand n × Cand n) → Cand n → Bool → PMF (Fin M → Bool)

/-- The law of the candidate queried by an action: `Gen_x` for `none`, and the deterministic
`XOR(u, v) = u + v` for `some (u, v)` (§6, p.8). -/
noncomputable def memQueryLaw {n : ℕ} (x : V n) : Option (Cand n × Cand n) → PMF (Cand n)
  | none => genLaw x
  | some (u, v) => PMF.pure (u + v)

/-- One round `t` of a memory-`M` policy on the hidden target `x`, acting on
(state `S`, list of the candidates queried so far, has the target been queried yet). The list is
bookkeeping of the run, not part of the policy's state: `act` and `upd` never see it. -/
noncomputable def memRoundStep {n M : ℕ} (π : MemoryPolicy n M) (x : V n) (t : ℕ)
    (s : (Fin M → Bool) × List (Cand n) × Bool) : PMF ((Fin M → Bool) × List (Cand n) × Bool) :=
  (π.act t s.1).bind fun a =>
    (memQueryLaw x a).bind fun z =>
      (π.upd t s.1 a z (hit x z)).map fun S' => (S', z :: s.2.1, s.2.2 || hit x z)

/-- The law after `T` rounds of (state `S_T`, queried candidates, `max_{t ∈ [T]} U_x(z_t) = 1`),
starting from `S₀ = init`; rounds are numbered from `1`. -/
noncomputable def memRunLaw {n M : ℕ} (π : MemoryPolicy n M) (x : V n) :
    ℕ → PMF ((Fin M → Bool) × List (Cand n) × Bool)
  | 0 => PMF.pure (π.init, [], false)
  | T + 1 => (memRunLaw π x T).bind (memRoundStep π x (T + 1))

/-- **The value `V^π_T(𝔊^par_x)` of a memory-`M` policy** (§2 "Query Complexity", p.4, and §6,
p.8): `V^π_T := E[max_{t ∈ [T]} U_x(z_t)]` with `x ∼ Unif({0,1}ⁿ)` independent of the policy, "and
`V^π_T` also averages over the choice of `x`".

**Formalization Note.** As in the published `GMRDiversity.value` (which is typed on live-pool
policies), the expectation of the `{0,1}`-valued maximum is the probability that some `z_t`,
`t ≤ T`, has first coordinate `x`, averaged over the `2ⁿ` targets; `V^π_0 = 0`. -/
noncomputable def memValue {n M : ℕ} (π : MemoryPolicy n M) (T : ℕ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, ((memRunLaw π x T).toOuterMeasure {s | s.2.2 = true}).toReal

/-- **XOR arguments are previously queried candidates** (§2 "Policies", p.4: operators take
"previous indices `i₁, …, i_k < t`"; §6, p.9): on every reachable state of every run, every
recombination the policy can choose combines two candidates that were queried in earlier rounds of
that run. In particular the first round is a generation. -/
def MemoryPolicy.XorOfQueried {n M : ℕ} (π : MemoryPolicy n M) : Prop :=
  ∀ (x : V n) (T : ℕ), ∀ s ∈ (memRunLaw π x T).support, ∀ u v : Cand n,
    some (u, v) ∈ (π.act (T + 1) s.1).support → u ∈ s.2.1 ∧ v ∈ s.2.1

end GMRDiversity.Supplement


