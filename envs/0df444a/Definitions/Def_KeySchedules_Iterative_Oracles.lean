-- Prove2me | Definitions.Def_KeySchedules_Iterative_Oracles
-- name    : KeySchedules_Iterative_Oracles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:50:10.240143+00:00
-- url     : https://prove2.me/theorems/a174acd0-a5bd-47af-8f3c-d1e028983280
-- title:
--   Oracle systems, adaptive adversaries with a per-oracle query budget, transcript probabilities, the distinguishing advantage and g★
-- statement:
--   A **game interface** consists of a finite set $\iota$ of oracles, a finite query alphabet $Q$, a finite response alphabet $R$, and a map $\mathrm{oracleOf}:Q\to\iota$ naming the oracle that receives each query. A **query-response transcript** $\tau$ is the chronological list of the pairs $(x,y)\in Q\times R$ exchanged; $\mathrm{queryCount}(\tau,o)$ is the number of its queries addressed to oracle $o$, and $\tau$ is *within $q$ queries* when this is at most $q$ for every oracle.
--
--   A **system** is described by its transcript probabilities $p(\tau)$: the probability that the system, given the queries of $\tau$ in their recorded order, returns the recorded responses. They satisfy
--   $$p(\tau)\ge 0,\qquad p([\,])=1,\qquad \sum_{y\in R}p(\tau\cdot(x,y))=p(\tau)\quad\text{for every }\tau\text{ and every next query }x,$$
--   which is exactly the information a (possibly stateful, jointly randomized) tuple of oracles presents to an adversary.
--
--   A **deterministic adversary** is a strategy: on the transcript so far it either asks a next query or stops, and once stopped it outputs a bit. A transcript is *consistent* with it when each recorded query is the one the strategy asks after the preceding part, and *complete* when moreover the strategy stops there. The strategy makes **at most $q$ queries to each oracle** when, on every consistent transcript and whatever the responses, it never asks a $(q+1)$-st query to any oracle; every run then stops. For such a strategy the transcript $\Theta$ against a system with probabilities $p$ satisfies $\Pr[\Theta=\tau]=p(\tau)$ for complete $\tau$ and $0$ otherwise, so
--   $$\Pr[\mathcal A^{S}\Rightarrow 1]=\sum_{\tau\text{ complete},\ \mathrm{out}(\tau)=1}p(\tau),\qquad \mathbb E[F(\Theta)]=\sum_{\tau\text{ complete}}p(\tau)F(\tau).$$
--   A (randomized) **adversary** is a finite mixture of deterministic strategies with probability weights; probabilities and expectations are averaged over the mixture, and it is within the budget when each of its strategies is. The **distinguishing advantage** (Eq. (1)) of two systems with probabilities $p_0$ (ideal) and $p_1$ (real) is
--   $$\mathrm{Adv}^{(S_0,S_1)}(\mathcal A)=\bigl|\Pr[\mathcal A^{S_1}\Rightarrow1]-\Pr[\mathcal A^{S_0}\Rightarrow1]\bigr|.$$
--   Finally, for a bad set $\mathcal T_{\mathrm{bad}}$ and a function $g$, Lemma 2.1's $g^\star(\tau)=1$ for $\tau\in\mathcal T_{\mathrm{bad}}$ and $g^\star(\tau)=\min\{1,g(\tau)\}$ otherwise.
--
--   **Formalization Note.** Sums over complete transcripts are `tsum`s over `List (Q × R)`; for an adversary within a budget only finitely many transcripts are complete, so they are finite sums. Statements always assume the budget.
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), pp. 6–8, §2.1 (Oracle and Adversary; Distinguishing Advantage, Eq. (1); Expectation Method; g★ of Lemma 2.1)

import Mathlib

namespace KeySchedules.Iterative

/-!
# Oracle systems, adaptive adversaries, transcripts and the distinguishing advantage

Beierle, Choi, Hhan, Jha, Kim, *Minimizing Key Schedules for Key-Alternating Ciphers*,
STOC 2027 submission (manuscript sha256 cd9f815b…), §2.1, pp. 6–8: "Oracle and Adversary",
"Distinguishing Advantage" (Eq. (1)), "Expectation Method" (the transcript probabilities
`p_b`, attainable transcripts, the function `g★` of Lemma 2.1).

* A game interface has a finite set of oracles `ι`, a finite query alphabet `Q` and a finite
  response alphabet `R`; every query is addressed to the oracle `oracleOf x`.
* A query-response transcript is the chronological list of (query, response) pairs.
* A system is given by its transcript probabilities `p(τ)`: the probability that the system,
  given the queries of `τ` in their recorded order, returns the recorded responses. They satisfy
  `p([]) = 1`, `p ≥ 0` and, for every transcript `τ` and next query `x`,
  `∑_y p(τ ++ [(x, y)]) = p(τ)`. This covers stateful systems with joint randomness.
* A deterministic adversary is a strategy: on the transcript so far it either asks the next
  query (`next τ = some x`) or stops (`next τ = none`) and outputs the bit `out τ`.
* A (randomized) adversary is a finite mixture of deterministic strategies with probability
  weights; probabilities and expectations are averaged over the mixture.
-/

/-- A game interface: finitely many oracles `ι`, finite query and response alphabets `Q`, `R`,
and the oracle `oracleOf x` that receives the query `x`. -/
structure Interface where
  ι : Type
  Q : Type
  R : Type
  oracleOf : Q → ι
  [fintypeι : Fintype ι]
  [decEqι : DecidableEq ι]
  [fintypeQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  [fintypeR : Fintype R]
  [decEqR : DecidableEq R]

attribute [instance] Interface.fintypeι Interface.decEqι Interface.fintypeQ Interface.decEqQ
  Interface.fintypeR Interface.decEqR

/-- A query-response transcript: the chronological list of (query, response) pairs. -/
abbrev Transcript (I : Interface) : Type := List (I.Q × I.R)

/-- The number of queries of the transcript `τ` addressed to the oracle `o`. -/
def queryCount {I : Interface} (τ : Transcript I) (o : I.ι) : ℕ :=
  τ.countP (fun e => decide (I.oracleOf e.1 = o))

/-- `τ` has at most `q` queries to each oracle. -/
def WithinQueries {I : Interface} (τ : Transcript I) (q : ℕ) : Prop :=
  ∀ o : I.ι, queryCount τ o ≤ q

/-- A system, given by its transcript probabilities `prob τ` (the paper's `p_b(τ)`). -/
structure System (I : Interface) where
  prob : Transcript I → ℝ
  prob_nonneg : ∀ τ, 0 ≤ prob τ
  prob_nil : prob [] = 1
  prob_extend : ∀ (τ : Transcript I) (x : I.Q), ∑ y : I.R, prob (τ ++ [(x, y)]) = prob τ

/-- A deterministic adversary: given the transcript so far, `next` is the next query or `none`
(stop), and `out` is the output bit once it has stopped. -/
structure DetAdversary (I : Interface) where
  next : Transcript I → Option I.Q
  out : Transcript I → Bool

/-- The query choices of `A` agree with `τ`: each query of `τ` is the one `A` asks after the
preceding part of `τ`. -/
def DetAdversary.Consistent {I : Interface} (A : DetAdversary I) (τ : Transcript I) : Prop :=
  ∀ i : Fin τ.length, A.next (τ.take i) = some (τ.get i).1

/-- `τ` is a complete transcript of `A`: its query choices and its stopping rule agree with `τ`. -/
def DetAdversary.Complete {I : Interface} (A : DetAdversary I) (τ : Transcript I) : Prop :=
  A.Consistent τ ∧ A.next τ = none

/-- `A` makes at most `q` queries to each oracle, whatever the responses: it never asks a
`(q+1)`-st query to any oracle. In particular every run stops. -/
def DetAdversary.WithinBudget {I : Interface} (A : DetAdversary I) (q : ℕ) : Prop :=
  ∀ (τ : Transcript I) (x : I.Q), A.Consistent τ → A.next τ = some x →
    queryCount τ (I.oracleOf x) < q

open Classical in
/-- `∑_{τ complete for A} f(τ)`. With `f = p · F`, this is `E[F(Θ)]` for the transcript `Θ` of
`A` against the system with transcript probabilities `p`, since `Pr[Θ = τ] = p(τ)` when the
query choices and stopping rule of `A` agree with `τ`, and `0` otherwise. -/
noncomputable def DetAdversary.sumComplete {I : Interface} (A : DetAdversary I)
    (f : Transcript I → ℝ) : ℝ :=
  ∑' τ : Transcript I, if A.Complete τ then f τ else 0

/-- `Pr[A^S ⇒ 1]` for a deterministic `A` and transcript probabilities `p` of `S`. -/
noncomputable def DetAdversary.accept {I : Interface} (A : DetAdversary I)
    (p : Transcript I → ℝ) : ℝ :=
  A.sumComplete (fun τ => if A.out τ = true then p τ else 0)

/-- A (randomized) adversary: a finite mixture of deterministic strategies `strat i` with
probability weights `weight i`. -/
structure Adversary (I : Interface) where
  n : ℕ
  weight : Fin n → ℝ
  strat : Fin n → DetAdversary I
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1

/-- Every strategy of the mixture makes at most `q` queries to each oracle. -/
def Adversary.WithinBudget {I : Interface} (A : Adversary I) (q : ℕ) : Prop :=
  ∀ i, (A.strat i).WithinBudget q

/-- `Pr[A^S ⇒ 1]`, averaged over the mixture. -/
noncomputable def Adversary.accept {I : Interface} (A : Adversary I)
    (p : Transcript I → ℝ) : ℝ :=
  ∑ i, A.weight i * (A.strat i).accept p

/-- `∑_{τ complete} f(τ)`, averaged over the mixture (`E[F(Θ)]` for `f = p · F`). -/
noncomputable def Adversary.sumComplete {I : Interface} (A : Adversary I)
    (f : Transcript I → ℝ) : ℝ :=
  ∑ i, A.weight i * (A.strat i).sumComplete f

/-- The distinguishing advantage (Eq. (1)):
`Adv^{(S0,S1)}(A) = |Pr[A^{S1} ⇒ 1] − Pr[A^{S0} ⇒ 1]|`, for transcript probabilities `p0`, `p1`. -/
noncomputable def advantage {I : Interface} (p0 p1 : Transcript I → ℝ) (A : Adversary I) : ℝ :=
  |A.accept p1 - A.accept p0|

open Classical in
/-- The function `g★` of Lemma 2.1: `1` on the bad set, `min{1, g}` off it. -/
noncomputable def gStar {α : Type} (bad : Set α) (g : α → ℝ) (x : α) : ℝ :=
  if x ∈ bad then 1 else min 1 (g x)

end KeySchedules.Iterative


