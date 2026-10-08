-- Prove2me | Definitions.Def_NegativeDP_OptEq_Futures
-- name    : NegativeDP_OptEq_Futures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:21.025257+00:00
-- url     : https://prove2.me/theorems/e18a2156-709e-4924-95b6-21d657f745b3
-- title:
--   The law $e_\pi(s)$ of the future $(a_1,s_2,a_2,s_3,\dots)$ under a policy, by Ionescu-Tulcea
-- statement:
--   Let $X = A\times S\times A\times S\times\cdots$ be the set of **futures** of the system, the sequences $x = (a_1,s_2,a_2,s_3,\dots)$ of actions and subsequent states, with the product σ-field. A policy $\pi$ and the law of motion $q$ define, for every initial state $s$, a probability measure
--   $$e_\pi(s) = \pi_1 q\, \pi_2 q \cdots \in P(X):$$
--   $a_1$ is drawn from $\pi_1(\cdot\mid s)$, then $s_2$ from $q(\cdot\mid s,a_1)$, then $a_2$ from $\pi_2(\cdot\mid s,a_1,s_2)$, and so on. This is the law of the whole future of the process started at $s$ under $\pi$ (Strauch, §3, p. 874).
--
--   It is used to define the set $\Gamma = \{(s,\nu) : \nu = e_\pi(s)\text{ for some policy }\pi\}\subseteq S\times P(X)$, whose Borel measurability (Lemma 7.2) is the first step towards the absolute measurability of the optimal return.
--
--   **Formalization Note** $X$ is `ℕ → A × S`; coordinate $n$ (from $0$) is the pair $(a_{n+1}, s_{n+2})$. $e_\pi(s)$ is built with Mathlib's Ionescu-Tulcea kernel `Kernel.traj` on the sequence of state-action pairs $((s_1,a_1),(s_2,a_2),\dots)$: the step kernel draws $s_{n+2}$ from $q(\cdot\mid s_{n+1},a_{n+1})$ and then $a_{n+2}$ from the plan's kernel at the history $(s_1,a_1,\dots,s_{n+2})$; the initial pair is $(s,a_1)$ with $a_1\sim\pi_1(\cdot\mid s)$, and the resulting trajectory law is pushed forward to $X$. $P(X)$ is the space of probability measures with Mathlib's Giry σ-field, the smallest σ-field making $\nu\mapsto\nu(B)$ measurable for every Borel $B$, which is the paper's $\Sigma^*$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 874 (§3, e_π = π_1qπ_2q⋯ ∈ Q(X | S)) and p. 884 (§7, X = ASAS⋯, Σ*)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_NegativeDP_OptEq_Model

namespace NegativeDP.OptEq

open MeasureTheory ProbabilityTheory Finset
open DiscountedDP.Stationary (Hist Plan)

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The set of futures `X = ASAS⋯` (p. 884): coordinate `n` is the pair `(aₙ₊₁, sₙ₊₂)`
(paper's indices, 1-based), with the product σ-field. -/
abbrev Futures (S A : Type*) := ℕ → A × S

/-- The first `n+1` state-action pairs of a trajectory, as a history prefix. -/
def trajPairs (n : ℕ) (x : Π _ : Iic n, S × A) : Fin (n + 1) → S × A :=
  fun i => x ⟨i.1, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩

/-- The last state-action pair `(sₙ₊₁, aₙ₊₁)` of a trajectory prefix. -/
def trajLast (n : ℕ) (x : Π _ : Iic n, S × A) : S × A :=
  x ⟨n, Finset.mem_Iic.2 le_rfl⟩

lemma measurable_trajPairs (n : ℕ) : Measurable (trajPairs (S := S) (A := A) n) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma measurable_trajLast (n : ℕ) : Measurable (trajLast (S := S) (A := A) n) :=
  measurable_pi_apply _

/-- Reading the futures `(a₁, s₂, a₂, s₃, …)` off a trajectory of pairs `((s₁, a₁), (s₂, a₂), …)`. -/
def toFutures (ω : ℕ → S × A) : Futures S A := fun n => ((ω n).2, (ω (n + 1)).1)

lemma measurable_toFutures : Measurable (toFutures (S := S) (A := A)) :=
  measurable_pi_lambda _ (fun n =>
    ((measurable_pi_apply n).snd).prodMk (measurable_pi_apply (n + 1)).fst)

/-- The history `(s₁, a₁, …, sₙ₊₁, aₙ₊₁, sₙ₊₂)` formed by a trajectory prefix and a new state. -/
def trajHist (n : ℕ) (p : (Π _ : Iic n, S × A) × S) : Hist S A (n + 1) :=
  (trajPairs n p.1, p.2)

lemma measurable_trajHist (n : ℕ) : Measurable (trajHist (S := S) (A := A) n) :=
  ((measurable_trajPairs n).comp measurable_fst).prodMk measurable_snd

variable [StandardBorelSpace S] [Nonempty S] [StandardBorelSpace A] [Nonempty A]

/-- One step of the process on state-action pairs: from the pairs `(s₁, a₁), …, (sₙ₊₁, aₙ₊₁)`,
draw `sₙ₊₂ ~ q(· | sₙ₊₁, aₙ₊₁)` and then `aₙ₊₂ ~ πₙ₊₂(· | s₁, a₁, …, sₙ₊₂)`. -/
noncomputable def pairKernel (P : NegativeDP.Stationary.Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) :
    Kernel (Π _ : Iic n, S × A) (S × A) :=
  letI : IsMarkovKernel P.q := P.q_markov
  letI : IsMarkovKernel (π.κ (n + 1)) := π.κ_markov (n + 1)
  (P.q.comap (trajLast n) (measurable_trajLast n)) ⊗ₖ
    ((π.κ (n + 1)).comap (trajHist n) (measurable_trajHist n))

instance (P : NegativeDP.Stationary.Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) :
    IsMarkovKernel (pairKernel P π n) := by
  have : IsMarkovKernel P.q := P.q_markov
  have : IsMarkovKernel (π.κ (n + 1)) := π.κ_markov (n + 1)
  unfold pairKernel
  infer_instance

/-- `e_π(s) = π₁qπ₂q⋯ ∈ P(X)` (p. 874): the law of the future `(a₁, s₂, a₂, …)` of the process
started at `s` under `π`, built with the Ionescu-Tulcea theorem (`Kernel.traj`). -/
noncomputable def futureLaw (P : NegativeDP.Stationary.Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    Measure (Futures S A) :=
  letI : IsMarkovKernel (π.κ 0) := π.κ_markov 0
  (((Kernel.traj (pairKernel P π) 0).comap
      (fun a : A => (fun _ : Iic 0 => (s, a)))
      (measurable_pi_lambda _ (fun _ => measurable_prodMk_left)) ∘ₘ
    (π.κ 0 ((fun i : Fin 0 => Fin.elim0 i), s)))).map toFutures

end NegativeDP.OptEq


