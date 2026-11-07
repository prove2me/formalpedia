-- Prove2me | Definitions.Def_DataValidation_Policy
-- name    : DataValidation_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:47.266083+00:00
-- url     : https://prove2.me/theorems/479acbf7-bd5a-4db8-ae09-ccf62494f557
-- title:
--   Histories, probable edges, adaptive policies and the expected reward $W(\pi)$
-- statement:
--   A **history** is the list of probes made so far with their outcomes. After a history, let $S$ be the set of edges probed successfully, so that the current graph is $E\setminus S$; a failed edge stays in the graph and cannot be probed again. The **probable edges** are the unprobed edges of $R(E\setminus S)$ whose cost $\tau_e$ the leftover budget can pay for; every probe pays its cost, on success and on failure.
--
--   A deterministic **policy** maps a history to the next probe or to "stop", and is **valid** if along every run each probe is of a probable edge. Given independent $\Omega_e\sim\mathrm{Bernoulli}(p_e)$, its **expected total reward** is
--
--   $$W(\pi)=\mathbb E\Big[\sum_{e\in E}w_e\mathbf 1\{\pi\text{ successfully probes }e\}\Big].$$
--
--   **Formalization Note** The expectation is the finite sum over joint outcomes $\omega$ of $\prod_{e\in E}p_e^{\omega_e}(1-p_e)^{1-\omega_e}$ times the reward on $\omega$. The display on p.1 omits $w_e$; the sentence before it and Lemma 11 (p.7) include it, and so does this definition. A valid policy has stopped after $|E|$ moves.
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), §1, p.1; §3, p.7, X(H, F, T)

import Definitions.Def_DataValidation_Instance

set_option autoImplicit false

namespace DataValidation

namespace Instance

variable (I : Instance)

/-- An edge position of the instance. -/
abbrev Edge : Type := Fin I.n × Fin I.n

/-- A **history**: the probes made so far with their outcomes, oldest first (`true` = success). -/
abbrev History : Type := List (I.Edge × Bool)

/-- A joint outcome of the variables `Ω_e`, `e ∈ E` (`true` means `Ω_e = 1`). -/
abbrev Outcome : Type := {e // e ∈ I.E} → Bool

/-- A deterministic **adaptive policy**: from what it has seen, the next probe, or `none` to stop.
Depending on the history only, it cannot see an outcome before the probe. -/
abbrev Policy : Type := I.History → Option I.Edge

variable {I}

/-- The edges probed successfully in a history; these are the edges removed from the graph. -/
def successes (h : I.History) : Finset I.Edge :=
  ((h.filter (·.2)).map (·.1)).toFinset

/-- The edges probed in a history, with either outcome. -/
def probed (h : I.History) : Finset I.Edge :=
  (h.map (·.1)).toFinset

/-- The budget spent in a history: every probe pays `τ_e`, on success and on failure. -/
def spent (h : I.History) : ℕ :=
  (h.map fun x => I.τ x.1).sum

/-- The **probable edges** after a history: the unprobed edges of the transitive reduction of the
current graph that the leftover budget can pay for. arXiv:2611.06773 (sha256 6595f819…), §1, p.1:
"e stays in E and cannot be probed anymore", "an edge can only be probed if it lies in the transitive
reduction of E"; §3, p.7, `X(H, F, T) = R(H ∪ F) ∩ {e ∈ H : τ_e ≤ T}`.

**Formalization Note.** A failed edge stays in the current graph `E ∖ successes h`, the page's
`H ∪ F`. The test `spent h + τ_e ≤ T` is the page's `τ_e ≤` leftover budget without a subtraction. -/
noncomputable def probable (h : I.History) : Finset I.Edge :=
  (transReduction (I.E \ successes h)).filter fun e =>
    e ∉ probed h ∧ spent h + I.τ e ≤ I.T

/-- One move of a policy on a history, the outcome of a probed edge being read from `ω`. -/
def step (π : I.Policy) (ω : I.Outcome) (h : I.History) : I.History :=
  match π h with
  | none => h
  | some e => if he : e ∈ I.E then h ++ [(e, ω ⟨e, he⟩)] else h

/-- The history after `k` moves of `π` on the outcome `ω`. -/
def run (π : I.Policy) (ω : I.Outcome) : ℕ → I.History
  | 0 => []
  | k + 1 => step π ω (run π ω k)

/-- `π` is **valid**: along every run, every probe it makes is of a probable edge. The obligation to
halt, arXiv:2611.06773 (sha256 6595f819…), §1, p.1, is the case where no edge is probable.

**Formalization Note.** Returning `none` early is allowed; the page says when a policy must halt, not
that it may not halt sooner, and `w ≥ 0`. The page's "τ_e > T for any unprobed edge" is read through
`X(H, F, T)` on p.7, as "for all". -/
def IsValidPolicy (π : I.Policy) : Prop :=
  ∀ (ω : I.Outcome) (k : ℕ) (e : I.Edge),
    π (run π ω k) = some e → e ∈ probable (run π ω k)

/-- The complete history of `π` on `ω`. A valid policy probes every edge at most once, so it has
stopped after `|E|` moves. -/
def finalHistory (π : I.Policy) (ω : I.Outcome) : I.History :=
  run π ω I.E.card

/-- The total weight collected by `π` on `ω`: the sum of `w_e` over the edges probed successfully. -/
def rewardOf (π : I.Policy) (ω : I.Outcome) : ℕ :=
  ∑ e ∈ successes (finalHistory π ω), I.w e

/-- The probability of the joint outcome `ω` when the `Ω_e ∼ Bernoulli(p_e)` are mutually independent.
arXiv:2611.06773 (sha256 6595f819…), §1, p.1. -/
noncomputable def outcomeProb (ω : I.Outcome) : ℝ :=
  ∏ e : {e // e ∈ I.E}, if ω e then (I.p e : ℝ) else 1 - (I.p e : ℝ)

/-- The **expected total reward** `W(π) = E[∑_{e ∈ E} w_e 1{π successfully probes e}]`.
arXiv:2611.06773 (sha256 6595f819…), §1, p.1, with Lemma 11, p.7, for the weight.

**Formalization Note.** The display on p.1 omits `w_e`; the sentences around it ("we collect w_e as a
reward") and Lemma 11's profit `∑_e w_e P(A_{e,π} ∩ B_e)` include it, and so does this definition. The
expectation is a finite sum over joint outcomes. -/
noncomputable def W (π : I.Policy) : ℝ :=
  ∑ ω : I.Outcome, outcomeProb ω * (rewardOf π ω : ℝ)

end Instance

end DataValidation


