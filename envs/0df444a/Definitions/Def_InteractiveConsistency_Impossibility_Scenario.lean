-- Prove2me | Definitions.Def_InteractiveConsistency_Impossibility_Scenario
-- name    : InteractiveConsistency_Impossibility_Scenario
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:09.26932+00:00
-- url     : https://prove2.me/theorems/b0458fec-a312-4e72-978a-d77e9cbe246d
-- title:
--   Section 4 (p. 232) — scenarios, p-scenarios, consistency with N, and assuring interactive consistency for m faults
-- statement:
--   Let $P$ be a finite set of processors, $n = |P|$, and $V$ a set of values. Write $P^*$ for the set of all strings over $P$ (the empty string included) and $P^+$ for the nonempty ones. A string $p_1p_2\cdots p_r$ records a chain of reports: $p_1$ says that $p_2$ said that $\dots$ that $p_r$'s private value is the recorded value.
--
--   1. A **scenario** is a map $\sigma : P^+ \to V$; $\sigma(p)$ is processor $p$'s private value, and $\sigma(p_1\cdots p_r)$ is the value $p_1$ received for the chain $p_2\cdots p_r$.
--   2. For $p\in P$, the **$p$-scenario** $\sigma_p$ is the restriction of $\sigma$ to strings beginning with $p$: everything $p$ knows or has heard.
--   3. For $N\subseteq P$ (the nonfaulty processors), $\sigma$ is **consistent with $N$** if
--   $$\sigma(pqw) = \sigma(qw)\qquad\text{for all } q\in N,\ p\in P,\ w\in P^*,$$
--   i.e. every processor in $N$ always reports truthfully what it knows or hears. Faulty processors are unconstrained.
--   4. A family $\{F_p \mid p\in P\}$, where $F_p(\sigma_p, q)\in V$ is the value $p$ computes for $q$ from its own $p$-scenario, **assures interactive consistency for $m$ faults** if for every $N\subseteq P$ with $|N|\ge n-m$ and every scenario $\sigma$ consistent with $N$:
--      - (i) $F_p(\sigma_p, q) = \sigma(q)$ for all $p, q\in N$;
--      - (ii) $F_p(\sigma_p, r) = F_q(\sigma_q, r)$ for all $p, q\in N$ and $r\in P$.
--
--   Clause (i) says that each nonfaulty processor computes the true private value of each nonfaulty processor; clause (ii) says that any two nonfaulty processors compute the same vector. These are the objects of the THEOREM of Section 4. Strings are of unbounded length, so no bound on the number of rounds of information exchange is built in.
--
--   **Formalization Note** Processors are a `Finset P` of a type with decidable equality; a string is a `List`, read left to right ($p_1$ is the list's head). A scenario is a total function on lists; its values on the empty list and on lists with a letter outside $P$ stand for nothing, and every condition quantifies only over strings whose letters lie in $P$. The $p$-scenario is presented as $w\mapsto\sigma(pw)$, and $F_p$ is only ever applied to it, never to $\sigma$. The quorum $|N|\ge n-m$ is written $|P|\le|N|+m$ to avoid truncated subtraction on natural numbers; $\sigma(q)$ is the value at the one-letter list $[q]$.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 232, Section 4 (definitions of scenario, p-scenario, consistency with N, and interactive consistency for m faults)

import Mathlib

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport, *Reaching agreement in the presence of faults*, J. ACM 27 (1980),
p. 232, Section 4: a string over `P`, i.e. a list all of whose letters lie in the processor set `P`.
The string `p₁p₂…p_r` of the paper is the list `[p₁, …, p_r]`, read left to right. The empty list
is the empty string, a member of `P*`. -/
def IsString {α : Type*} (P : Finset α) (w : List α) : Prop :=
  ∀ x ∈ w, x ∈ P

instance {α : Type*} [DecidableEq α] (P : Finset α) (w : List α) : Decidable (IsString P w) := by
  unfold IsString; infer_instance

/-- p. 232: the `p`-scenario `σ_p`, the restriction of the scenario `σ` to strings beginning with
`p`, presented as the map `w ↦ σ(p w)`. -/
def restrict {α V : Type*} (σ : List α → V) (p : α) : List α → V :=
  fun w => σ (p :: w)

/-- p. 232: the scenario `σ` is *consistent with* the set `N` of nonfaulty processors if for each
`q ∈ N`, `p ∈ P` and `w ∈ P*` (the empty string included), `σ(pqw) = σ(qw)`. -/
def ConsistentWith {α V : Type*} (P N : Finset α) (σ : List α → V) : Prop :=
  ∀ q ∈ N, ∀ p ∈ P, ∀ w : List α, IsString P w → σ (p :: q :: w) = σ (q :: w)

/-- p. 232: the family `{F_p | p ∈ P}` *assures interactive consistency for `m` faults* if for each
choice of `N ⊆ P` with `|N| ≥ n − m` (here `n = |P|`, written `|P| ≤ |N| + m`) and each scenario `σ`
consistent with `N`,
(i) for all `p, q ∈ N`, `F_p(σ_p, q) = σ(q)`, and
(ii) for all `p, q ∈ N` and `r ∈ P`, `F_p(σ_p, r) = F_q(σ_q, r)`.
`F p τ q` is the value processor `p` computes for `q` from the `p`-scenario `τ`; it is applied only
to `σ_p = restrict σ p`, never to `σ`. -/
def AssuresIC {α V : Type*} (P : Finset α) (m : ℕ) (F : α → (List α → V) → α → V) : Prop :=
  ∀ N : Finset α, N ⊆ P → P.card ≤ N.card + m →
    ∀ σ : List α → V, ConsistentWith P N σ →
      (∀ p ∈ N, ∀ q ∈ N, F p (restrict σ p) q = σ [q]) ∧
      (∀ p ∈ N, ∀ q ∈ N, ∀ r ∈ P, F p (restrict σ p) r = F q (restrict σ q) r)

end InteractiveConsistency.Impossibility


