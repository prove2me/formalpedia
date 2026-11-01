-- Prove2me | Definitions.Def_EntanglementParadigm_IsAchievableRate
-- name    : EntanglementParadigm_IsAchievableRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:46.671983+00:00
-- url     : https://prove2.me/theorems/408e0a48-2735-4f1d-aecb-0dc0c2b49563
-- title:
--   Achievable rate $Q$ for redistributing $\rho_A$ with side-information $\rho_{A'C}$
-- statement:
--   Let $\psi$ be a state on $B\otimes A'\otimes A\otimes C$. A real number $Q$ is an achievable rate for $\psi$ when, for every $\varepsilon,\delta>0$, there is $N$ such that for every block length $n\ge\max(N,1)$ there is a protocol with
--
--   $$
--   F\bigl(\text{output on }\psi^{\otimes n},\ \psi^{\otimes n}\bigr)\ge 1-\varepsilon,
--   \qquad
--   \log_2\dim Q_n\le n(Q+\delta).
--   $$
--
--   A protocol consists of an arbitrary finite shared density matrix on registers $T_A,T_B$, independent of $\psi$ and free of charge; a channel at the sender from $A^nA'^nT_A$ to a message register $Q_n$ and $A'^n$; and a channel at the receiver from $C^nQ_nT_B$ to $A^nC^n$. Bob's register $B^n$ is never acted on, and the fidelity compares the full state on $B^nA'^nA^nC^n$ with $\psi^{\otimes n}$. The paper's $Q_{A'C}$ is the infimum of the achievable rates.
--
--   This is the operational notion of rate: it quantifies over protocols, and no entropy formula enters.
--
--   **Formalization Note** Rates are in qubits (base 2). $F$ is the squared fidelity, which does not affect the limit. Nonnegativity of $Q$ is a consequence of $\log_2\dim Q_n\ge0$, so it is not a clause.
-- source:
--   J. Oppenheim, A paradigm for entanglement theory based on quantum communication, arXiv:0801.0458v1, p.2 ("let QA′C be the rate of quantum communication that is required"), p.3 ("Sending ρA is deemed successful if")

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P75

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)
open QAlgorithms.Papers.Independent.Intakenext100.P75 (Redistribution fullCopies fullTarget)

namespace EntanglementParadigm

/-- Oppenheim, arXiv:0801.0458v1, p.2 ("the rate of quantum communication that is required to
send `ρ_A` to a receiver who holds state `ρ_C` with `ρ_A′` being held by the sender") and p.3
(the success criterion): `Q` qubits per copy suffice to redistribute `ψ`. For every `ε, δ > 0`
and every large enough block length `n`, some protocol on `ψ^{⊗n}`, using a noiseless channel
and arbitrary shared assistance, reaches fidelity at least `1 - ε` on the whole state and sends
a message of at most `n (Q + δ)` qubits. The paper's `Q_{A′C}` is the infimum of these `Q`.

**Formalization Note.** Registers are ordered `B × (R × (A × C))`, with `R` the paper's `A′`.
`Redistribution` holds any finite shared density matrix, of any size and at no charge, a CPTP
encoder `A R T_A → Q R`, a CPTP decoder `C Q T_B → A C`, and leaves `B` untouched. Rates are in
qubits (`logb 2` of the message dimension); `fidelity` is squared, so the limit is unaffected.
Block lengths are `n ≥ 1`. No clause `0 ≤ Q` is needed: `p.cost ≥ 0` already forces it. -/
def IsAchievableRate {A B C R : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (ψ : Mat (B × (R × (A × C)))) (Q : ℝ) : Prop :=
  ∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
    ∃ p : Redistribution (Fin n → A) (Fin n → C) (Fin n → R),
      1 - ε ≤ fidelity (p.output (fullCopies ψ n)) (fullTarget (fullCopies ψ n)) ∧
      p.cost ≤ n * (Q + δ)

end EntanglementParadigm


