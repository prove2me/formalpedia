-- Prove2me | Definitions.Def_SatiaLave_MaxMin_Algorithm
-- name    : SatiaLave_MaxMin_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:37:19.605485+00:00
-- url     : https://prove2.me/theorems/9c024131-f0c5-476e-a040-c1b34a7e65ce
-- title:
--   Phases 1 and 2 of the max-min policy-iteration algorithm: the steps (6) and (7) and the Phase 1 stopping test
-- statement:
--   This file defines the two routines of Satia and Lave's max-min policy-iteration algorithm (p. 730), which modifies Howard's policy iteration.
--
--   **Phase 1 (policy evaluation, nature's routine).** Fix a policy $A$ and nature's current choice $P$, with present values $v^A$ solving (5). One iteration produces a new choice $P'$ whose row in each state $i$ at decision $A_i$ minimizes, as in (6),
--   $$\min_{p_i\in S_i^{A_i}}\ \sum_j p_{ij}\big(r^{A_i}_{ij}+\beta v_j^A\big)$$
--   (rows at other decisions are irrelevant to $A$ and unconstrained). The **stopping test** holds when the minimizing rows reproduce the current values,
--   $$\sum_j p'^{A}_{ij}\big(r^{A_i}_{ij}+\beta v^A_j\big)=v_i^A\qquad\text{for every state } i,$$
--   in which case the routine proceeds to Phase 2; otherwise it returns to (a) with $P=P'$.
--
--   **Phase 2 (policy improvement).** For a value vector $v$, the test quantity (7) of decision $k$ in state $i$ is
--   $$t_i^k(v)=\min_{p\in S_i^k}\ \sum_j p_j\big(r^k_{ij}+\beta v_j\big).$$
--   One iteration from policy $A$ to policy $B$ chooses, in every state $i$, a decision $B_i$ maximizing $t_i^k(\underline v(A))$ over $k$, where $\underline v(A)$ is nature's minimum for $A$ (the value Phase 1 delivers), and keeps $B_i=A_i$ whenever $A_i$ is already a maximizer. If $B\ne A$ the algorithm returns to Phase 1 with $A=B$; otherwise it terminates.
--
--   **Formalization Note.** Three readings are fixed here. (i) The stopping test on p. 730 is printed without the summation sign, "$p'^A_{ij}(r^A_{ij}+\beta v^A_j)=v^A_i$"; the sum over $j$ is meant, since $v_i^A$ is a sum over $j$ in (5). (ii) Phase 2 uses the exact value of Phase 1, nature's minimum $\underline v(A)$ (`robustValue M A`): the proofs of Propositions 3 and 5 take Phase 1's rows to be exact minimizers ("As $p^{*B}$ minimizes the return, given policy $B$", p. 731); Proposition 4 is the statement that Phase 1 reaches this value. (iii) The **retention rule** $B_i=A_i$ on ties is not printed; it is the rule of Howard's algorithm, which the paper says it modifies, and the proof of Proposition 5 ("the inequality holds for at least one $i$") needs it: without it two tied decisions can alternate forever. The Phase 2 display carries no number but is cited as (7) on pp. 731–732. Every minimum is an infimum over a nonempty compact set of a linear function, hence attained and never a junk value; a Phase 1 successor and a Phase 2 successor exist from every state of the algorithm.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 730, The Algorithm (Phase 1 (a), (b), Eq. (6); Phase 2, cited as (7) on pp. 731-732)

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model

namespace SatiaLave.MaxMin

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}

/-- One iteration of Phase 1, the policy-evaluation routine (Satia–Lave 1973, p. 730, (a)–(b)
and (6)), for a fixed policy `A`: starting from nature's current choice `P`, the new choice
`P'` uses, in every state `i`, a row `p_i'^A ∈ S_i^A` that minimizes
`Σ_j p_ij (r^A_ij + β v^A_j)` over `S_i^A`, where `v^A` is the present value of `A` under `P`.
Rows of `P'` at decisions other than `A i` are unconstrained. -/
def IsPhase1Step (M : UncertainMDP S D) (A : Policy S D) (P P' : Sel M) : Prop :=
  ∀ i, ∀ q ∈ M.U i (A i),
    ∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) ≤
      ∑ j, q j * (M.r i (A i) j + M.β * presentValue M A P j)

/-- The stopping test of Phase 1 (p. 730): the new rows reproduce the current present values,
`Σ_j p'^A_ij (r^A_ij + β v^A_j) = v^A_i` for every state `i`; then the routine proceeds to
Phase 2. -/
def Phase1Stops (M : UncertainMDP S D) (A : Policy S D) (P P' : Sel M) : Prop :=
  ∀ i, ∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) =
    presentValue M A P i

/-- The Phase 2 test quantity, cited as (7) (p. 730): for a value vector `v`, state `i` and
decision `k`, the minimum over `p ∈ S_i^k` of `Σ_j p_j (r^k_ij + β v_j)`. -/
noncomputable def test7 (M : UncertainMDP S D) (v : S → ℝ) (i : S) (k : D i) : ℝ :=
  ⨅ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * v j)

variable [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

/-- One iteration of Phase 2, the policy-improvement routine (p. 730), from policy `A` to
policy `B`, with Phase 1 taken to be exact (it returns nature's minimum `robustValue M A`):
in every state `i`, `B i` maximizes `test7 (robustValue M A) i k` over the decisions `k`, and
`B i = A i` whenever `A i` is itself a maximizer (the retention rule of Howard's algorithm). -/
def IsPhase2Step (M : UncertainMDP S D) (A B : Policy S D) : Prop :=
  ∀ i, test7 M (robustValue M A) i (B i) =
      (Finset.univ : Finset (D i)).sup' Finset.univ_nonempty (test7 M (robustValue M A) i) ∧
    (test7 M (robustValue M A) i (A i) =
        (Finset.univ : Finset (D i)).sup' Finset.univ_nonempty (test7 M (robustValue M A) i) →
      B i = A i)

end SatiaLave.MaxMin


