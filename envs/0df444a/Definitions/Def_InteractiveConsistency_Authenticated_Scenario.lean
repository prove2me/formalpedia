-- Prove2me | Definitions.Def_InteractiveConsistency_Authenticated_Scenario
-- name    : InteractiveConsistency_Authenticated_Scenario
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:30.690254+00:00
-- url     : https://prove2.me/theorems/da9334a6-7554-4e4c-85ea-507ffc18c659
-- title:
--   Section 5 — authenticated scenarios and consistency with nonfaulty processors
-- statement:
--   Let $P$ be the finite set of processors, $N\subseteq P$ the nonfaulty processors, and $V$ the set of private values. A scenario assigns each string of processor names either a value in $V$ or the marker NIL. Every processor's one-letter string has an actual private value, rather than NIL. Processor $p$ sees only the strings beginning with $p$; its view removes that leading $p$.
--
--   An $(m+1)$-level scenario is **authenticated and consistent with $N$** when, for every nonfaulty $p\in N$, every $q\in P$, and strings $w,w'$ over $P$ whose displayed left-hand sides have length at most $m+2$,
--
--   $$
--   \sigma(qpw)=\sigma(pw),\qquad
--   \sigma(w'pw)\in\{\sigma(pw),\mathrm{NIL}\}.
--   $$
--
--   The first condition states truthful forwarding by a nonfaulty processor. The second permits a message from a nonfaulty processor to be dropped, but not altered. These predicates specify the model used by the procedure and the mission's theorems.
--
--   **Formalization Note** Strings are lists read from receiver to originator. The scenario is a total function on lists, but the consistency conditions constrain only strings over $P$ of length at most $m+2$, which are the strings an $(m+1)$-level procedure can inspect. A private value is explicitly non-NIL.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), pp. 232–233, Section 4 definitions and Section 5 conditions (i)–(ii); https://doi.org/10.1145/322186.322188

import Mathlib
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- A private value is an actual value, rather than the NIL marker. -/
def IsAuthScenario {α V : Type*} (P : Finset α) (σ : List α → Option V) : Prop :=
  ∀ p ∈ P, σ [p] ≠ none

/-- The messages visible to receiver `p`, with the receiver's leading letter removed. -/
def view {α V : Type*} (σ : List α → Option V) (p : α) : List α → Option V :=
  fun w => σ (p :: w)

/-- Section 5's two authentication conditions, restricted to the strings in an
`(m + 1)`-level scenario. Such strings have length at most `m + 2`. -/
def AuthConsistent {α V : Type*} (P N : Finset α) (m : ℕ)
    (σ : List α → Option V) : Prop :=
  (∀ p ∈ N, ∀ q ∈ P, ∀ w : List α,
    (∀ x ∈ w, x ∈ P) → (q :: p :: w).length ≤ m + 2 →
      σ (q :: p :: w) = σ (p :: w)) ∧
  (∀ p ∈ N, ∀ w' w : List α,
    (∀ x ∈ w', x ∈ P) → (∀ x ∈ w, x ∈ P) →
      (w' ++ p :: w).length ≤ m + 2 →
        σ (w' ++ p :: w) = σ (p :: w) ∨
        σ (w' ++ p :: w) = none)

end InteractiveConsistency.Authenticated


