-- Prove2me | Definitions.Def_CLRS_Chapter4_Substitution
-- name    : CLRS_Chapter4_Substitution
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:02:14.722859+00:00
-- url     : https://prove2.me/theorems/7313f9c4-f3ea-431a-801e-f5a8df049a0d
-- title:
--   General discrete recurrences and substitution predicates
-- statement:
--   This bundle defines recurrence and candidate inequalities for natural-valued costs with finite ordered child lists, a natural cutoff, and natural tolls. SmallerChildren requires strictly smaller children above the cutoff; repeats retain multiplicity. Exact recurrence, upper and lower candidates, and natural-valued eventual Big-O, Big-Omega and theta use explicit positive natural constants and thresholds. The generic comparison theorems are separate nodes.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Substitution, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Substitution.lean

import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

/-!
CLRS §4.3: substitution as comparison with a proposed upper or lower bound.

Subproblem sizes are natural numbers; costs and tolls are natural-valued.
Every non-base problem has a finite list of strictly smaller children. The
number of children and their sizes may vary with the parent, and children need
not have equal sizes. Thus floor/ceiling splits, unequal splits, missing
branches, and repeated subproblems fit the same interface.

These theorems establish facts about numerical recurrences. Applying them to a
program additionally requires a proof connecting that program's charged cost
to the corresponding recurrence, as in the source-linked algorithm analyses.
-/
namespace Chapter4Substitution

/-- Sum the costs of a finite list of subproblems, preserving multiplicity. -/
def childSum (sizes : List Nat) (cost : Nat → Nat) : Nat :=
  (sizes.map cost).sum









/-- Every child of a non-base problem has a strictly smaller size. -/
def SmallerChildren (children : Nat → List Nat) (cutoff : Nat) : Prop :=
  ∀ n, cutoff ≤ n → ∀ child ∈ children n, child < n

/-- An upper recurrence inequality for the cost being analyzed. -/
def UpperRecurrence (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → cost n ≤ toll n + childSum (children n) cost

/-- A lower recurrence inequality for the cost being analyzed. -/
def LowerRecurrence (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → toll n + childSum (children n) cost ≤ cost n

/-- An exact recurrence above the base-case cutoff. -/
def ExactRecurrence (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → cost n = toll n + childSum (children n) cost

/-- Substituting a candidate upper bound makes the recurrence no larger
    than that candidate. This is often called a supersolution. -/
def UpperCandidate (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (candidate : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → toll n + childSum (children n) candidate ≤ candidate n

/-- Substituting a candidate lower bound makes the recurrence no smaller
    than that candidate. This is often called a subsolution. -/
def LowerCandidate (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (candidate : Nat → Nat) : Prop :=
  ∀ n, cutoff ≤ n → candidate n ≤ toll n + childSum (children n) candidate

























/-! Natural-valued asymptotic bounds. Constants and thresholds are natural
numbers; constants must be positive, and finitely many sizes below the threshold
are unrestricted. This API does not define real powers or assert a Master theorem. -/

/-- Eventually, f is bounded above by one positive constant multiple of g. -/
def IsBigO (f g : Nat → Nat) : Prop :=
  ∃ C N : Nat, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * g n



/-- Matching eventual upper and lower bounds for natural-valued costs. -/
def IsTheta (f g : Nat → Nat) : Prop := IsBigO f g ∧ IsBigO g f

























end Chapter4Substitution

end CLRS


