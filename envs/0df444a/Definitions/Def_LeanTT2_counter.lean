-- Prove2me | Definitions.Def_LeanTT2_counter
-- name    : LeanTT2_counter
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T02:15:45.992832+00:00
-- url     : https://prove2.me/theorems/c028526c-ed31-4943-a6c8-1dd7c977742b
-- title:
--   The counterexample data of thesis section 3.1: an undecidable equation and a non-transitive equality
-- statement:
--   The abstract counterexample data for the negative metatheory of thesis section 3.1. A Boolean step predicate P encodes a machine that halts exactly when P is false at some stage; a family accAt of propositions (an accessibility family) carries an initial proof acc0; and a function f maps a numeral and an accessibility proof to the unit type. The chain field asserts that the initial application of f is definitionally equal to the application at any later numeral with a suitable proof, the unfolding of page 16 of the thesis; if P k is false then the unfolding at k is definitionally the unit element; if P is always true then the initial application is not definitionally the unit element; and no Boolean is equivalent to the existence of a false step (the halting problem is undecidable). Additionally, three terms x, y, z of the unit type witness that the algorithmic equality of the kernel relates x to y and y to z, but not x to z.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, section 3.1 (pp. 16-17).

import Mathlib
import Definitions.Def_LeanTT2_frag

universe u

/-!
# The Type Theory of Lean, part II: the counterexample data of thesis section 3.1

The abstract counterexample data for the negative metatheory of Mario
Carneiro's thesis "The Type Theory of Lean" (Carnegie Mellon University,
2019), section 3.1 (pages 16 and 17). Thesis section 3.1 fixes a
decidable step predicate `P : ℕ → 2` (for example, "Turing machine M
runs for at least n steps without halting") and builds, in a context
carrying an accessibility proof for the non-well-founded relation `>`
on the naturals, a function `f` from numerals and accessibility proofs
to the unit type, which unfolds as
`f n (intro_acc n h) ↦* if P n then f (n+1) (h (n+1) (p n)) else ()`.
Definitional equality ignores the consistency of the context: by proof
irrelevance, the proof `a` of `acc_> 0` is definitionally equal to
`intro_acc 0 (inv_0 a)`, so `f 0 a` is definitionally equal to
`f k h` for every k and a suitable proof h; if the machine halts (some
`P k` is false) the chain reaches the unit element, and if the machine
never halts (`P k` is always true) it never does. Hence the ideal
definitional equality decides the halting of M, and is undecidable.

The structure `Counter` packages this construction abstractly: the
step predicate `P`, the numerals, the accessibility family `accAt`
with its proofs, the function `f` with its typing, the unfolding chain
of page 16, the halting dichotomy, and the assumption that no Boolean
decides the halting of `P`. The remaining fields `x`, `y`, `z` are the
witnesses of thesis section 3.1.1 (page 17): the algorithmic equality of
the kernel relates `x` to `y` and `y` to `z` but not `x` to `z`, the
"creative middle step" of the unfolding. The theorems of the mission
extract the negative conclusions (non-transitivity, failure of subject
reduction, undecidability) from this interface.
-/

namespace LeanTT2

/-- The counterexample data of thesis section 3.1: a halting instance
encoded by a Boolean step predicate `P` with numerals `num`, an
accessibility family `accAt` of propositions with an initial proof
`acc0`, and a function `f` mapping a numeral and an accessibility
proof to the unit type. The field `chain` records the unfolding of
page 16 (the initial application `f (num 0) acc0` is definitionally
equal to `f (num k) h` for every k with a suitable proof h); the fields
`step_false` and `no_unit` record the halting dichotomy (the chain
reaches the unit element exactly when the machine halts); the field
`hundec` records that no Boolean decides the halting of the machine;
and the fields `x`, `y`, `z` with `halg1`, `halg2`, `halg3` record the
non-transitivity of the algorithmic equality of thesis section 3.1.1.
-/
structure Counter (F : Frag.{u}) where
  /-- the defining context of the counterexample -/
  Γ : F.Ctx
  /-- the defining context is valid -/
  hΓ : F.ok Γ
  /-- the step predicate: P k is false exactly when the machine halts
  at or before step k -/
  P : ℕ → Bool
  /-- the numerals of the fragment -/
  num : ℕ → F.E
  /-- the accessibility family of the fragment, a proposition for each
  numeral -/
  accAt : ℕ → F.E
  /-- the accessibility family consists of propositions, so proof
  irrelevance applies to its proofs -/
  haccAt : ∀ k, F.isProp Γ (accAt k)
  /-- the initial accessibility proof -/
  acc0 : F.E
  /-- the initial proof proves accessibility at the initial numeral -/
  hacc0 : F.ty Γ acc0 (accAt 0)
  /-- the unfolding function of thesis section 3.1: a numeral and an
  accessibility proof produce an element of the unit type -/
  f : F.E
  /-- the unit type of the fragment -/
  unit : F.E
  /-- the unit type is a type -/
  hunit : F.isType Γ unit
  /-- the unfolding function is typed: for every numeral and every
  proof of accessibility at that numeral, the application lands in the
  unit type -/
  hf : ∀ k (h : F.E), F.ty Γ h (accAt k) →
    F.ty Γ (F.app (F.app f (num k)) h) unit
  /-- the unfolding chain of page 16: the initial application is
  definitionally equal to the application at any later numeral, with a
  suitable accessibility proof -/
  chain : ∀ k, ∃ h, F.ty Γ h (accAt k) ∧
    F.deq Γ (F.app (F.app f (num 0)) acc0) (F.app (F.app f (num k)) h)
  /-- if the machine halts, the chain reaches the unit element: at a
  false step the unfolding is definitionally the unit element -/
  step_false : ∀ k (h : F.E), F.ty Γ h (accAt k) → P k = false →
    F.deq Γ (F.app (F.app f (num k)) h) unit
  /-- if the machine never halts, the initial application is not
  definitionally the unit element -/
  no_unit : (∀ k, P k = true) →
    ¬ F.deq Γ (F.app (F.app f (num 0)) acc0) unit
  /-- the halting of the machine is undecidable: no Boolean is
  equivalent to the existence of a false step -/
  hundec : ∀ d : Bool, (d = true ↔ ∃ k, P k = false) → False
  /-- the first non-transitivity witness, the term f (num 0) acc0 of
  thesis section 3.1.1 -/
  x : F.E
  /-- the second non-transitivity witness, the creative middle step of
  the unfolding -/
  y : F.E
  /-- the third non-transitivity witness, the term f (num 1) (inv_0 a 1
  (p 0)) of thesis section 3.1.1 -/
  z : F.E
  /-- the first witness is typed at the unit type -/
  hx : F.ty Γ x unit
  /-- the second witness is typed at the unit type -/
  hy : F.ty Γ y unit
  /-- the third witness is typed at the unit type -/
  hz : F.ty Γ z unit
  /-- the algorithmic equality relates the first witness to the second -/
  halg1 : F.alg Γ x y
  /-- the algorithmic equality relates the second witness to the third -/
  halg2 : F.alg Γ y z
  /-- the algorithmic equality does not relate the first witness to
  the third: the algorithmic equality is not transitive -/
  halg3 : ¬ F.alg Γ x z

end LeanTT2


