-- Prove2me | Definitions.Def_PricingWithTips3DM_06e60956ff918030951e5808
-- name    : PricingWithTips3DM_06e60956ff918030951e5808
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:18:02.438852+00:00
-- url     : https://prove2.me/theorems/b9dc3cb4-ec11-4ba4-8be3-7c14b53a9ee8
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Core
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Mathlib.Logic.Basic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Decision problems and many-one reductions

The foundational layer of the library: a `Problem` is simply a predicate on an
instance type, and a `Reduction` is a map between instance types together with a
proof that it preserves and reflects membership.

Deliberately absent: any notion of polynomial time. Certification that a
reduction map is computationally tame is layered on separately, as a syntactic
certificate (`Cert/Language.lean`, `Cert/Bridge.lean`), so that the
mathematical content of reductions is developed independently of it.

Restricted problems ("hard even if planar / regular / width ≤ 3") are handled
promise-free: `Problem.restrict` conjoins the side condition into the
predicate, `Reduction.codRestrict` strengthens a reduction whose outputs
satisfy the condition, and `Reduction.ofRestrict` recovers hardness of the
unrestricted problem from hardness of the restriction.
-/

namespace Hardness

universe u v w

/-- A decision problem over instances of type `α`: the set of yes-instances,
given as a predicate. -/
def Problem (α : Type u) : Type u := α → Prop

/-- A many-one reduction from `P` to `Q`: a map on instances that preserves and
reflects yes-instances. No resource bound is imposed here. -/
structure Reduction {α : Type u} {β : Type v} (P : Problem α) (Q : Problem β) where
  /-- The underlying map on instances. -/
  map : α → β
  /-- The map preserves and reflects yes-instances. -/
  correct : ∀ x, P x ↔ Q (map x)

@[inherit_doc] infixr:25 " ⟶ᵣ " => Reduction

namespace Reduction

variable {α : Type u} {β : Type v} {γ : Type w}
variable {P : Problem α} {Q : Problem β} {R : Problem γ}

/-- The identity reduction. -/
def id (P : Problem α) : P ⟶ᵣ P := ⟨fun x ↦ x, fun _ ↦ Iff.rfl⟩

/-- Composition of reductions. -/
def comp (r : P ⟶ᵣ Q) (s : Q ⟶ᵣ R) : P ⟶ᵣ R :=
  ⟨fun x ↦ s.map (r.map x), fun x ↦ (r.correct x).trans (s.correct _)⟩

@[simp] theorem comp_map (r : P ⟶ᵣ Q) (s : Q ⟶ᵣ R) (x : α) :
    (r.comp s).map x = s.map (r.map x) := rfl

end Reduction

/-- Pull back a problem along an interpretation map: `P.comap f` is the
problem on `β`-instances whose meaning is given by transporting to `α` via
`f`. Used to define concrete (encoded) versions of abstract problems. -/
def Problem.comap {α : Type u} {β : Type v} (P : Problem α) (f : β → α) : Problem β :=
  fun b ↦ P (f b)

/-- Restrict a problem to instances satisfying a side condition, in the
promise-free formulation: a yes-instance of `P.restrict R` is an instance
that satisfies `R` *and* is a yes-instance of `P`; an instance violating `R`
is simply a no-instance. No promise infects the instance type, so reductions
between restricted problems remain plain `Reduction`s.

"`P` is hard even if `R`" (Garey–Johnson's "remains NP-complete even if …")
is then a first-class statement: a reduction *into* `P.restrict R`. -/
def Problem.restrict {α : Type u} (P : Problem α) (R : α → Prop) : Problem α :=
  fun x ↦ R x ∧ P x

namespace Reduction

variable {α : Type u} {β : Type v} {P : Problem α} {Q : Problem β}

/-- Strengthen a reduction into a restriction of its target: if the map lands
in `R` on every input, then `P` reduces to `Q` even restricted to `R`. This is
the usual situation for gadget constructions, whose outputs satisfy the
restriction by construction. -/
def codRestrict (r : P ⟶ᵣ Q) (R : β → Prop) (h : ∀ x, R (r.map x)) :
    P ⟶ᵣ Q.restrict R :=
  ⟨r.map, fun x ↦
    ⟨fun hp ↦ ⟨h x, (r.correct x).mp hp⟩, fun hq ↦ (r.correct x).mpr hq.2⟩⟩

/-- Weakening: a restricted problem reduces to the unrestricted one — hardness
even-if implies plain hardness. Not by the identity map! `R x ∧ Q x ↔ Q x`
fails for yes-instances of `Q` violating `R`; the correct map keeps instances
satisfying `R` and sends the rest to a fixed no-instance. This requires the
restriction to be decidable — the classical requirement that promises be
checkable, falling out of the formalization by itself. -/
def ofRestrict {Q : Problem α} (R : α → Prop) [DecidablePred R]
    (no : α) (hno : ¬Q no) : Q.restrict R ⟶ᵣ Q where
  map x := if R x then x else no
  correct x := by
    by_cases h : R x
    · rw [if_pos h]
      exact ⟨fun hq ↦ hq.2, fun hq ↦ ⟨h, hq⟩⟩
    · rw [if_neg h]
      exact ⟨fun hq ↦ absurd hq.1 h, fun hq ↦ absurd hq hno⟩

end Reduction

/-- `P ≤ᵣ Q`: there exists a many-one reduction from `P` to `Q`. -/
def Reducible {α : Type u} {β : Type v} (P : Problem α) (Q : Problem β) : Prop :=
  Nonempty (P ⟶ᵣ Q)

@[inherit_doc] infix:50 " ≤ᵣ " => Reducible

theorem Reducible.trans {α : Type u} {β : Type v} {γ : Type w}
    {P : Problem α} {Q : Problem β} {R : Problem γ}
    (h₁ : P ≤ᵣ Q) (h₂ : Q ≤ᵣ R) : P ≤ᵣ R :=
  h₁.elim fun r ↦ h₂.elim fun s ↦ ⟨r.comp s⟩

end Hardness


