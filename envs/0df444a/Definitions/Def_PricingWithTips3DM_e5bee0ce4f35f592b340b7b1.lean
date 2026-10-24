-- Prove2me | Definitions.Def_PricingWithTips3DM_e5bee0ce4f35f592b340b7b1
-- name    : PricingWithTips3DM_e5bee0ce4f35f592b340b7b1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:36:02.142617+00:00
-- url     : https://prove2.me/theorems/47ed9d2d-bac8-47f7-b980-a987d12cc573
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Sets.Matching3D.FromSat
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Definitions.Def_PricingWithTips3DM_259835d7bdacc7647a6f2f2b
import Definitions.Def_PricingWithTips3DM_ddcced5313ed447b67330e23
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# SAT → 3-dimensional matching

Garey–Johnson's three-part construction (§3.1.2), a genuinely multi-part
gadget. Given a CNF formula with clause count `m`
and a variable list of length `n`:

* a **truth-setting** component per variable slot: a `2m`-cycle of triples
  whose two perfect matchings are "all true" and "all false", releasing one
  of the two external elements `(i, j, true)`, `(i, j, false)` per clause
  index `j`;
* a **satisfaction-testing** component per clause: one triple per literal,
  all competing for the clause's private pair of internal elements, so the
  clause is covered exactly when one of its literals was released;
* a **garbage-collection** component: `m * n` further internal pairs, each
  joinable to *any* external element, absorbing the released elements that
  no clause consumed.

The construction works for arbitrary CNF formulas — clause width affects only
the size of the output. An empty clause yields an uncoverable testing pair,
matching its unsatisfiability.

## The dummy variable slot

Variable slots are `Fin (n + 1)`, one more than there are variables: slot `n`
is a dummy that no literal ever names. This buys two things. The slot map
`varSlot` becomes *total* — a literal whose variable is missing from the list
lands on the dummy — so no proof argument or `filterMap` infects the
definitions. And the garbage count comes out as exactly `m * n`, with no
truncated subtraction: the leftover external elements of clause `j` are those
of the `n` slots other than the one its chosen literal used, and the
bijection with `Fin n` is literally `Fin.succAbove`.
-/

namespace Hardness

namespace Sat3dm

variable {V : Type*}

/-! ## Element types -/

/-- The external elements (the `W` coordinate): a variable slot, a clause
index, and a polarity. These are the elements the three components compete
for; everything else is private to one component. -/
abbrev Ext (n m : ℕ) : Type := Fin (n + 1) × Fin m × Bool

/-- The internal elements (the `X` and `Y` coordinates): one per
(variable slot, clause) for the truth-setting rings, one per clause for
satisfaction testing, and `m * n` for garbage collection. -/
abbrev Slot (n m : ℕ) : Type := (Fin (n + 1) × Fin m) ⊕ Fin m ⊕ (Fin m × Fin n)

/-- A triple of the produced instance. -/
abbrev Trip (n m : ℕ) : Type := Ext n m × Slot n m × Slot n m

/-! The three element types are built from `Fin`, `Bool`, sums and products,
so their `Fintype` and `DecidableEq` instances exist; they are named here
because the nested product `Trip` exceeds the default instance-search size
budget when assembled from scratch at every use site. -/

instance instFintypeExt (n m : ℕ) : Fintype (Ext n m) := inferInstance
instance instDecidableEqExt (n m : ℕ) : DecidableEq (Ext n m) := inferInstance
instance instFintypeSlot (n m : ℕ) : Fintype (Slot n m) := inferInstance
instance instDecidableEqSlot (n m : ℕ) : DecidableEq (Slot n m) := inferInstance
instance instFintypeTrip (n m : ℕ) : Fintype (Trip n m) := inferInstance
instance instDecidableEqTrip (n m : ℕ) : DecidableEq (Trip n m) := inferInstance

/-! ## The cyclic successor on clause indices -/

/-- The cyclic successor on clause indices — the shift that closes each
truth-setting component into a ring. -/
def next {m : ℕ} (j : Fin m) : Fin m := ⟨(j.1 + 1) % m, Nat.mod_lt _ j.pos⟩

/-- Closed form of the cyclic successor: the ordinary successor, wrapping to
zero at the end. -/
theorem next_val {m : ℕ} (j : Fin m) :
    (next j).1 = if j.1 + 1 = m then 0 else j.1 + 1 := by
  have h0 : (next j).1 = (j.1 + 1) % m := rfl
  rw [h0]
  by_cases h : j.1 + 1 = m
  · rw [if_pos h, h, Nat.mod_self]
  · rw [if_neg h, Nat.mod_eq_of_lt (by have := j.isLt; omega)]

/-- The successor of a non-final index is the ordinary successor. -/
theorem next_val_of_lt {m : ℕ} (j : Fin m) (h : j.1 + 1 < m) :
    (next j).1 = j.1 + 1 := by
  rw [next_val, if_neg (by omega)]

/-- The cyclic successor is injective. -/
theorem next_injective {m : ℕ} : Function.Injective (next (m := m)) := by
  intro a b hab
  have ha := next_val a
  have hb := next_val b
  rw [hab] at ha
  have h1 := a.isLt
  have h2 := b.isLt
  refine Fin.ext ?_
  by_cases hA : a.1 + 1 = m <;> by_cases hB : b.1 + 1 = m
  · omega
  · rw [if_pos hA] at ha; rw [if_neg hB] at hb; omega
  · rw [if_neg hA] at ha; rw [if_pos hB] at hb; omega
  · rw [if_neg hA] at ha; rw [if_neg hB] at hb; omega

/-- The cyclic successor is surjective — this is what makes each ring's `Y`
elements exactly consumed by the "all false" matching. -/
theorem next_surjective {m : ℕ} : Function.Surjective (next (m := m)) :=
  Finite.surjective_of_injective next_injective

/-! ## The triples of the three components -/

section Triples

variable {n m : ℕ}

/-- The truth-setting triple of variable slot `i` at clause index `j`
belonging to the "`i` is true" matching of the ring: it consumes the
*negative* external element, leaving the positive one free. -/
def trueTrip (i : Fin (n + 1)) (j : Fin m) : Trip n m :=
  ((i, j, false), Sum.inl (i, j), Sum.inl (i, j))

/-- The truth-setting triple belonging to the "`i` is false" matching: it
consumes the positive external element and takes the *next* ring element in
the `Y` coordinate — the shift that closes the component into a cycle, so
that the two matchings are the only two ways to cover it. -/
def falseTrip (i : Fin (n + 1)) (j : Fin m) : Trip n m :=
  ((i, j, true), Sum.inl (i, j), Sum.inl (i, next j))

/-- The satisfaction-testing triple of a literal with slot `i` and polarity
`b` occurring in clause `j`: it consumes the external element that the
truth-setting ring of `i` releases exactly when the literal holds, together
with the clause's private pair of internal elements. -/
def testTrip (i : Fin (n + 1)) (j : Fin m) (b : Bool) : Trip n m :=
  ((i, j, b), Sum.inr (Sum.inl j), Sum.inr (Sum.inl j))

/-- The garbage-collection triple joining the internal pair `p` to an
arbitrary external element `w`. -/
def junkTrip (p : Fin m × Fin n) (w : Ext n m) : Trip n m :=
  (w, Sum.inr (Sum.inr p), Sum.inr (Sum.inr p))

/-! Triples of different components never coincide: the ring triples are
told apart by the polarity they consume, and the components by their
internal coordinates. -/

/-- A "true" and a "false" ring triple always differ — they consume opposite
polarities. -/
theorem trueTrip_ne_falseTrip (i i' : Fin (n + 1)) (j j' : Fin m) :
    trueTrip i j ≠ falseTrip i' j' := fun h ↦
  Bool.false_ne_true (congrArg (fun t ↦ t.1.2.2) h)

/-- A testing triple is never a ring triple: their `X` coordinates lie in
different summands. -/
theorem testTrip_ne_trueTrip (i i' : Fin (n + 1)) (j j' : Fin m) (b : Bool) :
    testTrip i j b ≠ trueTrip i' j' := fun h ↦ by
  exact absurd (congrArg (fun t ↦ t.2.1) h) (by simp [testTrip, trueTrip])

/-- A testing triple is never a ring triple. -/
theorem testTrip_ne_falseTrip (i i' : Fin (n + 1)) (j j' : Fin m) (b : Bool) :
    testTrip i j b ≠ falseTrip i' j' := fun h ↦ by
  exact absurd (congrArg (fun t ↦ t.2.1) h) (by simp [testTrip, falseTrip])

end Triples

/-- The available triples of the produced instance: the truth-setting rings
of every variable slot, the testing triples of every literal occurrence, and
the garbage-collection pairs. -/
def tripleSet [DecidableEq V] (φ : CNF V) (vs : List V) :
    Finset (Trip vs.length φ.length) :=
  (Finset.univ.image fun p : Fin (vs.length + 1) × Fin φ.length ↦ trueTrip p.1 p.2) ∪
    (Finset.univ.image fun p : Fin (vs.length + 1) × Fin φ.length ↦ falseTrip p.1 p.2) ∪
    (Finset.univ.image fun o : φ.Occ ↦
      testTrip (varSlot vs (φ.occLit o).var) o.1 (φ.occLit o).polarity) ∪
    (Finset.univ.image fun q : (Fin φ.length × Fin vs.length) × Ext vs.length φ.length ↦
      junkTrip q.1 q.2)

variable [DecidableEq V] {φ : CNF V} {vs : List V}

/-- Membership in the triple set: a triple is available exactly when it is
one of the four kinds the construction emits. -/
theorem mem_tripleSet_iff (t : Trip vs.length φ.length) :
    t ∈ tripleSet φ vs ↔
      (∃ i j, t = trueTrip i j) ∨ (∃ i j, t = falseTrip i j) ∨
        (∃ o : φ.Occ, t = testTrip (varSlot vs (φ.occLit o).var) o.1 (φ.occLit o).polarity) ∨
          (∃ p w, t = junkTrip p w) := by
  simp only [tripleSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, eq_comm, or_assoc]

theorem trueTrip_mem_tripleSet (i : Fin (vs.length + 1)) (j : Fin φ.length) :
    trueTrip i j ∈ tripleSet φ vs :=
  (mem_tripleSet_iff _).mpr (Or.inl ⟨i, j, rfl⟩)

theorem falseTrip_mem_tripleSet (i : Fin (vs.length + 1)) (j : Fin φ.length) :
    falseTrip i j ∈ tripleSet φ vs :=
  (mem_tripleSet_iff _).mpr (Or.inr (Or.inl ⟨i, j, rfl⟩))

theorem testTrip_mem_tripleSet (o : φ.Occ) :
    testTrip (varSlot vs (φ.occLit o).var) o.1 (φ.occLit o).polarity ∈ tripleSet φ vs :=
  (mem_tripleSet_iff _).mpr (Or.inr (Or.inr (Or.inl ⟨o, rfl⟩)))

theorem junkTrip_mem_tripleSet (p : Fin φ.length × Fin vs.length)
    (w : Ext vs.length φ.length) : junkTrip p w ∈ tripleSet φ vs :=
  (mem_tripleSet_iff _).mpr (Or.inr (Or.inr (Or.inr ⟨p, w, rfl⟩)))

/-! ### Reading a triple off its internal coordinates

The `X` and `Y` coordinates of an available triple say which component it
belongs to; these three lemmas are the case analyses the correctness proof
runs on. -/

/-- An available triple whose `X` coordinate is the ring element `(i, j)` is
one of that ring position's two triples. -/
theorem eq_trueTrip_or_falseTrip {t : Trip vs.length φ.length} (ht : t ∈ tripleSet φ vs)
    {i : Fin (vs.length + 1)} {j : Fin φ.length} (hx : t.2.1 = Sum.inl (i, j)) :
    t = trueTrip i j ∨ t = falseTrip i j := by
  rcases (mem_tripleSet_iff t).mp ht with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨o, rfl⟩ | ⟨p, w, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Sum.inl.inj hx
    exact Or.inl rfl
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Sum.inl.inj hx
    exact Or.inr rfl
  · exact absurd hx (by simp [testTrip])
  · exact absurd hx (by simp [junkTrip])

/-- An available triple whose `X` coordinate is clause `j`'s testing element
is a testing triple of an occurrence in clause `j`. -/
theorem eq_testTrip {t : Trip vs.length φ.length} (ht : t ∈ tripleSet φ vs)
    {j : Fin φ.length} (hx : t.2.1 = Sum.inr (Sum.inl j)) :
    ∃ o : φ.Occ, o.1 = j ∧
      t = testTrip (varSlot vs (φ.occLit o).var) j (φ.occLit o).polarity := by
  rcases (mem_tripleSet_iff t).mp ht with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨o, rfl⟩ | ⟨p, w, rfl⟩
  · exact absurd hx (by simp [trueTrip])
  · exact absurd hx (by simp [falseTrip])
  · have ho : o.1 = j := Sum.inl.inj (Sum.inr.inj hx)
    exact ⟨o, ho, by rw [ho]⟩
  · exact absurd hx (by simp [junkTrip])

/-- An available triple whose `Y` coordinate is the ring element `(i, j)` is
either the "true" triple at `j` or the "false" triple one step back — the
step that the ring's shift introduces. -/
theorem eq_trueTrip_or_falseTrip_of_snd {t : Trip vs.length φ.length}
    (ht : t ∈ tripleSet φ vs) {i : Fin (vs.length + 1)} {j : Fin φ.length}
    (hy : t.2.2 = Sum.inl (i, j)) :
    t = trueTrip i j ∨ ∃ j', next j' = j ∧ t = falseTrip i j' := by
  rcases (mem_tripleSet_iff t).mp ht with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨o, rfl⟩ | ⟨p, w, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Sum.inl.inj hy
    exact Or.inl rfl
  · obtain ⟨rfl, hb⟩ := Prod.mk.injEq .. ▸ Sum.inl.inj hy
    exact Or.inr ⟨b, hb, rfl⟩
  · exact absurd hy (by simp [testTrip])
  · exact absurd hy (by simp [junkTrip])

/-! ## From a matching to a satisfying assignment

Only the truth-setting and satisfaction-testing components carry information
in this direction: the garbage-collection triples are never inspected. -/

section Backward

variable {M : Finset (Trip vs.length φ.length)}

/-- Each ring position's `X` element forces a choice between that position's
two triples. -/
theorem ring_exactly_one (hM : M ⊆ tripleSet φ vs)
    (hX : IsExactCover M (fun t ↦ t.2.1)) (i : Fin (vs.length + 1)) (j : Fin φ.length) :
    (trueTrip i j ∈ M ∧ falseTrip i j ∉ M) ∨ (trueTrip i j ∉ M ∧ falseTrip i j ∈ M) := by
  obtain ⟨t, ⟨htM, htx⟩, -⟩ := hX (Sum.inl (i, j))
  have hne : ¬(trueTrip i j ∈ M ∧ falseTrip i j ∈ M) := by
    rintro ⟨h1, h2⟩
    exact trueTrip_ne_falseTrip i i j j (hX.inj h1 h2 rfl)
  rcases eq_trueTrip_or_falseTrip (hM htM) htx with rfl | rfl
  · exact Or.inl ⟨htM, fun h ↦ hne ⟨htM, h⟩⟩
  · exact Or.inr ⟨fun h ↦ hne ⟨h, htM⟩, htM⟩

/-- Each ring position's `Y` element forces a choice between that position's
"true" triple and the *previous* position's "false" triple — the shift is
what couples consecutive positions. -/
theorem ring_exactly_one_snd (hM : M ⊆ tripleSet φ vs)
    (hY : IsExactCover M (fun t ↦ t.2.2)) (i : Fin (vs.length + 1))
    {j j' : Fin φ.length} (hj : next j' = j) :
    (trueTrip i j ∈ M ∧ falseTrip i j' ∉ M) ∨ (trueTrip i j ∉ M ∧ falseTrip i j' ∈ M) := by
  obtain ⟨t, ⟨htM, hty⟩, -⟩ := hY (Sum.inl (i, j))
  have hne : ¬(trueTrip i j ∈ M ∧ falseTrip i j' ∈ M) := by
    rintro ⟨h1, h2⟩
    refine trueTrip_ne_falseTrip i i j j' (hY.inj h1 h2 ?_)
    change (Sum.inl (i, j) : Slot _ _) = Sum.inl (i, next j')
    rw [hj]
  rcases eq_trueTrip_or_falseTrip_of_snd (hM htM) hty with rfl | ⟨j'', hj'', rfl⟩
  · exact Or.inl ⟨htM, fun h ↦ hne ⟨htM, h⟩⟩
  · obtain rfl : j'' = j' := next_injective (hj''.trans hj.symm)
    exact Or.inr ⟨fun h ↦ hne ⟨h, htM⟩, htM⟩

/-- **The ring lemma**: an exact cover must take either every "true" triple
of a truth-setting component or every "false" one. This is what makes the
component *set a truth value* — and it is the only place the cyclic shift is
used. -/
theorem all_trueTrip_or_all_falseTrip (hM : M ⊆ tripleSet φ vs)
    (hX : IsExactCover M (fun t ↦ t.2.1)) (hY : IsExactCover M (fun t ↦ t.2.2))
    (i : Fin (vs.length + 1)) :
    (∀ j, trueTrip i j ∈ M) ∨ (∀ j, falseTrip i j ∈ M) := by
  by_cases h0 : ∀ j : Fin φ.length, trueTrip i j ∈ M
  · exact Or.inl h0
  refine Or.inr ?_
  push Not at h0
  obtain ⟨j0, hj0⟩ := h0
  have hf0 : falseTrip i j0 ∈ M :=
    ((ring_exactly_one hM hX i j0).resolve_left fun h ↦ hj0 h.1).2
  -- consecutive positions agree, because they are coupled through the `Y`
  -- element they share
  have hstep : ∀ (k : ℕ) (h : k + 1 < φ.length),
      (falseTrip i ⟨k, by omega⟩ ∈ M ↔ falseTrip i ⟨k + 1, h⟩ ∈ M) := by
    intro k h
    have hk : k < φ.length := by omega
    have hnext : next (⟨k, hk⟩ : Fin φ.length) = ⟨k + 1, h⟩ :=
      Fin.ext (next_val_of_lt _ h)
    have hA := ring_exactly_one hM hX i ⟨k + 1, h⟩
    have hB := ring_exactly_one_snd hM hY i hnext
    tauto
  -- hence all positions agree with position zero
  have hzero : ∀ (k : ℕ) (h : k < φ.length),
      (falseTrip i ⟨k, h⟩ ∈ M ↔ falseTrip i ⟨0, j0.pos⟩ ∈ M) := by
    intro k
    induction k with
    | zero => intro _; exact Iff.rfl
    | succ k ih => intro h; exact (hstep k h).symm.trans (ih (by omega))
  intro j
  exact (hzero j.1 j.isLt).mpr ((hzero j0.1 j0.isLt).mp hf0)

/-- The assignment read off a matching: a variable is true exactly when its
truth-setting component took the "true" matching. -/
def assignmentOfMatching (M : Finset (Trip vs.length φ.length)) (v : V) : Bool :=
  decide (∀ j, trueTrip (varSlot vs v) j ∈ M)

/-- A matching satisfies the formula: each clause's testing element must be
covered by one of its literals' triples, and that literal's external element
is then unavailable to the truth-setting component, pinning the ring to the
matching that makes the literal hold. -/
theorem sat_assignmentOfMatching (hM : M ⊆ tripleSet φ vs)
    (hW : IsExactCover M (fun t ↦ t.1)) (hX : IsExactCover M (fun t ↦ t.2.1))
    (hY : IsExactCover M (fun t ↦ t.2.2)) : φ.Sat (assignmentOfMatching M) := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  -- the clause's private testing element is covered, necessarily by a
  -- testing triple of one of its own literals
  obtain ⟨t, ⟨htM, htx⟩, -⟩ := hX (Sum.inr (Sum.inl ⟨j, hj⟩))
  obtain ⟨⟨i, p⟩, ho, rfl⟩ := eq_testTrip (hM htM) htx
  obtain rfl : i = ⟨j, hj⟩ := ho
  set l : Literal V := φ.occLit ⟨⟨j, hj⟩, p⟩ with hl
  refine ⟨l, φ.occLit_mem _, ?_⟩
  -- the testing triple owns the external element `(varSlot l.var, j, l.polarity)`
  change decide (∀ j, trueTrip (varSlot vs l.var) j ∈ M) = l.polarity
  rcases all_trueTrip_or_all_falseTrip hM hX hY (varSlot vs l.var) with hall | hall
  · -- the ring took "true", so the polarity must be positive
    have hpol : l.polarity = true := by
      by_contra hcon
      rw [Bool.not_eq_true] at hcon
      refine testTrip_ne_trueTrip (varSlot vs l.var) (varSlot vs l.var) ⟨j, hj⟩ ⟨j, hj⟩
        l.polarity (hW.inj htM (hall ⟨j, hj⟩) ?_)
      change ((varSlot vs l.var, (⟨j, hj⟩ : Fin φ.length), l.polarity) : Ext _ _)
        = (varSlot vs l.var, ⟨j, hj⟩, false)
      rw [hcon]
    rw [hpol]
    exact decide_eq_true hall
  · -- the ring took "false", so the polarity must be negative
    have hpol : l.polarity = false := by
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      refine testTrip_ne_falseTrip (varSlot vs l.var) (varSlot vs l.var) ⟨j, hj⟩ ⟨j, hj⟩
        l.polarity (hW.inj htM (hall ⟨j, hj⟩) ?_)
      change ((varSlot vs l.var, (⟨j, hj⟩ : Fin φ.length), l.polarity) : Ext _ _)
        = (varSlot vs l.var, ⟨j, hj⟩, true)
      rw [hcon]
    rw [hpol]
    refine decide_eq_false fun hcon ↦ ?_
    exact (ring_exactly_one hM hX (varSlot vs l.var) ⟨j, hj⟩).elim
      (fun h ↦ h.2 (hall ⟨j, hj⟩)) fun h ↦ h.1 (hcon ⟨j, hj⟩)

end Backward

/-! ## From a satisfying assignment to a matching

The assignment fixes each ring's matching; each clause contributes the
testing triple of one holding literal; and the garbage-collection pairs mop
up the released external elements that no clause took. The three exact-cover
properties hold for an *arbitrary* choice of clause slots — only the
containment `matchingOf ⊆ tripleSet` needs the slots to come from real
literals. -/

section Forward

section Ring

variable {n m : ℕ}

/-- The ring triple a truth value selects: the "true" triple when the slot is
true, the "false" one otherwise. -/
def ringTrip (b : Bool) (i : Fin (n + 1)) (j : Fin m) : Trip n m :=
  if b then trueTrip i j else falseTrip i j

/-- The selected ring triple consumes the external element of the *opposite*
polarity — which is exactly why the agreeing one is left free for a clause. -/
theorem ringTrip_fst (b : Bool) (i : Fin (n + 1)) (j : Fin m) :
    (ringTrip b i j).1 = (i, j, !b) := by cases b <;> rfl

theorem ringTrip_snd_fst (b : Bool) (i : Fin (n + 1)) (j : Fin m) :
    (ringTrip b i j).2.1 = Sum.inl (i, j) := by cases b <;> rfl

theorem ringTrip_snd_snd (b : Bool) (i : Fin (n + 1)) (j : Fin m) :
    (ringTrip b i j).2.2 = Sum.inl (i, if b then j else next j) := by cases b <;> rfl

end Ring

theorem ringTrip_mem_tripleSet (b : Bool) (i : Fin (vs.length + 1)) (j : Fin φ.length) :
    ringTrip b i j ∈ tripleSet φ vs := by
  cases b
  · exact falseTrip_mem_tripleSet i j
  · exact trueTrip_mem_tripleSet i j

/-- The matching assembled from an assignment `σ` and a choice `pick` of one
variable slot per clause: every ring takes the matching `σ` dictates, every
clause takes the testing triple at its chosen slot, and the garbage pair
`(j, i')` takes the external element of clause `j` at the `i'`-th slot *other
than* `pick j` — which `Fin.succAbove` enumerates exactly. -/
def matchingOf (vs : List V) (σ : V → Bool) {φ : CNF V}
    (pick : Fin φ.length → Fin (vs.length + 1)) : Finset (Trip vs.length φ.length) :=
  (Finset.univ.image fun p : Fin (vs.length + 1) × Fin φ.length ↦
      ringTrip (slotValue vs σ p.1) p.1 p.2) ∪
    (Finset.univ.image fun j : Fin φ.length ↦
      testTrip (pick j) j (slotValue vs σ (pick j))) ∪
    (Finset.univ.image fun q : Fin φ.length × Fin vs.length ↦
      junkTrip q ((pick q.1).succAbove q.2, q.1,
        slotValue vs σ ((pick q.1).succAbove q.2)))

variable {σ : V → Bool} {pick : Fin φ.length → Fin (vs.length + 1)}

/-- The external element the garbage pair `q` absorbs. -/
def junkExt (vs : List V) (σ : V → Bool) {φ : CNF V}
    (pick : Fin φ.length → Fin (vs.length + 1)) (q : Fin φ.length × Fin vs.length) :
    Ext vs.length φ.length :=
  ((pick q.1).succAbove q.2, q.1, slotValue vs σ ((pick q.1).succAbove q.2))

omit [DecidableEq V] in
theorem mem_matchingOf {t : Trip vs.length φ.length} :
    t ∈ matchingOf vs σ pick ↔
      (∃ i j, t = ringTrip (slotValue vs σ i) i j) ∨
        (∃ j, t = testTrip (pick j) j (slotValue vs σ (pick j))) ∨
          ∃ q, t = junkTrip q (junkExt vs σ pick q) := by
  simp only [matchingOf, junkExt, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, Prod.exists, eq_comm, or_assoc]

omit [DecidableEq V] in
/-- The `X` coordinates are covered exactly: each ring element belongs to one
ring position, each testing element to one clause, each garbage element to
one pair. -/
theorem isExactCover_matchingOf_snd_fst :
    IsExactCover (matchingOf vs σ pick) (fun t ↦ t.2.1) := by
  rw [isExactCover_iff]
  refine ⟨?_, ?_⟩
  · rintro (⟨i, j⟩ | j | q)
    · exact ⟨_, mem_matchingOf.mpr (Or.inl ⟨i, j, rfl⟩), ringTrip_snd_fst _ i j⟩
    · exact ⟨_, mem_matchingOf.mpr (Or.inr (Or.inl ⟨j, rfl⟩)), rfl⟩
    · exact ⟨_, mem_matchingOf.mpr (Or.inr (Or.inr ⟨q, rfl⟩)), rfl⟩
  · rintro t₁ h₁ t₂ h₂ heq
    rcases mem_matchingOf.mp h₁ with ⟨i₁, j₁, rfl⟩ | ⟨j₁, rfl⟩ | ⟨q₁, rfl⟩ <;>
      rcases mem_matchingOf.mp h₂ with ⟨i₂, j₂, rfl⟩ | ⟨j₂, rfl⟩ | ⟨q₂, rfl⟩ <;>
        simp only [ringTrip_snd_fst, testTrip, junkTrip, Sum.inl.injEq, Sum.inr.injEq,
          Prod.mk.injEq, reduceCtorEq] at heq <;>
        (obtain ⟨rfl, rfl⟩ := heq; rfl)

omit [DecidableEq V] in
/-- The `Y` coordinates are covered exactly. The ring elements are the
interesting case: a "true" ring covers them on the nose, a "false" ring
covers them through the shift, which is a bijection. -/
theorem isExactCover_matchingOf_snd_snd :
    IsExactCover (matchingOf vs σ pick) (fun t ↦ t.2.2) := by
  rw [isExactCover_iff]
  refine ⟨?_, ?_⟩
  · rintro (⟨i, j⟩ | j | q)
    · by_cases hb : slotValue vs σ i = true
      · exact ⟨_, mem_matchingOf.mpr (Or.inl ⟨i, j, rfl⟩), by
          rw [ringTrip_snd_snd, if_pos hb]⟩
      · obtain ⟨j', hj'⟩ := next_surjective j
        exact ⟨_, mem_matchingOf.mpr (Or.inl ⟨i, j', rfl⟩), by
          rw [ringTrip_snd_snd, if_neg hb, hj']⟩
    · exact ⟨_, mem_matchingOf.mpr (Or.inr (Or.inl ⟨j, rfl⟩)), rfl⟩
    · exact ⟨_, mem_matchingOf.mpr (Or.inr (Or.inr ⟨q, rfl⟩)), rfl⟩
  · rintro t₁ h₁ t₂ h₂ heq
    rcases mem_matchingOf.mp h₁ with ⟨i₁, j₁, rfl⟩ | ⟨j₁, rfl⟩ | ⟨q₁, rfl⟩ <;>
      rcases mem_matchingOf.mp h₂ with ⟨i₂, j₂, rfl⟩ | ⟨j₂, rfl⟩ | ⟨q₂, rfl⟩ <;>
        simp only [ringTrip_snd_snd, testTrip, junkTrip, Sum.inl.injEq, Sum.inr.injEq,
          Prod.mk.injEq, reduceCtorEq] at heq <;>
        first
          | (obtain rfl := heq; rfl)
          | skip
    -- the ring/ring case: equal slots, then equal positions before or after
    -- the shift
    obtain ⟨rfl, hj⟩ := heq
    by_cases hb : slotValue vs σ i₁ = true
    · rw [if_pos hb, if_pos hb] at hj
      rw [hj]
    · rw [if_neg hb, if_neg hb] at hj
      rw [next_injective hj]

omit [DecidableEq V] in
/-- The `W` coordinates are covered exactly. Every triple in the matching
consumes the external element `(i, j, slotValue i)` — the one its slot's
assignment *agrees* with — except the ring triples, which consume the
disagreeing one; that single bit is what separates the three components. -/
theorem isExactCover_matchingOf_fst :
    IsExactCover (matchingOf vs σ pick) (fun t ↦ t.1) := by
  rw [isExactCover_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, j, b⟩
    by_cases hb : b = slotValue vs σ i
    · by_cases hi : i = pick j
      · refine ⟨_, mem_matchingOf.mpr (Or.inr (Or.inl ⟨j, rfl⟩)), ?_⟩
        change ((pick j, j, slotValue vs σ (pick j)) : Ext _ _) = (i, j, b)
        rw [hb, hi]
      · obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hi
        refine ⟨_, mem_matchingOf.mpr (Or.inr (Or.inr ⟨(j, i'), rfl⟩)), ?_⟩
        change junkExt vs σ pick (j, i') = (i, j, b)
        rw [junkExt, hb]
        simp only [hi']
    · refine ⟨_, mem_matchingOf.mpr (Or.inl ⟨i, j, rfl⟩), ?_⟩
      rw [ringTrip_fst]
      have : (!slotValue vs σ i) = b := by
        cases hbv : slotValue vs σ i <;> cases b <;> simp_all
      rw [this]
  · rintro t₁ h₁ t₂ h₂ heq
    rcases mem_matchingOf.mp h₁ with ⟨i₁, j₁, rfl⟩ | ⟨j₁, rfl⟩ | ⟨q₁, rfl⟩ <;>
      rcases mem_matchingOf.mp h₂ with ⟨i₂, j₂, rfl⟩ | ⟨j₂, rfl⟩ | ⟨q₂, rfl⟩ <;>
        simp only [ringTrip_fst, testTrip, junkTrip, junkExt, Prod.mk.injEq] at heq
    -- ring / ring
    · obtain ⟨rfl, rfl, -⟩ := heq
      rfl
    -- ring / testing: the polarities disagree by construction
    · obtain ⟨hi, -, hbad⟩ := heq
      rw [hi] at hbad
      simp at hbad
    -- ring / garbage
    · obtain ⟨hi, -, hbad⟩ := heq
      rw [hi] at hbad
      simp at hbad
    -- testing / ring
    · obtain ⟨hi, -, hbad⟩ := heq
      rw [hi] at hbad
      simp at hbad
    -- testing / testing
    · obtain ⟨-, rfl, -⟩ := heq
      rfl
    -- testing / garbage: a slot is never `succAbove` of itself
    · obtain ⟨hpick, hj, -⟩ := heq
      rw [hj] at hpick
      exact absurd hpick.symm (Fin.succAbove_ne _ _)
    -- garbage / ring
    · obtain ⟨hi, -, hbad⟩ := heq
      rw [hi] at hbad
      simp at hbad
    -- garbage / testing
    · obtain ⟨hpick, hj, -⟩ := heq
      rw [hj] at hpick
      exact absurd hpick (Fin.succAbove_ne _ _)
    -- garbage / garbage
    · obtain ⟨hsucc, hj, -⟩ := heq
      have hq : q₁ = q₂ := by
        refine Prod.ext hj (Fin.succAbove_right_injective (p := pick q₁.1) ?_)
        rw [hsucc, hj]
      rw [hq]

/-- The assembled matching uses only available triples, provided every
clause's chosen slot really is the slot of one of its literals, carrying the
polarity the assignment gives it. -/
theorem matchingOf_subset
    (h : ∀ j : Fin φ.length, ∃ o : φ.Occ, o.1 = j ∧
      varSlot vs (φ.occLit o).var = pick j ∧
        (φ.occLit o).polarity = slotValue vs σ (pick j)) :
    matchingOf vs σ pick ⊆ tripleSet φ vs := by
  intro t ht
  rcases mem_matchingOf.mp ht with ⟨i, j, rfl⟩ | ⟨j, rfl⟩ | ⟨q, rfl⟩
  · exact ringTrip_mem_tripleSet _ i j
  · obtain ⟨o, ho, hvar, hpol⟩ := h j
    have hmem := testTrip_mem_tripleSet (vs := vs) o
    rwa [hvar, hpol, ho] at hmem
  · exact junkTrip_mem_tripleSet q _


end Forward


/-! ## Correctness -/

/-- **The mathematical content of the reduction**: a CNF formula is
satisfiable exactly when the three-component triple set built over any
variable list covering it contains a matching.

The variable list is a parameter rather than `cnfVars φ` so that the
certificate may supply the list its own deduplication produces; all that is
required of it is that it name every variable of the formula. -/
theorem satisfiable_iff_exists_matching (φ : CNF V) (vs : List V)
    (hvs : ∀ c ∈ φ, ∀ l ∈ c, l.var ∈ vs) :
    φ.Satisfiable ↔
      ∃ M ⊆ tripleSet φ vs, IsExactCover M (fun t ↦ t.1) ∧
        IsExactCover M (fun t ↦ t.2.1) ∧ IsExactCover M (fun t ↦ t.2.2) := by
  constructor
  · rintro ⟨σ, hσ⟩
    -- pick a holding literal in each clause, as an occurrence
    have hch : ∀ j : Fin φ.length, ∃ p : Fin (φ[j.1]'j.isLt).length,
        (φ.occLit ⟨j, p⟩).Holds σ := by
      intro j
      obtain ⟨l, hl, hh⟩ := hσ _ (List.getElem_mem j.isLt)
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hl
      exact ⟨⟨p, hp⟩, hh⟩
    choose p hp using hch
    refine ⟨matchingOf vs σ fun j ↦ varSlot vs (φ.occLit ⟨j, p j⟩).var,
      matchingOf_subset ?_, isExactCover_matchingOf_fst,
      isExactCover_matchingOf_snd_fst, isExactCover_matchingOf_snd_snd⟩
    intro j
    refine ⟨⟨j, p j⟩, rfl, rfl, ?_⟩
    have hmem : (φ.occLit ⟨j, p j⟩).var ∈ vs :=
      hvs _ (List.getElem_mem j.isLt) _ (φ.occLit_mem _)
    rw [slotValue_varSlot hmem]
    exact (hp j).symm
  · rintro ⟨M, hM, hW, hX, hY⟩
    exact ⟨assignmentOfMatching M, sat_assignmentOfMatching hM hW hX hY⟩

end Sat3dm

open Sat3dm in
/-- The 3-dimensional matching instance built from a SAT instance: external
elements indexed by (variable slot, clause, polarity), internal elements by
the three components' private slots, and the triples of
`Sat3dm.tripleSet`. -/
def satToMatching3DInstance (x : SatInstance) : Matching3DInstance where
  W := Ext (cnfVars x.φ).length x.φ.length
  X := Slot (cnfVars x.φ).length x.φ.length
  Y := Slot (cnfVars x.φ).length x.φ.length
  triples := tripleSet x.φ (cnfVars x.φ)

/-- SAT reduces to 3-DIMENSIONAL MATCHING. -/
def satToMatching3D : SAT ⟶ᵣ MATCHING_3D where
  map := satToMatching3DInstance
  correct x :=
    Sat3dm.satisfiable_iff_exists_matching x.φ (cnfVars x.φ) fun _ hc _ hl ↦ mem_cnfVars hc hl

/-- 3SAT reduces to 3-DIMENSIONAL MATCHING, by weakening the source. -/
def sat3ToMatching3D : SAT3 ⟶ᵣ MATCHING_3D := sat3ToSat.comp satToMatching3D

end Hardness


