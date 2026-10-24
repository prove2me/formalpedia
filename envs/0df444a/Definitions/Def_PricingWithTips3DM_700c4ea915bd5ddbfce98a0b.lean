-- Prove2me | Definitions.Def_PricingWithTips3DM_700c4ea915bd5ddbfce98a0b
-- name    : PricingWithTips3DM_700c4ea915bd5ddbfce98a0b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:19:40.674259+00:00
-- url     : https://prove2.me/theorems/b9c8bd4b-45fc-4dcc-9fc8-d93ee28921ff
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Logic.OneInThree3Sat
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Definitions.Def_PricingWithTips3DM_559a735c0442b6eef1922892
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# ONE-IN-THREE 3SAT

Satisfaction with the demand made exact: an assignment must make **exactly
one** literal of each clause true. Garey–Johnson's [LO4], and the third
question this catalog asks of a width-3 CNF instance, beside 3SAT's *some*
(`Clause.Sat`) and NAE3SAT's *some but not all* (`Clause.Nae`).

What sets it apart from its two neighbours is the *absence* of a symmetry.
Not-all-equal satisfaction is invariant under complementing the assignment, so
its solutions come in pairs and a gadget may fix a distinguished variable
without loss of generality (`CNF.exists_naeSat_eq_false`). Exactly-one
satisfaction has no such invariance — complementing `(x, y, z)` with exactly
one true literal leaves two — so nothing here plays the role of
`CNF.naeSat_not`, and a gadget that wants a variable held false has to *force*
it, with clauses of its own (`falseBlock`, in `FromSat3.lean`). The pay-off of
the rigidity is that all-positive clauses already say something: three positive
literals with exactly one true is a set of size three covering one element,
which is why the monotone restriction is X3C in disguise.

Counting is over *positions*, so a clause repeating a literal counts it twice.
That is the reading under which the width-3 characterization `Clause.one_triple`
holds with no distinctness hypothesis, and it agrees with Garey–Johnson
wherever their clauses do, their `c ∈ C` being a three-element set of literals.

Hardness proof (in `OneInThree3Sat/`): from 3SAT (`FromSat3.lean`, Schaefer's
four-fresh-variable chain per clause; certified in `FromSat3/Code.lean` and
`FromSat3/Adequacy.lean`).
-/

namespace Hardness

variable {V W : Type*}

/-! ### Exactly-one satisfaction -/

/-- A clause is *exactly-one satisfied* when precisely one of its literals
holds. Note what this says about short clauses: the empty clause can never be
exactly-one satisfied, having nothing to be its true literal — which is what a
gadget uses to reject an input it must not answer for. -/
def Clause.One (σ : V → Bool) (c : Clause V) : Prop :=
  (c.countP fun l ↦ decide (l.Holds σ)) = 1

instance {σ : V → Bool} {c : Clause V} : Decidable (c.One σ) := by
  unfold Clause.One
  infer_instance

/-- Exactly-one satisfaction is stronger than satisfaction: one holding literal
is still a holding literal. -/
theorem Clause.One.sat {σ : V → Bool} {c : Clause V} (h : Clause.One σ c) :
    Clause.Sat σ c := by
  have hpos : 0 < c.countP fun l ↦ decide (l.Holds σ) := by
    have hone : (c.countP fun l ↦ decide (l.Holds σ)) = 1 := h
    omega
  obtain ⟨l, hl, hh⟩ := List.countP_pos_iff.mp hpos
  exact ⟨l, hl, of_decide_eq_true hh⟩

/-- Exactly-one satisfaction of a clause only depends on the assignment's
values at the variables of the clause. -/
theorem Clause.one_congr {c : Clause V} {τ τ' : V → Bool}
    (h : ∀ l ∈ c, τ l.var = τ' l.var) : Clause.One τ c ↔ Clause.One τ' c := by
  have hc : (c.countP fun l ↦ decide (l.Holds τ)) = c.countP fun l ↦ decide (l.Holds τ') :=
    List.countP_congr fun l hl ↦ by simpa using Literal.holds_congr (h l hl)
  unfold Clause.One
  rw [hc]

/-! ### The width-3 face

A clause of three literals is exactly-one satisfied when one of three cases
holds, and the three cases are a finite check on Booleans. `oneOf3` is that
check; every fact about a three-literal gadget clause is `decide`d through it,
which is how the case analysis a paper does on trust becomes machine-checked
exhaustion. -/

/-- Exactly one of three Booleans is `true`. -/
def oneOf3 (p q r : Bool) : Bool :=
  (p && !q && !r) || (!p && q && !r) || (!p && !q && r)

/-- **The width-3 characterization**: a three-literal clause is exactly-one
satisfied precisely when `oneOf3` accepts the three truth values. Counting over
positions is what makes this hold with no hypothesis relating the three
literals. -/
theorem Clause.one_triple {σ : V → Bool} (l₁ l₂ l₃ : Literal V) :
    Clause.One σ [l₁, l₂, l₃]
      ↔ oneOf3 (decide (l₁.Holds σ)) (decide (l₂.Holds σ))
          (decide (l₃.Holds σ)) = true := by
  unfold Clause.One
  simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
  cases decide (l₁.Holds σ) <;> cases decide (l₂.Holds σ) <;> cases decide (l₃.Holds σ) <;>
    simp [oneOf3]

/-- A positive literal's truth value is its variable's value — one of the two
faces a gadget clause presents to `oneOf3`, fresh variables always entering
positively. -/
theorem decide_holds_pos {σ : V → Bool} (v : V) :
    decide ((⟨v, true⟩ : Literal V).Holds σ) = σ v := by
  cases h : σ v <;> simp [Literal.Holds, h]

/-- A negated literal's truth value is the complement of the literal's — the
other face, a gadget reading an input literal negated. -/
theorem decide_holds_neg {σ : V → Bool} (l : Literal V) :
    decide (l.neg.Holds σ) = !decide (l.Holds σ) := by
  by_cases h : l.Holds σ
  · rw [decide_eq_true h, decide_eq_false fun hc ↦ (Literal.holds_neg.mp hc) h]
    rfl
  · rw [decide_eq_false h, decide_eq_true (Literal.holds_neg.mpr h)]
    rfl

/-- A three-literal clause is satisfied precisely when one of the three truth
values is `true` — the companion of `Clause.one_triple` on the source side of a
reduction, in the same Boolean form. -/
theorem Clause.sat_triple {σ : V → Bool} (l₁ l₂ l₃ : Literal V) :
    Clause.Sat σ [l₁, l₂, l₃]
      ↔ (decide (l₁.Holds σ) || decide (l₂.Holds σ) || decide (l₃.Holds σ)) = true := by
  simp [Clause.Sat, or_assoc]

/-! ### Formulas -/

/-- A formula is exactly-one satisfied if every clause is. -/
def CNF.OneSat (σ : V → Bool) (φ : CNF V) : Prop :=
  ∀ c ∈ φ, c.One σ

/-- A formula is exactly-one satisfiable if some assignment does it. -/
def CNF.OneSatisfiable (φ : CNF V) : Prop :=
  ∃ σ : V → Bool, φ.OneSat σ

/-! ### Relabeling

A counting predicate transports along a relabeling for the same reason a
counting objective does: the map carries the literals of a clause one for one,
so `List.countP_map` moves the count and `List.countP_congr` reads the two
predicates against each other literal by literal. Both directions of the
transport go through `Clause.one_map_relabel`; only the reflection direction
needs the labelling to separate the occurring variables, and it needs it only
through `CNF.exists_relabel_assignment`. -/

/-- Exactly-one satisfaction of a relabeled clause, against the assignment read
through the relabeling. Both directions of the transport are this lemma. -/
theorem Clause.one_map_relabel {f : V → W} {τ : W → Bool} {σ : V → Bool} {c : Clause V}
    (h : ∀ l ∈ c, τ (f l.var) = σ l.var) :
    Clause.One τ (c.map (Literal.relabel f)) ↔ Clause.One σ c := by
  have hc : ((c.map (Literal.relabel f)).countP fun l ↦ decide (l.Holds τ))
      = c.countP fun l ↦ decide (l.Holds σ) := by
    rw [List.countP_map]
    exact List.countP_congr fun l hl ↦ by simpa using Literal.holds_relabel (h l hl)
  unfold Clause.One
  rw [hc]

/-- Relabeling preserves and reflects exactly-one satisfiability as soon as the
map is injective *on the variables that occur*. The form the representation
theorem needs; gadget certificates use the corollary
`CNF.oneSatisfiable_relabel`. -/
theorem CNF.oneSatisfiable_relabel_of_injOn {f : V → W} {φ : CNF V}
    (hf : Set.InjOn f φ.vars) :
    (φ.relabel f).OneSatisfiable ↔ φ.OneSatisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨fun v ↦ τ (f v), fun c hc ↦
      (Clause.one_map_relabel fun _ _ ↦ rfl).mp (hτ _ (List.mem_map_of_mem hc))⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ⟩ := CNF.exists_relabel_assignment hf σ
    refine ⟨τ, fun c hc ↦ ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (Clause.one_map_relabel fun l hl ↦ hτ l.var (CNF.mem_vars hd hl)).mpr (hσ d hd)

/-- Relabeling along an *injective* map preserves and reflects exactly-one
satisfiability: the corollary gadget certificates use, their naming maps being
injective on all of `V`. -/
theorem CNF.oneSatisfiable_relabel {f : V → W} (hf : Function.Injective f)
    (φ : CNF V) : (φ.relabel f).OneSatisfiable ↔ φ.OneSatisfiable :=
  CNF.oneSatisfiable_relabel_of_injOn hf.injOn

/-! ### The problems -/

/-- ONE-IN-THREE SAT: has the formula an assignment making exactly one literal
of each clause true? Not a catalog entry of its own — Garey–Johnson lists only
the width-3 version, and this is here to be restricted. -/
def ONE_IN_THREE_SAT : Problem SatInstance := fun x ↦ x.φ.OneSatisfiable

/-- ONE-IN-THREE 3SAT: the same question of a formula all of whose clauses have
exactly three literals. In the promise-free formulation of `Problem.restrict` —
a formula with a clause of another width is simply a no-instance. -/
def ONE_IN_THREE_SAT3 : Problem SatInstance :=
  ONE_IN_THREE_SAT.restrict fun x ↦ ∀ c ∈ x.φ, c.length = 3

end Hardness


