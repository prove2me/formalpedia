-- Prove2me | Definitions.Def_PricingWithTips3DM_559a735c0442b6eef1922892
-- name    : PricingWithTips3DM_559a735c0442b6eef1922892
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:18:49.301007+00:00
-- url     : https://prove2.me/theorems/d6eea94c-5203-4c87-ba26-b19929b073ca
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Logic.Sat
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import Definitions.Def_PricingWithTips3DM_06e60956ff918030951e5808
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# CNF satisfiability

A small self-contained theory of CNF formulas over a typed variable set, and the
SAT decision problem. Clauses are lists of literals; the same literal may occur
several times, and positions in these lists serve as literal *occurrences*
(which gadget reductions use as fresh names).
-/

namespace Hardness

variable {V W : Type*}

/-- A literal: a variable together with a polarity (`true` = positive). -/
structure Literal (V : Type*) where
  /-- The underlying variable. -/
  var : V
  /-- The polarity: `true` for a positive literal, `false` for a negated one. -/
  polarity : Bool
deriving DecidableEq, Repr

/-- A clause: a disjunction of literals, as a list. -/
abbrev Clause (V : Type*) := List (Literal V)

/-- A CNF formula: a conjunction of clauses, as a list. -/
abbrev CNF (V : Type*) := List (Clause V)

/-- A literal holds under an assignment if the variable's value matches the
polarity. -/
def Literal.Holds (σ : V → Bool) (l : Literal V) : Prop :=
  σ l.var = l.polarity

instance {σ : V → Bool} {l : Literal V} : Decidable (l.Holds σ) := by
  unfold Literal.Holds; infer_instance

/-- Whether a literal holds depends on the assignment only at its own
variable. -/
theorem Literal.holds_congr {σ τ : V → Bool} {l : Literal V} (h : σ l.var = τ l.var) :
    l.Holds σ ↔ l.Holds τ := by
  unfold Literal.Holds
  rw [h]

/-- Under the complementary assignment a literal holds exactly when it failed.
This is the symmetry that makes not-all-equal satisfaction (`Logic/Nae3Sat.lean`)
invariant under flipping every variable. -/
theorem Literal.holds_not {σ : V → Bool} {l : Literal V} :
    l.Holds (fun v ↦ !σ v) ↔ ¬l.Holds σ := by
  unfold Literal.Holds
  cases hσ : σ l.var <;> cases l.polarity <;> simp [hσ]

/-- A literal's negation: the same variable, the opposite polarity. -/
def Literal.neg (l : Literal V) : Literal V := ⟨l.var, !l.polarity⟩

/-- A negated literal holds exactly when the literal fails. -/
@[simp] theorem Literal.holds_neg {σ : V → Bool} {l : Literal V} :
    l.neg.Holds σ ↔ ¬l.Holds σ := by
  unfold Literal.Holds Literal.neg
  cases l.polarity <;> simp

/-- Two literals conflict if they assert opposite polarities of one variable. -/
def Literal.Conflicts (l₁ l₂ : Literal V) : Prop :=
  l₁.var = l₂.var ∧ l₁.polarity ≠ l₂.polarity

instance [DecidableEq V] {l₁ l₂ : Literal V} : Decidable (l₁.Conflicts l₂) := by
  unfold Literal.Conflicts; infer_instance

theorem Literal.Conflicts.symm {l₁ l₂ : Literal V} (h : l₁.Conflicts l₂) :
    l₂.Conflicts l₁ :=
  ⟨h.1.symm, h.2.symm⟩

/-- Literals that hold under a common assignment do not conflict. -/
theorem Literal.Holds.not_conflicts {σ : V → Bool} {l₁ l₂ : Literal V}
    (h₁ : l₁.Holds σ) (h₂ : l₂.Holds σ) : ¬l₁.Conflicts l₂ := by
  rintro ⟨hv, hp⟩
  unfold Literal.Holds at h₁ h₂
  rw [hv] at h₁
  exact hp (h₁.symm.trans h₂)

/-- A clause is satisfied if some literal in it holds. -/
def Clause.Sat (σ : V → Bool) (c : Clause V) : Prop :=
  ∃ l ∈ c, l.Holds σ

instance {σ : V → Bool} {c : Clause V} : Decidable (c.Sat σ) := by
  unfold Clause.Sat
  infer_instance

/-- A one-literal clause is satisfied iff its literal holds. -/
@[simp] theorem Clause.sat_singleton_iff {σ : V → Bool} {l : Literal V} :
    Clause.Sat σ [l] ↔ l.Holds σ := by
  constructor
  · rintro ⟨l', hl', hh⟩
    obtain rfl := List.mem_singleton.mp hl'
    exact hh
  · exact fun h ↦ ⟨l, List.mem_singleton_self _, h⟩

/-- A two-literal clause is satisfied iff one of its literals holds. -/
theorem Clause.sat_pair_iff {σ : V → Bool} {l₁ l₂ : Literal V} :
    Clause.Sat σ [l₁, l₂] ↔ l₁.Holds σ ∨ l₂.Holds σ := by
  constructor
  · rintro ⟨l, hl, hh⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Or.inl hh
    · obtain rfl := List.mem_singleton.mp hl
      exact Or.inr hh
  · rintro (h | h)
    · exact ⟨l₁, List.mem_cons_self, h⟩
    · exact ⟨l₂, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

/-- Satisfaction of a clause only depends on the assignment's values at the
variables of the clause. -/
theorem Clause.sat_congr {c : Clause V} {τ τ' : V → Bool}
    (h : ∀ l ∈ c, τ l.var = τ' l.var) : Clause.Sat τ c ↔ Clause.Sat τ' c :=
  ⟨fun ⟨l, hl, hh⟩ ↦ ⟨l, hl, (Literal.holds_congr (h l hl)).mp hh⟩,
    fun ⟨l, hl, hh⟩ ↦ ⟨l, hl, (Literal.holds_congr (h l hl)).mpr hh⟩⟩

/-- A CNF formula is satisfied if every clause is. -/
def CNF.Sat (σ : V → Bool) (φ : CNF V) : Prop :=
  ∀ c ∈ φ, c.Sat σ

/-- A CNF formula is satisfiable if some assignment satisfies it. -/
def CNF.Satisfiable (φ : CNF V) : Prop :=
  ∃ σ : V → Bool, φ.Sat σ

/-- A formula containing the empty clause is unsatisfiable. -/
theorem CNF.not_satisfiable_of_nil_mem {φ : CNF V} (h : [] ∈ φ) :
    ¬φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  obtain ⟨l, hl, -⟩ := hσ [] h
  simp at hl

/-! ### Relabeling variables

Gadget constructions name their fresh variables by *tagging tuples of input
objects*, so the formula they build lives over a structured variable type
(`V ⊕ (Fin n × ℕ)` and the like). A concrete encoding has only `ℕ` labels to
offer, so the tags must be realized as numbers. Relabeling along an injection
is the passage between the two views, and it changes nothing that either
problem can see: widths are untouched and satisfiability is preserved. -/

/-- The variables *occurring* in a formula. A formula is a finite object, so
this is a finite set however large `V` is — which is what makes a concrete
encoding possible at all: only these variables need labels. `cnfVars` is the
computable listing of exactly this set (`mem_cnfVars_iff`). -/
def CNF.vars (φ : CNF V) : Set V :=
  {v | ∃ c ∈ φ, ∃ l ∈ c, l.var = v}

/-- The variable of a literal of a clause of `φ` occurs in `φ`. -/
theorem CNF.mem_vars {φ : CNF V} {c : Clause V} (hc : c ∈ φ) {l : Literal V}
    (hl : l ∈ c) : l.var ∈ φ.vars :=
  ⟨c, hc, l, hl, rfl⟩

/-- Rename the variable of a literal along `f`. -/
def Literal.relabel (f : V → W) (l : Literal V) : Literal W :=
  ⟨f l.var, l.polarity⟩

/-- Rename the variables of a formula along `f`. -/
def CNF.relabel (f : V → W) (φ : CNF V) : CNF W :=
  φ.map (List.map (Literal.relabel f))

/-- Relabeling distributes over concatenation. -/
theorem CNF.relabel_append (f : V → W) (φ₁ φ₂ : CNF V) :
    (φ₁ ++ φ₂).relabel f = φ₁.relabel f ++ φ₂.relabel f :=
  List.map_append ..

/-- Relabeling changes no clause widths: any property of the widths holds of
the relabeled formula iff it holds of the original. -/
theorem CNF.forall_length_relabel {f : V → W} {φ : CNF V} {P : ℕ → Prop} :
    (∀ c ∈ φ.relabel f, P c.length) ↔ ∀ c ∈ φ, P c.length := by
  constructor
  · intro h c hc
    have hm := h (c.map (Literal.relabel f)) (List.mem_map_of_mem hc)
    rwa [List.length_map] at hm
  · intro h c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    rw [List.length_map]
    exact h d hd

/-- Relabeling does not change clause widths, so it preserves every width
restriction. -/
theorem CNF.width_relabel {f : V → W} {φ : CNF V} {n : ℕ} (h : ∀ c ∈ φ, c.length ≤ n) :
    ∀ c ∈ φ.relabel f, c.length ≤ n :=
  CNF.forall_length_relabel (P := (· ≤ n)).mpr h

/-- Satisfaction of a relabeled clause is satisfaction under the assignment read
through the relabeling. The counting form of `CNF.satisfiable_relabel_of_injOn`'s
easy direction, and what makes `CNF.numSat` transport along a relabeling. -/
theorem Clause.sat_map_relabel {f : V → W} {τ : W → Bool} (c : Clause V) :
    Clause.Sat τ (c.map (Literal.relabel f)) ↔ Clause.Sat (fun v ↦ τ (f v)) c := by
  constructor
  · rintro ⟨l', hl', hh⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    exact ⟨l, hl, hh⟩
  · rintro ⟨l, hl, hh⟩
    exact ⟨l.relabel f, List.mem_map_of_mem hl, hh⟩

/-- Embed a literal into a sum variable type: `Literal.relabel Sum.inl` under
another name, used by gadget constructions to inject a formula's original
variables into the extended variable set they build over. -/
def Literal.embed (l : Literal V) : Literal (V ⊕ W) :=
  ⟨Sum.inl l.var, l.polarity⟩

/-- Satisfaction of an embedded clause only depends on the assignment's
restriction to the original variables. -/
theorem Clause.sat_map_embed (c : Clause V) (τ : V ⊕ W → Bool) :
    Clause.Sat τ (c.map Literal.embed) ↔ Clause.Sat (fun v ↦ τ (Sum.inl v)) c := by
  constructor
  · rintro ⟨l', hl', hh⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    exact ⟨l, hl, hh⟩
  · rintro ⟨l, hl, hh⟩
    exact ⟨l.embed, List.mem_map.mpr ⟨l, hl, rfl⟩, hh⟩

/-- A relabeled literal holds under an assignment of the labels exactly when
the original holds under an assignment agreeing with it at that variable. -/
theorem Literal.holds_relabel {f : V → W} {τ : W → Bool} {σ : V → Bool}
    {l : Literal V} (h : τ (f l.var) = σ l.var) :
    (l.relabel f).Holds τ ↔ l.Holds σ := by
  unfold Literal.Holds Literal.relabel
  rw [h]

/-- **Assignments transport along a labelling that separates the occurring
variables**: some assignment of the labels gives every variable of `φ` the
value it had. The one place the injectivity hypothesis is used, and therefore
the one lemma each notion of satisfaction has to be pushed through — plain
satisfaction (`CNF.satisfiable_relabel_of_injOn`) and not-all-equal
satisfaction (`CNF.naeSatisfiable_relabel_of_injOn`) both reduce to it.

Labels carried by no occurring variable are given `false`; nothing observes
them. (Without injectivity on `φ.vars` no such assignment need exist:
collapsing a variable with its negation makes `[[x], [¬y]]` unsatisfiable.) -/
theorem CNF.exists_relabel_assignment {f : V → W} {φ : CNF V}
    (hf : Set.InjOn f φ.vars) (σ : V → Bool) :
    ∃ τ : W → Bool, ∀ v ∈ φ.vars, τ (f v) = σ v := by
  classical
  refine ⟨fun w ↦ if h : ∃ v ∈ φ.vars, f v = w then σ h.choose else false,
    fun v hv ↦ ?_⟩
  have hex : ∃ u ∈ φ.vars, f u = f v := ⟨v, hv, rfl⟩
  change (if h : ∃ u ∈ φ.vars, f u = f v then σ h.choose else false) = σ v
  rw [dif_pos hex, hf hex.choose_spec.1 hv hex.choose_spec.2]

/-- Relabeling preserves and reflects satisfiability as soon as the map is
injective *on the variables that occur* — nothing is asked of it elsewhere,
since the formula cannot see the difference.

Reflection is free — precompose the assignment with `f`. Preservation needs the
injectivity: a satisfying assignment of `φ` is transported along `f` by reading
each label back to the unique occurring variable carrying it. (Without
injectivity on `φ.vars` the statement is false: collapsing a variable with its
negation makes `[[x], [¬y]]` unsatisfiable.)

This is the form a *representation* theorem needs, where the labelling is the
position in a list of the occurring variables and so is defined — but not
injective — on all of `V`. Gadget certificates, whose naming maps are injective
outright, use the corollary `CNF.satisfiable_relabel`. -/
theorem CNF.satisfiable_relabel_of_injOn {f : V → W} {φ : CNF V}
    (hf : Set.InjOn f φ.vars) : (φ.relabel f).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v ↦ τ (f v), fun c hc ↦ ?_⟩
    obtain ⟨l, hl, hh⟩ := hτ (c.map (Literal.relabel f)) (List.mem_map_of_mem hc)
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    exact ⟨l₀, hl₀, hh⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ⟩ := CNF.exists_relabel_assignment hf σ
    refine ⟨τ, fun c hc ↦ ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨l, hl, hh⟩ := hσ d hd
    exact ⟨l.relabel f, List.mem_map_of_mem hl,
      (Literal.holds_relabel (hτ l.var (CNF.mem_vars hd hl))).mpr hh⟩

/-- Relabeling along an *injective* map preserves and reflects satisfiability:
the corollary of `CNF.satisfiable_relabel_of_injOn` that gadget certificates
use, their naming maps being injective on all of `V`. -/
theorem CNF.satisfiable_relabel {f : V → W} (hf : Function.Injective f) (φ : CNF V) :
    (φ.relabel f).Satisfiable ↔ φ.Satisfiable :=
  CNF.satisfiable_relabel_of_injOn hf.injOn

/-- The type of literal occurrences of a CNF formula: a clause index together
with a position inside that clause. Gadget reductions use occurrences as fresh
names ("tagged tuples of input objects"). -/
abbrev CNF.Occ (φ : CNF V) : Type :=
  (i : Fin φ.length) × Fin (φ[i.1]'i.isLt).length

/-- The literal sitting at a given occurrence. -/
def CNF.occLit (φ : CNF V) (o : φ.Occ) : Literal V :=
  (φ[o.1.1]'o.1.isLt)[o.2.1]'o.2.isLt

/-- The literal at an occurrence lies in the clause the occurrence points
into. -/
theorem CNF.occLit_mem (φ : CNF V) (o : φ.Occ) :
    φ.occLit o ∈ (φ[o.1.1]'o.1.isLt) :=
  List.getElem_mem _

/-- Occurrences enumerate the literals clause by clause: a property holds of
some occurrence exactly when it holds of some literal of some clause, together
with that clause's index. Certificates use this to match a `φ.Occ` existential
against a loop over the concrete clause list. -/
theorem CNF.exists_occ_iff {φ : CNF V} (Q : Literal V → ℕ → Prop) :
    (∃ o : φ.Occ, Q (φ.occLit o) o.1.1) ↔ ∃ j, ∃ hj : j < φ.length, ∃ l ∈ φ[j], Q l j := by
  constructor
  · rintro ⟨⟨⟨j, hj⟩, ⟨k, hk⟩⟩, hQ⟩
    exact ⟨j, hj, _, List.getElem_mem hk, hQ⟩
  · rintro ⟨j, hj, l, hl, hQ⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    exact ⟨⟨⟨j, hj⟩, ⟨k, hk⟩⟩, hQ⟩

/-- All occurrences of a formula, in clause-by-clause order. -/
def allOccs (φ : CNF V) : List φ.Occ :=
  (List.finRange φ.length).sigma fun i ↦ List.finRange (φ[i.1]'i.isLt).length

/-- `allOccs` is complete: every occurrence is listed. -/
theorem mem_allOccs (φ : CNF V) (o : φ.Occ) : o ∈ allOccs φ := by
  obtain ⟨i, j⟩ := o
  exact List.mem_sigma.mpr ⟨List.mem_finRange i, List.mem_finRange j⟩

/-- `allOccs` has no duplicates. -/
theorem nodup_allOccs (φ : CNF V) : (allOccs φ).Nodup :=
  (List.nodup_finRange _).sigma fun _ ↦ List.nodup_finRange _

/-- `allOccs` enumerates the literals in flattening order: reading every
occurrence off is exactly flattening the formula. The order matters to
certificates, whose programs see the concrete clause list and can only iterate
it clause by clause. -/
theorem map_occLit_allOccs (φ : CNF V) : (allOccs φ).map φ.occLit = φ.flatten := by
  rw [allOccs, List.sigma, List.map_flatMap]
  conv_rhs => rw [← List.map_getElem_finRange φ, List.flatMap_def.symm]
  exact List.flatMap_congr fun i _ ↦ by
    rw [List.map_map]
    exact List.map_getElem_finRange _

/-- The variables of `φ`, listed without duplicates. Gadget reductions that
need one component per *variable* (rather than per occurrence) index it by
this list; `mem_cnfVars` is the completeness property they rely on. -/
def cnfVars [DecidableEq V] (φ : CNF V) : List V :=
  ((allOccs φ).map fun o ↦ (φ.occLit o).var).dedup

/-- `cnfVars` is complete: every variable occurring anywhere in `φ` is
listed. -/
theorem mem_cnfVars [DecidableEq V] {φ : CNF V} {c : Clause V} (hc : c ∈ φ)
    {l : Literal V} (hl : l ∈ c) : l.var ∈ cnfVars φ := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  exact List.mem_dedup.mpr
    (List.mem_map.mpr ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, mem_allOccs φ _, rfl⟩)

/-- `cnfVars` has no duplicates. -/
theorem nodup_cnfVars [DecidableEq V] (φ : CNF V) : (cnfVars φ).Nodup :=
  List.nodup_dedup _

/-- `cnfVars` in flattening form: the occurrence enumeration it is defined by
reads off the flattened formula, so a certificate — which sees only the
concrete clause list — can match it against a `dedup` of a flatten-and-map.
This is what ties `cnfVars` to `vsOf`, and with it the *positions* in the two
lists, which is what a positional relabeling needs. -/
theorem cnfVars_eq_dedup [DecidableEq V] (φ : CNF V) :
    cnfVars φ = (φ.flatten.map Literal.var).dedup := by
  rw [cnfVars, ← map_occLit_allOccs, List.map_map]
  rfl

/-- `cnfVars` lists exactly the occurring variables: it is the computable face
of `CNF.vars`, and nothing else is on it. Keeping the two tied means a
construction may index by the list and reason about the set. -/
theorem mem_cnfVars_iff [DecidableEq V] {φ : CNF V} {v : V} :
    v ∈ cnfVars φ ↔ v ∈ φ.vars := by
  constructor
  · intro hv
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
    exact CNF.mem_vars (List.getElem_mem o.1.isLt) (CNF.occLit_mem φ o)
  · rintro ⟨c, hc, l, hl, rfl⟩
    exact mem_cnfVars hc hl

/-! ### Variable slots

A gadget with one component per variable indexes it by a position in a variable
list. The indexing map must be *total* — defined on every `v : V`, not only on
those that occur — or a membership proof rides along into the gadget's vertex
names and infects every statement about them. `varSlot` buys totality with one
dummy slot; injectivity, all a construction ever needs, survives on variables
that really do occur. -/

/-- The variable slot of `v`: its position in `vs`, or the dummy slot
`vs.length` when `v` does not occur in `vs`. Total by construction — the
dummy slot exists precisely so that no proof obligation rides along. -/
def varSlot [DecidableEq V] (vs : List V) (v : V) : Fin (vs.length + 1) :=
  ⟨min (vs.idxOf v) vs.length, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- A variable of the list lands on its own position, not on the dummy. -/
theorem varSlot_val_of_mem [DecidableEq V] {vs : List V} {v : V} (h : v ∈ vs) :
    (varSlot vs v).1 = vs.idxOf v := by
  have hlt : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem h
  have h0 : (varSlot vs v).1 = min (vs.idxOf v) vs.length := rfl
  rw [h0]
  omega

/-- Distinct variables of the list get distinct slots. -/
theorem varSlot_inj [DecidableEq V] {vs : List V} {u v : V} (hu : u ∈ vs) (hv : v ∈ vs)
    (h : varSlot vs u = varSlot vs v) : u = v := by
  have hu' := varSlot_val_of_mem hu
  have hv' := varSlot_val_of_mem hv
  have hidx : vs.idxOf u = vs.idxOf v := by
    rw [← hu', ← hv', h]
  have h1 : vs[vs.idxOf u]'(List.idxOf_lt_length_of_mem hu) = u := List.getElem_idxOf _
  have h2 : vs[vs.idxOf v]'(List.idxOf_lt_length_of_mem hv) = v := List.getElem_idxOf _
  rw [← h1, ← h2]
  simp only [hidx]

/-! #### Slots of a structured variable list

A construction that builds its variable list out of pieces — a `map` of one
family appended to a `map` of another, as `cutVarList` does — needs each
piece's contribution to the slot number in closed form. Stated over an opaque
element type on purpose: written directly at a sum type, `idxOf`'s `BEq` would
be synthesized as `Sum.instBEq` rather than the one `varSlot` itself uses. -/

/-- Positions survive an injective relabeling of a list. -/
theorem idxOf_map_of_injective {W : Type*} [DecidableEq V] [DecidableEq W]
    {f : V → W} (hf : Function.Injective f) (l : List V) (a : V) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    by_cases h : b = a
    · subst h; simp
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun hc ↦ h (hf hc)),
        List.idxOf_cons_ne _ h, ih]

theorem varSlot_val_append_left [DecidableEq V] {vs l : List V} {v : V} (hv : v ∈ vs) :
    (varSlot (vs ++ l) v).1 = (varSlot vs v).1 := by
  rw [varSlot_val_of_mem (List.mem_append_left _ hv), varSlot_val_of_mem hv,
    List.idxOf_append_of_mem hv]

theorem varSlot_val_append_right [DecidableEq V] {vs l : List V} {v : V}
    (hv : v ∉ vs) (hv' : v ∈ l) :
    (varSlot (vs ++ l) v).1 = vs.length + (varSlot l v).1 := by
  rw [varSlot_val_of_mem (List.mem_append_right _ hv'), varSlot_val_of_mem hv',
    List.idxOf_append_of_notMem hv]

theorem varSlot_val_map {W : Type*} [DecidableEq V] [DecidableEq W] {f : V → W}
    (hf : Function.Injective f) {vs : List V} {v : V} (hv : v ∈ vs) :
    (varSlot (vs.map f) (f v)).1 = (varSlot vs v).1 := by
  rw [varSlot_val_of_mem (List.mem_map_of_mem hv), varSlot_val_of_mem hv,
    idxOf_map_of_injective hf]

/-- The truth value an assignment gives to a variable *slot*: the value of the
variable sitting there, and an arbitrary value at the dummy slot. The companion
of `varSlot` — a gadget indexed by slots reads its assignment through this.
Phrased through `getElem?` rather than `getElem` so that rewriting the index
needs no motive. -/
def slotValue (vs : List V) (σ : V → Bool) (i : Fin (vs.length + 1)) : Bool :=
  (vs[i.1]?).elim true σ

/-- At the slot of a variable that really occurs, `slotValue` is that
variable's value. -/
theorem slotValue_varSlot [DecidableEq V] {vs : List V} {σ : V → Bool} {v : V} (hv : v ∈ vs) :
    slotValue vs σ (varSlot vs v) = σ v := by
  have hlt : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hv
  have h0 : slotValue vs σ (varSlot vs v) = (vs[(varSlot vs v).1]?).elim true σ := rfl
  rw [h0, varSlot_val_of_mem hv, List.getElem?_eq_getElem hlt, List.getElem_idxOf]
  rfl

/-- An instance of a satisfiability problem: a variable type with decidable
equality, and a CNF formula over it. -/
structure SatInstance : Type 1 where
  /-- The variable type. -/
  V : Type
  [decEqV : DecidableEq V]
  /-- The formula. -/
  φ : CNF V

attribute [instance] SatInstance.decEqV

/-- SAT: is the formula satisfiable? -/
def SAT : Problem SatInstance := fun x ↦ x.φ.Satisfiable

end Hardness


