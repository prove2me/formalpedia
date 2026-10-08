-- Prove2me | Definitions.Def_ChoicelessPolynomialTime
-- name    : ChoicelessPolynomialTime
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.83253+00:00
-- url     : https://prove2.me/theorems/4990578f-f3e5-46b2-a81e-eecf291bde2f
-- statement:
--   The block defines a finite relational query over the field F₃ and two notions of polynomial-time computation. An input is an arbitrary finite set A with eight Boolean binary relations Ed, Cf, EB, VB, I and Zδ for δ∈F₃; edges E and configurations C are selected by the diagonal Ed and Cf relations. Put c(y,a)=∑_{x∈E:I(a,x)}∑_{δ:Zδ(y,x)}δ, and call (t,y) incident when some a∈C and x∈E satisfy VB(t,a), I(a,x) and EB(y,x). The query asks for λ:C→F₃ and μ:E→F₃ such that ∑_{a:VB(t,a)}λ(a)=1 for every t∈C and μ(y)=∑_{a:VB(t,a)}λ(a)c(y,a) for every incident (t,y). No further relational axioms are imposed; input isomorphisms are bijections preserving every relation. Hereditarily finite objects over A comprise atoms and extensional finite sets, with membership, rank, unordered pairs, finite ordinals, and closure under recursively taking elements, including the original object. Operations include all atoms, union, the unique element of a singleton with empty-set default otherwise, and cardinality represented as an ordinal; the empty set and ordinal 1 encode false and true. A state assigns such objects to function-symbol locations with finitely many nonempty values. Terms combine variables, ordinals, state lookup, these set operations, equality, membership, atom and input-relation tests, Boolean operations, conditionals and bounded comprehension. Rules produce simultaneous finite updates using assignment, parallel composition, conditionals, bounded universal iteration and local variable binding. Programs have finitely many function symbols of specified arities and nullary halt and accept flags. Runs begin with every location empty, repeat the program body with initially empty variable assignments, fail if one location receives unequal updates, and remain stationary after halting. Active objects include the membership closures of stored nonempty values and their location arguments, all atoms, the set of all atoms, and Boolean constants. Occurring objects additionally count intermediate evaluated term values and their membership closures, following executed branches and bounded iterations. Acceptance within polynomials t,s∈ℕ[X] requires a successful run reaching both flags by step h≤t(|A|), with at most s(|A|) distinct occurring objects through that run. EvaluationDefinable(Q) means one program and two such polynomials characterize Q on every finite input by this bounded acceptance condition; it imposes no separate halting requirement on negative instances. Ordered inputs identify A with Fin N and list all 8N² relation bits. Their machine encoding is N blank letters, a zero delimiter, and the relation bits as F₃-valued letters; answers are single encoded Boolean letters. OrdinaryPolynomialTime is the defined proposition that a TM2 machine with finite component alphabets computes a Boolean answer in polynomial time on these encodings, and that its answer equals the query for every finite input and every choice of ordering.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ChoicelessPolynomialTime.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ChoicelessPolynomialTime.lean; bytes 16..19291
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

universe uA uB uC uF uR

namespace CPTSeparation

abbrev Scalar := ZMod 3

inductive Symbol
  | Ed | Cf | EB | VB | I | Z (δ : Scalar)
  deriving DecidableEq, Fintype

structure Input (A : Type) where
  rel : Symbol → A → A → Bool

namespace Input

variable {A B : Type} [Fintype A] [Fintype B]

abbrev Edge (S : Input A) := {y : A // S.rel .Ed y y = true}

abbrev Config (S : Input A) := {a : A // S.rel .Cf a a = true}

instance (S : Input A) : Fintype S.Edge := inferInstanceAs (Fintype (Subtype _))

instance (S : Input A) : Fintype S.Config := inferInstanceAs (Fintype (Subtype _))

def coefficient (S : Input A) (y : S.Edge) (a : S.Config) : Scalar :=
  ∑ x : S.Edge, if S.rel .I a x then
    ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0
    else 0

def incident (S : Input A) (t : S.Config) (y : S.Edge) : Prop :=
  ∃ a : S.Config, S.rel .VB t a = true ∧
    ∃ x : S.Edge, S.rel .I a x = true ∧ S.rel .EB y x = true

def normalized (S : Input A) (lambda : S.Config → Scalar) : Prop :=
  ∀ t : S.Config, (∑ a : S.Config, if S.rel .VB t a then lambda a else 0) = 1

def consistent (S : Input A) (lambda : S.Config → Scalar) (mu : S.Edge → Scalar) : Prop :=
  ∀ (t : S.Config) (y : S.Edge), S.incident t y →
    mu y = ∑ a : S.Config, if S.rel .VB t a then lambda a * S.coefficient y a else 0

def query (S : Input A) : Prop :=
  ∃ (lambda : S.Config → Scalar) (mu : S.Edge → Scalar), S.normalized lambda ∧ S.consistent lambda mu

structure Iso (S : Input A) (T : Input B) extends A ≃ B where
  rel_eq : ∀ r x y, T.rel r (toEquiv x) (toEquiv y) = S.rel r x y

end Input

namespace Hereditary

section

abbrev HF (A : Type uA) := Quotient (@Lists.instSetoidLists A)

variable {A : Type uA} {B : Type uB}

local instance instDecidableEqHF {A : Type uA} : DecidableEq (HF A) := Classical.decEq _

def mk (l : Lists A) : HF A := Quotient.mk Lists.instSetoidLists l

def atom (a : A) : HF A := mk (Lists.atom a)

def isSet (x : HF A) : Bool := Quotient.liftOn x (fun l => l.1)
  (by intro l r h; cases h <;> rfl)

def rawElements (l : Lists A) : Finset (HF A) := by
  classical
  exact l.toList.toFinset.image mk

def elements (x : HF A) : Finset (HF A) := Quotient.liftOn x rawElements (by
  have mem_rawElements (a l : Lists A) : mk a ∈ rawElements l ↔ a ∈ l := by
    classical
    rcases l with ⟨(_ | _), l⟩
    · cases l
      change mk a ∈ (∅ : Finset (HF A)) ↔ False
      simp
    · change mk a ∈ (Lists'.toList l).toFinset.image mk ↔ a ∈ l
      simp only [Finset.mem_image, List.mem_toFinset, Lists'.mem_def, mk, Quotient.eq]
      constructor
      · rintro ⟨a',ha',heq⟩
        exact ⟨a',ha',heq.symm⟩
      · rintro ⟨a',ha',heq⟩
        exact ⟨a',ha',heq.symm⟩
  have raw_mem_congr_right {l r : Lists A} (h : Lists.Equiv l r) (a : Lists A) :
      a ∈ l ↔ a ∈ r := by
    cases h with
    | refl => rfl
    | antisymm hl hr =>
      exact ⟨Lists'.mem_of_subset hl, Lists'.mem_of_subset hr⟩
  intro l r h
  ext z
  induction z using Quotient.inductionOn with
  | _ a =>
    change mk a ∈ rawElements l ↔ mk a ∈ rawElements r
    rw [mem_rawElements, mem_rawElements]
    exact raw_mem_congr_right h a)

instance : Membership (HF A) (HF A) := ⟨fun y x => x ∈ elements y⟩

def ofFinset (s : Finset (HF A)) : HF A :=
  mk (Lists.ofList (s.toList.map Quotient.out))

def rawRank' : {b : Bool} → Lists' A b → ℕ
  | _, .atom _ => 0
  | _, .nil => 0
  | _, .cons' a l => max (rawRank' a + 1) (rawRank' l)

def rawRank (l : Lists A) : ℕ := rawRank' l.2

def rank (x : HF A) : ℕ := Quotient.liftOn x rawRank (by
  have rawRank_lt_of_mem {b : Bool} (l : Lists' A b) (a : Lists A)
      (ha : a ∈ l.toList) : rawRank a < rawRank' l := by
    induction l with
    | atom => simp at ha
    | nil => simp at ha
    | cons' c l ihc ihl =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihl ha) (le_max_right _ _)
  have rawRank_congr {l r : Lists A} (h : Lists.Equiv l r) : rawRank l = rawRank r := by
    induction h using Lists.Equiv.rec
        (motive_2 := fun l r _ => rawRank' l ≤ rawRank' r) with
    | refl => rfl
    | antisymm hl hr ihl ihr => exact Nat.le_antisymm ihl ihr
    | nil => exact Nat.zero_le _
    | @cons a a' l r heq hmem hsub iheq ihsub =>
      change max (rawRank a + 1) (rawRank' l) ≤ rawRank' r
      refine max_le ?_ ihsub
      rw [iheq]
      exact rawRank_lt_of_mem r a' hmem
  exact fun _ _ h => rawRank_congr h)

end

open Classical Finset

variable {A : Type uA} {B : Type uB}

def double (a b : HF A) : HF A := ofFinset {a,b}

def ordinal : ℕ → HF A
  | 0 => ofFinset ∅
  | i+1 => ofFinset (insert (ordinal i) (elements (ordinal i)))

end Hereditary

namespace Operational

open Classical Hereditary Finset

variable {A : Type uA} {B : Type uB} {R : Type uR} {F : Type uF} {arity : F → ℕ}

local instance instDecidableEqHF {C : Type uC} : DecidableEq (HF C) := Classical.decEq _

abbrev empty : HF A := ordinal 0

abbrev truth : HF A := ordinal 1

def boolean (p : Prop) : HF A := if p then truth else empty

def inputRelation (rel : R → A → A → Bool) (r : R) (x y : HF A) : Prop :=
  ∃ a b, x = atom a ∧ y = atom b ∧ rel r a b = true

def allAtoms [Fintype A] : HF A := ofFinset (univ.image atom)

def unionHF (x : HF A) : HF A := ofFinset ((elements x).biUnion elements)

def uniqueHF (x : HF A) : HF A :=
  if h : ∃ a, elements x = {a} then h.choose else empty

def cardinalityHF (x : HF A) : HF A := ordinal (elements x).card

abbrev Location (F : Type uF) (arity : F → ℕ) (A : Type uA) := Σ f : F, Fin (arity f) → HF A

structure State (F : Type uF) (arity : F → ℕ) (A : Type uA) where
  value : Location F arity A → HF A
  finite : Set.Finite {l | value l ≠ empty}

namespace State

def initial : State F arity A := ⟨fun _ => empty, by simp⟩

def support (s : State F arity A) : Finset (Location F arity A) := s.finite.toFinset

end State

abbrev Update (F : Type uF) (arity : F → ℕ) (A : Type uA) := Location F arity A × HF A

def State.Consistent (u : Finset (Update F arity A)) : Prop :=
  ∀ l x y, (l,x) ∈ u → (l,y) ∈ u → x = y

def State.updatedValue (s : State F arity A) (u : Finset (Update F arity A))
    (l : Location F arity A) : HF A :=
  if h : ∃ x, (l,x) ∈ u then h.choose else s.value l

def State.applyUpdates (s : State F arity A) (u : Finset (Update F arity A)) : State F arity A where
  value := s.updatedValue u
  finite := by
    apply (s.finite.union (u.image Prod.fst).finite_toSet).subset
    intro l hl
    by_cases h : ∃ x, (l,x) ∈ u
    · obtain ⟨x,hx⟩ := h
      exact Or.inr (mem_image.mpr ⟨(l,x),hx,rfl⟩)
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq,updatedValue,dite_eq_right h] using hl)

inductive Control | halt | accept deriving DecidableEq

end Operational

section

open Classical Finset

variable {A : Type uA} {B : Type uB}

local instance Hereditary.instDecidableEqHF_1 {C : Type uC} : DecidableEq (HF C) := Classical.decEq _

def Hereditary.closure (x : HF A) : Finset (HF A) :=
  insert x ((elements x).attach.biUnion (fun y => closure y.val))
termination_by rank x
decreasing_by
  have mem_rawElements (a l : Lists A) : mk a ∈ rawElements l ↔ a ∈ l := by
    classical
    rcases l with ⟨(_ | _), l⟩
    · cases l
      change mk a ∈ (∅ : Finset (HF A)) ↔ False
      simp
    · change mk a ∈ (Lists'.toList l).toFinset.image mk ↔ a ∈ l
      simp only [Finset.mem_image, List.mem_toFinset, Lists'.mem_def, mk, Quotient.eq]
      constructor
      · rintro ⟨a',ha',heq⟩
        exact ⟨a',ha',heq.symm⟩
      · rintro ⟨a',ha',heq⟩
        exact ⟨a',ha',heq.symm⟩
  have rawRank_lt_of_mem {b : Bool} (l : Lists' A b) (a : Lists A)
      (ha : a ∈ l.toList) : rawRank a < rawRank' l := by
    induction l with
    | atom => simp at ha
    | nil => simp at ha
    | cons' c l ihc ihl =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihl ha) (le_max_right _ _)
  have rawRank_congr {l r : Lists A} (h : Lists.Equiv l r) : rawRank l = rawRank r := by
    induction h using Lists.Equiv.rec
        (motive_2 := fun l r _ => rawRank' l ≤ rawRank' r) with
    | refl => rfl
    | antisymm _hl _hr ihl ihr => exact Nat.le_antisymm ihl ihr
    | nil => exact Nat.zero_le _
    | @cons a a' l r _heq hmem _hsub iheq ihsub =>
      change max (rawRank a + 1) (rawRank' l) ≤ rawRank' r
      refine max_le ?_ ihsub
      rw [iheq]
      exact rawRank_lt_of_mem r a' hmem
  have rank_lt_of_mem {x y : HF A} (h : x ∈ y) : rank x < rank y := by
    induction y using Quotient.inductionOn with
    | _ l =>
      induction x using Quotient.inductionOn with
      | _ a =>
        have h' := (mem_rawElements a l).mp h
        rcases l with ⟨(_ | _), l⟩
        · exact False.elim h'
        · obtain ⟨a',ha',heq⟩ := h'
          change rawRank a < rawRank' l
          rw [rawRank_congr heq]
          exact rawRank_lt_of_mem l a' ha'
  exact rank_lt_of_mem y.property

def Hereditary.familyClosure (f : Finset (HF A)) : Finset (HF A) := f.biUnion closure

end

section

open Classical Hereditary Finset

variable {A : Type uA} {R : Type uR} {F : Type uF} {arity : F → ℕ}

local instance Operational.instDecidableEqHF_1 {C : Type uC} : DecidableEq (HF C) := Classical.decEq _

def Operational.State.critical (s : State F arity A) : Finset (HF A) :=
  s.support.biUnion (fun l => insert (s.value l) (univ.image l.2))

def Operational.State.active [Fintype A] (s : State F arity A) : Finset (HF A) :=
  familyClosure (s.critical ∪ {allAtoms,empty,truth} ∪ univ.image atom)

end

namespace FullCPT

section

open Classical Hereditary Finset

open Operational (State Control Location Update)

local instance instDecidableEqHF {C : Type} : DecidableEq (HF C) := Classical.decEq _

inductive Term (R F : Type) (arity : F → ℕ) : Type
  | var (name : ℕ)
  | ordinal (n : ℕ)
  | atoms
  | app (f : F) (args : Fin (arity f) → Term R F arity)
  | pair (a b : Term R F arity)
  | union (a : Term R F arity)
  | unique (a : Term R F arity)
  | card (a : Term R F arity)
  | equal (a b : Term R F arity)
  | member (a b : Term R F arity)
  | isAtom (a : Term R F arity)
  | input (r : R) (a b : Term R F arity)
  | not (a : Term R F arity)
  | and (a b : Term R F arity)
  | or (a b : Term R F arity)
  | conditional (c a b : Term R F arity)
  | comprehend (name : ℕ) (bound guard body : Term R F arity)

variable {A R F : Type} {arity : F → ℕ}

namespace Term

variable [Fintype A]

def eval (rel : R → A → A → Bool) (s : State F arity A) :
    Term R F arity → (ℕ → HF A) → HF A
  | .var n, v => v n
  | .ordinal n, _ => Hereditary.ordinal n
  | .atoms, _ => Operational.allAtoms
  | .app f args, v => s.value ⟨f, fun i => eval rel s (args i) v⟩
  | .pair a b, v => double (eval rel s a v) (eval rel s b v)
  | .union a, v => Operational.unionHF (eval rel s a v)
  | .unique a, v => Operational.uniqueHF (eval rel s a v)
  | .card a, v => Operational.cardinalityHF (eval rel s a v)
  | .equal a b, v => Operational.boolean (eval rel s a v = eval rel s b v)
  | .member a b, v => Operational.boolean (eval rel s a v ∈ eval rel s b v)
  | .isAtom a, v => Operational.boolean (isSet (eval rel s a v) = false)
  | .input r a b, v => Operational.boolean (Operational.inputRelation rel r (eval rel s a v) (eval rel s b v))
  | .not a, v => Operational.boolean (eval rel s a v ≠ Operational.truth)
  | .and a b, v => Operational.boolean (eval rel s a v = Operational.truth ∧ eval rel s b v = Operational.truth)
  | .or a b, v => Operational.boolean (eval rel s a v = Operational.truth ∨ eval rel s b v = Operational.truth)
  | .conditional c a b, v => if eval rel s c v = Operational.truth then eval rel s a v else eval rel s b v
  | .comprehend n bound guard body, v =>
      ofFinset (((elements (eval rel s bound v)).filter
        (fun x => eval rel s guard (Function.update v n x) = Operational.truth)).image
        (fun x => eval rel s body (Function.update v n x)))

end Term

inductive Rule (R F : Type) (arity : F → ℕ) : Type
  | skip
  | update (f : F) (args : Fin (arity f) → Term R F arity) (value : Term R F arity)
  | parallel (a b : Rule R F arity)
  | conditional (condition : Term R F arity) (a b : Rule R F arity)
  | forall (name : ℕ) (bound : Term R F arity) (body : Rule R F arity)
  | letValue (name : ℕ) (value : Term R F arity) (body : Rule R F arity)

namespace Rule

def updates [Fintype A] (rel : R → A → A → Bool) (s : State F arity A) :
    Rule R F arity → (ℕ → HF A) → Finset (Update F arity A)
  | .skip, _ => ∅
  | .update f args value, v => {(⟨f, fun i => (args i).eval rel s v⟩, value.eval rel s v)}
  | .parallel a b, v => updates rel s a v ∪ updates rel s b v
  | .conditional c a b, v => if c.eval rel s v = Operational.truth then updates rel s a v else updates rel s b v
  | .forall n bound body, v => (elements (bound.eval rel s v)).biUnion
      (fun x => updates rel s body (Function.update v n x))
  | .letValue n value body, v => updates rel s body (Function.update v n (value.eval rel s v))

end Rule

structure Program (R : Type) where
  Functions : Type
  finiteFunctions : Fintype Functions
  arity : Functions → ℕ
  body : Rule R (Control ⊕ Functions) (Sum.elim (fun _ => 0) arity)

namespace Program

variable (P : Program R) [Fintype A]

abbrev functionArity : Control ⊕ P.Functions → ℕ := Sum.elim (fun _ => 0) P.arity

abbrev Store := State (Control ⊕ P.Functions) P.functionArity A

def flag (s : P.Store (A := A)) (c : Control) : Prop := s.value ⟨.inl c, Fin.elim0⟩ = Operational.truth

def step (rel : R → A → A → Bool) (s : P.Store (A := A)) : Option (P.Store (A := A)) :=
  if P.flag s .halt then some s else
    let u := P.body.updates rel s (fun _ => Operational.empty)
    if State.Consistent u then some (s.applyUpdates u) else none

def run (rel : R → A → A → Bool) : ℕ → Option (P.Store (A := A))
  | 0 => some State.initial
  | j+1 => (run rel j).bind (P.step rel)

def active (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
  (Finset.range (h+1)).biUnion (fun j => ((P.run rel j).toFinset).biUnion State.active)

end Program

end

open Classical Hereditary Finset

open Operational (State Control)

local instance instDecidableEqHF_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {A R F : Type} {arity : F → ℕ}

section

variable [Fintype A]

def Term.roots (rel : R → A → A → Bool) (s : State F arity A) :
    Term R F arity → (ℕ → HF A) → Finset (HF A)
  | t@(.var _), v | t@(.ordinal _), v | t@(.atoms), v => {t.eval rel s v}
  | t@(.app _ args), v => insert (t.eval rel s v)
      ((List.ofFn (fun i => roots rel s (args i) v)).foldr (· ∪ ·) ∅)
  | t@(.pair a b), v | t@(.equal a b), v | t@(.member a b), v
  | t@(.input _ a b), v | t@(.and a b), v | t@(.or a b), v =>
      insert (t.eval rel s v) (roots rel s a v ∪ roots rel s b v)
  | t@(.union a), v | t@(.unique a), v | t@(.card a), v
  | t@(.isAtom a), v | t@(.not a), v => insert (t.eval rel s v) (roots rel s a v)
  | .conditional c a b, v => roots rel s c v ∪
      if c.eval rel s v = Operational.truth then roots rel s a v else roots rel s b v
  | t@(.comprehend n bound guard body), v => insert (t.eval rel s v)
      (roots rel s bound v ∪ (elements (bound.eval rel s v)).biUnion (fun x =>
        roots rel s guard (Function.update v n x) ∪
        if guard.eval rel s (Function.update v n x) = Operational.truth then
          roots rel s body (Function.update v n x) else ∅))

def Rule.roots (rel : R → A → A → Bool) (s : State F arity A) :
 Rule R F arity → (ℕ → HF A) → Finset (HF A)
 | .skip, _ => ∅
 | .update _ args value, v => value.roots rel s v ∪
     (List.ofFn (fun i => (args i).roots rel s v)).foldr (· ∪ ·) ∅
 | .parallel a b, v => roots rel s a v ∪ roots rel s b v
 | .conditional c a b, v => c.roots rel s v ∪
     if c.eval rel s v = Operational.truth then roots rel s a v else roots rel s b v
 | .forall n bound body, v => bound.roots rel s v ∪
     (elements (bound.eval rel s v)).biUnion (fun x => roots rel s body (Function.update v n x))
 | .letValue n value body, v => value.roots rel s v ∪
     roots rel s body (Function.update v n (value.eval rel s v))

end

section

variable (P : Program R) [Fintype A]

def Program.stepRoots (rel : R → A → A → Bool) (s : P.Store (A := A)) : Finset (HF A) :=
 if P.flag s .halt then ∅ else P.body.roots rel s (fun _ => Operational.empty)

def Program.occurring (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
 P.active rel h ∪ (range h).biUnion (fun j => match P.run rel j with
   | none => ∅
   | some s => familyClosure (P.stepRoots rel s))

def Program.evaluationAccepts (time space : Polynomial ℕ) (rel : R → A → A → Bool) : Prop :=
 ∃ h st, h ≤ time.eval (Fintype.card A) ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
   (P.occurring rel h).card ≤ space.eval (Fintype.card A)

end

def EvaluationDefinable (Q : ∀ {A : Type}, [Fintype A] → Input A → Prop) : Prop :=
 ∃ P : Program Symbol, ∃ time space : Polynomial ℕ,
   ∀ (A : Type) [Fintype A] (I : Input A), P.evaluationAccepts time space I.rel ↔ Q I

end FullCPT

namespace OrderedQuery

section

open Finset

variable {N : ℕ}

abbrev Data (N : ℕ) := Input (Fin N)

end

def indexSymbol (i : Fin 8) : Symbol :=
  if i.val = 0 then .Ed else
  if i.val = 1 then .Cf else
  if i.val = 2 then .EB else
  if i.val = 3 then .VB else
  if i.val = 4 then .I else .Z ((i.val-5 : ℕ) : Scalar)

variable {N : ℕ}

def cellValue (S : Data N) (k : Fin (8*(N*N))) : Bool :=
  let ij := finProdFinEquiv.symm k
  let ab := finProdFinEquiv.symm ij.2
  S.rel (indexSymbol ij.1) ab.1 ab.2

def tableBits (S : Data N) : List Bool := List.ofFn (cellValue S)

abbrev OrderedInput := Σ N, Data N

end OrderedQuery

namespace GaussMachine

abbrev Letter := Option Scalar

def boolCode (b : Bool) : List Letter := [some (if b then 1 else 0)]

end GaussMachine

namespace CounterLang

abbrev Letter := Option Scalar

end CounterLang

namespace TableMachine

open CounterLang

def bitLetter (b : Bool) : Letter := some (if b then 1 else 0)

def tableInput {N} (S : OrderedQuery.Data N) : List Letter :=
 (OrderedQuery.tableBits S).map bitLetter

def code (S : OrderedQuery.OrderedInput) : List Letter :=
 List.replicate S.1 none ++ some 0 :: tableInput S.2

end TableMachine

def Input.ordered {A : Type} {N : ℕ} (S : Input A) (e : A ≃ Fin N) : OrderedQuery.Data N :=
  ⟨fun r i j => S.rel r (e.symm i) (e.symm j)⟩

def OrdinaryPolynomialTime : Prop :=
  ∃ answer : OrderedQuery.OrderedInput → Bool,
    ∃ machine : Turing.TM2ComputableInPolyTime TableMachine.code GaussMachine.boolCode answer,
      (∀ k, Finite (machine.tm.Γ k)) ∧
      ∀ (A : Type) [Fintype A] (N : ℕ) (e : A ≃ Fin N) (S : Input A),
        answer ⟨N,S.ordered e⟩ = true ↔ S.query



end CPTSeparation
end
end OAI


