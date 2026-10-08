-- Prove2me | Definitions.Def_WitnessedChoice
-- name    : WitnessedChoice
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:39.404359+00:00
-- url     : https://prove2.me/theorems/a9a7c1f8-1c75-43d7-b39f-4b80724559b6
-- statement:
--   This block builds a logic over finite structures whose formulas can contain a witnessed-choice iteration construct, and defines a main statement about it. First, HF(A) is the type of hereditarily finite sets over a set of atoms A, realized as a quotient of nested lists. The block gives atoms, an isSet test, finite element sets, construction from a finite set, rank, transport along a map A to B (so a group acting on A acts on HF(A)), singleton, unordered double, Kuratowski pair, von Neumann ordinals, and the closure of a set (itself together with the closures of its elements). It also fixes the scalars ZMod 3, the six relation symbols Ed, Cf, EB, VB, I and Z(δ) for δ in ZMod 3, and an input on A, which assigns each symbol a Boolean binary relation on A. Terms with n free variables are built from variables, empty, atoms, pair, union, unique, card, comprehension (body, range, guard, binding one new variable) and iterate (a step term binding one variable). Formulas are equalities, input atoms for a symbol, negation, conjunction, disjunction, and wsc, which takes a step term with two bound variables, a choice term, a witness term with two bound variables and an output formula. Free-variable sets and the number of wsc occurrences are defined recursively. Evaluation is partial, returning Option values. Union takes the union of the elements, unique returns the sole element or the empty set, and card returns the ordinal of the number of elements. An input atom holds exactly when both arguments are atoms related by the symbol. Comprehension is defined only when guards and needed bodies are all defined on the range elements. Iterate starts from the empty set and repeatedly applies the step, using a bound p(|A|) given by the floor of a real polynomial p. It returns a fixed point if reached, and the empty set if the transitive closure of the current set exceeds the bound or the p+1 steps run out. The wsc evaluation checks a GoodWSC condition. Along choice-generated paths, with each choice a member of a nonempty choice set on which the step is defined, strict paths must have length and transitive-closure size at most p. Each first-repeat path must have length t with t+2≤p, a defined output, and, for each i≤t, a witness set M of permutation graphs. Each permutation graph is an automorphism of the input fixing the parameters and b_0,...,b_i, and the graphs in M carry any element of the choice set to any other. If GoodWSC holds, wsc evaluates to whether the output is true on every such first path, and otherwise it is undefined. A sentence is a closed formula with a polynomial, evaluated on finite inputs. It is CPT if it has no wsc. MainStatement is a defined proposition, not an established theorem. It says some sentence has exactly one wsc occurrence, evaluates to a Boolean on every finite input, and has a set of true models different from that of every CPT sentence.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WitnessedChoice.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WitnessedChoice.lean; bytes 16..17702
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

universe u v w

namespace WitnessedSeparation

namespace Hereditary

abbrev HF (A : Type u) := Quotient (@Lists.instSetoidLists A)

variable {A : Type u} {B : Type v}

section

local instance {A : Type u} : DecidableEq (HF A) := Classical.decEq _

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
    | antisymm _ _ ihl ihr => exact Nat.le_antisymm ihl ihr
    | nil => exact Nat.zero_le _
    | @cons a a' l r _ hmem _ iheq ihsub =>
      change max (rawRank a + 1) (rawRank' l) ≤ rawRank' r
      refine max_le ?_ ihsub
      rw [iheq]
      exact rawRank_lt_of_mem r a' hmem
  exact fun _ _ h => rawRank_congr h)

def rawMap' (f : A → B) : {b : Bool} → Lists' A b → Lists' B b
  | _, .atom a => .atom (f a)
  | _, .nil => .nil
  | _, .cons' a l => .cons' (rawMap' f a) (rawMap' f l)

def rawMap (f : A → B) (l : Lists A) : Lists B := ⟨l.1, rawMap' f l.2⟩

def map (f : A → B) (x : HF A) : HF B := by
  have toList_rawMap' (f : A → B) {b : Bool} (l : Lists' A b) :
      (rawMap' f l).toList = l.toList.map (rawMap f) := by
    induction l with
    | atom => rfl
    | nil => rfl
    | cons' a l iha ihl => simp only [rawMap', Lists'.toList, ihl]; rfl
  have rawMap_congr (f : A → B) {l r : Lists A} (h : Lists.Equiv l r) :
      Lists.Equiv (rawMap f l) (rawMap f r) := by
    induction h using Lists.Equiv.rec
        (motive_2 := fun l r _ => Lists'.Subset (rawMap' f l) (rawMap' f r)) with
    | refl => exact Lists.Equiv.refl _
    | antisymm hl hr ihl ihr => exact Lists.Equiv.antisymm ihl ihr
    | nil => exact Lists'.Subset.nil
    | @cons a a' l r _ hmem _ iheq ihsub =>
      apply Lists'.Subset.cons iheq _ ihsub
      rw [toList_rawMap']
      exact List.mem_map.mpr ⟨a',hmem,rfl⟩
  exact Quotient.liftOn x (fun l => mk (rawMap f l)) (fun _ _ h => Quotient.eq.mpr (rawMap_congr f h))

instance {G : Type w} [Group G] [MulAction G A] : MulAction G (HF A)  := by
  have map_mk {A B : Type u} (f : A → B) (l : Lists A) : map f (mk l) = mk (rawMap f l) := rfl
  have rawMap_id {A : Type u} : ∀ l : Lists A, rawMap id l = l := by
    rintro ⟨b,l⟩
    have h : rawMap' id l = l := by
      induction l with
      | atom => rfl
      | nil => rfl
      | cons' a l iha ihl => simp only [rawMap', iha,ihl]
    exact congrArg (Sigma.mk b) h
  have map_id {A : Type u} (x : HF A) : map id x = x := by
    induction x using Quotient.inductionOn with
    | _ l =>
      change map id (mk l) = mk l
      rw [map_mk, rawMap_id]
  have rawMap_comp {A B : Type u} {C : Type u} (g : B → C) (f : A → B) (l : Lists A) :
      rawMap g (rawMap f l) = rawMap (g ∘ f) l := by
    rcases l with ⟨b,l⟩
    have h : rawMap' g (rawMap' f l) = rawMap' (g ∘ f) l := by
      induction l with
      | atom => rfl
      | nil => rfl
      | cons' a l iha ihl => simp only [rawMap', iha,ihl]
    exact congrArg (Sigma.mk b) h
  have map_comp {A B : Type u} {C : Type u} (g : B → C) (f : A → B) (x : HF A) :
      map g (map f x) = map (g ∘ f) x := by
    induction x using Quotient.inductionOn with
    | _ l =>
      change map g (map f (mk l)) = map (g ∘ f) (mk l)
      simp only [map_mk,rawMap_comp]
  exact {
    smul g x := map (fun a => g • a) x
    one_smul x := by
      change map (fun a : A => (1 : G) • a) x = x
      have h : (fun a : A => (1 : G) • a) = id := by funext a; simp
      rw [h,map_id]
    mul_smul g h x := by
      change map (fun a : A => (g*h) • a) x = map (fun a => g • a) (map (fun a => h • a) x)
      rw [map_comp]
      congr 1
      funext a
      exact mul_smul g h a }

end

open Classical Finset

def singleton (a : HF A) : HF A := ofFinset {a}

def double (a b : HF A) : HF A := ofFinset {a,b}

def pair (a b : HF A) : HF A := double (singleton a) (double a b)

def ordinal : ℕ → HF A
  | 0 => ofFinset ∅
  | i+1 => ofFinset (insert (ordinal i) (elements (ordinal i)))

local instance {C : Type w} : DecidableEq (HF C) := Classical.decEq _

def closure (x : HF A) : Finset (HF A) :=
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
    | antisymm _ _ ihl ihr => exact Nat.le_antisymm ihl ihr
    | nil => exact Nat.zero_le _
    | @cons a a' l r _ hmem _ iheq ihsub =>
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

end Hereditary

abbrev Scalar := ZMod 3

inductive Symbol
  | Ed | Cf | EB | VB | I | Z (δ : Scalar)
  deriving DecidableEq, Fintype

structure Input (A : Type) where
  rel : Symbol → A → A → Bool

end WitnessedSeparation

namespace WitnessedChoice

namespace BGS

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

mutual

inductive Term : ℕ → Type
    | var {n} (i : Fin n) : Term n
    | empty {n} : Term n
    | atoms {n} : Term n
    | pair {n} (a b : Term n) : Term n
    | union {n} (a : Term n) : Term n
    | unique {n} (a : Term n) : Term n
    | card {n} (a : Term n) : Term n
    | comprehend {n} (body : Term (n+1)) (range : Term n)
        (guard : Formula (n+1)) : Term n
    | iterate {n} (step : Term (n+1)) : Term n
  inductive Formula : ℕ → Type
    | equal {n} (a b : Term n) : Formula n
    | input {n} (r : Symbol) (a b : Term n) : Formula n
    | neg {n} (a : Formula n) : Formula n
    | and {n} (a b : Formula n) : Formula n
    | or {n} (a b : Formula n) : Formula n
    | wsc {n} (step : Term (n+2)) (choice : Term (n+1))
        (witness : Term (n+2)) (output : Formula (n+1)) : Formula n

end

def dropFree {n} (f : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.succ ∈ f)

mutual

def Term.free : {n : ℕ} → Term n → Finset (Fin n)
    | _, .var i => {i}
    | _, .empty | _, .atoms => ∅
    | _, .pair a b => a.free ∪ b.free
    | _, .union a | _, .unique a | _, .card a => a.free
    | _, .comprehend body range guard => range.free ∪ dropFree (body.free ∪ guard.free)
    | _, .iterate step => dropFree step.free
  def Formula.free : {n : ℕ} → Formula n → Finset (Fin n)
    | _, .equal a b | _, .input _ a b => a.free ∪ b.free
    | _, .neg a => a.free
    | _, .and a b | _, .or a b => a.free ∪ b.free
    | _, .wsc step choice witness output =>
        dropFree (dropFree (step.free ∪ witness.free)) ∪ dropFree (choice.free ∪ output.free)

end

mutual

def Term.wscCount : {n : ℕ} → Term n → ℕ
    | _, .var _ | _, .empty | _, .atoms => 0
    | _, .pair a b => a.wscCount + b.wscCount
    | _, .union a | _, .unique a | _, .card a => a.wscCount
    | _, .comprehend body range guard => body.wscCount + range.wscCount + guard.wscCount
    | _, .iterate step => step.wscCount
  def Formula.wscCount : {n : ℕ} → Formula n → ℕ
    | _, .equal a b | _, .input _ a b => a.wscCount + b.wscCount
    | _, .neg a => a.wscCount
    | _, .and a b | _, .or a b => a.wscCount + b.wscCount
    | _, .wsc step choice witness output =>
        1 + step.wscCount + choice.wscCount + witness.wscCount + output.wscCount

end

variable {A : Type}

abbrev Result (α : Type) := Option α

def emptyHF : HF A := ofFinset ∅

def TC (x : HF A) : Finset (HF A) := (elements x).biUnion closure

def unionHF (x : HF A) : HF A := ofFinset ((elements x).biUnion elements)

def uniqueHF (x : HF A) : HF A :=
  if h : ∃ y, elements x = {y} then h.choose else emptyHF

def cardHF (x : HF A) : HF A := ordinal (elements x).card

def inputHF (S : Input A) (r : Symbol) (x y : HF A) : Bool :=
  decide (∃ a b, x = atom a ∧ y = atom b ∧ S.rel r a b = true)

def lift₂ {X Y Z : Type} (f : X → Y → Z) (a : Result X) (b : Result Y) : Result Z :=
  a.bind (fun x => b.map (f x))

def collect (r : HF A) (guard : HF A → Result Bool) (body : HF A → Result (HF A)) :
    Result (HF A) :=
  if (∀ x ∈ elements r, (guard x).isSome) ∧
      (∀ x ∈ elements r, guard x = some true → (body x).isSome) then
    some (ofFinset (((elements r).filter (fun x => guard x = some true)).image
      (fun x => (body x).getD emptyHF)))
  else none

def iterationLoop (p : ℕ) (step : HF A → Result (HF A)) : ℕ → HF A → Result (HF A)
  | 0, _ => some emptyHF
  | fuel+1, x =>
      if (TC x).card ≤ p then
        (step x).bind (fun y =>
          if x = y then some x else iterationLoop p step fuel y)
      else some emptyHF

def ordinaryIteration (p : ℕ) (step : HF A → Result (HF A)) : Result (HF A) :=
  iterationLoop p step (p+1) emptyHF

def resource (p : Polynomial ℝ) (n : ℕ) : ℕ := ⌊p.eval (n : ℝ)⌋₊

variable [Fintype A]

def permutationGraph (g : Equiv.Perm A) : HF A :=
  ofFinset (Finset.univ.image (fun a => pair (atom a) (atom (g a))))

def Automorphism (S : Input A) (g : Equiv.Perm A) : Prop :=
  ∀ r a b, S.rel r (g a) (g b) = S.rel r a b

def ChoicePrefix (step : HF A → HF A → Result (HF A))
    (choice : HF A → Result (HF A)) (b c : ℕ → HF A) (k : ℕ) : Prop :=
  b 0 = emptyHF ∧ ∀ i < k,
    (∃ D, choice (b i) = some D ∧ c i ∈ elements D) ∧
    step (b i) (c i) = some (b (i+1))

def StrictPrefix (b : ℕ → HF A) (k : ℕ) : Prop := ∀ i < k, b i ≠ b (i+1)

def FirstPath (step : HF A → HF A → Result (HF A))
    (choice : HF A → Result (HF A)) (b c : ℕ → HF A) (t : ℕ) : Prop :=
  ChoicePrefix step choice b c (t+1) ∧ StrictPrefix b t ∧ b t = b (t+1)

def FixesParameters {n : ℕ} (free : Finset (Fin n)) (env : Fin n → HF A)
    (g : Equiv.Perm A) : Prop := ∀ i ∈ free, g • env i = env i

def WitnessesHistory {n : ℕ} (S : Input A) (free : Finset (Fin n))
    (env : Fin n → HF A) (b : ℕ → HF A) (i : ℕ) (D M : HF A) : Prop :=
  isSet M = true ∧
  (∀ w ∈ elements M, ∃ g : Equiv.Perm A,
    w = permutationGraph g ∧ Automorphism S g ∧ FixesParameters free env g ∧
      ∀ j ≤ i, g • b j = b j) ∧
  (∀ u ∈ elements D, ∀ v ∈ elements D, ∃ g : Equiv.Perm A,
    permutationGraph g ∈ elements M ∧ g • u = v)

def GoodWSC {n : ℕ} (S : Input A) (p : ℕ) (free : Finset (Fin n))
    (env : Fin n → HF A) (step : HF A → HF A → Result (HF A))
    (choice : HF A → Result (HF A)) (witness : HF A → HF A → Result (HF A))
    (output : HF A → Result Bool) : Prop :=
  (∀ b c k, ChoicePrefix step choice b c k → StrictPrefix b k →
    k ≤ p ∧ (TC (b k)).card ≤ p ∧ ∃ D, choice (b k) = some D ∧
      (elements D).Nonempty ∧ ∀ u ∈ elements D, (step (b k) u).isSome) ∧
  (∀ b c t, FirstPath step choice b c t → t+2 ≤ p ∧
    (∀ i ≤ t, ∃ D M, choice (b i) = some D ∧ witness (b t) (b i) = some M ∧
      WitnessesHistory S free env b i D M) ∧ (output (b t)).isSome)

def witnessedIteration {n : ℕ} (S : Input A) (p : ℕ) (free : Finset (Fin n))
    (env : Fin n → HF A) (step : HF A → HF A → Result (HF A))
    (choice : HF A → Result (HF A)) (witness : HF A → HF A → Result (HF A))
    (output : HF A → Result Bool) : Result Bool :=
  if GoodWSC S p free env step choice witness output then
    some (decide (∀ b c t, FirstPath step choice b c t → output (b t) = some true))
  else none

mutual

def Term.eval (S : Input A) (p : Polynomial ℝ) : {n : ℕ} → Term n →
      (Fin n → HF A) → Result (HF A)
    | _, .var i, env => some (env i)
    | _, .empty, _ => some emptyHF
    | _, .atoms, _ => some (ofFinset (Finset.univ.image atom))
    | _, .pair a b, env => lift₂ double (a.eval S p env) (b.eval S p env)
    | _, .union a, env => (a.eval S p env).map unionHF
    | _, .unique a, env => (a.eval S p env).map uniqueHF
    | _, .card a, env => (a.eval S p env).map cardHF
    | _, .comprehend body range guard, env =>
        (range.eval S p env).bind (fun r => collect r
          (fun x => guard.eval S p (Fin.cons x env))
          (fun x => body.eval S p (Fin.cons x env)))
    | _, .iterate step, env => ordinaryIteration (resource p (Fintype.card A))
        (fun x => step.eval S p (Fin.cons x env))
  def Formula.eval (S : Input A) (p : Polynomial ℝ) : {n : ℕ} → Formula n →
      (Fin n → HF A) → Result Bool
    | _, .equal a b, env => lift₂ (fun x y => decide (x = y)) (a.eval S p env) (b.eval S p env)
    | _, .input r a b, env => lift₂ (inputHF S r) (a.eval S p env) (b.eval S p env)
    | _, .neg a, env => (a.eval S p env).map Bool.not
    | _, .and a b, env => lift₂ Bool.and (a.eval S p env) (b.eval S p env)
    | _, .or a b, env => lift₂ Bool.or (a.eval S p env) (b.eval S p env)
    | _, .wsc step choice witness output, env =>
        witnessedIteration S (resource p (Fintype.card A))
          (Formula.wsc step choice witness output).free env
          (fun x y => step.eval S p (Fin.cons y (Fin.cons x env)))
          (fun x => choice.eval S p (Fin.cons x env))
          (fun z x => witness.eval S p (Fin.cons x (Fin.cons z env)))
          (fun x => output.eval S p (Fin.cons x env))

end

structure FiniteInput where
  Carrier : Type
  finite : Fintype Carrier
  input : Input Carrier

attribute [instance] FiniteInput.finite

structure Sentence where
  formula : Formula 0
  polynomial : Polynomial ℝ

def Sentence.eval (φ : Sentence) (S : FiniteInput) : Result Bool :=
  φ.formula.eval S.input φ.polynomial Fin.elim0

def Sentence.isCPT (φ : Sentence) : Prop := φ.formula.wscCount = 0

def Sentence.BooleanOnAllInputs (φ : Sentence) : Prop :=
  ∀ S, ∃ b : Bool, φ.eval S = some b

def Sentence.TrueModels (φ : Sentence) : Set FiniteInput := {S | φ.eval S = some true}

def MainStatement : Prop := ∃ φ : Sentence,
  φ.formula.wscCount = 1 ∧ φ.BooleanOnAllInputs ∧
    ∀ ψ : Sentence, ψ.isCPT → φ.TrueModels ≠ ψ.TrueModels

end BGS

end WitnessedChoice



end
end OAI


