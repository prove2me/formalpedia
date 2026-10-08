-- Prove2me | Definitions.Def_PartitionConsistency
-- name    : PartitionConsistency
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:00.982649+00:00
-- url     : https://prove2.me/theorems/a0713734-47f9-46c9-b586-418cff724200
-- statement:
--   This block builds, inside Lean, a deductive framework for pure first-order set theory with only equality and membership. Formula n is the type of formulas with n variables in scope, built from falsum, membership, equality, implication, conjunction, disjunction, and universal and existential quantifiers, where a quantifier binds the last variable; negation and biconditional are abbreviations, and renaming, instantiation and universal closure are defined. Derives is a classical natural-deduction relation with equality, with rules for hypotheses, weakening, implication, falsum, classical contradiction, conjunction, disjunction, quantifiers using a fresh last variable, equality reflexivity and substitution, and variable renaming; derivations are finite though theories may be infinite. A theory is a set of sentences, and Consistent(T) means that for every finite number n of free variables, falsum is not derivable from T viewed with n variables. In the set-language section, abbreviations expressed as pure membership formulas define subset, empty, nonempty, unordered pair, successor, Kuratowski ordered pair, internal graph edges, function on a domain, maps-to, surjection, injection, transitive set, membership as a strict linear order, internal well-foundedness (every nonempty internal subset has a minimal element, not external well-foundedness), von Neumann ordinal, choice function, nonempty family indexed by an ordinal, and choice for such a family. From these, PP is the Partition Principle that any surjection from X onto Y yields an injection from Y into X, not required to be a section; AC is Choice for every set of nonempty sets; ACwo is choice for every ordinal-indexed family of nonempty sets. Full ZF consists of Extensionality, Empty Set, Pairing, Union, Power Set, Infinity, Foundation, and all instances of Separation and Replacement for arbitrary formulas with arbitrary parameters universally closed, without Choice. The defined theory targetTheory is ZF together with PP, ACwo and the negation of AC; the block defines this theory but does not itself prove or state that it is consistent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PartitionConsistency.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PartitionConsistency.lean; bytes 16..14606
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PartitionConsistency

/-- Pure first-order membership syntax with equality. `n` variables are in scope.
A quantifier binds the last variable in its body. There are no atoms/urelements,
function symbols, constants, semantic predicates, or mathematical assumptions
in this syntax. -/
inductive Formula : ℕ → Type where
  | bot {n} : Formula n
  | mem {n} (x y : Fin n) : Formula n
  | equal {n} (x y : Fin n) : Formula n
  | imp {n} (p q : Formula n) : Formula n
  | conj {n} (p q : Formula n) : Formula n
  | disj {n} (p q : Formula n) : Formula n
  | all {n} (p : Formula (n + 1)) : Formula n
  | ex {n} (p : Formula (n + 1)) : Formula n

namespace Formula

abbrev neg {n} (p : Formula n) : Formula n := p.imp .bot
abbrev iff {n} (p q : Formula n) : Formula n := (p.imp q).conj (q.imp p)

/-- Under a binder, a renaming leaves the newly bound variable bound. -/
def liftRen {n m} (r : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.lastCases (Fin.last m) (fun i => (r i).castSucc)

/-- Capture-avoiding renaming; in this relational language all terms are variables. -/
def rename {n m} (r : Fin n → Fin m) : Formula n → Formula m
  | .bot => .bot
  | .mem x y => .mem (r x) (r y)
  | .equal x y => .equal (r x) (r y)
  | .imp p q => .imp (rename r p) (rename r q)
  | .conj p q => .conj (rename r p) (rename r q)
  | .disj p q => .disj (rename r p) (rename r q)
  | .all p => .all (rename (liftRen r) p)
  | .ex p => .ex (rename (liftRen r) p)

abbrev raise {n} (p : Formula n) : Formula (n + 1) := rename Fin.castSucc p

/-- Substitution of a variable term for the variable just quantified. -/
def instantiate {n} (p : Formula (n + 1)) (x : Fin n) : Formula n :=
  rename (Fin.lastCases x id) p

/-- Universal closure of all the free variables. -/
def close : {n : ℕ} → Formula n → Formula 0
  | 0, p => p
  | _ + 1, p => close (.all p)

end Formula

abbrev Sentence := Formula 0
abbrev Theory := Set Sentence

/-- Classical first-order natural deduction with equality. Hypotheses may be an
infinite theory, but a derivation is a finite inductive proof. The `allI` and
`exE` rules use a fresh last variable, and shift all assumptions to avoid
capture. We allow finitely many free variables in proofs of closed sentences. -/
inductive Derives : {n : ℕ} → Set (Formula n) → Formula n → Prop where
  | hyp {n} {Γ : Set (Formula n)} {p} : p ∈ Γ → Derives Γ p
  | weaken {n} {Γ Δ : Set (Formula n)} {p} :
      Γ ⊆ Δ → Derives Γ p → Derives Δ p
  | impI {n} {Γ : Set (Formula n)} {p q} :
      Derives (insert p Γ) q → Derives Γ (.imp p q)
  | impE {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.imp p q) → Derives Γ p → Derives Γ q
  | botE {n} {Γ : Set (Formula n)} {p} : Derives Γ .bot → Derives Γ p
  | classical {n} {Γ : Set (Formula n)} {p} :
      Derives (insert p.neg Γ) .bot → Derives Γ p
  | conjI {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ p → Derives Γ q → Derives Γ (.conj p q)
  | conjL {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.conj p q) → Derives Γ p
  | conjR {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.conj p q) → Derives Γ q
  | disjL {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ p → Derives Γ (.disj p q)
  | disjR {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ q → Derives Γ (.disj p q)
  | disjE {n} {Γ : Set (Formula n)} {p q r} :
      Derives Γ (.disj p q) → Derives (insert p Γ) r →
      Derives (insert q Γ) r → Derives Γ r
  | allI {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} :
      Derives (Formula.raise '' Γ) p → Derives Γ (.all p)
  | allE {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} (t : Fin n) :
      Derives Γ (.all p) → Derives Γ (p.instantiate t)
  | exI {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} (t : Fin n) :
      Derives Γ (p.instantiate t) → Derives Γ (.ex p)
  | exE {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} {q : Formula n} :
      Derives Γ (.ex p) → Derives (insert p (Formula.raise '' Γ)) q.raise →
      Derives Γ q
  | eqRefl {n} {Γ : Set (Formula n)} (t : Fin n) : Derives Γ (.equal t t)
  | eqSubst {n} {Γ : Set (Formula n)} {s t : Fin n} (p : Formula (n + 1)) :
      Derives Γ (.equal s t) → Derives Γ (p.instantiate s) →
      Derives Γ (p.instantiate t)
  | rename {n m} {Γ : Set (Formula n)} {p : Formula n} (r : Fin n → Fin m) :
      Derives Γ p → Derives (Formula.rename r '' Γ) (Formula.rename r p)

/-- Sentences are usable as open hypotheses with any finite supply of variables. -/
def Theory.at (T : Theory) (n : ℕ) : Set (Formula n) :=
  Formula.rename Fin.elim0 '' T

/-- Ordinary syntactic consistency: there is no finite natural-deduction proof
of falsity from the theory, with any finite supply of free variables. -/
def Consistent (T : Theory) : Prop := ∀ n, ¬ Derives (T.at n) .bot

namespace SetLanguage
open Formula

/-! All abbreviations in this namespace expand to formulas of the pure language
of equality and membership. Functions are sets of Kuratowski pairs *inside the
structure*. In particular, no quantification over external Lean functions is
used in PP, Choice, or ordinal-indexed Choice. -/

/-- `a ⊆ b`. -/
def subset {n} (a b : Fin n) : Formula n :=
  rename ![a, b] (Formula.all ((Formula.mem 2 0).imp (Formula.mem 2 1)) : Formula 2)

/-- `a = ∅`. -/
def empty {n} (a : Fin n) : Formula n :=
  rename ![a] (Formula.all (Formula.mem 1 0).neg : Formula 1)

/-- `a ≠ ∅`, stated as existence of a member. -/
def nonempty {n} (a : Fin n) : Formula n :=
  rename ![a] (Formula.ex (Formula.mem 1 0) : Formula 1)

/-- `p = {x,y}`. -/
def unorderedPair {n} (p x y : Fin n) : Formula n :=
  rename ![p, x, y]
    (Formula.all ((Formula.mem 3 0).iff ((Formula.equal 3 1).disj (Formula.equal 3 2))) : Formula 3)

/-- `b = a ∪ {a}`. -/
def successor {n} (b a : Fin n) : Formula n :=
  rename ![b, a]
    (Formula.all ((Formula.mem 2 0).iff ((Formula.mem 2 1).disj (Formula.equal 2 1))) : Formula 2)

/-- Kuratowski ordered pair: `p = {{x},{x,y}}`. -/
def orderedPair {n} (p x y : Fin n) : Formula n :=
  rename ![p, x, y]
    (Formula.ex (Formula.ex ((unorderedPair 3 1 1).conj
      ((unorderedPair 4 1 2).conj (unorderedPair 0 3 4)))) : Formula 3)

/-- The internal graph relation `⟨x,y⟩ ∈ f`. -/
def edge {n} (f x y : Fin n) : Formula n :=
  rename ![f, x, y]
    (Formula.ex ((Formula.mem 3 0).conj (orderedPair 3 1 2)) : Formula 3)

/-- `f` is a set graph of a function whose domain is exactly `d`.
The first conjunct excludes non-pairs and graph entries outside the domain;
the second conjunct asserts totality and single-valuedness. -/
def functionOn {n} (f d : Fin n) : Formula n :=
  rename ![f, d]
    ((Formula.all ((Formula.mem 2 0).imp
        (Formula.ex (Formula.ex ((Formula.mem 3 1).conj (orderedPair 2 3 4)))))).conj
      (Formula.all ((Formula.mem 2 1).imp
        (Formula.ex ((edge 0 2 3).conj (Formula.all ((edge 0 2 4).imp (Formula.equal 4 3))))))) : Formula 2)

/-- Internal set function `f : d → r`. -/
def mapsTo {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((functionOn 0 1).conj
      (Formula.all (Formula.all ((Formula.mem 3 1).imp ((edge 0 3 4).imp (Formula.mem 4 2))))) : Formula 3)

/-- Internal set surjection `f : d ↠ r`. -/
def surjection {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((mapsTo 0 1 2).conj
      (Formula.all ((Formula.mem 3 2).imp (Formula.ex ((Formula.mem 4 1).conj (edge 0 4 3))))) : Formula 3)

/-- Internal set injection `f : d ↪ r`. -/
def injection {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((mapsTo 0 1 2).conj
      (Formula.all (Formula.all (.all
        ((Formula.mem 3 1).imp ((Formula.mem 4 1).imp
          (((edge 0 3 5).conj (edge 0 4 5)).imp (Formula.equal 3 4))))))) : Formula 3)

/-- Transitivity of a set (not transitivity of the external structure). -/
def transitiveSet {n} (a : Fin n) : Formula n :=
  rename ![a]
    (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 1).imp (Formula.mem 2 0)))) : Formula 1)

/-- Membership is an internal strict linear order on `a`. -/
def membershipLinear {n} (a : Fin n) : Formula n :=
  rename ![a]
    ((Formula.all ((Formula.mem 1 0).imp (Formula.mem 1 1).neg)).conj
      ((Formula.all (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 3 0).imp
        (((Formula.mem 1 2).conj (Formula.mem 2 3)).imp (Formula.mem 1 3)))))))).conj
        (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp
          ((Formula.equal 1 2).disj ((Formula.mem 1 2).disj (Formula.mem 2 1)))))))) : Formula 1)

/-- Every nonempty internal subset of `a` has a membership-minimal element.
This does NOT assert external well-foundedness of the relation. -/
def membershipWellFounded {n} (a : Fin n) : Formula n :=
  rename ![a]
    (Formula.all (((subset 1 0).conj (nonempty 1)).imp
      (Formula.ex ((Formula.mem 2 1).conj (Formula.all ((Formula.mem 3 1).imp (Formula.mem 3 2).neg))))) : Formula 1)

/-- A von Neumann ordinal: a transitive set internally wellordered by membership. -/
def ordinal {n} (a : Fin n) : Formula n :=
  (transitiveSet a).conj ((membershipLinear a).conj (membershipWellFounded a))

/-- A choice function on the set `A` of nonempty sets. -/
def choiceOn {n} (c A : Fin n) : Formula n :=
  rename ![c, A]
    ((functionOn 0 1).conj
      (Formula.all ((Formula.mem 2 1).imp (Formula.ex ((edge 0 2 3).conj (Formula.mem 3 2))))) : Formula 2)

/-- A graph `F` coding a family of nonempty sets indexed by ordinal `η`. -/
def nonemptyFamily {n} (F η : Fin n) : Formula n :=
  rename ![F, η]
    ((functionOn 0 1).conj
      (Formula.all (Formula.all ((Formula.mem 2 1).imp ((edge 0 2 3).imp (nonempty 3))))) : Formula 2)

/-- `c(ξ) ∈ F(ξ)` for every `ξ ∈ η`, with `c` an internal function. -/
def choiceForFamily {n} (c η F : Fin n) : Formula n :=
  rename ![c, η, F]
    ((functionOn 0 1).conj
      (Formula.all (Formula.all ((Formula.mem 3 1).imp ((edge 2 3 4).imp
        (Formula.ex ((edge 0 3 5).conj (Formula.mem 5 4))))))) : Formula 3)

/-- The Partition Principle. The reverse injection is not required to be a
section of the original surjection. Both `X` and `Y` range over all sets. -/
def PP : Sentence :=
  Formula.all (Formula.all ((Formula.ex (surjection 2 0 1)).imp (Formula.ex (injection 2 1 0))))

/-- Ordinary Choice for every set of nonempty sets. -/
def AC : Sentence :=
  Formula.all ((Formula.all ((Formula.mem 1 0).imp (nonempty 1))).imp (Formula.ex (choiceOn 1 0)))

/-- Choice for every ordinal-indexed family of nonempty sets, including ordinals
which may fail to be well founded from outside a model. -/
def ACwo : Sentence :=
  Formula.all ((ordinal 0).imp
    (Formula.all ((nonemptyFamily 1 0).imp (Formula.ex (choiceForFamily 2 0 1)))))

/-! Full pure-set ZF, not a finite fragment and not ZFA. -/

def extensionality : Sentence :=
  Formula.all (Formula.all ((Formula.all ((Formula.mem 2 0).iff (Formula.mem 2 1))).imp (Formula.equal 0 1)))

def emptySet : Sentence := Formula.ex (empty 0)

def pairing : Sentence := Formula.all (Formula.all (Formula.ex (unorderedPair 2 0 1)))

def union : Sentence :=
  Formula.all (Formula.ex (Formula.all ((Formula.mem 2 1).iff (Formula.ex ((Formula.mem 3 0).conj (Formula.mem 2 3))))))

def powerSet : Sentence := Formula.all (Formula.ex (Formula.all ((Formula.mem 2 1).iff (subset 2 0))))

def infinity : Sentence :=
  Formula.ex ((Formula.ex ((Formula.mem 1 0).conj (empty 1))).conj
    (Formula.all ((Formula.mem 1 0).imp (Formula.ex ((Formula.mem 2 0).conj (successor 2 1))))))

def foundation : Sentence :=
  Formula.all ((nonempty 0).imp
    (Formula.ex ((Formula.mem 1 0).conj (Formula.all ((Formula.mem 2 1).imp (Formula.mem 2 0).neg)))))

/-- The instance of Separation for an entirely arbitrary formula `p(params,x)`.
All parameters are universally closed. Neither the quantifier complexity of
`p` nor the number of parameters is bounded. -/
def separation {n} (p : Formula (n + 1)) : Sentence :=
  let A : Fin (n + 3) := (Fin.last n).castSucc.castSucc
  let B : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let x : Fin (n + 3) := Fin.last (n + 2)
  let r : Fin (n + 1) → Fin (n + 3) :=
    Fin.lastCases x (fun i => i.castSucc.castSucc.castSucc)
  close (Formula.all (Formula.ex (Formula.all ((Formula.mem x B).iff ((Formula.mem x A).conj (rename r p))))))

/-- Substitution into a binary formula with `n` additional parameters. -/
def relation {n m} (p : Formula (n + 2)) (params : Fin n → Fin m) (x y : Fin m) :
    Formula m :=
  rename (Fin.lastCases y (Fin.lastCases x params)) p

/-- The instance of Replacement for an entirely arbitrary formula
`p(params,x,y)`: if it is single-valued and total on `A`, its image is a set.
As with Separation, the parameters are all universally closed. -/
def replacement {n} (p : Formula (n + 2)) : Sentence :=
  let unique : Formula (n + 3) :=
    Formula.all ((relation p (fun i => i.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (n + 1)).castSucc.castSucc (Fin.last (n + 3))).imp
      (Formula.equal (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc))
  let totalFunctional : Formula (n + 1) :=
    Formula.all ((Formula.mem (Fin.last (n + 1)) (Fin.last n).castSucc).imp
      (Formula.ex ((relation p (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n + 1)).castSucc (Fin.last (n + 2))).conj unique)))
  let image : Formula (n + 1) :=
    Formula.ex (Formula.all ((Formula.mem (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc).iff
      (Formula.ex ((Formula.mem (Fin.last (n + 3)) (Fin.last n).castSucc.castSucc.castSucc).conj
        (relation p (fun i => i.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc)))))
  close (Formula.all (totalFunctional.imp image))

/-- Exactly the axioms and all schema instances of pure first-order ZF. -/
inductive IsZFAxiom : Sentence → Prop where
  | extensionality : IsZFAxiom extensionality
  | emptySet : IsZFAxiom emptySet
  | pairing : IsZFAxiom pairing
  | union : IsZFAxiom union
  | powerSet : IsZFAxiom powerSet
  | infinity : IsZFAxiom infinity
  | foundation : IsZFAxiom foundation
  | separation {n} (p : Formula (n + 1)) : IsZFAxiom (separation p)
  | replacement {n} (p : Formula (n + 2)) : IsZFAxiom (replacement p)

/-- Zermelo–Fraenkel set theory, without Choice. -/
def ZF : Theory := {p | IsZFAxiom p}

/-- ZF with the Partition Principle, ordinal-indexed Choice and failure of Choice. -/
def targetTheory : Theory := ZF ∪ {PP, ACwo, AC.neg}

end SetLanguage



end PartitionConsistency
end OAI


