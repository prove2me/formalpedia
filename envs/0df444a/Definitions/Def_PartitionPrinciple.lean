-- Prove2me | Definitions.Def_PartitionPrinciple
-- name    : PartitionPrinciple
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:01.185743+00:00
-- url     : https://prove2.me/theorems/1fcc54bc-b2ac-4333-bf59-a8b90c9b1547
-- statement:
--   This block develops a formal first-order language of set theory over Lean's ZFSet and several predicates on a transitive ground class. SetFormula n is the type of formulas with n free variables built from equality, membership, negation, conjunction and universal quantification, with Realize U φ env interpreting quantifiers as ranging only over a given class U of sets; existential quantification, disjunction and implication are defined from these. BoundedFormula is a variant whose universal quantifier is bounded by membership in a variable, and toFormula translates it into SetFormula. Using bounded formulas, the block encodes singletons, unordered and ordered pairs, pair membership, relations between sets, functions, nonemptiness, choice functions, injections and surjections. A TransitiveGround is a class of sets closed under taking members; InjectionCode D N f says f is a function from D to N that is injective. Relative to such a ground M, groundEmbeddable D N means some injection code from D to N lies in M, groundPower B is the part of the powerset of B lying in M, and GroundCardinal κ means κ has the ordinal-set property (it and all its members are transitive sets) and does not embed in M into any smaller member. Further predicates give GroundBelow, CofinalFunctionCode, regularity (no member of K is the domain of an M-function cofinal in K), a strong-limit condition, and GroundStandardInaccessible, which combines cardinality, not embedding into ω, regularity and strong limit. Formulas are given for extensionality, foundation, empty set, pairing, union, power set, infinity and choice, together with Separation, Collection and Replacement schemas relative to U, a finite-axiom conjunction, and ZFRealization U, saying the finite axioms hold in U along with Separation and Replacement. Finally, partitionPrinciple is a defined sentence, not a proved theorem, stating that for all sets a, b and f, if f is a function from a onto b then there is an injection from b into a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PartitionPrinciple.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PartitionPrinciple.lean; bytes 16..9348
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PartitionPilot.Forcing

universe u

inductive SetFormula : Nat → Type
  | equal {n} : Fin n → Fin n → SetFormula n
  | mem {n} : Fin n → Fin n → SetFormula n
  | neg {n} : SetFormula n → SetFormula n
  | conj {n} : SetFormula n → SetFormula n → SetFormula n
  | all {n} : SetFormula (n + 1) → SetFormula n

namespace SetFormula

def extend {A : Type u} {n : Nat} (x : A) (env : Fin n → A) : Fin (n + 1) → A :=
  Fin.cases x env

def Realize (U : Set ZFSet.{u}) : {n : Nat} → SetFormula n → (Fin n → ZFSet.{u}) → Prop
  | _, .equal i j, env => env i = env j
  | _, .mem i j, env => env i ∈ env j
  | _, .neg φ, env => ¬ Realize U φ env
  | _, .conj φ ψ, env => Realize U φ env ∧ Realize U ψ env
  | _, .all φ, env => ∀ x ∈ U, Realize U φ (extend x env)

def ex {n : Nat} (φ : SetFormula (n + 1)) : SetFormula n := .neg (.all (.neg φ))

def disj {n : Nat} (φ ψ : SetFormula n) : SetFormula n := .neg (.conj (.neg φ) (.neg ψ))

def imp {n : Nat} (φ ψ : SetFormula n) : SetFormula n := .neg (.conj φ (.neg ψ))

end SetFormula

inductive BoundedFormula : Nat → Type
  | equal {n} : Fin n → Fin n → BoundedFormula n
  | mem {n} : Fin n → Fin n → BoundedFormula n
  | neg {n} : BoundedFormula n → BoundedFormula n
  | conj {n} : BoundedFormula n → BoundedFormula n → BoundedFormula n
  | allMem {n} : Fin n → BoundedFormula (n + 1) → BoundedFormula n

namespace BoundedFormula

open SetFormula

def imp {n} (φ ψ : BoundedFormula n) : BoundedFormula n := .neg (.conj φ (.neg ψ))

def disj {n} (φ ψ : BoundedFormula n) : BoundedFormula n := .neg (.conj (.neg φ) (.neg ψ))

def exMem {n} (b : Fin n) (φ : BoundedFormula (n + 1)) : BoundedFormula n :=
  .neg (.allMem b (.neg φ))

def toFormula : {n : Nat} → BoundedFormula n → SetFormula n
  | _, .equal i j => .equal i j
  | _, .mem i j => .mem i j
  | _, .neg φ => .neg φ.toFormula
  | _, .conj φ ψ => .conj φ.toFormula ψ.toFormula
  | _, .allMem b φ => .all (SetFormula.imp (.mem 0 b.succ) φ.toFormula)

def singletonFormula {n} (z x : Fin n) : BoundedFormula n :=
  .conj (.mem x z) (.allMem z (.equal 0 x.succ))

def unorderedPairFormula {n} (z x y : Fin n) : BoundedFormula n :=
  .conj (.mem x z) (.conj (.mem y z) (.allMem z (disj (.equal 0 x.succ) (.equal 0 y.succ))))

def orderedPairFormula {n} (z x y : Fin n) : BoundedFormula n :=
  exMem z (.conj (singletonFormula 0 x.succ)
    (exMem z.succ (.conj (unorderedPairFormula 0 x.succ.succ y.succ.succ)
      (unorderedPairFormula z.succ.succ 1 0))))

def pairMembershipFormula {n} (x y r : Fin n) : BoundedFormula n :=
  exMem r (orderedPairFormula 0 x.succ y.succ)

def relationBetweenFormula {n} (a b f : Fin n) : BoundedFormula n :=
  .allMem f (exMem a.succ (exMem b.succ.succ (orderedPairFormula 2 1 0)))

def functionFormula {n} (a b f : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula a b f)
    (.allMem a (exMem b.succ (.conj (pairMembershipFormula 1 0 f.succ.succ)
      (.allMem b.succ.succ (imp (pairMembershipFormula 2 0 f.succ.succ.succ) (.equal 0 1))))))

def nonemptyFormula {n} (x : Fin n) : BoundedFormula n := exMem x (.equal 0 0)

def choiceFunctionFormula {n} (a f : Fin n) : BoundedFormula n :=
  .conj (.allMem f (exMem a.succ (exMem 0 (orderedPairFormula 2 1 0))))
    (.allMem a (exMem 0 (.conj (pairMembershipFormula 1 0 f.succ.succ)
      (.allMem 1 (imp (pairMembershipFormula 2 0 f.succ.succ.succ) (.equal 0 1))))))

end BoundedFormula

structure TransitiveGround where
  sets : Set ZFSet.{u}
  transitive : ∀ {x y}, x ∈ sets → y ∈ x → y ∈ sets

structure InjectionCode (D N f : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc D N f
  injective : ∀ x y z, ZFSet.pair x z ∈ f → ZFSet.pair y z ∈ f → x = y

namespace TransitiveGround

open SetFormula

variable (M : TransitiveGround.{u})

def groundEmbeddable (D N : ZFSet.{u}) : Prop := ∃ f ∈ M.sets, InjectionCode D N f

end TransitiveGround

def setTransitive (x : ZFSet.{u}) : Prop := ∀ y ∈ x, ∀ z ∈ y, z ∈ x

def ordinalSetProperty (x : ZFSet.{u}) : Prop :=
  setTransitive x ∧ ∀ y ∈ x, setTransitive y

namespace TransitiveGround

open SetFormula

variable (M : TransitiveGround.{u})

noncomputable def groundPower (B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => p ∈ M.sets) (ZFSet.powerset B)

end TransitiveGround

def GroundBelow (M : TransitiveGround.{u}) (A K : ZFSet.{u}) : Prop :=
  ∃ β ∈ K, M.groundEmbeddable A β

def GroundCardinal (M : TransitiveGround.{u}) (κ : ZFSet.{u}) : Prop :=
  ordinalSetProperty κ ∧ ∀ β ∈ κ, ¬ M.groundEmbeddable κ β

def CofinalFunctionCode (α K f : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc α K f ∧ ∀ β ∈ K, ∃ x ∈ α, ∃ y ∈ K,
    ZFSet.pair x y ∈ f ∧ (β = y ∨ β ∈ y)

def GroundCofinalRegular (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  ∀ α ∈ K, ∀ f ∈ M.sets, ¬ CofinalFunctionCode α K f

def GroundCardinalStrongLimit (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  ∀ κ ∈ K, GroundCardinal M κ → GroundBelow M (M.groundPower κ) K

def GroundStandardInaccessible (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  GroundCardinal M K ∧ ¬ M.groundEmbeddable K ZFSet.omega ∧
    GroundCofinalRegular M K ∧ GroundCardinalStrongLimit M K

namespace SetFormula

def extensionality : SetFormula 0 :=
  .all (.all (imp
    (.all (.conj (imp (.mem 0 2) (.mem 0 1)) (imp (.mem 0 1) (.mem 0 2))))
    (.equal 1 0)))

def foundation : SetFormula 0 :=
  .all (imp (ex (.mem 0 1))
    (ex (.conj (.mem 0 1) (.all (.neg (.conj (.mem 0 2) (.mem 0 1)))))))

def emptySet : SetFormula 0 := ex (.all (.neg (.mem 0 1)))

def pairing : SetFormula 0 :=
  .all (.all (ex (.all (.conj
    (imp (.mem 0 1) (disj (.equal 0 3) (.equal 0 2)))
    (imp (disj (.equal 0 3) (.equal 0 2)) (.mem 0 1))))))

def union : SetFormula 0 :=
  .all (ex (.all (.conj
    (imp (.mem 0 1) (ex (.conj (.mem 0 3) (.mem 1 0))))
    (imp (ex (.conj (.mem 0 3) (.mem 1 0))) (.mem 0 1)))))

def powerSet : SetFormula 0 :=
  .all (ex (.all (.conj
    (imp (.mem 0 1) (.all (imp (.mem 0 1) (.mem 0 3))))
    (imp (.all (imp (.mem 0 1) (.mem 0 3))) (.mem 0 1)))))

def SeparationSchema (U : Set ZFSet.{u}) : Prop :=
  ∀ {n} (φ : SetFormula (n + 1)) (params : Fin n → ZFSet.{u}),
    (∀ i, params i ∈ U) → ∀ x ∈ U, ∃ y ∈ U,
      ∀ z ∈ U, z ∈ y ↔ z ∈ x ∧ Realize U φ (extend z params)

def CollectionSchema (U : Set ZFSet.{u}) : Prop :=
  ∀ {n} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u}),
    (∀ i, params i ∈ U) → ∀ a ∈ U,
      (∀ x ∈ U, x ∈ a → ∃ y ∈ U, Realize U φ (extend x (extend y params))) →
      ∃ b ∈ U, ∀ x ∈ U, x ∈ a →
        ∃ y ∈ U, y ∈ b ∧ Realize U φ (extend x (extend y params))

def emptySetFormula {n : Nat} (x : Fin n) : SetFormula n := .all (.neg (.mem 0 x.succ))

def successorFormula {n : Nat} (y x : Fin n) : SetFormula n :=
  .all (.conj (imp (.mem 0 y.succ) (disj (.equal 0 x.succ) (.mem 0 x.succ)))
    (imp (disj (.equal 0 x.succ) (.mem 0 x.succ)) (.mem 0 y.succ)))

def infinity : SetFormula 0 :=
  ex (.conj (ex (.conj (.mem 0 1) (emptySetFormula 0)))
    (.all (imp (.mem 0 1) (ex (.conj (.mem 0 2) (successorFormula 0 1))))))

def choice : SetFormula 0 :=
  .all (imp (BoundedFormula.allMem 0 (BoundedFormula.nonemptyFormula 0)).toFormula
    (ex (BoundedFormula.choiceFunctionFormula 1 0).toFormula))

def ReplacementSchema (U : Set ZFSet.{u}) : Prop :=
  ∀ {n} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u}),
    (∀ i, params i ∈ U) → ∀ A ∈ U,
      (∀ x ∈ U, x ∈ A → ∃ y ∈ U, Realize U φ (extend x (extend y params)) ∧
        ∀ z ∈ U, Realize U φ (extend x (extend z params)) → z = y) →
      ∃ B ∈ U, ∀ y ∈ U, y ∈ B ↔ ∃ x ∈ U, x ∈ A ∧ Realize U φ (extend x (extend y params))

def finiteZFAxioms : SetFormula 0 :=
  .conj extensionality (.conj foundation (.conj emptySet
    (.conj pairing (.conj SetFormula.union (.conj powerSet infinity)))))

def ZFRealization (U : Set ZFSet.{u}) : Prop :=
  Realize U finiteZFAxioms Fin.elim0 ∧ SeparationSchema U ∧ ReplacementSchema U

end SetFormula

namespace BoundedFormula

open SetFormula

def injectionFormula {n} (d c f : Fin n) : BoundedFormula n :=
  .conj (functionFormula d c f) (.allMem d (.allMem d.succ (.allMem c.succ.succ
    (imp (.conj (pairMembershipFormula 2 0 f.succ.succ.succ)
      (pairMembershipFormula 1 0 f.succ.succ.succ)) (.equal 2 1)))))

end BoundedFormula

namespace SetFormula

def hasInjectionFormula {n} (d c : Fin n) : SetFormula n :=
  ex (BoundedFormula.injectionFormula d.succ c.succ 0).toFormula

end SetFormula

namespace BoundedFormula

open SetFormula

def surjectionFormula {n : Nat} (a b f : Fin n) : BoundedFormula n :=
  .conj (functionFormula a b f)
    (.allMem b (exMem a.succ (pairMembershipFormula 0 1 f.succ.succ)))

end BoundedFormula

namespace SetFormula

def partitionPrinciple : SetFormula 0 :=
  .all (.all (.all (imp (BoundedFormula.surjectionFormula (n := 3) 2 1 0).toFormula
    (hasInjectionFormula (n := 3) 1 2))))

end SetFormula

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula

universe u

variable (M : TransitiveGround.{u})



end PartitionPilot.Forcing.TransitiveGround
end OAI


