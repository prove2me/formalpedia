-- Prove2me | Definitions.Def_definable_saturated_fol
-- name    : definable_saturated_fol
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T22:48:29.820811+00:00
-- url     : https://prove2.me/theorems/f04aa67a-9ed7-4529-b958-67fb942ce87a
-- title:
--   First-order set theory, satisfaction, ordinal definability, and cardinality
-- statement:
--   This bundle provides the **first-order set-theory layer** used by the definable-saturated consistency theorem. All notions are formulas interpreted *inside* a first-order model of set theory.
--
--   It defines: (1) the language of set theory with function symbols $\emptyset,\omega,\mathcal P,\bigcup,(\cdot,\cdot)$ and relation $\in$, together with depth-polymorphic terms and formulas and the finite axiom list **ZFC**; (2) formula **composition** helpers for building predicates; (3) a recursive **satisfaction** relation on finite formula trees and finite assignment graphs; (4) **rank segments** $V_\alpha$; (5) **ordinal definability** — unique definition over a rank segment from finitely many ordinal parameters; and (6) **cardinality** predicates expressing countability, equicardinality, the first uncountable ordinal $\omega_1$, and cardinality $\aleph_1$.
--
--   These definitions are the shared foundation for the arithmetic-coding layer and the final Scott sentence; they are reusable for any first-order formalization of set-theoretic definability and cardinality.
--
--   **Formalization Note.** Formulas are `Language.BoundedFormula` values; the satisfaction relation is defined internally to set theory rather than via the ambient metatheory.
-- source:
--   https://github.com/elliotglazer/definable-saturated/blob/6d4822c80dd683360e43a39043296d27b5dd3254/DefinableSaturated/Challenge.lean#L45-L410

/- Transplanted from elliotglazer/definable-saturated, DefinableSaturated/Challenge.lean (Apache 2.0, (c) 2026 Elliot Glazer). -/
import Mathlib.ModelTheory.Satisfiability

open FirstOrder FirstOrder.Language
open scoped FirstOrder
namespace Erdos501.FOL
/-- Function symbols: `∅` (arity 0), `ω` (arity 0), `𝒫` (arity 1), `⋃` (arity 1),
the ordered pair `(·,·)` (arity 2). -/
inductive Func : ℕ → Type
  | emptyset : Func 0
  | omega : Func 0
  | powerset : Func 1
  | union : Func 1
  | pair : Func 2
/-- Relation symbols: `∈` (arity 2). -/
inductive Rel : ℕ → Type
  | mem : Rel 2
/-- The first-order language of set theory used here: `∅, ω, 𝒫, ⋃, (·,·)` and `∈`. -/
abbrev L : Language := ⟨Func, Rel⟩
/-- Depth-polymorphic formulas. -/
abbrev Fm : Type := ∀ n : ℕ, L.BoundedFormula Empty n
/-- Depth-polymorphic terms. -/
abbrev Tm : Type := ∀ n : ℕ, L.Term (Empty ⊕ Fin n)
/-- The variable of de Bruijn level `ℓ` (`0` = outermost).  (For `ℓ ≥ n` — never
used — it is the constant `∅`.) -/
def varT (ℓ : ℕ) : Tm := fun n =>
  if h : ℓ < n then Term.var (Sum.inr ⟨ℓ, h⟩) else Term.func Func.emptyset Fin.elim0
/-- The constant `∅`. -/
def empT : Tm := fun _ => Term.func Func.emptyset Fin.elim0
/-- The constant `ω`. -/
def omT : Tm := fun _ => Term.func Func.omega Fin.elim0
/-- The power set `𝒫 t`. -/
def powT (t : Tm) : Tm := fun n => Term.func Func.powerset ![t n]
/-- The union `⋃ t`. -/
def unionT (t : Tm) : Tm := fun n => Term.func Func.union ![t n]
/-- The ordered pair `(s, t)`. -/
def pairT (s t : Tm) : Tm := fun n => Term.func Func.pair ![s n, t n]
/-- `s ∈ t`. -/
def memF (s t : Tm) : Fm := fun n => Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (s n) (t n)
/-- `s = t`. -/
def eqF (s t : Tm) : Fm := fun n => Term.bdEqual (s n) (t n)
/-- The pointwise conjunction `φ ∧ ψ` of two depth-polymorphic formulas. -/
def andF (φ ψ : Fm) : Fm := fun n => φ n ⊓ ψ n
/-- The pointwise disjunction `φ ∨ ψ` of two depth-polymorphic formulas. -/
def orF (φ ψ : Fm) : Fm := fun n => φ n ⊔ ψ n
/-- The pointwise implication `φ → ψ` of two depth-polymorphic formulas. -/
def impF (φ ψ : Fm) : Fm := fun n => (φ n).imp (ψ n)
/-- The pointwise biconditional `φ ↔ ψ` of two depth-polymorphic formulas. -/
def iffF (φ ψ : Fm) : Fm := fun n => (φ n).iff (ψ n)
/-- The pointwise negation `¬φ` of a depth-polymorphic formula. -/
def notF (φ : Fm) : Fm := fun n => (φ n).not
/-- `∀ x, φ x`; the body receives the *level* of the bound variable. -/
def allF (φ : ℕ → Fm) : Fm := fun n => (φ n (n + 1)).all
/-- `∃ x, φ x`; the body receives the *level* of the bound variable. -/
def exF (φ : ℕ → Fm) : Fm := fun n => (φ n (n + 1)).ex
/-- `∀ x ∈ t, φ x`. -/
def allIn (t : Tm) (φ : ℕ → Fm) : Fm := allF fun x => impF (memF (varT x) t) (φ x)
/-- `∃ x ∈ t, φ x`. -/
def exIn (t : Tm) (φ : ℕ → Fm) : Fm := exF fun x => andF (memF (varT x) t) (φ x)
/-- Conjunction of a list of formulas (`⊤` for the empty list). -/
def andsF : List Fm → Fm
  | [] => notF (fun _ => ⊥)
  | [φ] => φ
  | φ :: φs => andF φ (andsF φs)
/-- The sentence denoted by a depth-polymorphic formula (evaluation at depth `0`). -/
def toSentence (φ : Fm) : L.Sentence := φ 0
/-- `s ⊆ t`. -/
def subsetF (s t : Tm) : Fm := allF fun z => impF (memF (varT z) s) (memF (varT z) t)
/-- `∀ x, x ∉ ∅`. -/
def axiomOfEmptyset : L.Sentence := toSentence <|
  allF fun x => notF (memF (varT x) empT)
/-- `∀ x y z w, (x, y) = (z, w) ↔ x = z ∧ y = w`: the pairing symbol produces
ordered pairs. -/
def axiomOfOrderedPairs : L.Sentence := toSentence <|
  allF fun x => allF fun y => allF fun z => allF fun w =>
    iffF (eqF (pairT (varT x) (varT y)) (pairT (varT z) (varT w)))
      (andF (eqF (varT x) (varT z)) (eqF (varT y) (varT w)))
/-- `∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
def axiomOfExtensionality : L.Sentence := toSentence <|
  allF fun x => allF fun y =>
    impF (allF fun z => iffF (memF (varT z) (varT x)) (memF (varT z) (varT y)))
      (eqF (varT x) (varT y))
/-- `∀ u x, x ∈ ⋃ u ↔ ∃ y, y ∈ u ∧ x ∈ y`. -/
def axiomOfUnion : L.Sentence := toSentence <|
  allF fun u => allF fun x =>
    iffF (memF (varT x) (unionT (varT u)))
      (exF fun y => andF (memF (varT y) (varT u)) (memF (varT x) (varT y)))
/-- `∀ z y, y ∈ 𝒫 z ↔ ∀ x, x ∈ y → x ∈ z`. -/
def axiomOfPowerset : L.Sentence := toSentence <|
  allF fun z => allF fun y =>
    iffF (memF (varT y) (powT (varT z)))
      (allF fun x => impF (memF (varT x) (varT y)) (memF (varT x) (varT z)))
/-- `a` (a variable level) is an ordinal: `∈` is trichotomous and well-founded on
`a`, and `a` is transitive. -/
def ordF (a : ℕ) : Fm :=
  andF
    (andF
      -- ∈-trichotomy on `a`
      (allF fun y => impF (memF (varT y) (varT a)) (allF fun z => impF (memF (varT z) (varT a))
        (orF (orF (eqF (varT y) (varT z)) (memF (varT y) (varT z))) (memF (varT z) (varT y)))))
      -- ∈-well-foundedness on `a`: every nonempty subset has an ∈-minimal element
      (allF fun y => impF (subsetF (varT y) (varT a)) (impF (notF (eqF (varT y) empT))
        (exF fun z => andF (memF (varT z) (varT y))
          (allF fun w => impF (memF (varT w) (varT y)) (notF (memF (varT w) (varT z))))))))
    -- transitivity of `a`
    (allF fun y => impF (memF (varT y) (varT a)) (subsetF (varT y) (varT a)))
/-- Infinity: `∅ ∈ ω`, `ω` is closed under "there is a larger element", `ω` is an
ordinal, and `ω` is contained in every ordinal `a` with `∅ ∈ a` closed under
"there is a larger element" — i.e. `ω` is the least infinite ordinal. -/
def axiomOfInfinity : L.Sentence := toSentence <|
  andF
    (andF
      (andF
        (memF empT omT)
        (allF fun x => impF (memF (varT x) omT)
          (exF fun y => andF (memF (varT y) omT) (memF (varT x) (varT y)))))
      (exF fun a => andF (ordF a) (eqF omT (varT a))))
    (allF fun a => impF (ordF a) (impF
      (andF (memF empT (varT a))
        (allF fun x => impF (memF (varT x) (varT a))
          (exF fun y => andF (memF (varT y) (varT a)) (memF (varT x) (varT y)))))
      (subsetF omT (varT a))))
/-- `∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y`. -/
def axiomOfRegularity : L.Sentence := toSentence <|
  allF fun x => impF (notF (eqF (varT x) empT))
    (exF fun y => andF (memF (varT y) (varT x))
      (allF fun z => impF (memF (varT z) (varT x)) (notF (memF (varT z) (varT y)))))
/-- Zorn's lemma: if `x ≠ ∅` and the union of every chain `y ⊆ x` (a subset of `x`
linearly ordered by `⊆`) belongs to `x`, then `x` has a `⊆`-maximal element. -/
def zornsLemma : L.Sentence := toSentence <|
  allF fun x => impF (notF (eqF (varT x) empT)) (impF
    (allF fun y => impF
      (andF (subsetF (varT y) (varT x))
        (allF fun w₁ => allF fun w₂ =>
          impF (andF (memF (varT w₁) (varT y)) (memF (varT w₂) (varT y)))
            (orF (subsetF (varT w₁) (varT w₂)) (subsetF (varT w₂) (varT w₁)))))
      (memF (unionT (varT y)) (varT x)))
    (exF fun m => andF (memF (varT m) (varT x))
      (allF fun z => impF (memF (varT z) (varT x))
        (impF (subsetF (varT m) (varT z)) (eqF (varT m) (varT z))))))
/-- Strong collection for the formula `ψ`, whose bound variables are the `n`
parameters `&0, …, &(n-1)`, `x = &n` and `y = &(n+1)`:

`∀ params, ∀ u, (∀ x ∈ u, ∃ y, ψ) → ∃ v, (∀ x ∈ u, ∃ y ∈ v, ψ) ∧ (∀ y ∈ v, ∃ x ∈ u, ψ)`.

`ψ.liftAt k n` is `ψ` with `k` new variables inserted at level `n` (i.e. below
`x` and `y`, above the parameters); in the last conjunct the roles of the two
innermost variables are exchanged by introducing a copy `y'` of `y`.  The
levels of the variables in the three clauses are (`p` = parameters):
`p, u, x, y`; `p, u, v, x, y`; `p, u, v, y, x, y'`. -/
def collectionAxiom (n : ℕ) (ψ : L.BoundedFormula Empty (n + 2)) : L.Sentence :=
  BoundedFormula.alls (n := n + 1) <|
    BoundedFormula.imp
      -- ∀ x ∈ u, ∃ y, ψ                                    (levels: p, u, x, y)
      (BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 1, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) (BoundedFormula.ex (ψ.liftAt 1 n))))
      (BoundedFormula.ex
        -- ∀ x ∈ u, ∃ y ∈ v, ψ                              (levels: p, u, v, x, y)
        ((BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 2, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) (BoundedFormula.ex ((Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 3, by omega⟩)) (Term.var (Sum.inr ⟨n + 1, by omega⟩))) ⊓ (ψ.liftAt 2 n))))) ⊓
         -- ∀ y ∈ v, ∃ x ∈ u, ∃ y', y' = y ∧ ψ              (levels: p, u, v, y, x, y')
         (BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 2, by omega⟩)) (Term.var (Sum.inr ⟨n + 1, by omega⟩))) (BoundedFormula.ex ((Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 3, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) ⊓ (BoundedFormula.ex ((Term.bdEqual (Term.var (Sum.inr ⟨n + 4, by omega⟩)) (Term.var (Sum.inr ⟨n + 2, by omega⟩))) ⊓ (ψ.liftAt 3 n)))))))))
/-- **The theory `ZFC`**: extensionality, empty set, ordered pairs, union, power
set, infinity, regularity, Zorn's lemma, and the strong collection scheme.  This
is the axiom system of Han–van Doorn's Flypitch formalization of ZFC; it is
equivalent to the usual ZFC. -/
def ZFC : L.Theory :=
  {axiomOfEmptyset, axiomOfOrderedPairs, axiomOfExtensionality, axiomOfUnion,
    axiomOfPowerset, axiomOfInfinity, axiomOfRegularity, zornsLemma} ∪
  ⋃ n : ℕ, Set.range (collectionAxiom n)
/-- `f(x) = y`, for a function `f` given as a set of ordered pairs. -/
def appF (f x y : Tm) : Fm := memF (pairT x y) f
/-- `op(x, y) = z`, for a binary operation `op` given as a set of pairs `((x, y), z)`. -/
def app2F (op x y z : Tm) : Fm := memF (pairT (pairT x y) z) op
/-- `f` is a (total, single-valued) function from `dom` to `cod`: every `x ∈ dom`
has exactly one `f`-value, and it lies in `cod`. -/
def isFunF (dom cod f : Tm) : Fm :=
  allIn dom fun x => exIn cod fun y =>
    andF (appF f (varT x) (varT y))
      (allF fun y' => impF (appF f (varT x) (varT y')) (eqF (varT y') (varT y)))
/-- `m = n ∪ {n}` (the successor of `n`). -/
def succF (n m : Tm) : Fm :=
  allF fun z => iffF (memF (varT z) m) (orF (memF (varT z) n) (eqF (varT z) n))
end Erdos501.FOL
namespace Scotts.FOL.Composition
open Erdos501.FOL
universe u v w
variable {K : Language.{u, v}} {M : Type w} [K.Structure M] {k n : ℕ}
/-- Expose the current bounded variables as a finite tuple of free variables. -/
def freeFormula (φ : K.BoundedFormula Empty k) : K.Formula (Fin k) :=
  φ.toFormula.relabel (Sum.elim Empty.elim id)
/-- Substitute arbitrary terms for the predicate's arguments, then bind their variables
in the ambient context. The original predicate's quantifiers remain capture-free. -/
def insertFormula (φ : K.BoundedFormula Empty k)
    (ts : Fin k → K.Term (Empty ⊕ Fin n)) : K.BoundedFormula Empty n :=
  BoundedFormula.relabel Sum.inr
    ((freeFormula φ).subst (fun i => (ts i).relabel (Sum.elim Empty.elim id)))
/-- Depth-polymorphic version for the manuscript's formula-building notation. -/
def predicateF {k : ℕ} (φ : L.BoundedFormula Empty k) (ts : Fin k → Tm) : Fm :=
  fun n => insertFormula φ (fun i => ts i n)
end Scotts.FOL.Composition
namespace Scotts.FOL.Satisfaction
open Erdos501.FOL Scotts.FOL.Composition
/-- A closed term for `V_k`, used only for the five fixed syntax tags. -/
def tagT : ℕ → Tm
  | 0 => empT
  | k + 1 => powT (tagT k)
/-- The set code for the falsity node of a set-theory formula tree. -/
def botT : Tm := pairT (tagT 0) empT
/-- The set code for the atomic equality node with variable indices `i` and `j`. -/
def equalT (i j : Tm) : Tm := pairT (tagT 1) (pairT i j)
/-- The set code for the atomic membership node with variable indices `i` and `j`. -/
def memT (i j : Tm) : Tm := pairT (tagT 2) (pairT i j)
/-- The set code for the implication node with immediate subformulas `φ` and `ψ`. -/
def impT (φ ψ : Tm) : Tm := pairT (tagT 3) (pairT φ ψ)
/-- The set code for the universal-quantifier node with body `φ`. -/
def allT (φ : Tm) : Tm := pairT (tagT 4) φ
/-- An entry records the formula tree, the assignment length, and its finite graph. -/
def holdsF (S n φ v : Tm) : Fm := memF (pairT φ (pairT n v)) S
/-- Total function on the specified domain, with no unrelated pairs or other junk in its graph. -/
def assignmentF (n A v : Tm) : Fm := andF (isFunF n A v)
  (allIn v fun z => exIn n fun i => exIn A fun x =>
    eqF (varT z) (pairT (varT i) (varT x)))
/-- Appending a value at the new final natural-number index. -/
def appendF (n v x w : Tm) : Fm := allF fun z =>
  iffF (memF (varT z) w)
    (orF (memF (varT z) v) (eqF (varT z) (pairT n x)))
/-- `F` contains both children of every implication code in `F` and the body of every universal code in `F`. -/
def subformulasClosedF (F : Tm) : Fm := andF
  (allF fun φ => allF fun ψ =>
    impF (memF (impT (varT φ) (varT ψ)) F)
      (andF (memF (varT φ) F) (memF (varT ψ) F)))
  (allF fun φ => impF (memF (allT (varT φ)) F) (memF (varT φ) F))
/-- The five concrete recursion clauses, evaluated only on finite assignment graphs. -/
def recursionF (A F S : Tm) : Fm := andF (subformulasClosedF F)
  (allIn omT fun n => allF fun v =>
    impF (assignmentF (varT n) A (varT v)) (andsF [
      impF (memF botT F) (notF (holdsF S (varT n) botT (varT v))),
      allIn omT fun i => allIn omT fun j =>
        impF (memF (equalT (varT i) (varT j)) F)
          (iffF (holdsF S (varT n) (equalT (varT i) (varT j)) (varT v))
            (exIn A fun x => exIn A fun y => andsF [
              appF (varT v) (varT i) (varT x),
              appF (varT v) (varT j) (varT y), eqF (varT x) (varT y)])),
      allIn omT fun i => allIn omT fun j =>
        impF (memF (memT (varT i) (varT j)) F)
          (iffF (holdsF S (varT n) (memT (varT i) (varT j)) (varT v))
            (exIn A fun x => exIn A fun y => andsF [
              appF (varT v) (varT i) (varT x),
              appF (varT v) (varT j) (varT y), memF (varT x) (varT y)])),
      allF fun φ => allF fun ψ =>
        impF (memF (impT (varT φ) (varT ψ)) F)
          (iffF (holdsF S (varT n) (impT (varT φ) (varT ψ)) (varT v))
            (impF (holdsF S (varT n) (varT φ) (varT v))
              (holdsF S (varT n) (varT ψ) (varT v)))),
      allF fun φ => impF (memF (allT (varT φ)) F)
        (iffF (holdsF S (varT n) (allT (varT φ)) (varT v))
          (allIn A fun x => exF fun m => exF fun w => andsF [
            succF (varT n) (varT m),
            appendF (varT n) (varT v) (varT x) (varT w),
            holdsF S (varT m) (varT φ) (varT w)]))
    ]))
/-- The actual first-order predicate with variables `A,F,S`, in that order. -/
def recursionFormula : L.BoundedFormula Empty 3 :=
  recursionF (varT 0) (varT 1) (varT 2) 3
/-- An actual first-order satisfaction predicate, witnessed by a recursion certificate. -/
def satisfactionF (A φ n v : Tm) : Fm := exF fun F => exF fun S => andsF [
  recursionF A (varT F) (varT S), memF φ (varT F), holdsF (varT S) n φ v]
/-- Variables are the domain, tree code, assignment length, and assignment graph. -/
def satisfactionFormula : L.BoundedFormula Empty 4 :=
  satisfactionF (varT 0) (varT 1) (varT 2) (varT 3) 4
/-- A set is closed under the five literal formula-code constructors. -/
def constructorClosedF (D : Tm) : Fm := andsF [
  memF botT D,
  allIn omT fun i => allIn omT fun j => memF (equalT (varT i) (varT j)) D,
  allIn omT fun i => allIn omT fun j => memF (memT (varT i) (varT j)) D,
  allIn D fun φ => allIn D fun ψ => memF (impT (varT φ) (varT ψ)) D,
  allIn D fun φ => memF (allT (varT φ)) D]
/-- Least-closed-set characterization of actual finite tree codes. -/
def treeCodeF (φ : Tm) : Fm := allF fun D => impF (constructorClosedF (varT D))
  (memF φ (varT D))
/-- Unary predicate saying that a set is a genuine finite set-theory formula-tree code. -/
def treeCodeFormula : L.BoundedFormula Empty 1 := treeCodeF (varT 0) 1
end Scotts.FOL.Satisfaction
namespace Scotts.FOL.RankLevels
open Erdos501.FOL
/-- `i` lies in the ordinal successor `θ + 1`, expressed as `i ∈ θ ∨ i = θ`. -/
def inSuccessorF (i θ : Tm) : Fm := orF (memF i θ) (eqF i θ)
/-- `h` is the full graph on `θ + 1` of the cumulative-rank recursion `i ↦ V_i`. -/
def rankHierarchyF (θ h : Tm) : Fm := andF
  (allF fun i => impF (inSuccessorF (varT i) θ)
    (exF fun V => andF (appF h (varT i) (varT V))
      (allF fun W => impF (appF h (varT i) (varT W)) (eqF (varT W) (varT V)))))
  (andF
    (allIn h fun z => exF fun i => andF (inSuccessorF (varT i) θ)
      (exF fun V => eqF (varT z) (pairT (varT i) (varT V))))
    (allF fun i => allF fun V => impF (appF h (varT i) (varT V))
      (allF fun x => iffF (memF (varT x) (varT V))
        (exIn (varT i) fun j => exF fun U => andF (appF h (varT j) (varT U))
          (subsetF (varT x) (varT U))))))
/-- `V` is the `θ`-th value of a cumulative-rank hierarchy, hence `V = V_θ` for ordinal `θ`. -/
def rankLevelF (θ V : Tm) : Fm :=
  exF fun h => andF (rankHierarchyF θ (varT h)) (appF (varT h) θ V)
/-- Binary first-order predicate saying that `h` is the cumulative-rank hierarchy through `θ`. -/
def rankHierarchyFormula : L.BoundedFormula Empty 2 := rankHierarchyF (varT 0) (varT 1) 2
/-- Binary first-order predicate saying that `V` is the rank segment `V_θ`. -/
def rankLevelFormula : L.BoundedFormula Empty 2 := rankLevelF (varT 0) (varT 1) 2
end Scotts.FOL.RankLevels
namespace Scotts.FOL.OrdinalDefinitions
open Erdos501.FOL
open Scotts.FOL.Composition Scotts.FOL.Satisfaction Scotts.FOL.RankLevels
/-- `x` is transitive: every member of `x` is a subset of `x`. -/
def transitiveF (x : Tm) : Fm := allIn x fun y => subsetF (varT y) x
/-- `x` is a von Neumann ordinal: it and each of its members are transitive. -/
def ordinalF (x : Tm) : Fm := andF (transitiveF x)
  (allIn x fun y => transitiveF (varT y))
/-- Unary first-order predicate saying that its argument is a von Neumann ordinal. -/
def ordinalFormula : L.BoundedFormula Empty 1 := ordinalF (varT 0) 1
/-- `x` satisfies `φ` in `A` under the finite assignment `p` extended by `x` in the last position. -/
def lastRealizationF (A φ n p x : Tm) : Fm := exF fun m => exF fun w => andsF [
  succF n (varT m), Satisfaction.appendF n p x (varT w),
  predicateF satisfactionFormula ![A, φ, varT m, varT w] ]
/-- `x` is uniquely defined over some rank segment by a finite formula and finitely many ordinal parameters. -/
def definitionF (x : Tm) : Fm :=
  exF fun θ => exF fun A => exF fun φ => exF fun n => exF fun p => andsF [
    predicateF ordinalFormula ![varT θ],
    predicateF rankLevelFormula ![varT θ, varT A],
    predicateF treeCodeFormula ![varT φ],
    memF (varT n) omT,
    assignmentF (varT n) (varT θ) (varT p), memF x (varT A),
    allIn (varT A) fun y => iffF
      (lastRealizationF (varT A) (varT φ) (varT n) (varT p) (varT y))
      (eqF (varT y) x)]
/-- A concrete first-order predicate, with one free object variable. -/
def definitionFormula : L.BoundedFormula Empty 1 := definitionF (varT 0) 1
end Scotts.FOL.OrdinalDefinitions
namespace Scotts.FOL.SetCardinality
open Erdos501.FOL
open Scotts.FOL
open Scotts.FOL.Composition Scotts.FOL.OrdinalDefinitions
/-- The graph `g` is injective on `A`: equal output values for inputs in `A` force equal inputs. -/
def injectiveF (A g : Tm) : Fm := allIn A fun x => allIn A fun y => allF fun z =>
  impF (appF g (varT x) (varT z))
    (impF (appF g (varT y) (varT z)) (eqF (varT x) (varT y)))
/-- The graph `g` maps some member of `A` to every member of `B`. -/
def ontoF (A B g : Tm) : Fm := allIn B fun y => exIn A fun x => appF g (varT x) (varT y)
/-- `g` is the graph of a total injective function from `A` to `B`. -/
def injectionF (A B g : Tm) : Fm :=
  andF (Satisfaction.assignmentF A B g) (injectiveF A g)
/-- `g` is the graph of a bijection from `A` onto `B`. -/
def bijectionF (A B g : Tm) : Fm := andF (injectionF A B g) (ontoF A B g)
/-- Unary predicate saying that its argument injects into `ω`, hence is countable. -/
def countableFormula : L.BoundedFormula Empty 1 :=
  (exF fun g => injectionF (varT 0) omT (varT g)) 1
/-- Binary predicate saying that its arguments are in bijection. -/
def sameCardinalityFormula : L.BoundedFormula Empty 2 :=
  (exF fun g => bijectionF (varT 0) (varT 1) (varT g)) 2
/-- Depth-polymorphic insertion of the unary countability predicate at the term `A`. -/
def countableF (A : Tm) : Fm := Composition.predicateF countableFormula ![A]
/-- Depth-polymorphic insertion of the unary ordinal predicate at the term `A`. -/
def ordinalF (A : Tm) : Fm := Composition.predicateF OrdinalDefinitions.ordinalFormula ![A]
/-- Depth-polymorphic assertion that the sets denoted by `A` and `B` are in bijection. -/
def sameCardinalityF (A B : Tm) : Fm := Composition.predicateF sameCardinalityFormula ![A, B]
/-- Unary predicate defining the first uncountable ordinal: an uncountable ordinal all of whose members are countable. -/
def omegaOneFormula : L.BoundedFormula Empty 1 :=
  (andF (ordinalF (varT 0)) (andF (notF (countableF (varT 0)))
    (allIn (varT 0) fun x => countableF (varT x)))) 1
/-- Depth-polymorphic assertion that the term `A` denotes the first uncountable ordinal. -/
def omegaOneF (A : Tm) : Fm := Composition.predicateF omegaOneFormula ![A]
/-- Unary predicate saying that its argument is in bijection with the first uncountable ordinal. -/
def sizeAlephOneFormula : L.BoundedFormula Empty 1 :=
  (exF fun o => andF (omegaOneF (varT o)) (sameCardinalityF (varT 0) (varT o))) 1
end Scotts.FOL.SetCardinality


