-- Prove2me | Definitions.Def_definable_saturated_arithmetic
-- name    : definable_saturated_arithmetic
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T22:48:53.64865+00:00
-- url     : https://prove2.me/theorems/5a8d2d3a-66e7-456c-918b-009bff4622bc
-- title:
--   Arithmetic coding, saturation, isomorphism, and the Scott sentence
-- statement:
--   This bundle provides the **arithmetic-coding layer** and the final **Scott sentence** of the definable-saturated consistency theorem, building on the first-order set-theory layer.
--
--   It defines: (1) **set codes** for finite sequences and assignments; (2) **term evaluation** and (3) **arithmetic satisfaction** for genuine arithmetic formula codes; (4) **syntax recognition** distinguishing genuine term/formula codes from junk; (5) **elementary maps** between coded arithmetic structures; (6) **row predicates** for $\omega$-indexed families of formulas with parameters; (7) **countable saturation** — every finitely satisfiable such row is realized; (8) the **canonical natural-number code** recognizing $(\omega,0,1,+,\times)$; (9) **saturated elementary extensions** of the naturals; (10) **isomorphism** of coded presentations; and (11) the sentences `scottSentence` ($\sigma$) and `scottCHSentence` ($\sigma_{\mathrm{CH}}$).
--
--   The sentence $\sigma$ asserts existence, uniqueness up to isomorphism, and absence of an ordinal-definable packed code for the countably saturated elementary extensions of $\mathbb N$ of cardinality $\aleph_1$; $\sigma_{\mathrm{CH}}$ conjoins CH. These are the sentences whose consistency with ZFC is the mission's target.
--
--   **Formalization Note.** A presentation is packed as the nested ordered pair $\langle D,\langle 0,\langle 1,\langle +,\times\rangle\rangle\rangle\rangle$; saturation quantifies over set-coded $\omega$-sequences of genuine arithmetic formula/parameter rows.
-- source:
--   https://github.com/elliotglazer/definable-saturated/blob/6d4822c80dd6/DefinableSaturated/Challenge.lean#L411-L739

/- Transplanted from elliotglazer/definable-saturated, DefinableSaturated/Challenge.lean (Apache 2.0, (c) 2026 Elliot Glazer). -/
import Mathlib.ModelTheory.Satisfiability
import Definitions.Def_definable_saturated_fol

open FirstOrder FirstOrder.Language
open scoped FirstOrder
namespace Scotts.Arithmetic.SetCodes
open Erdos501.FOL
/-- The literal first-order predicate recognizing a total binary operation
graph; its shape clause excludes unrelated elements of the graph. -/
def binaryOperationF (D f : Tm) : Fm := andF
  (allIn D fun x => allIn D fun y => exIn D fun z => andF
    (memF (pairT (pairT (varT x) (varT y)) (varT z)) f)
    (allF fun z' => impF
      (memF (pairT (pairT (varT x) (varT y)) (varT z')) f)
      (eqF (varT z') (varT z))))
  (allIn f fun t => exIn D fun x => exIn D fun y => exIn D fun z =>
    eqF (varT t) (pairT (pairT (varT x) (varT y)) (varT z)))
/-- Variables `(D,0,1,+,×)`, in that order. This is an actual formula of the
existing set-theoretic language, not a new relation symbol. -/
def validFormula : L.BoundedFormula Empty 5 :=
  andsF [memF (varT 1) (varT 0), memF (varT 2) (varT 0),
    binaryOperationF (varT 0) (varT 3), binaryOperationF (varT 0) (varT 4)] 5
end Scotts.Arithmetic.SetCodes
namespace Scotts.Arithmetic.TermEvaluation
open Erdos501.FOL
open Scotts.FOL.Satisfaction (tagT assignmentF)
/-- The set code for an arithmetic variable term with index `i`. -/
def varT' (i : Tm) : Tm := pairT (tagT 0) i
/-- The set code for the arithmetic constant term `0`. -/
def zeroT : Tm := pairT (tagT 1) empT
/-- The set code for the arithmetic constant term `1`. -/
def oneT : Tm := pairT (tagT 2) empT
/-- The set code for the arithmetic term `t + s`. -/
def addT (t s : Tm) : Tm := pairT (tagT 3) (pairT t s)
/-- The set code for the arithmetic term `t × s`. -/
def mulT (t s : Tm) : Tm := pairT (tagT 4) (pairT t s)
/-- `E` records that term code `t` has value `z` at arity `n` under assignment graph `v`. -/
def valueF (E t n v z : Tm) : Fm := memF (pairT t (pairT n (pairT v z))) E
/-- `T` is downward closed under the immediate subterms of addition and multiplication codes. -/
def closedF (T : Tm) : Fm := andF
  (allF fun t => allF fun s => impF (memF (addT (varT t) (varT s)) T)
    (andF (memF (varT t) T) (memF (varT s) T)))
  (allF fun t => allF fun s => impF (memF (mulT (varT t) (varT s)) T)
    (andF (memF (varT t) T) (memF (varT s) T)))
/-- The subterms `t,s` evaluate to `x,y ∈ D`, and the operation graph `f` sends `(x,y)` to `z`. -/
def binaryClauseF (E t s n v f z D : Tm) : Fm := exIn D fun x => exIn D fun y => andsF [
  valueF E t n v (varT x), valueF E s n v (varT y),
  memF (pairT (pairT (varT x) (varT y)) z) f]
/-- `E` obeys the recursive evaluation clauses on term-code set `T` for the coded arithmetic structure. -/
def recursionF (D z₀ z₁ plus times T E : Tm) : Fm := andF (closedF T)
  (allIn omT fun n => allF fun v => impF (assignmentF (varT n) D (varT v))
    (allIn D fun z => andsF [
      allIn omT fun i => impF (memF (varT' (varT i)) T)
        (iffF (valueF E (varT' (varT i)) (varT n) (varT v) (varT z))
          (orF (appF (varT v) (varT i) (varT z))
            (andF (notF (memF (varT i) (varT n))) (eqF (varT z) z₀)))),
      impF (memF zeroT T) (iffF (valueF E zeroT (varT n) (varT v) (varT z)) (eqF (varT z) z₀)),
      impF (memF oneT T) (iffF (valueF E oneT (varT n) (varT v) (varT z)) (eqF (varT z) z₁)),
      allF fun t => allF fun s => impF (memF (addT (varT t) (varT s)) T)
        (iffF (valueF E (addT (varT t) (varT s)) (varT n) (varT v) (varT z))
          (binaryClauseF E (varT t) (varT s) (varT n) (varT v) plus (varT z) D)),
      allF fun t => allF fun s => impF (memF (mulT (varT t) (varT s)) T)
        (iffF (valueF E (mulT (varT t) (varT s)) (varT n) (varT v) (varT z))
          (binaryClauseF E (varT t) (varT s) (varT n) (varT v) times (varT z) D))]))
/-- Seven-place predicate expressing the certified recursive evaluation relation `E` on `T`. -/
def recursionFormula : L.BoundedFormula Empty 7 :=
  recursionF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) (varT 6) 7
/-- Uniform term evaluation, specified only by set-theoretic formulas. -/
def evaluationF (D z₀ z₁ plus times t n v z : Tm) : Fm :=
  exF fun T => exF fun E => andsF [
    recursionF D z₀ z₁ plus times (varT T) (varT E),
    memF t (varT T), valueF (varT E) t n v z]
/-- Nine-place predicate saying that an arithmetic term code evaluates to the stated value under the stated finite assignment. -/
def evaluationFormula : L.BoundedFormula Empty 9 :=
  evaluationF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4)
    (varT 5) (varT 6) (varT 7) (varT 8) 9
/-- Closure under all literal term-code constructors. -/
def constructorClosedF (T : Tm) : Fm := andsF [
  allIn omT fun i => memF (varT' (varT i)) T, memF zeroT T, memF oneT T,
  allIn T fun t => allIn T fun s => memF (addT (varT t) (varT s)) T,
  allIn T fun t => allIn T fun s => memF (mulT (varT t) (varT s)) T]
/-- Unary predicate saying that a set contains all variable, constant, addition, and multiplication term codes. -/
def constructorClosedFormula : L.BoundedFormula Empty 1 := constructorClosedF (varT 0) 1
end Scotts.Arithmetic.TermEvaluation
namespace Scotts.Arithmetic.Satisfaction
open Erdos501.FOL
open Scotts.FOL.Satisfaction (tagT assignmentF appendF)
open Scotts.Arithmetic
/-- The set code for the falsity node of an arithmetic formula tree. -/
def botT : Tm := pairT (tagT 5) empT
/-- The set code for an arithmetic equality node with term-code children `t` and `s`. -/
def equalT (t s : Tm) : Tm := pairT (tagT 6) (pairT t s)
/-- The set code for an arithmetic implication node with formula-code children `φ` and `ψ`. -/
def impT (φ ψ : Tm) : Tm := pairT (tagT 7) (pairT φ ψ)
/-- The set code for an arithmetic universal-quantifier node with body code `φ`. -/
def allT (φ : Tm) : Tm := pairT (tagT 8) φ
/-- The common membership predicate recording that a coded formula holds under a finite assignment. -/
def holdsF := Scotts.FOL.Satisfaction.holdsF
/-- Formula set `F` contains the immediate term or formula children of each composite formula code it contains. -/
def closedF (T F : Tm) : Fm := andsF [
  allF fun t => allF fun s => impF (memF (equalT (varT t) (varT s)) F)
    (andF (memF (varT t) T) (memF (varT s) T)),
  allF fun φ => allF fun ψ => impF (memF (impT (varT φ) (varT ψ)) F)
    (andF (memF (varT φ) F) (memF (varT ψ) F)),
  allF fun φ => impF (memF (allT (varT φ)) F) (memF (varT φ) F)]
/-- The equality formula with term codes `t,s` holds exactly when both terms evaluate to one common element of `D`. -/
def equalClauseF (D E t s n v : Tm) : Fm := exIn D fun x => andF
  (TermEvaluation.valueF E t n v (varT x)) (TermEvaluation.valueF E s n v (varT x))
/-- Substitution of the already verified term-recursion predicate. -/
def termRecursionF (D z₀ z₁ plus times T E : Tm) : Fm :=
  Scotts.FOL.Composition.predicateF TermEvaluation.recursionFormula ![D, z₀, z₁, plus, times, T, E]
/-- `E` evaluates terms and `S` obeys the recursive truth clauses on term codes `T` and formula codes `F`. -/
def recursionF (D z₀ z₁ plus times T F E S : Tm) : Fm := andF
  (termRecursionF D z₀ z₁ plus times T E) (andF (closedF T F)
  (allIn omT fun n => allF fun v => impF (assignmentF (varT n) D (varT v)) (andsF [
    impF (memF botT F) (notF (holdsF S (varT n) botT (varT v))),
    allF fun t => allF fun s => impF (memF (equalT (varT t) (varT s)) F)
      (iffF (holdsF S (varT n) (equalT (varT t) (varT s)) (varT v))
        (equalClauseF D E (varT t) (varT s) (varT n) (varT v))),
    allF fun φ => allF fun ψ => impF (memF (impT (varT φ) (varT ψ)) F)
      (iffF (holdsF S (varT n) (impT (varT φ) (varT ψ)) (varT v))
        (impF (holdsF S (varT n) (varT φ) (varT v))
          (holdsF S (varT n) (varT ψ) (varT v)))),
    allF fun φ => impF (memF (allT (varT φ)) F)
      (iffF (holdsF S (varT n) (allT (varT φ)) (varT v))
        (allIn D fun x => exF fun m => exF fun w => andsF [succF (varT n) (varT m),
          appendF (varT n) (varT v) (varT x) (varT w), holdsF S (varT m) (varT φ) (varT w)]))])))
/-- Nine-place predicate expressing a complete term-evaluation and arithmetic-satisfaction recursion certificate. -/
def recursionFormula : L.BoundedFormula Empty 9 :=
  recursionF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4)
    (varT 5) (varT 6) (varT 7) (varT 8) 9
/-- A uniform arithmetic satisfaction formula with the five structure-code
parameters, formula code, assignment length, and assignment graph. -/
def satisfactionF (D z₀ z₁ plus times φ n v : Tm) : Fm :=
  exF fun T => exF fun F => exF fun E => exF fun S => andsF [
    Scotts.FOL.Composition.predicateF recursionFormula
      ![D, z₀, z₁, plus, times, varT T, varT F, varT E, varT S],
    memF φ (varT F), holdsF (varT S) n φ v]
/-- Eight-place predicate saying that a coded arithmetic formula is true under the stated finite assignment. -/
def satisfactionFormula : L.BoundedFormula Empty 8 :=
  satisfactionF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) (varT 6) (varT 7) 8
end Scotts.Arithmetic.Satisfaction
namespace Scotts.Arithmetic.SyntaxRecognition
open Erdos501.FOL
open Scotts.Arithmetic
open Scotts.Arithmetic.Satisfaction
open Scotts.FOL.Satisfaction (tagT)
/-- `F` contains falsity and is closed under equality over `T`, implication, and universal quantification. -/
def constructorClosedF (T F : Tm) : Fm := andsF [
  memF botT F,
  allIn T fun t => allIn T fun s => memF (equalT (varT t) (varT s)) F,
  allIn F fun φ => allIn F fun ψ => memF (impT (varT φ) (varT ψ)) F,
  allIn F fun φ => memF (allT (varT φ)) F]
/-- `T` contains every code obtained from the arithmetic term constructors. -/
def termConstructorClosedF (T : Tm) : Fm :=
  Scotts.FOL.Composition.predicateF TermEvaluation.constructorClosedFormula ![T]
/-- `φ` belongs to every formula set closed over every constructor-closed term set, so `φ` is a genuine finite formula code. -/
def formulaCodeF (φ : Tm) : Fm := allF fun T => allF fun F => impF
  (andF (termConstructorClosedF (varT T)) (constructorClosedF (varT T) (varT F)))
  (memF φ (varT F))
/-- Unary first-order predicate recognizing exactly the genuine finite arithmetic formula codes. -/
def formulaCodeFormula : L.BoundedFormula Empty 1 := formulaCodeF (varT 0) 1
end Scotts.Arithmetic.SyntaxRecognition
namespace Scotts.Arithmetic.ElementaryMaps
open Erdos501.FOL
open Scotts.Arithmetic Scotts.Arithmetic.SetCodes
/-- For indices below `n`, assignment graphs `v,w` give values related pointwise by the graph `g`. -/
def assignmentMapF (n v w g : Tm) : Fm := allIn n fun i => allF fun x => allF fun y =>
  impF (appF v (varT i) (varT x))
    (impF (appF w (varT i) (varT y)) (appF g (varT x) (varT y)))
/-- Depth-polymorphic assertion that `φ` is a genuine arithmetic formula code. -/
def syntaxF (φ : Tm) : Fm :=
  Scotts.FOL.Composition.predicateF SyntaxRecognition.formulaCodeFormula ![φ]
/-- Depth-polymorphic assertion that `φ` is true in the coded structure under assignment `v` of length `n`. -/
def satF (D z₀ z₁ plus times φ n v : Tm) : Fm :=
  Scotts.FOL.Composition.predicateF Satisfaction.satisfactionFormula ![D, z₀, z₁, plus, times, φ, n, v]
/-- `g` is a total map between the two coded structures and preserves every arithmetic formula on finite assignments. -/
def elementaryMapF (D z₀ z₁ plus times D' z₀' z₁' plus' times' g : Tm) : Fm :=
  andF (Scotts.FOL.Satisfaction.assignmentF D D' g)
    (allIn omT fun n => allF fun v => impF
      (Scotts.FOL.Satisfaction.assignmentF (varT n) D (varT v))
      (allF fun w => impF (Scotts.FOL.Satisfaction.assignmentF (varT n) D' (varT w))
        (impF (assignmentMapF (varT n) (varT v) (varT w) g)
          (allF fun φ => impF (syntaxF (varT φ))
            (iffF (satF D z₀ z₁ plus times (varT φ) (varT n) (varT v))
              (satF D' z₀' z₁' plus' times' (varT φ) (varT n) (varT w)))))))
/-- Eleven parameters: five for each arithmetic structure and the proposed
elementary map graph. Validity of the two structure codes is separate. -/
def elementaryMapFormula : L.BoundedFormula Empty 11 :=
  elementaryMapF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4)
    (varT 5) (varT 6) (varT 7) (varT 8) (varT 9) (varT 10) 11
end Scotts.Arithmetic.ElementaryMaps
namespace Scotts.Arithmetic.RowPredicates
open Erdos501.FOL
open Scotts.Arithmetic Scotts.Arithmetic.ElementaryMaps
/-- `r` codes a genuine arithmetic formula together with a finite tuple of parameters from `D`. -/
def validRowF (D r : Tm) : Fm := exF fun φ => exF fun k => exF fun v =>
  andF (eqF r (pairT (varT φ) (pairT (varT k) (varT v))))
    (andF (syntaxF (varT φ)) (andF (memF (varT k) omT)
      (Scotts.FOL.Satisfaction.assignmentF (varT k) D (varT v))))
/-- The element `x` realizes row `r`: appending `x` to the row's parameter tuple makes its formula true. -/
def rowTruthF (D z₀ z₁ plus times r x : Tm) : Fm :=
  exF fun φ => exF fun k => exF fun v =>
    andF (eqF r (pairT (varT φ) (pairT (varT k) (varT v))))
      (exF fun n => exF fun w => andF (succF (varT k) (varT n))
        (andF (Scotts.FOL.Satisfaction.appendF (varT k) (varT v) x (varT w))
          (satF D z₀ z₁ plus times (varT φ) (varT n) (varT w))))
/-- Binary first-order predicate saying that `r` is a valid formula-and-parameter row over `D`. -/
def validRowFormula : L.BoundedFormula Empty 2 := validRowF (varT 0) (varT 1) 2
/-- Seven-place first-order predicate saying that `x` realizes row `r` in the coded arithmetic structure. -/
def rowTruthFormula : L.BoundedFormula Empty 7 :=
  rowTruthF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) (varT 6) 7
/-- Compositional insertion of the verified row-validity formula. -/
def validRowPredF (D r : Tm) : Fm :=
  Scotts.FOL.Composition.predicateF validRowFormula ![D, r]
/-- Compositional insertion of the verified row-realization formula. -/
def rowTruthPredF (D z₀ z₁ plus times r x : Tm) : Fm :=
  Scotts.FOL.Composition.predicateF rowTruthFormula ![D, z₀, z₁, plus, times, r, x]
end Scotts.Arithmetic.RowPredicates
namespace Scotts.Arithmetic.Saturation
open Erdos501.FOL
open Scotts.Arithmetic Scotts.Arithmetic.RowPredicates
/-- `R` is the graph of an `ω`-sequence whose values are valid rows over `D`. -/
def rowSequenceF (D R : Tm) : Fm := exF fun P =>
  andF (allIn (varT P) fun r => validRowPredF D (varT r))
    (Scotts.FOL.Satisfaction.assignmentF omT (varT P) R)
/-- `x` realizes every row selected by `R` at an index belonging to `I`. -/
def rowsHoldF (D z₀ z₁ plus times R I x : Tm) : Fm :=
  allIn I fun i => allF fun r => impF (appF R (varT i) (varT r))
    (rowTruthPredF D z₀ z₁ plus times (varT r) x)
/-- Every coded `ω`-sequence of rows whose finite prefixes are realizable in `D` is jointly realized in `D`. -/
def saturatedF (D z₀ z₁ plus times : Tm) : Fm := allF fun R =>
  impF (rowSequenceF D (varT R))
    (impF (allIn omT fun k => exIn D fun x =>
      rowsHoldF D z₀ z₁ plus times (varT R) (varT k) (varT x))
      (exIn D fun x => rowsHoldF D z₀ z₁ plus times (varT R) omT (varT x)))
/-- The five parameters are the carrier, zero, one, addition graph and
multiplication graph. Code validity is handled separately. -/
def saturatedFormula : L.BoundedFormula Empty 5 :=
  saturatedF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) 5
end Scotts.Arithmetic.Saturation
namespace Scotts.Arithmetic.NaturalCode
open Erdos501.FOL
open Scotts.Arithmetic Scotts.Arithmetic.SetCodes
/-- Binary predicate saying that the second set is the von Neumann successor of the first. -/
def successorFormula : L.BoundedFormula Empty 2 := succF (varT 0) (varT 1) 2
/-- Depth-polymorphic assertion that `t = s ∪ {s}`. -/
def successorF (s t : Tm) : Fm :=
  Scotts.FOL.Composition.predicateF successorFormula ![s, t]
/-- The operation graphs `add,mul` satisfy the usual recursion equations for addition and multiplication on `ω`. -/
def recursiveArithmeticF (add mul : Tm) : Fm := andsF [
  allIn omT fun x => app2F add (varT x) empT (varT x),
  allIn omT fun x => allIn omT fun y => allIn omT fun z =>
    impF (app2F add (varT x) (varT y) (varT z))
      (exF fun y' => exF fun z' => andsF [successorF (varT y) (varT y'),
        successorF (varT z) (varT z'), app2F add (varT x) (varT y') (varT z')]),
  allIn omT fun x => app2F mul (varT x) empT empT,
  allIn omT fun x => allIn omT fun y => allIn omT fun z => allIn omT fun w =>
    impF (app2F mul (varT x) (varT y) (varT z))
      (impF (app2F add (varT z) (varT x) (varT w))
        (exF fun y' => andF (successorF (varT y) (varT y'))
          (app2F mul (varT x) (varT y') (varT w))))]
/-- The five fields are exactly `ω`, zero, one, and total operation graphs satisfying the standard arithmetic recursions. -/
def naturalCodeF (D zero one add mul : Tm) : Fm := andsF [
  eqF D omT, eqF zero empT, successorF empT one,
  binaryOperationF omT add, binaryOperationF omT mul, recursiveArithmeticF add mul]
/-- Five parameters `(D,0,1,+,×)` recognize exactly the natural structure. -/
def naturalCodeFormula : L.BoundedFormula Empty 5 :=
  naturalCodeF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) 5
end Scotts.Arithmetic.NaturalCode
namespace Scotts.Arithmetic.SaturatedExtensions
open Erdos501.FOL
open Scotts.Arithmetic Scotts.Arithmetic.SetCodes Scotts.Arithmetic.ElementaryMaps Scotts.Arithmetic.Saturation
open Scotts.FOL.Composition
/-- There is a valid canonical presentation of natural-number arithmetic and an elementary embedding of it into the given structure. -/
def naturalEmbeddingF (D z₀ z₁ plus times : Tm) : Fm :=
  exF fun a₀ => exF fun a₁ => exF fun aplus => exF fun atimes =>
    andF (predicateF NaturalCode.naturalCodeFormula
      ![omT, varT a₀, varT a₁, varT aplus, varT atimes])
      (exF fun g => predicateF elementaryMapFormula
        ![omT, varT a₀, varT a₁, varT aplus, varT atimes,
          D, z₀, z₁, plus, times, varT g])
/-- Existence of an elementary embedding of the canonical natural structure. -/
def naturalEmbeddingFormula : L.BoundedFormula Empty 5 :=
  naturalEmbeddingF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) 5
/-- Valid arithmetic operations, an elementary copy of the naturals, and
countable saturation. The cardinality condition is supplied separately. -/
def saturatedExtensionFormula : L.BoundedFormula Empty 5 :=
  validFormula ⊓ (naturalEmbeddingFormula ⊓ saturatedFormula)
end Scotts.Arithmetic.SaturatedExtensions
namespace Scotts.Arithmetic.Isomorphisms
open Erdos501.FOL
open Scotts.Arithmetic Scotts.Arithmetic.ElementaryMaps Scotts.Arithmetic.SaturatedExtensions
open Scotts.FOL.SetCardinality Scotts.FOL.Composition
/-- Eleven-place predicate saying that the last argument is the graph of an isomorphism between the two coded structures. -/
def isomorphismFormula : L.BoundedFormula Empty 11 :=
  elementaryMapFormula ⊓ ontoF (varT 0) (varT 5) (varT 10) 11
/-- Ten-place predicate saying that the two coded arithmetic structures are isomorphic. -/
def isomorphicFormula : L.BoundedFormula Empty 10 :=
  (exF fun g => predicateF isomorphismFormula
    ![varT 0, varT 1, varT 2, varT 3, varT 4,
      varT 5, varT 6, varT 7, varT 8, varT 9, varT g]) 10
/-- The coded structure is a countably saturated elementary extension of the naturals whose domain has cardinality `ℵ₁`. -/
def saturatedAlephOneFormula : L.BoundedFormula Empty 5 :=
  saturatedExtensionFormula ⊓ predicateF sizeAlephOneFormula ![varT 0] 5
end Scotts.Arithmetic.Isomorphisms
namespace Scotts.FOL.ScottStatement
open Erdos501.FOL
open Scotts.Arithmetic.Isomorphisms
open Scotts.FOL.Composition Scotts.FOL.OrdinalDefinitions
/-- The nested ordered-pair code packing the five fields `(D,0,1,+,×)` of a presentation. -/
def presentationT : Tm :=
  pairT (varT 0) (pairT (varT 1) (pairT (varT 2) (pairT (varT 3) (varT 4))))
/-- Sentence asserting that a countably saturated elementary extension of the naturals of cardinality `ℵ₁` exists. -/
def existsSentence : L.Sentence := saturatedAlephOneFormula.exs
/-- If both five-field tuples are saturated `ℵ₁`-sized elementary extensions of the naturals, then they are isomorphic. -/
def uniquenessFormula : L.BoundedFormula Empty 10 :=
  ((andF (predicateF saturatedAlephOneFormula ![varT 0, varT 1, varT 2, varT 3, varT 4])
    (predicateF saturatedAlephOneFormula ![varT 5, varT 6, varT 7, varT 8, varT 9])) 10).imp
      isomorphicFormula
/-- Universal closure asserting uniqueness up to isomorphism of the saturated `ℵ₁`-sized presentations. -/
def uniquenessSentence : L.Sentence := uniquenessFormula.alls
/-- Any saturated `ℵ₁`-sized presentation has a packed five-field code that is not ordinal definable. -/
def noODFormula : L.BoundedFormula Empty 5 :=
  saturatedAlephOneFormula.imp ((predicateF definitionFormula ![presentationT] 5).not)
/-- Universal closure asserting that no qualifying presentation has an ordinal-definable packed code. -/
def noODSentence : L.Sentence := noODFormula.alls
/-- Existence, uniqueness up to isomorphism, and no OD presentation. -/
def scottSentence : L.Sentence := existsSentence ⊓ (uniquenessSentence ⊓ noODSentence)
/-- The optional explicit CH strengthening used by the intended construction. -/
def chSentence : L.Sentence := predicateF SetCardinality.sizeAlephOneFormula ![powT omT] 0
/-- The conjunction of CH with existence, uniqueness up to isomorphism, and absence of an ordinal-definable presentation. -/
def scottCHSentence : L.Sentence := chSentence ⊓ scottSentence
end Scotts.FOL.ScottStatement


