-- Prove2me | Definitions.Def_MetricMSO_Formula
-- name    : MetricMSO_Formula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:23.240367+00:00
-- url     : https://prove2.me/theorems/4bf129fb-dddc-421c-8fae-16a393390c0c
-- title:
--   Formulas of $\mathrm{CMSO}_2[\mathsf{SP},\mathsf{EqGC}]$ and their length $|\varphi|$
-- statement:
--   The syntax of **counting monadic second-order logic with shortest-path and geodesic-cycle atoms**. There are four sorts of variables: vertices, edges, vertex sets and edge sets. The atoms are falsity, adjacency $E(x,y)$, equality of vertices and of edges, incidence $\mathrm{Inc}(e,x)$, membership $x\in X$ and $e\in Y$, the unary input predicates on vertices and on edges, the modulo-counting atoms $\mathrm{card}_{a,\ell}(X)$ on vertex sets and on edge sets, and the two metric atoms $\mathsf{SP}(P,s,t)$ and $\mathsf{EqGC}(C,x,y,u,v)$. Formulas are closed under negation, conjunction and existential quantification over all four sorts.
--
--   The **length** $|\varphi|$ of a formula is the length of its binary code: a five-bit tag per constructor, followed by the self-delimiting binary codes of its numeric arguments, so that the constants $a,\ell$ "contribute to its length" as on p.16.
--
--   **Formalization Note** Variables are de Bruijn levels, one numbering for each sort: a variable is the number of variables of its sort introduced before it. Disjunction, implication and universal quantification are abbreviations. The code uses the published `encodeNat`.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.7, p.16 (PDF 18); §2.8, Definitions 2.10, 2.11, 2.15, pp.18–19 (PDF 20–21)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine

namespace MetricMSO

open ExponomialAssortment.FPTAS (encodeNat)

/-- **Formulas of CMSO2[SP, EqGC]** over graphs with unary input predicates.

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.7, p.16 (PDF 18):
FO uses "equality, adjacency E(x, y), and the unary input predicates"; MSO1 adds vertex-set
quantification and "membership atoms x ∈ X"; MSO2 is MSO on the incidence structure I(G), "the logic
in which we may quantify over vertices, edges, vertex sets, and edge sets", with the incidence
relation Inc(e, v); CMSO adds "atoms card_{a,ℓ}(X) expressing that |X| ≡ a (mod ℓ), where ℓ ≥ 2 and
0 ≤ a < ℓ", applied "to both vertex sets and edge sets" in CMSO2. §2.8, p.18 (PDF 20), Definitions
2.10, 2.11 and 2.15: the atoms SP(P, s, t) and EqGC(C, x, y, u, v).

There are four sorts of variables: vertices, edges, vertex sets and edge sets. Each sort has its own
**de Bruijn levels**: a variable is the natural number counting how many variables of its sort were
introduced before it (free variables first, then quantified ones from the outside in). Constructors:
* `ff` (falsity);
* `adj x y` (E(x, y)), `eqV x y`, `eqE e f`, `inc e x` (Inc(e, x));
* `memV x X`, `memE e Y` (membership);
* `vpred j x`, `epred j e` (the `j`-th vertex or edge input predicate);
* `cardV a l X`, `cardE a l Y` (card_{a,ℓ});
* `sp P s t` (SP(P, s, t)) and `eqgc C x y u v` (EqGC(C, x, y, u, v)), with `P`, `C` vertex-set
  variables and the others vertex variables;
* `neg`, `and`, and the four existential quantifiers `exV`, `exE`, `exVS`, `exES`.

**Formalization Note** Disjunction, implication and universal quantification are the usual
abbreviations (`or`, `imp`, `allV`, `allVS` below). -/
inductive Formula : Type
  | ff : Formula
  | adj (x y : ℕ) : Formula
  | eqV (x y : ℕ) : Formula
  | eqE (e f : ℕ) : Formula
  | inc (e x : ℕ) : Formula
  | memV (x X : ℕ) : Formula
  | memE (e Y : ℕ) : Formula
  | vpred (j x : ℕ) : Formula
  | epred (j e : ℕ) : Formula
  | cardV (a l X : ℕ) : Formula
  | cardE (a l Y : ℕ) : Formula
  | sp (P s t : ℕ) : Formula
  | eqgc (C x y u v : ℕ) : Formula
  | neg (φ : Formula) : Formula
  | and (φ ψ : Formula) : Formula
  | exV (φ : Formula) : Formula
  | exE (φ : Formula) : Formula
  | exVS (φ : Formula) : Formula
  | exES (φ : Formula) : Formula
  deriving DecidableEq

namespace Formula

/-- Disjunction `φ ∨ ψ := ¬(¬φ ∧ ¬ψ)`. -/
def or (φ ψ : Formula) : Formula := neg (and (neg φ) (neg ψ))

/-- Implication `φ → ψ := ¬(φ ∧ ¬ψ)`. -/
def imp (φ ψ : Formula) : Formula := neg (and φ (neg ψ))

/-- Truth `¬⊥`. -/
def tt : Formula := neg ff

/-- Universal vertex quantifier `∀x φ := ¬∃x ¬φ`. -/
def allV (φ : Formula) : Formula := neg (exV (neg φ))

/-- Universal vertex-set quantifier `∀X φ := ¬∃X ¬φ`. -/
def allVS (φ : Formula) : Formula := neg (exVS (neg φ))

/-- Five-bit tag of a constructor (least significant bit first). -/
def tag (k : ℕ) : List Bool := (List.range 5).map fun i => k.testBit i

/-- **Binary encoding of a formula.** Each constructor is written as a five-bit tag followed by the
self-delimiting binary codes (`encodeNat`) of its natural-number arguments (variable levels,
predicate indices and the constants `a`, `ℓ`) and then the codes of its subformulas, in prefix
order. The code is prefix-free, hence injective. -/
def encode : Formula → List Bool
  | ff => tag 0
  | adj x y => tag 1 ++ encodeNat x ++ encodeNat y
  | eqV x y => tag 2 ++ encodeNat x ++ encodeNat y
  | eqE e f => tag 3 ++ encodeNat e ++ encodeNat f
  | inc e x => tag 4 ++ encodeNat e ++ encodeNat x
  | memV x X => tag 5 ++ encodeNat x ++ encodeNat X
  | memE e Y => tag 6 ++ encodeNat e ++ encodeNat Y
  | vpred j x => tag 7 ++ encodeNat j ++ encodeNat x
  | epred j e => tag 8 ++ encodeNat j ++ encodeNat e
  | cardV a l X => tag 9 ++ encodeNat a ++ encodeNat l ++ encodeNat X
  | cardE a l Y => tag 10 ++ encodeNat a ++ encodeNat l ++ encodeNat Y
  | sp P s t => tag 11 ++ encodeNat P ++ encodeNat s ++ encodeNat t
  | eqgc C x y u v =>
      tag 12 ++ encodeNat C ++ encodeNat x ++ encodeNat y ++ encodeNat u ++ encodeNat v
  | neg φ => tag 13 ++ encode φ
  | and φ ψ => tag 14 ++ encode φ ++ encode ψ
  | exV φ => tag 15 ++ encode φ
  | exE φ => tag 16 ++ encode φ
  | exVS φ => tag 17 ++ encode φ
  | exES φ => tag 18 ++ encode φ

/-- **The length `|φ|` of a formula**: the length of its binary encoding. In particular the
encodings of the constants `a`, `ℓ` of the modulo-counting atoms "contribute to its length"
(§2.7, p.16). -/
def length (φ : Formula) : ℕ := (encode φ).length

end Formula

end MetricMSO


