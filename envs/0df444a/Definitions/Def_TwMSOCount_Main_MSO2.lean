-- Prove2me | Definitions.Def_TwMSOCount_Main_MSO2
-- name    : TwMSOCount_Main_MSO2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:38:09.20177+00:00
-- url     : https://prove2.me/theorems/ab24d7a5-80ec-4830-8aaf-9bf373c5fc90
-- title:
--   Graph MSO2 over the incidence vocabulary: sorted syntax with vertex constants, satisfaction, sentences, quantifier rank, size and code
-- statement:
--   Formulas of **graph MSO2** speak about a colored graph $(G,\chi)$ through its **incidence structure** $I(G,\chi) = (V \,\dot\cup\, E;\ \mathrm{Vertex}, \mathrm{Edge}, \mathrm{Inc}, (P_c)_{c\in C})$: the domain has a vertex sort $V$ and an edge sort $E$, $\mathrm{Inc}(e,v)$ says that $v$ is an endpoint of $e$, and $P_c$ holds of the vertices of color $c$. Colors are $C = \{0,\dots,r-1\}$.
--
--   The syntax is **sorted**. There are four kinds of variables, each named by a natural number: vertex variables, edge variables, vertex-set variables and edge-set variables. A **vertex term** is a vertex variable or a **constant symbol** $c_b$ taken from a parameter set $K$ (for boundaried graphs, $K = \Lambda_k$ and $c_b$ names the boundary vertex $\iota(b)$). Atomic formulas are
--   $$x = y,\quad e = f,\quad x \in X,\quad e \in Y,\quad \mathrm{Inc}(e, x),\quad P_c(x),\quad \top,\quad \bot,$$
--   for vertex terms $x,y$, edge variables $e,f$, a vertex-set variable $X$ and an edge-set variable $Y$. Formulas are closed under $\neg, \wedge, \vee, \to$ and under $\exists$ and $\forall$ over each of the four kinds of variables. There is no order relation and no modular counting predicate; the predicates $\mathrm{Vertex}$ and $\mathrm{Edge}$ are expressed by the sorts.
--
--   **Satisfaction** is the standard two-sorted one: individual variables range over $V$ or over the edge set $E(G)$, set variables over subsets of $V$ or of $E(G)$, and constants are interpreted by a partial map $\kappa$ (an atom containing an uninterpreted constant is false). Either sort may be empty: an individual variable may be unassigned, and a quantifier over an empty sort has no witness. A **sentence** has no free variable of any kind (it may contain constants); $I \models \varphi$ means satisfaction under the empty assignment. Each satisfying graph satisfies a sentence once, however many witnesses it has.
--
--   The **quantifier rank** $\mathrm{qr}$ is $0$ on atoms, unchanged by negation, the maximum for binary connectives, and $1+$ for each quantifier (Definition C.1). The **size** of a formula counts its symbols plus the names of its variables and the indices of its color predicates, so that only finitely many constant-free formulas have a given size. The **code** of a formula is its prefix (Polish) encoding as a list of natural numbers.
--
--   **Formalization Note.** `Formula r K`, `Formula.Sat G χ κ a φ`, `Formula.Models`, `Formula.IsSentence` (`fv = ∅`), `Formula.consts`, `Formula.qr`, `Formula.size`, `Formula.encode`. Edges are elements of `Sym2 V` in `G.edgeSet`.
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), §2, pp. 3–4 (PDF 4–5); Appendix C.1 and Definition C.1, pp. 23–24 (PDF 24–25)

import Mathlib

namespace TwMSOCount.Main

/-- Vertex terms of graph MSO2: a vertex variable (named by a natural number) or a vertex
constant symbol from `K` (Appendix C.1: "Vertex terms are vertex variables or these constants;
edge terms are edge variables"). -/
inductive VTerm (K : Type) where
  | var : ℕ → VTerm K
  | const : K → VTerm K

/-- Formulas of graph MSO2 over the incidence vocabulary `V_C = {Vertex, Edge, Inc} ∪ {P_c}` with
`r` colors `P_0, …, P_{r-1}` and vertex constant symbols from `K` (Section 2 and Appendix C.1).
The syntax is sorted: individual variables of vertex sort (`exV`/`allV`) and of edge sort
(`exE`/`allE`), set variables of vertex sort (`exVS`/`allVS`) and of edge sort (`exES`/`allES`),
each named by a natural number, one name space per sort. Atoms: equality of two vertex terms or two
edge variables, membership in a set variable of the matching sort, `Inc(e, x)` and `P_c(x)`. The
predicates `Vertex`, `Edge` are implicit in the sorts. There is no order relation and no modular
counting predicate. -/
inductive Formula (r : ℕ) (K : Type) where
  | tt : Formula r K
  | ff : Formula r K
  | eqV : VTerm K → VTerm K → Formula r K
  | eqE : ℕ → ℕ → Formula r K
  | memV : VTerm K → ℕ → Formula r K
  | memE : ℕ → ℕ → Formula r K
  | inc : ℕ → VTerm K → Formula r K
  | col : Fin r → VTerm K → Formula r K
  | neg : Formula r K → Formula r K
  | conj : Formula r K → Formula r K → Formula r K
  | disj : Formula r K → Formula r K → Formula r K
  | impl : Formula r K → Formula r K → Formula r K
  | exV : ℕ → Formula r K → Formula r K
  | allV : ℕ → Formula r K → Formula r K
  | exE : ℕ → Formula r K → Formula r K
  | allE : ℕ → Formula r K → Formula r K
  | exVS : ℕ → Formula r K → Formula r K
  | allVS : ℕ → Formula r K → Formula r K
  | exES : ℕ → Formula r K → Formula r K
  | allES : ℕ → Formula r K → Formula r K

/-- An assignment of the four sorts of variables in a graph on `V`. Individual variables may be
unassigned (`none`), so that an empty sort is allowed; set variables of edge sort range over sets of
unordered pairs, and the quantifiers below only ever bind them to sets of edges. -/
structure Assign (V : Type) where
  v : ℕ → Option V
  e : ℕ → Option (Sym2 V)
  vs : ℕ → Set V
  es : ℕ → Set (Sym2 V)

/-- The empty assignment: every individual variable unassigned, every set variable `∅`. -/
def Assign.empty (V : Type) : Assign V := ⟨fun _ => none, fun _ => none, fun _ => ∅, fun _ => ∅⟩

/-- Value of a vertex term; constants are interpreted by `κ` (`none` for an uninterpreted
constant, which makes every atom containing it false). -/
def VTerm.eval {K V : Type} (κ : K → Option V) (a : Assign V) : VTerm K → Option V
  | .var x => a.v x
  | .const c => κ c

/-- Satisfaction `I(G, χ), a ⊨ φ` in the two-sorted incidence structure of a colored graph
`(G, χ)` with constants interpreted by `κ`: the vertex sort is `V`, the edge sort is the edge set
of `G`, `Inc(e, x)` holds when `x` is an endpoint of `e`, and `P_c(x)` when `χ x = c`
(Appendix C.1: "the standard one for two-sorted monadic second-order logic"). -/
def Formula.Sat {r : ℕ} {K V : Type} (G : SimpleGraph V) (χ : V → Fin r) (κ : K → Option V) :
    Assign V → Formula r K → Prop
  | _, .tt => True
  | _, .ff => False
  | a, .eqV s t => ∃ u, s.eval κ a = some u ∧ t.eval κ a = some u
  | a, .eqE e f => ∃ d, a.e e = some d ∧ a.e f = some d
  | a, .memV s X => ∃ u, s.eval κ a = some u ∧ u ∈ a.vs X
  | a, .memE e X => ∃ d, a.e e = some d ∧ d ∈ a.es X
  | a, .inc e s => ∃ d u, a.e e = some d ∧ s.eval κ a = some u ∧ u ∈ d
  | a, .col c s => ∃ u, s.eval κ a = some u ∧ χ u = c
  | a, .neg φ => ¬ Formula.Sat G χ κ a φ
  | a, .conj φ ψ => Formula.Sat G χ κ a φ ∧ Formula.Sat G χ κ a ψ
  | a, .disj φ ψ => Formula.Sat G χ κ a φ ∨ Formula.Sat G χ κ a ψ
  | a, .impl φ ψ => Formula.Sat G χ κ a φ → Formula.Sat G χ κ a ψ
  | a, .exV x φ => ∃ u : V, Formula.Sat G χ κ { a with v := Function.update a.v x (some u) } φ
  | a, .allV x φ => ∀ u : V, Formula.Sat G χ κ { a with v := Function.update a.v x (some u) } φ
  | a, .exE x φ => ∃ d ∈ G.edgeSet,
      Formula.Sat G χ κ { a with e := Function.update a.e x (some d) } φ
  | a, .allE x φ => ∀ d ∈ G.edgeSet,
      Formula.Sat G χ κ { a with e := Function.update a.e x (some d) } φ
  | a, .exVS X φ => ∃ S : Set V, Formula.Sat G χ κ { a with vs := Function.update a.vs X S } φ
  | a, .allVS X φ => ∀ S : Set V, Formula.Sat G χ κ { a with vs := Function.update a.vs X S } φ
  | a, .exES X φ => ∃ S : Set (Sym2 V), S ⊆ G.edgeSet ∧
      Formula.Sat G χ κ { a with es := Function.update a.es X S } φ
  | a, .allES X φ => ∀ S : Set (Sym2 V), S ⊆ G.edgeSet →
      Formula.Sat G χ κ { a with es := Function.update a.es X S } φ

/-- `I(G, χ, κ) ⊨ φ` for a sentence `φ`: satisfaction under the empty assignment. -/
def Formula.Models {r : ℕ} {K V : Type} (G : SimpleGraph V) (χ : V → Fin r) (κ : K → Option V)
    (φ : Formula r K) : Prop :=
  Formula.Sat G χ κ (Assign.empty V) φ

/-- Free variables of a vertex term, as (sort, name) pairs; sort `0` is the vertex sort. -/
def VTerm.fv {K : Type} : VTerm K → Finset (Fin 4 × ℕ)
  | .var x => {(0, x)}
  | .const _ => ∅

/-- Free variables, tagged by sort: `0` vertex, `1` edge, `2` vertex set, `3` edge set. -/
def Formula.fv {r : ℕ} {K : Type} : Formula r K → Finset (Fin 4 × ℕ)
  | .tt => ∅
  | .ff => ∅
  | .eqV s t => s.fv ∪ t.fv
  | .eqE e f => {(1, e), (1, f)}
  | .memV s X => s.fv ∪ {(2, X)}
  | .memE e X => {(1, e), (3, X)}
  | .inc e s => {(1, e)} ∪ s.fv
  | .col _ s => s.fv
  | .neg φ => φ.fv
  | .conj φ ψ => φ.fv ∪ ψ.fv
  | .disj φ ψ => φ.fv ∪ ψ.fv
  | .impl φ ψ => φ.fv ∪ ψ.fv
  | .exV x φ => φ.fv.erase (0, x)
  | .allV x φ => φ.fv.erase (0, x)
  | .exE x φ => φ.fv.erase (1, x)
  | .allE x φ => φ.fv.erase (1, x)
  | .exVS X φ => φ.fv.erase (2, X)
  | .allVS X φ => φ.fv.erase (2, X)
  | .exES X φ => φ.fv.erase (3, X)
  | .allES X φ => φ.fv.erase (3, X)

/-- A sentence has no free individual or set variables (it may contain constant symbols). -/
def Formula.IsSentence {r : ℕ} {K : Type} (φ : Formula r K) : Prop := φ.fv = ∅

/-- Constant symbols of a vertex term. -/
def VTerm.consts {K : Type} [DecidableEq K] : VTerm K → Finset K
  | .var _ => ∅
  | .const c => {c}

/-- Constant symbols occurring in a formula; a formula is over `V_{C,B}` when they lie in `B`. -/
def Formula.consts {r : ℕ} {K : Type} [DecidableEq K] : Formula r K → Finset K
  | .tt => ∅
  | .ff => ∅
  | .eqV s t => s.consts ∪ t.consts
  | .eqE _ _ => ∅
  | .memV s _ => s.consts
  | .memE _ _ => ∅
  | .inc _ s => s.consts
  | .col _ s => s.consts
  | .neg φ => φ.consts
  | .conj φ ψ => φ.consts ∪ ψ.consts
  | .disj φ ψ => φ.consts ∪ ψ.consts
  | .impl φ ψ => φ.consts ∪ ψ.consts
  | .exV _ φ => φ.consts
  | .allV _ φ => φ.consts
  | .exE _ φ => φ.consts
  | .allE _ φ => φ.consts
  | .exVS _ φ => φ.consts
  | .allVS _ φ => φ.consts
  | .exES _ φ => φ.consts
  | .allES _ φ => φ.consts

/-- Quantifier rank (Definition C.1): `0` for atoms and `⊤, ⊥`; negation preserves it; a binary
connective takes the maximum; each quantifier adds one. -/
def Formula.qr {r : ℕ} {K : Type} : Formula r K → ℕ
  | .neg φ => φ.qr
  | .conj φ ψ => max φ.qr ψ.qr
  | .disj φ ψ => max φ.qr ψ.qr
  | .impl φ ψ => max φ.qr ψ.qr
  | .exV _ φ => φ.qr + 1
  | .allV _ φ => φ.qr + 1
  | .exE _ φ => φ.qr + 1
  | .allE _ φ => φ.qr + 1
  | .exVS _ φ => φ.qr + 1
  | .allVS _ φ => φ.qr + 1
  | .exES _ φ => φ.qr + 1
  | .allES _ φ => φ.qr + 1
  | _ => 0

/-- Size of a vertex term: `1 +` the variable name (constants count `1`). -/
def VTerm.size {K : Type} : VTerm K → ℕ
  | .var x => x + 1
  | .const _ => 1

/-- Size of a formula: one per symbol plus the names of its variables and the indices of its color
predicates. For a constant-free vocabulary only finitely many formulas have a given size, so a
function of `(k, |C|, ψ)` and a function of `k + |C| + size ψ` are interchangeable. -/
def Formula.size {r : ℕ} {K : Type} : Formula r K → ℕ
  | .tt => 1
  | .ff => 1
  | .eqV s t => 1 + s.size + t.size
  | .eqE e f => 1 + (e + 1) + (f + 1)
  | .memV s X => 1 + s.size + (X + 1)
  | .memE e X => 1 + (e + 1) + (X + 1)
  | .inc e s => 1 + (e + 1) + s.size
  | .col c s => 1 + (c.val + 1) + s.size
  | .neg φ => 1 + φ.size
  | .conj φ ψ => 1 + φ.size + ψ.size
  | .disj φ ψ => 1 + φ.size + ψ.size
  | .impl φ ψ => 1 + φ.size + ψ.size
  | .exV x φ => 1 + (x + 1) + φ.size
  | .allV x φ => 1 + (x + 1) + φ.size
  | .exE x φ => 1 + (x + 1) + φ.size
  | .allE x φ => 1 + (x + 1) + φ.size
  | .exVS x φ => 1 + (x + 1) + φ.size
  | .allVS x φ => 1 + (x + 1) + φ.size
  | .exES x φ => 1 + (x + 1) + φ.size
  | .allES x φ => 1 + (x + 1) + φ.size

/-- Prefix code of a vertex term: `[0, x]` for a variable, `[1, cK c]` for a constant. -/
def VTerm.encode {K : Type} (cK : K → ℕ) : VTerm K → List ℕ
  | .var x => [0, x]
  | .const c => [1, cK c]

/-- Prefix (Polish) code of a formula as a list of natural numbers: a constructor tag `0, …, 19`
followed by the codes of its arguments; constants are coded by `cK`. -/
def Formula.encode {r : ℕ} {K : Type} (cK : K → ℕ) : Formula r K → List ℕ
  | .tt => [0]
  | .ff => [1]
  | .eqV s t => 2 :: (s.encode cK ++ t.encode cK)
  | .eqE e f => [3, e, f]
  | .memV s X => 4 :: (s.encode cK ++ [X])
  | .memE e X => [5, e, X]
  | .inc e s => 6 :: e :: s.encode cK
  | .col c s => 7 :: c.val :: s.encode cK
  | .neg φ => 8 :: φ.encode cK
  | .conj φ ψ => 9 :: (φ.encode cK ++ ψ.encode cK)
  | .disj φ ψ => 10 :: (φ.encode cK ++ ψ.encode cK)
  | .impl φ ψ => 11 :: (φ.encode cK ++ ψ.encode cK)
  | .exV x φ => 12 :: x :: φ.encode cK
  | .allV x φ => 13 :: x :: φ.encode cK
  | .exE x φ => 14 :: x :: φ.encode cK
  | .allE x φ => 15 :: x :: φ.encode cK
  | .exVS x φ => 16 :: x :: φ.encode cK
  | .allVS x φ => 17 :: x :: φ.encode cK
  | .exES x φ => 18 :: x :: φ.encode cK
  | .allES x φ => 19 :: x :: φ.encode cK

end TwMSOCount.Main


