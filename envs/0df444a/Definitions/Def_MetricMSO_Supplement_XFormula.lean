-- Prove2me | Definitions.Def_MetricMSO_Supplement_XFormula
-- name    : MetricMSO_Supplement_XFormula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:53:29.070031+00:00
-- url     : https://prove2.me/theorems/94ee9514-713e-4a7b-8136-e9248d0b6a14
-- title:
--   Formulas of the metric extensions $L[F]$ and their fragments
-- statement:
--   This definition gives the syntax of the metric extensions $L[F]$ of Definition 2.15, for $L\in\{\mathrm{FO},\mathrm{MSO}_1,\mathrm{CMSO}_1,\mathrm{MSO}_2,\mathrm{CMSO}_2\}$ and $F$ a set of metric atoms.
--
--   An extended formula is built from
--
--   1. a formula $\varphi$ of $\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$ (the published `MetricMSO.Formula`), read in the same variable assignment;
--   2. the distance atom $\mathrm{Dist}(x,y,\delta)$, where $\delta$ is a numerical parameter symbol (Definition 2.12);
--   3. the unguarded comparisons $\mathrm{EqDist}(x,y,u,v)$ and $\mathrm{Close}(x,u,v)$ (Definition 2.14);
--   4. the nearest-label atoms $\mathrm{NearLab}_i(x;S)$ with $S$ a vertex-set variable (Definition 2.13);
--
--   by negation, conjunction, disjunction and existential quantification over vertices, edges, vertex sets and edge sets. Variables are de Bruijn levels, one sequence per sort, as in the published syntax.
--
--   The **length** $|\varphi|$ is the length of the binary code. It counts the occurrences of the numerical symbols (their indices) but not their values: "we count its logical syntax, including the occurrences of the numerical symbols, but we do not include the binary encodings of their values".
--
--   The module also defines the fragments used by the supplement's theorems:
--
--   1. a feature record $F$ selecting the sorts (edge sort for the incidence logics $\mathrm{MSO}_2$, $\mathrm{CMSO}_2$), the modulo-counting atoms and each metric atom, with the logic $\mathrm{Logic}(F)$ of formulas using only these features;
--   2. first-order formulas over the adjacency structure with vertex colors (no set quantifier and no set argument);
--   3. the existential fragment (negation only on atoms; $\wedge$, $\vee$, $\exists x$);
--   4. $\mathrm{EMSO}_1$ formulas: a block of existential vertex-set quantifiers followed by a first-order formula that may use membership in those sets.
--
--   **Formalization Note** The separation and covering atoms occur only at the top level of packing-covering templates and are part of the template structure, not of this syntax. Disjunction is a constructor so that the existential fragment is syntactic.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Definitions 2.12–2.15, pp.18–19 (PDF 20–21); §1, p.10 (PDF 12)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_MetricMSO_Formula
import Definitions.Def_MetricMSO_IsFormulaIn

set_option autoImplicit false

namespace MetricMSO.Supplement

open MetricMSO
open ExponomialAssortment.FPTAS (encodeNat)

/-- **Formulas of the metric extensions `L[F]`** (Definitions 2.12–2.15).

Chakraborty, Ordyniak, Siebertz, *Model Checking for Metric Extensions of Monadic Second-Order
Logic* (arXiv:2610.41974, sha256 prefix ad3c5863), §2.8, pp.18–19 (PDF 20–21): Definition 2.12
(`Dist(u, v, δ)` with a numerical parameter symbol `δ`), Definition 2.13 (`NearLab_i(v; S)`),
Definition 2.14 (`EqDist(x, y, u, v)`, `Close(x, u, v)`) and Definition 2.15 ("we write L[F] for
the extension in which we additionally allow the atoms from F with arguments of the appropriate
sorts. Adding an atom does not add new kinds of quantification").

The variables are those of the published `MetricMSO.Formula`: four sorts (vertices, edges, vertex
sets, edge sets), each with its own de Bruijn levels. Constructors:
* `base φ`: a published CMSO2[SP, EqGC] formula `φ`, read in the same variable assignment (so every
  atom and connective of `MetricMSO.Formula` is available);
* `dist x y δ`: `Dist(x, y, δ)`, where `δ` is the index of a numerical parameter symbol;
* `eqDist x y u v`: `EqDist(x, y, u, v)`;
* `close x u v`: `Close(x, u, v)`;
* `nearLab i x S`: `NearLab_i(x; S)`, with `i` the index of an input label and `S` a vertex-set
  variable;
* `neg`, `and`, `or` and the four existential quantifiers `exV`, `exE`, `exVS`, `exES`.

**Formalization Note** `or` is a constructor (not the abbreviation `¬(¬φ ∧ ¬ψ)`) so that the
existential fragment ("negation only on atoms") can be stated syntactically. The separation and
covering atoms `Sep_δ(X, Y)`, `Cover_ρ(U, Y)` occur only at the top level of packing-covering
templates (Definition 6.1) and are part of `MetricMSO.Supplement.Template`, not of this syntax. -/
inductive XFormula : Type
  | base (φ : Formula) : XFormula
  | dist (x y δ : ℕ) : XFormula
  | eqDist (x y u v : ℕ) : XFormula
  | close (x u v : ℕ) : XFormula
  | nearLab (i x S : ℕ) : XFormula
  | neg (φ : XFormula) : XFormula
  | and (φ ψ : XFormula) : XFormula
  | or (φ ψ : XFormula) : XFormula
  | exV (φ : XFormula) : XFormula
  | exE (φ : XFormula) : XFormula
  | exVS (φ : XFormula) : XFormula
  | exES (φ : XFormula) : XFormula
  deriving DecidableEq

namespace XFormula

/-- **Binary encoding of an extended formula**: a five-bit tag (the published `Formula.tag`)
followed by the self-delimiting binary codes of the natural-number arguments (variable levels,
label indices and the *indices* of numerical parameter symbols, never their values) and the codes
of the subformulas, in prefix order; `base φ` writes the published code of `φ`. -/
def encode : XFormula → List Bool
  | base φ => Formula.tag 0 ++ φ.encode
  | dist x y δ => Formula.tag 1 ++ encodeNat x ++ encodeNat y ++ encodeNat δ
  | eqDist x y u v => Formula.tag 2 ++ encodeNat x ++ encodeNat y ++ encodeNat u ++ encodeNat v
  | close x u v => Formula.tag 3 ++ encodeNat x ++ encodeNat u ++ encodeNat v
  | nearLab i x S => Formula.tag 4 ++ encodeNat i ++ encodeNat x ++ encodeNat S
  | neg φ => Formula.tag 5 ++ encode φ
  | and φ ψ => Formula.tag 6 ++ encode φ ++ encode ψ
  | or φ ψ => Formula.tag 7 ++ encode φ ++ encode ψ
  | exV φ => Formula.tag 8 ++ encode φ
  | exE φ => Formula.tag 9 ++ encode φ
  | exVS φ => Formula.tag 10 ++ encode φ
  | exES φ => Formula.tag 11 ++ encode φ

/-- **The length `|φ|`**: the length of the binary code. It counts the logical syntax including
the occurrences (indices) of the numerical parameter symbols, but not their values (Definition
2.12, p.18: "we count its logical syntax, including the occurrences of the numerical symbols, but
we do not include the binary encodings of their values"). -/
def length (φ : XFormula) : ℕ := (encode φ).length

/-- `wellScoped φ dV dE dS dES`: every variable of `φ` refers to the context (`dV` vertex, `dE` edge,
`dS` vertex-set and `dES` edge-set variables) or to an enclosing quantifier; the published
`Formula.scopedAt` is used for the `base` parts. -/
def wellScoped : XFormula → ℕ → ℕ → ℕ → ℕ → Bool
  | base φ, dV, dE, dS, dES => φ.scopedAt dV dE dS dES
  | dist x y _, dV, _, _, _ => x < dV && y < dV
  | eqDist x y u v, dV, _, _, _ => x < dV && y < dV && u < dV && v < dV
  | close x u v, dV, _, _, _ => x < dV && u < dV && v < dV
  | nearLab _ x S, dV, _, dS, _ => x < dV && S < dS
  | neg φ, dV, dE, dS, dES => wellScoped φ dV dE dS dES
  | and φ ψ, dV, dE, dS, dES => wellScoped φ dV dE dS dES && wellScoped ψ dV dE dS dES
  | or φ ψ, dV, dE, dS, dES => wellScoped φ dV dE dS dES && wellScoped ψ dV dE dS dES
  | exV φ, dV, dE, dS, dES => wellScoped φ (dV + 1) dE dS dES
  | exE φ, dV, dE, dS, dES => wellScoped φ dV (dE + 1) dS dES
  | exVS φ, dV, dE, dS, dES => wellScoped φ dV dE (dS + 1) dES
  | exES φ, dV, dE, dS, dES => wellScoped φ dV dE dS (dES + 1)

/-- `φ` is a **sentence**: it has no free variable of any sort (numerical parameter symbols may
occur; their values come with the input). -/
def IsSentence (φ : XFormula) : Prop := φ.wellScoped 0 0 0 0 = true

/-- `symbolsBelow k φ`: every `Dist` atom of `φ` uses one of the numerical parameter symbols
`0, …, k − 1`. -/
def symbolsBelow (k : ℕ) : XFormula → Bool
  | dist _ _ δ => δ < k
  | neg φ => symbolsBelow k φ
  | and φ ψ => symbolsBelow k φ && symbolsBelow k ψ
  | or φ ψ => symbolsBelow k φ && symbolsBelow k ψ
  | exV φ => symbolsBelow k φ
  | exE φ => symbolsBelow k φ
  | exVS φ => symbolsBelow k φ
  | exES φ => symbolsBelow k φ
  | _ => true

/-- `nearLabSetIs j φ`: every `NearLab` atom of `φ` has the vertex-set variable of level `j` as its
set argument. -/
def nearLabSetIs (j : ℕ) : XFormula → Bool
  | nearLab _ _ S => S == j
  | neg φ => nearLabSetIs j φ
  | and φ ψ => nearLabSetIs j φ && nearLabSetIs j ψ
  | or φ ψ => nearLabSetIs j φ && nearLabSetIs j ψ
  | exV φ => nearLabSetIs j φ
  | exE φ => nearLabSetIs j φ
  | exVS φ => nearLabSetIs j φ
  | exES φ => nearLabSetIs j φ
  | _ => true

end XFormula

/-- **The features of a logic `L[F]`**: which sorts and atoms it may use.
* `edges`: edge and edge-set variables, incidence, edge predicates (MSO2/CMSO2, read on the
  incidence structure `I(G)`); without it the logic is an MSO1/CMSO1 variant (adjacency structure,
  vertex colors only);
* `card`: the modulo-counting atoms `card_{a,ℓ}` (the C of CMSO);
* `sp`, `eqgc`, `dist`, `eqDist`, `close`, `nearLab`: the metric atoms of Definition 2.15. -/
structure Features where
  edges : Bool
  card : Bool
  sp : Bool
  eqgc : Bool
  dist : Bool
  eqDist : Bool
  close : Bool
  nearLab : Bool

/-- `fAllowed F φ`: the published formula `φ` uses only the features `F`. -/
def fAllowed (F : Features) : Formula → Bool
  | .eqE .. => F.edges
  | .inc .. => F.edges
  | .memE .. => F.edges
  | .epred .. => F.edges
  | .cardV .. => F.card
  | .cardE .. => F.edges && F.card
  | .sp .. => F.sp
  | .eqgc .. => F.eqgc
  | .neg φ => fAllowed F φ
  | .and φ ψ => fAllowed F φ && fAllowed F ψ
  | .exV φ => fAllowed F φ
  | .exE φ => F.edges && fAllowed F φ
  | .exVS φ => fAllowed F φ
  | .exES φ => F.edges && fAllowed F φ
  | _ => true

/-- `XFormula.allowed F φ`: the extended formula `φ` is a formula of the logic with features `F`. -/
def XFormula.allowed (F : Features) : XFormula → Bool
  | .base φ => fAllowed F φ
  | .dist .. => F.dist
  | .eqDist .. => F.eqDist
  | .close .. => F.close
  | .nearLab .. => F.nearLab
  | .neg φ => XFormula.allowed F φ
  | .and φ ψ => XFormula.allowed F φ && XFormula.allowed F ψ
  | .or φ ψ => XFormula.allowed F φ && XFormula.allowed F ψ
  | .exV φ => XFormula.allowed F φ
  | .exE φ => F.edges && XFormula.allowed F φ
  | .exVS φ => XFormula.allowed F φ
  | .exES φ => F.edges && XFormula.allowed F φ

/-- The monadic logic with features `F`, as a set of extended formulas. -/
def Logic (F : Features) (φ : XFormula) : Prop := φ.allowed F = true

/-- `fFirstOrder m φ`: the published formula `φ` is a first-order formula over the adjacency
structure with vertex colors: only `⊥`, adjacency, equality of vertices, the vertex input
predicates, negation, conjunction and vertex quantifiers; if `m`, also membership `x ∈ X` in a
vertex-set variable (used for the first-order kernel of an EMSO1 formula). -/
def fFirstOrder (m : Bool) : Formula → Bool
  | .ff => true
  | .adj .. => true
  | .eqV .. => true
  | .vpred .. => true
  | .memV .. => m
  | .neg φ => fFirstOrder m φ
  | .and φ ψ => fFirstOrder m φ && fFirstOrder m ψ
  | .exV φ => fFirstOrder m φ
  | _ => false

/-- `fLiteral φ`: `φ` is a first-order atom over the adjacency structure (`⊥`, `E(x, y)`, `x = y`,
`L_j(x)`) or the negation of one. -/
def fLiteral : Formula → Bool
  | .ff => true
  | .adj .. => true
  | .eqV .. => true
  | .vpred .. => true
  | .neg .ff => true
  | .neg (.adj ..) => true
  | .neg (.eqV ..) => true
  | .neg (.vpred ..) => true
  | _ => false

namespace XFormula

/-- `firstOrder m φ`: `φ` is a first-order formula over the adjacency structure with vertex colors
(no set quantifier, no set argument; Definition 2.15: "in a first-order extension a set argument
must be a named unary predicate"), possibly with the metric atoms `Dist`, `EqDist`, `Close`; if
`m`, membership `x ∈ X` in vertex-set variables is allowed as well. -/
def firstOrder (m : Bool) : XFormula → Bool
  | base φ => fFirstOrder m φ
  | dist .. => true
  | eqDist .. => true
  | close .. => true
  | nearLab .. => false
  | neg φ => firstOrder m φ
  | and φ ψ => firstOrder m φ && firstOrder m ψ
  | or φ ψ => firstOrder m φ && firstOrder m ψ
  | exV φ => firstOrder m φ
  | exE _ => false
  | exVS _ => false
  | exES _ => false

/-- `existentialFO φ`: `φ` is an **existential first-order formula**: built from literals (atoms
and negated atoms, the metric atoms `Dist`, `EqDist`, `Close` included) by `∧`, `∨` and `∃x`. -/
def existentialFO : XFormula → Bool
  | base φ => fLiteral φ
  | dist .. => true
  | eqDist .. => true
  | close .. => true
  | neg (dist ..) => true
  | neg (eqDist ..) => true
  | neg (close ..) => true
  | neg (base φ) => fLiteral (.neg φ)
  | and φ ψ => existentialFO φ && existentialFO ψ
  | or φ ψ => existentialFO φ && existentialFO ψ
  | exV φ => existentialFO φ
  | _ => false

/-- `emso1 φ`: `φ` is an **EMSO1 formula**: a block `∃X₁ … ∃X_k` of existential vertex-set
quantifiers followed by a first-order formula over the adjacency structure that may use membership
in those sets. -/
def emso1 : XFormula → Bool
  | exVS φ => emso1 φ
  | φ => firstOrder true φ

end XFormula

/-- The features of `FO[R]`, `EMSO1[R]` and of the other adjacency logics with only the metric
atoms selected by `eq` (EqDist), `cl` (Close) and `d` (Dist): no edge sort, no counting, no SP,
no EqGC, no NearLab. -/
def foFeatures (d eq cl : Bool) : Features :=
  ⟨false, false, false, false, d, eq, cl, false⟩

/-- `FO[R]` for the unguarded predicates selected by `eq` (EqDist) and `cl` (Close): first-order
sentences over the adjacency structure with vertex colors. -/
def IsFO (eq cl : Bool) (φ : XFormula) : Prop :=
  φ.firstOrder false = true ∧ Logic (foFeatures false eq cl) φ

/-- The existential fragment of `FO[R]`. -/
def IsExFO (eq cl : Bool) (φ : XFormula) : Prop :=
  φ.existentialFO = true ∧ Logic (foFeatures false eq cl) φ

/-- `EMSO1[F]`: existential monadic second-order formulas over the adjacency structure whose
metric atoms are among `Dist` (if `d`), `EqDist` (if `eq`), `Close` (if `cl`). -/
def IsEMSO1 (d eq cl : Bool) (φ : XFormula) : Prop :=
  φ.emso1 = true ∧ Logic (foFeatures d eq cl) φ

/-- `MSO2[F']` (`card = false`) or `CMSO2[F']` (`card = true`) on incidence structures, with the
metric atoms `SP` (if `sp`), `EqGC` (if `eqgc`), `EqDist` (if `eq`), `Close` (if `cl`). -/
def incFeatures (card sp eqgc eq cl : Bool) : Features :=
  ⟨true, card, sp, eqgc, false, eq, cl, false⟩

/-- `MSO1[F']` (`card = false`) or `CMSO1[F']` (`card = true`) on adjacency structures, with the
metric atoms `SP` (if `sp`), `EqGC` (if `eqgc`), `EqDist` (if `eq`), `Close` (if `cl`). -/
def adjFeatures (card sp eqgc eq cl : Bool) : Features :=
  ⟨false, card, sp, eqgc, false, eq, cl, false⟩

/-- The features of single-interface nearest-label formulas (Definition 6.2): `CMSO2[SP, EqGC]`
plus `NearLab`; no `Dist`, `EqDist`, `Close`. -/
def nearLabFeatures : Features :=
  ⟨true, true, true, true, false, false, false, true⟩

/-- The embedding of `MetricMSO.Formula` into the extended syntax uses only the features of
`CMSO2[SP, EqGC]`. -/
theorem base_allowed (φ : Formula) :
    (XFormula.base φ).allowed ⟨true, true, true, true, false, false, false, false⟩ = true := by
  induction φ <;> simp_all [XFormula.allowed, fAllowed]

end MetricMSO.Supplement


