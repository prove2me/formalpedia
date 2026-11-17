-- Prove2me | Definitions.Def_StretchDepth_Supplement_FPNPProc
-- name    : StretchDepth_Supplement_FPNPProc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:09:11.354474+00:00
-- url     : https://prove2.me/theorems/1a76eb2d-3b43-414b-a44b-c122d6b3f5b7
-- title:
--   $\mathbf{FP^{NP}}$ query procedures of complexity $q$ (Definition 5)
-- statement:
--   Fix $G:\{0,1\}^n\to\{0,1\}^N$. The propositional variables are $G(w)_i$ for $w\in\{0,1\}^n$ and $i<N$; a **literal** is a variable or its negation, and $G$ satisfies $G(w)_i$ iff $G(w)_i=1$ and $\neg G(w)_i$ iff $G(w)_i=0$. A **DNF** is a finite disjunction of terms, each a conjunction of literals; $G$ satisfies it iff some term has all its literals satisfied (the empty DNF is false). A DNF has **width** $q$ if every term has at most $q$ literals; the number of terms is not bounded.
--
--   An **$\mathbf{FP^{NP}}$ query procedure** with output in $\{0,1\}^N$ is a decision tree: at each node it presents a DNF and learns, at unit cost, whether $G$ satisfies it; the next DNF depends on all previous answers; at a leaf it outputs a string in $\{0,1\}^N$. A family $\mathrm{Solve}=(\mathrm{Solve}(y))_{y\in\{0,1\}^M}$ of such procedures has **complexity $q$** if on every input $y$ and every $G$ the run of $\mathrm{Solve}(y)^G$
--   1. asks at most $q$ DNFs, and
--   2. each DNF it asks has width at most $q$.
--
--   This is the solver model of the Avoid amplification reductions of Definition 6.
--
--   **Formalization Note** Bounds are imposed on the queries asked against actual functions $G$, not on branches no $G$ reaches. "Proceeds in $q$ phases" is read as at most $q$ phases.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Definition 5, p.15 (PDF p.15)

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_StretchDepth_RoundTree

set_option autoImplicit false

namespace StretchDepth.Supplement

open QAlgorithms

/-- A literal over the propositional variables `G(w)_i` (`w ∈ {0,1}^n`, `i < N`): the variable
`G(w)_i` when `pos = true`, its negation `¬G(w)_i` when `pos = false`. -/
structure Literal (n N : ℕ) where
  /-- the input `w` of `G` -/
  w : Bits n
  /-- the output coordinate `i` -/
  i : Fin N
  /-- `true` for `G(w)_i`, `false` for `¬G(w)_i` -/
  pos : Bool

/-- A DNF: a finite disjunction (list) of terms, each a conjunction (list) of literals. -/
abbrev DNF (n N : ℕ) := List (List (Literal n N))

/-- "Under the natural interpretation" (Definition 5, p.15): `G` satisfies the literal `G(w)_i` iff
`G(w)_i = 1`, and `¬G(w)_i` iff `G(w)_i = 0`. -/
def Literal.Sat {n N : ℕ} (G : Bits n → Bits N) (l : Literal n N) : Prop := G l.w l.i = l.pos

/-- `G` satisfies a DNF iff some term has all its literals satisfied (the empty DNF is false). -/
def DNF.Sat {n N : ℕ} (G : Bits n → Bits N) (φ : DNF n N) : Prop :=
  ∃ term ∈ φ, ∀ l ∈ term, l.Sat G

/-- A DNF of width `q`: every term is a conjunction of at most `q` literals. The number of terms
is not bounded. -/
def DNF.WidthLE {n N : ℕ} (φ : DNF n N) (q : ℕ) : Prop := ∀ term ∈ φ, term.length ≤ q

open Classical in
/-- The answer of an NP-query: whether `G` satisfies the DNF. -/
noncomputable def npAnswer {n N : ℕ} (G : Bits n → Bits N) (φ : DNF n N) : Bool :=
  decide (φ.Sat G)

/-- The queries asked along the path an answer function `x` selects, in order. -/
def pathQueries {ι κ α : Type*} : DecisionTree ι κ α → (ι → κ) → List ι
  | .leaf _, _ => []
  | .node i next, x => i :: pathQueries (next (x i)) x

/-- An `FP^NP` query procedure querying `G : {0,1}^n → {0,1}^N` with output in `{0,1}^N`: a
decision tree whose queries are DNFs over the variables `G(w)_i` and whose answers are bits
(whether `G` satisfies the DNF). -/
abbrev FPNPProc (n N : ℕ) := DecisionTree (DNF n N) Bool (Bits N)

/-- The output `Q^G` of the procedure against the function `G`. -/
noncomputable def FPNPProc.out {n N : ℕ} (Q : FPNPProc n N) (G : Bits n → Bits N) : Bits N :=
  Q.eval (npAnswer G)

/-- **`FP^NP` query procedure of complexity `q`** (for every input `y` of `Solve`).
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Definition 5, p.15: "An FP^NP query procedure Q of complexity q querying a
function G : {0,1}^n → {0,1}^N is defined as follows. Q^G proceeds in q phases. At each phase, a
single "NP-query" to G of complexity q is made, which is defined as follows: some DNF ϕ of width q
over the propositional variables (G(w)_i)_{w∈{0,1}^n, i≤N} is presented, and at unit cost it is
determined whether the function G satisfies ϕ under the natural interpretation … Based on this
determination (and all previous), we choose the next DNF to query, and so on."

`Solve` assigns a procedure to each input `y`; on every input and every real `G`, the run asks at
most `q` DNFs, each of width at most `q`.

**Formalization Note.** "q phases" is read as "at most q phases" (a procedure may stop early; it
can always ask dummy queries). The bounds are imposed on real runs only (the queries the procedure
asks against an actual `G`), as for the base mission's `IsConstruction` and `WithinQueries`;
`DecisionTree.MakesAtMost` is not used. Coordinates are `i : Fin N` (the page's `i ≤ N` with
`1`-based indices). The page's output in `{0,1}^*` is `{0,1}^N` here, as Definition 6 requires of
`Solve`. -/
def IsFPNPProc {M n N : ℕ} (Solve : Bits M → FPNPProc n N) (q : ℕ) : Prop :=
  ∀ (y : Bits M) (G : Bits n → Bits N),
    (Solve y).queries (npAnswer G) ≤ q ∧
      ∀ φ ∈ pathQueries (Solve y) (npAnswer G), φ.WidthLE q

end StretchDepth.Supplement


