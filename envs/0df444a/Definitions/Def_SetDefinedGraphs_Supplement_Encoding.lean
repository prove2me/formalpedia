-- Prove2me | Definitions.Def_SetDefinedGraphs_Supplement_Encoding
-- name    : SetDefinedGraphs_Supplement_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:43:32.569747+00:00
-- url     : https://prove2.me/theorems/02d3c8b4-d239-4fbe-a5b8-0a06563f28da
-- title:
--   Finite codes of Boolean functions $f$ and of pairs $(P,Z)$, the inputs and outputs of the paper's algorithms
-- statement:
--   An algorithm receives a Boolean function $f:\{0,1\}^{d^2}\to\{0,1\}$ as finite data. Here $f$ is given by $d$ and the list of its satisfying assignments (its truth table), each a $d\times d$ Boolean matrix written as a list of rows: $f(Q)=1$ iff $Q$ is listed. Every Boolean function has such a code.
--
--   A pair $(P,Z)$ of dimension $d'$ is coded by $d'$, the $d'\times d'$ matrix of the clause digraph $\Delta_P$, and the list of pairs $(L_s,\lambda_s)$ with $L_s$ a list of coordinates. A code is **valid** if $P$ is a loopless path clause and every constraint has coordinates in $[d']$ and $\lambda_s\notin L_s$.
--
--   These codes make "an algorithm that, given $f$, decides" and "the pairs $(P_i,Z_i)$ can be computed from $f$" (Theorems 1.7 and 4.15) precise as computability on finite data.
--
--   **Formalization Note** Codes live in `ℕ × List (List (List Bool))` and `ℕ × List (List Bool) × List (List ℕ × ℕ)`, which are `Primcodable`; matrix entries beyond a short row read as `false`, so every code denotes a function or clause. Other standard truth-table presentations are computably interconvertible with this one.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 1.7 p.4 (PDF p.6); Theorem 4.15 p.31 (PDF p.33); proof of Lemma 4.16 p.31 (PDF p.33): "we construct a full DNF F for f from its truth table"

import Mathlib
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_Supplement_PathClauseClass

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- The `d × d` Boolean matrix (an assignment of the variables `q_{i,j}`, or a full clause over them) encoded by a list
of rows: entry `(i, j)` is the `j`-th entry of the `i`-th row, `false` where the list is too short. Every matrix
`Fin d → Fin d → Bool` has a code (the list of its rows). -/
def matrixOfCode {d : ℕ} (M : List (List Bool)) : Fin d → Fin d → Bool :=
  fun i j => (M.getD i.1 []).getD j.1 false

/-- Codes of Boolean functions: a list of `d × d` matrix codes. -/
abbrev BoolFnCode : Type := List (List (List Bool))

/-- The Boolean function `f : {0,1}^{d²} → {0,1}` presented by a code `c` (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev,
*Set-defined graph classes: χ-boundedness meets tropical algebra*, arXiv:2607.23754 (held version, sha256 642c0d70…),
Theorems 1.7 and 4.15, pp.4, 31): `f(Q) = 1` iff `Q` is one of the matrices listed in `c`. This is the finite input "a
Boolean function `f`" of an algorithm: the list of the satisfying assignments (the truth table), which by the paper's
convention is how `f` is given (p.31: "we construct a full DNF F for f from its truth table").

**Formalization Note** The input of an algorithm is the pair `(d, c) : ℕ × BoolFnCode`, which is `Primcodable`. Every
Boolean function has a code (list its satisfying matrices), and a code of any shape denotes a function (rows padded with
`false`); converting between this and any other standard presentation of a truth table is computable, so computability
does not depend on the choice. -/
def fnOfCode (d : ℕ) (c : BoolFnCode) : (Fin d → Fin d → Bool) → Bool :=
  fun Q => c.any (fun M => decide (∀ i j : Fin d, matrixOfCode M i j = Q i j))

/-- Codes of pairs `(P, Z)` (of a dimension `d′`): `(d′, P, Z)` with `P` a `d′ × d′` matrix code (the clause digraph of
the full clause) and `Z` a list of pairs `(L, λ)` with `L` a list of coordinates. -/
abbrev PZCode : Type := ℕ × List (List Bool) × List (List ℕ × ℕ)

/-- The full clause `P` (over `d′²` variables, `d′ = x.1`) encoded by `x`. -/
def pzClause (x : PZCode) : FullClause (Fin x.1) :=
  matrixOfCode x.2.1

/-- The functional constraints `Z = ((L₁, λ₁), …)` over `[d′]` encoded by `x`: each code `(L, λ)` with `λ < d′` gives
`(L ∩ [d′], λ)`. On valid codes (`IsValidPZCode`) no entry is dropped or truncated. -/
def pzConstraints (x : PZCode) : List (Finset (Fin x.1) × Fin x.1) :=
  x.2.2.filterMap (fun p => if h : p.2 < x.1 then
    some (Finset.univ.filter (fun i : Fin x.1 => i.1 ∈ p.1), ⟨p.2, h⟩) else none)

/-- A code `x` is **valid** if it encodes a loopless path clause `P` over `[d′]` and a tuple `Z` of functional
constraints over `[d′]` (every coordinate `< d′`, `λ_s ∉ L_s`), the data of a class `Y⃗_{P,Z}` (arXiv:2607.23754,
§4.5 p.30). -/
def IsValidPZCode (x : PZCode) : Prop :=
  IsLooplessPathClause (pzClause x) ∧ ∀ p ∈ x.2.2, p.2 < x.1 ∧ p.2 ∉ p.1 ∧ ∀ i ∈ p.1, i < x.1

end SetDefinedGraphs.Supplement


