-- Prove2me | Definitions.Def_MinCostMaj_encInst
-- name    : MinCostMaj_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:24:30.800719+00:00
-- url     : https://prove2.me/theorems/fcb69fbb-c495-4cf2-9bbc-0723a3d81c16
-- title:
--   Fixed binary encodings of instances, coin strings and answers
-- statement:
--   To speak of polynomial-time algorithms, every input and output is written as a word over the four-letter alphabet $\{0,1,2,3\}$: $0,1$ are bits, $2$ separates the numerator and denominator of a rational (and stands alone for the cost $\infty$), and $3$ ends each token. Natural numbers are written in binary and rationals as reduced numerator and denominator; lists are prefixed by their length.
--
--   - A $\mathrm{MinCostCSP}$ instance is encoded as $n$, the constraints (relation index, scope length, scope) and the cost rows.
--   - An instance together with a coin string appends one token of coin bits.
--   - An answer is a list of values (an assignment) or the token "$2$" for *infeasible*.
--   - A $\mathrm{cUG}$ instance is encoded as $n$ followed by its arcs (two endpoints and a weight), and a $\mathrm{cUG}$ instance together with a list of values appends the list.
--
--   These encodings fix the input length with respect to which running times are measured.
--
--   **Formalization Note** The alphabet and the number encodings are the published `OnlineCRS.Combine.{Sym, bit, encNat, encInt, encRat}`. No number is written in unary.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem 1.1, p.4 ("polynomial-time") (PDF p.5)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_MinCostMaj_MCInst
import Definitions.Def_MinCostMaj_CUGInst

namespace MinCostMaj

open OnlineCRS.Combine

/-- Words joined as tokens: every word followed by the separator symbol `3`. -/
def tokJoin (ws : List (List Sym)) : List Sym :=
  ws.flatMap fun w => w ++ [3]

/-- A cost entry: `some q ↦ encRat q` (starts with a sign bit), `none` (∞) `↦ [2]`. -/
def encCost : Option ℚ → List Sym
  | none => [2]
  | some q => encRat q

/-- The tokens of a MinCostCSP instance: `n`; the number of constraints, then each constraint as
its relation index, its scope length and its scope; the number of cost rows, then each row as its
length and its entries. -/
def instTokens (I : MCInst) : List (List Sym) :=
  [encNat I.n, encNat I.cons.length] ++
    I.cons.flatMap (fun c => encNat c.1 :: encNat c.2.length :: c.2.map encNat) ++
    [encNat I.cost.length] ++
    I.cost.flatMap (fun row => encNat row.length :: row.map encCost)

/-- **Binary encoding of a MinCostCSP(A) instance** (input of the machines of Theorem 1.1).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem 1.1, p.4 ("polynomial-time").

**Formalization Note.** The paper names no machine model. "Polynomial time" is read in Mathlib's
`Turing.TM2ComputableInPolyTime`, which needs a fixed encoding over a finite alphabet. The alphabet
is the published `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational and for `∞`, `3`
separator); numbers are binary (`encNat`), rationals are reduced numerator and denominator
(`encRat`); every token is followed by `3`; lists are length-prefixed. No number is unary. -/
def encInst (I : MCInst) : List Sym :=
  tokJoin (instTokens I)

/-- **Encoding of an instance with a coin string** (input of the randomized machine): the instance
tokens, then one token of coin bits. -/
def encInstCoins (x : MCInst × List Bool) : List Sym :=
  tokJoin (instTokens x.1 ++ [x.2.map bit])

/-- **Encoding of a list of natural numbers**: each in binary followed by `3`. -/
def encList (L : List ℕ) : List Sym :=
  tokJoin (L.map encNat)

/-- **Encoding of an algorithm's answer**: an assignment (list of values) as `encList`, and the
answer "infeasible" (`none`) as the token `[2]`, which no `encList` word contains. -/
def encOut : Option (List ℕ) → List Sym
  | none => tokJoin [[2]]
  | some L => encList L

/-- The tokens of a cUG instance: `n`, the number of arcs, then each arc as its two endpoints and
its weight. -/
def cugTokens (G : CUGInst) : List (List Sym) :=
  [encNat G.n, encNat G.arcs.length] ++
    G.arcs.flatMap (fun e => [encNat e.1, encNat e.2.1, encRat e.2.2])

/-- **Binary encoding of a cUG(k) instance** (input of the reduction map `Φ`). -/
def encCUG (G : CUGInst) : List Sym :=
  tokJoin (cugTokens G)

/-- **Encoding of a cUG instance with a solution of the target instance** (input of the solution
map `Ψ`): the cUG tokens, then the number of values, then the values. -/
def encCUGSol (x : CUGInst × List ℕ) : List Sym :=
  tokJoin (cugTokens x.1 ++ [encNat x.2.length] ++ x.2.map encNat)

end MinCostMaj


