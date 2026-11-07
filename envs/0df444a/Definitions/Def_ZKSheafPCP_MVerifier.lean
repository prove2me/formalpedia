-- Prove2me | Definitions.Def_ZKSheafPCP_MVerifier
-- name    : ZKSheafPCP_MVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:10:54.871437+00:00
-- url     : https://prove2.me/theorems/9bc256a2-0e38-4d01-91c3-d6f52cf06a6b
-- title:
--   Malicious verifiers, their view, and the simulator's black-box access
-- statement:
--   A **malicious verifier** with $m$ coins is an arbitrary function that, given its coins and the answers received so far, names its next query or stops. It is **$b$-query bounded** if it stops after $b$ answers on every answer sequence. Its **view** $\mathrm{View}_{V^*,P}$ comprises its random coins and all answers to its queries: the law of $(r,\text{answers})$ with $r$ uniform and the proof drawn from the prover, independently.
--
--   The simulator reads a verifier through a **bit oracle**: the query $(r,\text{answers},j)$ returns bit $j$ of a code of the next move. The simulator gets the explicit input, $1^m$ and its own coins, and writes the view in a fixed code.
--
--   **Formalization Note** The verifier has unbounded complexity and any coin length, so the simulator must get $1^m$: it has to output $m$ coins, and Definition 3.28 puts no bound on $m$.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definitions 3.26, 3.28, p.14

import Mathlib
import Definitions.Def_ZKSheafPCP_queryLog

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace ZKSheafPCP

open Classical

/-- A possibly malicious adaptive verifier (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission,
manuscript sha256 ac5e528f…, Definitions 3.26 and 3.28, p.14): given its `m` coins and the answers so far, it
names its next query or stops.

**Formalization Note** `next` is an arbitrary function, so the verifier has unbounded complexity and any
coin length `m`. Queries lie in `Pos`, so no out-of-range query exists. -/
structure MVerifier (m : ℕ) (Pos : Type) (a : ℕ) where
  /-- the next query, or `none` to stop -/
  next : (Fin m → Bool) → List (Fin a) → Option Pos

/-- `q∗`-query-boundedness: the verifier stops after `b` answers, on every answer sequence. Repeated
queries count. -/
def MVerifier.Bounded {m : ℕ} {Pos : Type} {a : ℕ} (V : MVerifier m Pos a) (b : ℕ) : Prop :=
  ∀ r as, b ≤ as.length → V.next r as = none

/-- The interaction with a fixed answer table `ans`, for at most `fuel` queries, from the answers `as`. -/
def MVerifier.interact {m : ℕ} {Pos : Type} {a : ℕ} (V : MVerifier m Pos a) (r : Fin m → Bool)
    (ans : Pos → Fin a) : ℕ → List (Fin a) → List (Fin a)
  | 0, as => as
  | fuel + 1, as =>
    match V.next r as with
    | none => as
    | some p => MVerifier.interact V r ans fuel (as ++ [ans p])

/-- `View_{V∗,P}` (Definition 3.26, p.14), "`V∗`'s random coins and all answers to `V∗`'s queries": the
law of `(r, answers)` with `r` uniform and the answer table drawn from `law`, independently. -/
noncomputable def MVerifier.viewLaw {m : ℕ} {Pos : Type} {a : ℕ} (V : MVerifier m Pos a)
    (law : PMF (Pos → Fin a)) (b : ℕ) : PMF ((Fin m → Bool) × List (Fin a)) :=
  (PMF.uniformOfFintype (Fin m → Bool)).bind fun r =>
    law.map fun ans => (r, V.interact r ans b [])

/-- The black-box oracle of a malicious verifier, as the simulator reads it: on the query
`(r, j, as)` it answers bit `j` of the code of `next r as`, where `none` has code `0` and a position `p` has
code `code p + 1`. Every other string answers `false`.

**Formalization Note** The simulator reads the verifier one bit at unit cost, and never sees it otherwise. -/
noncomputable def MVerifier.oracle {m : ℕ} {Pos : Type} {a : ℕ} (V : MVerifier m Pos a)
    (code : Pos → ℕ) : Oracle := fun q =>
  decide (∃ (r : Fin m → Bool) (as : List (Fin a)) (j : ℕ),
    q = tup ([coinStr r, binN j] ++ as.map fun s => binN s.val) ∧
    (match V.next r as with
      | none => 0
      | some p => code p + 1).testBit j = true)

/-- The fixed code of a view, as the simulator writes it. It is injective, since the coins have fixed
length and `tup` is injective. -/
def viewCode {m a : ℕ} (v : (Fin m → Bool) × List (Fin a)) : Str :=
  tup (coinStr v.1 :: v.2.map fun s => binN s.val)

/-- The simulator's input: the explicit input `x`, `1^m`, and its coins `s`.

**Formalization Note** The simulator gets `1^m` because it has to output `m` coins; it runs in time
polynomial in `|x| + m`. This is the only reading in which "PPT" can hold, since Definition 3.28 puts no
bound on the coin length of `V∗`. -/
def simInput {σ : ℕ} (x : Str) (m : ℕ) (s : Fin σ → Bool) : Str :=
  tup [x, unary m, coinStr s]

end ZKSheafPCP


