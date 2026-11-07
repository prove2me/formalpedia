-- Prove2me | Definitions.Def_UniqueOptScores_Dtt
-- name    : UniqueOptScores_Dtt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:02.97114+00:00
-- url     : https://prove2.me/theorems/76024208-f1f7-41e6-8dc5-bf98e1fa977c
-- title:
--   The class $D^A = \mathrm{P}_{\mathrm{dtt}}(\mathrm{US}^A)$
-- statement:
--   A language $L$ belongs to $D^A$ if there are a fixed language $K \in \mathrm{US}^A$ and a clocked deterministic oracle transducer $T$ (with access to $A$, but not to $K$) such that, writing $(y_1, \dots, y_m)$ for the list output by $T^A$ on $x$,
--   $$
--   x \in L \iff \exists\, i \in [m]:\ y_i \in K .
--   $$
--   Queries to $A$ may be adaptive; the list to $K$ is produced before any answer about $K$ is known, and answers are combined by disjunction. An empty list rejects.
--
--   **Formalization Note** The list is decoded from the transducer's output; malformed output is the empty list. Its length is polynomial because $T$ is clocked.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, p.14 (Disjunctive access); Definition 3.1, p.15

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_IsClocked
import Definitions.Def_UniqueOptScores_output
import Definitions.Def_UniqueOptScores_decodeList
import Definitions.Def_UniqueOptScores_US

namespace UniqueOptScores

/-- **The class D^A = P_dtt(US^A) (disjunctive access).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Definition 3.1, p.15: "For an oracle A, a language L belongs to D^A := P_dtt(US^A) if it
has a disjunctive truth-table reduction to a fixed language K ∈ US^A, computed by a deterministic
polynomial-time oracle transducer T^A. The transducer may query A adaptively, but must generate its
entire query list without access to K. … acceptance is determined by the disjunction of the answers
to this list, and an empty list yields rejection."

`L ∈ Dtt A` if there are `K ∈ US A` and a clocked transducer `T` with oracle `A` such that `x ∈ L`
exactly when some string of the list output by `T` on `x` belongs to `K`.

**Formalization Note.** The list is decoded by `decodeList` (malformed output = empty list); an
empty list rejects. The list length is polynomial because `T` is clocked. -/
def Dtt (A : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ K ∈ US A, ∃ (T : HMBinPacking.OracleMachine) (t : Polynomial ℕ), IsClocked T t ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ y ∈ decodeList (output T A x), y ∈ K}

end UniqueOptScores


