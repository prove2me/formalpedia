-- Prove2me | Definitions.Def_UniqueOptScores_decodeList
-- name    : UniqueOptScores_decodeList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:53.096511+00:00
-- url     : https://prove2.me/theorems/790e5610-ec56-4b4d-93a0-242bc553f094
-- title:
--   Reading an output word as a list of queries
-- statement:
--   A transducer that generates a list of queries $(y_1, \dots, y_m)$ writes each $y_i$ with every bit doubled, followed by the separator $01$. The decoder inverts this encoding; a word that is not of this form is **malformed** and decodes to the empty list, as in the paper: "Malformed lists become empty lists". An empty list makes every disjunctive or parallel query procedure see no queries.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, p.14 ("outputs a list (y1, . . . , ym)"); Definition 3.1, p.15; Section 7.3, p.27 ("Malformed lists become empty lists")

import Mathlib

namespace UniqueOptScores

/-- Auxiliary parser for `decodeList`: reads bit pairs, `bb` appends `b` to the current entry,
`01` closes the entry; anything else is malformed (`none`). -/
def decodeListAux : List Bool → List Bool → List (List Bool) → Option (List (List Bool))
  | [], [], acc => some acc.reverse
  | [], _ :: _, _ => none
  | [_], _, _ => none
  | a :: b :: rest, cur, acc =>
      if a = b then decodeListAux rest (cur ++ [a]) acc
      else if a = false then decodeListAux rest [] (cur :: acc)
      else none

/-- **Reading a transducer's output as a list of query strings.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.14 ("outputs a list (y1, . . . , ym)"), Definition 3.1, p.15, and §7.3, p.27
("Malformed lists become empty lists").

The list `(y₁, …, y_m)` is encoded by writing each `yᵢ` with every bit doubled, followed by the
separator `01`. `decodeList` inverts this encoding and returns the empty list on a malformed word.

**Formalization Note.** A fixed, linear-time list encoding; the paper's convention that malformed
lists become empty lists (and hence reject) is built in. -/
def decodeList (w : List Bool) : List (List Bool) :=
  (decodeListAux w [] []).getD []

end UniqueOptScores


