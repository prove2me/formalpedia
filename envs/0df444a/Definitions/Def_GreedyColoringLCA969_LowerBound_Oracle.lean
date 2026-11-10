-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Oracle
-- name    : GreedyColoringLCA969_LowerBound_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:43:53.689689+00:00
-- url     : https://prove2.me/theorems/185e5d80-6a21-4a80-84b3-8134d683350d
-- title:
--   Standard degree/neighbor oracle and the stronger full-list oracle
-- statement:
--   For a represented graph with ordered lists $L_v$, the standard interface permits two graph queries: the degree of any vertex and its neighbor at any positive integer position. A query past the list end returns a distinguished null response:
--
--   $$\operatorname{Degree}(v)=|L_v|,\qquad
--   \operatorname{Neighbor}(v,i)=\begin{cases}L_v[i],&1\le i\le |L_v|,\\\bot,&i>|L_v|.\end{cases}$$
--
--   The stronger interface in Section 3 footnote 2 returns all of $L_v$ in one query. Either kind of graph call costs one query. Degree is then recoverable from list length. There is no requirement that a queried vertex be near the questioned vertex.
--
--   **Formalization Note** Positive positions are typed as positive integers. Replies use finite lists of natural numbers: a degree reply is the singleton containing the degree; a neighbor reply is a singleton containing the zero-based vertex code, or the empty list for null. A full-list reply preserves the supplied order. The known query tag disambiguates these encodings, including vertex code zero.
--
--   Differences from the source:
--   - encoding: positive neighbor positions, degree replies, neighbor identifiers and bottom → positive-integer positions and tagged finite-list reply codes; reason: the codes distinguish every reply, including vertex zero and bottom; list order is unchanged
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Definition 2.5, p.8 (PDF 9); Section 3 footnote 2, p.10 (PDF 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_Representation

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

inductive OracleMode where
  | standard
  | fullList
  deriving DecidableEq

/-- Neighbor positions are positive, as in Definition 2.5. -/
abbrev StandardQuery (n : ℕ) := Fin n ⊕ (Fin n × ℕ+)

/-- The full-list model in footnote 2 has one query for an entire list. -/
def GraphQuery : OracleMode → ℕ → Type
  | .standard, n => StandardQuery n
  | .fullList, n => Fin n

/-- Replies are finite lists of natural vertex codes. For a standard degree query the
reply is [degree]; for a neighbor query it is [ID] or [], with [] denoting bottom.
IDs are zero-based Fin values. The query tag makes these encodings unambiguous. -/
def oracleReply {n : ℕ} (m : OracleMode) (R : Representation n) : GraphQuery m n → List ℕ :=
  match m with
  | .standard => fun q => match q with
    | .inl v => [(R.val v).length]
    | .inr (v, i) => ((R.val v)[i.val - 1]?).toList.map Fin.val
  | .fullList => fun v => (R.val v).map Fin.val

end GreedyColoringLCA969.LowerBound


