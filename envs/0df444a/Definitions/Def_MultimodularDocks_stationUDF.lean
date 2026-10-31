-- Prove2me | Definitions.Def_MultimodularDocks_stationUDF
-- name    : MultimodularDocks_stationUDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:38.893075+00:00
-- url     : https://prove2.me/theorems/b25b3cd4-dc6a-41d6-b08b-2b83956b9853
-- title:
--   Station UDF $c_i(d,b)=\mathbb E_{X\sim p_i}[c_X(d,b)]$
-- statement:
--   For a **demand profile** $p_i$ at station $i$, a probability distribution over finite arrival sequences, the station's user dissatisfaction function is the expected (weighted) number of out-of-stock events,
--
--   $$
--   c_i(d,b)=\mathbb E_{X\sim p_i}\bigl[c_X(d,b)\bigr]=\sum_{X} p_i(X)\,c_X(d,b).
--   $$
--
--   **Formalization Note** The demand profile is a `PMF (List Arrival)`, and the expectation is the series $\sum_X p_i(X)\,c_X(d,b)$. Lean assigns the value $0$ to a non-summable series, so results about $c_i$ assume summability explicitly.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §2, p.9

import Mathlib
import Definitions.Def_MultimodularDocks_udf

namespace MultimodularDocks

/-- **The UDF of a station** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, §2, p.9):
`c_i(d, b) = E_{X∼p_i}[c_X(d, b)]`, the expected (weighted) number of out-of-stock events at a
station with `d` empty docks and `b` bikes, for a demand profile `p_i`, a distribution over
arrival sequences.

**Formalization Note** The demand profile is a `PMF (List Arrival)` on the countable set of
finite arrival sequences, and the expectation is the sum `∑' X, p(X) · c_X(d, b)`. Lean's `tsum`
of a non-summable family is `0`, so every statement about `stationUDF` that needs the
expectation to be finite assumes summability explicitly. -/
noncomputable def stationUDF (p : PMF (List Arrival)) (η : ℝ) (d b : ℤ) : ℝ :=
  ∑' X, (p X).toReal * udf η d b X

end MultimodularDocks


