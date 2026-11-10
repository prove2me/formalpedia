-- Prove2me | Definitions.Def_NearOptOWF_OracleDist
-- name    : NearOptOWF_OracleDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:28.507973+00:00
-- url     : https://prove2.me/theorems/8c948bbd-dbc6-40ef-b63b-bc8038e5f448
-- title:
--   Non-uniform adaptive oracle distinguisher
-- statement:
--   An **oracle distinguisher** is a list of query circuits and a final circuit, all with the same number of inputs. Query circuit $i$ reads the answers received so far and outputs query $i$; the final circuit reads all answers and outputs a bit. It models a polynomial-size adaptive oracle circuit, such as the test in the proof of Lemma 4.10 that queries $f$ at random points.
--
--   **Formalization Note** This encoding and polynomial-size oracle circuits simulate each other with polynomial overhead, which the sub-exponential bound $2^{-\lambda^\delta}$ with existential $\delta$ absorbs.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19); its proof, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- A **non-uniform adaptive oracle distinguisher** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19):
"`H` … is a sub-exponentially secure PRF", whose proof runs a polynomial-time test with oracle access
to `f`, p.18 (PDF p.20)): a list of query circuits and a final circuit, all with `arity` inputs. Query
circuit `i` maps the answers received so far to query `i`; the final circuit maps all answers to the
output bit.

**Formalization Note** This is a polynomially equivalent encoding of polynomial-size oracle circuits;
the sub-exponential security bound `∃ δ, 2^{−λ^δ}` absorbs the polynomial blow-up between the two
models. -/
structure OracleDist where
  /-- the common number of inputs of the circuits -/
  arity : ℕ
  /-- the query circuits, in order -/
  queries : List (MCircuit arity)
  /-- the circuit computing the output bit -/
  final : MCircuit arity

end NearOptOWF


