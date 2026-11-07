-- Prove2me | Definitions.Def_GeoSemialgCSP_Inst
-- name    : GeoSemialgCSP_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:00.998913+00:00
-- url     : https://prove2.me/theorems/ef01f337-87e1-4010-85bb-84eba563fb28
-- title:
--   Unweighted $k$-ary CSP instance
-- statement:
--   An **instance** of a $k$-ary CSP consists of a number $n$ of variables $[n]=\{0,\dots,n-1\}$ and a finite list of constraints, each an ordered $k$-tuple $(i_1,\dots,i_k)$ of variables. A constraint may be listed several times; its multiplicity is its weight.
--
--   The paper's reduction ends with unweighted instances ("The resulting unweighted instance has at most $Q$ constraints"), obtained from rational weights by parallel copies; these are the instances of the hardness theorems.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 'CSP instances and solutions', p.7 (PDF p.8); proof of Theorem 6.1, p.19 (PDF p.20)

import Mathlib

namespace GeoSemialgCSP

/-- **Unweighted CSP instance.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 "CSP instances and solutions", printed p.7
(PDF p.8), and the proof of Theorem 6.1, printed p.19 (PDF p.20): "The resulting unweighted
instance has at most Q constraints".

An instance of a `k`-ary CSP has variables `[n]` and a list of constraints, each an ordered
`k`-tuple of variables.

**Formalization Note.** A list with repetitions: a constraint listed `m` times has weight `m`
(the unweighted form with parallel copies, which is how the paper removes weights). -/
structure Inst (k : ℕ) where
  /-- the number of variables -/
  n : ℕ
  /-- the constraints, each an ordered `k`-tuple of variables -/
  cons : List (Fin k → Fin n)

end GeoSemialgCSP


