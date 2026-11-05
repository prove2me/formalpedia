-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_MarkovPolicy
-- name    : BauerleRiederMDP_RegimeSwitching_MarkovPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:09.077025+00:00
-- url     : https://prove2.me/theorems/0fa66a1d-0fba-441d-9f43-91514c86e4e8
-- title:
--   Markov policy $\pi=(f_0,f_1,\dots)$ of measurable maps
-- statement:
--   A **Markov policy** is a sequence $\pi=(f_0,f_1,\dots)$ of measurable maps $f_n:E\to A$; at time $n$ in state $x$ the action $f_n(x)$ is taken. An $N$-stage policy $(f_0,\dots,f_{N-1})$ is a Markov policy whose later rules are never used.
--
--   Admissibility, $f_n(x)\in D_n(x)$, which makes each $f_n$ a decision rule, is a separate predicate.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.1.5, p.16 (PDF p.31)

import Mathlib

namespace BauerleRiederMDP.RegimeSwitching

/-- A **Markov policy** `π = (f_0, f_1, …)`: a sequence of measurable maps `f_n : E → A`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 2.1.5, p.16, PDF p.31). Admissibility `f_n(x) ∈ D_n(x)`, which turns the
`f_n` into decision rules, is the separate predicate `MarkovPolicy.IsAdmissible`.

**Formalization Note.** An `N`-stage policy `(f_0, …, f_{N-1})` is a Markov policy whose rules
`f_n`, `n ≥ N`, are never used. -/
structure MarkovPolicy (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  /-- the decision rule `f_n` used at time `n` -/
  f : ℕ → E → A
  measurable_f : ∀ n, Measurable (f n)

end BauerleRiederMDP.RegimeSwitching


