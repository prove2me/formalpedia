-- Prove2me | Definitions.Def_SmoothedNash_Supplement_PredOut
-- name    : SmoothedNash_Supplement_PredOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:03:47.695776+00:00
-- url     : https://prove2.me/theorems/9592ddd1-d99a-473e-bb7d-60af62c22731
-- title:
--   Outputs Run / Stop / Project of the stopping predicate
-- statement:
--   The stopping predicate of Lemma 4.4 takes one of three values: **Run** (continue the path following), **Stop** (return the current point) and **Project** (return the current point projected radially onto the unit sphere).
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 4.4, p.27

import Mathlib

namespace SmoothedNash.Supplement

/-- The three outputs `Run`, `Stop`, `Project` of the stopping predicate `H` of Lemma 4.4
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.27). -/
inductive PredOut : Type
  | run
  | stop
  | project
  deriving DecidableEq

end SmoothedNash.Supplement


