-- Prove2me | Definitions.Def_SybilClinch_Fill
-- name    : SybilClinch_Fill
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:00.013207+00:00
-- url     : https://prove2.me/theorems/9c9b84ba-21cd-4a09-a0a0-d3b1d267e82c
-- title:
--   Outcome of one identity: amount sold, amount received
-- statement:
--   The outcome of one identity is a pair (sold, received). For a sell-$Y$ identity it is $(S_{Y,i},R_{X,i})$, units of $Y$ sold and of $X$ received; for a sell-$X$ identity it is $(S_{X,i},R_{Y,i})$, units of $X$ sold and of $Y$ received. The per-identity feasibility constraints (1)–(2) are $0\le S\le$ budget and $R\ge0$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, (1)–(2), p.5 (PDF p.7)

import Mathlib

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, printed p.5 (PDF p.7), (1)–(2): the outcome of one identity. For a sell-`Y` identity,
`sold = S_{Y,i}` units of `Y` sold and `recv = R_{X,i}` units of `X` received; for a sell-`X`
identity, `sold = S_{X,i}` units of `X` sold and `recv = R_{Y,i}` units of `Y` received. -/
structure Fill where
  /-- Units of the identity's budget token sold (`S_{Y,i}` or `S_{X,i}`). -/
  sold : ℝ
  /-- Units of the other token received (`R_{X,i}` or `R_{Y,i}`). -/
  recv : ℝ

end SybilClinch


