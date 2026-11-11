-- Prove2me | Definitions.Def_SybilClinch_Dir
-- name    : SybilClinch_Dir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:36:57.831363+00:00
-- url     : https://prove2.me/theorems/d7f9ea66-4533-4514-8e67-5b6e09c090ed
-- title:
--   Order direction: sell-$Y$ or sell-$X$
-- statement:
--   Every order (and every physical trader's type) has one of two directions: a **sell-$Y$** order offers $Y$ in exchange for $X$, and a **sell-$X$** order offers $X$ in exchange for $Y$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, p.5 (PDF p.7)

import Mathlib

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, printed p.5 (PDF p.7): the two order directions. A sell-`Y` order sells `Y` for `X`;
a sell-`X` order sells `X` for `Y`. -/
inductive Dir where
  | sellY
  | sellX
  deriving DecidableEq

end SybilClinch


