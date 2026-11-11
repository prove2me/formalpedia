-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM_Zsupply
-- name    : SybilClinch_AdmissibleAMM_Zsupply
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:05.75414+00:00
-- url     : https://prove2.me/theorems/0bd401b4-30eb-4828-979c-c5ba21e3fa19
-- title:
--   Marginal-supply function $Z(p)$
-- statement:
--   With $a(z)=C'_+(z)$ the pool's right marginal ask, the marginal-supply function is
--   $$Z(p):=\sup\{z\in[0,x_0):a(z)\le p\},\qquad p\ge p_0,\qquad(36)$$
--   the amount of pool supply available at a right marginal ask of at most $p$. It is a generalized inverse of $a$, valid when $a$ has flat segments or jumps.
--
--   **Formalization Note** $a(z)$ is the right derivative `derivWithin C (Ici z) z`; $C$ need not be differentiable.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.3, (36), p.16 (PDF p.18); §3.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_C

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.3, (36), printed p.16 (PDF p.18): the marginal-supply function
`Z(p) := sup {z ∈ [0, x₀) : a(z) ≤ p}`, `p ≥ p₀`, where `a(z) = C′₊(z)` is the pool's right
marginal ask (§3.1, p.8).

**Formalization Note.** `a(z)` is the right derivative `derivWithin C (Ici z) z`, which exists for
the convex `C` at every `z < x₀`; `C` need not be differentiable. -/
noncomputable def AdmissibleAMM.Zsupply (A : AdmissibleAMM) (p : ℝ) : ℝ :=
  sSup {z : ℝ | 0 ≤ z ∧ z < A.x0 ∧ derivWithin A.C (Ici z) z ≤ p}

end SybilClinch


