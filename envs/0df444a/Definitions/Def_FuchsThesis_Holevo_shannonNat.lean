-- Prove2me | Definitions.Def_FuchsThesis_Holevo_shannonNat
-- name    : FuchsThesis_Holevo_shannonNat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:17.204086+00:00
-- url     : https://prove2.me/theorems/246cf75b-1967-4b61-a90f-d4a98ba0093d
-- title:
--   Shannon information $H(q)$ in nats
-- statement:
--   For a function $q$ on a finite set (a probability distribution in all uses), the Shannon information is
--
--   $$
--   H(q) = -\sum_b q(b)\ln q(b),
--   $$
--
--   measured in **nats** (natural logarithm), with the convention $0\ln 0=0$.
--
--   It is the entropy entering the mutual information (3.144) of a binary quantum channel.
--
--   **Formalization Note** The summand is Mathlib's `Real.negMulLog`, $x\mapsto -x\ln x$, which is $0$ at $x=0$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.145), pp.64–65 (PDF pp.73–74)

import Mathlib

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.145), pp.64–65 (PDF pp.73–74): the Shannon
information `H(q) = −∑_b q(b) ln q(b)` of a distribution `q` on a finite set, in **nats**
("Because a natural logarithm has been used in this definition, information here is quantified in
terms of 'nats'", p.65).

**Formalization Note.** `Real.negMulLog x = −x ln x`, with `negMulLog 0 = 0` (the convention
`0 ln 0 = 0`). -/
noncomputable def shannonNat {X : Type} [Fintype X] (q : X → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (q x)

end FuchsThesis.Holevo


