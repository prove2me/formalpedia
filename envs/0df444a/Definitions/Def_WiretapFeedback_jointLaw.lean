-- Prove2me | Definitions.Def_WiretapFeedback_jointLaw
-- name    : WiretapFeedback_jointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:59.299492+00:00
-- url     : https://prove2.me/theorems/11ac0d90-ba30-46f4-acdc-398be3a90473
-- title:
--   Joint input–output law $P_XW$
-- statement:
--   For an input distribution $P_X$ on a finite alphabet $\mathcal X$ and a channel $W:\mathcal X\to\mathcal O$, the joint law of input and output is
--   $$
--   (P_XW)(x,o)=P_X(x)\,W(o|x).
--   $$
--
--   For the wiretap channel $W:\mathcal X\to\mathcal Y\times\mathcal Z$ this is the law $P_{XYZ}$ of the triple $(X,Y,Z)$ used in Theorem 1 ("where $P_{XYZ}$ is given by $P_XW$").
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, proof of Theorem 1, p.3

import Mathlib
import Definitions.Def_WildeQIT_Channel

namespace WiretapFeedback

/-- The joint distribution `P_X W` of a channel input and output, `(x, o) ↦ P_X(x) W(o|x)`
(Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, proof of Theorem 1, p. 3: "where `P_{XYZ}` is given by
`P_X W`"). For the wiretap channel `W : X → Y × Z` it is a distribution on `X × Y × Z`, i.e. the
law `P_{XYZ}` of the triple `(X, Y, Z)`. -/
noncomputable def jointLaw {X O : Type} [Fintype X] [Fintype O] (p : WildeQIT.FinDist X)
    (W : WildeQIT.Channel X O) : WildeQIT.FinDist (X × O) where
  prob xo := p.prob xo.1 * (W xo.1).prob xo.2
  nonneg xo := mul_nonneg (p.nonneg _) ((W _).nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (W _).sum_eq_one, mul_one]
    exact p.sum_eq_one

end WiretapFeedback


