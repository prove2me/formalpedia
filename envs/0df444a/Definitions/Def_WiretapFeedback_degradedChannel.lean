-- Prove2me | Definitions.Def_WiretapFeedback_degradedChannel
-- name    : WiretapFeedback_degradedChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:53.820858+00:00
-- url     : https://prove2.me/theorems/185f268a-a937-4f8b-acc3-f902c6990aa9
-- title:
--   Degraded-form wiretap channel $V(y,z|x)=V_2(z|x)V_1(y|z)$
-- statement:
--   Given channels $V_2:\mathcal X\to\mathcal Z$ and $V_1:\mathcal Z\to\mathcal Y$, the wiretap channel $V:\mathcal X\to\mathcal Y\times\mathcal Z$ is
--   $$
--   V(y,z|x)=V_2(z|x)\,V_1(y|z),
--   $$
--   in which the legitimate receiver's output is a degraded version of the eavesdropper's. These are the alternative hypotheses of Theorem 6 and Lemma 7.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, Theorem 6 and Lemma 7, p.3

import Mathlib
import Definitions.Def_WildeQIT_Channel

namespace WiretapFeedback

/-- The wiretap channel `V : X → Y × Z` with `V(y, z|x) = V₂(z|x) V₁(y|z)` built from channels
`V₂ : X → Z` and `V₁ : Z → Y` (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, Theorem 6 and
Lemma 7, p. 3): the eavesdropper's output is produced first and the legitimate receiver's output
is a degraded version of it. -/
noncomputable def degradedChannel {X Y Z : Type} [Fintype Y] [Fintype Z]
    (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y) : WildeQIT.Channel X (Y × Z) :=
  fun x =>
    { prob := fun yz => (V₂ x).prob yz.2 * (V₁ yz.2).prob yz.1
      nonneg := fun yz => mul_nonneg ((V₂ x).nonneg _) ((V₁ _).nonneg _)
      sum_eq_one := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp_rw [← Finset.mul_sum, (V₁ _).sum_eq_one, mul_one]
        exact (V₂ x).sum_eq_one }

end WiretapFeedback


