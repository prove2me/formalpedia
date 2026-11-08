-- Prove2me | Definitions.Def_DPVerify_IsReplicableAt
-- name    : DPVerify_IsReplicableAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:11.89568+00:00
-- url     : https://prove2.me/theorems/186d664d-e2e8-4868-b9e6-fd214d0b89a2
-- title:
--   $\rho$-replicability at a distribution $D$
-- statement:
--   Let $D$ be a distribution on $\mathcal X$ and $\mathcal A$ a randomized algorithm with internal randomness $r$. The algorithm is **$\rho$-replicable at $D$** if two runs on independent i.i.d. samples $S,S'\sim D^m$ that share the internal randomness $r$ agree with probability at least $1-\rho$:
--
--   $$
--   \Pr_{S,S',r}\bigl[\mathcal A(S,r)=\mathcal A(S',r)\bigr]\;\ge\;1-\rho .
--   $$
--
--   Replicability is what lets the reduction of Theorem 4.1 replace the verifier's sample-dependent message by its public seed: with high probability the message does not depend on which sample was drawn.
--
--   **Formalization Note** The probability is that of the agreement set under the product of $D^m$, $D^m$ and the law of the coins.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.5, p.5 (PDF p.8)

import Mathlib
import Definitions.Def_DPVerify_RandAlg

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- `ρ`-replicability at the distribution `D` (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.5, p.5 = PDF p.8):
`Pr_{S, S′, r}[A(S, r) = A(S′, r)] ≥ 1 − ρ`, where `S, S′ ∼ D^m` are independent i.i.d. samples
and `r` is the internal randomness of `A`, shared by the two runs.

**Formalization Note** The probability is the product measure `D^m ⊗ D^m ⊗ P` of the agreement
set, in `ℝ≥0∞`. -/
def IsReplicableAt {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {m : ℕ}
    (A : RandAlg X Y m) (D : ProbabilityMeasure X) (ρ : ℝ) : Prop :=
  ENNReal.ofReal (1 - ρ) ≤
    ((Measure.pi fun _ : Fin m => (D : Measure X)).prod
        ((Measure.pi fun _ : Fin m => (D : Measure X)).prod A.P))
      {q | A.run q.1 q.2.2 = A.run q.2.1 q.2.2}

end DPVerify


