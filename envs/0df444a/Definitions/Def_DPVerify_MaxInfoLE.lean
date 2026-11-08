-- Prove2me | Definitions.Def_DPVerify_MaxInfoLE
-- name    : DPVerify_MaxInfoLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:11.719262+00:00
-- url     : https://prove2.me/theorems/0221ef0f-607a-4903-9197-0f650a58f488
-- title:
--   $\beta$-approximate max-information $I^\beta_\infty(S;\mathcal A(S))\le k$ for $S\sim D^m$
-- statement:
--   Let $\mathcal A:\mathcal X^m\to\mathcal Y$ be a randomized algorithm and $D$ a probability distribution on $\mathcal X$. Draw $S\sim D^m$ and run $\mathcal A$ on it. The **$\beta$-approximate max-information** between $S$ and $\mathcal A(S)$ is
--
--   $$
--   I^\beta_\infty(S;\mathcal A(S))=\log\sup_{O:\ \Pr[(S,\mathcal A(S))\in O]>\beta}\frac{\Pr[(S,\mathcal A(S))\in O]-\beta}{\Pr[S\otimes\mathcal A(S)\in O]},
--   $$
--
--   where $S\otimes\mathcal A(S)$ denotes a pair with the same two marginals drawn independently. The predicate states $I^\beta_\infty(S;\mathcal A(S))\le k$ in the equivalent form: for every measurable $O\subseteq\mathcal X^m\times\mathcal Y$,
--
--   $$
--   \Pr[(S,\mathcal A(S))\in O]\;\le\;e^{k}\,\Pr[S\otimes\mathcal A(S)\in O]+\beta .
--   $$
--
--   Max-information measures how much the output of an algorithm can reveal about its sample; Lemma 4.2 bounds it for differentially private algorithms and Lemma 4.3 turns the bound into one-way perfect generalization.
--
--   **Formalization Note** The two forms agree also when the product probability is $0$ and when no $O$ has joint probability above $\beta$. The logarithm is natural, matching $e^\varepsilon$ in Definitions 2.2 and 2.4. The sample is an i.i.d. sample $D^m$, the only case the paper uses (its $I^\beta_{\infty,P}$).
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.3, p.5 (PDF p.8)

import Mathlib
import Definitions.Def_DPVerify_RandAlg

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {m : ℕ}

/-- The joint law of `(S, A(S))` when `S ∼ D^m` and the coins of `A` are drawn independently. -/
noncomputable def jointLaw (A : RandAlg X Y m) (D : ProbabilityMeasure X) :
    Measure ((Fin m → X) × Y) :=
  ((Measure.pi fun _ : Fin m => (D : Measure X)).prod A.P).map fun q => (q.1, A.run q.1 q.2)

/-- The product `S ⊗ A(S)` of the two marginals of `jointLaw A D`: `D^m` times the output law
of `A(S)` averaged over `S ∼ D^m`. -/
noncomputable def productLaw (A : RandAlg X Y m) (D : ProbabilityMeasure X) :
    Measure ((Fin m → X) × Y) :=
  (Measure.pi fun _ : Fin m => (D : Measure X)).prod ((jointLaw A D).map Prod.snd)

/-- `I^β_∞(S; A(S)) ≤ k` for `S ∼ D^m`: the `β`-approximate max-information between the sample and
the output is at most `k` (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.3, p.5 = PDF p.8):
`I^β_∞(X; Z) = log sup_{O ⊆ X×Z, Pr[(X,Z) ∈ O] > β} (Pr[(X,Z) ∈ O] − β) / Pr[X ⊗ Z ∈ O]`.

**Formalization Note** `I^β_∞ ≤ k` is stated in its equivalent linear form: for every measurable
`O`, `Pr[(S, A(S)) ∈ O] ≤ e^k · Pr[S ⊗ A(S) ∈ O] + β`. The two agree also when
`Pr[S ⊗ A(S) ∈ O] = 0` (the ratio is `+∞` exactly when the joint mass exceeds `β`) and when no
`O` has joint mass above `β` (the supremum of the empty set gives `log 0 = −∞ ≤ k`). The
logarithm is natural, matching `e^ε` in Definitions 2.2 and 2.4. The distribution of the sample
is the product `D^m`, which is the only case Lemmas 4.2 and 4.3 use (the paper's
`I^β_{∞,P}`); `D` is a probability measure on an arbitrary measurable space. -/
def MaxInfoLE (A : RandAlg X Y m) (D : ProbabilityMeasure X) (β k : ℝ) : Prop :=
  ∀ O : Set ((Fin m → X) × Y), MeasurableSet O →
    jointLaw A D O ≤ ENNReal.ofReal (Real.exp k) * productLaw A D O + ENNReal.ofReal β

end DPVerify


