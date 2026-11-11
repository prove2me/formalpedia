-- Prove2me | Definitions.Def_ShuffleDecoys_Hierarchy_Info
-- name    : ShuffleDecoys_Hierarchy_Info
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:21:36.602348+00:00
-- url     : https://prove2.me/theorems/c38a8452-34ef-4f00-ace9-b06528bbfb87
-- title:
--   Discrete information measures in nats: mutual information (KL from the product of marginals), total variation, square-root distance, variance on ℤ
-- statement:
--   All laws are probability mass functions on an arbitrary type (so they are discrete, with countable support), and every logarithm is natural, so information is measured in **nats**.
--
--   For laws $p$ on $\alpha$ and $q$ on $\beta$, $p\otimes q$ (`prodPMF`) is the law of an independent pair. For a law $p$ on $\alpha$ and a channel $W:\alpha\to\Delta(\beta)$, `channelJoint p W` is the joint law of $(X,Y)$ with $X\sim p$ and $Y\mid X=a\sim W(a)$.
--
--   The **mutual information** of a joint law $J$ of $(X,Y)$ is the Kullback–Leibler divergence of $J$ from the product of its marginals,
--   $$I(X;Y)=D_{\mathrm{KL}}\big(J\,\big\|\,J_X\otimes J_Y\big)=\sum_{x,y}J(x,y)\log\frac{J(x,y)}{J_X(x)\,J_Y(y)}\in[0,\infty],$$
--   computed with Mathlib's `InformationTheory.klDiv` (natural logarithm) with every subset measurable.
--
--   The **total variation distance** is $D_{\mathrm{TV}}(p,q)=\tfrac12\sum_x|p(x)-q(x)|$, and the squared distance of square-root mass vectors is $\|\sqrt p-\sqrt q\|_2^2=\sum_x(\sqrt{p(x)}-\sqrt{q(x)})^2$.
--
--   For a law $S$ on $\mathbb Z$, `HasFiniteVar S` means $\sum_k S(k)k^2<\infty$; then `pmfMean S` $=\sum_k kS(k)$ and `pmfVar S` $=\sum_k S(k)(k-\text{mean})^2$ are the mean and the variance.
--
--   **Formalization Note.** Mutual information takes values in $[0,\infty]$, so it is never truncated; on the finite and countable spaces of this mission it agrees with the textbook sum (terms with $J(x,y)=0$ contribute $0$). The real series in `tvDist` and `sqrtDistSq` always converge; the mean and variance are meaningful under `HasFiniteVar`, which every statement using them assumes.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 9 (natural logarithms, nats), p. 16 (Lemma 3.1: D_TV, Var), p. 17 (Lemma 3.2: ‖√A − √B‖²₂), p. 26 (D_TV)

import Mathlib

open MeasureTheory InformationTheory
open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-!
# Discrete information measures (natural logarithm)

Su, Cheng, Wang, *The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model*,
STOC 2027 submission, p. 9 ("all logarithms are natural, and mutual information is measured in
nats"), p. 26 (total variation).

Every law here is a probability mass function (`PMF`) on an arbitrary type, so it is discrete
(countably supported). Divergences are computed with every subset measurable (`⊤`).
-/

/-- The product `p ⊗ q` of two probability mass functions: the law of `(X, Y)` with `X ∼ p` and
`Y ∼ q` independent. -/
noncomputable def prodPMF {α β : Type*} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

/-- The joint law of `(X, Y)` when `X ∼ p` and, given `X = a`, `Y ∼ W a` (a channel `W`). -/
noncomputable def channelJoint {α β : Type*} (p : PMF α) (W : α → PMF β) : PMF (α × β) :=
  p.bind fun a => (W a).map fun b => (a, b)

/-- Mutual information `I(X; Y)` **in nats** of a joint law `J` of `(X, Y)`: the
Kullback–Leibler divergence (Mathlib's `InformationTheory.klDiv`, natural logarithm) of `J` from
the product of its two marginals. Every subset is measurable. Values in `[0, ∞]`. -/
noncomputable def mutualInfo {α β : Type*} (J : PMF (α × β)) : ℝ≥0∞ :=
  letI : MeasurableSpace (α × β) := ⊤
  klDiv J.toMeasure (prodPMF (J.map Prod.fst) (J.map Prod.snd)).toMeasure

/-- Total variation distance `D_TV(p, q) = ½ Σₓ |p(x) − q(x)|` of two discrete laws. -/
noncomputable def tvDist {α : Type*} (p q : PMF α) : ℝ :=
  (1 / 2) * ∑' x, |(p x).toReal - (q x).toReal|

/-- Squared distance of square-root mass vectors `‖√p − √q‖₂² = Σₓ (√p(x) − √q(x))²`. -/
noncomputable def sqrtDistSq {α : Type*} (p q : PMF α) : ℝ :=
  ∑' x, (Real.sqrt (p x).toReal - Real.sqrt (q x).toReal) ^ 2

/-- An integer-valued law has finite variance: `Σₖ p(k) k² < ∞`. -/
def HasFiniteVar (S : PMF ℤ) : Prop :=
  Summable fun k : ℤ => (S k).toReal * (k : ℝ) ^ 2

/-- The mean `Σₖ k p(k)` of an integer-valued law (meaningful under `HasFiniteVar`). -/
noncomputable def pmfMean (S : PMF ℤ) : ℝ :=
  ∑' k : ℤ, (S k).toReal * (k : ℝ)

/-- The variance `Σₖ p(k) (k − mean)²` of an integer-valued law (meaningful under
`HasFiniteVar`). -/
noncomputable def pmfVar (S : PMF ℤ) : ℝ :=
  ∑' k : ℤ, (S k).toReal * ((k : ℝ) - pmfMean S) ^ 2

end ShuffleDecoys.Hierarchy


