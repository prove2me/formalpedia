-- Prove2me | Definitions.Def_AgnHalfMem_AgnLearnsUnder
-- name    : AgnHalfMem_AgnLearnsUnder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:13:08.524684+00:00
-- url     : https://prove2.me/theorems/e5986dd5-a72b-4435-96d1-0669149e6f53
-- title:
--   Agnostic learning under a fixed marginal $\mu$
-- statement:
--   Let $\mu$ be a probability measure on $X$, $\mathcal G$ a class of classifiers and $\varepsilon\in\mathbb R$. A randomized streaming algorithm $A$ with seed law $P$ **agnostically learns $\mathcal G$ under marginal $\mu$ to excess error $\varepsilon$** if for every probability distribution $D$ on $X\times\{-1,1\}$ whose $X$-marginal is $\mu$,
--   $$
--   \Pr_{\omega\sim P,\ (x_t,y_t)\overset{\text{iid}}{\sim} D}\big[\mathrm{err}(f,D)\le \mathrm{OPT}_{\mathcal G}(D)+\varepsilon\big]\ \ge\ 0.9,
--   $$
--   where $f$ is the classifier output on the seed $\omega$ and the samples. The success probability is defined separately (`succProb`).
--
--   **Formalization Note** The success probability is the product measure $P\otimes D^{\otimes T}$ of the success set; for measurable algorithms that set is measurable. "With high probability" in Theorem 3.1 is this $0.9$.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §2, p.6

import Mathlib
import Definitions.Def_AgnHalfMem_err
import Definitions.Def_AgnHalfMem_StreamAlg

open MeasureTheory

namespace AgnHalfMem

/-- **Success probability of a streaming learner.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs
for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), §2, p.6. For a randomized algorithm `A` (seed law `P`), a distribution `D` on
`X × {−1, 1}`, a class `G` and an excess error `ε`, `succProb A P D G ε` is the probability, over
the seed and `T` i.i.d. samples from `D`, that the output `f` satisfies
`err(f, D) ≤ OPT_G(D) + ε`.

**Formalization Note.** The probability is the product measure `P ⊗ D^{⊗T}` of the success set.
Lean's measure of a set is its outer measure, which can only make the success probability larger;
for measurable algorithms (`IsMeasurableAlg`) the success set is measurable. -/
noncomputable def succProb {Ω S X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {T : ℕ}
    (A : StreamAlg Ω S X T) (P : Measure Ω) (D : Measure (X × Bool)) (G : Set (X → Bool))
    (ε : ℝ) : ENNReal :=
  (P.prod (Measure.pi fun _ : Fin T => D)) {q | err D ((A q.1).output q.2) ≤ opt D G + ε}

/-- **Agnostic learning under a marginal.** §2, p.6: "An algorithm agnostically learns H to excess
error ε if, for every distribution D, given i.i.d. samples from D, it outputs, with probability at
least 0.9, a function f : X → {−1, 1} satisfying err_D(f) ≤ OPT_H(D) + ε. When the marginal
distribution on X is fixed to be μ […] we refer to the resulting problem as agnostic learning under
marginal μ."

`AgnLearnsUnder μ G ε A P`: for every probability measure `D` on `X × Bool` whose `X`-marginal is
`μ`, the algorithm `A` with seed law `P` succeeds with probability at least `0.9`.

**Formalization Note.** Labels are `Bool` (`true ↔ +1`); "with high probability" in Theorem 3.1
is this `0.9`. -/
def AgnLearnsUnder {Ω S X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {T : ℕ}
    (μ : Measure X) (G : Set (X → Bool)) (ε : ℝ) (A : StreamAlg Ω S X T) (P : Measure Ω) : Prop :=
  ∀ D : Measure (X × Bool), IsProbabilityMeasure D → D.map Prod.fst = μ →
    ENNReal.ofReal (9 / 10) ≤ succProb A P D G ε

end AgnHalfMem


