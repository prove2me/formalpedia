-- Prove2me | Definitions.Def_MemoSDPI_Main_SDPI
-- name    : MemoSDPI_Main_SDPI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:41:20.906231+00:00
-- url     : https://prove2.me/theorems/c7d704ca-5e79-4f59-9903-1d4987f85064
-- title:
--   Strong data processing inequality (η-SDPI) of a jointly distributed pair
-- statement:
--   Let $(V, W)$ be a pair of jointly distributed random variables with joint law $\mu$ on $V \times W$, and let $\eta \in [0,1]$. The pair **satisfies an $\eta$-SDPI** (strong data processing inequality) if every Markov chain $V \to W \to U$ satisfies
--   $$
--   I(U; V) \;\le\; \eta\, I(U; W),
--   $$
--   where $I$ is mutual information in nats. A Markov chain $V \to W \to U$ means that $U$ is produced from $W$ alone, with randomness independent of $(V, W)$.
--
--   Ordinary data processing gives $I(U;V) \le I(U;W)$, i.e. a $1$-SDPI for every pair; an $\eta$-SDPI with $\eta < 1$ quantifies a strict loss of information. The paper applies it to the pair (parameter, sample) of an average-case problem to lower-bound excess memorization (Proposition 2.3).
--
--   **Formalization Note** The pair is given by its joint law `μ : Measure (V × W)`. The output $U$ ranges over every Markov kernel $\kappa$ from $W$ into every measurable space `U : Type`, and the joint law of $((V,W),U)$ is $\mu \otimes \kappa(\cdot \mid w)$. Mutual information is the published `ThompsonTutorial.InfoRatio.mutualInfo` (relative entropy of the joint law from the product of marginals, in $[0,\infty]$), and $\eta$ enters through `ENNReal.ofReal`. The range $\eta \in [0,1]$ is a hypothesis of the theorems that use the predicate.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 9, Definition 2.1

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- **η-SDPI of a pair** (Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and
Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript
sha256 dbb300da…), p. 9, Definition 2.1). A pair `(V, W)` with joint law `μ` satisfies an
`η`-SDPI if every Markov chain `V → W → U` satisfies `I(U; V) ≤ η · I(U; W)`.

**Formalization Note.** The pair is given by its joint law `μ` on `V × W`; the definition is a
property of that law. A Markov chain `V → W → U` is an output `U` generated from `W` alone by an
arbitrary Markov kernel `κ : W → U` into an arbitrary measurable space `U : Type`, so the joint
law of `((V, W), U)` is `μ ⊗ₘ (κ ∘ snd)`. Mutual information is the published
`ThompsonTutorial.InfoRatio.mutualInfo` (relative entropy of the joint law from the product of
the marginals, in nats, valued in `ℝ≥0∞`), and `η` enters as `ENNReal.ofReal η`. The paper takes
`η ∈ [0, 1]`; the range is a hypothesis of the theorems that use the predicate. -/
def SatisfiesSDPI {V W : Type} [MeasurableSpace V] [MeasurableSpace W]
    (μ : Measure (V × W)) (η : ℝ) : Prop :=
  ∀ (U : Type) [MeasurableSpace U] (κ : Kernel W U), IsMarkovKernel κ →
    ThompsonTutorial.InfoRatio.mutualInfo (μ ⊗ₘ Kernel.prodMkLeft V κ)
        (fun p => p.2) (fun p => p.1.1) ≤
      ENNReal.ofReal η *
        ThompsonTutorial.InfoRatio.mutualInfo (μ ⊗ₘ Kernel.prodMkLeft V κ)
          (fun p => p.2) (fun p => p.1.2)

end MemoSDPI.Main


