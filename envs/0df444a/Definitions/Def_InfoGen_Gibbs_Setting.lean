-- Prove2me | Definitions.Def_InfoGen_Gibbs_Setting
-- name    : InfoGen_Gibbs_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:40.707596+00:00
-- url     : https://prove2.me/theorems/4d91a980-a1a8-438b-837c-4c9b803b530e
-- title:
--   The learning problem, Gibbs kernel, and relaxed objective (4), (26)–(27)
-- statement:
--   Let $\mathcal Z$ be the instance space, $\mathcal W$ the hypothesis space, $\mu$ the instance distribution, $S=(Z_1,\ldots,Z_n)$ an independent sample, and $\ell(w,z)$ a nonnegative loss. The population and empirical risks are $L_\mu(w)=\mathbb E_{Z\sim\mu}\ell(w,Z)$ and $L_S(w)=n^{-1}\sum_i\ell(w,Z_i)$. These two risk functions and the sample law are reused from the published learning setting.
--
--   For a learning kernel $P_{W|S}$, the expected generalization error is
--   $$\operatorname{gen}(\mu,P_{W|S})=\mathbb E_{(S,W)}[L_\mu(W)-L_S(W)].$$
--   Given a probability distribution $Q$ on $\mathcal W$ and $\beta>0$, the **Gibbs kernel** assigns to each sample $s$ the probability distribution
--   $$P^*_{W|S=s}(dw)=\frac{e^{-\beta L_s(w)}Q(dw)}{\mathbb E_Q[e^{-\beta L_s(W)}]}.$$
--   The **relaxed objective** of a learning kernel is
--   $$\mathbb E[L_S(W)]+\frac1\beta\int D(P_{W|S=s}\Vert Q)\,\mu^{\otimes n}(ds).$$
--   These definitions express the algorithm and the optimization problem of Theorem 5.
--
--   **Formalization Note** Samples have type `Fin n → Z`; a Markov kernel describes the randomized learner. The relaxed objective takes values in extended nonnegative reals, so an infinite KL cost remains infinite. The Gibbs kernel uses a joint density; the theorems require joint measurability of $\ell$, since the kernel construction returns zero on a nonmeasurable density. The density normalizes to one for the nonnegative loss and probability prior used in the results.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, §1 eqs. (1)–(4), p. 2; §4.3 eqs. (26)–(27), p. 6

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_InfoGen_Expected_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace InfoGen.Gibbs

open LearnStability.Characterization (sampleLaw risk empRisk)

/-- The Gibbs learning rule in (27), normalized separately at each sample. -/
noncomputable def gibbsKernel {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {n : ℕ} (ℓ : W → Z → ℝ) (Q : Measure W) [IsProbabilityMeasure Q] (β : ℝ) :
    Kernel (Fin n → Z) W :=
  Kernel.withDensity (Kernel.const (Fin n → Z) Q)
    (fun s w => ENNReal.ofReal
      (Real.exp (-β * empRisk ℓ s w) /
        ∫ w', Real.exp (-β * empRisk ℓ s w') ∂Q))

/-- The extended nonnegative objective in (26): expected empirical risk plus
`1/β` times conditional relative entropy. -/
noncomputable def relaxedObjective {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (ℓ : W → Z → ℝ) (μ : Measure Z) (Q : Measure W)
    (β : ℝ) {n : ℕ} (κ : Kernel (Fin n → Z) W) : ℝ≥0∞ :=
  ∫⁻ s, ((∫⁻ w, ENNReal.ofReal (empRisk ℓ s w) ∂(κ s)) +
    ENNReal.ofReal (1 / β) * klDiv (κ s) Q) ∂(sampleLaw μ n)

end InfoGen.Gibbs


