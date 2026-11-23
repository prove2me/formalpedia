-- Prove2me | Definitions.Def_OTSensitivity_MaxFun_Supplement_Entropic
-- name    : OTSensitivity_MaxFun_Supplement_Entropic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:24:33.64945+00:00
-- url     : https://prove2.me/theorems/7c404cb9-f956-43b3-82d7-e2e55e09ef55
-- title:
--   Entropic OT functional $K_\varepsilon$ (8) and the entropic sensitivity measure $\xi^{K_\varepsilon}(Y,X|\mathcal F)$
-- statement:
--   Let $\mathsf Y$ be a measurable space, $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ a cost and $\varepsilon\ge0$. For measures $\nu,\nu'$ on $\mathsf Y$ the **entropic OT functional** of (8) is
--
--   $$K_\varepsilon(\nu,\nu')=\inf_{\pi\in\Pi(\nu,\nu')}\int\!\!\int k(y,y')\,d\pi(y,y')+\varepsilon\,\mathrm{KL}(\pi\,|\,\nu\times\nu'),$$
--
--   where $\Pi(\nu,\nu')$ is the set of probability measures $\pi$ on $\mathsf Y\times\mathsf Y$ with first marginal $\nu$ and second marginal $\nu'$, and $\mathrm{KL}(\pi|\vartheta)=\int\log\frac{d\pi}{d\vartheta}\,d\pi$ (7), with $\mathrm{KL}(\pi|\vartheta)=+\infty$ if $\pi$ is not absolutely continuous with respect to $\vartheta$. If $\Pi(\nu,\nu')$ is empty the infimum is $+\infty$. Setting $\varepsilon=0$ recovers the classical functional $K$ of (1).
--
--   Given random variables $X:\Omega\to\mathsf X$, $Y:\Omega\to\mathsf Y$ on $(\Omega,P)$ with laws $\mu$ and $\nu$, and a version $\kappa$ of the conditional distribution $(\nu^{\mathcal F}_x)_{x\in\mathsf X}$ of $Y$ given $(X,\mathcal F)$, the **entropic OT-based sensitivity measure** is
--
--   $$\xi^{K_\varepsilon}(Y,X|\mathcal F)=\int_{\mathsf X}K_\varepsilon(\nu,\nu^{\mathcal F}_x)\,d\mu(x)=\mathbb E\big[K_\varepsilon(P_Y,P^{\mathcal F}_{Y|X})\big],$$
--
--   Definition 1 with $K$ replaced by $K_\varepsilon$ (p. 11, (72) p. 38). With $\mathcal F=\mathcal B(\mathsf X)$ it is $\xi^{K_\varepsilon}(Y,X)$.
--
--   These are the objects of the paper's entropic results: Lemma 10, Theorem 11, and the entropic index (31) of Theorem 19.
--
--   **Formalization Note** Values are in `ℝ≥0∞` and $\varepsilon$ is in `ℝ≥0`; at $\varepsilon=0$ the convention $0\cdot\infty=0$ gives $K_0=K$ exactly. KL is Mathlib's `InformationTheory.klDiv`, which for probability measures equals (7), including the value $+\infty$. The couplings are those of the published `RWPI.SqrtLasso.transportCost`. `xiEps` takes the kernel $\kappa$ as an argument; the theorems quantify over every $\kappa$ satisfying `OTSensitivity.Info.IsCondDistrib`.
--
--   Differences from the source:
--   - generalization: (8) on probability laws on the Euclidean output support, with the standing cost regularity → the same formula on any measurable output space and any nonnegative extended-valued function; non-probability marginals have no admissible probability coupling and give +∞; reason: every source instance is retained; the theorems impose Polish/Borel structure, IsCost and probability laws where needed
--   - encoding: (7), (8), (16) and (72) → ℝ≥0∞ lower integrals, ε : ℝ≥0, klDiv relative to ν.prod ν′, and an explicit kernel argument for xiEps; reason: on admissible probability couplings Mathlib’s mass correction cancels and KL agrees with (7); nonintegrable positive entropy gives +∞, while 0·∞=0 gives K₀=K
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), (7) and (8), p. 5; Theorem 11, p. 11; (72), p. 38

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OTSensitivity.MaxFun.Supplement

/-- The entropic OT functional (8), p. 5:
`K_ε(ν, ν') = inf_{π ∈ Π(ν, ν')} ∫∫ k dπ + ε · KL(π | ν × ν')`, `ε ≥ 0`.
The infimum ranges over probability measures `π` on `𝒴 × 𝒴` with first marginal `ν` and second
marginal `ν'` (as in `RWPI.SqrtLasso.transportCost`); it is `⊤` when there is no such coupling.
`InformationTheory.klDiv` is `+∞` when `π` is not absolutely continuous w.r.t. `ν × ν'` (or the
log-likelihood ratio is not integrable), and for probability measures equals `∫ log(dπ/d(ν×ν')) dπ`
otherwise, which is (7). At `ε = 0`, `0 * ⊤ = 0`, so `K_0` is the classical functional (1). -/
noncomputable def entropicTransportCost {𝒴 : Type*} [MeasurableSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞)
    (ε : ℝ≥0) (ν ν' : Measure 𝒴) : ℝ≥0∞ :=
  ⨅ (π : Measure (𝒴 × 𝒴)) (_ : IsProbabilityMeasure π ∧ π.map Prod.fst = ν ∧ π.map Prod.snd = ν'),
    (∫⁻ w, k w.1 w.2 ∂π) + (ε : ℝ≥0∞) * InformationTheory.klDiv π (ν.prod ν')

/-- The entropic OT-based sensitivity measure `ξ^{K_ε}(Y, X | 𝓕) = ∫_𝒳 K_ε(ν, ν^𝓕_x) dµ(x)`
(p. 11, (72) p. 38): Definition 1 with `K` replaced by `K_ε`, computed from a version `κ` of the
conditional distribution of `Y`; `ν` is the law of `Y` and `µ` the law of `X`. -/
noncomputable def xiEps {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (ε : ℝ≥0) (P : Measure Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (κ : Kernel 𝒳 𝒴) :
    ℝ≥0∞ :=
  ∫⁻ x, entropicTransportCost k ε (P.map Y) (κ x) ∂(P.map X)

end OTSensitivity.MaxFun.Supplement


