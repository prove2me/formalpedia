-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass
-- name    : KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:57:52.12738+00:00
-- url     : https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f
-- title:
--   Import context: Probability/MomentMeasure/ConjugateMass
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Convex.AffineMaximum` and `FunctionalInequalities.Probability.MomentMeasure.Basic`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Constructions.HaarToSphere`, `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, `Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence`, `Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp`, `Mathlib.Topology.Instances.EReal.Lemmas`, and `Mathlib.Topology.Order.LiminfLimsup`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.AffineMaximum
--   import FunctionalInequalities.Probability.MomentMeasure.Basic
--   import Mathlib.MeasureTheory.Constructions.HaarToSphere
--   import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
--   import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
--   import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
--   import Mathlib.Topology.Instances.EReal.Lemmas
--   import Mathlib.Topology.Order.LiminfLimsup
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/AffineMaximum`](https://prove2.me/theorems/6ce50813-8eec-46a5-abb0-e806e1385307), [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c).
--
--   Theorems in source order:
--
--   - [`integrable_exp_sub_norm`](https://prove2.me/theorems/6e84bf56-c441-4d85-881f-7cdd5b15ecb5)
--   - [`limsup_density_legendre_le`](https://prove2.me/theorems/50c36fd7-1bb7-40be-8a5b-91f04f40fa30)
--   - [`exists_integrable_exponential_domination`](https://prove2.me/theorems/0002089c-2c4b-4c6b-8010-16b85c45339e)
--   - [`limsup_mass_legendre_le`](https://prove2.me/theorems/a6e9fd8e-5a77-41be-9761-9a4957084c5b)
--   - [`log_sub_ge_of_integral_limits`](https://prove2.me/theorems/8c2c9203-7701-486b-b236-68a42ba9b8b5)
--   - [`real_legendre_normalization`](https://prove2.me/theorems/c3394fe1-6941-4e93-a4a1-c77d84338af6)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean) · `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L1-L308 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, import-context bundle `KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup


