-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Bound
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Bound
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:19:19.799737+00:00
-- url     : https://prove2.me/theorems/aa56646a-429f-4f7a-b76b-db51e21f5aa2
-- title:
--   Import context: KLS/BKL/Localization/Lyapunov/Bound
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Bound` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator`, `FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative`, `FunctionalInequalities.KLS.BKL.Localization.NoiseBound`, `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, `FunctionalInequalities.Probability.Diffusion.VectorGenerator`, `FunctionalInequalities.Probability.Diffusion.InverseCalculus`, `FunctionalInequalities.KLS.BKL.Localization.Energy.Generator`, `FunctionalInequalities.KLS.BKL.Localization.Energy.Bound`, `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic`, `FunctionalInequalities.KLS.BKL.Posterior.Covariance`, `FunctionalInequalities.KLS.BKL.Posterior.Regularity`, and `FunctionalInequalities.Probability.Diffusion.Generator`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator
--   import FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
--   import FunctionalInequalities.KLS.BKL.Localization.NoiseBound
--   import FunctionalInequalities.Analysis.Operator.HilbertSchmidt
--   import FunctionalInequalities.Probability.Diffusion.VectorGenerator
--   import FunctionalInequalities.Probability.Diffusion.InverseCalculus
--   import FunctionalInequalities.KLS.BKL.Localization.Energy.Generator
--   import FunctionalInequalities.KLS.BKL.Localization.Energy.Bound
--   import FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   import FunctionalInequalities.KLS.BKL.Posterior.Regularity
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/CovarianceGenerator`](https://prove2.me/theorems/7af1dbcb-be0a-4bda-96c4-e0b07cecb1c1), [`KLS/BKL/Localization/CumulantDerivative`](https://prove2.me/theorems/b075fb8a-3376-43d8-a3ac-d3bc2b12f9f8), [`KLS/BKL/Localization/NoiseBound`](https://prove2.me/theorems/f9dd651e-3cbd-4d7a-892b-a8785e460e72), [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34), [`Probability/Diffusion/VectorGenerator`](https://prove2.me/theorems/a27154a7-c41b-4d48-aa0c-9939263debb7), [`Probability/Diffusion/InverseCalculus`](https://prove2.me/theorems/c78d55be-9c73-46d5-85f1-1fc1bf677188), [`KLS/BKL/Localization/Energy/Generator`](https://prove2.me/theorems/736f8a3e-ae32-497a-8859-0c6fecc1a72e), [`KLS/BKL/Localization/Energy/Bound`](https://prove2.me/theorems/4ab05ed1-3d8d-48ff-a6a8-e41faa7f3068), [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa), [`KLS/BKL/Posterior/Regularity`](https://prove2.me/theorems/d3a1b3f7-aa50-410c-a659-85a6897688cc), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`sum_hsNormSq_conjugatedNoiseOperator_le`](https://prove2.me/theorems/9cbd62f1-3843-46f4-9c08-7b3b98e32302)
--   - [`generator_stdTrace_ringInverse_cov_le`](https://prove2.me/theorems/654de5d1-c780-4937-8de4-674da4bed607)
--   - [`sum_sq_fderiv_stdTrace_ringInverse_cov_noise_le`](https://prove2.me/theorems/b5070c35-02cf-4bfa-a4a7-cf8eb07675cc)
--   - [`exists_generator_lyapunov_le`](https://prove2.me/theorems/97e70d80-18de-4ef1-846f-10a392703228)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean) · `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Bound` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean#L1-L626 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Bound`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Bound`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_VectorGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_InverseCalculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Bound
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Regularity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator


