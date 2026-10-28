-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:15:47.450555+00:00
-- url     : https://prove2.me/theorems/99978ac0-75f0-4e2a-93f1-fae71240d06b
-- title:
--   Permutation action on tensor fields
-- statement:
--   For a tensor field `u : Field ν k` and a permutation $σ$ of `Fin k`, `permField σ u` is the field with component at $I$ equal to $u(I\circ σ)$. The declared simp results state that this action has the displayed component formula and that the identity permutation acts trivially; the module also contains the combinatorial symmetrization bound for adjacent transpositions.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.PoissonIterate.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   @[simp] theorem permField_apply (σ : Equiv.Perm (Fin k)) (u : Field ν k)
--       (I : Fin k → Fin (Module.finrank ℝ V)) : permField σ u I = u (I ∘ σ) := rfl
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375).
--
--   Theorems in source order:
--
--   - [`sqrt_normSq_sub_permField_le_of_adjacent`](https://prove2.me/theorems/584de1b3-b865-446f-97d5-352cf6522404)
--   - [`normSq_sub_symField_le`](https://prove2.me/theorems/76359b53-6bf9-43ab-bb7a-bc9a40372a88)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Permutation.lean) · `FunctionalInequalities.KLS.BKL.PoissonIterate.Permutation` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Permutation.lean#L59-L63 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Permutation`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Tensor
open scoped Classical
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace PoissonIterate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : ProbabilityMeasure V} {k : ℕ}
@[simp] theorem permField_apply (σ : Equiv.Perm (Fin k)) (u : Field ν k)
    (I : Fin k → Fin (Module.finrank ℝ V)) : permField σ u I = u (I ∘ σ) := rfl
/-- The identity permutation acts trivially. -/
@[simp] theorem permField_one (u : Field ν k) : permField 1 u = u := rfl
end PoissonIterate
end LogConcave
end KLS
end FunctionalInequalities


