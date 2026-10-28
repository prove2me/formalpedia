-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:57:17.324225+00:00
-- url     : https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d
-- title:
--   Ball-truncated convex conjugate
-- statement:
--   For a real inner-product space $E$, a real function $u:E\to\mathbb{R}$, $M\in\mathbb{R}$, and $p\in E$, `truncatedConjugate u M p` is the supremum of $\langle p,x\rangle-u(x)$ over the closed ball $\{x:\|x\|\le M\}$. It is the finite-ball truncation used in the weak Caffarelli strict-convexity development, which also contains geometric comparison lemmas.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Alexandrov
--   import FunctionalInequalities.Analysis.Convex.Normalization
--   import FunctionalInequalities.Analysis.Convex.Subgradient
--   import Mathlib.Analysis.LocallyConvex.Separation
--   import Mathlib.Analysis.Convex.Extrema
--   import Mathlib.Analysis.Convex.Continuous
--   import FunctionalInequalities.Analysis.Convex.Coercivity
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def truncatedConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
--       (M : ℝ) (p : E) : ℝ :=
--     sSup ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905), [`Analysis/Convex/Normalization`](https://prove2.me/theorems/c20810ec-8464-4452-b023-bf292cc5b276), [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7), [`Analysis/Convex/Coercivity`](https://prove2.me/theorems/2ca7e523-4058-4fe5-bce8-76262b1a4a2d).
--
--   Theorems in source order:
--
--   - [`infDist_frontier_image_le_of_width`](https://prove2.me/theorems/942275ce-7a7e-445b-9191-6b35e86c5433)
--   - [`exists_compact_sections_subset_and_shrink`](https://prove2.me/theorems/e7f0ab2e-a85f-430a-8fd7-c28dea0e4a20)
--   - [`contact_stepA`](https://prove2.me/theorems/8b79d3f8-eb05-43a8-ba70-26607440bbcb)
--   - [`contactSet_eq_singleton_of_exposed_of_local_bounds`](https://prove2.me/theorems/b68b47d0-6adf-4db3-9250-a72ca18aaa5f)
--   - [`strictConvexOn_of_contact_eq`](https://prove2.me/theorems/6e139777-147e-446b-9423-99da9a6d9b75)
--   - [`subgradient_mem_interior_of_strictConvexOn`](https://prove2.me/theorems/a618a7d2-7d13-4aef-99ab-5b9c4a71d731)
--   - [`exists_exposed_contact_of_lt`](https://prove2.me/theorems/955fb26b-d452-446f-81e7-00212e58fa6b)
--   - [`exists_truncatedConjugate_eq`](https://prove2.me/theorems/c5409e58-60c1-4780-bcb8-119d240430ab)
--   - [`convexOn_truncatedConjugate`](https://prove2.me/theorems/8b13f81e-b6fb-4053-9362-bcc047017760)
--   - [`truncatedConjugate_centered_spec`](https://prove2.me/theorems/e5ce804e-84d7-49ea-8db6-f2b00ef88634)
--   - [`isOpen_setOf_truncatedConjugate_maximizer_lt`](https://prove2.me/theorems/88c71aef-4402-44f2-b3b2-345e8d21ce72)
--   - [`n7_subgradient_eq_maximizer`](https://prove2.me/theorems/7f300c00-6c7e-43ce-894b-43082cb54e74)
--   - [`subgradientImage_truncatedConjugate_eq`](https://prove2.me/theorems/e685fa4c-013a-44d7-b25b-31318e3dcf54)
--   - [`eq_of_two_contacts_below`](https://prove2.me/theorems/1bde12d1-3df1-4935-9ced-e218f57c79c3)
--   - [`eq_of_contact_of_sublevel_bounds`](https://prove2.me/theorems/5fba9dd0-6290-4810-ab52-5b74c100b270)
--   - [`strictConvexOn_of_map_gradient`](https://prove2.me/theorems/2ec0713b-027d-49b5-9ef0-008413f11729)
--   - [`contDiff_one_of_map_gradient`](https://prove2.me/theorems/0ffece2e-a383-4c75-b592-04da65ab3fa7)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean) · `FunctionalInequalities.Analysis.Convex.Caffarelli` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1279-L1284 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Continuous
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Coercivity

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F2TruncatedConjugate
open Set Metric
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
/-- The **ball-truncated conjugate** `p ↦ sup_{‖x‖ ≤ M} (⟪p, x⟫ − u x)` (weak Letwin route;
KLS500 `truncatedLegendrePotential`): a globally finite convex function that agrees with the Legendre
transform of `u` wherever the supremum is attained inside the ball. -/
def truncatedConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
    (M : ℝ) (p : E) : ℝ :=
  sSup ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M)
end Analysis
end FunctionalInequalities
end LT11F2TruncatedConjugate


