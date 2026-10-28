-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Algebra
-- name    : KLSModular_BrownianMotion_Auxiliary_Algebra
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:34:46.449436+00:00
-- url     : https://prove2.me/theorems/04959ec9-aef2-4820-b562-f262499c17bc
-- title:
--   Nonzero finite dimension under nontriviality
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931`, with a local Mathlib compatibility patch under Apache-2.0. `Module.finrank_ne_zero` states that the module rank over a domain is nonzero when the module is finite, torsion-free, and nontrivial; the bundle also registers the zero-dimensional simplification for subsingleton modules.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.LinearAlgebra.Dimension.Finite
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   @[simp]
--   lemma Module.finrank_ne_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
--       [StrongRankCondition R] [Module.Finite R M] [IsDomain R] [IsTorsionFree R M]
--       [h : Nontrivial M] :
--       finrank R M ≠ 0 := finrank_pos.ne'
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/Algebra.lean) · `BrownianMotion.Auxiliary.Algebra` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Algebra.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.Algebra`, definition bundle `KLSModular_BrownianMotion_Auxiliary_Algebra`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/Algebra.lean, lines 29-33). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.LinearAlgebra.Dimension.Finite

-- Modified by kls-lean for Lean/Mathlib v4.33.0; see formalization/vendor/port.patch.
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/Algebra.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
attribute [simp] Module.finrank_zero_of_subsingleton
@[simp]
lemma Module.finrank_ne_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [StrongRankCondition R] [Module.Finite R M] [IsDomain R] [IsTorsionFree R M]
    [h : Nontrivial M] :
    finrank R M ≠ 0 := finrank_pos.ne'
open Finset


