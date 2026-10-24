-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
-- name    : KLS408915f_BrownianMotion_Auxiliary_Algebra
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:05:26.769929+00:00
-- url     : https://prove2.me/theorems/07a5099d-98d7-4502-973c-79f4dcdc1903
-- title:
--   Nonzero finite dimension under nontriviality
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931`, with a local Mathlib compatibility patch under Apache-2.0. `Module.finrank_ne_zero` states that the module rank over a domain is nonzero when the module is finite, torsion-free, and nontrivial; the bundle also registers the zero-dimensional simplification for subsingleton modules.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Algebra.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.Algebra`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_Algebra`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/Algebra.lean, lines 29-33). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

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


