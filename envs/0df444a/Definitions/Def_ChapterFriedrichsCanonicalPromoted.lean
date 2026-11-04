-- Prove2me | Definitions.Def_ChapterFriedrichsCanonicalPromoted
-- name    : ChapterFriedrichsCanonicalPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-03T12:25:35.905236+00:00
-- url     : https://prove2.me/theorems/94db7a61-aa2f-423b-ac7e-9496d9eab51a
-- title:
--   The Friedrichs extension is canonical: the promoted facts
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFriedrichsCanonical.lean`): `resolvent_mem_friedrichsDomain` (the form resolvent lands in the Friedrichs domain, the term proof the `friedrichsOp_resolvent` statement carries) and `qgScalaronPosSymOp_dense` (the Gauss-polynomial core is dense, the hypothesis the quantum-gravity `friedrichs_canonical` / `friedrichs_unique` statements need), carved out of ChapterFriedrichsCanonical under the §2.13 new-name route because the served copy predates both. Consumers add a single `import Definitions.Def_ChapterFriedrichsCanonicalPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsCanonical.lean

-- Generated from ChapterFriedrichsCanonical.lean — two facts that the platform's
-- served ChapterFriedrichsCanonical copy predates (§2.13 new-name route:
-- submit-definition rejects an existing name, so the decls live here instead).
-- `resolvent_mem_friedrichsDomain` is the term proof the `friedrichsOp_resolvent`
-- statement carries as `⟨u, resolvent_mem_friedrichsDomain P u⟩`;
-- `qgScalaronPosSymOp_dense` the density hypothesis `friedrichs_canonical` /
-- `friedrichs_unique` need for the quantum-gravity instance.
import Definitions.Def_ChapterFriedrichsCanonical
import Mathlib

namespace BookProof.FriedrichsCanonical

open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The form resolvent lands in the Friedrichs domain, by construction. -/
theorem resolvent_mem_friedrichsDomain (P : PosSymOp F) (u : F) :
    friedrichsResolvent P u ∈ friedrichsDomain P := ⟨u, rfl⟩

open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.HermiteProductCore

/-- The Gauss–polynomial core is dense, so the scalaron operator has dense domain. -/
theorem qgScalaronPosSymOp_dense (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    Dense (((qgScalaronPosSymOp M alpha hM halpha).dom : Submodule ℂ (L2d 1)) : Set (L2d 1)) :=
  polyGaussCore_dense

end

end BookProof.FriedrichsCanonical


