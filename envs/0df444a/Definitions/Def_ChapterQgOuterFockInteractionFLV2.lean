-- Prove2me | Definitions.Def_ChapterQgOuterFockInteractionFLV2
-- name    : ChapterQgOuterFockInteractionFLV2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-02T20:18:07.727442+00:00
-- url     : https://prove2.me/theorems/7e1bfeb0-c618-4e52-9468-4d67b924cfa3
-- title:
--   Chapter QgOuterFockInteractionFL V2
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgOuterFockInteractionFL.lean`): the `QgFamily` Faris-Lavine relative bound `secExt_rel` carved out of ChapterQgOuterFockInteractionFL under the §2.13 new-name route, since the platform's served copy stops at `secExt` and submit-definition cannot update an existing name. See BookProof/ChapterQgOuterFockInteractionFL.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockInteractionFL.lean

-- Generated from ChapterQgOuterFockInteractionFL.lean — the `QgFamily`
-- relative-bound layer that the platform's served ChapterQgOuterFockInteractionFL
-- copy predates (§2.13 new-name route: submit-definition rejects an existing
-- name, so the decl lives here instead).  The served bundle stops at
-- `secExt`; `secExt_rel` is the Faris–Lavine relative bound the two
-- `esa_farisLavine` statements project as `F.secExt_rel`.
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_norm_le
import Mathlib

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

namespace BookProof.QgOuterFockInteractionFL

namespace QgFamily

variable (F : QgFamily)

/-- **The Faris–Lavine relative bound of the sector extension.**  The lifted
`n`-particle Hamiltonian `secExt n` is relatively bounded by the sector
comparison operator `harmFried (n * 84)` with the family's uniform constant
`flK` -- uniformly in `n`, which is exactly the input the `ℓ²`-direct-sum
Faris–Lavine theorem needs.  Inherited from the `CoreData` of the sector,
whose `rel` field is `secHam_norm_le`. -/
theorem secExt_rel : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
    ‖F.secExt n u‖ ≤ F.flK * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖ :=
  fun n u => (F.secData n).ext_norm_le u

end QgFamily

end BookProof.QgOuterFockInteractionFL


