-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:45.605981+00:00
-- url     : https://prove2.me/theorems/c6d1bc52-3054-40b4-817a-6b2eed745310
-- title:
--   Be Sum Statement Iff Defect Sum Bound
-- statement:
--   Definitions and structural lemmas for Be Sum Statement Iff Defect Sum Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
namespace GlobalTheory.DefectSumCompare
section Galois
variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]
end Galois
end GlobalTheory.DefectSumCompare


