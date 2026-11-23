-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LineHyperplaneCut
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LineHyperplaneCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:33.7708+00:00
-- url     : https://prove2.me/theorems/9e3010df-7259-4018-9c3b-a0d84c6b356f
-- title:
--   Line Hyperplane Cut
-- statement:
--   Definitions and structural lemmas for Line Hyperplane Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LineHyperplaneCut.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.EigenSplit
namespace GlobalTheory.EigenLine
variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]
noncomputable def twist (c : O →+* O) : K ⊗[ℤ] O →ₐ[ℤ] K ⊗[ℤ] O :=
  Algebra.TensorProduct.map (AlgHom.id ℤ K) c.toIntAlgHom
end GlobalTheory.EigenLine


