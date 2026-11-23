-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondProjSplitMulVec
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondProjSplitMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:24.604162+00:00
-- url     : https://prove2.me/theorems/92bd557c-47dc-4a46-8bc0-3c1706a8a0e7
-- title:
--   Second Proj Split Mul Vec
-- statement:
--   Definitions and structural lemmas for Second Proj Split Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondProjSplitMulVec.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace MassDataIdxSpl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Matrix
open scoped TensorProduct
section Uni
variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)
end Uni
end MassDataIdxSpl


