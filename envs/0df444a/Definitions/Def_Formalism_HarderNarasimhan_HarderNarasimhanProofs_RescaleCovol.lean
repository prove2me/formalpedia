-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:50.069016+00:00
-- url     : https://prove2.me/theorems/025fc023-4afd-4fe3-bb70-0176fe163720
-- title:
--   Rescale Covol
-- statement:
--   Definitions and structural lemmas for Rescale Covol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RescaleCovol.lean

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.HN
def rscMap {P ι : Type*} [Fintype P] [Fintype ι] (c : P → ℝ) :
    EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (P × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun p => (c p.1)⁻¹ • LinearMap.proj p) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (P × ι × Fin 2 → ℝ)).toLinearMap
section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
end
end Formalism.HN


