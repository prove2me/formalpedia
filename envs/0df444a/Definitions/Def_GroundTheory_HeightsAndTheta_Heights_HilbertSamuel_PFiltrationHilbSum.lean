-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:00.641035+00:00
-- url     : https://prove2.me/theorems/e3405f22-22f5-4aed-9514-deed248cd0ef
-- title:
--   PFiltration Hilb Sum
-- statement:
--   Definitions and structural lemmas for PFiltration Hilb Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
namespace FiltrationHilbSum
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
def comp [DirectSum.Decomposition piece] (m : K → ℤ) : M →ₗ[F] M :=
  (piece m).subtype ∘ₗ DirectSum.component F (K → ℤ) (fun i => piece i) m ∘ₗ
    (DirectSum.decomposeLinearEquiv piece).toLinearMap
end FiltrationHilbSum
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


