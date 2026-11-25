-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:51:32.701795+00:00
-- url     : https://prove2.me/theorems/9420e470-5dbe-4be6-8c8c-5c10feceb736
-- title:
--   Mem Span Bn
-- statement:
--   Definitions and structural lemmas for Mem Span Bn, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/MemSpanBn.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
def Bn (X : PT E) (n : ℕ) :
    Basis (Σ _ : Fin n, Fin (2 * Fintype.card (Idx X.dim))) ℝ (Fin n → Vsp X.dim) :=
  Pi.basis fun _ => X.b
instance volHaar (X : PT E) (n : ℕ) : (volume : Measure (Fin n → Vsp X.dim)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ => volume)
instance cntL (X : PT E) (n : ℕ) : Countable (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup :=
  inferInstanceAs (Countable (Submodule.span ℤ (Set.range (Bn X n))))
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries


