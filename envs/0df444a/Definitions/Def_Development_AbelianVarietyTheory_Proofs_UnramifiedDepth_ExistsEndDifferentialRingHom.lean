-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEndDifferentialRingHom
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEndDifferentialRingHom
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:34:07.222372+00:00
-- url     : https://prove2.me/theorems/8e6e1c0c-f3bb-5a81-a5cd-e1ddd9066185
-- title:
--   Exists End Differential Ring Hom
-- statement:
--   Definitions and structural lemmas for Exists End Differential Ring Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsEndDifferentialRingHom.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DualPairInh
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
variable {R₀ : Type} [CommRing R₀]
def endDiff_IsMat {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) (d : Matrix (Fin g) (Fin g) (O : Type)) : Prop :=
  ∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
    (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (d k l) * i) →
      e.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)
end GlobalTheory


