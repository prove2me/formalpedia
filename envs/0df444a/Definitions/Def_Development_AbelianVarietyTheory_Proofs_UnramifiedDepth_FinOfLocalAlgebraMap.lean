-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:56.982476+00:00
-- url     : https://prove2.me/theorems/c5a70e00-b513-5d37-be26-935aec415449
-- title:
--   Fin Of Local Algebra Map
-- statement:
--   Definitions and structural lemmas for Fin Of Local Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean

import Mathlib
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
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FinOf
lemma finOf_local_algebraMap {O Q : Type} [CommRing O] [CommRing Q] [IsLocalRing O]
    [IsLocalRing Q] [Algebra O Q] [Algebra.IsIntegral O Q] : IsLocalHom (algebraMap O Q) :=
  ((local_hom_TFAE (algebraMap O Q)).out 4 0).1
    (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal Q)))
variable {R₀ : Type} [CommRing R₀]
def finOf_fst (C : Type) [Field C] [Algebra R₀ C] :
    LHom (R₀ := R₀) ⟨DualNumber C⟩ ⟨C⟩ :=
  ⟨TrivSqZeroExt.fstHom R₀ C C, ⟨fun a h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩
section Split
variable (O : LAlg R₀) {A : Type} [CommRing A] [Algebra (O : Type) A] [Algebra R₀ A]
  [IsScalarTower R₀ (O : Type) A]
def finOf_sO [Module.Finite (O : Type) A] (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    LHom O ⟨A ⧸ I⟩ :=
  ⟨IsScalarTower.toAlgHom R₀ (O : Type) (A ⧸ I), finOf_local_algebraMap (O := O) (Q := A ⧸ I)⟩
end Split
end GlobalTheory.FinOf


