-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HopfPointMem
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HopfPointMem
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:04.352697+00:00
-- url     : https://prove2.me/theorems/38820b70-48d2-4e02-9a03-e861c7750039
-- title:
--   Hopf Point Mem
-- statement:
--   Definitions and structural lemmas for Hopf Point Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/HopfPointMem.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
theorem hopfPoint_mem {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [Unique N] (f : N → C) (hf : f ∈ L2.intFun (C := C) R N) :
    ∃ r : R, f = r • (1 : N → C) := by
  obtain ⟨r, hr⟩ := hf default
  refine ⟨r, funext fun x => ?_⟩
  rw [Subsingleton.elim x default, ← hr]
  simp [Algebra.smul_def]
theorem hopfPoint_one {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) : (1 : N → C) ∈ L2.intFun (C := C) R N := fun _ => ⟨1, by simp⟩
def hopfPoint {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [Unique N] :
    L2.HopfOrder (C := C) R N where
  carrier := L2.intFun R N
  lat := by
    refine ⟨1, by simp, le_antisymm ?_ ?_⟩
    · intro f hf
      obtain ⟨r, rfl⟩ := hopfPoint_mem R N f hf
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, ?_⟩)
      funext x
      rw [Subsingleton.elim x default]
      simp
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩ x
      refine ⟨1, ?_⟩
      rw [Subsingleton.elim x j]
      simp
  le_int := le_rfl
  one_mem := hopfPoint_one R N
  mul_mem := by
    intro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r * s, by simp [hr, hs]⟩
  comul := by
    intro f hf
    refine Submodule.subset_span ⟨f, hf, 1, hopfPoint_one R N, ?_⟩
    funext q
    change f (q.1 + q.2) = f q.1 * 1
    rw [_root_.mul_one, Subsingleton.elim (q.1 + q.2) q.1]
  antipode := fun f hf x => hf (-x)
end GlobalTheory.ChF


