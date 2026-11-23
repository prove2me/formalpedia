-- Prove2me | Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__QuotientByFiniteFlatStatement_f78b19e861f50157
-- name    : P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__QuotientByFiniteFlatStatement_f78b19e861f50157
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:02.807943+00:00
-- url     : https://prove2.me/theorems/54238c4b-a3e5-4cce-a39c-526c88483bc7
-- title:
--   Quotient By Finite Flat Statement
-- statement:
--   Definitions and structural lemmas for Quotient By Finite Flat Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/QuotientByFiniteFlatStatement.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsTight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_StepOrderRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.GR
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
def QuotientByFiniteFlatStatement : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left),
    IsAbelianScheme A → L.IsLB → Out.RelAmple A L →
    ∀ (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A), IsFinFlatSub A B h →
    ∃ (A' : Over (Spec (CommRingCat.of R))) (_ : GrpObj A') (L' : LB A'.left) (q : A ⟶ A'),
      IsAbelianScheme A' ∧ L'.IsLB ∧ Out.RelAmple A' L' ∧ IsMonHom q ∧
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
        z ≫ q = 1 ↔ ∃ φ : B →ₐ[R] S, spMap φ ≫ h = z
end GlobalTheory.CompanionTheory.Ar.GR


