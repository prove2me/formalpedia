-- Prove2me | Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__ZarhinStatement_5859ff56c184faee
-- name    : P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__ZarhinStatement_5859ff56c184faee
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:45.563824+00:00
-- url     : https://prove2.me/theorems/77b8759b-fabf-4117-b263-b8b154b816f5
-- title:
--   Zarhin Statement
-- statement:
--   Definitions and structural lemmas for Zarhin Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/ZarhinStatement.lean

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
def ZarhinStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left),
      IsAbelianScheme A → L.IsLB → Out.RelAmple A L →
      ∃ (P : Out.PolAV (Spec (CommRingCat.of R))) (i : A ⟶ P.A) (r : P.A ⟶ A),
        IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 A
end GlobalTheory.CompanionTheory.Ar.GR


