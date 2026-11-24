-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T19:46:00.453916+00:00
-- url     : https://prove2.me/theorems/2bae9bb2-f9ce-4bed-9306-0dc522d6e8b0
-- title:
--   Exists Weak Neron Model
-- statement:
--   Definitions and structural lemmas for Exists Weak Neron Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeakNeronModel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
section Ev
variable {X : Scheme.{0}} {L : Type} [Field L] (a : Sp L ⟶ X)
def ev (W : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ W) : Γ(X, W) →+* L :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp (a.appLE W ⊤ h).hom
end Ev
section Alg
variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {D : Type} [CommRing D] [Algebra K D] [Algebra R D] [IsScalarTower R K D]
def gen (B : Subalgebra R D) : TensorProduct R K B →ₐ[K] D :=
  Algebra.TensorProduct.lift (Algebra.ofId K D) B.val (fun _ _ => Commute.all _ _)
end Alg
end GlobalTheory.SS.WeakNeronEx
end


