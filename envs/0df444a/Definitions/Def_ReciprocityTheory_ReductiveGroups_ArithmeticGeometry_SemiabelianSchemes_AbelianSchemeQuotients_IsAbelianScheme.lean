-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:18.973118+00:00
-- url     : https://prove2.me/theorems/e28d3c92-bfe5-45df-a720-4a7a002ceb3b
-- title:
--   Is Abelian Scheme
-- statement:
--   Definitions and structural lemmas for Is Abelian Scheme, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/AbelianSchemeQuotients/IsAbelianScheme.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
import Mathlib.AlgebraicGeometry.Morphisms.Proper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{u}}
class IsAbelianScheme (A : Over S) [GrpObj A] : Prop where
  comm : IsCommMonObj A
  smooth : Smooth A.hom
  proper : IsProper A.hom
  geomConnected : GeometricallyConnected A.hom
structure TorusExtension {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] where

  X : Type u
  [addCommGroup : AddCommGroup X]
  [free : Module.Free ℤ X]
  [finite : Module.Finite ℤ X]

  B : Over (Spec (.of K))
  [grpB : GrpObj B]
  isAbelian : IsAbelianScheme B

  q : G ⟶ B
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surjective : Surjective q.left
  q_quasiCompact : QuasiCompact q.left

  i : splitTorus (Spec (.of K)) X ⟶ G
  i_hom : IsMonHom i

  isKernel : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)
class IsSemiAbelian (G : Over S) [GrpObj G] : Prop where
  comm : IsCommMonObj G
  smooth : Smooth G.hom
  separated : IsSeparated G.hom
  quasiCompact : QuasiCompact G.hom
  geomConnected : GeometricallyConnected G.hom
  fibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
    Nonempty (TorusExtension ((Over.pullback p).obj G))
end ReciprocityTheory.ChartRestriction.G.Semi


