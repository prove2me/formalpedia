-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_CmapComp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_CmapComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:32.663927+00:00
-- url     : https://prove2.me/theorems/e082e162-6497-46d0-9854-78b85cf1adf8
-- title:
--   Cmap Comp
-- statement:
--   Definitions and structural lemmas for Cmap Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/CmapComp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
abbrev cmap {κ X A : Type} [AddCommGroup X] [CommRing A] (b : Module.Basis κ ℤ X) (v : κ → Aˣ) :
    Multiplicative X →* A :=
  (Units.coeHom A).comp (AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun k => Additive.ofMul (v k))).toAddMonoidHom)
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf


