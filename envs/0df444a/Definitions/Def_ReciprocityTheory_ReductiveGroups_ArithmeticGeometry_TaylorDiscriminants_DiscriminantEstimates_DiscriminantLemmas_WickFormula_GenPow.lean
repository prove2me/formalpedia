-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:03.396804+00:00
-- url     : https://prove2.me/theorems/49425d04-ca9f-47ed-a7f5-3a04efe81c19
-- title:
--   Gen Pow
-- statement:
--   Definitions and structural lemmas for Gen Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenPow.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace PI.WickFormula.Gen
section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
noncomputable abbrev pd (a : I ⊕ J) : Module.End K (MvPolynomial (I ⊕ J) K) :=
  (pderiv a).toLinearMap
end
section
variable {K I J : Type} [CommRing K] [Algebra ℚ K] [Fintype I] [Fintype J]
end
end PI.WickFormula.Gen


