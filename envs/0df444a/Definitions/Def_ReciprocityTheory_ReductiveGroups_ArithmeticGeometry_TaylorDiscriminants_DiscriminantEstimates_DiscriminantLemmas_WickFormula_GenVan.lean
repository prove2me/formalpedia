-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:13.809474+00:00
-- url     : https://prove2.me/theorems/e1d6e2b6-fd42-4050-af38-9285eb052e7f
-- title:
--   Gen Van
-- statement:
--   Definitions and structural lemmas for Gen Van, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean

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
variable {K σ ι : Type} [CommRing K] [Fintype ι]
noncomputable def lowDeg (f : ι → σ) (t : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {m | ∑ i, m (f i) < t}
end
section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
end
end PI.WickFormula.Gen


