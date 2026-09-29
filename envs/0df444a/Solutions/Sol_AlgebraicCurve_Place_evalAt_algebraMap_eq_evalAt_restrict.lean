-- Prove2me | solution 1 for AlgebraicCurve.Place.evalAt_algebraMap_eq_evalAt_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/34f7e905-6f1b-53db-bde9-3410a12409d1

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict

open IsLocalRing AlgebraicCurve AlgebraicCurve.Place

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') (hv : (w.restrict F).IsRational) {g : F} (hg : g ∈ (w.restrict F).toValuationSubring) : w.evalAt (algebraMap F F' g) = (w.restrict F).evalAt g := by
  have hg' : algebraMap F F' g ∈ w.toValuationSubring := ValuationSubring.mem_comap.mp hg
  have h2 : residue w.toValuationSubring (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring)
      = algebraMap K w.ResidueField ((w.restrict F).evalAt g) := by
    have h3 : (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring)
        = restrictInclusion F w ⟨g, hg⟩ := rfl
    rw [h3, ← restrictResidueMap_residue, ((w.restrict F).algebraMap_evalAt hv hg).symm]
    show restrictResidueMap F w
        (residue _ (algebraMap K (w.restrict F).toValuationSubring ((w.restrict F).evalAt g)))
      = residue _ (algebraMap K w.toValuationSubring ((w.restrict F).evalAt g))
    rw [restrictResidueMap_residue]
    refine congrArg _ (Subtype.ext ?_)
    show algebraMap F F' (algebraMap K F ((w.restrict F).evalAt g))
        = algebraMap K F' ((w.restrict F).evalAt g)
    rw [← IsScalarTower.algebraMap_apply]
  rw [w.evalAt_of_mem hg', h2, w.residueInv_algebraMap]

end S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
end P2MW
export P2MW.S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict (solution)
