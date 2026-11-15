-- Prove2me | Definitions.Def_Transport_PhysicalHigh_EnergyMesh
-- name    : Transport_PhysicalHigh_EnergyMesh
-- status  : Definition
-- author  : @Himan
-- created : 2026-11-15T03:23:16.494398+00:00
-- url     : https://prove2.me/theorems/1ebd0d11-cd0f-4fb2-85e4-d2533cdfc4af
-- title:
--   The plain energy mesh $\mathrm{plainMesh}(\varepsilon)$ of the tuned high-side argument
-- statement:
--   This file defines the mesh size that bounds the slot lengths in the high-side moment argument of LW56e2's refinement of OpenAI's $7/8$ zero-free half-plane.
--
--   OpenAI's centered-moment energy induction comes with a width schedule: for a moment degree parameter $M$, a base $B$, an initial range $L$, a contraction $\kappa$ and an error $\varepsilon$, the source defines a fine mesh $\operatorname{fineMesh}(M,B,L,\kappa,\varepsilon)>0$, the mesh attached to the final source cap of the schedule. The plain mesh specializes this to the parameters used for plain (unmarked) moments:
--   $$
--   \operatorname{plainMesh}(\varepsilon)=\operatorname{fineMesh}\big(2,\,0,\,1,\,\tfrac34,\,\tfrac{\varepsilon}{4}\big).
--   $$
--
--   Its role is purely as an upper bound: the tuned slot lengths are required to be at most $\operatorname{plainMesh}(t)/200$ for the reserved loss $t$, so that the energy mesh is fixed before the number of slots is chosen.
--
--   **Formalization Note** `fineMesh` is `OAI.SevenEighths.CenteredMomentEnergyWidthRanges.fineMesh` from the platform bundle `OAIHecke78B026`. The definition is transcribed verbatim from the source; the positivity lemma `plainMesh_pos` of the source file is not part of this definition file.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/EnergyMesh.lean, def plainMesh (L8): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/EnergyMesh.lean#L8

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

set_option autoImplicit false

namespace RH.Transport.PhysicalHigh
noncomputable section
open OAI OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

def plainMesh (εm:ℝ):ℝ:=fineMesh 2 0 1 (3/4) (εm/4)

end
end RH.Transport.PhysicalHigh


