-- Prove2me | Definitions.Def_TiltedCvx_classMono
-- name    : TiltedCvx_classMono
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:38.470307+00:00
-- url     : https://prove2.me/theorems/c96a794f-1b3d-4631-bc3b-7ca62eb18bf8
-- title:
--   The class $\mathcal F^\gamma_{\mathrm{mono}}$
-- statement:
--   For $\gamma\in[0,1]$, $\mathcal F^\gamma_{\mathrm{mono}}$ consists of the proper lsc functions $f:\mathbb R^d\to\overline{\mathbb R}$ whose Clarke–Rockafellar subdifferential $\bar\partial f$ is $\gamma$–tilted monotone.
--
--   **Formalization Note** $\bar\partial f$ is the published `ClarkeStrat.Proj.ClarkeSubdiff`.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 5, p.14

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedMonotone
import Definitions.Def_ClarkeStrat_Proj_Setting

open ClarkeStrat.Proj

namespace TiltedCvx

/-- **The class `F^γ_mono`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Definition 5,
p.14: for `γ ∈ [0, 1]`, `F^γ_mono` consists of the proper lsc functions `f : ℝ^d → ℝ̄` such that
the Clarke subdifferential `∂̄f` is γ–tilted monotone.

**Formalization Note** `∂̄f` is the published `ClarkeStrat.Proj.ClarkeSubdiff`. -/
def classMono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (γ : ℝ) :
    Set (E → EReal) :=
  {f | IsProper f ∧ LowerSemicontinuous f ∧ TiltedMonotone γ (ClarkeSubdiff f)}

end TiltedCvx


