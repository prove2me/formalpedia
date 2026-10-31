-- Prove2me | Definitions.Def_LevyExtrema_SBA_bgIndex
-- name    : LevyExtrema_SBA_bgIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:10.843901+00:00
-- url     : https://prove2.me/theorems/f8c6ba8f-1290-455d-99b4-530753440853
-- title:
--   Blumenthal–Getoor index $\beta=\inf\{p>0:I^p_0<\infty\}$
-- statement:
--   The **Blumenthal–Getoor index** of a Lévy process with Lévy measure $\nu$ is
--
--   $$\beta=\inf\{p>0 : I^p_0<\infty\},\qquad I^p_0=\int_{(-1,1)}|x|^p\,\nu(dx).$$
--
--   Since $I^2_0<\infty$ for every Lévy measure, $\beta\in[0,2]$. It measures the activity of the small jumps: $I^p_0<\infty$ for every $p>\beta$, while $I^\beta_0$ may be finite or infinite.
--
--   **Formalization Note** The infimum is the real `sInf`; for a Lévy triplet the set contains $2$ and is bounded below by $0$, so the value is the paper's $\beta$.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (4.5), p. 21

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Blumenthal–Getoor index β**, (4.5).
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (4.5), p. 21:
"β = inf{p > 0 : I^p_0 < ∞} … and note that β ∈ [0, 2] since I^2_0 < ∞".

**Formalization Note.** Real `sInf`. For a Lévy triplet (`Triplet.IsLevy`) the set contains 2 and
is bounded below by 0, so the infimum is the paper's β ∈ [0, 2]; the junk value of an empty set
cannot occur in any statement of the mission, all of which assume `Triplet.IsLevy`. -/
noncomputable def bgIndex (Tr : Triplet) : ℝ :=
  sInf {p : ℝ | 0 < p ∧ I0 Tr p < ⊤}

end LevyExtrema.SBA


