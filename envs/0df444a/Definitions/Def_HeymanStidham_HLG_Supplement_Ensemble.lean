-- Prove2me | Definitions.Def_HeymanStidham_HLG_Supplement_Ensemble
-- name    : HeymanStidham_HLG_Supplement_Ensemble
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:13:25.459804+00:00
-- url     : https://prove2.me/theorems/aced3be9-ae53-4d17-a5c9-1f47b7a3fd71
-- title:
--   p. 987 — ensemble average of a sample-path average
-- statement:
--   For a real sample-path average $A(\omega)$ on a probability space $(\Omega,\mathcal F,P)$, its ensemble average is
--
--   $$\overline A=\int_\Omega A(\omega)\,dP.$$
--
--   This notation is used with the customer average $G(\omega)$ and the time average $H(\omega)$, exactly as on p. 987. Theorems 4 and 5 assert integrability of their chosen limit functions along with the identity $\overline H=\lambda\overline G$.
--
--   **Formalization Note** The real Bochner integral is used only with explicit integrability in the theorem conclusions. This definition alone does not assert that an arbitrary function is integrable.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), DOI 10.1287/opre.28.4.983, p. 987, definitions of ensemble averages; PDF p. 5

import Mathlib

namespace HeymanStidham.HLG.Supplement

open MeasureTheory

/-- The ensemble average of a sample-path average, p. 987.
Uses are accompanied by integrability, never the Bochner default. -/
noncomputable def ensembleAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Ω → ℝ) : ℝ := ∫ ω, A ω ∂P

end HeymanStidham.HLG.Supplement


