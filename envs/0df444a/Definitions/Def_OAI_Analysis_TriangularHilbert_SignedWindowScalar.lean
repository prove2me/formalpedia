-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
-- name    : OAI_Analysis_TriangularHilbert_SignedWindowScalar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:09:19.134069+00:00
-- url     : https://prove2.me/theorems/369d955e-45bf-4562-b1fe-262b86846c33
-- title:
--   Odd Gaussian window and its ratio to a wider Gaussian
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$.
--
--   1. **Odd window.** For a scale $s>0$, $\mathrm{oddWindow}(s,t)=\dfrac{t}{\sqrt s}\,\phi_s(t)$, an odd function of $t$ normalised so that it is scale invariant up to the Gaussian factor.
--   2. **Window ratio.** The odd window is compared with a Gaussian of slightly larger variance:
--   $$
--   \mathrm{windowRatio}(s,t)=\frac{\mathrm{oddWindow}(s,t)}{\phi_{11s/10}(t)} .
--   $$
--   This ratio is bounded in $t$, which lets odd windows be dominated by heat weights of variance $\frac{11}{10}s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SignedWindowScalar.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SignedWindowScalar.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def oddWindow (s t : ℝ) : ℝ := t / Real.sqrt s * density s t

def windowRatio (s t : ℝ) : ℝ := oddWindow s t / density ((11/10)*s) t

end
end TriangularHilbert.Heat
end

end OAI


