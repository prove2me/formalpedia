-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
-- name    : OAI_Combinatorics_SharpThreshold_FourierDerivative
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:27:36.15858+00:00
-- url     : https://prove2.me/theorems/fa93020f-ba16-4210-95e2-601d6bc64abf
-- title:
--   The discrete derivative in one coordinate
-- statement:
--   For $g:\{0,1\}^\iota\to\mathbb{R}$ and a coordinate $i$, the discrete derivative is
--   $$
--   \Delta_ig(x)=g(x^{i\to1})-g(x^{i\to0}) .
--   $$
--   It does not depend on $x_i$, i.e. $\Delta_ig(x^{i\to b})=\Delta_ig(x)$, and consequently $\Delta_i\Delta_ig=0$.
--
--   In the biased Fourier basis $\Delta_i$ kills characters not containing $i$ and rescales those containing $i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierDerivative.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierDerivative.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex

namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313.BiasedFourier

variable {ι : Type u} [DecidableEq ι]

/-- The discrete derivative, retained as a function on the full cube. -/
def delta (i : ι) (g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  g (Function.update x i true) - g (Function.update x i false)

@[simp] theorem delta_update (i : ι) (g : (ι → Bool) → ℝ)
    (x : ι → Bool) (b : Bool) :
    delta i g (Function.update x i b) = delta i g x := by
  simp [delta, Function.update_idem]

@[simp] theorem delta_delta_fun (i : ι) (g : (ι → Bool) → ℝ) :
    delta i (delta i g) = 0 := by
  funext x
  simp [delta, Function.update_idem]

@[simp] theorem delta_delta (i : ι) (g : (ι → Bool) → ℝ) (x : ι → Bool) :
    delta i (delta i g) x = 0 := by simp [delta]

variable [Fintype ι]

end Problem313.BiasedFourier

end

end OAI


