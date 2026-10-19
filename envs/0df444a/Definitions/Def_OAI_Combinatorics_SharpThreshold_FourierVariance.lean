-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
-- name    : OAI_Combinatorics_SharpThreshold_FourierVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:25:37.37868+00:00
-- url     : https://prove2.me/theorems/bcb03a85-a5b0-4ae8-a867-0898f6aeefd7
-- title:
--   The empty Fourier coefficient is the mean
-- statement:
--   Let $\iota$ be a finite set of coordinates and $p\in\mathbb{R}$. A point of the cube is $x\in\{0,1\}^\iota$, with $p$-biased weight $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$. For any $g$,
--   $$
--   \hat g(\emptyset)=\sum_xw_p(x)\,g(x) .
--   $$
--   For graph configurations the Fourier weight agrees with the graph weight, so for a graph property $f$ the empty coefficient of $[f]$ is $\mu_p(f)$, the probability that $f$ holds.
--
--   The variance of $f$ is then the Fourier mass on nonempty sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierVariance.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierVariance.lean by skeleton subtraction
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

namespace OAI

universe u v

noncomputable section

open scoped BigOperators Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

@[simp] theorem coeff_empty (p : ℝ) (g : (ι → Bool) → ℝ) :
    coeff p g ∅ = ∑ x, weight p x * g x := by
  classical
  simp [coeff]

end Problem313.BiasedFourier

namespace Problem313

open BiasedFourier

@[simp] theorem fourier_weight_eq_graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) :
    BiasedFourier.weight p x = graphWeight p x := rfl

@[simp] theorem fourier_coeff_empty_eq_graphMean {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool) :
    coeff p (fun x => boolReal (f x)) ∅ = graphMean p f := by
  rw [coeff_empty]
  unfold graphMean
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  rw [fourier_weight_eq_graphWeight]

end Problem313

end

end OAI


