-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
-- name    : OAI_Combinatorics_SharpThreshold_InfluenceReindex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:15:35.056899+00:00
-- url     : https://prove2.me/theorems/72dec23d-52a4-441b-8fdb-7d098cc786f4
-- title:
--   Transporting Boolean functions along a bijection of coordinates
-- statement:
--   Let $e:\iota\simeq\kappa$ be a bijection of coordinate sets.
--
--   1. A configuration $x\in\{0,1\}^\iota$ is transported to $e_*x\in\{0,1\}^\kappa$, $(e_*x)_j=x_{e^{-1}(j)}$; this is a bijection of cubes with $(e_*x)_{e(i)}=x_i$.
--   2. For finite $\iota$, the $p$-biased weight and the pivotal influence of coordinate $i$ on $f$ are
--   $$
--   w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]},\qquad I_i^p(f)=\sum_xw_p(x)\bigl[f(x^{i\to1})\ne f(x^{i\to0})\bigr].
--   $$
--
--   These general-coordinate versions let graph statements be transported to arbitrary finite index sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/InfluenceReindex.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/InfluenceReindex.lean by skeleton subtraction
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

namespace OAI

universe u v

noncomputable section

namespace Problem313
namespace Reindex

variable {ι : Type u} {κ : Type v}

def config (e : ι ≃ κ) (x : ι → Bool) : κ → Bool := fun j => x (e.symm j)

def configEquiv (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun := config e
  invFun := config e.symm
  left_inv x := by ext i; simp [config]
  right_inv x := by ext i; simp [config]

@[simp] theorem config_apply (e : ι ≃ κ) (x : ι → Bool) (i : ι) :
    config e x (e i) = x i := by simp [config]

@[simp] theorem configEquiv_apply (e : ι ≃ κ) (x : ι → Bool) :
    configEquiv e x = config e x := rfl

def weight [Fintype ι] (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i = true then p else 1 - p

def influence [Fintype ι] (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ := by
  classical
  exact ∑ x, if f (Function.update x i true) ≠ f (Function.update x i false)
    then weight p x else 0

end Reindex
end Problem313

end

end OAI


