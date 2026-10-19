-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
-- name    : OAI_Combinatorics_SharpThreshold_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:01:54.78468+00:00
-- url     : https://prove2.me/theorems/ca4833f4-76a7-4778-a014-3e8dc36a8b8b
-- title:
--   Variance and edge influences of a graph property
-- statement:
--   Fix $n$. An edge is a $2$-element subset of $\{0,\dots,n-1\}$, and a configuration $x$ assigns true or false to every edge, i.e. it is a graph on $n$ labelled vertices. Under the $p$-biased product measure each edge is present independently with probability $p$, so $x$ has weight $w_p(x)=\prod_ep^{[x_e]}(1-p)^{1-[x_e]}$, and $\mu_p(f)=\sum_xw_p(x)[f(x)]$ is the probability that a property $f$ holds. For a graph property $f$:
--
--   1. Its variance is $\mathrm{Var}_p(f)=\sum_xw_p(x)\bigl([f(x)]-\mu_p(f)\bigr)^2$.
--   2. The influence of an edge $e$ is the probability that $e$ is pivotal,
--   $$
--   I_e^p(f)=\sum_x w_p(x)\,\bigl[f(x^{e\to1})\ne f(x^{e\to0})\bigr],
--   $$
--      where $x^{e\to b}$ sets edge $e$ to $b$.
--   3. The total influence is $I^p(f)=\sum_eI_e^p(f)$.
--
--   By Russo's formula the total influence is the derivative of $\mu_p(f)$ in $p$. Large total influence therefore forces a narrow threshold window.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold

namespace OAI

noncomputable section

namespace Problem313

def graphVariance {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) : ℝ := by
  classical
  exact Finset.univ.sum (fun x : GraphConfig n =>
    graphWeight p x * (boolReal (f x) - graphMean p f) ^ 2)

def edgeInfluence {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (e : GraphEdge n) : ℝ := by
  classical
  exact Finset.univ.sum (fun x : GraphConfig n =>
    if f (Function.update x e true) ≠ f (Function.update x e false)
    then graphWeight p x else 0)

def totalInfluence {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) : ℝ := by
  classical
  exact Finset.univ.sum (fun e : GraphEdge n => edgeInfluence p f e)

end Problem313

end

end OAI


