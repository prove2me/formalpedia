-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_WeightSeparation
-- name    : OAI_NumberTheory_PiExponent_Approximation_WeightSeparation
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:44:58.376277+00:00
-- url     : https://prove2.me/theorems/18191872-ab9e-4020-bab8-ad80da015219
-- title:
--   Geometric weights and separated growth
-- statement:
--   Let $w_0,v_0,\theta\in\mathbb{R}$, let $x:\mathbb{N}\to\mathbb{R}$, and let $i,m\in\mathbb{N}$. The degree weight is $w_0$ at index $0$ and $x(i)$ at every other index. The jet weight is $v_0$ at index $0$ and $x(i)/\theta$ at every other index. For $C,w_0,v_0,\theta\in\mathbb{R}$ and $m\in\mathbb{N}$, the separation factor is
--
--   $$
--   C\left(\max\left\{1,\frac{\max\{v_0,1/\theta\}}{\min\{w_0,1\}}\right\}\right)^{m+1}.
--   $$
--
--   Finally, $\mathrm{SeparatedWeightGrowth}(m,D,x)$ means that for every integer $i$ with $0<i\le m$,
--
--   $$
--   D\prod_{j=0}^{i-1}x(j)<x(i).
--   $$
--
--   These are four definitions: the two index-dependent weights, the separation factor, and the separated-growth predicate. They impose no positivity or existence hypotheses by themselves; such assumptions must be supplied where later results use them.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/WeightSeparation.lean#L14-L108

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring






namespace OAI

namespace PiExponentApprox

noncomputable section

def geometricDegreeWeight (w0 : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then w0 else x i

def geometricJetWeight (v0 theta : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then v0 else x i / theta

def weightSeparationFactor (m : ℕ) (C w0 v0 theta : ℝ) : ℝ :=
  C * (max 1 (max v0 (1 / theta) / min w0 1)) ^ (m + 1)





def SeparatedWeightGrowth (m : ℕ) (D : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ i, 0 < i → i ≤ m → D * (∏ j ∈ Finset.range i, x j) < x i



end
end PiExponentApprox

end OAI


