-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_Supplement_prefixLimits
-- name    : SampleCRS_AlmostGreedy_Supplement_prefixLimits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:36:06.963987+00:00
-- url     : https://prove2.me/theorems/50fd40ab-c1d1-49c1-ac82-8e74bb9d55e5
-- title:
--   Acceptance tails, their actual interpolation and the explicit h₂
-- statement:
--   For a capacity-$k$ online policy on a vector $p$, let $N_j$ count accepted elements in the first $j$ arrivals, $s_j=\sum_{i\le j}p_i$ and $H_{\ell,j}=E[(N_j-\ell+1)^+]$. Prefix zero has count and mass zero. For strictly positive coordinates, linearly interpolate the actual $H_{\ell,j}$ on the strictly increasing nodes $s_j$; the last node has its actual terminal value. Define $\delta=\max_i p_i$, with empty maximum zero.
--
--   With the operational adversarial optimum $\gamma=\gamma_{\rm adv}(k)$, put $t_2=(1-\gamma)/\gamma$ and
--   $$h_2(t)=\begin{cases}0&t\le t_2,\\\gamma(t-t_2-1+e^{-(t-t_2)})&t>t_2.\end{cases}$$
--   This is the explicit function (11), not an arbitrary ODE solution or an assumed terminal identity. The interpolation is used only on $[0,k]$ for positive coordinates of total mass $k$; it is defined by half-open segments and a separate terminal endpoint.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §5.2, equations (10)–(11), p.23

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_sampleModel

namespace SampleCRS.AlmostGreedy.Supplement

noncomputable def prefixMass {n : ℕ} (p : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i.val < j), p i

noncomputable def tailExpectation {n : ℕ} (k : ℕ) (π : OnlineKernel n)
    (p : Fin n → ℝ) (ell j : ℕ) : ℝ :=
  policyE k π p (fun D => max ((prefixCount D j : ℝ) - (ell : ℝ) + 1) 0)

/-- Piecewise affine interpolation on s_0,…,s_n. Strictly positive p makes
all denominators positive. Half-open intervals avoid double-counting nodes;
the last node is given its actual terminal value. -/
noncomputable def interpolateTail {n : ℕ} (k : ℕ) (π : OnlineKernel n)
    (p : Fin n → ℝ) (ell : ℕ) (t : ℝ) : ℝ :=
  if t = prefixMass p n then tailExpectation k π p ell n
  else ∑ i : Fin n, if prefixMass p i.val ≤ t ∧ t < prefixMass p (i.val + 1) then
    tailExpectation k π p ell i.val + (t - prefixMass p i.val) / p i *
      (tailExpectation k π p ell (i.val + 1) - tailExpectation k π p ell i.val)
    else 0

noncomputable def maxBias {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ((Finset.univ.sup (fun i => Real.toNNReal (p i)) : NNReal) : ℝ)

noncomputable def secondStart (k : ℕ) : ℝ := (1 - gammaAdv k) / gammaAdv k

/-- The explicit solution h_2 in (11), with the true operational optimum γ.
No ODE terminal condition or desired impossibility is assumed in defining γ. -/
noncomputable def hSecond (k : ℕ) (t : ℝ) : ℝ :=
  if t ≤ secondStart k then 0 else
    gammaAdv k * (t - secondStart k - 1 + Real.exp (-(t - secondStart k)))

end SampleCRS.AlmostGreedy.Supplement


