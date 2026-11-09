-- Prove2me | Definitions.Def_TranspositionIID_Main_Auxiliary
-- name    : TranspositionIID_Main_Auxiliary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:42.411022+00:00
-- url     : https://prove2.me/theorems/d903d950-1ca3-403f-b7d2-cc50de9bca12
-- title:
--   Auxiliary exclusion kernel with physical-distance heat-bath swaps
-- statement:
--   Given $x\in\mathbb R$ and $0<\theta\le1/2$, label $i$ is low when $y_i\le x$, intermediate when $x<y_i\le x+\theta$, and high when $y_i>x+\theta$. Choose uniformly a left-to-right adjacent pair $(i,j)$ in the subsequence of non-intermediate labels. Reject pairs of the same class. For unlike classes swap their positions with probability
--   $$\frac{p_j^d}{p_j^d+p_i^d},\qquad d=\operatorname{position}_\sigma(j)-\operatorname{position}_\sigma(i).$$
--   All other positions remain fixed, and the rejection probability remains on the diagonal. If the reduced subsequence has fewer than two labels, the kernel is the identity. The distance includes intermediate labels, and empty low or high classes are allowed.
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Definition 3.3, equation (3.1), printed p.6 = PDF p.6

import Definitions.Def_TranspositionIID_Main_Buffer
import Definitions.Def_TranspositionIID_Main_Stationary

noncomputable section

namespace TranspositionIID.Main

/-- Pairs oriented left-to-right, adjacent after deleting intermediate labels (Definition 3.3, p.6). -/
def auxiliaryPairs {n : ℕ} (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij =>
    (Real.log (p ij.1) ≤ x ∨ x + θ < Real.log (p ij.1)) ∧
    (Real.log (p ij.2) ≤ x ∨ x + θ < Real.log (p ij.2)) ∧
    σ ij.1 < σ ij.2 ∧
    ∀ k, σ ij.1 < σ k → σ k < σ ij.2 → x < Real.log (p k) ∧ Real.log (p k) ≤ x + θ)

/-- Reject same-class pairs; otherwise swap the endpoint positions with probability (3.1).
The exponent is physical position distance, including intermediate labels. -/
def auxiliaryPairKernel {n : ℕ} (p : Fin n → ℝ) (x : ℝ)
    (σ η : ListState n) (ij : Fin n × Fin n) : ℝ :=
  if (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x) then
    if σ = η then 1 else 0
  else
    let d := (σ ij.2).val - (σ ij.1).val
    let a := p ij.2 ^ d / (p ij.2 ^ d + p ij.1 ^ d)
    (if σ.trans (Equiv.swap (σ ij.1) (σ ij.2)) = η then a else 0) +
      (if σ = η then 1 - a else 0)

/-- Identity when fewer than two non-intermediate labels remain, uniform choice otherwise. -/
def auxiliaryKernel {n : ℕ} (p : Fin n → ℝ) (x θ : ℝ) : Matrix (ListState n) (ListState n) ℝ :=
  fun σ η =>
    let pairs := auxiliaryPairs p x θ σ
    if pairs.card = 0 then (if σ = η then 1 else 0)
    else (∑ ij ∈ pairs, auxiliaryPairKernel p x σ η ij) / (pairs.card : ℝ)

end TranspositionIID.Main


