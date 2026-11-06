-- Prove2me | Definitions.Def_ParetoNCSched_xStar
-- name    : ParetoNCSched_xStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:38.693797+00:00
-- url     : https://prove2.me/theorems/cf5fbfc0-a6ba-4b35-9513-ceb39b9d2ca3
-- title:
--   The profile $x^*$
-- statement:
--   The profile is
--   $$x^*(w)=W^{-1}(w)\ \text{ for } w\in[0,\tilde w),\qquad x^*(w)=1\ \text{ for } w\in[\tilde w,1].$$
--
--   **Formalization Note** $W^{-1}(w)$ is written as the generalized inverse $\inf\{\xi\in[0,\tilde\xi]:\ W(\xi)\ge w\}$, which is $W^{-1}(w)$ on $[0,\tilde w)$ because $W$ is a continuous increasing bijection $[0,\tilde\xi]\to[0,\tilde w]$ (Lemma D.5(a)).
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, p.28

import Mathlib
import Definitions.Def_ParetoNCSched_wT

namespace ParetoNCSched

/-- **The profile `x*`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, p.28: "x*(w) = W⁻¹(w) for w ∈ [0, w̃), x*(w) = 1 for
w ∈ [w̃, 1]".

**Formalization Note.** `W⁻¹(w)` is written as the generalized inverse
`inf{ξ ∈ [0, ξ̃] : W(ξ) ≥ w}`, which equals `W⁻¹(w)` on `[0, w̃)` because `W` is a continuous
increasing bijection `[0, ξ̃] → [0, w̃]` (Lemma D.5(a)). Values for `w < 0` or `w > 1` are not used. -/
noncomputable def xStar (R w : ℝ) : ℝ :=
  if w < wT R then sInf {ξ : ℝ | ξ ∈ Set.Icc 0 (xiT R) ∧ w ≤ Wp R ξ} else 1

end ParetoNCSched


