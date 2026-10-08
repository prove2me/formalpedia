-- Prove2me | Definitions.Def_RobustDP_ChiSquare_RelEntropy
-- name    : RobustDP_ChiSquare_RelEntropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:26.64053+00:00
-- url     : https://prove2.me/theorems/43dca1a6-8142-4214-8c12-c68904ec0902
-- title:
--   Relative entropy $D(p\|q)$ on a finite set, natural logarithm (35)
-- statement:
--   Let $\mathcal S$ be a finite set and $p,q:\mathcal S\to\mathbb R$ with $q(s)>0$ for all $s$. The **relative entropy** (Kullback–Leibler divergence) of $p$ with respect to $q$ is
--
--   $$
--   D(p\|q)=\sum_{s\in\mathcal S}p(s)\log\frac{p(s)}{q(s)},
--   $$
--
--   with the natural logarithm, as in (35) of Iyengar's paper, and the convention $0\log 0=0$.
--
--   The relative-entropy confidence regions of Section 4.1 are sublevel sets of $D(\cdot\|q)$; Section 4.2 bounds $D$ by the χ² distance to obtain the conservative set (46).
--
--   **Formalization Note** With Mathlib's convention `Real.log 0 = 0`, a coordinate with $p(s)=0$ contributes $0$, which is the convention $0\log 0=0$. The definition is used only with $q(s)>0$. The finite-sum form is used instead of Mathlib's measure-level `InformationTheory.klDiv`. The published `RobustMDP.EntropyInner.klDiv` is the same formula indexed by `Fin n`; this mission works over an arbitrary finite type, so it defines its own.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 16, eq. (35), and p. 18, Section 4.2

import Mathlib

namespace RobustDP.ChiSquare

/-- The relative entropy (35) `D(p‖q) = ∑_{s ∈ S} p(s) log(p(s)/q(s))`, natural logarithm
(Iyengar, TR-2002-07, pp. 16 and 18). With Mathlib's `Real.log 0 = 0`, a coordinate with
`p(s) = 0` contributes `0`, the convention `0 log 0 = 0`. It is used only with `q(s) > 0`. -/
noncomputable def relEntropy {S : Type*} [Fintype S] (p q : S → ℝ) : ℝ :=
  ∑ s, p s * Real.log (p s / q s)

end RobustDP.ChiSquare


