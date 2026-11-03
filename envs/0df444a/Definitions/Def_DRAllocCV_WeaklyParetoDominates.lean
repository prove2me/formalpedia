-- Prove2me | Definitions.Def_DRAllocCV_WeaklyParetoDominates
-- name    : DRAllocCV_WeaklyParetoDominates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:14.935725+00:00
-- url     : https://prove2.me/theorems/a84965b2-10e4-4777-b659-f14abd3ecbd5
-- title:
--   Weak Pareto robust dominance (Definition 2, (1))
-- statement:
--   A feasible mechanism $(p',q')$ **weakly Pareto robustly dominates** a feasible mechanism $(p,q)$ if
--
--   $$
--   \mathbb E_{\mathbb P}\Bigl[\sum_{i}\bigl(p'_i(\tilde t)\tilde t_i-q'_i(\tilde t)c_i\bigr)\Bigr]\ \ge\ \mathbb E_{\mathbb P}\Bigl[\sum_{i}\bigl(p_i(\tilde t)\tilde t_i-q_i(\tilde t)c_i\bigr)\Bigr]\qquad\forall\,\mathbb P\in\mathcal P. \tag{1}
--   $$
--
--   **Formalization Note** The dominating mechanism $(p',q')$ is the first pair of arguments; feasibility of both mechanisms is part of the definition.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, Definition 2, eq. (1)

import Mathlib
import Definitions.Def_DRAllocCV_Feasible
import Definitions.Def_DRAllocCV_expectedPayoff

open MeasureTheory

namespace DRAllocCV

/-- **Weak Pareto robust dominance** (Definition 2, (1), Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.7): a feasible mechanism
`(p′, q′)` weakly Pareto robustly dominates a feasible mechanism `(p, q)` if
`𝔼_ℙ[∑ᵢ (p′ᵢ(t̃) t̃ᵢ − q′ᵢ(t̃) cᵢ)] ≥ 𝔼_ℙ[∑ᵢ (pᵢ(t̃) t̃ᵢ − qᵢ(t̃) cᵢ)]` for all `ℙ ∈ 𝒫`.

The dominating mechanism `(p′, q′)` comes first in the argument list. -/
def WeaklyParetoDominates {ι : Type*} [Fintype ι] [DecidableEq ι] (tlo thi : ι → ℝ)
    (Pset : Set (Measure (ι → ℝ))) (c : ι → ℝ) (p' q' p q : ι → (ι → ℝ) → ℝ) : Prop :=
  Feasible tlo thi p' q' ∧ Feasible tlo thi p q ∧
  ∀ P ∈ Pset, expectedPayoff P c p q ≤ expectedPayoff P c p' q'

end DRAllocCV


