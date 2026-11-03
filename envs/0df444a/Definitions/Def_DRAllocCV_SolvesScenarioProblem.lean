-- Prove2me | Definitions.Def_DRAllocCV_SolvesScenarioProblem
-- name    : DRAllocCV_SolvesScenarioProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:23.132005+00:00
-- url     : https://prove2.me/theorems/060303c9-269d-4ccd-b9cc-4b1966fae3f7
-- title:
--   $(p^\star,q^\star)$ solves the scenario problem $\mathrm{SP}_k(t)$
-- statement:
--   Let $S_1,\dots,S_m$ be subsets of the type space and $(p^\star,q^\star)\in\mathcal X$. For $k\in\{1,\dots,m\}$ and a scenario $t$, the **auxiliary scenario problem** is
--
--   $$
--   \max_{(p,q)\in\mathcal X}\ \sum_{i}\bigl(p_i(t)t_i-q_i(t)c_i\bigr)\quad\text{s.t.}\quad \sum_{i}\bigl(p_i(t')t'_i-q_i(t')c_i\bigr)=\sum_{i}\bigl(p^\star_i(t')t'_i-q^\star_i(t')c_i\bigr)\ \ \forall t'\in\textstyle\bigcup_{l=1}^{k-1}S_l. \tag{$\mathrm{SP}_k(t)$}
--   $$
--
--   $(p^\star,q^\star)$ **solves** $\mathrm{SP}_k(t)$ if it is feasible in it and no feasible point of $\mathrm{SP}_k(t)$ has a larger objective value.
--
--   **Formalization Note** Cells are indexed by $\{0,\dots,m-1\}$, so cell $k$ in Lean is the paper's $S_{k+1}$ and $\bigcup_{l=1}^{k-1}S_l$ is the union over $l<k$. "Solves" is a proposition, not a supremum.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.9, Proposition 1 (ii), problem SP_k(t)

import Mathlib
import Definitions.Def_DRAllocCV_Feasible
import Definitions.Def_DRAllocCV_payoff

namespace DRAllocCV

/-- **`(p⋆, q⋆)` solves the auxiliary scenario problem `SP_k(t)`** (Proposition 1 (ii),
Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.9) for a family of cells `S₁, …, S_m` of the type space:
`(p⋆, q⋆)` is feasible in `SP_k(t)` and maximizes
`max_{(p,q) ∈ 𝒳} ∑ᵢ (pᵢ(t) tᵢ − qᵢ(t) cᵢ)` subject to
`∑ᵢ (pᵢ(t′) t′ᵢ − qᵢ(t′) cᵢ) = ∑ᵢ (p⋆ᵢ(t′) t′ᵢ − q⋆ᵢ(t′) cᵢ)` for all `t′ ∈ ⋃_{l=1}^{k−1} S_l`.

**Formalization Note.** Cells are indexed by `Fin m`, so Lean's cell `k` is the paper's
`S_{k+1}` and `⋃_{l=1}^{k−1} S_l` is `⋃ l < k, S l`. "Solves" is stated as a `Prop`: `(p⋆, q⋆)`
is feasible in `SP_k(t)` (it lies in `𝒳` and trivially satisfies the equality constraints), and
every feasible `(p, q)` of `SP_k(t)` has objective value at most that of `(p⋆, q⋆)`. -/
def SolvesScenarioProblem {ι : Type*} [Fintype ι] [DecidableEq ι] (tlo thi c : ι → ℝ) {m : ℕ}
    (S : Fin m → Set (ι → ℝ)) (pstar qstar : ι → (ι → ℝ) → ℝ) (k : Fin m) (t : ι → ℝ) : Prop :=
  Feasible tlo thi pstar qstar ∧
  ∀ p q, Feasible tlo thi p q →
    (∀ l, l < k → ∀ t' ∈ S l, payoff c p q t' = payoff c pstar qstar t') →
    payoff c p q t ≤ payoff c pstar qstar t

end DRAllocCV


