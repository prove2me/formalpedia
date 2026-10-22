-- Prove2me | Definitions.Def_ReferencePricing_Myopic_optPrice
-- name    : ReferencePricing_Myopic_optPrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:34:31.395006+00:00
-- url     : https://prove2.me/theorems/33fa3c9d-8f61-4284-9c7e-0d667751cbd2
-- title:
--   Optimal pricing policy p*(r) (largest maximizer of W), reference policy q*(r), and the optimal state and price paths
-- statement:
--   The **optimal pricing policy** is the largest maximizer of the Bellman objective,
--   $$p^*(r) = \max\,\operatorname*{arg\,max}_{p \in P} W(p, r),$$
--   and the **optimal reference price policy** is $q^*(r) = \alpha r + (1-\alpha) p^*(r)$. From an initial reference price $r_0$, the **state path** is $r^*_0 = r_0$, $r^*_{t+1} = q^*(r^*_t)$, and the **pricing path** is $p^*_t = p^*(r^*_t)$.
--
--   These are the strategic (optimizing) firm's policy and trajectories.
--
--   **Formalization Note.** The paper's convention (p. 417) that $\arg\max$ denotes the largest maximizer is encoded as the supremum of the set $\{p \in P : W(p', r) \le W(p, r)\ \forall p' \in P\}$. That set is nonempty and compact under the paper's hypotheses (a fact to be proved, not assumed); if it were empty, Lean's `sSup` would return $0$.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 417, Section 3 (optimal pricing policy, pricing path, state path)

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_value

namespace ReferencePricing.Myopic

/-- The optimal pricing policy `p*(r) = argmax_{p ∈ P} W(p, r)` (p. 417), with the paper's
convention that `argmax` is the largest maximizer: the supremum of the set of maximizers of
`W(·, r)` over `P = [0, p̄]`. -/
noncomputable def optPrice (prof : ℝ → ℝ → ℝ) (α β pbar r : ℝ) : ℝ :=
  sSup {p | p ∈ Set.Icc (0 : ℝ) pbar ∧
    ∀ p' ∈ Set.Icc (0 : ℝ) pbar, bellmanObjective prof α β pbar p' r ≤ bellmanObjective prof α β pbar p r}

/-- The optimal reference price policy `q*(r) = α r + (1 - α) p*(r)` (p. 417). -/
noncomputable def optRef (prof : ℝ → ℝ → ℝ) (α β pbar r : ℝ) : ℝ :=
  α * r + (1 - α) * optPrice prof α β pbar r

/-- The optimal state path (p. 417): `r*_0 = r₀`, `r*_{t+1} = q*(r*_t)`. -/
noncomputable def statePath (prof : ℝ → ℝ → ℝ) (α β pbar r₀ : ℝ) : ℕ → ℝ
  | 0 => r₀
  | t + 1 => optRef prof α β pbar (statePath prof α β pbar r₀ t)

/-- The optimal pricing path (p. 417): `p*_t = p*(r*_t)`. -/
noncomputable def pricePath (prof : ℝ → ℝ → ℝ) (α β pbar r₀ : ℝ) (t : ℕ) : ℝ :=
  optPrice prof α β pbar (statePath prof α β pbar r₀ t)

end ReferencePricing.Myopic


