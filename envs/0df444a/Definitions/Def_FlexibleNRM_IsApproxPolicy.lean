-- Prove2me | Definitions.Def_FlexibleNRM_IsApproxPolicy
-- name    : FlexibleNRM_IsApproxPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:26:58.853872+00:00
-- url     : https://prove2.me/theorems/d08fe732-8ac7-43a9-a11f-e95652ffc701
-- title:
--   The approximate policy, Eq. (7)
-- statement:
--   The approximate policy is greedy with respect to $\hat J$: at period $t$ in a feasible state $x$ it offers an assortment attaining
--   $$\max_{S\subseteq\mathcal J}\Big\{\sum_{j\in\mathcal J}\phi_{jt}(S)\,\mathbf 1_{(\mathcal F(x+e_j)\ne\emptyset)}\big[f_j+\hat J_{t+1}(x+e_j)-\hat J_{t+1}(x)\big]\Big\}.$$
--
--   **Formalization Note** (7) prints `max` where it means `arg max`. The relation covers every maximizer, including those that offer an unavailable product, and it says nothing at infeasible states, which the policy does not reach from $x=0$.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (7), p.11

import Mathlib
import Definitions.Def_FlexibleNRM_assortmentValue
import Definitions.Def_FlexibleNRM_vfa

namespace FlexibleNRM

/-- `Sapp` is an **approximate policy**, the greedy policy with respect to `Ĵ`, Eq. (7): at each
period `t` and state `x` with `F(x) ≠ ∅`, the assortment `Sapp t x` maximizes
`∑_j φ_jt(S) 1(F(x + e_j) ≠ ∅) [f_j + Ĵ_{t+1}(x + e_j) − Ĵ_{t+1}(x)]` over `S ⊆ J`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (7), p.11.

**Formalization Note** (7) prints `max` where it means `arg max`: the next sentence speaks of an
optimal solution, and (11) evaluates `φ_jt` at `S_t^App(x)`. This is a relation, so every maximizer
is covered, including one that offers a product `j` with `F(x + e_j) = ∅`; the paper's choice,
which offers no such product, is one of them. It constrains feasible `x` only, since `Ĵ` is a
maximum over an empty set at an infeasible state, and the policy never reaches such a state from
`x = 0`. -/
def IsApproxPolicy {n m r : ℕ} (N : Network n m r) (γ : Fin n → Fin r → ℕ → ℝ)
    (Sapp : ℕ → (Fin n → ℕ) → Finset (Fin n)) : Prop :=
  ∀ t ∈ Finset.Icc 1 N.T, ∀ x, Feasible N x → ∀ S : Finset (Fin n),
    assortmentValue N t (vfa N γ (t + 1)) x S ≤
      assortmentValue N t (vfa N γ (t + 1)) x (Sapp t x)

end FlexibleNRM


