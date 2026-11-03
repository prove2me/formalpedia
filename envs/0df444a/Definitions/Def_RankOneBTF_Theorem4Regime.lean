-- Prove2me | Definitions.Def_RankOneBTF_Theorem4Regime
-- name    : RankOneBTF_Theorem4Regime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:07.254292+00:00
-- url     : https://prove2.me/theorems/75df77ee-7090-4917-b6b2-6a73a883ccc0
-- title:
--   The asymptotic regime of Theorem 4
-- statement:
--   Let $r_{\bar x},r_{\bar y},r_{\bar z}$ be constants. A sequence of instances $t\mapsto(n_t,m_t,l_t,\bar x_t,\bar y_t,\bar z_t)$ is in the **regime of Theorem 4** if
--
--   1. the ratios of ones are the constants: $|\{i:\bar x_{t,i}=1\}|=r_{\bar x}n_t$, $|\{j:\bar y_{t,j}=1\}|=r_{\bar y}m_t$, $|\{k:\bar z_{t,k}=1\}|=r_{\bar z}l_t$ for every $t$;
--   2. $n_t,m_t,l_t\to\infty$;
--   3. the limit assumptions hold:
--   $$
--   n_tm_tl_t\,e^{-n_t}\to0,\qquad n_tm_tl_t\,e^{-m_t}\to0,\qquad n_tm_tl_t\,e^{-l_t}\to0 .
--   $$
--
--   An event happens **with high probability** if its probability goes to one as $n,m,l\to\infty$; in this mission that means: along every sequence in the regime.
--
--   **Formalization Note** The informal "as $n,m,l\to\infty$" with constant ratios is read as quantification over sequences indexed by $t\in\mathbb N$. Sizes are cast to reals before multiplying.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §4.3, p.10, Theorem 4 (assumptions); p.3 (ratios r_x̄, r_ȳ, r_z̄; 'with high probability')

import Mathlib
import Definitions.Def_RankOneBTF_groundTruth

namespace RankOneBTF

open Filter Topology

/-- The **asymptotic regime of Theorem 4** (arXiv:2202.07053v3, p.10): along a sequence
`t ↦ (n_t, m_t, l_t, x̄_t, ȳ_t, z̄_t)` of instances,
1. the ratios of ones are the constants `r_x̄, r_ȳ, r_z̄`: `|{i : x̄_{t,i} = 1}| = r_x̄ n_t`,
   `|{j : ȳ_{t,j} = 1}| = r_ȳ m_t`, `|{k : z̄_{t,k} = 1}| = r_z̄ l_t` for every `t` (p.3: "Denote by
   r_x̄ (resp. r_ȳ, r_z̄) the ratio of ones in x̄ (resp. ȳ, z̄) to the number of elements"; Theorem 4:
   "r_x̄, r_ȳ, r_z̄ are positive constants");
2. `n_t, m_t, l_t → ∞` ("as n, m, l → ∞");
3. `n_t m_t l_t exp(−n_t)`, `n_t m_t l_t exp(−m_t)`, `n_t m_t l_t exp(−l_t)` → 0 (Theorem 4's limit
   assumptions).

**Formalization Note** "With high probability as n, m, l → ∞" (p.3) is read along sequences:
a statement holds w.h.p. if its probability tends to `1` along every sequence in this regime.
The sizes are cast to `ℝ` before multiplying. -/
def Theorem4Regime (rx ry rz : ℝ) (n m l : ℕ → ℕ) (xb : ∀ t, Fin (n t) → Bool)
    (yb : ∀ t, Fin (m t) → Bool) (zb : ∀ t, Fin (l t) → Bool) : Prop :=
  (∀ t, numOnes (xb t) = rx * (n t : ℝ)) ∧
  (∀ t, numOnes (yb t) = ry * (m t : ℝ)) ∧
  (∀ t, numOnes (zb t) = rz * (l t : ℝ)) ∧
  Tendsto n atTop atTop ∧ Tendsto m atTop atTop ∧ Tendsto l atTop atTop ∧
  Tendsto (fun t => (n t : ℝ) * (m t : ℝ) * (l t : ℝ) * Real.exp (-(n t : ℝ))) atTop (𝓝 0) ∧
  Tendsto (fun t => (n t : ℝ) * (m t : ℝ) * (l t : ℝ) * Real.exp (-(m t : ℝ))) atTop (𝓝 0) ∧
  Tendsto (fun t => (n t : ℝ) * (m t : ℝ) * (l t : ℝ) * Real.exp (-(l t : ℝ))) atTop (𝓝 0)

end RankOneBTF


