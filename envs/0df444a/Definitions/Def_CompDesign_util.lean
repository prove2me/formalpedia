-- Prove2me | Definitions.Def_CompDesign_util
-- name    : CompDesign_util
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:52:39.265921+00:00
-- url     : https://prove2.me/theorems/2f63573f-27a0-4546-94c7-127ec15b93b1
-- title:
--   Agent utility $u_i(S)$ in the marginal-contribution game $\Gamma^{mc}$
-- statement:
--   Let $N=\{1,\dots,n\}$ be the agents, $v$ the value function, $B$ the budget and $c_i$ agent $i$'s private cost. In the game $\Gamma^{mc}$ induced by the marginal-contribution payment rule $p^{mc}$ of (8), the **utility** of agent $i$ at the participating set $S$ is
--
--   $$
--   u_i(S)=\begin{cases}0 & \text{if } i\notin S,\\ p^{mc}_i(S)-c_i & \text{otherwise,}\end{cases}
--   \qquad
--   p^{mc}_i(S)=\begin{cases}B\,\dfrac{v(S)-v(S\setminus\{i\})}{v(S)} & \text{if } i\in S \text{ and } v(S)>0,\\ 0&\text{otherwise.}\end{cases}
--   $$
--
--   An agent who opts out is paid nothing and pays no cost; an agent who opts in is paid its normalized marginal contribution times the budget and pays its cost. These utilities define the strict better responses of Theorem 4.1.
--
--   **Formalization Note** Agents are `Fin n`, sets are `Finset (Fin n)`, costs and values are real. The payment is the published definition `CompDesignBFM.mcPay`, which is (8) verbatim.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §3.1, p.13 (PDF 16), definition of u_i; eq. (8), p.15 (PDF 18)

import Mathlib
import Definitions.Def_CompDesignBFM_mcPay

namespace CompDesign

/-- The utility of agent `i` at the participating set `S` in the game `Γ^mc` induced by the
marginal-contribution payment rule (8) (Anagnostides et al., *Compensation Design*, arXiv:2607.14438,
version of November 3, 2026, sha256 3d305d4d…, §3.1, p.13 (PDF 16), and (8), p.15 (PDF 18)):
`u_i(S) = 0` if `i ∉ S`, and `u_i(S) = p^mc_i(S) − c_i` otherwise.

**Formalization Note.** Agents are `Fin n`, sets of participating agents are `Finset (Fin n)`, costs
are `c : Fin n → ℝ`, the value function is `v : Finset (Fin n) → ℝ` and the budget is `B : ℝ`. The
payment is the published definition `CompDesignBFM.mcPay`, which is (8) verbatim. -/
noncomputable def util {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S then CompDesignBFM.mcPay v B S i - c i else 0

end CompDesign


