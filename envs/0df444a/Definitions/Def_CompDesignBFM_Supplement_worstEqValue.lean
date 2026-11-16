-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_worstEqValue
-- name    : CompDesignBFM_Supplement_worstEqValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:05:34.809765+00:00
-- url     : https://prove2.me/theorems/13bde316-a4db-4bfa-9eec-61b8b6bbfae5
-- title:
--   Value of the worst pure Nash equilibrium
-- statement:
--   For a deterministic payment rule $p$, a value function $v$ and costs $c$, the value of the worst pure Nash equilibrium is
--
--   $$V_p(c)=\min_{S\in E(p,c)}v(S),$$
--
--   the denominator of the pure price of anarchy $\mathrm{PoA}(p,c)=\mathrm{OPT}/V_p(c)$. For a randomized rule the price of anarchy uses $\mathbb E_p[V_p(c)]$.
--
--   **Formalization Note** $E(p,c)$ is finite, so the infimum of the paper is a minimum. When $E(p,c)=\emptyset$ the value is set to $0$; Theorem B.1 assumes equilibria always exist, so this case does not arise there.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.1, p.5 (PDF 7); V_p(c) in the proof of Theorem B.1, p.43 (PDF 45)

import Mathlib
import Definitions.Def_CompDesignBFM_Supplement_IsPNEOf

namespace CompDesignBFM

namespace Supplement

open Classical in
/-- The value of the worst pure Nash equilibrium, `inf_(S ∈ E(p,c)) v(S)` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.1, p.5, PDF 7;
`V_p(c)` in the proof of Theorem B.1, p.43, PDF 45), for a deterministic payment rule `p` and costs `c`.
**Formalization Note.** `E(p,c)` is a finite set, so the infimum is a minimum (`Finset.inf'`). When
`E(p,c) = ∅` the value is the junk `0`; Theorem B.1 assumes every rule has an equilibrium at every
nonnegative cost vector, so the junk branch is never used there. -/
noncomputable def worstEqValue {n : ℕ} (p : Finset (Fin n) → Fin n → ℝ) (v : Finset (Fin n) → ℝ)
    (c : Fin n → ℝ) : ℝ :=
  if h : (Finset.univ.filter fun S : Finset (Fin n) => IsPNEOf p c S).Nonempty then
    (Finset.univ.filter fun S : Finset (Fin n) => IsPNEOf p c S).inf' h v
  else 0

end Supplement

end CompDesignBFM


