-- Prove2me | Definitions.Def_DSICCompComp_Supplement_interimIntegrand
-- name    : DSICCompComp_Supplement_interimIntegrand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:19:05.688189+00:00
-- url     : https://prove2.me/theorems/5caf9135-442b-4bfe-bd73-3c4e8c3f6732
-- title:
--   Ex-post utility of bidder $i$ with values $v_i$ reporting $v'_i$
-- statement:
--   Consider $n$ additive bidders and $m$ items, and a mechanism with ex-post allocation rule $x_{ij}(\cdot)$ (the probability that bidder $i$ receives item $j$) and payment rule $p_i(\cdot)$. For a bidder $i$, her true value vector $v_i \in \mathbb R_{\ge 0}^m$, a report $v'_i \in \mathbb R_{\ge 0}^m$ and a value profile $v$ whose entries other than the $i$-th give the reports $v_{-i}$ of the other bidders, the bidder's ex-post utility is
--
--   $$
--   u_i(v_i \to v'_i;\, v_{-i}) \;=\; \sum_{j=1}^m x_{ij}(v'_i, v_{-i})\, v_{ij} \;-\; p_i(v'_i, v_{-i}).
--   $$
--
--   Its expectation over $v_{-i} \sim D^{n-1}$ is the interim utility that appears in the Bayesian incentive compatibility and individual rationality constraints.
--
--   **Formalization Note** Mechanisms are the published `MultiItemRev.MultiBuyer.MechanismN n (Fin m)`; bidders and items are 0-based. The profile $(v'_i, v_{-i})$ is `Function.update v i vi'`, so the $i$-th entry of `v` is ignored.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, BIC and BIR, pp.5–6 (pdf pp.6–7)

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open scoped NNReal

namespace DSICCompComp

namespace Supplement

/-- The ex-post utility of bidder `i` with true values `v_i` (here `vi`) when she reports `v'_i`
(here `vi'`) and the other bidders report `v_{-i}`, read off a full profile `v`:
`∑_j x_ij(v'_i, v_{-i}) · v_ij − p_i(v'_i, v_{-i})` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Section 2, BIC and BIR, pp.5–6 (pdf pp.6–7)). Its expectation over `v_{-i} ∼ D^{n-1}` is the
interim utility in the BIC/BIR constraints.

**Formalization Note** Mechanisms are the published `MultiItemRev.MultiBuyer.MechanismN n (Fin m)`
(`q v i j` = probability that bidder `i` gets item `j`, `s v i` = her payment); bidders and items
are 0-based. The deviation profile `(v'_i, v_{-i})` is `Function.update v i vi'`, so the `i`-th
coordinate of `v` is ignored; values are in `ℝ≥0`. -/
def interimIntegrand {n m : ℕ} (M : MultiItemRev.MultiBuyer.MechanismN n (Fin m)) (i : Fin n)
    (vi vi' : Fin m → ℝ≥0) (v : Fin n → Fin m → ℝ≥0) : ℝ :=
  ∑ j, M.q (Function.update v i vi') i j * (vi j : ℝ) - M.s (Function.update v i vi') i

end Supplement

end DSICCompComp


