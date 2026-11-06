-- Prove2me | Definitions.Def_CoverModular_FDPInstance_Standing
-- name    : CoverModular_FDPInstance_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:17.246178+00:00
-- url     : https://prove2.me/theorems/948e88f9-14a6-490b-aaec-5733dc2018a9
-- title:
--   Standing sign conditions of the flexibility design model
-- statement:
--   An instance $(\mu,c,d,p)$ satisfies the **standing conditions** if
--
--   1. $\mu_\omega\ge0$ for every scenario $\omega$;
--   2. $c_{i\omega}\ge0$ and $d_{j\omega}\ge0$ for all nodes and scenarios;
--   3. $p_{ij}\ge0$ for every arc.
--
--   The paper's $\mu_\omega$ are scenario probabilities and its profits satisfy $p_{ij}\ge0$ (p.6).
--
--   **Formalization Note** Only $\mu_\omega\ge0$ is required, not $\sum_\omega\mu_\omega=1$; no result of the mission uses the normalization. Capacities and demands carry no printed sign, but they are capacities and demands, LP (1) is infeasible if one is negative, and display (6) distinguishes only $>0$ and $=0$.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §2, pp.5–6

import Mathlib
import Definitions.Def_CoverModular_FDPInstance

namespace CoverModular

namespace FDPInstance

variable {I J Ω : Type}

/-- The standing sign conditions of the flexibility design model (DeValve, Pekeč, Wei,
SSRN 3844987, §2, pp.5–6): scenario weights `µ_ω ≥ 0`, capacities `c_iω ≥ 0`, demands
`d_jω ≥ 0`, and profits `p_ij ≥ 0`.

**Formalization Note** The paper's `µ_ω` are probabilities; only `µ_ω ≥ 0` is required here
(`∑ µ_ω = 1` is not used by any result of the mission). Capacities and demands are not given a
sign in print, but they are capacities and demands, LP (1) is infeasible if one is negative,
and display (6) splits into the cases `> 0` and `= 0`; so `c, d ≥ 0` are recorded as standing
conditions. `p_ij ≥ 0` is printed on p.6. -/
def Standing (inst : FDPInstance I J Ω) : Prop :=
  (∀ ω, 0 ≤ inst.μ ω) ∧ (∀ i ω, 0 ≤ inst.c i ω) ∧ (∀ j ω, 0 ≤ inst.d j ω) ∧
    ∀ i j, 0 ≤ inst.p i j

end FDPInstance

end CoverModular


