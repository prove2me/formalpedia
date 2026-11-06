-- Prove2me | Definitions.Def_IAFTRL_IsFeasible2_3
-- name    : IAFTRL_IsFeasible2_3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:57.112902+00:00
-- url     : https://prove2.me/theorems/f601822b-5c19-4c89-a27e-6ee2675a179e
-- title:
--   Feasible set of the sampling program (2.3)
-- statement:
--   Fix round $t\ge1$ and the cumulative estimate $S=\sum_{s<t}\hat\theta_s$, which determine $q_t$, $r_t$ and $Z_t$. A vector $p\in\mathbb R^{\mathcal A}$ is **feasible for (2.3)** if
--   1. $p$ is a probability distribution on $\mathcal A$;
--   2. (2.3b)–(2.3c) there is $w\ge0$ with $\gamma=\sum_bw_b\le\Gamma_t$ and $p=(1-\gamma)q_t+w$;
--   3. (2.3d) for all actions $a,b$: $\ |(a-r_t)^\top v_b(p)|\le\beta_t+Z_{t,a}/B$;
--   4. (2.3e) for every action $a$: $\ (a-r_t)^\top M(p)^{-1}(a-r_t)\le\beta_t+Z_{t,a}^2/(Bt)$;
--   5. (2.3f) $\ C_t(p)\le 2d/\beta_t$.
--
--   Here $M(p)=\sum_ap_a\,aa^\top$ and $v_b(p)=M(p)^{-1}b$. The mixture constraint gives $p_a\ge(1-\Gamma_t)q_{t,a}>0$, hence $M(p)\succ0$.
--
--   **Formalization Note** The paper states (2.3d)–(2.3f) as suprema over all families of feedback laws supported on $[-1,1]$, and gives the computable forms used here as equivalent (pp.18–19): the update magnitude form $|(a-r_t)^\top v_b(p)|\le\beta_t+Z_{t,a}/B$, the second-moment form $\sum_bp_b[(a-r_t)^\top v_b(p)]^2=(a-r_t)^\top M(p)^{-1}(a-r_t)\le\beta_t+Z^2_{t,a}/(Bt)$, and $C_t(p)\le2d/\beta_t$. The equivalences use $|Y|\le1$, the Dirac laws at $\pm1$, and that $\chi$ is even and increasing in $|x|$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, pp.17–19, Eqs. (2.3b)–(2.3f)

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Gam
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_qSoft
import Definitions.Def_IAFTRL_refArm
import Definitions.Def_IAFTRL_Zd
import Definitions.Def_IAFTRL_vCoef
import Definitions.Def_IAFTRL_proxyC

namespace IAFTRL

open Matrix

/-- **The feasible set of program (2.3).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, pp.17–19, constraints
(2.3b)–(2.3f): "`p = (1 − γ)q_t + w`, `γ = Σ_{b∈𝒜} w_b` (2.3b), `w_b ≥ 0` (∀b ∈ 𝒜), `γ ≤ Γ_t` (2.3c)",
together with the update magnitude constraint (2.3d), the second-moment constraint (2.3e) and the
stability constraint (2.3f), over `p ∈ 𝒫(𝒜)`.

`IsFeasible2_3 arms t S p` (paper round `t ≥ 1`, `S = Σ_{s<t} θ̂_s`, `β_t = beta d K t`,
`q_t = qSoft β_t arms S`, `r_t = refArm arms S`, `Z_{t,a} = Zd arms S a`, `v_b(p) = vCoef arms p b`,
`M(p) = linearAllocationMatrix arms p`) says:
1. `p` is a probability vector;
2. (2.3b)–(2.3c) there is `w ≥ 0` with `γ = Σ_b w_b ≤ Γ_t` and `p = (1 − γ)q_t + w`;
3. (2.3d) `|(a − r_t)^⊤ v_b(p)| ≤ β_t + Z_{t,a}/B` for all `a, b`;
4. (2.3e) `(a − r_t)^⊤ M(p)^{-1} (a − r_t) ≤ β_t + Z_{t,a}²/(Bt)` for all `a`;
5. (2.3f) `C_t(p) ≤ 2d/β_t`.

**Formalization Note.** The paper states (2.3d)–(2.3f) as suprema over all families `Q` of
feedback laws on `[−1, 1]`; the Lean uses the computable forms the paper gives as equivalent:
"its equivalent computable form is `|(a − r_t)^⊤v_b(p)| ≤ β_t + Z_{t,a}/B`" (p.18); "(2.3e) is
equivalent to `Σ_b p_b[(a − r_t)^⊤v_b(p)]² = (a − r_t)^⊤M(p)^{-1}(a − r_t) ≤ β_t + Z²_{t,a}/(Bt)`"
(p.19); the computable form `C_t(p) ≤ 2d/β_t` of (2.3f) (p.19). The mixture constraint forces
`M(p) ≻ 0`, so no junk inverse occurs on the feasible set. -/
def IsFeasible2_3 {d K : ℕ} (arms : Fin K → Fin d → ℝ) (t : ℕ) (S : Fin d → ℝ)
    (p : Fin K → ℝ) : Prop :=
  (∀ b, 0 ≤ p b) ∧ ∑ b, p b = 1 ∧
    (∃ w : Fin K → ℝ, (∀ b, 0 ≤ w b) ∧ ∑ b, w b ≤ Gam d K t ∧
      p = fun a => (1 - ∑ b, w b) * qSoft (beta d K t) arms S a + w a) ∧
    (∀ a b, |(arms a - refArm arms S) ⬝ᵥ vCoef arms p b| ≤
      beta d K t + Zd arms S a / Bc K) ∧
    (∀ a, (arms a - refArm arms S) ⬝ᵥ
        (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ *ᵥ (arms a - refArm arms S) ≤
      beta d K t + Zd arms S a ^ 2 / (Bc K * t)) ∧
    proxyC arms t S p ≤ 2 * (d : ℝ) / beta d K t

end IAFTRL


