-- Prove2me | Definitions.Def_AuditEvasion_Costs
-- name    : AuditEvasion_Costs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:34.756628+00:00
-- url     : https://prove2.me/theorems/6ad82c77-0852-4157-9274-70f87385af8d
-- title:
--   §3.4–§4, pp.1848–1850 — threat utility, agent strategies, agent's cost (3), obedience (6), IC, feasibility and objective (11)
-- statement:
--   **Threat utility** (§3.4). $U_t$ is the agent's expected discounted cost from $t$ on after an evasive action at $t$: $U_t=E[Fe^{-\theta(D-t)}]$, where $D$ is the first later audit (an audit at $t$ itself included) that detects the issue. The future audits follow the policy given no audit since the last one, and each detects independently with probability $\beta$. When $\beta=0$, $U_t\equiv0$.
--
--   **Strategies and agent's cost** (§3.5). A strategy chooses the action time $\sigma\ge T$ ($\sigma=\infty$: never act) from $T$ and the history before $T$. With $\tau(T)$ the first audit at or after $T$ and $c_\sigma=P_\sigma\wedge(h+U_\sigma)\wedge r$, the agent's cost is (3):
--
--   $$C_a(P,\sigma)=E\big[e^{-\theta\sigma}\mathbf 1\{\sigma\le\tau(T)\}c_\sigma+\mathbf 1\{\sigma>\tau(T)\}Fe^{-\theta\tau(T)}\big].$$
--
--   Prompt disclosure is $\sigma=T$.
--
--   **Feasibility.** A policy is feasible for problem (11) if it is well formed, $P_t\le F$ (§3.2), it satisfies obedience (6),
--
--   $$P_t\le r\wedge(h+U_t),$$
--
--   on every history and every $t$ after its last audit, and it is incentive compatible: $C_a(P,T)\le C_a(P,\sigma)$ for every strategy $\sigma$ (Theorem 1 part 3).
--
--   **Objective** (11). The principal's cost of a policy is
--
--   $$C(P)=\frac{\lambda}{\theta+\lambda}\,r+E\Big[k\sum_{i:\ \tau_i\le T}e^{-\theta\tau_i}-e^{-\theta T}P_T\Big],$$
--
--   where $k\sum_{\tau_i\le T}e^{-\theta\tau_i}=k\int_0^Te^{-\theta t}dN_t$ is the auditing expense and $P_T$ the payment at the issue time on the history before $T$.
--
--   **Formalization Note** Costs are extended reals: the auditing expense is a nonnegative extended integral, the payment term is taken through its positive and negative parts. The paper's formal threat utility is (A.4) of its Online Appendix A, not used here. Strategies are delays fixed at $T$: the agent learns nothing between $T$ and $\tau(T)$ and is caught at $\tau(T)$ if still inactive.
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, §3.4–§3.6 p.1848, (3) p.1848, Theorem 1 parts 2–3 and (6) p.1849, (11) p.1850

import Mathlib
import Definitions.Def_AuditEvasion_Model
import Definitions.Def_AuditEvasion_AuditProcess

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section
open Classical

namespace AuditEvasion

/-- The threat utility `U_t` (§3.4, p.1848; recursion (7)–(8), p.1849): the agent's expected
discounted cost from time `t` onwards after an evasive action taken at `t` on the phase after the
history `H`, `U = E[F e^{-θ(D - t)}]`, where `D` is the first audit at or after `t` that detects
the issue (`0` if none does). The audits after `t` follow the policy conditioned on no audit in
`(lastEpoch n H, t)` (`auditFrom`, first noise sequence); each audit detects independently with
probability `β` (second noise sequence: audit `m` detects iff its uniform is `< β`); the fine is
`F_t = F` (p.1849).

Oper. Res. 72(5) (2024), §3.4, p.1848 and Theorem 1 part 2, p.1849.

**Formalization Note** The paper's formal definition is (A.4) of its Online Appendix A, not
used here; this is the definition of the quoted sentence ("expected discounted cost … after
taking an evasive action … fully determined by the audit schedule Q_t, fine F_t, and
postevasion detection probability β"). An audit at the instant `t` itself counts (Figure 1:
the agent acts, then the audit takes place, as in (7)). With `β = 0` no audit detects and
`U ≡ 0`, as p.1848 states. -/
def threatUtility (p : Params) (π : Policy) (n : ℕ) (H : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∫⁻ ω : (ℕ → unitInterval) × (ℕ → unitInterval),
      (if hD : ∃ m, auditFrom π n H t ω.1 m ≠ ⊤ ∧ ((ω.2 m : unitInterval) : ℝ) < p.beta then
        ENNReal.ofReal
          (p.F * Real.exp (-p.theta * ((auditFrom π n H t ω.1 (Nat.find hD)).toReal - t)))
      else 0) ∂(auditNoise.prod auditNoise)).toReal

/-- An agent strategy (§3.5, p.1848: "stopping time σ(T) ≥ T denote the instant when the agent
takes an action after an issue has emerged at time T"): the action time `σ = delay n H T`
(`⊤` = never act) as a function of the issue time `T` and of the public history `H = H_T` of the
audits before `T`.

**Formalization Note** (encoding) The agent's information is `T` and the audit epochs. No audit
happens in `(T, τ(T))`, and an agent who has not acted by `τ(T)` is caught there, so on the event
that matters every stopping time `σ ≥ T` agrees with a delay fixed at `T`; randomized strategies
are averages of these. Delays are Borel measurable. -/
structure Strategy where
  /-- The action time chosen at the issue time `t` after the history `H`. -/
  delay : (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ≥0∞
  le_delay : ∀ n (H : Fin n → ℝ) t, ENNReal.ofReal t ≤ delay n H t
  measurable_delay : ∀ n, Measurable fun x : (Fin n → ℝ) × ℝ => delay n x.1 x.2

/-- Prompt disclosure, `σ(T) = T` (Theorem 1 part 3, p.1849: `C_a(P,T)`). -/
def prompt : Strategy where
  delay _ _ t := ENNReal.ofReal t
  le_delay _ _ _ := le_rfl
  measurable_delay _ := ENNReal.measurable_ofReal.comp measurable_snd

/-- The agent's realized discounted cost (the integrand of (3), p.1848) when the issue time is
`x.1 = T` and the audit noise is `x.2`: with `σ` the action time and `τ = τ(T)` the first audit at
or after `T`, it is `e^{-θσ} c_σ` if `σ ≤ τ` (and `0` if `σ = τ = ∞`), where
`c_σ = P_σ ∧ (h + U_σ) ∧ r`, and `F e^{-θτ}` if `σ > τ`. -/
def agentLoss (p : Params) (π : Policy) (s : Strategy) (x : ℝ × (ℕ → unitInterval)) : ℝ :=
  if s.delay (stageAt π x.2 x.1) (histAt π x.2 x.1) x.1 ≤ firstAuditAfter π x.2 x.1 then
    (if s.delay (stageAt π x.2 x.1) (histAt π x.2 x.1) x.1 = ⊤ then 0
     else
      Real.exp (-p.theta * (s.delay (stageAt π x.2 x.1) (histAt π x.2 x.1) x.1).toReal) *
        min (π.pay (stageAt π x.2 x.1) (histAt π x.2 x.1)
              (s.delay (stageAt π x.2 x.1) (histAt π x.2 x.1) x.1).toReal)
          (min (p.h + threatUtility p π (stageAt π x.2 x.1) (histAt π x.2 x.1)
                  (s.delay (stageAt π x.2 x.1) (histAt π x.2 x.1) x.1).toReal) p.r))
  else p.F * Real.exp (-p.theta * (firstAuditAfter π x.2 x.1).toReal)

/-- The expectation of a real function in `EReal`, `∫ g⁺ − ∫ g⁻`, each part a `lintegral`
(no Bochner junk value for a non-integrable `g`). -/
def eExpect {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (g x) ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ x, ENNReal.ofReal (-g x) ∂μ : ℝ≥0∞) : EReal)

/-- The agent's expected discounted cost `C_a(P, σ)` of (3), p.1848, with `F_t = F` (p.1849). -/
def agentCost (p : Params) (π : Policy) (s : Strategy) : EReal :=
  eExpect (issueAuditLaw p) (agentLoss p π s)

/-- The states `(H, t)` at which a payment can be offered: `H` is a history and `t` lies after its
last audit (`t ≥ 0` for the empty history). -/
def PayState (n : ℕ) (H : Fin n → ℝ) (t : ℝ) : Prop :=
  ValidHist n H ∧ (lastEpoch n H < t ∨ (n = 0 ∧ t = 0))

/-- Limited liability (§3.2, p.1847): the disclosure payment satisfies `P_t ≤ F`. -/
def LimitedLiability (p : Params) (π : Policy) : Prop :=
  ∀ n (H : Fin n → ℝ) t, PayState n H t → π.pay n H t ≤ p.F

/-- Obedience constraint (6) (Theorem 1 part 2, p.1849): `P_t ≤ r ∧ (h + U_t)` for all `t ≥ 0`,
on every public history. -/
def Obedient (p : Params) (π : Policy) : Prop :=
  ∀ n (H : Fin n → ℝ) t, PayState n H t →
    π.pay n H t ≤ min p.r (p.h + threatUtility p π n H t)

/-- The informational IC constraint (Theorem 1 part 3, p.1849): "Ca(P,T) ≤ Ca(P,σ) for all σ". -/
def IncentiveCompatible (p : Params) (π : Policy) : Prop :=
  ∀ s : Strategy, agentCost p π prompt ≤ agentCost p π s

/-- The feasible set of problem (11) (p.1850, "subject to (6)–(10)"): a well-formed policy
(§3.1) with `P_t ≤ F` (§3.2) satisfying obedience (6) and the IC constraint in its global form
`C_a(P,T) ≤ C_a(P,σ)` for all `σ` (equivalent to (9)–(10) by Theorem 1 part 3). -/
structure Feasible (p : Params) (π : Policy) : Prop where
  wellFormed : WellFormed π
  limitedLiability : LimitedLiability p π
  obedient : Obedient p π
  incentiveCompatible : IncentiveCompatible p π

/-- The principal's total expected discounted auditing expense before the issue,
`E[k ∫_0^T e^{-θt} dN_t] = E[k Σ_{i : τ_i ≤ T} e^{-θτ_i}]` (§3.6, p.1848; Corollary 1, p.1851:
"the principal's total auditing expense"), in `ℝ≥0∞` (it can be `+∞`). -/
def auditExpense (p : Params) (π : Policy) : ℝ≥0∞ :=
  ∫⁻ x, ∑' i, (if audits π x.2 i ≤ ENNReal.ofReal x.1 then
      ENNReal.ofReal (p.k * Real.exp (-p.theta * (audits π x.2 i).toReal)) else 0)
    ∂(issueAuditLaw p)

/-- The disclosure payment `P_T` at the issue time, on the history of the audits before `T`. -/
def paymentAtIssue (π : Policy) (x : ℝ × (ℕ → unitInterval)) : ℝ :=
  π.pay (stageAt π x.2 x.1) (histAt π x.2 x.1) x.1

/-- The objective of problem (11), p.1850:
`C(P) = λ/(θ+λ) · r + E[k ∫_0^T e^{-θt} dN_t − e^{-θT} P_T]`, in `EReal`: the auditing expense in
`ℝ≥0∞` plus the expectation of `−e^{-θT} P_T` through its positive and negative parts. -/
def principalCost (p : Params) (π : Policy) : EReal :=
  ((p.lam / (p.theta + p.lam) * p.r : ℝ) : EReal) + (auditExpense p π : EReal) +
    eExpect (issueAuditLaw p) (fun x => -(Real.exp (-p.theta * x.1) * paymentAtIssue π x))

end AuditEvasion


