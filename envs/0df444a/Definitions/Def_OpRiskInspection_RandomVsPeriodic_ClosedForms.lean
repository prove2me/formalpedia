-- Prove2me | Definitions.Def_OpRiskInspection_RandomVsPeriodic_ClosedForms
-- name    : OpRiskInspection_RandomVsPeriodic_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:58.458421+00:00
-- url     : https://prove2.me/theorems/dfe38cff-7c35-4a32-b575-c8ebc3a4454f
-- title:
--   (12), (14), (EC.2), (EC.4), (EC.49) — regime thresholds and closed-form payoffs
-- statement:
--   For penalty $P>c/\lambda$, the effort thresholds are $\underline v_R=rc/(P\lambda-c)$ and $\underline v_D=r/\log(P\lambda/c)$, from (12) and (14). The functions $\bar V_R$, $V_R^0$, $\bar V_D$, $\underline V_D$, and $V_D^0$ are the paper's explicit payoff branches in (EC.2) and (EC.4); each takes the inspection cost $K$ and the frequency $v$, and the induced-effort branches also take $P$.
--
--   The random-policy cost threshold in (EC.49) is
--   $$K_R=\frac{c}{r}\frac{(e^\delta-1)^2}{e^\delta\delta(\delta+1)},\qquad \delta=\frac{cr}{L\lambda-cr}.$$
--   These functions allow the model payoff to be compared by effort regime without replacing the model-level principal objective by a bare formula.
--
--   **Formalization Note** The functions are total real-valued Lean definitions; statements invoking a branch carry its positive-frequency and positive-penalty domain conditions. $K_R$ is well defined under Assumption 1.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 13, (12), (14); pp. ec5–ec6, (EC.2), (EC.4); p. ec25, (EC.49)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.RandomVsPeriodic

/-- The random-policy effort threshold in (12), for `P > c/λ`. -/
noncomputable def vR (p : Params) (P : ℝ) : ℝ :=
  p.r * p.c / (P * p.lam - p.c)

/-- The periodic-policy effort threshold in (14), for `P > c/λ`. -/
noncomputable def vD (p : Params) (P : ℝ) : ℝ :=
  p.r / Real.log (P * p.lam / p.c)

/-- The random-policy induced-effort branch in (EC.2). -/
noncomputable def VbarR (p : Params) (K v P : ℝ) : ℝ :=
  (mubar p - p.c * Real.log ((P * p.lam / p.c) * (v / (p.r + v))) -
    (p.L * p.c / P) * (1 / v) -
    K * p.r / (Real.exp (p.r / v) - 1)) / p.r

/-- The random-policy zero-effort branch in (EC.2). -/
noncomputable def V0R (p : Params) (K v : ℝ) : ℝ :=
  (mubar p - p.L * p.lam / (p.r + v) -
    K * p.r / (Real.exp (p.r / v) - 1)) / p.r

/-- The periodic-policy induced-effort branch in (EC.4). -/
noncomputable def VbarD (p : Params) (K v P : ℝ) : ℝ :=
  (mubar p -
    p.c * (1 + Real.log (P * p.lam / p.c) -
      p.r / (v * (1 - Real.exp (-(p.r / v))))) -
    (p.c * p.L / (P * p.r)) *
      ((Real.exp (p.r / v) - 1) / 2) -
    K * p.r / (Real.exp (p.r / v) - 1)) / p.r

/-- The periodic-policy partially induced-effort branch in (EC.4). -/
noncomputable def VunderD (p : Params) (K v P : ℝ) : ℝ :=
  (mubar p -
    p.c * (P * p.lam / p.c - (1 + Real.log (P * p.lam / p.c))) /
      (Real.exp (p.r / v) - 1) -
    ((p.L * p.lam / p.r) *
      ((Real.exp (p.r / v) - p.r / v) -
        (Real.exp (p.r / vD p P) - p.r / vD p P)) +
      (p.c * p.L / (P * p.r)) *
        ((Real.exp (p.r / vD p P) - 1) ^ 2 / 2)) /
      (Real.exp (p.r / v) - 1) -
    K * p.r / (Real.exp (p.r / v) - 1)) / p.r

/-- The periodic-policy zero-effort branch in (EC.4). -/
noncomputable def V0D (p : Params) (K v : ℝ) : ℝ :=
  (mubar p - (p.L * p.lam / p.r) *
    (Real.exp (p.r / v) - p.r / v - 1) /
      (Real.exp (p.r / v) - 1) -
    K * p.r / (Real.exp (p.r / v) - 1)) / p.r

/-- The random-policy inspection-cost threshold in (EC.49). -/
noncomputable def KR (p : Params) : ℝ :=
  let δ := p.c * p.r / (p.L * p.lam - p.c * p.r)
  p.c / p.r * (Real.exp δ - 1) ^ 2 /
    (Real.exp δ * δ * (δ + 1))

end OpRiskInspection.RandomVsPeriodic


