-- Prove2me | Definitions.Def_RecordInaccuracy_Objective
-- name    : RecordInaccuracy_Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:44.73439+00:00
-- url     : https://prove2.me/theorems/aeea7897-98ce-4ef0-94ce-477a8ad63bd7
-- title:
--   Objective $v_u(F;\tau)$ of problem (4), value function $v^*_u$, feasibility conditions
-- statement:
--   This definition uses the model of `RecordInaccuracy.Model`. The **running cost rate** at belief $\Pi$ is
--   $$c(\Pi)=(c_D+m)\lambda_D\Pi_0+c_L\lambda_L(1-\Pi_0)+\Delta p\,\lambda_E(1-\Pi_0).$$
--
--   For a restocking value $u\in\mathbb R$, a function $V$ on beliefs, an initial belief $F$ and a restocking time $\tau\ge 0$, the **objective of problem (4)** is
--   $$v_{u,V}(F;\tau)=\int_0^\tau e^{-\rho s}S^F(s)\Big[c(\Pi^F(s))+h(\Pi^F(s))\,V\big(J(\Pi^F(s))\big)\Big]ds+(k_R+u)\,e^{-\rho\tau}S^F(\tau).$$
--   This is
--   $$\mathbb E\Big[\int_0^{\tau\wedge\iota}c(\Pi(s))e^{-\rho s}ds+V(\Pi(\iota))e^{-\rho\iota}\mathbb 1_{\{\iota\le\tau\}}+(k_R+u)e^{-\rho\tau}\mathbb 1_{\{\tau<\iota\}}\Big]$$
--   with the law of the next observable event $\iota$ written out.
--
--   $V$ is the **value function** $v^*_u$ for $u$ when $V$ is measurable, bounded on the probability simplex, and satisfies equation (4):
--   $$V(F)=\inf_{\tau\in\mathbb R_+}v_{u,V}(F;\tau)\qquad\text{for every distribution }F.$$
--
--   The **feasibility conditions** of Appendix B are
--
--   1. (FC1) $(\lambda_Lc_L+\Delta p\,\lambda_E)/\rho<(c_D+m)\lambda_D/\rho$;
--   2. (FC2) $k_R+u<(c_D+m)\lambda_D/\rho$.
--
--   The paper assumes both throughout. The restocking value $u$ is tied to $V$ by $u=V(\mathbb 1_{\{q=q_m\}})$, the minimum cost from a full shelf.
--
--   **Formalization Note** The infimum in (4) is stated as `IsGLB` of the real values $\{v_{u,V}(F;\tau):\tau\ge 0\}$. Boundedness and measurability of $V$ make the integrand integrable and exclude junk solutions. The continuation weight $E[e^{-\rho\iota}]$ is at most $(\lambda_{\hat D}+\lambda_P)/(\rho+\lambda_{\hat D}+\lambda_P)<1$, so (4) is a sup-norm contraction on bounded functions. Its bounded solution on the simplex is therefore unique, and it is the paper's $v^*_u$.
-- source:
--   Chehrazi, Inventory Systems with Record Inaccuracy, MSOM (2025), doi:10.1287/msom.2023.0274, problems (SP') p.13 and (4) p.16; u = v*_u(1{q=qm}) p.13; Appendix B feasibility conditions 1–2, pp.47–48

import Mathlib
import Definitions.Def_RecordInaccuracy_Model

namespace RecordInaccuracy

namespace Params

variable (P : Params)

/-- The **running cost rate** of problems (SP') and (4) (pp.13, 16) at belief `b`:
`(c_D + m) λ_D b_0 + c_L λ_L (1 − b_0) + Δp λ_E (1 − b_0)` — stockout cost of demand, cost of
loss and cost of transaction errors, each while the shelf is (resp. is not) empty. -/
def runningCost (b : Fin (P.qm + 1) → ℝ) : ℝ :=
  (P.cD + P.m) * P.lamD * b 0 + P.cL * P.lamL * (1 - b 0) + P.dp * P.lamE * (1 - b 0)

/-- The **objective `v_u(F; τ)` of problem (4)** (p.16), with the continuation value `v*_u`
replaced by a function `V`: for a restocking time `τ ≥ 0`,
`v_{u,V}(F; τ) = ∫_0^τ e^{−ρs} S^F(s) [c(Π^F(s)) + h(Π^F(s)) V(J(Π^F(s)))] ds
  + (k_R + u) e^{−ρτ} S^F(τ)`.

**Formalization Note.** Problem (4) is
`E[∫_0^{τ∧ι} c(Π(s)) e^{−ρs} ds + v*_u(Π(ι)) e^{−ρι} 1{ι ≤ τ} + (k_R + u) e^{−ρτ} 1{τ < ι}]`
with `ι` the next observable event; `ι` has survival function `S^F` and hazard `h(Π^F(s))`, and
`Π(ι) = J(Π^F(ι))` by (2). Writing the expectation with this law gives the formula above. -/
noncomputable def objective (u : ℝ) (V : (Fin (P.qm + 1) → ℝ) → ℝ)
    (F : Fin (P.qm + 1) → ℝ) (τ : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..τ,
      Real.exp (-P.rho * s) * P.survival F s *
        (P.runningCost (P.flow F s) +
          P.hazard (P.flow F s) * V (P.jump (P.flow F s)))) +
    (P.kR + u) * Real.exp (-P.rho * τ) * P.survival F τ

/-- `V` is **the value function `v*_u` of problem (4)** for the restocking value `u`: `V` is
measurable, bounded on the probability simplex, and for every shelf inventory distribution `F`,
`V(F) = inf_{τ ∈ ℝ₊} v_{u,V}(F; τ)` (equation (4), p.16), the infimum taken as a greatest lower
bound of real values.

**Formalization Note.** The paper defines `v*_u` as the value of (SP') (an infimum over
predictable stopping times) and characterizes it by (4). The continuation weight
`∫_0^∞ e^{−ρs} S^F(s) h(Π^F(s)) ds = E[e^{−ρι}] ≤ (λ_D̂ + λ_P)/(ρ + λ_D̂ + λ_P) < 1`, so the
right-hand side of (4) is a sup-norm contraction on bounded functions and its bounded solution is
unique on the simplex: it is `v*_u`. -/
structure IsValueFunction (u : ℝ) (V : (Fin (P.qm + 1) → ℝ) → ℝ) : Prop where
  measurable : Measurable V
  bounded : ∃ B : ℝ, ∀ F ∈ stdSimplex ℝ (Fin (P.qm + 1)), |V F| ≤ B
  bellman : ∀ F ∈ stdSimplex ℝ (Fin (P.qm + 1)),
    IsGLB (P.objective u V F '' Set.Ici 0) (V F)

/-- **Feasibility condition 1** (Appendix B, p.47):
`(λ_L c_L + Δp λ_E)/ρ < (c_D + m) λ_D/ρ`. -/
def FC1 : Prop :=
  (P.lamL * P.cL + P.dp * P.lamE) / P.rho < (P.cD + P.m) * P.lamD / P.rho

/-- **Feasibility condition 2** (Appendix B, p.48): `k_R + u < (c_D + m) λ_D/ρ`. -/
def FC2 (u : ℝ) : Prop :=
  P.kR + u < (P.cD + P.m) * P.lamD / P.rho

end Params

end RecordInaccuracy


