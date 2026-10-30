-- Prove2me | Definitions.Def_GhadimiLanAudit_TwoPhase_Problem
-- name    : GhadimiLanAudit_TwoPhase_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:48:36.618388+00:00
-- url     : https://prove2.me/theorems/d874099d-e9d4-438d-baf2-7db15a89a048
-- title:
--   Smooth lower-bounded objective, full noise domain and exact integer parameters
-- statement:
--   Let $E=\mathbb R^n$ with its Euclidean norm, for any finite dimension $n$. A problem consists of an objective $f:E\to\mathbb R$, its actual gradient $g$, a Borel oracle $G:E\times\Xi\to E$, a deterministic starting point $x_1$, and constants $L>0$, $\sigma\ge0$, $\widetilde D>0$. The objective is bounded below and $g$ is $L$-Lipschitz. Neither convexity nor attainment of the infimum is required. Define
--
--   $$f^*=\inf_{x\in E}f(x),\qquad D_f=\sqrt{2(f(x_1)-f^*)/L}.$$
--
--   For accuracy $\epsilon>0$ and failure tolerance $0<\Lambda<1$, define
--
--   $$S=\lceil\log_2(2/\Lambda)\rceil,\quad N=\left\lceil\max\left\{32L^2D_f^2/\epsilon,[32L(\widetilde D+D_f^2/\widetilde D)\sigma/\epsilon]^2\right\}\right\rceil,\quad T=\left\lceil24(S+1)\sigma^2/(\Lambda\epsilon)\right\rceil.$$
--
--   The constant RSG step is the published $\min\{1/L,\widetilde D/(\sigma\sqrt N)\}$ for positive noise, completed by $1/L$ at zero noise. These definitions supply the full-domain model for the counted algorithm.
--
--   **Formalization Note** The optimal value is computed as a real infimum of a nonempty bounded-below range. The Euclidean carrier, actual-gradient smoothness predicate, positive-noise step and distance formula reuse published definitions. The noise carrier may be any measurable space. The logarithm reading and the zero-noise correction are explained in the goal's differences list.
-- source:
--   Ghadimi and Lan, Stochastic First- and Zeroth-Order Methods for Nonconvex Stochastic Programming, arXiv:1309.5549v1, https://arxiv.org/abs/1309.5549v1, p. 2, (1.1) and A1; pp. 6, 8, 12, (2.5), (2.13), (2.24)–(2.26)

import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_GhadimiLan_TwoPhase_Model

open MeasureTheory ProbabilityTheory

namespace GhadimiLanAudit.TwoPhase

/-- Problem (1.1), p. 2: the full noise domain, without convexity or attainment.
The derivative/Lipschitz predicate and Euclidean carrier are published interfaces. -/
structure Problem (n : ℕ) (Ξ : Type*) [MeasurableSpace Ξ] where
  f : GhadimiLan.RSG.E n → ℝ
  g : GhadimiLan.RSG.E n → GhadimiLan.RSG.E n
  G : GhadimiLan.RSG.E n → Ξ → GhadimiLan.RSG.E n
  x1 : GhadimiLan.RSG.E n
  L : ℝ
  σ : ℝ
  Dt : ℝ
  smooth : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L
  L_pos : 0 < L
  sigma_nonneg : 0 ≤ σ
  Dt_pos : 0 < Dt
  bounded_below : BddBelow (Set.range f)
  oracle_measurable : Measurable (Function.uncurry G)

/-- The actual optimal value (1.1), computed from f. The range is nonempty and
bounded below in every Problem, so the real infimum is a genuine GLB. -/
noncomputable def optimalValue {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) : ℝ := sInf (Set.range P.f)

/-- Reuse (2.5), with the computed optimal value. -/
noncomputable def distanceScale {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) : ℝ := GhadimiLan.RSG.Df P.f P.x1 (optimalValue P) P.L

/-- (2.13) completed only at zero noise. No call is made with this step if N = 0. -/
noncomputable def completedStep {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (N : ℕ) : ℝ :=
  if P.σ = 0 then 1 / P.L else GhadimiLan.TwoPhase.rsgStep P.L P.Dt P.σ N

/-- (2.24), log read in base two as required on p. 13. -/
noncomputable def runCount (Λ : ℝ) : ℕ := Nat.ceil (Real.logb 2 (2 / Λ))

/-- (2.25), including both terms, square and ceiling. -/
noncomputable def iterationCount {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (ε : ℝ) : ℕ :=
  Nat.ceil (max (32 * P.L ^ 2 * distanceScale P ^ 2 / ε)
    ((32 * P.L * (P.Dt + distanceScale P ^ 2 / P.Dt) * P.σ / ε) ^ 2))

/-- (2.26), retaining S+1 and the ceiling. -/
noncomputable def validationCount {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (ε Λ : ℝ) : ℕ :=
  Nat.ceil (24 * ((runCount Λ : ℝ) + 1) * P.σ ^ 2 / (Λ * ε))

end GhadimiLanAudit.TwoPhase


