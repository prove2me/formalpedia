-- Prove2me | Definitions.Def_StochKolmogorov_Extinct_Extinction
-- name    : StochKolmogorov_Extinct_Extinction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:08.411478+00:00
-- url     : https://prove2.me/theorems/45222ed4-e32a-48e8-a5c7-3ff195767214
-- title:
--   §5 — the extinction Lyapunov functions
-- statement:
--   Fix a boundary measure $\mu$, weights $\widehat p_j$ on its surviving species, a weight $\check p$ for missing species, and a small exponent $\theta$. The function used to measure approach to the selected face is
--
--   $$U_\theta(x)=\sum_{i\notin I_\mu}\left(\frac{(1+c^\top x)x_i^{\check p}}{\prod_{j\in I_\mu}x_j^{\widehat p_j}}\right)^\theta,\qquad x\in\mathbb R^{n,\circ}_+.$$
--
--   The module also defines its individual summands, the finite cap $\varsigma=\delta_e^{\check p\theta}/C_U^\theta$, the capped function $\widetilde U_\theta=\min\{\varsigma,U_\theta\}$, and the time averages in (5.3).
--
--   These are the functions in the contraction and supermartingale milestones.
--
--   **Formalization Note** Real powers and division have total Lean values at zero. The source defines $U_\theta$ on the strictly positive orthant, and the theorem statements keep that domain for starting points.
--
--   **Moderation note** The real supremum defining $C_U$ is used with the selected normalized weights, whose sum is at most $\delta_0<1$; this makes the supremum finite and positive.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §5, pp. 21–23, (5.3), Proposition 5.1, Theorem 5.1 proof

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Faces

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

/-- The factor U_i of §5, p. 22. -/
noncomputable def Ui {n : ℕ} (c : SDEState n) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck : ℝ) (i : Fin n) (x : SDEState n) : ℝ :=
  (1 + ∑ j, c j * x j) * x i ^ pcheck / ∏ j ∈ supp mu, x j ^ phat j

/-- The sum U_θ of §5, p. 22. -/
noncomputable def Utheta {n : ℕ} (c : SDEState n) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck θ : ℝ) (x : SDEState n) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ supp mu), (Ui c mu phat pcheck i x) ^ θ

/-- The constant C_U of §5, p. 22. -/
noncomputable def CU {n : ℕ} (c : SDEState n) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) : ℝ :=
  sSup ((fun x : SDEState n => (∏ i ∈ supp mu, x i ^ phat i) /
    (1 + ∑ i, c i * x i)) '' openOrthant n)

/-- The cap ς of §5, p. 22. -/
noncomputable def varsigma {n : ℕ} (c : SDEState n) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck θ δe : ℝ) : ℝ :=
  δe ^ (pcheck * θ) / (CU c mu phat) ^ θ

/-- The capped U_θ of §5, p. 22. -/
noncomputable def Utilde {n : ℕ} (c : SDEState n) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck θ δe : ℝ) (x : SDEState n) : ℝ :=
  min (varsigma c mu phat pcheck θ δe) (Utheta c mu phat pcheck θ x)

/-- The time average of the instantaneous invasion rate in (5.3). -/
noncomputable def lyapAvg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (i : Fin n) (T : ℝ) (x : SDEState n) : ℝ :=
  (1 / T) * ∫ t in (0 : ℝ)..T, ∫ ω,
    (C.f i (X x t.toNNReal ω) - C.sig i i * C.g i (X x t.toNNReal ω) ^ 2 / 2) ∂P

/-- The time average of the c-bracket in (5.3). -/
noncomputable def cAvg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (c : SDEState n) (T : ℝ) (x : SDEState n) : ℝ :=
  (1 / T) * ∫ t in (0 : ℝ)..T, ∫ ω, cBracket C c (X x t.toNNReal ω) ∂P

end StochKolmogorov.Extinct


