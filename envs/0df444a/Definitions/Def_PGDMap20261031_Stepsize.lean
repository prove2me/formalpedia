-- Prove2me | Definitions.Def_PGDMap20261031_Stepsize
-- name    : PGDMap20261031_Stepsize
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-31T13:01:09.706496+00:00
-- url     : https://prove2.me/theorems/4dc35658-7158-415e-9bf2-548b1d1ff393
-- title:
--   Optimal PGD stepsizes, parameter laws, and endpoint conventions
-- statement:
--   For $N\ge2$ and $q\ge0$, the optimal-step target is built from the infimum of the actual crossing set $\{h\in(1,2):A_N(h,q)=B_N(h,q)\}$. The formal obligations assert its existence in that interval, strict optimality over $(0,2)$, crossing uniqueness, monotonicity, scalar root equations, asymptotics and the two-update closed form.
--
--   The one-update problem is stated separately: $1/(1-q)$ is the unique interior optimum for $0\le q<1/2$; for $q\ge1/2$ the infimum is approached at the excluded endpoint $h=2$. No minimizing interpretation is assigned to the crossing-based function at $N=0$ or $N=1$. Limits use horizons $N=n+2$, so all asymptotic terms stay within the intended domain.
-- source:
--   Three author manuscripts dated 2026-10-30: Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty; Optimal Constant Stepsizes for the Exact PGD Residual Curve; Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures. Definitions preceding Theorem 1 in each manuscript.

import Definitions.Def_PGDMap20261031_Curves

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace PGDMap20261031

def optimalStep (N : ℕ) (q : ℝ) : ℝ :=
  sInf {h : ℝ | 1 < h ∧ h < 2 ∧ branchA N h q = branchB N h q}

def IsStrictCurveMin (N : ℕ) (q h : ℝ) : Prop :=
  validStep h ∧ ∀ u, validStep u → u ≠ h → curve N h q < curve N u q

def StepBalanceClaim : Prop :=
  ∀ N q, 2 ≤ N → 0 ≤ q →
    1 < optimalStep N q ∧ optimalStep N q < 2 ∧
    IsStrictCurveMin N q (optimalStep N q) ∧
    branchA N (optimalStep N q) q = branchB N (optimalStep N q) q ∧
    ∀ h, 1 < h → h < 2 → branchA N h q = branchB N h q → h = optimalStep N q

def StepMonotonicityClaim : Prop :=
  (∀ N q₁ q₂, 2 ≤ N → 0 ≤ q₁ → q₁ < q₂ →
    optimalStep N q₁ < optimalStep N q₂) ∧
  (∀ N₁ N₂ q, 2 ≤ N₁ → N₁ < N₂ → 0 ≤ q →
    optimalStep N₁ q < optimalStep N₂ q)

def StepRootEquationsClaim : Prop :=
  ∀ N q h, 2 ≤ N → 0 ≤ q → 1 < h → h < 2 →
    (h = optimalStep N q ↔
      if q = 0 then (h - 1) ^ (2 * (N - 1)) * (1 + 2 * ((N - 1 : ℕ) : ℝ) * h) = 1
      else (h - 1) ^ (2 * (N - 1)) =
        q / (1 + q - (base h q) ^ (-(2 * ((N - 1 : ℕ) : ℤ)))))

def StepAsymptoticsClaim : Prop :=
  (∀ q, 0 ≤ q → Tendsto (fun n : ℕ => optimalStep (n + 2) q) atTop (𝓝 2)) ∧
  (∀ q, 0 < q → Tendsto
    (fun n : ℕ => 2 * ((n + 1 : ℕ) : ℝ) * (2 - optimalStep (n + 2) q))
    atTop (𝓝 (Real.log (1 + 1 / q)))) ∧
  Tendsto
    (fun n : ℕ => 2 * ((n + 1 : ℕ) : ℝ) * (2 - optimalStep (n + 2) 0) -
      Real.log (4 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0)

def TwoUpdateFormulaClaim : Prop :=
  ∀ q, 0 ≤ q → optimalStep 2 q =
    if q = 0 then 3 / 2 else (q - 1 + Real.sqrt (q ^ 2 + q + 1)) / q

def oneStepValues (q : ℝ) : Set ℝ :=
  {v | ∃ h, validStep h ∧ v = curveOne h q}

def OneUpdateClaim : Prop :=
  (∀ q, 0 ≤ q → q < 1 / 2 →
    IsStrictCurveMin 1 q (1 / (1 - q))) ∧
  (∀ q, 1 / 2 ≤ q →
    (∀ h, validStep h → ∃ u, validStep u ∧ curveOne u q < curveOne h q) ∧
    Tendsto (fun h : ℝ => curveOne h q) (𝓝[<] 2) (𝓝 (sInf (oneStepValues q))))

def FullStepsizeTheorem : Prop :=
  StepBalanceClaim ∧ StepMonotonicityClaim ∧ StepRootEquationsClaim ∧
  StepAsymptoticsClaim ∧ TwoUpdateFormulaClaim ∧ OneUpdateClaim

end PGDMap20261031


