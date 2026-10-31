-- Prove2me | Definitions.Def_FamilyGenTest_Pmax
-- name    : FamilyGenTest_Pmax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:49.115005+00:00
-- url     : https://prove2.me/theorems/fb44ec95-cc12-4ffa-a3f5-089109812f4e
-- title:
--   The thresholds $\mathbb P_i^{\min}(\mathbf s)$, $\mathbb P_i^{\max}(\mathbf s)$ (corrected at $r_i^\delta=0$)
-- statement:
--   For $A\ge0$, $B$, $C$ real, the inequality $-Ap^2+Bp-C\ge0$ has the thresholds below. The first row is the formula of p.ec3; the other rows solve the linear inequality in the case $A=0$, where the printed formula divides by zero.
--
--   | Case | Thresholds exist iff | Lower | Upper |
--   |---|---|---|---|
--   | $A>0$ | $B^2\ge4AC$ | $(B-\sqrt{B^2-4AC})/(2A)$ | $(B+\sqrt{B^2-4AC})/(2A)$ |
--   | $A=0,\ B>0$ | always | $C/B$ | $\max(C/B,1)$ |
--   | $A=0,\ B<0$ | always | $\min(C/B,0)$ | $C/B$ |
--   | $A=0,\ B=0$ | $C\le0$ | $0$ | $1$ |
--
--   In the model,
--   $$
--   \Phi_i(\mathbf s)=\alpha_i(\mathbf s)V^*(\mathbf s_1\cup\{i\})-V^*(\mathbf s_0\cup\{i\})+V^*(\mathbf s_2\cup\{i\})-\alpha_i(\mathbf s)V^*(\mathbf s_2\cup\{i\}),
--   $$
--   $$
--   A=r_i^\delta,\quad B=r_i^\delta+d_i-c_i^f+\Phi_i(\mathbf s),\quad C=c_i^s-V^*(\mathbf s_0\cup\{i\})+\sum_{l\in\mathcal I\setminus\mathbf s:\,l\ne i}\bar r_l(\mathbb P_l(\mathbf s)),
--   $$
--   so that $\Psi=AC$ is the $\Psi$ of p.ec3. The **net gain function** is $\mathrm{gap}_i(\mathbf s)(p)=-Ap^2+Bp-C$, and $\mathbb P_i^{\min}(\mathbf s)$, $\mathbb P_i^{\max}(\mathbf s)$ are the thresholds of $(A,B,C)$. The predicate `RiskBetween` says that they exist and that $\mathbb P_i(\mathbf s)$ lies between them.
--
--   These are the closed forms of Theorem 1.
--
--   **Formalization Note** The discriminant condition is kept as a separate predicate because `Real.sqrt` of a negative number is $0$ in Lean. In the code the case $A<0$ falls in the `else` branches, and it does not occur: every theorem assumes `CensoredOrder`, which gives $A\ge0$.
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), Proof of Theorem 1, pp.ec2–ec3

import Mathlib
import Definitions.Def_FamilyGenTest_Vstar

namespace FamilyGenTest

/-- Whether the concave quadratic `−Ap² + Bp − C`, `A ≥ 0`, has real thresholds: `B² ≥ 4AC` if
`A > 0` (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), p.ec3),
and, in the corrected case `A = 0`, always unless `B = 0` and `C > 0`.

**Formalization Note** The case `A = 0` is a correction: Assumption 4 allows `rᵢ^δ = 0`, where the
printed formulas divide by `0`. -/
def QuadExists (A B C : ℝ) : Prop :=
  if 0 < A then 4 * (A * C) ≤ B ^ 2 else B = 0 → C ≤ 0

/-- The lower threshold of `−Ap² + Bp − C ≥ 0`: `(B − √(B² − 4AC))/(2A)` if `A > 0` (Adelman & Wang,
SSRN 4624694, p.ec3). In the corrected case `A = 0`: `C/B` if `B > 0`, `min(C/B, 0)` if `B < 0`, and
`0` if `B = 0`. -/
noncomputable def quadMin (A B C : ℝ) : ℝ :=
  if 0 < A then (B - Real.sqrt (B ^ 2 - 4 * (A * C))) / (2 * A)
  else if 0 < B then C / B
  else if B < 0 then min (C / B) 0
  else 0

/-- The upper threshold of `−Ap² + Bp − C ≥ 0`: `(B + √(B² − 4AC))/(2A)` if `A > 0` (Adelman & Wang,
SSRN 4624694, p.ec3). In the corrected case `A = 0`: `max(C/B, 1)` if `B > 0`, `C/B` if `B < 0`, and
`1` if `B = 0`. -/
noncomputable def quadMax (A B C : ℝ) : ℝ :=
  if 0 < A then (B + Real.sqrt (B ^ 2 - 4 * (A * C))) / (2 * A)
  else if 0 < B then max (C / B) 1
  else if B < 0 then C / B
  else 1

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- `Φᵢ(s) = αᵢ(s)V*(s₁ ∪ {i}) − V*(s₀ ∪ {i}) + V*(s₂ ∪ {i}) − αᵢ(s)V*(s₂ ∪ {i})` (Adelman & Wang,
SSRN 4624694, after (EC.2), p.ec2).

**Formalization Note** `V*` is `0` at an infeasible child (for example `s₀ ∪ {i}` when `ℙᵢ(s) = 1`). -/
noncomputable def Phi (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : ℝ :=
  alpha μ s i * Vstar R μ (test s i 1) - Vstar R μ (test s i 0) + Vstar R μ (test s i 2)
    - alpha μ s i * Vstar R μ (test s i 2)

/-- `B = rᵢ^δ + dᵢ − cᵢᶠ + Φᵢ(s)`, the linear coefficient of (EC.6) (Adelman & Wang, SSRN 4624694,
p.ec3). -/
noncomputable def coefB (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : ℝ :=
  rdelta R i + censoring R i - R.cf i + Phi R μ s i

/-- `C = cᵢˢ − V*(s₀ ∪ {i}) + ∑_{l ∈ I \ s, l ≠ i} r̄_l(ℙ_l(s))`, so that `Ψ = rᵢ^δ C` (Adelman & Wang,
SSRN 4624694, p.ec3). -/
noncomputable def coefC (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : ℝ :=
  R.cs i - Vstar R μ (test s i 0) + ∑ l ∈ (untested s).erase i, rbar R l (risk μ s l)

/-- The net gain function `−rᵢ^δ p² + B p − C` of testing `i` against stopping in `s`, the left side
of (EC.6) at belief `p` (Adelman & Wang, SSRN 4624694, p.ec3). -/
noncomputable def gap (R : Rewards I) (μ : Prior I) (s : State I) (i : I) (p : ℝ) : ℝ :=
  -rdelta R i * p ^ 2 + coefB R μ s i * p - coefC R μ s i

/-- The thresholds of `i` in `s` exist: `(rᵢ^δ + dᵢ − cᵢᶠ + Φᵢ(s))² ≥ 4Ψ` (Adelman & Wang, SSRN 4624694,
p.ec3), corrected at `rᵢ^δ = 0` as in `QuadExists`. -/
def ThresholdsExist (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : Prop :=
  QuadExists (rdelta R i) (coefB R μ s i) (coefC R μ s i)

/-- The lower threshold `ℙᵢᵐⁱⁿ(s)` (Adelman & Wang, SSRN 4624694, p.ec3), corrected at `rᵢ^δ = 0` as
in `quadMin`. -/
noncomputable def Pmin (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : ℝ :=
  quadMin (rdelta R i) (coefB R μ s i) (coefC R μ s i)

/-- The upper threshold `ℙᵢᵐᵃˣ(s)` (Adelman & Wang, SSRN 4624694, p.ec3), corrected at `rᵢ^δ = 0` as
in `quadMax`. -/
noncomputable def Pmax (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : ℝ :=
  quadMax (rdelta R i) (coefB R μ s i) (coefC R μ s i)

/-- `ℙᵢ(s)` lies between the two thresholds of `i` in `s`, which exist (Adelman & Wang, SSRN 4624694,
Theorem 1, p.17). -/
def RiskBetween (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : Prop :=
  ThresholdsExist R μ s i ∧ Pmin R μ s i ≤ risk μ s i ∧ risk μ s i ≤ Pmax R μ s i

end FamilyGenTest


