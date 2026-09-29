-- Prove2me | Definitions.Def_AvramDividend_BailOut_BailOutProblem
-- name    : AvramDividend_BailOut_BailOutProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:02:30.771521+00:00
-- url     : https://prove2.me/theorems/a213490d-d976-4830-922f-390cef461141
-- title:
--   The dividend problem with bail-out loans (2.4) and the double-barrier strategy $\bar\pi_{0,a}$
-- statement:
--   Fix a spectrally negative Lévy process $X$ on $(\Omega,\mathcal F,\mathbb F,P)$, a discount rate $q$, a cost $\varphi$ per unit of injected capital and initial capital $x\ge0$.
--
--   A **policy** $\bar\pi=(L,R)$ is a pair of nondecreasing $\mathbb F$-adapted processes with $L_0=R_0=0$, where $R$ (cumulative injected capital) is right-continuous and $L$ (cumulative dividends) is left-continuous. The **controlled risk process** is
--
--   $$V_t=x+X_t-L_t+R_t .$$
--
--   For a nondecreasing path $A$ with $A_0=0$, $\int_{[0,\infty)}e^{-qt}\,dA_t\in[0,\infty]$ is the integral against the Stieltjes measure of $A$, including the jump $A_{0+}-A_0$ at time $0$. A policy is **admissible** from $x$ if, almost surely, $V_t\ge0$ for all $t>0$ and $\int_0^\infty e^{-qt}\,dR_t<\infty$ (2.3). Its **value** is
--
--   $$\bar v_{\bar\pi}(x)=E\Bigl[\int_0^\infty e^{-qt}\,dL_t\Bigr]-\varphi\,E\Bigl[\int_0^\infty e^{-qt}\,dR_t\Bigr],$$
--
--   and the **value function of the bail-out problem** (2.4) is $\bar v_*(x)=\sup_{\bar\pi}\bar v_{\bar\pi}(x)$, the supremum over admissible policies from $x$.
--
--   Write $V_{t+}=x+X_t-L_{t+}+R_t$ ($t\ge0$) for the risk process right after the dividend decision at time $t$, where $L_{t+}$ is the right limit of $L$; at $t=0$ it is the capital after the initial lump sum. A policy is the **double-barrier strategy** $\bar\pi_{0,a}$ at level $a\ge0$ from $x$ if, almost surely, it satisfies all of the following (the two-sided Skorokhod problem on $[0,a]$ for the path $x+X$: pay out or in the minimal amount of capital that keeps the risk process in $[0,a]$):
--
--   1. $V_t\in[0,a]$ for all $t>0$ and $V_{t+}\in[0,a]$ for all $t\ge0$;
--   2. the Stieltjes measure $dL$ (including its atom $L_{0+}$ at time $0$) is carried by $\{t\ge0:V_{t+}=a\}$;
--   3. $dR$ is carried by $\{t\ge0:V_{t+}=0\}$;
--   4. $dL$ and $dR$ are mutually singular.
--
--   When $x>a$ this forces the lump sum $(x-a)^+$ to be paid at time $0$. For $a>0$, $(L,R)$ is the doubly reflected Lévy process of (4.2).
--
--   These are the objects of the goal theorem: the problem (2.4) and the strategy claimed to be optimal.
--
--   **Formalization Note** The two expectations are computed in $[0,\infty]$ and the value in the extended reals. It agrees with the paper's $E[\int e^{-qt}dL-\varphi\int e^{-qt}dR]$ whenever that expression is defined. A policy with both expectations infinite is assigned $-\infty$; this cannot change the supremum, because the optimal policy has finite value. The policy conditions (monotonicity, one-sided continuity, adaptedness) are required for every $\omega$; $V_t\ge0$, (2.3) and the barrier conditions 1–4 almost surely (the filtration is complete, so null-set modifications stay adapted). Conditions 2–3 use the exact contact sets of $V_{t+}$, as in the construction of pp. 10–11: the closure-of-support phrasing of (4.2) alone, or contact sets of the left-continuous $V_t$, would also admit non-minimal pairs (extra lump dividends at a jump time of $X$, or at a time when $V_t=a$), which have a strictly smaller value. Condition 4 is automatic for $a>0$. For $a=0$ it selects the paper's policy that keeps the risk process at zero (p. 11, Remark), $L_t=x\mathbf 1_{\{t>0\}}+dt$, $R=S$. Without it, adding the same increasing process to $L$ and $R$ would still satisfy conditions 1–3.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 3 (policies, admissibility (2.3), value), p. 4 (problem (2.4), double barrier strategy), pp. 10–11 (Section 4, eq. (4.2) and the construction, Remark)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

/-- Extension of a path `A : [0, ∞) → ℝ` to the real line by `0` on `(-∞, 0)`. -/
noncomputable def pathExt (A : ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then 0 else A t.toNNReal

open Classical in
/-- The Stieltjes measure `dA` of a nondecreasing path `A` with `A 0 = 0`, built from the
right-continuous version of `pathExt A`. It lives on `[0, ∞)` and its atom at `0` is the jump
`A(0+) - 0`, so lump sums paid at time `0` are counted. (Junk value `0` if `pathExt A` is not
monotone; every policy path is monotone.) -/
noncomputable def pathMeasure (A : ℝ≥0 → ℝ) : Measure ℝ :=
  if h : Monotone (pathExt A) then h.stieltjesFunction.measure else 0

/-- The discounted Laplace–Stieltjes integral `∫_{[0,∞)} e^{-qt} dA_t ∈ [0, ∞]`. -/
noncomputable def discountedIntegral (q : ℝ) (A : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (Real.exp (-q * t)) ∂(pathMeasure A)

/-- A dividend/bail-out policy `π̄ = (L, R)`: cumulative dividends `L` and cumulative injected
capital `R`. -/
structure Policy (Ω : Type*) where
  L : ℝ≥0 → Ω → ℝ
  R : ℝ≥0 → Ω → ℝ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The policy conditions of p. 3: `L` and `R` are nondecreasing, `𝔽`-adapted, start at
`L_0 = R_0 = 0`, `R` is right-continuous and `L` is left-continuous. -/
def IsPolicy (𝓕 : Filtration ℝ≥0 mΩ) (π : Policy Ω) : Prop :=
  (∀ ω, Monotone (fun t => π.L t ω)) ∧ (∀ ω, Monotone (fun t => π.R t ω)) ∧
    (∀ ω, π.L 0 ω = 0) ∧ (∀ ω, π.R 0 ω = 0) ∧
    (∀ ω (t : ℝ≥0), ContinuousWithinAt (fun s => π.L s ω) (Set.Iic t) t) ∧
    (∀ ω (t : ℝ≥0), ContinuousWithinAt (fun s => π.R s ω) (Set.Ici t) t) ∧
    Adapted 𝓕 π.L ∧ Adapted 𝓕 π.R

/-- The controlled risk process `V_t = x + X_t - L_t + R_t` (p. 3; `X` starts at `0`, so this is
the paper's `X_t - L_t + R_t` under `P_x`). -/
def controlled (Lv : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (π : Policy Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x + Lv.X t ω - π.L t ω + π.R t ω

/-- Admissible policies `Π̄` (p. 3): policies with `V_t ≥ 0` for `t > 0` and
`∫_0^∞ e^{-qt} dR_t < ∞`, `P`-almost surely, (2.3). -/
def IsAdmissible (Lv : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (π : Policy Ω) : Prop :=
  IsPolicy 𝓕 π ∧ (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → 0 ≤ controlled Lv x π t ω) ∧
    ∀ᵐ ω ∂P, discountedIntegral q (fun t => π.R t ω) < ∞

/-- The value `v̄_π̄ = E[∫_0^∞ e^{-qt} dL_t] - φ E[∫_0^∞ e^{-qt} dR_t]` of a policy (p. 3), computed
in `EReal` from the two expectations in `[0, ∞]`. It agrees with the paper's
`E[∫e^{-qt}dL - φ∫e^{-qt}dR]` whenever that expectation is defined; a policy with both
expectations infinite gets `⊤ - ⊤ = ⊥`. -/
noncomputable def policyValue (P : Measure Ω) (q φ : ℝ) (π : Policy Ω) : EReal :=
  ((∫⁻ ω, discountedIntegral q (fun t => π.L t ω) ∂P : ℝ≥0∞) : EReal) -
    (φ : EReal) * ((∫⁻ ω, discountedIntegral q (fun t => π.R t ω) ∂P : ℝ≥0∞) : EReal)

/-- The value function of the bail-out problem (2.4): `v̄_*(x) = sup_{π̄ ∈ Π̄} v̄_π̄(x)`, the
supremum in `EReal` over admissible policies from initial capital `x`. -/
noncomputable def optimalValue (Lv : SpectrallyNegativeLevy P 𝓕) (q φ x : ℝ) : EReal :=
  ⨆ π : {π : Policy Ω // IsAdmissible Lv q x π}, policyValue P q φ π.1

/-- The risk process right after the dividend decision at time `t ≥ 0`:
`V_{t+} = x + X_t - L_{t+} + R_t`, with `L_{t+}` the right limit of the (left-continuous) dividend
path; it is the right-continuous version of `V` (at `t = 0` it is the capital after the initial
lump sum). -/
noncomputable def controlledRight (Lv : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (π : Policy Ω)
    (t : ℝ) (ω : Ω) : ℝ :=
  x + Lv.X t.toNNReal ω - Function.rightLim (pathExt (fun s => π.L s ω)) t + π.R t.toNNReal ω

/-- `π̄ = (L, R)` is the double-barrier strategy `π̄_{0,a}` from initial capital `x` (pp. 4, 10–11):
a policy which, `P`-almost surely, solves the two-sided Skorokhod problem on `[0, a]` for the path
`x + X`: `V_t ∈ [0, a]` for all `t > 0` and `V_{t+} ∈ [0, a]` for all `t ≥ 0`; the Stieltjes
measure `dL` (which includes the initial lump sum `L_{0+} = (x - a)^+`) is carried by
`{t ≥ 0 : V_{t+} = a}` and `dR` by `{t ≥ 0 : V_{t+} = 0}` — "pay out or in the minimal amount of
capital required to keep the risk process between 0 and a" (p. 4; (4.2) and the construction of
pp. 10–11); and `dL`, `dR` are mutually singular (automatic for `a > 0`; for `a = 0` it pins the
policy that keeps the risk process at zero, p. 11 Remark). -/
def IsDoubleBarrier (Lv : SpectrallyNegativeLevy P 𝓕) (a x : ℝ) (π : Policy Ω) : Prop :=
  IsPolicy 𝓕 π ∧ ∀ᵐ ω ∂P,
    (∀ t : ℝ≥0, 0 < t → controlled Lv x π t ω ∈ Set.Icc 0 a) ∧
    (∀ t : ℝ, 0 ≤ t → controlledRight Lv x π t ω ∈ Set.Icc 0 a) ∧
    pathMeasure (fun t => π.L t ω) {t : ℝ | 0 ≤ t ∧ controlledRight Lv x π t ω = a}ᶜ = 0 ∧
    pathMeasure (fun t => π.R t ω) {t : ℝ | 0 ≤ t ∧ controlledRight Lv x π t ω = 0}ᶜ = 0 ∧
    pathMeasure (fun t => π.L t ω) ⟂ₘ pathMeasure (fun t => π.R t ω)

end AvramDividend.BailOut


