-- Prove2me | Definitions.Def_MFCLiquidation_Model
-- name    : MFCLiquidation_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:45.395204+00:00
-- url     : https://prove2.me/theorems/271ce570-20cb-492b-98b1-a83e7e590b82
-- title:
--   The liquidation model: random data, admissible strategies $\mathscr A_t$, state, cost $J(t,Z)$, value $V(t,\mathcal X)$, BSDE solutions and the candidate strategy
-- statement:
--   This module fixes the stochastic control problem of the paper.
--
--   1. **Random data.** A probability space $(\Omega,\mathcal F,P)$ with a horizon $T>0$, a Brownian motion $W$, a square-integrable initial position $x_0$ independent of $W$, the filtration $\mathcal F_s=\sigma(x_0)\vee\sigma(W_r:r\le s)$ augmented by the $P$-null sets, and a progressively measurable volatility $\sigma$ with $\mathbb E\int_0^T\sigma_s^2\,ds<\infty$ (possibly degenerate). This is item 3 of the standing assumption.
--   2. **Admissible strategies** (2.11). $Z\in\mathscr A_t$ if $Z$ is a càdlàg $\mathbb F$-semimartingale starting at $t$ ($Z_s=0$ for $s<t$), with $\mathbb E[[Z]_T]<\infty$ and $\mathbb E[\sup_{t\le s\le T}|Z_s|^2]<\infty$.
--   3. **State** (2.10)/(2.18). From an $\mathcal F_t$-measurable square-integrable initial state $\mathcal X=(X_{t-},Y_{t-},C_{t-})$,
--   $$d\mathcal X_s=(\mathcal H\mathcal X_s+\overline{\mathcal H}\,\mathbb E[\mathcal X_s]+\mathcal G)\,ds+\mathcal D_s\,dW_s+\mathcal K\,dZ_s,\qquad \mathcal D_s=(0,\sigma_s,0)^\top,$$
--   on $[t,T]$, written in integral form.
--   4. **Cost and value** (2.9), (2.12).
--   $$J(t,Z)=\mathbb E\Big[\int_t^T\big(Y_{s-}\,dZ_s+\tfrac{\gamma_2}2\,d[Z]_s+\sigma_s\,d[Z,W]_s\big)+\int_t^T\lambda X_s^2\,ds\Big],\qquad V(t,\mathcal X)=\inf J(t,Z),$$
--   the infimum over $Z\in\mathscr A_t$ whose state liquidates, $X_T=0$. The integrals include the initial jump at $t$.
--   5. **Coefficients.** A tuple $(A,B,D,F,Z^F)$ solving (2.14), (2.15), (2.16) and the BSDE (2.17), the matrices $A_s$, $B_s$, the vector $D_s$, the feedback vectors $I^A_s,I^B_s,I^D_s$, and the right side of (2.20), $\operatorname{Var}(\mu)(A_t)+\bar\mu^\top B_t\bar\mu+D_t^\top\bar\mu+\mathbb E[F_t]$ with $\operatorname{Var}(\mu)(A)=\int(x-\bar\mu)^\top A(x-\bar\mu)\,\mu(dx)$.
--   6. **Candidate strategy.** A run follows (2.21)–(2.22) if its initial jump is $\Delta\tilde Z_t=-\frac{I^A_t}{\tilde a}(\mathcal X_{t-}-\bar\mu)-\frac{I^B_t}{a}\bar\mu-\frac{I^D_t}{a}$, its terminal jump is $X_{T-}$, it has no jump in $(t,T)$, and on $(t,T)$
--   $$d\tilde Z_s=\Big(-\tfrac{\dot I^A_s}{\tilde a}(\mathcal X_s-\mathbb E\mathcal X_s)-\tfrac{\dot I^B_s}{a}\mathbb E\mathcal X_s-\tfrac{\dot I^D_s}{a}-\tfrac{I^A_s}{\tilde a}\mathcal H(\mathcal X_s-\mathbb E\mathcal X_s)-\tfrac{I^B_s}{a}\big((\mathcal H+\overline{\mathcal H})\mathbb E\mathcal X_s+\mathcal G\big)\Big)ds-\tfrac{I^A_s}{\tilde a}\mathcal D_s\,dW_s .$$
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$. Because `leftLim` at $0$ is the value at $0$, the initial jump is costed explicitly: the realized cost is $Y_{t-}Z_t+\frac{\gamma_2}2Z_t^2+\int_{(t,T]}Y_{s-}\,dZ_s+\frac{\gamma_2}2[Z]_{(t,T]}+[Z,N]_{(t,T]}+\int_t^T\lambda X_s^2\,ds$, with $N=\int\sigma\,dW$ (Kunita–Watanabe: $\int\sigma\,d[Z,W]=[Z,N]$). A `Run` bundles $Z$, the state, $N$, $\int Y_-dZ$, $[Z]$ and $[Z,N]$; they are unique for $Z\in\mathscr A_t$. The state is adapted from $t$ on. $J$ is a Bochner expectation; $V$ is an infimum in $\overline{\mathbb R}$ (`EReal`), so an empty or unbounded-below feasible set gives $\pm\infty$ rather than $0$. The filtration adjoins $\sigma(x_0)$ at time $0$, since $x_0$ is independent of $W$ but must be known at time $0$. The BSDE solution is sought among integrable adapted $F$ with $\int Z^F\,dW$ a true martingale (the page says square integrable, which is impossible in general when $\sigma$ is only square integrable).
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, setting p.5; (2.9)–(2.12), p.8; standing assumption item 3, p.10; (2.13) and (2.17), pp.9–10; (2.18), p.10; (2.20)–(2.22), p.11; Var(μ)(A), p.5; Proposition 4.1, p.16

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod
import Definitions.Def_KurtzProtter91_Integrals_Semimartingale
import Definitions.Def_EthierKurtz_HasCrossVariation
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati
import Definitions.Def_MFCLiquidation_IsItoIntegral

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal
open KurtzProtter91.Integrals

namespace MFCLiquidation

/-- The random data of the model: a probability measure `P`, the filtration `𝔽`, the Brownian
motion `W`, the initial position `x₀`, the volatility `σ` and the horizon `T`,
arXiv:2207.00446v3, pp.5, 10.

Formalization Note: time is `ℝ≥0`, as in the published `KurtzProtter91` and `EthierKurtz`
definitions; only `[0, T]` matters. Bundling `T` here keeps it after the threshold on `α` in the
statement of Theorem 2.3. -/
structure Model (Ω : Type*) [m : MeasurableSpace Ω] where
  P : Measure Ω
  𝓕 : Filtration ℝ≥0 m
  W : ℝ≥0 → Ω → ℝ
  x₀ : Ω → ℝ
  σ : ℝ≥0 → Ω → ℝ
  T : ℝ≥0

namespace Model

variable {Ω : Type*} [m : MeasurableSpace Ω] (D : Model Ω)

/-- The mean inventory `E[x₀]`. -/
noncomputable def Ex0 : ℝ := ∫ ω, D.x₀ ω ∂D.P

/-- Item 3 of the standing assumption, arXiv:2207.00446v3, p.10, with the setting of p.5: `P` is a
probability measure, `T > 0`, `W` is a Brownian motion, `x₀` is square integrable and independent
of `W`, `σ` is progressively measurable with `E∫₀ᵀσ² ds < ∞` (it may be degenerate, footnote 5),
and `𝔽` is the augmentation of the filtration generated by `x₀` and `W`.

Formalization Note: the page calls `𝔽` "the augmented Brownian filtration", but `x₀` is independent
of `W` and the initial jump (2.21) at `t = 0` must be `𝓕₀`-measurable, so `x₀` is adjoined at time
`0`. Null sets are taken among the measurable sets of the ambient space. Progressive measurability
concerns `[0, T]` only. -/
structure Assumption : Prop where
  prob : IsProbabilityMeasure D.P
  T_pos : 0 < D.T
  brownian : IsBrownianReal D.W D.P
  x₀_sq : MemLp D.x₀ 2 D.P
  x₀_indep : IndepFun D.x₀ (fun ω s => D.W s ω) D.P
  filtration : ∀ s, D.𝓕 s =
    MeasurableSpace.comap D.x₀ inferInstance ⊔
      (⨆ r : {r : ℝ≥0 // r ≤ s}, MeasurableSpace.comap (D.W r) inferInstance) ⊔
      MeasurableSpace.generateFrom {N | MeasurableSet N ∧ D.P N = 0}
  σ_prog : IsStronglyProgressive D.𝓕 (fun s ω => D.σ (min s D.T) ω)
  σ_sq : ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) (D.T : ℝ),
    ENNReal.ofReal (D.σ s.toNNReal ω ^ 2)) ∂D.P < ⊤

/-- `𝒳 = (X_{t−}, Y_{t−}, C_{t−})` is an admissible random initial state at time `t`,
arXiv:2207.00446v3, p.8: `𝓕_t`-measurable and square integrable. -/
def IsInitialState (t : ℝ≥0) (ξ : Ω → Fin 3 → ℝ) : Prop :=
  Measurable[D.𝓕 t] ξ ∧ ∀ i, MemLp (fun ω => ξ ω i) 2 D.P

/-- For a strategy `Z`, the process `Z_{(s ∨ t) ∧ T} − Z_t`: the trades strictly after the initial
time `t`, up to and including `T`. It is zero up to `t` and constant after `T`, so its integrals
and brackets over `[0, T]` are those of `Z` over `(t, T]`.

Formalization Note: `Function.leftLim` at `0` returns the value at `0`, so `[0, T]`-integrals of
`Z` itself would silently drop the initial jump when `t = 0`. The jump at `t` is therefore costed
explicitly in `Run.cost`, and the integrals are taken over `(t, T]`. -/
def postTrades (T t : ℝ≥0) (Z : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => Z (min (max s t) T) ω - Z t ω

/-- `Z ∈ 𝒜_t`, (2.11), arXiv:2207.00446v3, p.8: `Z` is a cadlag `𝔽`-semimartingale starting at `t`
with `E[[Z]_T] < ∞` and `E[sup_{t≤s≤T} |Z_s|²] < ∞`.

Formalization Note: "starting at `t`" is `Z_s = 0` for `s < t`, i.e. `Z_{t−} = 0`, so the initial
jump is `Z_t`, also when `t = 0`. Thus `[Z]_T = Z_t² + [postTrades]_T`. The liquidation constraint
is not part of `𝒜_t`; it is `Run.Liquidates`, as in (2.10). -/
def Admissible (t : ℝ≥0) (Z : ℝ≥0 → Ω → ℝ) : Prop :=
  IsSemimartingale D.𝓕 D.P (fun s ω (_ : Fin 1) => Z s ω) ∧
  (∀ s < t, ∀ ω, Z s ω = 0) ∧
  (∃ Q : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasCrossVariation D.P (postTrades D.T t Z) (postTrades D.T t Z) Q ∧
    ∫⁻ ω, ENNReal.ofReal (Z t ω ^ 2 + Q D.T ω) ∂D.P < ⊤) ∧
  ∫⁻ ω, (⨆ s ∈ Set.Icc t D.T, ENNReal.ofReal (Z s ω ^ 2)) ∂D.P < ⊤

end Model

/-- The expectation `E[Y]` of a vector-valued random variable, componentwise. For a law `μ` on
`ℝ³` this gives the vector of expected values `μ̄ = vecMean μ id`, arXiv:2207.00446v3, p.5. -/
noncomputable def vecMean {E : Type*} [MeasurableSpace E] (μ : Measure E) (Y : E → Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  fun i => ∫ x, Y x i ∂μ

/-- `Var(μ)(A) = ∫(x − μ̄)ᵀA(x − μ̄) μ(dx)`, arXiv:2207.00446v3, p.5. -/
noncomputable def lawVar (μ : Measure (Fin 3 → ℝ)) (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∫ x, (x - vecMean μ id) ⬝ᵥ (A *ᵥ (x - vecMean μ id)) ∂μ

/-- A strategy together with everything determined by it (up to indistinguishability): `Z`, the
state `𝒳 = (X, Y, C)`, the Itô integral `N = ∫σ dW`, the integral `∫_{(t,·]} Y_{s−} dZ_s`, the
bracket `[Z]` on `(t, ·]` and the bracket `[Z, N]` on `(t, ·]`.

Formalization Note: the cost needs these objects; they exist and are unique for every `Z ∈ 𝒜_t`,
so an infimum over runs is an infimum over strategies. -/
structure Run (Ω : Type*) where
  Z : ℝ≥0 → Ω → ℝ
  X : ℝ≥0 → Ω → Fin 3 → ℝ
  N : ℝ≥0 → Ω → ℝ
  intY : ℝ≥0 → Ω → ℝ
  brZ : ℝ≥0 → Ω → ℝ
  covZN : ℝ≥0 → Ω → ℝ

namespace Run

variable {Ω : Type*} [m : MeasurableSpace Ω] (p : Params) (D : Model Ω)

/-- `R` is a run of a strategy `Z ∈ 𝒜_t` from the initial state `ξ` at time `t`:

1. `Z ∈ 𝒜_t`, (2.11), and `N = ∫σ dW`;
2. `𝒳` is cadlag, adapted from `t` on, integrable on `[t, T]`, equal to `ξ` before `t`, and solves the state
   equation (2.18), the matrix form of (2.10), arXiv:2207.00446v3, pp.8, 10, on `[t, T]`:
   `𝒳_s = ξ + ∫_t^s (ℋ𝒳_r + ℋ̄E[𝒳_r] + 𝒢) dr + 𝒟-term + 𝒦 Z_s`, where `Z_{t−} = 0` and the
   `𝒟`-term is `(0, N_s − N_t, 0)ᵀ`;
3. `intY = ∫ Y_{s−} dZ_s` over `(t, ·]`, as a limit of left-point Riemann sums, `brZ = [Z]` over
   `(t, ·]` and `covZN = [Z, N]` over `(t, ·]`.

Formalization Note: `𝒳` before `t` plays no role except that its constant value `ξ` is `𝒳_{t−}`;
adaptedness is asked from `t` on only, since `ξ` is merely `𝓕_t`-measurable.
The expectation in (2.18) is the Bochner integral, hence the integrability clause. -/
structure IsRun (t : ℝ≥0) (ξ : Ω → Fin 3 → ℝ) (R : Run Ω) : Prop where
  admissible : D.Admissible t R.Z
  ito : IsItoIntegral D.P D.𝓕 D.W D.T D.σ R.N
  cadlag : ∀ ω, IsCadlag fun s => R.X s ω
  adapted : ∀ s, t ≤ s → StronglyMeasurable[D.𝓕 s] (R.X s)
  integrable : ∀ s ∈ Set.Icc t D.T, ∀ i, Integrable (fun ω => R.X s ω i) D.P
  before : ∀ s < t, ∀ ω, R.X s ω = ξ ω
  state : ∀ᵐ ω ∂D.P, ∀ s ∈ Set.Icc t D.T,
    R.X s ω = ξ ω
      + (fun i => ∫ r in (t : ℝ)..(s : ℝ),
          (p.H *ᵥ R.X r.toNNReal ω + p.Hbar *ᵥ vecMean D.P (R.X r.toNNReal) + p.G D.Ex0) i)
      + ![0, R.N s ω - R.N t ω, 0]
      + R.Z s ω • p.K
  intY_eq : HasStochIntegral (k := 1) (m := 1) D.P
    (fun s ω _ _ => R.X s ω 1)
    (fun s ω _ => Model.postTrades D.T t R.Z s ω)
    (fun s ω _ => R.intY s ω)
  brZ_eq : EthierKurtz.HasCrossVariation D.P
    (Model.postTrades D.T t R.Z) (Model.postTrades D.T t R.Z) R.brZ
  covZN_eq : EthierKurtz.HasCrossVariation D.P (Model.postTrades D.T t R.Z) R.N R.covZN

/-- The liquidation constraint `X_T = 0` of (2.10), arXiv:2207.00446v3, p.8. -/
def Liquidates (R : Run Ω) : Prop :=
  ∀ᵐ ω ∂D.P, R.X D.T ω 0 = 0

/-- The realized cost whose expectation is `J(t, Z)`, arXiv:2207.00446v3, p.8:
`∫_t^T (Y_{s−} dZ_s + (γ₂/2) d[Z]_s + σ_s d[Z, W]_s) + ∫_t^T λX_s² ds`, the integrals over the
closed interval `[t, T]` as in (4.1), p.16.

Formalization Note: the atom at `t` of the first two integrals is written out,
`Y_{t−} ΔZ_t + (γ₂/2)(ΔZ_t)² = ξ₂ Z_t + (γ₂/2) Z_t²`, and `[Z, W]` has no atom at `t` as `W` is
continuous. For the progressive integrand `σ`, the third term is `[Z, N]`, by the Kunita–Watanabe
identity `[Z, ∫σ dW] = ∫σ d[Z, W]`. -/
noncomputable def cost (t : ℝ≥0) (ξ : Ω → Fin 3 → ℝ) (R : Run Ω) (ω : Ω) : ℝ :=
  ξ ω 1 * R.Z t ω + p.γ₂ / 2 * R.Z t ω ^ 2
    + R.intY D.T ω + p.γ₂ / 2 * R.brZ D.T ω + R.covZN D.T ω
    + ∫ r in (t : ℝ)..(D.T : ℝ), p.lam * R.X r.toNNReal ω 0 ^ 2

/-- The cost functional `J(t, Z)`, arXiv:2207.00446v3, p.8, a Bochner expectation. The realized
cost is integrable on every run: this is part of `proposition_4_1`. -/
noncomputable def J (t : ℝ≥0) (ξ : Ω → Fin 3 → ℝ) (R : Run Ω) : ℝ :=
  ∫ ω, cost p D t ξ R ω ∂D.P

end Run

/-- The value function `V(t, 𝒳)`, (2.12), arXiv:2207.00446v3, p.8: the infimum of `J(t, Z)` over
`Z ∈ 𝒜_t` subject to (2.10), including `X_T = 0`.

Formalization Note: an infimum in `EReal`, so that no boundedness is presupposed: on an empty or
unbounded-below feasible set the value would be `⊤` or `⊥`, not the junk `0` of a real `sInf`. -/
noncomputable def V {Ω : Type*} [MeasurableSpace Ω] (p : Params) (D : Model Ω) (t : ℝ≥0)
    (ξ : Ω → Fin 3 → ℝ) : EReal :=
  ⨅ (R : Run Ω) (_ : Run.IsRun p D t ξ R ∧ Run.Liquidates D R), (Run.J p D t ξ R : EReal)

/-- `(F, Z^F)` solves the BSDE (2.17), arXiv:2207.00446v3, p.10, for the coefficients
`A₁₁, D₁, D₃`: `F` is adapted and integrable, `M = ∫Z^F dW` is a true martingale, and
`F_s = ∫_s^T g_r dr − (M_T − M_s)` for every `s ∈ [0, T]`, a.s.

Formalization Note: this is a **correction** of "square integrable" on p.9. For `σ` merely square
integrable, `σ²` is merely integrable, and no square-integrable solution exists in general; see the
Differences list of `theorem_2_3`. The martingale property of `M` is what singles out the solution
`F_s = E[∫_s^T g_r dr | 𝓕_s]`. -/
structure SolvesF {Ω : Type*} [MeasurableSpace Ω] (p : Params) (D : Model Ω)
    (A₁₁ D₁ D₃ : ℝ → ℝ) (F ZF M : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : ∀ s ≤ D.T, Measurable[D.𝓕 s] (F s)
  integrable : ∀ s ≤ D.T, Integrable (F s) D.P
  ito : IsItoIntegral D.P D.𝓕 D.W D.T ZF M
  eqn : ∀ s ≤ D.T, ∀ᵐ ω ∂D.P,
    F s ω = (∫ r in (s : ℝ)..(D.T : ℝ),
        p.genF D.Ex0 (D.σ r.toNNReal ω) (A₁₁ r) (D₁ r) (D₃ r))
      - (M D.T ω - M s ω)

/-- The coefficient processes `A, B, D, F` of (2.14)–(2.17), arXiv:2207.00446v3, pp.9–10. -/
structure Coeffs (Ω : Type*) where
  A₁₁ : ℝ → ℝ
  A₁₃ : ℝ → ℝ
  A₃₃ : ℝ → ℝ
  B₁₁ : ℝ → ℝ
  B₁₃ : ℝ → ℝ
  B₃₃ : ℝ → ℝ
  D₁ : ℝ → ℝ
  D₃ : ℝ → ℝ
  F : ℝ≥0 → Ω → ℝ
  ZF : ℝ≥0 → Ω → ℝ
  M : ℝ≥0 → Ω → ℝ

namespace Coeffs

variable {Ω : Type*} [MeasurableSpace Ω] (p : Params) (D : Model Ω) (c : Coeffs Ω)

/-- `c` solves (2.14), (2.15), the corrected (2.16) and (2.17), arXiv:2207.00446v3, pp.9–10. -/
def Solves : Prop :=
  p.SolvesA D.T c.A₁₁ c.A₁₃ c.A₃₃ ∧
  p.SolvesB D.T c.B₁₁ c.B₁₃ c.B₃₃ ∧
  p.SolvesD D.T D.Ex0 c.B₁₁ c.B₁₃ c.B₃₃ c.D₁ c.D₃ ∧
  SolvesF p D c.A₁₁ c.D₁ c.D₃ c.F c.ZF c.M

/-- The `3 × 3` matrix `A_s`. -/
noncomputable def matA (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  p.symMat (c.A₁₁ s) (c.A₁₃ s) (c.A₃₃ s)

/-- The `3 × 3` matrix `B_s`. -/
noncomputable def matB (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  p.symMat (c.B₁₁ s) (c.B₁₃ s) (c.B₃₃ s)

/-- The vector `D_s`. -/
noncomputable def vecD (s : ℝ) : Fin 3 → ℝ := p.dVec (c.D₁ s) (c.D₃ s)

/-- The row vector `I^A_s`, arXiv:2207.00446v3, p.11. -/
noncomputable def iA (s : ℝ) : Fin 3 → ℝ := p.IA (c.A₁₁ s) (c.A₁₃ s)

/-- The row vector `I^B_s`, arXiv:2207.00446v3, p.11. -/
noncomputable def iB (s : ℝ) : Fin 3 → ℝ := p.IB (c.B₁₁ s) (c.B₁₃ s) (c.B₃₃ s)

/-- The scalar `I^D_s`, arXiv:2207.00446v3, p.11. -/
noncomputable def iD (s : ℝ) : ℝ := p.ID D.Ex0 (c.D₁ s) (c.D₃ s)

/-- The right side of (2.20), arXiv:2207.00446v3, p.11, at time `t` for the law `μ`:
`Var(μ)(A_t) + μ̄ᵀB_tμ̄ + D_tᵀμ̄ + E[F_t]`. -/
noncomputable def valueFormula (t : ℝ≥0) (μ : Measure (Fin 3 → ℝ)) : ℝ :=
  lawVar μ (c.matA p t) + vecMean μ id ⬝ᵥ (c.matB p t *ᵥ vecMean μ id)
    + c.vecD p t ⬝ᵥ vecMean μ id + ∫ ω, c.F t ω ∂D.P

/-- The drift of `Z̃` in (2.22), arXiv:2207.00446v3, p.11, at time `s` and state `x` with mean
`m = E[𝒳_s]`. The dots are derivatives of the deterministic functions `I^A, I^B, I^D`, taken at
points of the open interval `(t, T)`, where these are differentiable. -/
noncomputable def drift (s : ℝ) (x m : Fin 3 → ℝ) : ℝ :=
  -((fun i => deriv (fun u => c.iA p u i) s) ⬝ᵥ (x - m) / p.aTilde)
    - (fun i => deriv (fun u => c.iB p u i) s) ⬝ᵥ m / p.a
    - deriv (fun u => c.iD p D u) s / p.a
    - c.iA p s ⬝ᵥ (p.H *ᵥ (x - m)) / p.aTilde
    - c.iB p s ⬝ᵥ ((p.H + p.Hbar) *ᵥ m + p.G D.Ex0) / p.a

/-- The volatility of `Z̃` in (2.22), arXiv:2207.00446v3, p.11: `−(I^A_s/ã)𝒟_s`. -/
noncomputable def vol (u : ℝ≥0) (ω : Ω) : ℝ :=
  -(c.iA p u ⬝ᵥ ![0, D.σ u ω, 0] / p.aTilde)

/-- The two square terms of Proposition 4.1, arXiv:2207.00446v3, p.16, along a run:
`∫_t^T (1/ã)(I^A_s(𝒳_s − μ̄_s))² ds + ∫_t^T (1/a)(I^B_s μ̄_s + I^D_s)² ds`. -/
noncomputable def squares (t : ℝ≥0) (R : Run Ω) (ω : Ω) : ℝ :=
  (∫ s in (t : ℝ)..(D.T : ℝ),
      1 / p.aTilde *
        (c.iA p s ⬝ᵥ (R.X s.toNNReal ω - vecMean D.P (R.X s.toNNReal))) ^ 2)
    + ∫ s in (t : ℝ)..(D.T : ℝ),
      1 / p.a * (c.iB p s ⬝ᵥ vecMean D.P (R.X s.toNNReal) + c.iD p D s) ^ 2

/-- `R` follows the candidate strategy of Theorem 2.3 (ii), arXiv:2207.00446v3, p.11, from `ξ` at
time `t`: the initial jump is (2.21), the terminal jump is `X_{T−}`, there is no jump in `(t, T)`,
and `Z` satisfies (2.22) on `(t, T)`.

Formalization Note: the initial jump `ΔZ̃_t` is `Z̃_t`, as `Z̃_{t−} = 0` (`Model.Admissible`). -/
structure IsCandidate (t : ℝ≥0) (ξ : Ω → Fin 3 → ℝ) (R : Run Ω) : Prop where
  initial : ∀ᵐ ω ∂D.P, R.Z t ω =
    -(c.iA p t ⬝ᵥ (ξ ω - vecMean D.P ξ) / p.aTilde)
      - c.iB p t ⬝ᵥ vecMean D.P ξ / p.a - c.iD p D t / p.a
  terminal : ∀ᵐ ω ∂D.P,
    jump (fun s => R.Z s ω) D.T = leftLim (fun s => R.X s ω 0) D.T
  noJump : ∀ᵐ ω ∂D.P, ∀ s ∈ Set.Ioo t D.T, jump (fun u => R.Z u ω) s = 0
  dynamics : ∃ L : ℝ≥0 → Ω → ℝ,
    IsItoIntegral D.P D.𝓕 D.W D.T (c.vol p D) L ∧
    ∀ᵐ ω ∂D.P, ∀ r s : ℝ≥0, t < r → r ≤ s → s < D.T →
      R.Z s ω - R.Z r ω =
        (∫ u in (r : ℝ)..(s : ℝ),
          c.drift p D u (R.X u.toNNReal ω) (vecMean D.P (R.X u.toNNReal)))
        + (L s ω - L r ω)

end Coeffs

end MFCLiquidation


