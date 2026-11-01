-- Prove2me | Definitions.Def_DelayedGLCB_DUCB
-- name    : DelayedGLCB_DUCB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:26:01.120814+00:00
-- url     : https://prove2.me/theorems/1f04f197-1973-4470-9fe4-a3218420702c
-- title:
--   DUCB-GLCB (Algorithm 1), the delay independence of p.5 and the regret $R_T$
-- statement:
--   **DUCB-GLCB** takes an inverse link $g$, a parameter $\kappa$, the noise level $\hat\sigma$, a confidence level $\delta$, a number $\tau$ of exploration rounds, an estimator and a tie-break rule. At round $t$:
--
--   1. if $t\le\tau$, it plays the exploration draw $\alpha_t$;
--   2. if $t>\tau$, it computes $\hat\theta_t$ from the complete tuples $(X_s,Y_s)$, $s\in T_t$ (a root of $\sum_{s\in T_t}(Y_s-g(X_s'\theta))X_s=0$), sets
--   $$
--   \beta_t=\frac{\hat\sigma}{\kappa}\sqrt{\frac d2\log\Big(1+\frac{2(t-G_t)}{d}\Big)+\log\frac1\delta}+\sqrt{G_t},
--   $$
--   and plays an arm maximizing $x_{t,a}'\hat\theta_t+\beta_t\|x_{t,a}\|_{V_t^{-1}}$, where $V_t=\sum_{s<t}X_sX_s'$.
--
--   Here $X_s=x_{s,a_s}$ and $Y_s=y_{s,a_s}$ are the feature and reward of the arm played at round $s$.
--
--   The **delay independence** of p.5 requires, for each $t\in[T]$, that $D_t$ be independent of $(D_s)_{s<t}$ and $(x_s,a_s,y_{s,a_s})_{s\le t}$. The **regret** of a strategy over $T$ rounds is
--   $$
--   R_T=\sum_{t=1}^T\Big(\max_{a\in[K]}g(x_{t,a}'\theta^*)-g(x_{t,a_t}'\theta^*)\Big).
--   $$
--
--   The algorithm is GLM-UCB adapted to delays: the estimator uses only rewards that have arrived, and the width grows with the number $G_t$ of missing rewards.
--
--   **Formalization Note** The estimator is any function of the complete tuples listed in increasing round order, so it cannot see a missing reward. Root selection is the separate condition that it returns a root of (5) whenever one exists. The tie-break returns a maximizer of every index vector. $V_t^{-1}$ is Mathlib's matrix inverse, which is $0$ for a singular matrix. The action process is defined by recursion over rounds.
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, Algorithm 1, p.7; (5), p.7; §2.2, p.5 (independence of D_t); Performance criterion, p.6 (R_T)

import Mathlib
import Definitions.Def_DelayedGLCB_Env
import Definitions.Def_DelayedGLCB_completeSet
import Definitions.Def_DelayedGLCB_Vmat

namespace DelayedGLCB

open Matrix MeasureTheory ProbabilityTheory

/-- An **estimator**: given `n` complete tuples `(X_s, Y_s)` listed in increasing round order, it
returns a parameter in `ℝ^d`. It sees nothing else, in particular no missing reward. -/
abbrev Estimator (d : ℕ) := (n : ℕ) → (Fin n → (Fin d → ℝ) × ℝ) → (Fin d → ℝ)

/-- The left side of the likelihood equation (5), `Σ_s (Y_s − g(X_s'θ)) X_s`, over a data list. -/
def scoreEq {d : ℕ} (g : ℝ → ℝ) (n : ℕ) (data : Fin n → (Fin d → ℝ) × ℝ) (θ : Fin d → ℝ) :
    Fin d → ℝ :=
  ∑ i, ((data i).2 - g ((data i).1 ⬝ᵥ θ)) • (data i).1

/-- **Root selection for (5).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, (5), p.7: "the MLE can be written as the solution of the
following equation `Σ_{s∈T_t} (Y_s − g(X_s'θ)) X_s = 0`, which is the estimator we use in Step 4 of
Algorithm 1."

The estimator returns a root of (5) whenever (5) has one; otherwise its output is arbitrary. -/
def IsRootSelecting {d : ℕ} (g : ℝ → ℝ) (est : Estimator d) : Prop :=
  ∀ n (data : Fin n → (Fin d → ℝ) × ℝ), (∃ θ, scoreEq g n data θ = 0) →
    scoreEq g n data (est n data) = 0

/-- A deterministic tie-break `tie` returning a maximizer of every index vector
(the `arg max` of Algorithm 1, line 6). -/
def IsArgmaxSelector {K : ℕ} (tie : (Fin K → ℝ) → Fin K) : Prop :=
  ∀ (v : Fin K → ℝ) (b : Fin K), v b ≤ v (tie v)

/-- The tuning data of **DUCB-GLCB** (Algorithm 1, p.7): the inverse link `g`, the model
parameter `κ`, the noise parameter `σ̂` (in `β_t`), the confidence parameter `δ`, the number `τ` of
exploration rounds, the estimator of Step 4 and the tie-break of Step 6. -/
structure DUCB (d K : ℕ) where
  g : ℝ → ℝ
  κ : ℝ
  σhat : ℝ
  δ : ℝ
  τ : ℕ
  est : Estimator d
  tie : (Fin K → ℝ) → Fin K

/-- **The adaptive width `β_t`** (Blanchet, Xu, Zhou, arXiv:2003.05174v1, Algorithm 1, line 5, p.7):
`β_t = (σ̂/κ) √( (d/2) log(1 + 2(t − G_t)/d) + log(1/δ) ) + √G_t`. -/
noncomputable def beta (σhat κ δ : ℝ) (d t G : ℕ) : ℝ :=
  σhat / κ * Real.sqrt ((d : ℝ) / 2 * Real.log (1 + 2 * ((t : ℝ) - G) / d) + Real.log (1 / δ))
    + Real.sqrt G

variable {Ω : Type*} {d K : ℕ}

/-- The chosen features `X_s = x_{s, act s}` for an action sequence `act`. -/
def featOf (E : Env Ω d K) (ω : Ω) (act : ℕ → Fin K) (s : ℕ) : Fin d → ℝ :=
  E.x s ω (act s)

/-- The complete tuples `(X_s, Y_s)`, `s ∈ T_t`, in increasing order of `s`. -/
noncomputable def dataOf (E : Env Ω d K) (ω : Ω) (act : ℕ → Fin K) (t : ℕ) :
    Fin (completeSet E.D ω t).card → (Fin d → ℝ) × ℝ :=
  fun i =>
    let s := (completeSet E.D ω t).orderEmbOfFin rfl i
    (featOf E ω act s, E.y s ω (act s))

/-- `θ̂_t`: the estimator applied to the complete tuples at round `t` (Algorithm 1, line 4). -/
noncomputable def thetaOf (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (act : ℕ → Fin K) (t : ℕ) :
    Fin d → ℝ :=
  A.est _ (dataOf E ω act t)

/-- `β_t` evaluated at round `t` with `G_t = missingCount E.D ω t`. -/
noncomputable def betaAt (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (t : ℕ) : ℝ :=
  beta A.σhat A.κ A.δ d t (missingCount E.D ω t)

/-- The UCB index `x_{t,a}'θ̂_t + β_t ‖x_{t,a}‖_{V_t^{-1}}` of Algorithm 1, line 6. -/
noncomputable def ucbIndex (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (act : ℕ → Fin K) (t : ℕ)
    (a : Fin K) : ℝ :=
  E.x t ω a ⬝ᵥ thetaOf A E ω act t + betaAt A E ω t * wnorm (Vmat (featOf E ω act) t)⁻¹ (E.x t ω a)

/-- One step of Algorithm 1 at round `t`, given the actions of the earlier rounds. -/
noncomputable def stepOf (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (act : ℕ → Fin K) (t : ℕ) : Fin K :=
  if t ≤ A.τ then E.α t ω else A.tie (ucbIndex A E ω act t)

/-- `actsUpTo A E ω n s` is the action of round `s` for `s ≤ n`. -/
noncomputable def actsUpTo (A : DUCB d K) (E : Env Ω d K) (ω : Ω) : ℕ → ℕ → Fin K
  | 0 => fun _ => E.α 0 ω
  | n + 1 => fun s => if s ≤ n then actsUpTo A E ω n s else stepOf A E ω (actsUpTo A E ω n) (n + 1)

/-- **DUCB-GLCB** (Blanchet, Xu, Zhou, arXiv:2003.05174v1, Algorithm 1, p.7): the arm `a_t` played at
round `t ≥ 1`.

"2: Initialization: randomly choose `α_t ∈ [K]` for `t ∈ [τ]` …
 4: Update Statistics: calculate the MLE `θ̂_t` by solving `Σ_{s∈T_t}(Y_s − g(X_s'θ))X_s = 0`
 5: Update Parameter: `β_t = (σ̂/κ)√((d/2) log(1 + 2(t−G_t)/d) + log(1/δ)) + √G_t`
 6: Select Action: choose `a_t = arg max_{a∈[K]} (x_{t,a}'θ̂_t + β_t ‖x_{t,a}‖_{V_t^{-1}})`"

For `t ≤ τ` the arm is `α_t`; for `t > τ` it is `tie` applied to the UCB index, where `θ̂_t` is the
estimator applied to the complete tuples `(X_s, Y_s)`, `s ∈ T_t`, and `V_t = Σ_{s<t} X_s X_s'`.

**Formalization Note.** `V_t^{-1}` is Mathlib's `Matrix.inv`, which is `0` for a singular matrix.
The estimator is any function of the complete tuples; root selection is the separate hypothesis
`IsRootSelecting`. Round `0` is unused. -/
noncomputable def action (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (t : ℕ) : Fin K :=
  actsUpTo A E ω t t

/-- The feature `X_s = x_{s,a_s}` of the arm DUCB-GLCB plays at round `s`. -/
noncomputable def X (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (s : ℕ) : Fin d → ℝ :=
  E.x s ω (action A E ω s)

/-- `V_t = Σ_{s=1}^{t−1} X_s X_s'` along the run of DUCB-GLCB. -/
noncomputable def V (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Vmat (X A E ω) t

/-- `W_t = Σ_{s ∈ T_t} X_s X_s'` along the run of DUCB-GLCB. -/
noncomputable def W (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Wmat E.D ω (X A E ω) t

/-- The estimate `θ̂_t` computed by DUCB-GLCB at round `t`. -/
noncomputable def thetaHat (A : DUCB d K) (E : Env Ω d K) (ω : Ω) (t : ℕ) : Fin d → ℝ :=
  thetaOf A E ω (action A E ω) t

/-- **The independence of the delays (literal, p.5).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, §2.2, p.5: "We assume `D_t` is a non-negative random number
which is independent of `{D_s}_{s≤t−1}` and `{x_s, y_{s,a_s}, a_s}_{s≤t}`."

For each `t ∈ [1, T]`, `D_t` is independent of `((D_s)_{1≤s<t}, (x_s, a_s, y_{s,a_s})_{1≤s≤t})`, where
`act` is the action process of the strategy that is run.

**Formalization Note.** Over `t ∈ [1, T]` this makes `D_1, …, D_T` mutually independent, the
"independent" of Assumption 2. -/
def DelayIndependent [MeasurableSpace Ω] (P : Measure Ω) (E : Env Ω d K) (act : ℕ → Ω → Fin K)
    (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, IndepFun (E.D t)
    (fun ω => ((fun s : Finset.Ico 1 t => E.D s ω),
      (fun s : Finset.Icc 1 t => (E.x s ω, act s ω, E.y s ω (act s ω))))) P

/-- **The regret `R_T`** (Blanchet, Xu, Zhou, arXiv:2003.05174v1, p.6: "`a_t^* = arg max_{a∈[K]}
g(x_{t,a}'θ*)` … `R_T(π) := Σ_{t=1}^T (g(x_{t,a_t^*}'θ*) − g(x_{t,a_t}'θ*))`") of the action process
`act`.

**Formalization Note.** `g(x_{t,a_t^*}'θ*)` is written as the maximum over arms, a supremum over the
finite type `Fin K` (the maximum when `K ≥ 1`). -/
noncomputable def regret (E : Env Ω d K) (g : ℝ → ℝ) (θstar : Fin d → ℝ) (act : ℕ → Ω → Fin K)
    (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ((⨆ a : Fin K, g (E.x t ω a ⬝ᵥ θstar)) - g (E.x t ω (act t ω) ⬝ᵥ θstar))

end DelayedGLCB


