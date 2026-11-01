-- Prove2me | Definitions.Def_TimeVaryingGames_MirrorDescent
-- name    : TimeVaryingGames_MirrorDescent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:24.680613+00:00
-- url     : https://prove2.me/theorems/e3a03d01-9ddf-4352-97df-7a18e13981ce
-- title:
--   Runs of multi-agent mirror descent and the oracle statistics (9a)–(9c)
-- statement:
--   Each player $i$ has a DGF $h_i$ on $\mathcal K_i$ with selection $\nabla h_i$ and prox-mapping $\mathcal P_i$, and a positive step-size sequence $\gamma_{i,t}$.
--
--   1. A **run of mirror descent** (Algorithm 1) with signals $V_{i,t}\in\mathcal Y_i$ is a sequence of profiles with $X_{i,1}$ in the prox-domain of $h_i$ and
--   $$X_{i,t+1}=\mathcal P_i(X_{i,t};\gamma_{i,t}V_{i,t})\qquad\text{for all }t\text{ and }i.$$
--   2. For random signals and iterates on a probability space with a filtration $(\mathcal F_t)$, the signal is decomposed as $V_{i,t}=v_{i,t}(X_t)+Z_{i,t}$ (the **observational error** $Z_{i,t}$), with **bias** $b_{i,t}=\mathbb E[Z_{i,t}\mid\mathcal F_t]$ and **noise** $U_{i,t}=Z_{i,t}-b_{i,t}$.
--   3. The **oracle statistics** hold with deterministic bounds $B_{i,t},\sigma_{i,t},M_{i,t}$ if almost surely
--   $$\|b_{i,t}\|_*\le B_{i,t},\qquad \mathbb E[\|U_{i,t}\|_*^2\mid\mathcal F_t]\le\sigma_{i,t}^2,\qquad \mathbb E[\|V_{i,t}\|_*^2\mid\mathcal F_t]\le M_{i,t}^2,$$
--   for every player and stage, the signals being measurable with $\mathbb E\|V_{i,t}\|_*^2<\infty$.
--
--   This is the learning model of the paper: every player runs mirror descent on an inexact, possibly biased gradient signal from a stochastic first-order oracle.
--
--   **Formalization Note** Lean's index $t$ starts at $0$ (the paper's stage $t+1$). The prox step is the relation `IsProxPoint`. The filtration is a parameter; in the theorems it is any filtration to which the iterates are adapted. Measurability of $V_{i,t}$ and integrability of $\|V_{i,t}\|_*^2$ are stated explicitly, since Lean's conditional expectation of a non-integrable function is $0$.
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, (SFO), p.6; eqs. (7)–(9c), p.7; (MD), p.7; Algorithm 1, p.8

import Mathlib
import Definitions.Def_TimeVaryingGames_ContinuousGame
import Definitions.Def_TimeVaryingGames_DGF

open MeasureTheory

namespace TimeVaryingGames

/-- **A run of mirror descent** (MD) / Algorithm 1, along one realization.
arXiv:1809.03066v3, §3.3, p.7: "X_{i,t+1} = P_i(X_{i,t}; γ_{i,t}V_{i,t}) (MD)"; Algorithm 1, p.8;
Lemma A.4, p.31: "with X_1 ∈ C_h initialized arbitrarily".

`IsMDPath K h gradh γ V X`: every player's initial action lies in the prox-domain of its DGF, and
at every stage `t` each player `i` moves to the prox-point of its current action with the scaled
signal `γ_{i,t} V_{i,t}`.

**Formalization Note.** Lean's `t : ℕ` is the paper's stage `t + 1` (`X 0` is the paper's `X_1`).
The prox step is the relation `IsProxPoint` (the minimizer of (13)). -/
def IsMDPath {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (K : ∀ i, Set (E i)) (h : ∀ i, E i → ℝ)
    (gradh : ∀ i, E i → E i →L[ℝ] ℝ) (γ : ι → ℕ → ℝ) (V : ∀ i, ℕ → E i →L[ℝ] ℝ)
    (X : ℕ → ∀ i, E i) : Prop :=
  (∀ i, X 0 i ∈ proxDomain (K i) (h i)) ∧
    ∀ t i, IsProxPoint (K i) (h i) (gradh i) (X t i) (γ i t • V i t) (X (t + 1) i)

/-- **Observational error** `Z_{i,t} = V_{i,t} − v_{i,t}(X_t)`.
arXiv:1809.03066v3, §3.2, p.6: "V_{i,t} = v_{i,t}(X_t) + Z_{i,t} (SFO) where the
"observational error" Z_{i,t} captures all sources of uncertainty in the received input." -/
noncomputable def oracleError {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {Ω : Type*}
    (X : ℕ → Ω → ∀ i, E i) (V : ∀ i, ℕ → Ω → E i →L[ℝ] ℝ)
    (uStage : ℕ → ι → (∀ j, E j) → ℝ) (i : ι) (t : ℕ) (ω : Ω) : E i →L[ℝ] ℝ :=
  V i t ω - partialGradient (uStage t) i (X t ω)

/-- **Bias** `b_{i,t} = E[Z_{i,t} | F_t]`.
arXiv:1809.03066v3, §3.2, p.7, eq. (8): "b_{i,t} = E[Z_{i,t} | F_t]".

**Formalization Note.** `F_t` is the σ-algebra `ℱ t` of a filtration to which the iterates are
adapted (the paper's natural filtration `σ(X_1, …, X_t)` is one such). -/
noncomputable def oracleBias {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {Ω : Type*}
    {m₀ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ∀ i, E i) (V : ∀ i, ℕ → Ω → E i →L[ℝ] ℝ)
    (uStage : ℕ → ι → (∀ j, E j) → ℝ) (i : ι) (t : ℕ) : Ω → E i →L[ℝ] ℝ :=
  condExp (ℱ t) P (oracleError X V uStage i t)

/-- **Zero-mean noise** `U_{i,t} = Z_{i,t} − b_{i,t}`.
arXiv:1809.03066v3, §3.2, p.7, eq. (8): "U_{i,t} = Z_{i,t} − b_{i,t}". -/
noncomputable def oracleNoise {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {Ω : Type*}
    {m₀ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ∀ i, E i) (V : ∀ i, ℕ → Ω → E i →L[ℝ] ℝ)
    (uStage : ℕ → ι → (∀ j, E j) → ℝ) (i : ι) (t : ℕ) (ω : Ω) : E i →L[ℝ] ℝ :=
  oracleError X V uStage i t ω - oracleBias P ℱ X V uStage i t ω

/-- **Oracle statistics** (9a)–(9c).
arXiv:1809.03066v3, §3.2, p.7: "(1) Bias: ‖b_{i,t}‖_* ≤ B_{i,t}. (9a) (2) Variance:
E[‖U_{i,t}‖²_* | F_t] ≤ σ²_{i,t}. (9b) (3) Second moment: E[‖V_{i,t}‖²_* | F_t] ≤ M²_{i,t}. (9c)
… B_{i,t}, σ_{i,t} and M_{i,t} are to be construed as deterministic upper bounds".

`OracleStatistics P ℱ X V uStage B σ M` says, for every player `i` and stage `t`:
1. the signal `V_{i,t}` is a (strongly) measurable random dual vector with `E‖V_{i,t}‖²_* < ∞`;
2. (9a) almost surely `‖b_{i,t}‖_* ≤ B_{i,t}`;
3. (9b) almost surely `E[‖U_{i,t}‖²_* | F_t] ≤ σ²_{i,t}`;
4. (9c) almost surely `E[‖V_{i,t}‖²_* | F_t] ≤ M²_{i,t}`.

**Formalization Note.** Item 1 is presupposed by (9): it makes the conditional expectations
meaningful (Lean's conditional expectation of a non-integrable function is `0`). The bounds
`B, σ, M` are functions of `(i, t)` only (deterministic). -/
def OracleStatistics {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {Ω : Type*}
    {m₀ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ∀ i, E i) (V : ∀ i, ℕ → Ω → E i →L[ℝ] ℝ)
    (uStage : ℕ → ι → (∀ j, E j) → ℝ) (B σ M : ι → ℕ → ℝ) : Prop :=
  (∀ i t, StronglyMeasurable (V i t)) ∧
  (∀ i t, Integrable (fun ω => ‖V i t ω‖ ^ 2) P) ∧
  (∀ i t, ∀ᵐ ω ∂P, ‖oracleBias P ℱ X V uStage i t ω‖ ≤ B i t) ∧
  (∀ i t, condExp (ℱ t) P (fun ω => ‖oracleNoise P ℱ X V uStage i t ω‖ ^ 2)
    ≤ᵐ[P] fun _ => σ i t ^ 2) ∧
  (∀ i t, condExp (ℱ t) P (fun ω => ‖V i t ω‖ ^ 2) ≤ᵐ[P] fun _ => M i t ^ 2)

end TimeVaryingGames


