-- Prove2me | Definitions.Def_RiskSensMDP_AverageCost_Model
-- name    : RiskSensMDP_AverageCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:17.145258+00:00
-- url     : https://prove2.me/theorems/57585bcb-15d7-42f5-8650-79d1d6d6c52b
-- title:
--   Borel MDP with bounded positive cost (§2): D, Q, c ∈ [c̲, c̄], history-dependent policies Π, path measure P^σ_x, C^n, stationary policies
-- statement:
--   This is the controlled Markov model of Bäuerle and Rieder, §2.
--
--   1. The **state space** $E$ and the **action space** $A$ are standard Borel spaces.
--   2. $D\subseteq E\times A$ is a measurable set of admissible state–action pairs, and every state has an admissible action: $D(x):=\{a\in A:(x,a)\in D\}\neq\emptyset$ for every $x\in E$.
--   3. The **transition law** $Q(\cdot\mid x,a)$ is a Markov kernel from $E\times A$ to $E$.
--   4. The **cost function** $c$ is measurable, and there are constants $0<\underline c<\bar c$ with $\underline c\le c(x,a)\le\bar c$ for every $(x,a)\in D$.
--
--   A **history** up to time $n$ is $h_n=(x_0,a_0,x_1,\dots,a_{n-1},x_n)$. A **history-dependent policy** $\sigma=(g_n)_{n\in\mathbb N_0}$ is a sequence of measurable maps $g_n$ from histories to actions with $g_n(h_n)\in D(x_n)$. The set of all such policies is $\Pi$.
--
--   For $\sigma\in\Pi$ and an initial state $x$, the **path measure** $\mathbb P^\sigma_x$ is the probability measure on trajectories $((X_0,A_0),(X_1,A_1),\dots)$ with $X_0=x$, $A_n=g_n(X_0,A_0,\dots,X_n)$ and $X_{n+1}\sim Q(\cdot\mid X_n,A_n)$. $\mathbb E^\sigma_x$ denotes expectation under it. The **accumulated cost** up to time $n$ is
--   $$
--   C^n=\sum_{k=0}^{n-1}c(X_k,A_k).
--   $$
--
--   A **stationary policy** $\pi=(f,f,\dots)$ is given by a measurable decision rule $f:E\to A$ with $f(x)\in D(x)$. As a history-dependent policy it is $g_n(h_n)=f(x_n)$. Under it the state process $(X_n)$ is the Markov chain with transition kernel
--   $$
--   P_f(x,B)=Q(B\mid x,f(x)).
--   $$
--
--   This model is the common ground of all results of §5. The objects are the paper's, specialised to the undiscounted case $\beta=1$ that §5 uses.
--
--   **Formalization Note** The path measure is built with Mathlib's Ionescu-Tulcea construction (`Kernel.trajMeasure`) on $(E\times A)^{\mathbb N_0}$. The decision rules $g_n$ are defined on $(E\times A)^n\times E$ instead of $D^n\times E$. This enlargement is harmless, because under $\mathbb P^\sigma_x$ only histories in $D^n\times E$ occur. $Q$ and $c$ are given on all of $E\times A$, and only their values on $D$ matter. The paper says only that $D$ is a nonempty Borel set. Nonemptiness of every $D(x)$ is added because policies must exist. Standard Borelness of $E$ and $A$ is assumed in the theorems, not in the structure. §5 uses no topology and none of the continuity–compactness conditions (CC) of §2, so they are omitted. "Stationary" here means Markov in the state $x$ alone, not in the extended states of §3.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 3, §2 (model, histories, Π, P^σ_x, C^N with β = 1), and p. 17, §5 (stationary policies π = (f, f, …))

import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

/-- The Markov decision model of Bäuerle & Rieder (2014), §2, p. 3: Borel state space `E` and action
space `A`, a measurable set `D ⊆ E × A` of admissible state–action pairs with nonempty sections
`D(x) = {a | (x, a) ∈ D}`, a transition law `Q(· | x, a)` and a measurable one-step cost `c` with
values in `[c̲, c̄]` on `D`, where `0 < c̲ < c̄`. `Q` and `c` are given on all of `E × A`; only their
values on `D` matter. -/
structure Model (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  /-- the set `D` of admissible state–action pairs -/
  D : Set (E × A)
  /-- `D` is a Borel set -/
  D_meas : MeasurableSet D
  /-- every state has an admissible action: `D(x) ≠ ∅` -/
  D_nonempty : ∀ x : E, ∃ a : A, (x, a) ∈ D
  /-- the transition law `Q(dx' | x, a)` -/
  Q : Kernel (E × A) E
  [Q_markov : IsMarkovKernel Q]
  /-- the one-step cost `c(x, a)` -/
  c : E × A → ℝ
  c_meas : Measurable c
  /-- the lower cost bound `c̲` -/
  cl : ℝ
  /-- the upper cost bound `c̄` -/
  cu : ℝ
  cl_pos : 0 < cl
  cl_lt_cu : cl < cu
  /-- `c : D → [c̲, c̄]` -/
  c_mem : ∀ p ∈ D, cl ≤ c p ∧ c p ≤ cu

attribute [instance] Model.Q_markov

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- A history-dependent (deterministic) policy `σ = (g_n)_{n ∈ ℕ₀}` (p. 3): `g_n` maps the history
`h_n = (x₀, a₀, …, x_{n-1}, a_{n-1}, x_n)`, stored as the pair (past state–action pairs, current
state), measurably to an action with `g_n(h_n) ∈ D(x_n)`. `Policy M` is the paper's set `Π`. -/
structure Policy (M : Model E A) where
  /-- the decision rule `g_n` -/
  g : (n : ℕ) → (Fin n → E × A) × E → A
  g_meas : ∀ n, Measurable (g n)
  g_adm : ∀ n h, (h.2, g n h) ∈ M.D

/-- The history `(x₀, a₀, …, x_t, a_t)`, indexed by `Finset.Iic t`, as a `Fin (t+1)`-tuple. -/
def histFin (t : ℕ) (h : Π _ : Iic t, E × A) : Fin (t + 1) → E × A :=
  fun j => h ⟨j.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt)⟩

lemma measurable_histFin (t : ℕ) : Measurable (histFin (E := E) (A := A) t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The last state–action pair `(x_t, a_t)` of a history indexed by `Finset.Iic t`. -/
def lastPair (t : ℕ) (h : Π _ : Iic t, E × A) : E × A :=
  h ⟨t, Finset.mem_Iic.mpr le_rfl⟩

/-- One step of the controlled process under `σ`: from the history up to `(x_t, a_t)` the next
state `x_{t+1}` is drawn from `Q(· | x_t, a_t)` and the next action is `a_{t+1} = g_{t+1}(h_{t+1})`. -/
noncomputable def stepKernel (M : Model E A) (σ : Policy M) (t : ℕ) :
    Kernel (Π _ : Iic t, E × A) (E × A) :=
  (M.Q.comap (lastPair t) (measurable_pi_apply _)) ⊗ₖ
    Kernel.deterministic (fun p : (Π _ : Iic t, E × A) × E => σ.g (t + 1) (histFin t p.1, p.2))
      ((σ.g_meas (t + 1)).comp
        (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))

instance (M : Model E A) (σ : Policy M) (t : ℕ) : IsMarkovKernel (stepKernel M σ t) := by
  have : IsMarkovKernel (M.Q.comap (lastPair (E := E) (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  unfold stepKernel; infer_instance

/-- The probability measure `P^σ_x` (p. 3) on the trajectories `ω = ((X₀, A₀), (X₁, A₁), …)`,
given by the Ionescu-Tulcea theorem: `X₀ = x`, `A_n = g_n(X₀, A₀, …, X_n)` and
`X_{n+1} ∼ Q(· | X_n, A_n)`. -/
noncomputable def pathMeasure (M : Model E A) (σ : Policy M) (x : E) : Measure (ℕ → E × A) :=
  Kernel.trajMeasure (X := fun _ => E × A)
    (Measure.dirac (x, σ.g 0 (fun j => j.elim0, x))) (stepKernel M σ)

/-- The accumulated cost `C^n = ∑_{k=0}^{n-1} c(X_k, A_k)` of a trajectory (p. 3, `β = 1`). -/
def cost (M : Model E A) (n : ℕ) (ω : ℕ → E × A) : ℝ :=
  ∑ k ∈ Finset.range n, M.c (ω k)

/-- A stationary policy `π = (f, f, …)` (§5, p. 17), given by a measurable decision rule
`f : E → A` with `f(x) ∈ D(x)`; it chooses the action from the current state alone. -/
structure StationaryRule (M : Model E A) where
  /-- the decision rule `f` -/
  f : E → A
  f_meas : Measurable f
  f_adm : ∀ x, (x, f x) ∈ M.D

/-- The history-dependent policy of `π = (f, f, …)`: `g_n(h_n) = f(x_n)`. -/
def StationaryRule.toPolicy {M : Model E A} (f : StationaryRule M) : Policy M where
  g := fun _ h => f.f h.2
  g_meas := fun _ => f.f_meas.comp measurable_snd
  g_adm := fun _ h => f.f_adm h.2

/-- The transition kernel `P_f(x, ·) = Q(· | x, f(x))` of the state process `(X_n)` under the
stationary policy `(f, f, …)`. -/
noncomputable def stateKernel (M : Model E A) (f : StationaryRule M) : Kernel E E :=
  M.Q.comap (fun x => (x, f.f x)) (measurable_id.prodMk f.f_meas)

instance (M : Model E A) (f : StationaryRule M) : IsMarkovKernel (stateKernel M f) := by
  unfold stateKernel; exact Kernel.IsMarkovKernel.comap _ _

end RiskSensMDP.AverageCost


