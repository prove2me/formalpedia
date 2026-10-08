-- Prove2me | Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP
-- name    : ArapostathisAC_CanonicalPolicy_CMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:17:18.982953+00:00
-- url     : https://prove2.me/theorems/a05999fa-5af6-4116-aee5-39e61b34fe9b
-- title:
--   The Borel controlled Markov process of §6.1: policies, path measures, finite-horizon and average costs, canonical triplets, strong average optimality
-- statement:
--   This file sets up the controlled Markov process (CMP) of Arapostathis, Borkar, Fernández-Gaucherand, Ghosh and Marcus (1993), §2, in the bounded-cost setting of §6.1.
--
--   **Model.** A CMP is a five-tuple $(S, A, U, P, c)$. The state space $S$ is a standard Borel space and the action space $A$ is a Borel space. For each state $x$, $U(x) \subseteq A$ is the nonempty compact set of admissible actions, and the set of admissible state–action pairs $K = \{(x,a) : a \in U(x)\}$ is measurable. $P(dy \mid x, a)$ is a stochastic kernel on $S$ given $S \times A$, and $c : S \times A \to \mathbb R$ is a measurable one-stage cost with $c \ge 0$ on $K$ (Assumption 2.1, which the paper assumes throughout).
--
--   **Policies.** A history at time $t$ is $h_t = (x_0, a_0, \dots, x_{t-1}, a_{t-1}, x_t)$. An admissible policy $\pi = (\pi_t)_{t \ge 0}$ is a sequence of stochastic kernels $\pi_t(da \mid h_t)$ with $\pi_t(U(x_t) \mid h_t) = 1$. The class of all admissible policies (randomized, history dependent) is $\Pi$. An initial state $x$ and a policy $\pi$ determine, by the Ionescu-Tulcea theorem, a probability measure $\mathcal P^\pi_x$ on trajectories $((X_0, A_0), (X_1, A_1), \dots)$ with $X_0 = x$, $A_t \sim \pi_t(\cdot \mid H_t)$ and $X_{t+1} \sim P(\cdot \mid X_t, A_t)$; $E^\pi_x$ is its expectation.
--
--   **Costs.** For $N \in \mathbb N_0$ and a terminal cost $h$,
--   $$J_N(x, \pi, h) = E^\pi_x\Big[\sum_{t=0}^{N-1} c(X_t, A_t) + h(X_N)\Big], \qquad J_N(x,\pi) = J_N(x,\pi,0), \qquad J^*_N(x, h) = \inf_{\pi \in \Pi} J_N(x, \pi, h).$$
--   The average cost and the optimal average cost are
--   $$J(x, \pi) = \limsup_{N\to\infty} \frac1N J_N(x, \pi), \qquad J^*(x) = \inf_{\pi\in\Pi} J(x,\pi).$$
--   $\mathcal M_b(S)$ is the set of bounded measurable real functions on $S$, and $c \in \mathcal M_b(K)$ means $c$ is bounded on $K$. For bounded $v$, the span seminorm is $\operatorname{span}(v) = \sup_{w, w'} \{v(w) - v(w')\} = \sup v - \inf v$.
--
--   **Canonical triplets and strong average optimality.** For $R, H \in \mathcal M_b(S)$ and $\pi^* \in \Pi$, the triplet $(R, H, \pi^*)$ is canonical if
--   $$J_N(x, \pi^*, H) = J^*_N(x, H) = H(x) + N R(x) \qquad \forall N \in \mathbb N_0,\ x \in S. \tag{6.4}$$
--   A policy $\pi^*$ is strong average optimal if
--   $$\limsup_{N\to\infty} \frac1N J_N(x,\pi^*) \le \liminf_{N\to\infty}\frac1N J_N(x,\pi) \qquad \forall x \in S,\ \pi \in \Pi. \tag{6.5}$$
--
--   These are the objects of §6.1 of the survey: a canonical triplet makes $\pi^*$ optimal for every finite horizon with terminal cost $H$, and Theorem 6.3 derives average-cost optimality from this.
--
--   **Formalization Note.** Policies are history-dependent randomized kernels, as on p. 285; histories are stored as (past state–action pairs, current state). $\mathcal P^\pi_x$ is Mathlib's `Kernel.trajMeasure`. $J_N$ is a Bochner integral; with $c$ bounded on $K$ (a hypothesis of every theorem that uses it) and $h$ bounded measurable it is the integral of an almost surely bounded function. $J^*_N$ is a real infimum; the family is bounded below by $-\sup|h|$ because $c \ge 0$ on $K$. $J$, $J^*$ and both sides of (6.5) are computed in the extended reals `EReal`, so no limit superior or inferior is a junk value; the $N = 0$ term $J_0/0$ is $0$ in Lean and does not affect the limits. `span` uses real suprema and infima and is meant for bounded functions. $c$ and $P$ are given on all of $S \times A$; only their values on $K$ enter.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 283 (notation, span), pp. 284–288 (§2.1–§2.4, Assumption 2.1), p. 316 ((6.4), (6.5))

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ArapostathisAC.CanonicalPolicy

/-- The controlled Markov process `(S, A, U, P, c)` of Arapostathis et al. (1993), §2.1, p. 284,
with Assumption 2.1 (`c ≥ 0` on `K`, p. 288). The state space `S` and the action space `A` are
Borel spaces. `U x` is the nonempty compact set of admissible actions at `x`, and
`K = {(x, a) : a ∈ U x}` is a measurable set. The one-step cost `c` and the transition kernel
`P(· | x, a)` are given on all of `S × A`; only their values on `K` matter. -/
structure BorelCMP (S A : Type*) [MeasurableSpace S] [TopologicalSpace A] [MeasurableSpace A] where
  /-- the admissible action sets `U(x)` -/
  U : S → Set A
  /-- `U` is strict: every `U(x)` is nonempty -/
  U_nonempty : ∀ x, (U x).Nonempty
  /-- `U` is compact-valued -/
  U_compact : ∀ x, IsCompact (U x)
  /-- the graph `K = {(x, a) : a ∈ U(x)}` is measurable -/
  K_meas : MeasurableSet {p : S × A | p.2 ∈ U p.1}
  /-- the one-step cost `c(x, a)` -/
  c : S × A → ℝ
  c_meas : Measurable c
  /-- Assumption 2.1: `c ≥ 0` on `K` -/
  c_nonneg : ∀ x, ∀ a ∈ U x, 0 ≤ c (x, a)
  /-- the transition kernel `P(dy | x, a)` -/
  P : Kernel (S × A) S
  [isMarkov : IsMarkovKernel P]

attribute [instance] BorelCMP.isMarkov

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

omit [StandardBorelSpace S] [BorelSpace A] in
/-- The admissible action set `U(x)` is measurable: it is the section of the measurable graph `K`. -/
lemma BorelCMP.measurableSet_U (M : BorelCMP S A) (x : S) : MeasurableSet (M.U x) :=
  measurable_prodMk_left M.K_meas

/-- An admissible policy `π = (π_t)` (p. 285): `π_t` is a stochastic kernel on `A` given the history
`h_t = (x₀, a₀, …, x_{t-1}, a_{t-1}, x_t)`, stored as the pair (past state–action pairs, current
state), with `π_t(U(x_t) | h_t) = 1`. This is the paper's class `Π` (history dependent, randomized). -/
structure Policy (M : BorelCMP S A) where
  /-- the decision rule `π_t` at epoch `t` -/
  rule : (t : ℕ) → Kernel ((Fin t → S × A) × S) A
  [isMarkov : ∀ t, IsMarkovKernel (rule t)]
  /-- admissibility: `π_t(U(x_t)ᶜ | h_t) = 0` -/
  adm : ∀ t hist, rule t hist (M.U hist.2)ᶜ = 0

attribute [instance] Policy.isMarkov

/-- The history `(x₀, a₀, …, x_t, a_t)`, indexed by `Finset.Iic t`, as a `Fin (t+1)`-tuple. -/
def histFin (t : ℕ) (h : Π _ : Finset.Iic t, S × A) : Fin (t + 1) → S × A :=
  fun j => h ⟨j.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt)⟩

omit [StandardBorelSpace S] [TopologicalSpace A] [BorelSpace A] in
lemma measurable_histFin (t : ℕ) : Measurable (histFin (S := S) (A := A) t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The last state–action pair `(x_t, a_t)` of a history indexed by `Finset.Iic t`. -/
def lastPair (t : ℕ) (h : Π _ : Finset.Iic t, S × A) : S × A :=
  h ⟨t, Finset.mem_Iic.mpr le_rfl⟩

/-- One step of the controlled process: given the history up to `(x_t, a_t)`, the next state is
drawn from `P(· | x_t, a_t)` and then the next action from `π_{t+1}(· | h_{t+1})`. -/
noncomputable def stepKernel (M : BorelCMP S A) (π : Policy M) (t : ℕ) :
    Kernel (Π _ : Finset.Iic t, S × A) (S × A) :=
  (M.P.comap (lastPair t) (measurable_pi_apply _)) ⊗ₖ
    ((π.rule (t + 1)).comap (fun p => (histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))

instance (M : BorelCMP S A) (π : Policy M) (t : ℕ) : IsMarkovKernel (stepKernel M π t) := by
  have h1 : IsMarkovKernel (M.P.comap (lastPair (S := S) (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (t + 1)).comap (fun p : (Π _ : Finset.Iic t, S × A) × S =>
      (histFin t p.1, p.2)) (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact Kernel.IsMarkovKernel.compProd _ _

/-- The law of `(x₀, a₀)`: `x₀ = x` and `a₀ ∼ π₀(· | x)`. -/
noncomputable def initMeasure {M : BorelCMP S A} (π : Policy M) (x : S) : Measure (S × A) :=
  ((π.rule 0) (fun j => j.elim0, x)).map (fun a => (x, a))

/-- The probability measure `𝒫^π_x` (p. 285, (2.1)–(2.3)) on trajectories
`ω = ((x₀, a₀), (x₁, a₁), …)`, given by the Ionescu-Tulcea theorem. -/
noncomputable def pathMeasure (M : BorelCMP S A) (π : Policy M) (x : S) :
    Measure (ℕ → S × A) :=
  Kernel.trajMeasure (X := fun _ => S × A) (initMeasure π x) (stepKernel M π)

/-- The `N`-stage cost with terminal cost `h` (p. 286):
`J_N(x, π, h) = E^π_x [ ∑_{t=0}^{N-1} c(X_t, A_t) + h(X_N) ]`, a Bochner integral. -/
noncomputable def JN (M : BorelCMP S A) (π : Policy M) (N : ℕ) (h : S → ℝ) (x : S) : ℝ :=
  ∫ ω, (∑ t ∈ Finset.range N, M.c (ω t)) + h (ω N).1 ∂(pathMeasure M π x)

/-- The `N`-stage cost without terminal cost, `J_N(x, π) = J_N(x, π, 0)` (p. 286). -/
noncomputable def JN0 (M : BorelCMP S A) (π : Policy M) (N : ℕ) (x : S) : ℝ :=
  JN M π N (fun _ => 0) x

/-- The optimal `N`-stage cost with terminal cost `h`: `J*_N(x, h) = inf_{π ∈ Π} J_N(x, π, h)`,
the infimum over all admissible policies. For bounded `c` and `h` the family is bounded below
by `-N · sup |c| - sup |h|`, so the real infimum is the true one. -/
noncomputable def JNopt (M : BorelCMP S A) (N : ℕ) (h : S → ℝ) (x : S) : ℝ :=
  ⨅ π : Policy M, JN M π N h x

/-- `h ∈ 𝓜_b(S)`: `h` is measurable and bounded. -/
def IsBoundedMeas (h : S → ℝ) : Prop :=
  Measurable h ∧ ∃ C, ∀ x, |h x| ≤ C

/-- `c ∈ 𝓜_b(K)`: the one-step cost is bounded on `K` (it is measurable by `BorelCMP.c_meas`). -/
def CostBounded (M : BorelCMP S A) : Prop :=
  ∃ C, ∀ x, ∀ a ∈ M.U x, |M.c (x, a)| ≤ C

/-- A canonical triplet `(R, H, π)` (p. 316, (6.4)): `R, H ∈ 𝓜_b(S)`, `π ∈ Π`, and
`J_N(x, π, H) = J*_N(x, H) = H(x) + N R(x)` for all `N ∈ ℕ₀` and `x ∈ S`. -/
def IsCanonical (M : BorelCMP S A) (R H : S → ℝ) (π : Policy M) : Prop :=
  IsBoundedMeas R ∧ IsBoundedMeas H ∧
    ∀ (N : ℕ) (x : S), JN M π N H x = JNopt M N H x ∧ JNopt M N H x = H x + N * R x

/-- The span seminorm (p. 283): `span(v) = sup_{w, w'} {v(w) - v(w')} = sup v - inf v`, for a
bounded `v`. -/
noncomputable def span (v : S → ℝ) : ℝ :=
  (⨆ x, v x) - (⨅ x, v x)

/-- The average cost (p. 286): `J(x, π) = limsup_{N → ∞} (1/N) J_N(x, π)`, computed in the
extended reals `EReal` (the term `N = 0` is `0` and does not affect the limit superior). -/
noncomputable def avgCost (M : BorelCMP S A) (π : Policy M) (x : S) : EReal :=
  limsup (fun N : ℕ => ((JN0 M π N x / N : ℝ) : EReal)) atTop

/-- The optimal average cost (p. 287): `J*(x) = inf_{π ∈ Π} J(x, π)`, the infimum over all
admissible policies, in `EReal`. -/
noncomputable def optAvg (M : BorelCMP S A) (x : S) : EReal :=
  ⨅ π : Policy M, avgCost M π x

/-- Strong average optimality (p. 316, (6.5)):
`limsup_{N → ∞} (1/N) J_N(x, π*) ≤ liminf_{N → ∞} (1/N) J_N(x, π)` for all `x ∈ S` and `π ∈ Π`,
both sides computed in `EReal`. -/
def IsStrongAvgOptimal (M : BorelCMP S A) (πs : Policy M) : Prop :=
  ∀ (x : S) (π : Policy M),
    limsup (fun N : ℕ => ((JN0 M πs N x / N : ℝ) : EReal)) atTop ≤
      liminf (fun N : ℕ => ((JN0 M π N x / N : ℝ) : EReal)) atTop

end ArapostathisAC.CanonicalPolicy


