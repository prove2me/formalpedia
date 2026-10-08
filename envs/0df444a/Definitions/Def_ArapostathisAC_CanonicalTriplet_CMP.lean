-- Prove2me | Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
-- name    : ArapostathisAC_CanonicalTriplet_CMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:59:43.984554+00:00
-- url     : https://prove2.me/theorems/9014caab-cf99-4634-9418-ce11161f8a02
-- title:
--   The Borel controlled Markov process of §2, its admissible policies, path measures, N-stage costs and canonical triplets
-- statement:
--   This file sets up the discrete-time controlled Markov process (CMP) of Arapostathis, Borkar, Fernández-Gaucherand, Ghosh and Marcus (1993), §2.1–§2.2, and the objects of §6.1 needed for canonical triplets.
--
--   **Model.** A CMP is a five-tuple $(\mathbf S,\mathbf A,U,P,c)$:
--   1. $\mathbf S$ (states) and $\mathbf A$ (actions) are Borel spaces;
--   2. $U$ assigns to each state $x$ a nonempty compact set $U(x)\subseteq\mathbf A$ of admissible actions, and the set of admissible pairs $\mathbf K=\{(x,a):a\in U(x)\}$ is measurable;
--   3. $P(dy\mid x,a)$ is a stochastic kernel on $\mathbf S$ given $\mathbf K$;
--   4. $c:\mathbf K\to\mathbb R$ is a measurable one-stage cost with $c\ge 0$ (Assumption 2.1 of the paper, assumed throughout).
--
--   **Policies.** A history is $h_t=(x_0,a_0,\dots,x_{t-1},a_{t-1},x_t)$. An admissible policy $\pi=(\pi_t)_{t\ge0}$ is a sequence of stochastic kernels $\pi_t(\cdot\mid h_t)$ on $\mathbf A$ with $\pi_t(U(x_t)\mid h_t)=1$; their set is $\Pi$. A stationary deterministic policy ($\Pi_{SD}$) is a measurable map $f:\mathbf S\to\mathbf A$ with $f(x)\in U(x)$, which chooses $a_t=f(x_t)$ at every epoch. An initial state $x$ and a policy $\pi$ determine a probability measure $\mathcal P^\pi_x$ on trajectories $((x_0,a_0),(x_1,a_1),\dots)$ with $x_0=x$, $a_t\sim\pi_t(\cdot\mid h_t)$ and $x_{t+1}\sim P(\cdot\mid x_t,a_t)$; $E^\pi_x$ is its expectation.
--
--   **Costs.** For a terminal cost $h$ and a horizon $N\in\mathbb N_0$,
--   $$J_N(x,\pi,h)=E^\pi_x\Big[\sum_{t=0}^{N-1}c(X_t,A_t)+h(X_N)\Big],\qquad J^*_N(x,h)=\inf_{\pi\in\Pi}J_N(x,\pi,h),$$
--   and $J_N(x,\pi)=J_N(x,\pi,0)$. $\mathcal M_b(\mathbf S)$ is the set of bounded measurable real functions on $\mathbf S$, and $c\in\mathcal M_b(\mathbf K)$ means that $c$ is bounded on $\mathbf K$.
--
--   **Canonical triplets** (Dynkin–Yushkevich; (6.4) of the paper). For $R,H\in\mathcal M_b(\mathbf S)$ and $\pi^*\in\Pi$, the triplet $(R,H,\pi^*)$ is canonical if
--   $$J_N(x,\pi^*,H)=J^*_N(x,H)=H(x)+NR(x)\qquad\forall N\in\mathbb N_0,\ x\in\mathbf S.$$
--
--   **The coupled optimality equations** (6.6)–(6.7), for $\rho,h\in\mathcal M_b(\mathbf S)$ and $f\in\Pi_{SD}$, in the form "the infimum equals the left side and is attained at $f(x)$": for every $x$,
--   $$\rho(x)=\int_{\mathbf S}\rho(y)P(dy\mid x,f(x))\le\int_{\mathbf S}\rho(y)P(dy\mid x,a)\quad\forall a\in U(x),$$
--   $$\rho(x)+h(x)=c(x,f(x))+\int_{\mathbf S}h(y)P(dy\mid x,f(x))\le c(x,a)+\int_{\mathbf S}h(y)P(dy\mid x,a)\quad\forall a\in U(x).$$
--
--   These objects are the vocabulary of the multichain average-cost theory with bounded costs, where the optimal average cost $\rho(\cdot)$ may depend on the initial state.
--
--   **Formalization Note.** $\Pi$ is the class of all history-dependent randomized admissible policies, as on p. 285 of the paper, and $J^*_N$ is the infimum over all of it. The path measure is Mathlib's `Kernel.trajMeasure` (Ionescu-Tulcea). $J_N$ is a Bochner integral; it is the genuine expectation whenever $c$ is bounded on $\mathbf K$ and $h$ is bounded measurable, which every statement using it assumes. $J^*_N$ is a real infimum; when $c\ge0$ on $\mathbf K$ and $h$ is bounded, the family $\{J_N(x,\pi,h)\}_\pi$ is bounded below by $-\sup|h|$, and the policy class is nonempty whenever a stationary policy is given, so the infimum is the true one. The cost $c$ and the kernel $P$ are given on all of $\mathbf S\times\mathbf A$; admissible policies only visit $\mathbf K$, and the statements evaluate them only on $\mathbf K$. The definitions do not assume continuity of $c$ or $P$ (Assumptions 2.2, 2.3, 6.1 of the paper are not used in §6.1's Theorem 6.2).
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 284–286 (§2.1–§2.2, J_N(μ, π, h)), p. 288 (Assumption 2.1), p. 316 ((6.4)), pp. 316–317 ((6.6), (6.7))

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ArapostathisAC.CanonicalTriplet

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

/-- The stationary deterministic policies `Π_SD` (p. 286): measurable maps `f : S → A` with
`f(x) ∈ U(x)`. -/
def StationaryPolicy (M : BorelCMP S A) : Type _ :=
  {f : S → A // Measurable f ∧ ∀ x, f x ∈ M.U x}

/-- A stationary deterministic policy `f` as an admissible policy: at every epoch the action
`f(x_t)` is chosen with probability one. -/
noncomputable def StationaryPolicy.toPolicy {M : BorelCMP S A} (f : StationaryPolicy M) :
    Policy M where
  rule _ := Kernel.deterministic (fun h => f.1 h.2) (f.2.1.comp measurable_snd)
  adm t hist := by
    rw [Kernel.deterministic_apply' _ _ (M.measurableSet_U hist.2).compl]
    simp [f.2.2 hist.2]

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
the infimum over all admissible policies. -/
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

/-- Equation (6.6) with the infimum attained at `f(x)`, for every `x`:
`ρ(x) = ∫ ρ(y) P(dy | x, f(x))` and `ρ(x) ≤ ∫ ρ(y) P(dy | x, a)` for every `a ∈ U(x)`; that is,
`ρ(x) = inf_{a ∈ U(x)} ∫ ρ(y) P(dy | x, a)` and `f(x)` attains the infimum. -/
def Eq66 (M : BorelCMP S A) (ρ : S → ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ x, ρ x = ∫ y, ρ y ∂(M.P (x, f.1 x)) ∧ ∀ a ∈ M.U x, ρ x ≤ ∫ y, ρ y ∂(M.P (x, a))

/-- Equation (6.7) with the infimum attained at `f(x)`, for every `x`:
`ρ(x) + h(x) = c(x, f(x)) + ∫ h(y) P(dy | x, f(x))` and
`ρ(x) + h(x) ≤ c(x, a) + ∫ h(y) P(dy | x, a)` for every `a ∈ U(x)`. -/
def Eq67 (M : BorelCMP S A) (ρ h : S → ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ x, ρ x + h x = M.c (x, f.1 x) + ∫ y, h y ∂(M.P (x, f.1 x)) ∧
    ∀ a ∈ M.U x, ρ x + h x ≤ M.c (x, a) + ∫ y, h y ∂(M.P (x, a))

end ArapostathisAC.CanonicalTriplet


