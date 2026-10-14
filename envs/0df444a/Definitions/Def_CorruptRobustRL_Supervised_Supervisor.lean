-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supervisor
-- name    : CorruptRobustRL_Supervised_Supervisor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:37.304665+00:00
-- url     : https://prove2.me/theorems/8946fc62-9d4c-4475-bfdf-ab520fd74b19
-- title:
--   §4.1–4.2, pp. 13–16 — Q-supervisors, confidence-admissibility, plausible sets, Q-supervised policies, UCB visitation ratio, Bellman errors, model-estimates and validity
-- statement:
--   This file sets up the SuperVIsed framework of §4.
--
--   **Q-supervisor.** A Q-supervisor $\mathcal T=(\bar Q,\underline Q,\mathcal A,\pi^{\mathrm{ucb}})$ consists of upper and lower Q-estimates $\bar Q_h(x,a),\underline Q_h(x,a)$, active sets $\mathcal A_h(x)\subseteq\mathcal A$ and a deterministic UCB policy. It is a Q-supervisor in the sense of p. 13 when, at every stage $h\le H$, $\bar Q_h,\underline Q_h\in[0,H]$ and $\pi^{\mathrm{ucb}}_h(x)\in\mathcal A_h(x)$ maximizes $\bar Q_h(x,\cdot)$ over $\mathcal A_h(x)$. With $\bar V_{H+1}=\underline V_{H+1}=0$,
--   $$\bar V_h(x)=\bar Q_h(x,\pi^{\mathrm{ucb}}_h(x)),\qquad \underline V_h(x)=\max_{a\in\mathcal A_h(x)}\underline Q_h(x,a).$$
--
--   **Confidence-admissibility (Definition 4.1).** $\pi^\star_h(x)\subseteq\mathcal A_h(x)$ and $\underline Q_h\le Q^\star_h\le\bar Q_h$ at every stage, state and action.
--
--   **Plausible sets and supervision (Definition 4.2).** $\mathcal A^{\mathrm{plaus}}_h(x)=\{a\in\mathcal A_h(x):\bar Q_h(x,a)\ge\underline Q_h(x,a')\ \forall a'\in\mathcal A_h(x)\}$. A randomized Markovian policy is Q-supervised by $\mathcal T$ if every action it plays with positive probability at stage $h$ in state $x$ lies in $\mathcal A^{\mathrm{plaus}}_h(x)$.
--
--   **Bellman errors (Definition 4.5).**
--   $$\overline{\mathbf{Bell}}_h(x,a)=\bar Q_h(x,a)-\big(r^\star(x,a)+p^\star(x,a)^\top\bar V_{h+1}\big),\qquad \underline{\mathbf{Bell}}_h(x,a)=\underline Q_h(x,a)-\big(r^\star(x,a)+p^\star(x,a)^\top\underline V_{h+1}\big).$$
--
--   **UCB visitation ratio (Definition 4.4).** A policy $\pi$ has UCB visitation ratio at most $\rho\ge1$ with respect to $\mathcal T$ if for all stages $h\le\tau$ and all $(x,a)$
--   $$P^{\pi\oplus_h\pi^{\mathrm{ucb}}}[(x_\tau,a_\tau)=(x,a)]\le\rho\,P^{\pi}[(x_\tau,a_\tau)=(x,a)].$$
--
--   **Model-estimates and validity (Definitions 4.6–4.7).** A model-estimate $\mathfrak m=(\tilde r,\tilde p,b)$ has $\tilde r\in[0,1]$, each $\tilde p(x,a)$ a probability vector and $b\in[0,H]$. It is valid with respect to $\mathcal T$ if for every stage $h$ and every $(x,a)$, writing $\mathrm{dev}(V)=\tilde r(x,a)-r^\star(x,a)+(\tilde p(x,a)-p^\star(x,a))^\top V$, either (a) $\tilde p(x,a)\ge0$ and $|\mathrm{dev}(V^\star_{h+1})|\le b(x,a)$, or (b) $|\mathrm{dev}(V)|\le b(x,a)$ for each $V\in\{V^\star_{h+1},\bar V_{h+1},\underline V_{h+1}\}$.
--
--   **Formalization Note** Stages are 0-based in Lean: the paper's stage $h\in[H]$ is Lean's `h - 1`, and the terminal values $V_{H+1}\equiv0$ sit at Lean index `H`. Three readings are fixed here. (1) The UCB policy maximizes $\bar Q$ over the active set, as in Algorithm 2 (line 9) and the proofs of Lemma D.1 and Proposition 4.1; p. 13 writes $\arg\max_a$ over all actions. (2) The visitation ratio is cross-multiplied, so a state-action pair that neither policy visits imposes no constraint (footnote 18). (3) The paper types $\tilde p$ as an element of $[0,1]^{\mathcal X}$; in the tabular setting $\hat p$ is an empirical distribution (2.5), so `IsModelEst` requires a probability vector. The disjunction (a)/(b) of validity is taken pointwise in $(h,x,a)$, the scope in which Definition 4.7 states it. $\underline V$ on an empty active set is $0$; this never arises for a Q-supervisor.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, pp. 13–16, Q-supervisor (p. 13), Definitions 4.1, 4.2, 4.4, 4.5, 4.6 (model-estimates), 4.7

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP

namespace CorruptRobustRL.Supervised

open Finset

variable {X A : Type}

/-- A Q-supervisor `𝒯 = (Q̄, Q̲, 𝒜, π^ucb)` (p. 13): upper and lower Q-estimates, active sets and a
deterministic UCB policy, all indexed by the 0-based stage. -/
structure QSupervisor (X A : Type) where
  Qbar : ℕ → X → A → ℝ
  Qlow : ℕ → X → A → ℝ
  act : ℕ → X → Finset A
  ucb : DetPolicy X A

namespace QSupervisor

/-- The three items of p. 13 at every stage `h < H`: `Q̄, Q̲ ∈ [0, H]`, and the UCB policy picks an
action of the active set maximizing `Q̄` over the active set (Algorithm 2, line 9). -/
def IsQSupervisor (H : ℕ) (T : QSupervisor X A) : Prop :=
  (∀ h < H, ∀ x a, 0 ≤ T.Qbar h x a ∧ T.Qbar h x a ≤ H ∧ 0 ≤ T.Qlow h x a ∧ T.Qlow h x a ≤ H) ∧
  ∀ h < H, ∀ x, T.ucb h x ∈ T.act h x ∧ ∀ a ∈ T.act h x, T.Qbar h x a ≤ T.Qbar h x (T.ucb h x)

/-- `V̄_h(x) = Q̄_h(x, π^ucb_h(x))` for `h < H`, and `V̄_{H+1} ≡ 0` (Definition 4.5). -/
noncomputable def Vbar (H : ℕ) (T : QSupervisor X A) (h : ℕ) (x : X) : ℝ :=
  if h < H then T.Qbar h x (T.ucb h x) else 0

/-- `V̲_h(x) = max_{a ∈ 𝒜_h(x)} Q̲_h(x, a)` for `h < H`, and `V̲_{H+1} ≡ 0` (Definition 4.5).
The value on an empty active set is `0`; it never arises for a Q-supervisor (`ucb h x ∈ act h x`). -/
noncomputable def Vlow (H : ℕ) (T : QSupervisor X A) (h : ℕ) (x : X) : ℝ :=
  if h < H then
    (if hne : (T.act h x).Nonempty then (T.act h x).sup' hne (T.Qlow h x) else 0)
  else 0

/-- Confidence-admissibility (Definition 4.1): at every stage `h < H` and state `x`, the active set
contains every optimal action, and `Q̲_h ≤ Q⋆_h ≤ Q̄_h`. -/
def IsAdmissible [Fintype X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (H : ℕ) (T : QSupervisor X A) : Prop :=
  ∀ h < H, ∀ x, optActions M H h x ⊆ T.act h x ∧
    ∀ a, T.Qlow h x a ≤ Qstar M H h x a ∧ Qstar M H h x a ≤ T.Qbar h x a

/-- The plausible set `𝒜^plaus_h(x) = {a ∈ 𝒜_h(x) : Q̄_h(x, a) ≥ Q̲_h(x, a') ∀ a' ∈ 𝒜_h(x)}` (p. 13). -/
noncomputable def plaus (T : QSupervisor X A) (h : ℕ) (x : X) : Finset A := by
  classical
  exact (T.act h x).filter (fun a => ∀ a' ∈ T.act h x, T.Qlow h x a' ≤ T.Qbar h x a)

/-- Upper Bellman error (Definition 4.5):
`Bell̄_h(x, a) = Q̄_h(x, a) − (r⋆(x, a) + p⋆(x, a)ᵀ V̄_{h+1})`. -/
noncomputable def upperBell [Fintype X] (M : NominalMDP X A) (H : ℕ) (T : QSupervisor X A)
    (h : ℕ) (x : X) (a : A) : ℝ :=
  T.Qbar h x a - (M.rstar x a + ∑ x', M.pstar x a x' * Vbar H T (h + 1) x')

/-- Lower Bellman error (Definition 4.5):
`Bell̲_h(x, a) = Q̲_h(x, a) − (r⋆(x, a) + p⋆(x, a)ᵀ V̲_{h+1})`. -/
noncomputable def lowerBell [Fintype X] (M : NominalMDP X A) (H : ℕ) (T : QSupervisor X A)
    (h : ℕ) (x : X) (a : A) : ℝ :=
  T.Qlow h x a - (M.rstar x a + ∑ x', M.pstar x a x' * Vlow H T (h + 1) x')

end QSupervisor

open QSupervisor

/-- A randomized Markovian policy is Q-supervised by `T` (Definition 4.2): every action it plays
with positive probability lies in the plausible set, at every stage `h < H` and every state. For a
mixture with nonnegative weights, `P[π_h(x) = a] > 0` iff some atom of positive weight plays `a`. -/
def IsQSupervised (H : ℕ) (π : Mixture X A) (T : QSupervisor X A) : Prop :=
  ∀ i, 0 < π.w i → ∀ h < H, ∀ x, π.σ i h x ∈ plaus T h x

/-- UCB visitation ratio at most `ρ` (Definition 4.4), cross-multiplied: `ρ ≥ 1` and for all
0-based stages `h ≤ τ < H` and all `(x, a)`,
`P^{π ⊕_h π^ucb}[(x_τ, a_τ) = (x, a)] ≤ ρ · P^π[(x_τ, a_τ) = (x, a)]`.
Only the UCB policy of the Q-supervisor enters, so it is the argument `ucb`. -/
def HasVisitRatio [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    (M : NominalMDP X A) (H : ℕ) (π : Mixture X A) (ucb : DetPolicy X A) (ρ : ℝ) : Prop :=
  1 ≤ ρ ∧ ∀ h τ x a, h ≤ τ → τ < H → mixOcc M H (concatMix π h ucb) τ x a ≤ ρ * mixOcc M H π τ x a

/-- A model-estimate `𝔪 = (r̃, p̃, b)` (p. 16): estimated rewards, estimated transitions, bonus. -/
structure ModelEst (X A : Type) where
  r : X → A → ℝ
  p : X → A → X → ℝ
  b : X → A → ℝ

/-- The ranges of a tabular model-estimate (Definition 4.6, p. 16, with `p̃` the empirical
distribution of (2.5)): `r̃ ∈ [0, 1]`, each `p̃(x, a)` a probability vector, `b ∈ [0, H]`. -/
def ModelEst.IsModelEst [Fintype X] (H : ℕ) (m : ModelEst X A) : Prop :=
  ∀ x a, (0 ≤ m.r x a ∧ m.r x a ≤ 1) ∧ IsProbVec (m.p x a) ∧ (0 ≤ m.b x a ∧ m.b x a ≤ H)

/-- The deviation `r̃(x, a) − r⋆(x, a) + (p̃(x, a) − p⋆(x, a))ᵀ V` of Definition 4.7. -/
noncomputable def ModelEst.dev [Fintype X] (M : NominalMDP X A) (m : ModelEst X A)
    (V : X → ℝ) (x : X) (a : A) : ℝ :=
  m.r x a - M.rstar x a + ∑ x', (m.p x a x' - M.pstar x a x') * V x'

/-- Validity of a model-estimate with respect to a Q-supervisor (Definition 4.7): for every stage
`h < H` and every `(x, a)`, either (a) `p̃(x, a) ≥ 0` and `|dev(V⋆_{h+1})| ≤ b(x, a)`, or (b)
`|dev(V)| ≤ b(x, a)` for each `V ∈ {V⋆_{h+1}, V̄_{h+1}, V̲_{h+1}}`. -/
def ModelEst.IsValid [Fintype X] [Fintype A] [Nonempty A]
    (M : NominalMDP X A) (H : ℕ) (T : QSupervisor X A) (m : ModelEst X A) : Prop :=
  ∀ h < H, ∀ x a,
    ((∀ x', 0 ≤ m.p x a x') ∧ |m.dev M (Vstar M H (h + 1)) x a| ≤ m.b x a) ∨
    (|m.dev M (Vstar M H (h + 1)) x a| ≤ m.b x a ∧
      |m.dev M (Vbar H T (h + 1)) x a| ≤ m.b x a ∧
      |m.dev M (Vlow H T (h + 1)) x a| ≤ m.b x a)

end CorruptRobustRL.Supervised


