-- Prove2me | Definitions.Def_LearnVsOpt_Play
-- name    : LearnVsOpt_Play
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:51.271087+00:00
-- url     : https://prove2.me/theorems/9f854008-c083-4a79-912c-7f30490f95ae
-- title:
--   The law of play: adaptive optimizers, outcomes, expectations, piecewise stationarity
-- statement:
--   An **adaptive optimizer** is a kernel $\sigma$ from the past $(i_r,m_r,j_r)_{r<t}$, with $m_r$ the learner's realized forecast index, to the law of $i_t$. In round $t$, $i_t\sim\sigma(\text{past})$, and independently of $i_t$ given the past the learner runs its move on its own state; then it observes the realized vector and updates. The **law of play** is the resulting distribution on the records of the $T$ rounds. It has finite support, and expectations are finite sums.
--
--   From an outcome one reads: $\mathcal T_t$, the active rounds up to $t$; the entries $M[i_t,j_t]$; the iterates of $F_t$; the units charged in round $t$; and the norms $\|R_t\|_{L^2},\|L_t\|_2,\|Z_t\|$ of the state after round $t$. Also defined are $\langle Z_{t-1},\bar\delta_t(v)\rangle=\mathbb E_{f\sim F_t}\langle Z_{t-1},\delta(f,v)\rangle$ for an outcome vector $v$, and the three lines of (22):
--   $$
--   \Big\langle Z_{\tau-1},\bar\delta_\tau(k_\tau)-\sum_k f^{\star}_k\bar\delta_\tau(k)\Big\rangle,\quad \Big\langle Z_{\tau-1},\sum_k\big(f^{\star}_k-\hat f_{\tau-1,k}\big)\bar\delta_\tau(k)\Big\rangle,\quad \sum_k\hat f_{\tau-1,k}\big\langle Z_{\tau-1},\bar\delta_\tau(k)\big\rangle .
--   $$
--   Here $f^\star$ is the law of the realized vector under $i_\tau\sim x$, and $\hat f_{\tau-1}$ is the empirical distribution of the outcomes of the earlier rounds of the interval, active or not, or the point mass on $uc^{(1)}=0$ in its first round.
--
--   The optimizer is **piecewise stationary** when $[T]$ is partitioned into $S$ contiguous intervals $I_s$, and $i_t\sim x^{(s)}$ in each round of $I_s$ whatever the past.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, §2, p.6; pp.2–3; Lemma 6.3, (22), p.18; Claim 6.4, p.19

import Mathlib
import Definitions.Def_LearnVsOpt_Algorithm

open scoped Matrix

namespace LearnVsOpt

variable {nO nL : ℕ}

/-- **An adaptive optimizer**: a kernel from the past `(i_r, m_r, j_r)`, `r < t`, to the law of `i_t`,
where `m_r` is the learner's realized index in round `r`.

**Formalization Note.** A round's moves are simultaneous: the kernel sees the past rounds, and neither
the current draw `f^(t)` nor `j_t`. -/
abbrev Optimizer (nO nL : ℕ) := List (Fin nO × ℕ × Fin nL) → PMF (Fin nO)

/-- The record of one round: `i_t`, the learner's move, the units the learner charged in the round
(its move and its update), and its state after the round. -/
structure Record (nO nL : ℕ) where
  /-- `i_t`. -/
  i : Fin nO
  /-- The learner's move. -/
  act : Action nL
  /-- The units the learner charged in this round. -/
  charged : ℕ
  /-- The learner's state after the round. -/
  st : LState nL

/-- A play: the records of the rounds so far, round `t` at position `t − 1`. -/
abbrev Outcome (nO nL : ℕ) := List (Record nO nL)

/-- The past as the optimizer sees it. -/
def pastOf (ω : Outcome nO nL) : List (Fin nO × ℕ × Fin nL) :=
  ω.map fun r => (r.i, r.act.m, r.act.j)

/-- The learner's current state. -/
def lastState (ω : Outcome nO nL) : LState nL :=
  (ω.getLast?.map Record.st).getD (LState.init nL)

/-- One round after the play `ω`: `i_t ∼ σ(past)`; independently, the learner runs its move on its own
state; then it observes `(U_L[i_t, :], C_L[i_t, :])` and updates its state. -/
noncomputable def roundLaw (G : Game nO nL) (σ : Optimizer nO nL) (P : Params nL)
    (ω : Outcome nO nL) : PMF (Record nO nL) :=
  (σ (pastOf ω)).bind fun i =>
    (act P (lastState ω) 0).bind fun r =>
      let o := observe P (lastState ω) r.1 (G.UL i, G.CL i)
      PMF.pure ⟨i, r.1, r.2 + o.cost, o.val⟩

/-- The law of the first `t` rounds. -/
noncomputable def lawUpTo (G : Game nO nL) (σ : Optimizer nO nL) (P : Params nL) :
    ℕ → PMF (Outcome nO nL)
  | 0 => PMF.pure []
  | t + 1 => (lawUpTo G σ P t).bind fun ω => (roundLaw G σ P ω).map fun r => ω ++ [r]

/-- **The law of play** over the `T = P.T` rounds. -/
noncomputable def law (G : Game nO nL) (σ : Optimizer nO nL) (P : Params nL) : PMF (Outcome nO nL) :=
  lawUpTo G σ P P.T

/-- Expectation under a law.

**Formalization Note.** All the laws here have finite support (finitely many actions, finitely many
iterates, finitely many rounds), so the sum is finite. -/
noncomputable def expect {α : Type} (μ : PMF α) (g : α → ℝ) : ℝ := ∑' a, (μ a).toReal * g a

/-- `max_{t ≤ T} g t`, over `t ∈ {1, …, T}`. -/
noncomputable def maxRounds (T : ℕ) (hT : 1 ≤ T) (g : ℕ → ℝ) : ℝ :=
  (Finset.Icc 1 T).sup' ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hT⟩⟩ g

/-- The record of round `t ≥ 1`. -/
def Outcome.rec? (ω : Outcome nO nL) (t : ℕ) : Option (Record nO nL) := ω[t - 1]?

/-- The learner's state after round `t` (the initial state for `t = 0`). -/
def Outcome.stAt (ω : Outcome nO nL) (t : ℕ) : LState nL :=
  if t = 0 then LState.init nL else ((ω.rec? t).map Record.st).getD (LState.init nL)

/-- Round `t` is active. -/
def Outcome.IsActive (ω : Outcome nO nL) (t : ℕ) : Prop :=
  ∃ r, ω.rec? t = some r ∧ r.act.active = true

open Classical in
/-- `𝒯_t`: the active rounds up to round `t`. -/
noncomputable def Outcome.activeSet (ω : Outcome nO nL) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter ω.IsActive

/-- The entry `M[i_t, j_t]` of a payoff or cost matrix in round `t`. -/
def Outcome.entry (ω : Outcome nO nL) (M : Matrix (Fin nO) (Fin nL) ℝ) (t : ℕ) : ℝ :=
  ((ω.rec? t).map fun r => M r.i r.act.j).getD 0

/-- `Σ_{t=1}^{T} M[i_t, j_t]`. -/
noncomputable def Outcome.total (ω : Outcome nO nL) (M : Matrix (Fin nO) (Fin nL) ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ω.entry M t

/-- The iterates of `F_t`, as stored by round `t`. -/
def Outcome.iters (ω : Outcome nO nL) (t : ℕ) : List (Iterate nL) :=
  ((ω.rec? t).map fun r => r.act.iters).getD []

/-- The units the learner charged in round `t`. -/
def Outcome.chargedAt (ω : Outcome nO nL) (t : ℕ) : ℕ :=
  ((ω.rec? t).map Record.charged).getD 0

/-- The realized vector `uc_t = (U_L[i_t, :], C_L[i_t, :])`. -/
def Outcome.ucAt (ω : Outcome nO nL) (G : Game nO nL) (t : ℕ) : UC nL :=
  ((ω.rec? t).map fun r => (G.UL r.i, G.CL r.i)).getD 0

/-- `‖R_t‖_{L²}`. -/
noncomputable def Outcome.normR (ω : Outcome nO nL) (t : ℕ) : ℝ :=
  JointVec.normR (ω.stAt t).dict.length (ω.stAt t).Z

/-- `‖L_t‖₂`. -/
noncomputable def Outcome.normL (ω : Outcome nO nL) (t : ℕ) : ℝ :=
  JointVec.normL (ω.stAt t).Z

/-- `‖Z_t‖`. -/
noncomputable def Outcome.normZ (ω : Outcome nO nL) (t : ℕ) : ℝ :=
  JointVec.norm (ω.stAt t).dict.length (ω.stAt t).Z

/-- `E_{f∼F}[g(f)]` for the uniform law on a list of iterates. -/
noncomputable def avgF (iters : List (Iterate nL)) (g : Iterate nL → ℝ) : ℝ :=
  (iters.map g).sum / iters.length

/-- `E_{f∼F_t}[e_{i_t}⊤ M y(f)]`: the expected entry of `M` in round `t` when the learner plays the
forecast's response, as in Theorem 4.2, p.10. -/
noncomputable def Outcome.forecastEntry (ω : Outcome nO nL) (M : Matrix (Fin nO) (Fin nL) ℝ) (t : ℕ) :
    ℝ :=
  ((ω.rec? t).map fun r => avgF r.act.iters fun it => M r.i ⬝ᵥ it.s.y).getD 0

/-- `⟨Z_{t−1}, δ̄_t(v)⟩ = E_{f∼F_t}[⟨Z_{t−1}, δ(f, v)⟩]`, for an outcome vector `v`, in round `t`.

**Formalization Note.** The inner product runs over the coordinates of the dictionary `𝒰𝒞_{t−1}`:
`Z_{t−1}` vanishes at any larger index, so a vector `v` not yet observed needs no index. -/
noncomputable def Outcome.drift (ω : Outcome nO nL) (ρL : ℝ) (t : ℕ) (v : UC nL) : ℝ :=
  let st := ω.stAt (t - 1)
  avgF (ω.iters t) fun it => JointVec.inner st.dict.length st.Z (delta ρL st.dict it.s it.fn v)

/-- `⟨Z_{τ−1}, δ̄_τ(k_τ) − Σ_k f^{⋆}_k δ̄_τ(k)⟩`, the first line of (22), p.18, with `f^⋆` the law of
`k_τ` induced by `i_τ ∼ x`, written as a sum over the optimizer's actions. -/
noncomputable def Outcome.xi₁ (ω : Outcome nO nL) (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ)
    (τ : ℕ) : ℝ :=
  ω.drift ρL τ (ω.ucAt G τ) - ∑ i, x i * ω.drift ρL τ (G.UL i, G.CL i)

open Classical in
/-- `Σ_k f̂_{τ−1,k} ⟨Z_{τ−1}, δ̄_τ(k)⟩`, the third line of (22), p.18: `f̂_{τ−1}` is the empirical
distribution of the outcomes of the rounds of the interval `I` before `τ`, active or not, and `e_1`,
the point mass on `uc^(1) = 0`, in the first round of `I` (p.18). -/
noncomputable def Outcome.xi₃ (ω : Outcome nO nL) (G : Game nO nL) (ρL : ℝ) (I : Finset ℕ)
    (τ : ℕ) : ℝ :=
  let prior := I.filter (· < τ)
  if prior = ∅ then ω.drift ρL τ 0
  else (∑ r ∈ prior, ω.drift ρL τ (ω.ucAt G r)) / prior.card

/-- `⟨Z_{τ−1}, Σ_k (f^⋆_k − f̂_{τ−1,k}) δ̄_τ(k)⟩`, the second line of (22), p.18. -/
noncomputable def Outcome.xi₂ (ω : Outcome nO nL) (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ)
    (I : Finset ℕ) (τ : ℕ) : ℝ :=
  ∑ i, x i * ω.drift ρL τ (G.UL i, G.CL i) - ω.xi₃ G ρL I τ

/-- The optimizer draws `i_t ∼ x` in every round `t ∈ I`, whatever the past. -/
def IsStationaryOn (σ : Optimizer nO nL) (I : Finset ℕ) (x : Fin nO → ℝ) : Prop :=
  ∀ t ∈ I, ∀ past : List (Fin nO × ℕ × Fin nL), past.length = t - 1 →
    ∀ i, (σ past i).toReal = x i

/-- **Piecewise stationarity** (Lemma 6.3, p.18): `[T]` is partitioned into `S` contiguous intervals,
and in each interval `I s` the optimizer draws `i_t ∼ x s` independently, `x s ∈ Δ_{n_O}`. -/
def IsPiecewiseStationary (σ : Optimizer nO nL) (T S : ℕ) (I : Fin S → Finset ℕ)
    (x : Fin S → Fin nO → ℝ) : Prop :=
  (∀ s, ∃ a b, I s = Finset.Ioc a b) ∧
  (∀ s s', s ≠ s' → Disjoint (I s) (I s')) ∧
  (∀ t, t ∈ Finset.Icc 1 T ↔ ∃ s, t ∈ I s) ∧
  (∀ s, x s ∈ stdSimplex ℝ (Fin nO)) ∧
  ∀ s, IsStationaryOn σ (I s) (x s)

end LearnVsOpt


