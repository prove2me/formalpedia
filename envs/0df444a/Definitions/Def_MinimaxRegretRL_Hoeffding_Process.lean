-- Prove2me | Definitions.Def_MinimaxRegretRL_Hoeffding_Process
-- name    : MinimaxRegretRL_Hoeffding_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:46:16.554292+00:00
-- url     : https://prove2.me/theorems/5d925933-b0b5-4736-b43d-8298e8261111
-- title:
--   Algorithms 1–3 — UCBVI-CH process and finite path law
-- statement:
--   UCBVI-CH collects the transition triples from earlier episodes and computes pooled counts $N_k(x,a,y)$ and $N_k(x,a)$. On a visited state-action pair it estimates $\widehat P_k(y\mid x,a)=N_k(x,a,y)/N_k(x,a)$. Algorithm 2 computes $Q_{k,h}$ backward, taking the minimum of the preceding episode's $Q$, the horizon $H$, and the empirical Bellman value with Algorithm 3's bonus; on an unvisited pair it sets $Q_{k,h}=H$. A greedy policy is selected at every state and step.
--
--   $$b_{k,h}(x,a)=\frac{7H\ln(5SAT/\delta)}{\sqrt{N_k(x,a)}},\qquad T=KH.$$
--
--   An outcome specifies all next-state draws. Starting states may depend on earlier episodes. The path probability is the product of the transition probabilities along its realized path, and regret is the sum of $V_1^*-V_1^{\pi_k}$ at each episode's starting state.
--
--   **Formalization Note** The bonus is used only when $N_k(x,a)>0$. At the first episode the unused preceding $Q$ table is initialized to $H$. A selection rule is passed separately so theorems cover every maximizer tie-break. Episodes and steps are zero-based in Lean. Two logarithms are defined as printed: the algorithm's $\ln(5SAT/\delta)$ (Algorithm 3) and the theorem's $\ln(5HSAT/\delta)$ (Theorem 1, p. 5). The starting state of episode $k$ is any function of the next-state draws of episodes $1,\dots,k-1$.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), pp. 2–4, §2 and Algorithms 1–3

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_MDP

namespace MinimaxRegretRL.Hoeffding

/-- The sequence of next-state draws in `K` episodes of `H` steps. -/
abbrev Outcomes (S : Type*) (K H : ℕ) := Fin K → Fin H → S

/-- The environment's starting-state rule can inspect only earlier episodes. -/
abbrev InitialRule (S : Type*) (K H : ℕ) :=
  (k : Fin K) → (Fin k.val → Fin H → S) → S

def past {S : Type*} {K H : ℕ} (ω : Outcomes S K H) (k : Fin K) :
    Fin k.val → Fin H → S :=
  fun i h => ω ⟨i.val, lt_trans i.isLt k.isLt⟩ h

/-- State before the zero-based step `h`; the state at `H` is the final draw. -/
def stateAt {S : Type*} {K H : ℕ} (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) : ℕ → S
  | 0 => init k (past ω k)
  | h + 1 => if hh : h < H then ω k ⟨h, hh⟩ else init k (past ω k)

/-- `N_k(x,a,y)` from the completed transition triples of earlier episodes. -/
def countSAS {S A : Type*} [DecidableEq S] [DecidableEq A]
    (hist : List (S × A × S)) (x : S) (a : A) (y : S) : ℕ :=
  (hist.filter (fun t => decide (t.1 = x ∧ t.2.1 = a ∧ t.2.2 = y))).length

/-- `N_k(x,a) = ∑_y N_k(x,a,y)`, pooled over all steps. -/
def countSA {S A : Type*} [Fintype S] [DecidableEq S] [DecidableEq A]
    (hist : List (S × A × S)) (x : S) (a : A) : ℕ :=
  ∑ y : S, countSAS hist x a y

/-- The empirical transition row, read only when `N_k(x,a)>0`. -/
noncomputable def empirical {S A : Type*} [Fintype S]
    [DecidableEq S] [DecidableEq A] (hist : List (S × A × S))
    (x : S) (a : A) (y : S) : ℝ :=
  (countSAS hist x a y : ℝ) / (countSA hist x a : ℝ)

/-- Algorithm 3 uses `ln(5 S A T / δ)` with `T=KH`. -/
noncomputable def algorithmLog (S A H K : ℕ) (δ : ℝ) : ℝ :=
  Real.log ((5 * (S : ℝ) * A * (K * H : ℕ)) / δ)

/-- Theorem 1 uses the different printed logarithm `ln(5 H S A T / δ)`. -/
noncomputable def theoremLog (S A H K : ℕ) (δ : ℝ) : ℝ :=
  Real.log ((5 * (H : ℝ) * S * A * (K * H : ℕ)) / δ)

/-- Algorithm 3: `7 H L_alg / √N`, called only for positive `N`. -/
noncomputable def bonus (S A H K n : ℕ) (δ : ℝ) : ℝ :=
  7 * (H : ℝ) * algorithmLog S A H K δ / Real.sqrt n

/-- Backward recursion of Algorithm 2. The previous episode's Q is a
parameter; the `min` with it is kept. At the terminal index, the value is 0. -/
noncomputable def qFuel {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ) : ℕ → ℕ → S → A → ℝ
  | 0, _, _, _ => 0
  | fuel + 1, h, x, a =>
      if h < H then
        if countSA hist x a = 0 then (H : ℝ)
        else min (prevQ h x a) (min (H : ℝ)
          (M.R x a +
            (∑ y : S, empirical hist x a y *
              Finset.univ.sup' Finset.univ_nonempty
                (fun a' : A => qFuel M H K δ hist prevQ fuel (h + 1) y a')) +
            bonus (Fintype.card S) (Fintype.card A) H K (countSA hist x a) δ))
      else 0

noncomputable def qAt {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ) (h : ℕ) (x : S) (a : A) : ℝ :=
  qFuel M H K δ hist prevQ (H - h) h x a

noncomputable def valueAt {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (Q : ℕ → S → A → ℝ) (h : ℕ) (x : S) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun a : A => Q h x a)

/-- Data available before the next episode and the preceding Q values. -/
structure RunState (S A : Type*) where
  history : List (S × A × S)
  prevQ : ℕ → S → A → ℝ

/-- After `n` episodes: the only data retained are prior triples and the
previous Q table. In episode one, all counts vanish and `prevQ=H`. -/
noncomputable def runPrefix {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) (ω : Outcomes S K H) : ℕ → RunState S A
  | 0 => ⟨[], fun _ _ _ => (H : ℝ)⟩
  | n + 1 =>
      let r := runPrefix M H K δ sel init ω n
      if hn : n < K then
        let k : Fin K := ⟨n, hn⟩
        let Q := qAt M H K δ r.history r.prevQ
        let π : Policy S A H := fun x h => sel (Q h.val x)
        let triples : List (S × A × S) :=
          List.ofFn (fun h : Fin H =>
            let x := stateAt init ω k h.val
            (x, π x h, ω k h))
        ⟨r.history ++ triples, Q⟩
      else r

/-- The Q table computed at the start of episode `k`. -/
noncomputable def episodeQ {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) (ω : Outcomes S K H) (k : Fin K) :
    ℕ → S → A → ℝ :=
  let r := runPrefix M H K δ sel init ω k.val
  qAt M H K δ r.history r.prevQ

/-- The entire greedy policy, including states off the observed trajectory. -/
noncomputable def episodePolicy {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) (ω : Outcomes S K H) (k : Fin K) :
    Policy S A H :=
  fun x h => sel (episodeQ M H K δ sel init ω k h.val x)

noncomputable def actionAt {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) (ω : Outcomes S K H) (k : Fin K)
    (h : Fin H) : A :=
  episodePolicy M H K δ sel init ω k (stateAt init ω k h.val) h

/-- Finite path probability; all randomness is in transition draws. -/
noncomputable def pathProb {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) (ω : Outcomes S K H) : ℝ :=
  ∏ k : Fin K, ∏ h : Fin H,
    M.P (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) (ω k h)

/-- The probability of an event, as a finite sum over complete paths. -/
noncomputable def probEvent {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) (E : Outcomes S K H → Prop) : ℝ := by
  classical
  exact ∑ ω : Outcomes S K H, if E ω then pathProb M H K δ sel init ω else 0

/-- Regret on a complete path, evaluated at each episode's actual initial state. -/
noncomputable def regret {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) (ω : Outcomes S K H) : ℝ :=
  ∑ k : Fin K,
    (optimalValue M H 0 (stateAt init ω k 0) -
      policyValue M H (episodePolicy M H K δ sel init ω k) 0 (stateAt init ω k 0))

end MinimaxRegretRL.Hoeffding


