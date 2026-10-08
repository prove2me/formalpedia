-- Prove2me | Definitions.Def_MinimaxRegretRL_Bernstein_Process
-- name    : MinimaxRegretRL_Bernstein_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:24:54.162985+00:00
-- url     : https://prove2.me/theorems/f67be5f1-1a07-4bd9-ac05-dab905f26424
-- title:
--   Algorithms 1, 2, and 4: the UCBVI-BF process and regret
-- statement:
--   At the start of episode $k$, the learner counts past transitions $(x,a,y)$ across all steps, forms the empirical row $\widehat P_k(\cdot\mid x,a)$ when $N_k(x,a)>0$, and counts prior visits to each state at each time. It then computes $Q_{k,h}$ backward with terminal value zero. An unseen state-action pair receives $Q_{k,h}=H$; otherwise $Q_{k,h}$ is the minimum of the preceding episode's estimate, $H$, and reward plus empirical next value plus Algorithm 4's Bernstein–Freedman bonus. A policy greedily selects an action maximizing $Q_{k,h}$ at every state.
--
--   The bonus uses $L_{\rm alg}=\ln(5SAT/\delta)$ and the empirical variance of the same episode's next value. Its third term includes $\min(100^2H^3S^2AL_{\rm alg}^2/N'_{k,h+1}(y),H^2)$. The outcome law is the product of the true transition probabilities along the resulting history. Regret is the sum of $V_1^*(x_{k,1})-V_1^{\pi_k}(x_{k,1})$.
--
--   These definitions make the algorithm, its law, and its regret concrete for the probability bounds.
--
--   **Formalization Note** At $N'_{k,h+1}(y)=0$, the quotient represents $+\infty$ and the minimum is $H^2$. At episode one the previous Q-table is $H$. The environment's initial-state rule reads completed episodes only; a maximizing selection rule is supplied by the theorem.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), pp. 2–5, §2, Algorithms 1, 2, and 4; p. 14, N-prime counts

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_MDP
import Definitions.Def_MinimaxRegretRL_Hoeffding_Process

open scoped Classical

namespace MinimaxRegretRL.Bernstein

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable {H K : ℕ}

/-- The environment chooses the next episode's initial state from completed episodes only. -/
abbrev InitialRule (S : Type*) (H : ℕ) := List (Fin H → S) → S

/-- The state at time `h`, for `0 ≤ h ≤ H`, in episode `k`. -/
def stateAt (init : InitialRule S H) (ω : MinimaxRegretRL.Hoeffding.Outcomes S K H) (k : Fin K)
    (h : Fin (H + 1)) : S :=
  if h0 : h.val = 0 then init ((List.ofFn ω).take k.val)
  else ω k ⟨h.val - 1, by omega⟩

/-- Data available at the start of an episode, including the previous Q-values. -/
structure ModelState (S A : Type*) (H : ℕ) where
  triples : S → A → S → ℕ
  visits : Fin (H + 1) → S → ℕ
  previousQ : Fin H → S → A → ℝ

def initialModel (S A : Type*) (H : ℕ) : ModelState S A H where
  triples := fun _ _ _ => 0
  visits := fun _ _ => 0
  previousQ := fun _ _ _ => (H : ℝ)

def countSA (st : ModelState S A H) (x : S) (a : A) : ℕ :=
  ∑ y : S, st.triples x a y

/-- The empirical kernel is used only when its row count is positive. -/
noncomputable def empiricalP (st : ModelState S A H) (x : S) (a : A) (y : S) : ℝ :=
  (st.triples x a y : ℝ) / (countSA st x a : ℝ)

noncomputable def empiricalExp (st : ModelState S A H) (x : S) (a : A) (f : S → ℝ) : ℝ :=
  finiteExp (empiricalP st x a) f

noncomputable def empiricalVar (st : ModelState S A H) (x : S) (a : A) (f : S → ℝ) : ℝ :=
  finiteVar (empiricalP st x a) f

/-- The logarithm printed in Algorithm 4, distinct from Theorem 2's logarithm. -/
noncomputable def algorithmLog (δ : ℝ) (S A K H : ℕ) : ℝ :=
  Real.log (5 * (S : ℝ) * A * (K * H) / δ)

/-- Algorithm 4's extra summand. A zero time-specific count means an infinite quotient
in the paper, so the minimum is H². -/
noncomputable def extraCap (st : ModelState S A H) (L : ℝ)
    (h : Fin H) (y : S) : ℝ :=
  let n := st.visits (Fin.succ h) y
  if n = 0 then (H : ℝ) ^ 2
  else min ((100 : ℝ) ^ 2 * (H : ℝ) ^ 3 * (Fintype.card S : ℝ) ^ 2 *
      (Fintype.card A : ℝ) * L ^ 2 / (n : ℝ)) ((H : ℝ) ^ 2)

/-- The Algorithm 4 Bernstein–Freedman bonus, evaluated only at positive counts. -/
noncomputable def bonus (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (h : Fin H) (x : S) (a : A) (nextV : S → ℝ) : ℝ :=
  let L := algorithmLog δ (Fintype.card S) (Fintype.card A) K H
  let n := (countSA st x a : ℝ)
  Real.sqrt (8 * L * empiricalVar st x a nextV / n) +
    14 * H * L / (3 * n) +
    Real.sqrt (8 * empiricalExp st x a (extraCap st L h) / n)

/-- Backward induction within one episode, using the preceding episode's Q-values. -/
noncomputable def qAt (M : MinimaxRegretRL.Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) :
    ℕ → S → A → ℝ
  | h, x, a =>
    if hh : h < H then
      if countSA st x a = 0 then (H : ℝ)
      else
        let nextV : S → ℝ := fun y =>
          if hn : h + 1 < H then ⨆ a' : A, qAt M st δ K (h + 1) y a'
          else 0
        min (min (st.previousQ ⟨h, hh⟩ x a) (H : ℝ))
          (M.R x a + empiricalExp st x a nextV + bonus st δ K ⟨h, hh⟩ x a nextV)
    else 0
  termination_by h => H - h
  decreasing_by all_goals omega

/-- The Q-values computed for an episode from its starting data. -/
noncomputable def episodeQ (M : MinimaxRegretRL.Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) :
    Fin H → S → A → ℝ :=
  fun h x a => qAt M st δ K h.val x a

/-- A greedy policy under any tie-breaking rule attaining a maximum. -/
noncomputable def greedyPolicy (q : Fin H → S → A → ℝ) (sel : (A → ℝ) → A) :
    MinimaxRegretRL.Hoeffding.Policy S A H :=
  fun x h => sel (q h x)

/-- Update the empirical data using exactly one completed episode. -/
noncomputable def advance (init : InitialRule S H) (ω : MinimaxRegretRL.Hoeffding.Outcomes S K H)
    (k : Fin K) (st : ModelState S A H) (q : Fin H → S → A → ℝ)
    (sel : (A → ℝ) → A) : ModelState S A H :=
  let π := greedyPolicy q sel
  { triples := fun x a y => st.triples x a y +
      ∑ h : Fin H, if stateAt init ω k (Fin.castSucc h) = x ∧
        π (stateAt init ω k (Fin.castSucc h)) h = a ∧ ω k h = y then 1 else 0
    visits := fun h x => st.visits h x + if stateAt init ω k h = x then 1 else 0
    previousQ := q }

/-- Start-of-episode data; the `k`th step uses only outcomes before episode `k`. -/
noncomputable def runState (M : MinimaxRegretRL.Hoeffding.MDP S A) (δ : ℝ) (K H : ℕ)
    (sel : (A → ℝ) → A) (init : InitialRule S H) (ω : MinimaxRegretRL.Hoeffding.Outcomes S K H) :
    ℕ → ModelState S A H
  | 0 => initialModel S A H
  | k + 1 =>
      let st := runState M δ K H sel init ω k
      if hk : k < K then
        advance init ω ⟨k, hk⟩ st (episodeQ M st δ K) sel
      else st

/-- The policy chosen at episode `k`, including actions at states not visited. -/
noncomputable def policyAt (M : MinimaxRegretRL.Hoeffding.MDP S A) (δ : ℝ) (K H : ℕ)
    (sel : (A → ℝ) → A) (init : InitialRule S H) (ω : MinimaxRegretRL.Hoeffding.Outcomes S K H)
    (k : Fin K) : MinimaxRegretRL.Hoeffding.Policy S A H :=
  greedyPolicy (episodeQ M (runState M δ K H sel init ω k.val) δ K) sel

/-- The joint law of all observed next states, constructed from the stationary kernel. -/
noncomputable def outcomeProb (M : MinimaxRegretRL.Hoeffding.MDP S A) (δ : ℝ) (K H : ℕ)
    (sel : (A → ℝ) → A) (init : InitialRule S H) (ω : MinimaxRegretRL.Hoeffding.Outcomes S K H) : ℝ :=
  ∏ k : Fin K, ∏ h : Fin H,
    M.P (stateAt init ω k (Fin.castSucc h))
      (policyAt M δ K H sel init ω k (stateAt init ω k (Fin.castSucc h)) h) (ω k h)

noncomputable def probEvent (M : MinimaxRegretRL.Hoeffding.MDP S A) (δ : ℝ) (K H : ℕ)
    (sel : (A → ℝ) → A) (init : InitialRule S H)
    (E : MinimaxRegretRL.Hoeffding.Outcomes S K H → Prop) : ℝ :=
  ∑ ω : MinimaxRegretRL.Hoeffding.Outcomes S K H, if E ω then outcomeProb M δ K H sel init ω else 0

/-- Theorem 2's regret: optimal value minus the chosen policy's value at each initial state. -/
noncomputable def regret (M : MinimaxRegretRL.Hoeffding.MDP S A) (δ : ℝ) (K H : ℕ)
    (sel : (A → ℝ) → A) (init : InitialRule S H) (ω : MinimaxRegretRL.Hoeffding.Outcomes S K H) : ℝ :=
  ∑ k : Fin K, (optimalValue M H 0 (stateAt init ω k ⟨0, by omega⟩) -
    valueAt M (policyAt M δ K H sel init ω k) 0 (stateAt init ω k ⟨0, by omega⟩))

end MinimaxRegretRL.Bernstein


