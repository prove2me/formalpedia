-- Prove2me | Definitions.Def_MinimaxRegretRL_Hoeffding_Analysis
-- name    : MinimaxRegretRL_Hoeffding_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:02:09.542354+00:00
-- url     : https://prove2.me/theorems/5e0066a9-ca3c-4a34-b61a-8dea8380c65b
-- title:
--   Appendix B — counts, confidence event and surrogate-regret terms
-- statement:
--   The analysis uses per-step state and state-action visit counts, the true and empirical next-state variances of the optimal value, the three confidence widths $c_1,c_2,c_3$, and the empirical-model confidence event $\mathcal E_{\widehat P}$. The event requires their concentration bounds simultaneously at every episode and step, for every state-action pair with a positive pooled count.
--
--   $$c_1(v,n)=2\sqrt{vL/n}+14HL/(3n),\quad c_2(p,n)=2\sqrt{p(1-p)L/n}+2L/(3n),\quad c_3(n)=2\sqrt{SL/n},\qquad L=\ln(5SAT/\delta).$$
--
--   The file also defines the surrogate gap $\widetilde\Delta_{k,h}=V_{k,h}-V_h^{\pi_k}$ and its martingale differences, typical-state restriction, and correction terms used in the weighted recursion of Lemma 3.
--
--   **Formalization Note** The typical-state threshold is $4H^2L$, as required by the proof's equations (34)–(36); B.1 prints $2H^2L$. The event is imposed only where $N_k(x,a)>0$, since the paper's confidence set has domain $n>0$.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), pp. 14–16, Appendix B, and pp. 19–21, B.5 and proof of Lemma 3

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_Process

namespace MinimaxRegretRL.Hoeffding

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A]

/-- Data available at the beginning of episode `k`. -/
noncomputable def priorHistory (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) : List (S × A × S) :=
  (runPrefix M H K δ sel init ω k.val).history

/-- `N'_{k,h}(x,a)`: visits at a specific step in earlier episodes. -/
noncomputable def stepCount (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (x : S) (a : A) : ℕ :=
  ∑ i : Fin k.val,
    let j : Fin K := ⟨i.val, lt_trans i.isLt k.isLt⟩
    if stateAt init ω j h.val = x ∧ actionAt M H K δ sel init ω j h = a then 1 else 0

/-- `N'_{k,h}(x)`: state visits at a specific step, including the terminal
states after step `H-1`. -/
noncomputable def stepStateCount (H K : ℕ) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin (H + 1)) (x : S) : ℕ :=
  ∑ i : Fin k.val,
    let j : Fin K := ⟨i.val, lt_trans i.isLt k.isLt⟩
    if stateAt init ω j h.val = x then 1 else 0

noncomputable def nAt (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (x : S) (a : A) : ℕ :=
  countSA (priorHistory M H K δ sel init ω k) x a

noncomputable def nyAt (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (x : S) (a : A) (y : S) : ℕ :=
  countSAS (priorHistory M H K δ sel init ω k) x a y

noncomputable def phatAt (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (x : S) (a : A) (y : S) : ℝ :=
  empirical (priorHistory M H K δ sel init ω k) x a y

noncomputable def estimatedValue (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : ℕ) (x : S) : ℝ :=
  valueAt (episodeQ M H K δ sel init ω k) h x

/-- Variance of `V*_h(Y)` under the true transition row. -/
noncomputable def trueVariance (M : MDP S A) (H h : ℕ) (x : S) (a : A) : ℝ :=
  (∑ y : S, M.P x a y * (optimalValue M H h y) ^ 2) -
    (∑ y : S, M.P x a y * optimalValue M H h y) ^ 2

/-- Variance of `V*_h(Y)` under the empirical row. -/
noncomputable def empiricalVariance (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : ℕ) (x : S) (a : A) : ℝ :=
  (∑ y : S, phatAt M H K δ sel init ω k x a y * (optimalValue M H h y) ^ 2) -
    (∑ y : S, phatAt M H K δ sel init ω k x a y * optimalValue M H h y) ^ 2

/-- The `c₁` confidence width of B.4, defined on positive counts. -/
noncomputable def c1 (S A H K n : ℕ) (δ v : ℝ) : ℝ :=
  2 * Real.sqrt (v * algorithmLog S A H K δ / n) +
    14 * (H : ℝ) * algorithmLog S A H K δ / (3 * n)

noncomputable def c2 (S A H K n : ℕ) (δ p : ℝ) : ℝ :=
  2 * Real.sqrt (p * (1 - p) * algorithmLog S A H K δ / n) +
    2 * algorithmLog S A H K δ / (3 * n)

noncomputable def c3 (S A H K n : ℕ) (δ : ℝ) : ℝ :=
  2 * Real.sqrt ((S : ℝ) * algorithmLog S A H K δ / n)

/-- The empirical-model component `E_P̂` of the event on p. 16. Every
confidence clause is restricted to observed state-action pairs (`N_k>0`). -/
noncomputable def confidenceEvent (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) : Prop :=
  ∀ (k : Fin K) (h : Fin H) (x : S) (a : A),
    0 < nAt M H K δ sel init ω k x a →
      (|(∑ y : S, (phatAt M H K δ sel init ω k x a y - M.P x a y) *
        optimalValue M H h.val y)| ≤
        min (c1 (Fintype.card S) (Fintype.card A) H K
          (nAt M H K δ sel init ω k x a) δ (trueVariance M H h.val x a))
          (c1 (Fintype.card S) (Fintype.card A) H K
            (nAt M H K δ sel init ω k x a) δ
            (empiricalVariance M H K δ sel init ω k h.val x a))) ∧
      (∀ y : S, |phatAt M H K δ sel init ω k x a y - M.P x a y| ≤
        c2 (Fintype.card S) (Fintype.card A) H K
          (nAt M H K δ sel init ω k x a) δ (M.P x a y)) ∧
      (∑ y : S, |phatAt M H K δ sel init ω k x a y - M.P x a y|) ≤
        c3 (Fintype.card S) (Fintype.card A) H K
          (nAt M H K δ sel init ω k x a) δ

/-- The estimate minus the value of the greedy policy. -/
noncomputable def surrogateGap (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : ℕ) (x : S) : ℝ :=
  estimatedValue M H K δ sel init ω k h x -
    policyValue M H (episodePolicy M H K δ sel init ω k) h x

noncomputable def pathP (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) : ℝ :=
  M.P (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) y

noncomputable def pathN (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℕ :=
  nAt M H K δ sel init ω k (stateAt init ω k h.val)
    (actionAt M H K δ sel init ω k h)

/-- The martingale difference `ε_{k,h}` of B.3. -/
noncomputable def epsilon (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  (∑ y : S, pathP M H K δ sel init ω k h y *
    surrogateGap M H K δ sel init ω k (h.val + 1) y) -
      surrogateGap M H K δ sel init ω k (h.val + 1) (ω k h)

/-- Corrected typical-state threshold `4H²L`, as required by (34)–(36). -/
noncomputable def typicalGap (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) : ℝ :=
  let p := pathP M H K δ sel init ω k h y
  let n := pathN M H K δ sel init ω k h
  if (4 * (H : ℝ) ^ 2 * algorithmLog (Fintype.card S) (Fintype.card A) H K δ ≤
      (n : ℝ) * p) then
    Real.sqrt (1 / ((n : ℝ) * p)) *
      surrogateGap M H K δ sel init ω k (h.val + 1) y
  else 0

noncomputable def barEpsilon (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  (∑ y : S, pathP M H K δ sel init ω k h y *
    typicalGap M H K δ sel init ω k h y) -
      typicalGap M H K δ sel init ω k h (ω k h)

noncomputable def pathC1 (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  c1 (Fintype.card S) (Fintype.card A) H K (pathN M H K δ sel init ω k h) δ
    (trueVariance M H (h.val + 1) (stateAt init ω k h.val)
      (actionAt M H K δ sel init ω k h))

noncomputable def pathC4 (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  4 * (H : ℝ) ^ 2 * Fintype.card S * Fintype.card A *
    algorithmLog (Fintype.card S) (Fintype.card A) H K δ /
      pathN M H K δ sel init ω k h

noncomputable def pathBonus (M : MDP S A) (H K : ℕ) (δ : ℝ)
    (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  bonus (Fintype.card S) (Fintype.card A) H K (pathN M H K δ sel init ω k h) δ

end MinimaxRegretRL.Hoeffding


