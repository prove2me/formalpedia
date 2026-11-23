-- Prove2me | Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_GreedyFirst
-- name    : MostlyExplorationFree_GreedyBandit_Supplement_GreedyFirst
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:48:25.271808+00:00
-- url     : https://prove2.me/theorems/ab77e839-423d-475c-834f-cc2b8e82deb5
-- title:
--   Algorithm 3 — first failed covariance test and a fresh OLS restart
-- statement:
--   Greedy-First follows the greedy run until the first period $R>t_0$ whose completed data satisfy
--   $$\min_i\lambda_{\min}(\hat\Sigma(S_{i,R}))<\lambda_0 R/4.$$
--   That period is still greedy. From period $R+1$ it starts a fresh OLS Bandit with empty data and local clock 1, using the contexts, noises and tie variables at their actual later times. If no test fails, it remains greedy forever. Thus
--   $$\mathrm{NoSwitch}=\{\forall t>t_0,\ \forall i,\ \lambda_{\min}(\hat\Sigma(S_{i,t}))\ge\lambda_0 t/4\}.$$
--
--   The definition specifies the transition required by both Greedy-First theorems. Theorems 3 and 4 use respectively zero and $m$ forced initial samples.
--
--   **Formalization Note** Initial estimates have the arbitrary independent law from the environment. The test is strict, is applied after the current observation, and is made strictly after $t_0$. There is no future-information choice: the stored first failure determines a greedy prefix and then a fresh fallback run. The sentinel $R=0$ means no switch. The local restart is the reading used by the regret bound on p. 24.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 22, Algorithm 3; pp. 23–25, switch timing and fallback regret

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_OLSBandit

namespace MostlyExplorationFree.GreedyBandit.Supplement

open MeasureTheory

/-- Algorithm 3 tests strictly after t0 and after recording the current greedy round. -/
def SwitchAt {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (lam0 : ℝ) (t0 t : ℕ) (ω : Ω) : Prop :=
  t0 < t ∧ ∃ i, lambdaMin (gram E m i t ω) < lam0 * t / 4

/-- First failed test, or zero if there is no failed test at any finite time. -/
noncomputable def switchTime {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (lam0 : ℝ) (t0 : ℕ) (ω : Ω) : ℕ := by
  classical
  exact if h : ∃ t, SwitchAt E m lam0 t0 t ω then Nat.find h else 0

def NoSwitch {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (lam0 : ℝ) (t0 : ℕ) : Set Ω :=
  {ω | ∀ t, t0 < t → ∀ i, lam0 * t / 4 ≤ lambdaMin (gram E m i t ω)}

/-- R is still a greedy round. At R+1, Algorithm 4 starts with local clock 1 and empty data.
The shifted process uses the very same context, noise and tie variables at absolute time R+t. -/
noncomputable def firstArm {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (lam0 : ℝ) (t0 q : ℕ) (h : ℝ) (t : ℕ) (ω : Ω) : Fin K :=
  let r := switchTime E m lam0 t0 ω
  if r = 0 ∨ t ≤ r then arm E m t ω else olsArm (E.shift r) q h (t - r) ω

end MostlyExplorationFree.GreedyBandit.Supplement


