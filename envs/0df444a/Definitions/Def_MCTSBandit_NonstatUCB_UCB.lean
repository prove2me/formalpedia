-- Prove2me | Definitions.Def_MCTSBandit_NonstatUCB_UCB
-- name    : MCTSBandit_NonstatUCB_UCB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:08.160386+00:00
-- url     : https://prove2.me/theorems/a8cd0a9c-6d0e-4ba0-8d0a-a0309b01a1e7
-- title:
--   Polynomial UCB rule and play thresholds
-- statement:
--   For arm $i$ after $s$ plays and at time $t$, the index is
--
--   $$U_{i,s,t}=\bar X_{i,s}+B_{t,s},\qquad B_{t,s}=\frac{\beta^{1/\xi}t^{\alpha/\xi}}{s^{1-\eta}}.$$
--
--   At round $t$, the run chooses an arm with maximal index using play counts through $t-1$. An unplayed arm has infinite priority. The file also defines the arm threshold $A_i(t)$ and the common threshold $A(t)$ by the ceiling formulas in (18) and (20). These definitions fix the algorithm and thresholds shared by Theorem 3 and its lemmas.
--
--   **Formalization Note** The real-valued bonus is used only for positive play counts; the unplayed-arm clause represents the paper's $+\infty$ convention.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, p. 16, §5.1, (14)–(16); p. 17, (18); p. 18, (20)

import Definitions.Def_MCTSBandit_NonstatUCB_Model

namespace MCTSBandit.NonstatUCB

universe u

/-- Polynomial exploration bonus (16); only positive play counts are used by the rule. -/
noncomputable def bonus (β ξ α η : ℝ) (t s : ℕ) : ℝ :=
  β ^ (1 / ξ) * (t : ℝ) ^ (α / ξ) / (s : ℝ) ^ (1 - η)

/-- Upper confidence index (14). -/
noncomputable def ucb {Ω : Type u} {K : ℕ} (X : Fin K → ℕ → Ω → ℝ)
    (β ξ α η : ℝ) (i : Fin K) (s t : ℕ) (ω : Ω) : ℝ :=
  empMean X i s ω + bonus β ξ α η t s

/-- Rule (15): an unplayed arm has infinite priority; otherwise maximize the real index. -/
def IsUCBRun {Ω : Type u} {K : ℕ} (X : Fin K → ℕ → Ω → ℝ)
    (β ξ α η : ℝ) (I : ℕ → Ω → Fin K) : Prop :=
  ∀ ω t, 1 ≤ t →
    ((∃ j : Fin K, pullCount I j (t - 1) ω = 0) →
      pullCount I (I t ω) (t - 1) ω = 0) ∧
    ((∀ j : Fin K, pullCount I j (t - 1) ω ≠ 0) →
      ∀ j : Fin K,
        ucb X β ξ α η j (pullCount I j (t - 1) ω) (t - 1) ω
          ≤ ucb X β ξ α η (I t ω) (pullCount I (I t ω) (t - 1) ω) (t - 1) ω)

/-- Arm-specific threshold in (18). -/
noncomputable def Aidx (Δi β ξ α η : ℝ) (t : ℕ) : ℕ :=
  ⌈((2 / Δi) * β ^ (1 / ξ) * (t : ℝ) ^ (α / ξ)) ^ (1 / (1 - η))⌉₊

/-- Common threshold in (20), with Δ standing for the minimum gap. -/
noncomputable def Afun (Δ β ξ α η : ℝ) (t : ℕ) : ℕ :=
  ⌈((2 / Δ) * β ^ (1 / ξ)) ^ (1 / (1 - η)) *
    (t : ℝ) ^ (α / (ξ * (1 - η)))⌉₊

end MCTSBandit.NonstatUCB


