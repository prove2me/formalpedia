-- Prove2me | Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_OLSBandit
-- name    : MostlyExplorationFree_GreedyBandit_Supplement_OLSBandit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:47:35.486803+00:00
-- url     : https://prove2.me/theorems/6a913bd8-5ef0-4137-84b9-cf810a71f628
-- title:
--   Appendix E — OLS Bandit with geometric forced-sample schedule
-- statement:
--   For an integer $q\ge1$, paper arm $i+1$ has forced-sample times
--   $$\mathcal T_{i+1}=\{(2^n-1)Kq+j:n\ge0,\ qi+1\le j\le q(i+1)\}.$$
--   At a forced time the designated arm is played. Otherwise, OLS estimates from forced samples retain the arms whose predicted reward is within $h/2$ of the highest forced-sample prediction. The arm with the largest all-sample OLS prediction among those retained is played. Both estimator families start at zero. Define $R_{\rm OB}(n)$ as the cumulative expected regret of this run from empty data, and specify a coefficient by
--   $$R_{\rm OB}(n)\le C_{\rm OB}\log n\qquad(n\ge2).$$
--
--   This makes the fallback algorithm in Theorem 3 concrete and ties its coefficient to its own regret, without importing constants from another paper.
--
--   **Formalization Note** The exponent is $2^n$. OLS uses zero while its matrix is singular. At nonforced times a uniform permutation resolves ties; the forced sets are disjoint. The bound on the coefficient excludes $n=1$, where $\log1=0$. Theorem 3 uses the explicitly stronger UniformOLSCoefficient: the same $C_{\rm OB}$ must bound every fresh run on the shifted observation sequences, for every deterministic absolute start $r\ge0$ and horizon $n\ge2$. Since the source permits time-dependent noise laws, an unshifted-run bound alone does not control a restart. DISPROOF.md supplies a counterexample to that weaker reading; the uniform premise is the one required by p. 24's fresh-run argument.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, pp. 48–49, equation (26), Algorithm 4; p. 24, definition of the OLS regret coefficient

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_GreedyRun

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory

/-- Equation (26), with paper arm i+1 represented by i. -/
def IsForced {K : ℕ} (q : ℕ) (i : Fin K) (t : ℕ) : Prop :=
  ∃ n j : ℕ, q * i.val + 1 ≤ j ∧ j ≤ q * (i.val + 1) ∧
    t = (2 ^ n - 1) * K * q + j

noncomputable def forcedTimes {K : ℕ} (q : ℕ) (i : Fin K) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 t).filter (IsForced q i)

/-- Algorithm 4's two-stage decision: forced sampling, then screening on forced estimates,
then maximisation on all-sample estimates. Both estimator families start at zero. -/
noncomputable def olsChoice {Ω : Type*} {d K : ℕ} [NeZero K]
    (E : Environment Ω d K) (q : ℕ) (h : ℝ) (a : ℕ → Fin K) (t : ℕ) (ω : Ω) : Fin K := by
  classical
  let forced : Finset (Fin K) := Finset.univ.filter (fun i => IsForced q i t)
  let forcedScores := fun i => E.X t ω ⬝ᵥ olsOn E ω 0 i (forcedTimes q i (t - 1))
  let maxForced := Finset.univ.sup' Finset.univ_nonempty forcedScores
  let candidates := Finset.univ.filter (fun i => maxForced - h / 2 ≤ forcedScores i)
  exact if hf : forced.Nonempty then forced.min' hf else
    selectArm candidates
      (fun i => E.X t ω ⬝ᵥ olsOn E ω 0 i (playedOf a i (t - 1))) (E.W t ω)

noncomputable def olsArm {Ω : Type*} {d K : ℕ} [NeZero K]
    (E : Environment Ω d K) (q : ℕ) (h : ℝ) (t : ℕ) (ω : Ω) : Fin K :=
  Nat.strongRec (fun t ih => if t = 0 then 0 else
    olsChoice E q h (fun s => if hs : s < t then ih s hs else 0) t ω) t

/-- The property specifying the coefficient C_OB on a fresh Algorithm 4 run. -/
def OLSCoefficient {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} [NeZero K]
    (P : Measure Ω) (E : Environment Ω d K) (q : ℕ) (h COB : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → regretOn P E (olsArm E q h) Set.univ n ≤ COB * Real.log n

/-- The same fresh-run coefficient at every absolute start time. The noises in the model
are independent but need not be identically distributed. A coefficient for start time zero
alone does not control the restarted run of Algorithm 3. -/
def UniformOLSCoefficient {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} [NeZero K]
    (P : Measure Ω) (E : Environment Ω d K) (q : ℕ) (h COB : ℝ) : Prop :=
  ∀ r : ℕ, OLSCoefficient P (E.shift r) q h COB

end MostlyExplorationFree.GreedyBandit.Supplement


