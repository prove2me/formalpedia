-- Prove2me | Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_GreedyRun
-- name    : MostlyExplorationFree_GreedyBandit_Supplement_GreedyRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:46:39.571975+00:00
-- url     : https://prove2.me/theorems/727e380f-884e-4936-b7a0-13a40fdac05c
-- title:
--   Algorithms 1 and §3.5 — forced initialization, greedy run, and regret on events
-- statement:
--   Give each of $K$ arms exactly $m$ context-independent samples in the first $Km$ periods, using consecutive blocks of $m$ periods. Thereafter select an arm maximizing the estimated reward, breaking ties uniformly. If $S_{i,t}$ is the set of periods in which arm $i$ has been played, the estimate is
--   $$\hat\beta(S_{i,t})=\left(\sum_{s\in S_{i,t}}X_sX_s^\top\right)^{-1}\sum_{s\in S_{i,t}}Y_{i,s}X_s$$
--   when the Gram matrix is invertible, and the initial estimate otherwise. Setting $m=0$ gives the uninitialized greedy algorithm. For an arm sequence $\pi$ write
--   $$\rho_t=\max_j X_t^\top\beta_j-X_t^\top\beta_{\pi_t},\quad R_T(E)=\mathbb E\left[\mathbb I_E\sum_{t=1}^T\rho_t\right].$$
--   Logarithmic regret on $E$ means $\exists C\in\mathbb R\ \forall T\ge2,\ R_T(E)\le C\log T$.
--
--   These definitions fix the actual run and its regret, rather than taking estimates, Gram matrices, or a success event as unconstrained input data.
--
--   **Formalization Note** Gram matrices grow by positive semidefinite increments. Consequently retaining the initial value on a singular matrix is equivalent to updating only when invertible. The maximum is finite and nonempty for every permitted arm count. The regret integrand is measurable and bounded by $2x_{\max}b_{\max}$ per period under the model and Assumption 1, so the real integrals are ordinary expectations. The logarithmic coefficient can depend on the instance but never on the horizon.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, pp. 7, 11–12, 19 and 55, regret, Definition 3, Algorithm 1, initialization

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Environment

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory

/-- Select a maximum-score eligible arm of smallest random rank. A uniform random permutation
makes the choice uniform among ties. The fallback is used only on an empty eligible set. -/
noncomputable def selectArm {K : ℕ} [NeZero K] (eligible : Finset (Fin K))
    (score : Fin K → ℝ) (w : TieIndex K) : Fin K := by
  classical
  let rank := (Fintype.equivFin (Equiv.Perm (Fin K))).symm w
  let ties := eligible.filter (fun i => ∀ j ∈ eligible, score j ≤ score i)
  exact if h : (ties.image rank).Nonempty then
    rank.symm ((ties.image rank).min' h) else 0

def playedOf {K : ℕ} (a : ℕ → Fin K) (i : Fin K) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter (fun s => a s = i)

def gramOn {Ω : Type*} {d K : ℕ} (E : Environment Ω d K) (ω : Ω) (S : Finset ℕ) :
    Matrix (Fin d) (Fin d) ℝ := ∑ s ∈ S, Matrix.vecMulVec (E.X s ω) (E.X s ω)

/-- OLS with the specified initial estimate retained while the Gram matrix is singular.
On samples of arm i, the potential reward below is its observed reward. -/
noncomputable def olsOn {Ω : Type*} {d K : ℕ} (E : Environment Ω d K) (ω : Ω)
    (initial : Fin d → ℝ) (i : Fin K) (S : Finset ℕ) : Fin d → ℝ :=
  if (gramOn E ω S).det ≠ 0 then
    (gramOn E ω S)⁻¹ *ᵥ ∑ s ∈ S, (E.X s ω ⬝ᵥ E.β i + E.ε i s ω) • E.X s ω
  else initial

noncomputable def estOf {Ω : Type*} {d K : ℕ} (E : Environment Ω d K) (ω : Ω)
    (a : ℕ → Fin K) (i : Fin K) (t : ℕ) : Fin d → ℝ :=
  olsOn E ω (E.initial ω i) i (playedOf a i t)

/-- Block schedule: the first m times play arm 0, then m times arm 1, and so on. -/
def initialArm {K : ℕ} [NeZero K] (m t : ℕ) : Fin K :=
  ⟨((t - 1) / m) % K, Nat.mod_lt _ (NeZero.pos K)⟩

/-- Forced initial samples, followed by the literal greedy recursion. The t=0 slot is unused. -/
noncomputable def arm {Ω : Type*} {d K : ℕ} [NeZero K]
    (E : Environment Ω d K) (m : ℕ) (t : ℕ) (ω : Ω) : Fin K :=
  Nat.strongRec (fun t ih =>
    if t = 0 then 0 else if t ≤ K * m then initialArm m t else
      selectArm Finset.univ
        (fun i => E.X t ω ⬝ᵥ estOf E ω
          (fun s => if hs : s < t then ih s hs else 0) i (t - 1)) (E.W t ω)) t

noncomputable def gram {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (i : Fin K) (t : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  gramOn E ω (playedOf (fun s => arm E m s ω) i t)

noncomputable def est {Ω : Type*} {d K : ℕ} [NeZero K] (E : Environment Ω d K)
    (m : ℕ) (i : Fin K) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  estOf E ω (fun s => arm E m s ω) i t

/-- Finite maximum; K is nonzero, so this is never an empty supremum. -/
noncomputable def bestReward {Ω : Type*} {d K : ℕ} [NeZero K]
    (E : Environment Ω d K) (t : ℕ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => E.X t ω ⬝ᵥ E.β i)

noncomputable def pseudoRegret {Ω : Type*} {d K : ℕ} [NeZero K]
    (E : Environment Ω d K) (a : ℕ → Ω → Fin K) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (bestReward E t ω - E.X t ω ⬝ᵥ E.β (a t ω))

noncomputable def regretOn {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} [NeZero K]
    (P : Measure Ω) (E : Environment Ω d K) (a : ℕ → Ω → Fin K)
    (A : Set Ω) (T : ℕ) : ℝ := ∫ ω, A.indicator (pseudoRegret E a T) ω ∂P

/-- One coefficient for the whole infinite sequence of horizons. -/
def LogarithmicOn {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} [NeZero K]
    (P : Measure Ω) (E : Environment Ω d K) (a : ℕ → Ω → Fin K) (A : Set Ω) : Prop :=
  ∃ C : ℝ, ∀ T : ℕ, 2 ≤ T → regretOn P E a A T ≤ C * Real.log T

end MostlyExplorationFree.GreedyBandit.Supplement


