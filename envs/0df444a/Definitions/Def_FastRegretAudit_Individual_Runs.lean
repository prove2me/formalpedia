-- Prove2me | Definitions.Def_FastRegretAudit_Individual_Runs
-- name    : FastRegretAudit_Individual_Runs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:59.979612+00:00
-- url     : https://prove2.me/theorems/39fb0997-2c4c-44b1-9b8a-49ea812eece9
-- title:
--   Finite prefixes of exact OFTRL updates and auxiliary leaders
-- statement:
--   Let $\eta>0$, let $\Delta$ be the simplex, and let $u^t,M^t\in\mathbb R^d$ be utility and predictor vectors. An OFTRL prefix through $H$ consists of feasible vectors attaining
--
--   $$w^0\in\arg\min_{v\in\Delta}\mathcal R(v),\qquad w^t\in\arg\max_{v\in\Delta}\left\langle v,\sum_{k=1}^{t-1}u^k+M^t\right\rangle-\frac{\mathcal R(v)}\eta\quad(1\le t\le H).$$
--
--   A leader prefix consists of feasible global maximizers
--
--   $$g^t\in\arg\max_{v\in\Delta}\left\langle v,\sum_{k=1}^{t}u^k\right\rangle-\frac{\mathcal R(v)}\eta\quad(0\le t\le H).$$
--
--   Each argmin or argmax is an inequality against every feasible comparator; no default choice or additional regularity is used. These are the finite restrictions of the compatible published update definitions, needed to avoid demanding unused future optimizers.
--
--   For game play, utility feedback is the published independent mixed-play expectation, and $M_i^t=u_i^{t-1}$. The initial-feedback reading is $u_i^0=u_i(w^0)$. Every player may use its own regularizer. Auxiliary leaders occur only in the two results that mention them, and are not part of the game-run relation.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, main p. 2, §2; main p. 5, §3.1.2; Appendix C, supplementary p. 3, PDF p. 12, leader display

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace FastRegretAudit.Individual

/-- The finite-horizon restriction of the published `IsOFTRL` relation:
initial minimization and global maximizing inequalities through H only. -/
def IsOFTRLThrough {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ)
    (M u w : ℕ → Fin d → ℝ) (H : ℕ) : Prop :=
  (w 0 ∈ stdSimplex ℝ (Fin d) ∧ ∀ v ∈ stdSimplex ℝ (Fin d), 𝓡 (w 0) ≤ 𝓡 v) ∧
    ∀ t, 1 ≤ t → t ≤ H → w t ∈ stdSimplex ℝ (Fin d) ∧
      ∀ v ∈ stdSimplex ℝ (Fin d),
        v ⬝ᵥ ((∑ k ∈ Finset.Ico 1 t, u k) + M t) - 𝓡 v / η ≤
          w t ⬝ᵥ ((∑ k ∈ Finset.Ico 1 t, u k) + M t) - 𝓡 (w t) / η

/-- The finite-horizon restriction of the published `IsLeader` relation,
including the zero-round minimizer. No leader is required in the goal theorem. -/
def IsLeaderThrough {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ)
    (u g : ℕ → Fin d → ℝ) (H : ℕ) : Prop :=
  ∀ t, t ≤ H → g t ∈ stdSimplex ℝ (Fin d) ∧
    ∀ v ∈ stdSimplex ℝ (Fin d),
      v ⬝ᵥ (∑ k ∈ Finset.Icc 1 t, u k) - 𝓡 v / η ≤
        g t ⬝ᵥ (∑ k ∈ Finset.Icc 1 t, u k) - 𝓡 (g t) / η

/-- Independent game play with one-step feedback, including the explicit
initialization reading u⁰ = utilVec u (w 0). Every player may use its own regularizer. -/
def IsGameOFTRLThrough {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ) (η : ℝ)
    (w : ℕ → Fin n → Fin d → ℝ) (H : ℕ) : Prop :=
  ∀ i, IsOFTRLThrough (𝓡 i) η
    (fun t => RegLearnGames.TotalRegret.utilVec u (w (t - 1)) i)
    (fun t => RegLearnGames.TotalRegret.utilVec u (w t) i) (fun t => w t i) H

end FastRegretAudit.Individual


