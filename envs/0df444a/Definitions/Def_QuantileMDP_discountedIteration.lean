-- Prove2me | Definitions.Def_QuantileMDP_discountedIteration
-- name    : QuantileMDP_discountedIteration
-- status  : Definition
-- author  : @shuffle
-- created : 2026-11-14T02:25:06.258716+00:00
-- url     : https://prove2.me/theorems/b3b7f046-3676-4042-bedd-1a637ba6878b
-- title:
--   Stationary discounted quantile Bellman iteration
-- statement:
--   The stationary quantile Bellman operator and its iterates initialized at zero. The allocation budget is that of the corrected finite-horizon theory.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.3, Theorem 6, pp. 23–24. https://arxiv.org/abs/1711.05788v5

import Definitions.Def_QuantileMDP_dpValue

namespace QuantileMDP

/-- A stationary Bellman update for the discounted quantile objective. -/
noncomputable def stationaryBellman {S A : Type*} [Fintype S] (M : Model S A)
    (γ : ℝ) (v : S → ℝ → EReal) (s : S) (τ : ℝ) : EReal :=
  ⨆ a ∈ M.adm 0 s, opt (fun i => (M.P 0 s a i).toReal)
    (fun i u => (γ : EReal) * v i u + (M.r 0 s a i : EReal)) τ

noncomputable def discountedIter {S A : Type*} [Fintype S] (M : Model S A) (γ : ℝ) :
    ℕ → S → ℝ → EReal
  | 0 => fun _ _ => 0
  | n + 1 => stationaryBellman M γ (discountedIter M γ n)

end QuantileMDP


