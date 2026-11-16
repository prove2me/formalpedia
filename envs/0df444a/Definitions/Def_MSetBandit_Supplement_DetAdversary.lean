-- Prove2me | Definitions.Def_MSetBandit_Supplement_DetAdversary
-- name    : MSetBandit_Supplement_DetAdversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:46:09.023261+00:00
-- url     : https://prove2.me/theorems/4995ffc7-ef3e-4cac-a5a7-5ffbb9ce153c
-- title:
--   Deterministic adaptive non-anticipating adversary $\ell_t=f_t(H_{t-1})$
-- statement:
--   A **deterministic adaptive non-anticipating adversary** on $\mathcal X_{d,m}$ is a sequence of deterministic maps $f_t$ from histories of length $t-1$ to loss vectors: at round $t$ it chooses
--   $$
--   \ell_t=f_t(H_{t-1})\in\mathbb R^d .
--   $$
--   It may depend on all past actions and feedback, but not on the learner's private randomness and not on the action $X_t$ of the current round.
--
--   This is the adversary model of Section 2 of the paper, to which the lower bounds are transferred from randomized adversaries.
--
--   **Formalization Note** Rounds are indexed from $0$; loss vectors are functions $\{0,\dots,d-1\}\to\mathbb R$.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.4 and Appendix E, p.41 ($\ell_t=f_t(H_{t-1},\Xi)$ with $\Xi$ fixed)

import Mathlib
import Definitions.Def_MSetBandit_Supplement_History

namespace MSetBandit.Supplement

/-- **Deterministic adaptive non-anticipating adversary.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.4, and
Appendix E, p.41: "the adversary's chosen loss vector as `ℓ_t = f_t(H_{t−1}, Ξ)`, where … `f_t`
[is a] deterministic function. Fixing `Ξ` therefore yields a deterministic adaptive
non-anticipating adversary, as required by our model."

A `DetAdversary d m` is, for each round `t`, a map `f t` from histories of length `t` to loss
vectors `ℓ_t ∈ ℝ^d`. It may depend on past actions and feedback, but neither on the learner's
private randomness nor on the current action.

**Formalization Note.** Rounds are 0-based; vectors of `ℝ^d` are functions `Fin d → ℝ`. -/
structure DetAdversary (d m : ℕ) where
  /-- the loss rule `f_t(H_{t−1})` -/
  f : (t : ℕ) → History d m t → Fin d → ℝ

end MSetBandit.Supplement


