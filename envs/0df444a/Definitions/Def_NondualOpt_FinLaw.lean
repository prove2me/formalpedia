-- Prove2me | Definitions.Def_NondualOpt_FinLaw
-- name    : NondualOpt_FinLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:40.876252+00:00
-- url     : https://prove2.me/theorems/0d3961d0-8c09-4919-a2fa-ceb75d24393f
-- title:
--   A finitely supported probability law on a set
-- statement:
--   A **finitely supported law** on a set $S\subseteq\alpha$ is a weight function $w:\alpha\to[0,\infty)$ with finite support contained in $S$ and $\sum_a w(a)=1$.
--
--   The paper notes that finitely supported adversarial laws suffice for the minimax interchanges (footnote 6). The randomized game and the adversaries of this mission use such laws, so all expectations are finite sums.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, footnote 6, p.9

import Mathlib

namespace NondualOpt

/-- A finitely supported probability law on a set `S ⊆ α`: nonnegative weights `w` with finite
support contained in `S`, summing to `1`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, footnote 6, p.9 ("Finitely supported
adversarial laws suffice for the minimax interchanges").

**Formalization Note.** The laws `r_t`, `s_t` of Assumption 3 and Proposition 4 are read as
finitely supported, so every expectation in the game is a finite sum. -/
structure FinLaw {α : Type*} (S : Set α) where
  /-- The weights. -/
  w : α →₀ ℝ
  nonneg : ∀ a, 0 ≤ w a
  supp : ∀ a ∈ w.support, a ∈ S
  sum_one : ∑ a ∈ w.support, w a = 1

end NondualOpt


