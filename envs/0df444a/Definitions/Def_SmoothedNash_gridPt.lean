-- Prove2me | Definitions.Def_SmoothedNash_gridPt
-- name    : SmoothedNash_gridPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:24.996944+00:00
-- url     : https://prove2.me/theorems/fffe0321-e15a-4763-a795-b1170ee6e2af
-- title:
--   Grid point $k/q_t$ of a numerator vector
-- statement:
--   For a support profile $A$, a level $t$ and a numerator vector $k$, the corresponding profile is
--   $$
--   x_i(a) = \frac{k_i(a)}{q_t}, \qquad i \in [m],\ a \in [n].
--   $$
--   For $k$ in the level-$t$ grid this is a point of $N_t(A) \subseteq K_A$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_q

namespace SmoothedNash

/-- The mixed profile `x_i(a) = k_i(a)/q_t` of a level-`t` numerator vector `k`
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14). -/
noncomputable def gridPt {m n : ℕ} (A : SupportProfile m n) (t : ℕ) (k : Fin m → Fin n → ℕ) :
    Fin m → Fin n → ℝ :=
  fun i a => (k i a : ℝ) / (q A t : ℝ)

end SmoothedNash


