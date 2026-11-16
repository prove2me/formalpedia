-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_NGame_BR
-- name    : QuasiStrictNE_Supplement_NGame_BR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:39:44.902185+00:00
-- url     : https://prove2.me/theorems/85bd01e8-f3d0-4d8d-8ea6-44ca881e3b41
-- title:
--   Pure best responses $BR_i(\nu_{-i})$ in an $n$-player game
-- statement:
--   For an $n$-player game $G$, a profile $\nu$ and a player $i$, the set of **pure best responses** of player $i$ is
--
--   $$
--   BR_i(\nu_{-i}) = \{a : P_{i,a}(\nu_{-i}) \ge P_{i,b}(\nu_{-i}) \text{ for every action } b \text{ of player } i\}.
--   $$
--
--   It generalizes $BR_1$, $BR_2$ of Definition 1 to $n$ players.
--
--   **Formalization Note** It is a `Finset` of 0-based actions, defined in the same way as the base `BR1`, `BR2`.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 1, p.4; proof of Theorem 2, pp.19–20 ($BR_i(\nu_{-i})$)

import Mathlib
import Definitions.Def_QuasiStrictNE_Supplement_NGame_payoff

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **Pure best responses of player `i` in an `n`-player game** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 2,
pp.19–20: `BRᵢ(ν₋ᵢ)`; the `n`-player form of `BR1`, `BR2` of Definition 1, p.4).

`BR G ν i` is the set of actions `a` of player `i` whose expected payoff `P_{i,a}(ν_{−i})` is maximal
among all actions of player `i`.

**Formalization Note** Same shape as the base `QuasiStrictNE.BR1`/`BR2`: a `Finset` of 0-based actions
defined by `∀ b, P_{i,b} ≤ P_{i,a}`. -/
noncomputable def NGame.BR {n : ℕ} (G : NGame n) (ν : (j : Fin n) → Fin (G.k j) → ℝ) (i : Fin n) :
    Finset (Fin (G.k i)) :=
  Finset.univ.filter (fun a => ∀ b, G.payoff ν i b ≤ G.payoff ν i a)

end QuasiStrictNE.Supplement


