-- Prove2me | Definitions.Def_MatroidOptGame_value
-- name    : MatroidOptGame_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:58:39.983138+00:00
-- url     : https://prove2.me/theorems/cab9eaef-ea49-463f-abb9-07699f39c7b0
-- title:
--   Value $V(M,w)$ of the game
-- statement:
--   The **value** of the matroid base minimization game on $(M, w)$ is
--   $$
--   V(M, w) = \min_{s} \max_{c}\; p(c, s),
--   $$
--   the minimum over legal MIN strategies $s$ of the maximum over legal MAX strategies $c$ of MAX's payoff. The paper notes that this equals $\max_c \min_s p(c, s)$, since the game is a finite perfect-information two-person zero-sum game.
--
--   **Formalization Note** Infimum and supremum in $\mathbb N \cup \{\infty\}$; the payoff takes finitely many values, so they are attained. The min–max equality is a consequence and is not used as the definition.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMax
import Definitions.Def_MatroidOptGame_LegalMin
import Definitions.Def_MatroidOptGame_payoff

namespace MatroidOptGame

/-- The value of the game, `V(M, w) = min_s max_c p(c, s)`, over legal MIN strategies `s` and legal
MAX strategies `c`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 ("The value of the game is V(M, w) = min_s max_c p(c, s) =
max_c min_s p(c, s)").

**Formalization Note.** Valued in `ℕ∞` (the payoff can be `∞`). Infimum and supremum are taken
in the complete lattice `ℕ∞`; the payoff takes finitely many values, so they are attained. The
equality with `max_c min_s` is a consequence (a pure equilibrium exists) and is not used as the
definition. -/
noncomputable def value {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (w : α → ℕ) : ℕ∞ :=
  ⨅ s : {s : Strategy α // LegalMin M s}, ⨆ c : {c : Strategy α // LegalMax M c}, payoff M w c.1 s.1

end MatroidOptGame


