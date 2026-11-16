-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_QSNEExists
-- name    : QuasiStrictNE_Supplement_QSNEExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:42:38.651429+00:00
-- url     : https://prove2.me/theorems/e7d58a15-d40b-4b83-a050-593123d2db58
-- title:
--   Decision problem: does an $n$-player game have a quasi-strict equilibrium?
-- statement:
--   For a fixed number $n$ of players, $\mathrm{QSNEExists}_n$ is the set of binary strings that code an $n$-player game $G$ in strategic form with rational payoffs, in which every player has at least one action and which has a quasi-strict Nash equilibrium.
--
--   $$
--   \mathrm{QSNEExists}_n = \{\operatorname{enc}(G) : k_i \ge 1 \text{ for all } i,\ G \text{ has a quasi-strict Nash equilibrium}\}.
--   $$
--
--   This is the decision problem of Theorem 2 for general-sum games.
--
--   **Formalization Note** $n$ is fixed and is not part of the input. The action counts and the payoff table are the input. Strings that do not code such a game are not in the language.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 2, p.19; p.3

import Mathlib
import Definitions.Def_QuasiStrictNE_Supplement_NGame_IsQSNE
import Definitions.Def_QuasiStrictNE_Supplement_NGame_enc

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **The decision problem of Theorem 2, general-sum** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Theorem 2, p.19: "deciding whether an
n-player game in strategic form with rational payoffs admits a quasi-strict Nash equilibrium").

For a fixed number `n` of players, `QSNEExists n` is the set of binary words that are the code
`G.enc` of an `n`-player rational game `G` in which every player has at least one action and which
has a quasi-strict Nash equilibrium (a real mixed profile `ν` with `G.IsQSNE ν`).

**Formalization Note** `n` is fixed (one language per `n`); the action counts and the payoff table
are the input. A word that is not the code of such a game is not in the language. -/
def QSNEExists (n : ℕ) : Set (List Bool) :=
  {w | ∃ G : NGame n, (∀ i, 1 ≤ G.k i) ∧ w = G.enc ∧ ∃ ν, G.IsQSNE ν}

end QuasiStrictNE.Supplement


