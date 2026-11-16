-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_QSNEExistsZS
-- name    : QuasiStrictNE_Supplement_QSNEExistsZS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:43:39.411193+00:00
-- url     : https://prove2.me/theorems/a33e6646-3689-4869-bfa0-f3129731166f
-- title:
--   Decision problem restricted to zero-sum $n$-player games
-- statement:
--   For a fixed number $n$ of players, $\mathrm{QSNEExistsZS}_n$ is the set of binary strings that code a **zero-sum** $n$-player game $G$ with rational payoffs, in which every player has at least one action and which has a quasi-strict Nash equilibrium.
--
--   This is the decision problem of the clause "even for zero-sum games" of Theorem 2.
--
--   **Formalization Note** Codes of games that are not zero-sum are not in the language.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 2, p.19; proof, p.20

import Mathlib
import Definitions.Def_QuasiStrictNE_Supplement_NGame_IsQSNE
import Definitions.Def_QuasiStrictNE_Supplement_NGame_IsZeroSum
import Definitions.Def_QuasiStrictNE_Supplement_NGame_enc

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **The decision problem of Theorem 2 restricted to zero-sum games** (Hansen & Nie, *On Existence
and Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Theorem 2, p.19: "…
admits a quasi-strict Nash equilibrium is ∃R-complete, even for zero-sum games").

For a fixed number `n` of players, `QSNEExistsZS n` is the set of binary words that are the code
`G.enc` of a zero-sum `n`-player rational game `G` in which every player has at least one action and
which has a quasi-strict Nash equilibrium.

**Formalization Note** Codes of games that are not zero-sum, and words that are not codes, are not in
the language. -/
def QSNEExistsZS (n : ℕ) : Set (List Bool) :=
  {w | ∃ G : NGame n, (∀ i, 1 ≤ G.k i) ∧ G.IsZeroSum ∧ w = G.enc ∧ ∃ ν, G.IsQSNE ν}

end QuasiStrictNE.Supplement


