-- Prove2me | Definitions.Def_UniqueOptScores_charFn
-- name    : UniqueOptScores_charFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:12.152421+00:00
-- url     : https://prove2.me/theorems/bdf5571e-c523-4c94-8344-467efe7574e8
-- title:
--   Characteristic function of an oracle on $\mathbb N$
-- statement:
--   For an oracle $\chi$, $\mathrm{char}_\chi(n) = \chi(w_n) \in \{0,1\}$, the oracle read along the length-lexicographic enumeration. Turing reducibility and Turing equivalence of oracles are those of these functions (Mathlib's `TuringReducible`, `TuringEquivalent`).
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Appendix C, p.35 ("a member of every Turing degree")

import Mathlib
import Definitions.Def_UniqueOptScores_str

namespace UniqueOptScores

/-- **The characteristic function of an oracle, as a function on ℕ.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), App. C, p.35: "a member of every Turing degree", "A ≤T B", "B ≤T A".

`charFn χ n = χ(str n)` (as `0` or `1`), the oracle read along the length-lexicographic enumeration;
Turing reducibility of oracles is Mathlib's `TuringReducible` on these functions. -/
def charFn (χ : List Bool → Bool) : ℕ →. ℕ :=
  fun n => Part.some (χ (str n)).toNat

end UniqueOptScores


