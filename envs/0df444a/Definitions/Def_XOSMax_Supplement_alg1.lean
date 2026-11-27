-- Prove2me | Definitions.Def_XOSMax_Supplement_alg1
-- name    : XOSMax_Supplement_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:32:25.069339+00:00
-- url     : https://prove2.me/theorems/de2dd20c-4f7f-4320-9e19-f03aacd411d5
-- title:
--   Algorithm 1 for deterministic general-XOS approximation
-- statement:
--   Given $\varepsilon>0$ and an enumeration of $V$, Algorithm 1 queries every subset of cardinality at most $\lceil1/\varepsilon\rceil$ and returns the first one of maximum value.
--
--   The program is constructed without access to the input function; it sees $f$ only through value-oracle calls.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Algorithm 1, p.4

import Mathlib
import Definitions.Def_XOSMax_OracleProg

namespace XOSMax.Supplement

open XOSMax OracleProg

variable {E : Type} [DecidableEq E]

/-- Query a candidate and retain the first candidate of maximum value. -/
noncomputable def alg1Consider (inc : Option (Finset E × ℝ)) (X : Finset E) :
    OracleProg E (Option (Finset E × ℝ)) := do
  tick
  let a ← ask X
  tick
  match inc with
  | none => pure (some (X, a))
  | some (Y, b) => if b < a then pure (some (X, a)) else pure (some (Y, b))

/-- **Algorithm 1:** query every subset of the enumerated ground set having cardinality at most
`⌈1/ε⌉` and return the first one of maximum value (Filmus, Kawase, Kobayashi & Yamaguchi,
arXiv:1811.09045v3, Algorithm 1, p.4).

**Formalization Note** The generator is the filtered powerset in its canonical finite-set order;
the source allows any appropriate constant-delay generator. The program is built only from `ε` and
`L`, never from the oracle. -/
noncomputable def alg1 (ε : ℝ) (L : List E) : OracleProg E (Finset E) := do
  let candidates := L.toFinset.powerset.filter fun X => X.card ≤ Nat.ceil (1 / ε)
  let inc ← candidates.toList.foldlM alg1Consider none
  match inc with
  | none => pure ∅
  | some (X, _) => pure X

end XOSMax.Supplement


