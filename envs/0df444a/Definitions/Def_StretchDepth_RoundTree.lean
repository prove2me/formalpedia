-- Prove2me | Definitions.Def_StretchDepth_RoundTree
-- name    : StretchDepth_RoundTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:03:26.700247+00:00
-- url     : https://prove2.me/theorems/575cd958-35a6-487e-9132-bee1b8858c85
-- title:
--   Round trees: adaptive batches of oracle queries
-- statement:
--   A **round tree** describes the computation of a query procedure on one fixed input. It is either a leaf that outputs a string $y\in\{0,1\}^M$, or a round: a list of queries $w_1,\dots,w_\ell\in\{0,1\}^n$ together with a continuation that receives the answer vector $(G(w_1),\dots,G(w_\ell))\in(\{0,1\}^N)^\ell$ and returns the next tree.
--
--   Given an oracle $G$ one obtains the output of the run, the list of batches asked (one list per round, in chronological order, with repetitions), the number of queries (with multiplicity) and the number of rounds. This is the combinatorial content of the "adaptive rounds" of a construction.
--
--   **Formalization Note** A tree holds no oracle: its only access to $G$ is through the answer vector. An empty batch counts as a round; such a round can be deleted without changing anything else.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Definition 1, p.13

import Mathlib

namespace StretchDepth

/-- **Bit strings.** `{0,1}^k`, as `Fin k → Bool`. -/
abbrev Bits (k : ℕ) := Fin k → Bool

/-- **Round tree of a construction.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Definition 1, p.13: "first a sequence of queries w1, . . . , wℓ ∈ {0, 1}n is
determined purely as a function of the input x; the procedure then evaluates G(w1), . . . , G(wℓ)
∈ {0, 1}N, and as a function of these returned values and the original input x, a second batch of
queries is determined."

For one fixed input `x`, the computation is either `output y` or `round ws k`: ask the batch `ws`
and continue with `k` on the vector of answers.

**Formalization Note.** A tree has no oracle inside it: its only access to `G` is through the
answer vector, so it is a query procedure. Bounds on queries and rounds are imposed on real runs
only (`IsConstruction`), never on branches no oracle reaches. -/
inductive RoundTree (n N M : ℕ) where
  /-- Stop and output `y`. -/
  | output (y : Bits M)
  /-- Ask the batch `ws` and continue with `k` on the vector of answers. -/
  | round (ws : List (Bits n)) (k : (Fin ws.length → Bits N) → RoundTree n N M)

variable {n N M : ℕ}

/-- The output of the tree when the oracle is `G` (`H^G(x)` for the tree of `x`). -/
def run (G : Bits n → Bits N) : RoundTree n N M → Bits M
  | .output y => y
  | .round ws k => run G (k fun i => G (ws.get i))

/-- The batches asked when the oracle is `G`, in order, one list per round, with repetitions. -/
def queriesOf (G : Bits n → Bits N) : RoundTree n N M → List (List (Bits n))
  | .output _ => []
  | .round ws k => ws :: queriesOf G (k fun i => G (ws.get i))

/-- The number of queries made when the oracle is `G`, with multiplicity. -/
def numQueries (G : Bits n → Bits N) (t : RoundTree n N M) : ℕ :=
  (queriesOf G t).flatten.length

/-- The number of adaptive rounds when the oracle is `G`. An empty batch counts as a round. -/
def numRounds (G : Bits n → Bits N) (t : RoundTree n N M) : ℕ :=
  (queriesOf G t).length

end StretchDepth


