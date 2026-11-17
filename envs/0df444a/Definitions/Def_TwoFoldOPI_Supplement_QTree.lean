-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_QTree
-- name    : TwoFoldOPI_Supplement_QTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:57:15.670922+00:00
-- url     : https://prove2.me/theorems/0c08965b-c032-4d83-9942-cea4265c95a4
-- title:
--   Computationally unbounded classical query algorithms
-- statement:
--   A **classical query algorithm** with unbounded local computation is a decision tree: each internal node queries the oracle at a point and branches on the answer; each leaf holds the output. Running it with an oracle $H$ gives its output and its number of queries.
--
--   Classical provers in the soundness claims of Theorems 11.9 and 11.10 are such trees.
--
--   **Formalization Note** A randomized classical prover is a mixture of deterministic trees, so a bound for every tree with at most $Q$ queries on every oracle is a bound for every randomized prover with at most $Q$ queries.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.2, Lemma 11.8, p. 61; §11.3, Theorems 11.9–11.10, p. 62

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **Computationally unbounded classical query algorithms (decision trees).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.2, Lemma 11.8, p.61 and §11.3, Theorems 11.9–11.10, p.62: "every computationally
unbounded classical prover making polynomially many classical queries"; p.61: "A classical
algorithm learns H_i(x_i) only by querying it."

A tree over queries `X`, answers `Y` and outputs `O`: `leaf o` stops with output `o`;
`query x next` asks the oracle at `x` and continues with `next (H x)`. `eval H` is the output
when run with oracle `H`, and `queries H` the number of queries made on that run.

**Formalization Note.** Local computation is unrestricted (any tree, any function of the answers
so far). A randomized classical prover is a probability mixture of such trees, so its acceptance
probability is an average of theirs; a bound for every deterministic tree with at most `Q`
queries on every oracle is therefore the same as a bound for every randomized prover with at most
`Q` queries. The module holds the inductive type with its two evaluation functions. -/
inductive QTree (X Y O : Type) where
  | leaf (o : O)
  | query (x : X) (next : Y → QTree X Y O)

/-- The output of the tree run with oracle `H`. -/
def QTree.eval {X Y O : Type} (H : X → Y) : QTree X Y O → O
  | .leaf o => o
  | .query x next => (next (H x)).eval H

/-- The number of queries made by the tree run with oracle `H`. -/
def QTree.queries {X Y O : Type} (H : X → Y) : QTree X Y O → ℕ
  | .leaf _ => 0
  | .query x next => (next (H x)).queries H + 1

end Supplement

end TwoFoldOPI


