-- Prove2me | Definitions.Def_HypRecov_IsCorrect
-- name    : HypRecov_IsCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:57.608349+00:00
-- url     : https://prove2.me/theorems/68f51649-1802-4707-af53-090c91073f0c
-- title:
--   Correct outputs: exactly $\mathcal B_k(H)$, each edge once, and a truncated-cut representation
-- statement:
--   An output string is **correct** for $(H,k)$ in the sense of Theorem 1.1 if it encodes a list $L$ of vertex sets and a weighted hypergraph $\widehat H$ such that
--
--   1. $L$ has no repetition and its members are exactly the edges of $\mathcal B_k(H)$;
--   2. for every $S\subseteq V$, $\min\{\mathrm{cut}_H(S),k\}=\min\{\mathrm{cut}_{\widehat H}(S),k\}$.
--
--   For Theorems 6.4 and D.1 an output is correct if it encodes such a list $L$ alone. Each edge is "reported once with all its vertices" (p.1).
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §1.1, p.1 (PDF p.2); Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_cutW
import Definitions.Def_HypRecov_encOut

namespace HypRecov

/-- **A correct output of Theorem 1.1.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous
Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem 1.1, p.2 (PDF p.3):
"recovers ℬ_k(H) … The same successful state gives a hypergraph representation Ĥ, permitting weighted
synthetic edges, such that simultaneously for every S ⊆ V, min{cut_H(S), k} = min{cut_Ĥ(S), k}"; §1.1,
p.1: "Each edge is reported once with all its vertices."

`IsCorrect E k out`: `out` encodes a duplicate-free list `L` whose members are exactly the edges of
`ℬ_k(H)`, and a weighted hypergraph `Ĥ` whose cut function agrees with that of `H` after truncation
at `k`, for every `S`. -/
def IsCorrect {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) (out : List Bool) : Prop :=
  ∃ (L : List (Finset (Fin n))) (H : List (Finset (Fin n) × ℕ)),
    out = encOut L H ∧ L.Nodup ∧ L.toFinset = crisp E k ∧
      ∀ S : Finset (Fin n), min (cut E S) k = min (cutW H S) k

/-- **A correct edge list** (Theorems 6.4, p.15, and D.1, p.37): `out` encodes a duplicate-free list
of exactly the edges of `ℬ_k(H)`. -/
def IsCorrectList {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) (out : List Bool) : Prop :=
  ∃ L : List (Finset (Fin n)), out = encEdges L ∧ L.Nodup ∧ L.toFinset = crisp E k

end HypRecov


