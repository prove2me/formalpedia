-- Prove2me | Definitions.Def_ReplParity_mult
-- name    : ReplParity_mult
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:48.849355+00:00
-- url     : https://prove2.me/theorems/fb85124f-00a9-4248-8e63-61a2f88168a7
-- title:
--   Multiplicities $n_S(V)$ and the vector $F(S)$
-- statement:
--   For a sequence $S$ of vectors in $\mathbb F_2^n$ and a subspace $V$, $n_S(V)$ is the number of parts of the stable partition of $S$ (zero vectors discarded) whose span is $V$. The vector of multiplicities is $F(S)=(n_S(V))_V$, indexed by all subspaces $V$ of $\mathbb F_2^n$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.4, p.13 (PDF p.15); §3.1, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ReplParity_stablePartition

namespace ReplParity

open Classical in
/-- **Multiplicities `n_S(V)`.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity
and a Geometric Characterization*, STOC 2027 submission (manuscript sha256 40424491…), §2.4, p.13
(PDF p.15): "Let n_S(V) be the number of parts whose span is the subspace V." and §3.1, p.15:
"We write F(S) = (n_S(V))_V for the vector of multiplicities of a sample S, indexed by all
subspaces V of 𝔽ⁿ₂."

`mult S V = n_S(V)`; the vector `F(S)` is the function `V ↦ mult S V`. Zero vectors of `S` are
discarded before partitioning (`stablePartition`). -/
noncomputable def mult {n : ℕ} (S : List (Vec n)) (V : Subsp n) : ℕ :=
  ((stablePartition S).filter (fun P => spanOf P = V)).length

end ReplParity


