-- Prove2me | Definitions.Def_ProcNetStab_Supplement_WeightedRationalizable
-- name    : ProcNetStab_Supplement_WeightedRationalizable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:57:12.630077+00:00
-- url     : https://prove2.me/theorems/35f328ff-7f6f-50d7-b21a-ff3a18f2ca81
-- title:
--   Rationalizable as weighted pairwise stable with weighted $k$-anonymous utilities (Definition 5.1 as printed)
-- statement:
--   Let $g$ be the observed weighted network on $V$, $k \in \mathbb N$ and $L : V \to T$ a type map. The network $g$ is **rationalizable as weighted pairwise stable with weighted $k$-anonymous utilities** if there is a profile $u = (u_a)_{a \in V}$ of real-valued utility functions on all weighted networks on $V$ such that
--
--   1. $u$ satisfies weighted $k$-anonymity (Definition 5.2), and
--   2. $g$ is weighted pairwise stable with respect to $u$ (Definition 5.1, as printed).
--
--   This is the weighted counterpart of rationalizability (Definition 3.2) used in the statement of Theorem 2.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Theorem 2, p.20, with Definition 3.2, p.7, and Definitions 5.1–5.2, pp.18–19

import Mathlib
import Definitions.Def_ProcNetStab_Supplement_WeightedPairwiseStable
import Definitions.Def_ProcNetStab_Supplement_WeightedKAnonymous

namespace ProcNetStab.Supplement

/-- **Rationalizable as weighted pairwise stable with weighted `k`-anonymous utilities**, with
Definition 5.1 as printed (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript,
2025), Theorem 2, p.20, with Definitions 5.1 and 5.2, pp.18–19): there is a utility profile
`u = (u_a)_{a ∈ V}` on all weighted networks that satisfies weighted `k`-anonymity and with respect
to which the observed weighted network `g` is weighted pairwise stable (Definition 5.1). -/
def WeightedRationalizable {V T : Type*} (L : V → T) (g : WeightedNet V) (k : ℕ) : Prop :=
  ∃ u : V → WeightedNet V → ℝ, WeightedKAnonymous L g k u ∧ WeightedPairwiseStable g u

end ProcNetStab.Supplement


