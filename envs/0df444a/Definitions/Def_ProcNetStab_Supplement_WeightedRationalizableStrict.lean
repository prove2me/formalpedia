-- Prove2me | Definitions.Def_ProcNetStab_Supplement_WeightedRationalizableStrict
-- name    : ProcNetStab_Supplement_WeightedRationalizableStrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:57:49.856734+00:00
-- url     : https://prove2.me/theorems/2cc161a9-0630-439e-aa18-dce2c372f620
-- title:
--   Rationalizable as weighted pairwise stable with weighted $k$-anonymous utilities (strict reading of Definition 5.1)
-- statement:
--   Let $g$ be the observed weighted network on $V$, $k \in \mathbb N$ and $L : V \to T$ a type map. The network $g$ is **rationalizable as strictly weighted pairwise stable with weighted $k$-anonymous utilities** if there is a profile $u = (u_a)_{a \in V}$ of real-valued utility functions on all weighted networks on $V$ such that
--
--   1. $u$ satisfies weighted $k$-anonymity (Definition 5.2), and
--   2. $g$ is weighted pairwise stable with respect to $u$ in the strict reading of Definition 5.1 used in Appendix A.7.1: every increase of a weight is strictly refused by at least one endpoint.
--
--   It is the reading of rationalizability in Theorem 2 under which the paper's proof of necessity is written.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Theorem 2, p.20, with Definition 3.2, p.7, Definitions 5.1–5.2, pp.18–19, and Appendix A.7.1, p.OA-7

import Mathlib
import Definitions.Def_ProcNetStab_Supplement_WeightedPairwiseStableStrict
import Definitions.Def_ProcNetStab_Supplement_WeightedKAnonymous

namespace ProcNetStab.Supplement

/-- **Rationalizable as weighted pairwise stable with weighted `k`-anonymous utilities**, with the
strict reading of Definition 5.1's condition 2 used in Appendix A.7.1 (Chiong, Qi, *Stability of
Procurement Networks* (authors' manuscript, 2025), Theorem 2, p.20; Appendix A.7.1, p.OA-7): there
is a utility profile `u` on all weighted networks that satisfies weighted `k`-anonymity
(Definition 5.2) and with respect to which `g` is `WeightedPairwiseStableStrict`. -/
def WeightedRationalizableStrict {V T : Type*} (L : V → T) (g : WeightedNet V) (k : ℕ) : Prop :=
  ∃ u : V → WeightedNet V → ℝ, WeightedKAnonymous L g k u ∧ WeightedPairwiseStableStrict g u

end ProcNetStab.Supplement


