-- Prove2me | Definitions.Def_ProcNetStab_Rationalizable
-- name    : ProcNetStab_Rationalizable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:44:42.588725+00:00
-- url     : https://prove2.me/theorems/a086e5f6-04eb-4233-ac3a-31d9775df370
-- title:
--   Rationalizable as pairwise stable with $k$-anonymous preferences
-- statement:
--   Let $g$ be the observed network on $V$, $L : V \to T$ a type map and $k \in \mathbb N$. The network $g$ is **rationalizable as pairwise stable with $k$-anonymous preferences** if there is a profile $\succeq = (\succeq_a)_{a \in V}$ of preference relations (weak orders) on the set of all networks on $V$ such that $\succeq$ satisfies $k$-anonymity and $g$ is pairwise stable with respect to $\succeq$.
--
--   Without the anonymity restriction every network is rationalizable (Remark 1 of the paper); with it, rationalizability becomes a testable property of the observed network.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 3.2, p.7, with the restriction of Definition 3.9, p.10, as used in Theorem 1, p.15

import Mathlib
import Definitions.Def_ProcNetStab_PairwiseStable
import Definitions.Def_ProcNetStab_KAnonymous

namespace ProcNetStab

/-- **Rationalizable as pairwise stable with `k`-anonymous preferences** (Chiong, Qi, *Stability of
Procurement Networks* (authors' manuscript, 2025), Definition 3.2, p.7, with the restriction of
Definition 3.9, p.10, as used in Theorem 1, p.15): there is a profile of preference relations
(weak orders) `⪰ = (⪰_a)_{a ∈ V}` on all networks on `V` that satisfies `k`-anonymity and with
respect to which the observed network `g` is pairwise stable. -/
def Rationalizable {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ pref : V → SimpleGraph V → SimpleGraph V → Prop,
    (∀ a, IsWeakOrder (pref a)) ∧ KAnonymous L g k pref ∧ PairwiseStable g pref

end ProcNetStab


