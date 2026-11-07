-- Prove2me | Definitions.Def_NSWBetter_Alloc
-- name    : NSWBetter_Alloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:16.163194+00:00
-- url     : https://prove2.me/theorems/ca4dd91a-5e98-478e-bb7b-23107f167b98
-- title:
--   Allocation: an $n$-subpartition of the goods
-- statement:
--   An **allocation** $X=(X_1,\dots,X_n)$ is an $n$-subpartition of the goods: the bundles are pairwise disjoint and need not cover $G$.
--
--   **Formalization Note** An allocation is a map from goods to `Option` agents: good $g$ belongs to $X_i$ when it is mapped to `some i`, and is unallocated when mapped to `none`.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.8 (an allocation is an n-subpartition)

import Mathlib
import Definitions.Def_NSWBetter_Inst

namespace NSWBetter

/-- **Allocations.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.8: "An allocation X = (X1, . . . , Xn) is an n-subpartition of the set of goods."

`Alloc I = Fin I.m → Option (Fin I.n)`: each good goes to at most one agent (`some i`) or to nobody (`none`); the bundle of agent `i` is `X_i = {g | X g = some i}`. -/
abbrev Alloc (I : Inst) : Type := Fin I.m → Option (Fin I.n)

end NSWBetter


