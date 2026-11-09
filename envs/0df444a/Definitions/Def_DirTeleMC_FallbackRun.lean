-- Prove2me | Definitions.Def_DirTeleMC_FallbackRun
-- name    : DirTeleMC_FallbackRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:33:01.517638+00:00
-- url     : https://prove2.me/theorems/523b0bf7-fab9-47e0-9b48-92dcdcd665dd
-- title:
--   The fallback schedule of Algorithm 2, line 2
-- statement:
--   The **fallback schedule** is the busy schedule along a shortest-path out-arborescence of $G$ from $s$ to the $k$ terminals of $K$ nearest to $s$, pruned to them: a set $Y \subseteq K$ of $k$ terminals with $\mathrm{dist}(s, y) \le \mathrm{dist}(s, t)$ for $y \in Y$, $t \in K \setminus Y$, a shortest-path out-arborescence from $s$ pruned to $Y$, and any child order. For DTM, $Y = K$.
--
--   The relation contains every run: ties among nearest terminals, the tree and the child order are left open.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Algorithm 2, line 2, p.24 (PDF p.25); §3, p.9 (PDF p.10); Lemma B.3, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_DirTeleMC_IsPrunedSPT
import Definitions.Def_DirTeleMC_arbSchedule

namespace DirTeleMC

/-- **The fallback schedule** of Algorithm 2, line 2.
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Algorithm 2, line 2, p.24: "best ← the busy schedule along a shortest-path
out-arborescence from s to the k terminals of K nearest to s"; §3, p.9; Lemma B.3, p.26.

`FallbackRun I S`: for some set `Y` of `k` terminals nearest to `s` (every terminal of `Y` is at distance at most
that of every terminal outside `Y`), some shortest-path out-arborescence of `G` from `s` pruned to `Y`, and some
child order, `S` is the busy schedule along it.

**Formalization Note.** For DTM (`k = |K|`), `Y = K`. Ties among the nearest terminals, the shortest-path
tree and the child order of the busy schedule are left open: the relation contains every run. -/
def FallbackRun (I : Inst) (S : Schedule I.n) : Prop :=
  ∃ (Y : Finset (Fin I.n)) (A : Arb I.n) (ord : Fin I.n → List (Fin I.n)),
    Y ⊆ I.K ∧ Y.card = I.k ∧ (∀ y ∈ Y, ∀ t ∈ I.K \ Y, dist I.adj I.s y ≤ dist I.adj I.s t) ∧
    IsPrunedSPT I.adj I.s Y A ∧ A.IsChildOrder ord ∧ S = A.arbSchedule ord

end DirTeleMC


