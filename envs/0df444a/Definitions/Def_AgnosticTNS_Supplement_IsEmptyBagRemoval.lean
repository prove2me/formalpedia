-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_IsEmptyBagRemoval
-- name    : AgnosticTNS_Supplement_IsEmptyBagRemoval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:39:09.610967+00:00
-- url     : https://prove2.me/theorems/45df1600-0d41-4c33-9be7-b4d36b1b6635
-- title:
--   Tree-indexed partition obtained by removing empty bags (Lemma 6.13)
-- statement:
--   Let $(\mathcal T,\mathcal X)$ be a tree-cut decomposition of $G$. A tree $\hat T$ (on $m$ nodes) with bags $\hat{\mathcal X}=\{\hat X_t\}$ is *obtained by removing empty bags* if $\hat{\mathcal X}$ is a partition of $V(G)$ into nonempty sets and
--   1. every bag $\hat X_t$ is one of the (nonempty) bags of $\mathcal X$;
--   2. for every edge $f$ of $\hat T$, the cut of $V(G)$ induced by $\hat T-f$ equals the cut induced by some edge of $\mathcal T$.
--
--   These are conclusions 1–2 of Lemma 6.13; every result of contracting empty bags into neighbouring bags satisfies them.
--
--   **Formalization Note** Conclusion 2 is stated on vertex sets: the union of the bags on one side of $f$ equals the union of the bags on one side of some edge of $\mathcal T$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 6.13, conclusions 1–2, p.55

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_TreeCutDecomp
import Definitions.Def_AgnosticTNS_Supplement_treeSide

namespace AgnosticTNS.Supplement

/-- **A tree-indexed partition obtained by removing empty bags**, Lemma 6.13, p.55 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
a tree `T̂` on `Fin m` and a partition `{X̂_t}` of `V(G)` into nonempty bags such that
1. every bag `X̂_t` is one of the (nonempty) bags of `(𝒯, X)`, and
2. for every edge `f = {t, t'}` of `T̂`, the cut of `V(G)` induced by `T̂ − f` equals the cut induced by
   some edge of `𝒯`.

**Formalization Note** Conclusion 2 is stated on vertex sets: the union of the bags on the `t'`-side
equals the union of the bags on one side of some edge `{s, s'}` of `𝒯`. Every result of the
empty-bag contraction in the proof of Lemma 6.13 satisfies 1–2; conclusion 3 of the lemma is a
consequence of the width bound and is not part of this predicate. -/
def IsEmptyBagRemoval {n m : ℕ} (D : TreeCutDecomp n) (That : SimpleGraph (Fin m))
    (Xhat : Fin m → Finset (Fin n)) : Prop :=
  That.IsTree ∧ (∀ t, (Xhat t).Nonempty) ∧ (∀ s t, s ≠ t → Disjoint (Xhat s) (Xhat t)) ∧
    (∀ v, ∃ t, v ∈ Xhat t) ∧ (∀ t, ∃ s, Xhat t = D.X s) ∧
    ∀ t t', That.Adj t t' → ∃ s s', D.T.Adj s s' ∧
      (treeSide That t t').biUnion Xhat = (treeSide D.T s s').biUnion D.X

end AgnosticTNS.Supplement


