-- Prove2me | Definitions.Def_TreeEdgeRankPC_Supplement_GapPromise
-- name    : TreeEdgeRankPC_Supplement_GapPromise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:09:40.486146+00:00
-- url     : https://prove2.me/theorems/2003fdb9-6ef8-4fe5-8bdc-b541c2972078
-- title:
--   Promise problems with additive gap $r$ for $\mathrm{er}(T)$, and their P-completeness under NC¹ many-one reductions
-- statement:
--   A **promise problem** is a pair $(Y,N)$ of sets of binary strings: the YES instances and the NO instances. Strings outside $Y\cup N$ violate the promise and carry no requirement. The pair $(Y,N)$ is **P-complete under NC¹ many-one reductions** if
--
--   1. *(membership)* some language $L\in\mathrm P$ satisfies $Y\subseteq L$ and $L\cap N=\emptyset$, and
--   2. *(hardness)* for every language $L'\in\mathrm P$ there is a map $f$ computable by a logspace-uniform family of bounded fan-in circuits of polynomial size and depth $O(\log n)$ such that
--   $$x\in L'\ \Rightarrow\ f(x)\in Y,\qquad x\notin L'\ \Rightarrow\ f(x)\in N.$$
--
--   For a tree $T$ and an integer $K\ge0$, write $\langle T,K\rangle$ for the binary code of the instance ($K$ in binary). For a fixed integer $r$ and a bound $D$, the **gap-$r$ instances** are
--   $$\mathrm{YES}=\{\langle T,K\rangle:\ \mathrm{er}(T)\le K\},\qquad \mathrm{NO}_r=\{\langle T,K\rangle:\ \mathrm{er}(T)\ge K+r\},$$
--   and their restrictions $\mathrm{YES}^{D}$, $\mathrm{NO}_r^{D}$ to trees of diameter at most $D$ (every two vertices at distance at most $D$). Here $\mathrm{er}(T)$ is the least possible maximum rank of an edge ranking of $T$. A string that codes no tree is in none of these sets.
--
--   These are the decision problems of Theorem 4.11 (constant additive gap): distinguishing $\mathrm{er}(T)\le K$ from $\mathrm{er}(T)\ge K+r$.
--
--   **Formalization Note** $\mathrm{YES}$ is the published language `TreeEdgeRankPC.TER`, and $\mathrm{YES}^6$ coincides with the published `TER6`. P is the published `CookPvsNP.P Bool`, NC¹ computability the published `TreeEdgeRankPC.NC1Computable`. For a language $L$, the pair $(L, L^{\mathrm c})$ is P-complete in this sense exactly when $L$ is P-complete in the sense of `TreeEdgeRankPC.PCompleteNC1`.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Theorem 4.11, p.21 (the promise problem); §3.2, p.12 (NC¹ many-one reductions, P-completeness); §3.1, p.10 (er(T), diameter)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TreeEdgeRankPC_EdgeRanking
import Definitions.Def_TreeEdgeRankPC_NC1
import Definitions.Def_TreeEdgeRankPC_TreeLanguage

namespace TreeEdgeRankPC.Supplement

open TreeEdgeRankPC

/-- **P-completeness of a promise problem under NC¹ many-one reductions**, for the sentence of
Theorem 4.11, p.21 (Giliberti–Hajiaghayi–Yun, *Parallel Edge Ranking of Trees*, arXiv:2610.12438,
held version of 2026-11-02, sha256 9e04ca7b…): "promised that either … or …, deciding which
inequality holds is P-complete under NC^1 many-one reductions", read with the definitions of §3.2,
p.12.

A promise problem is a pair `(Y, N)` of sets of strings: the YES instances and the NO instances;
strings outside `Y ∪ N` violate the promise and carry no requirement.
1. *Membership in P*: some language `L ∈ P` contains every YES instance and no NO instance
   (it decides the promise problem; its answer outside the promise is arbitrary).
2. *P-hardness*: every language `L' ∈ P` reduces to `(Y, N)` by a logspace-uniform NC¹-computable
   map `f` sending every `x ∈ L'` into `Y` and every `x ∉ L'` into `N`.

**Formalization Note.** `NC1Computable` and `CookPvsNP.P Bool` are the published definitions used by
`TreeEdgeRankPC.PCompleteNC1`; for a language `L` with complement `Lᶜ`,
`PromisePCompleteNC1 L Lᶜ ↔ PCompleteNC1 L`. The reduction (and its NC¹ constants) is chosen after
`L'`, as in `PCompleteNC1`. -/
def PromisePCompleteNC1 (Y N : Set (List Bool)) : Prop :=
  (∃ L ∈ CookPvsNP.P Bool, Y ⊆ L ∧ Disjoint L N) ∧
    ∀ L' ∈ CookPvsNP.P Bool, ∃ f : List Bool → List Bool, NC1Computable f ∧
      ∀ x, (x ∈ L' → f x ∈ Y) ∧ (x ∉ L' → f x ∈ N)

/-- The **NO instances with additive gap `r`**, Theorem 4.11, p.21: codes `encTree T K` of a tree `T`
and an integer `K ≥ 0` (in binary) with `er(T) ≥ K + r`. The YES instances (`er(T) ≤ K`) are the
published language `TreeEdgeRankPC.TER`. A string that codes no tree is in neither set. -/
def GapNo (r : ℕ) : Set (List Bool) :=
  {s | ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (K : ℕ), T.IsTree ∧ s = encTree T K ∧ K + r ≤ er T}

/-- The **YES instances restricted to trees of diameter at most `D`**, Theorem 4.11, p.21 ("The
hardness remains for trees of diameter at most 6r", used with `D = 6r`): codes `encTree T K` of a
tree `T` with `∀ u v, dist(u, v) ≤ D` and `er(T) ≤ K`.

**Formalization Note.** §3.1, p.10: a tree "has diameter D when its longest simple path has D
edges"; in a tree this is the maximum of `T.dist`, as in the published `TER6` (which is
`GapYesDiam 6`). -/
def GapYesDiam (D : ℕ) : Set (List Bool) :=
  {s | ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (K : ℕ),
    T.IsTree ∧ (∀ u v, T.dist u v ≤ D) ∧ s = encTree T K ∧ er T ≤ K}

/-- The **NO instances with additive gap `r`, restricted to trees of diameter at most `D`**,
Theorem 4.11, p.21: codes `encTree T K` of a tree `T` with `∀ u v, dist(u, v) ≤ D` and
`er(T) ≥ K + r`. -/
def GapNoDiam (r D : ℕ) : Set (List Bool) :=
  {s | ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (K : ℕ),
    T.IsTree ∧ (∀ u v, T.dist u v ≤ D) ∧ s = encTree T K ∧ K + r ≤ er T}

end TreeEdgeRankPC.Supplement


