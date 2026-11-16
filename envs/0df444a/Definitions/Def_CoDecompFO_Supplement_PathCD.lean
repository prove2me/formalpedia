-- Prove2me | Definitions.Def_CoDecompFO_Supplement_PathCD
-- name    : CoDecompFO_Supplement_PathCD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:49:17.005187+00:00
-- url     : https://prove2.me/theorems/f9fdf7ac-8c7b-46df-8a14-d8218bb674a7
-- title:
--   $(s,t)$-PATH given a tree co-decomposition and two matching families
-- statement:
--   An instance is a tree co-decomposition $\mathcal T$ of graphs and two matching families $s,t\in\lim\mathcal T$; the limit itself is not part of the input (¶3.1). It is a yes-instance if $\lim\mathcal T$ has a directed path from $s$ to $t$, where $(x,y)$ is an edge of $\lim\mathcal T$ iff $(x_u,y_u)$ is an edge of every bag $G_u$.
--
--   The input string over $\{0,1,2\}$ is the published code of $\mathcal T$ (bags and adhesions with bit tables of their relations, the maps as value lists), then the $b$ coordinates of $s$ and then of $t$, each number written in binary followed by the separator $2$. The language $\mathrm{PathCD}$ is the set of codes of yes-instances.
--
--   **Formalization Note** The code is injective, so membership depends only on the instance. Its length is polynomial in $b$ and the bag sizes (a graph bag on $n$ points costs $n^2$ bits), not in $|\lim\mathcal T|$, which can be as large as $w^b$.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶1.13, p.3; ¶3.1–3.2, p.8 (PDF pp.5, 10)

import Mathlib
import Definitions.Def_CoDecompFO_Supplement_GraphSig
import Definitions.Def_CoDecompFO_Codes
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

/-- A natural number over the alphabet `{0, 1, 2}`: its binary digits, least significant first, then the
separator `2`. -/
def encNat3 (n : ℕ) : List (Fin 3) := (Nat.bits n).map (fun b => if b then 1 else 0) ++ [2]

/-- The **input of (s,t)-PATH on a co-decomposition** (Bumpus et al., arXiv:2611.04658, held file sha256
d550d7af…, ¶1.13, p.3; ¶3.1–3.2, p.8): the code of the tree co-decomposition `T` (published `encCoDecomp`, bags and
adhesions as bit tables, the maps as value lists), then the `b` coordinates of the matching family `s`, then those
of `t`, each number written in binary over `{0, 1}` and closed by the separator `2`. The limit is not part of the
input: "when we are given a tree co-decomposition T, we are not also given its limit lim T". -/
noncomputable def pathCode (T : CoDecomp graphSig) (s t : T.Lim) : List (Fin 3) :=
  (encCoDecomp T ++ List.ofFn (fun i => (s.val i).val) ++ List.ofFn (fun i => (t.val i).val)).flatMap encNat3

/-- **(s,t)-PATH given only a tree co-decomposition and two matching families** (¶1.13, p.3; ¶3.2, p.8): the codes
of the instances `(T, s, t)` such that there is a directed path from `s` to `t` in `lim T`. An edge of `lim T` is
an edge in every bag simultaneously (¶2.7, p.7). Strings that are not codes of instances are not in the language.

**Formalization Note** A path is a finite sequence of edges, `Relation.ReflTransGen IsEdge s t`; the empty path
is allowed when `s = t`. The code is injective (each part's length is determined by the numbers before it), so
membership depends only on the instance. Each number has `O(log)` bits and a graph bag of `n` points costs `n²`
bits, so the input size is polynomial in `b` and the bag sizes, never in the size of the limit. -/
def PathCD : CookPvsNP.Lang (Fin 3) :=
  {w | ∃ (T : CoDecomp graphSig) (s t : T.Lim), w = pathCode T s t ∧ Relation.ReflTransGen IsEdge s t}

end Supplement

end CoDecompFO


