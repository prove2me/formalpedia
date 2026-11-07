-- Prove2me | Definitions.Def_PctDistortion_Election
-- name    : PctDistortion_Election
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:58.158936+00:00
-- url     : https://prove2.me/theorems/1227046f-714e-4bad-a868-06a65eda228d
-- title:
--   Elections: voters with strict total rankings of candidates
-- statement:
--   An **election** $\mathcal E=(V,C,\vec\succ)$ consists of a set $V$ of $n$ voters, a set $C$ of $m$ candidates, and a ranking profile $\vec\succ=(\succ_v)_{v\in V}$. Each ranking $\succ_v$ is a strict total order on $C$; $a\succ_v b$ means that voter $v$ strictly prefers $a$ to $b$.
--
--   Elections are the input of every voting rule in this mission; the α-majority digraph, the percentile costs and the distortion of a lottery are all computed from the rankings.
--
--   **Formalization Note** The structure records the relation `prefers v` and a proof that it is a strict total order (`IsStrictTotalOrder`). Finiteness and nonemptiness of $V$ and $C$ are hypotheses of the theorems ($n,m\ge 1$).
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §2, p.8

import Mathlib

set_option autoImplicit false

namespace PctDistortion

/-- An **election** `E = (V, C, ≻⃗)` with voter type `V` and candidate type `C`: every voter
`v` has a ranking `≻_v`, a strict total order on `C`; `E.prefers v c c'` means `c ≻_v c'`,
i.e. voter `v` strictly prefers `c` to `c'`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2, p.8: "An election is a triple E = (V, C, ≻⃗), where V is a set of n voters, C is a set of
m candidates, and ≻⃗ = (≻v)v∈V is a ranking profile. Each ranking ≻v is a total order on C."

**Formalization Note.** Finiteness and nonemptiness of `V` and `C` are not part of the
structure; every theorem of the mission assumes `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`
(the paper's `n` voters and `m` candidates, `n, m ≥ 1`). -/
structure Election (V C : Type) where
  /-- `prefers v c c'`: voter `v` strictly prefers `c` to `c'` (`c ≻_v c'`). -/
  prefers : V → C → C → Prop
  /-- Each ranking `≻_v` is a strict total order on `C`. -/
  isStrictTotalOrder : ∀ v, IsStrictTotalOrder C (prefers v)

end PctDistortion


