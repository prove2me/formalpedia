-- Prove2me | Definitions.Def_DetCCHard_Supplement_RawList
-- name    : DetCCHard_Supplement_RawList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:53:58.755468+00:00
-- url     : https://prove2.me/theorems/7f7037fd-e49b-4af4-bb65-d194fdf22990
-- title:
--   Indexed tuple lists with rational label weights, full products and interlaces
-- statement:
--   An **indexed list of tuples** consists of a finite label set $L$, rational weights $\nu$ on the labels and a decoder $z : L \to Y^{\iota}$; distinct labels may decode to the same tuple, each keeping its own weight. The **full product list** has labels $Y^{\iota}$, the identity decoder and the product weights
--   $$
--   \mu_\iota(f) = \prod_{i \in \iota} \mu(f_i).
--   $$
--   The **interlace** of a base matrix $R : X \times Y \to \{0,1\}$ on a list has rows $(i, u) \in \iota \times X$, one column per label $\ell$, and entry $R(u, z_i(\ell))$; block $i$ is $\{i\} \times X$. The **full $Q$-fold interlace, transposed**, $(I_Q(W))^{\mathsf T}$, has a row for each $f \in Y^Q$ and a column for each $(i, u) \in [Q] \times X$, with entry $W(u, f_i)$.
--
--   These are the list objects of the amplification construction: full products in the randomized reduction, explicit lists in the deterministic one.
--
--   **Formalization Note** This is the published tuple list (`DetCCHard.TupleList`) without its built-in proof that the weights are positive and sum to one; the construction forms full products of weights it builds itself, so positivity and normalization are stated as hypotheses (`IsWeight`) where needed.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definitions 4.3 and 4.4, pp.14–15

import Mathlib
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_TupleList

namespace DetCCHard.Supplement

open DetCCHard

/-- An **indexed list of tuples with rational label weights** (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, Definition 4.4, p.15): a finite label set `L`,
rational weights `ν` on the labels, and a decoder `z : L → Y^ι`.

**Formalization Note** This is the published `DetCCHard.TupleList` without its built-in proof that
the weights are positive and sum to one. The amplification construction (Definitions 6.2 and 8.3)
forms full products of weights it builds itself, so the positivity and normalization are stated as
the hypothesis `IsWeight T.ν` wherever a statement needs them rather than proved inside the
construction. Distinct labels may decode to the same tuple; each keeps its own weight. -/
structure RawList (Y ι : Type) where
  /-- the label set -/
  L : Type
  [instFintype : Fintype L]
  [instDecEq : DecidableEq L]
  /-- the label weights -/
  ν : L → ℚ
  /-- the decoder: label `ℓ` decodes to the tuple `z ℓ` -/
  z : L → ι → Y

attribute [instance] RawList.instFintype RawList.instDecEq

/-- The **product weights** `μ_ι(f) = ∏_{i ∈ ι} μ(f_i)` on tuples `f : ι → Y` (§4.2, p.14). -/
def prodWt {ι Y : Type} [Fintype ι] (μ : Y → ℚ) : (ι → Y) → ℚ :=
  fun f => ∏ i, μ (f i)

/-- The **full product list** (§4.3, p.16: "The full product is the list with labels `Y^q`,
identity decoder and product weights"). -/
def RawList.full {Y : Type} [Fintype Y] [DecidableEq Y] (μ : Y → ℚ) (ι : Type) [Fintype ι]
    [DecidableEq ι] : RawList Y ι where
  L := ι → Y
  ν := prodWt μ
  z := id

/-- The **interlace of a base matrix on a list** (Definitions 4.3 and 4.4, pp.14–15): rows
`(i, u) ∈ ι × X`, one column per label `ℓ`, entry `R(u, z_i(ℓ))`; block `i` is `{i} × X`. -/
def RawList.interlace {X Y ι : Type} (R : X → Y → Bool) (T : RawList Y ι) : ι × X → T.L → Bool :=
  fun r ℓ => R r.2 (T.z ℓ r.1)

/-- The **full `Q`-fold interlace, transposed** (Definition 4.3, p.14, and Theorem 6.17, p.31):
`(I_Q(W))^T`, with a row for each column tuple `f ∈ Y^Q` and a column for each `(i, u) ∈ [Q] × X`,
entry `W(u, f_i)`. Its row weights are `prodWt μY` and its column weights `μX(u)/Q`
(published `interlaceRowWt`).

**Formalization Note** Blocks are indexed from `0` (`Fin Q`). -/
def fullInterlaceT {X Y : Type} (W : X → Y → Bool) (Q : ℕ) : (Fin Q → Y) → Fin Q × X → Bool :=
  fun f p => W p.2 (f p.1)

end DetCCHard.Supplement


