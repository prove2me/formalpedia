-- Prove2me | Definitions.Def_DetCCHard_TupleList
-- name    : DetCCHard_TupleList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:10.525758+00:00
-- url     : https://prove2.me/theorems/a1c907da-b219-49a9-86c0-e617a30ebfee
-- title:
--   Indexed tuple lists and exact $D$-wise independence
-- statement:
--   Let $Y$ be a finite alphabet and $\iota$ a set of coordinates ($\iota = [q]$ for tuples of length $q$). An **indexed tuple list** consists of a finite nonempty label set $L$, positive normalized rational weights $\nu$ on $L$, and a decoder $z : L \to Y^\iota$. Distinct labels may decode to the same tuple and keep separate weights.
--
--   Weights $\nu$ and a decoder $z$ are **exactly $D$-wise independent with marginal $\mu$** if for every $J \subseteq \iota$ with $|J| \le D$ and every $a \in Y^J$,
--   $$
--   \nu\bigl(\{\ell : z(\ell)_j = a_j \text{ for all } j \in J\}\bigr) = \prod_{j \in J} \mu(a_j),
--   $$
--   that is, the map $\ell \mapsto z(\ell)_J$ induces the product weights $\mu_J$. No independence on larger sets is required. The full product (labels $Y^q$, identity decoder, product weights) is exactly $D$-wise independent for every $D$.
--
--   Short exactly independent lists replace full products in the deterministic reduction.
--
--   **Formalization Note** The coordinate set is an arbitrary type so that nested lists (Lemma 8.2, coordinates $[q_{\rm out}] \times [q_{\rm in}]$) are tuple lists too. Independence is also stated for a bare weight function and decoder, so that it applies to conditional weights.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definition 4.4, p.15

import Mathlib
import Definitions.Def_DetCCHard_IsWeight

namespace DetCCHard

/-- An **indexed tuple list** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, Definition 4.4, p.15): a finite nonempty label set `L`, positive normalized
rational weights `ν` on its labels, and a decoder `z : L → Y^ι` sending each label to a tuple of
letters of the alphabet `Y`, indexed by the coordinate set `ι` (`ι = Fin q` for tuples of length
`q`).

**Formalization Note** The coordinate set is an arbitrary type `ι`, so that the nested lists of
Lemma 8.2 (coordinates `[q_out] × [q_in]`) are tuple lists too. Distinct labels may decode to the
same tuple; each keeps its own weight. -/
structure TupleList (Y ι : Type) where
  /-- the label set -/
  L : Type
  [instFintype : Fintype L]
  [instNonempty : Nonempty L]
  [instDecEq : DecidableEq L]
  /-- the label weights -/
  ν : L → ℚ
  /-- the weights are positive and sum to one -/
  hν : IsWeight ν
  /-- the decoder: label `ℓ` decodes to the tuple `z ℓ` -/
  z : L → ι → Y

attribute [instance] TupleList.instFintype TupleList.instNonempty TupleList.instDecEq

/-- **Exact `D`-wise independence** of weights `ν` and a decoder `z : L → Y^ι` with marginal `μ`
(Definition 4.4, p.15): for every set `J` of at most `D` coordinates and every assignment
`a : J → Y`, the labels whose decoded tuple agrees with `a` on `J` have total weight
`∏_{j ∈ J} μ(a_j)`, i.e. the map `ℓ ↦ z(ℓ)_J` induces the product weights `μ_J`. No independence
on larger sets is required.

**Formalization Note** Stated for a weight function and a decoder separately, so that it also
applies to conditional weights (Lemma 8.2, second sentence). -/
noncomputable def ExactlyIndepW {L Y ι : Type} [Fintype L] (ν : L → ℚ) (z : L → ι → Y) (D : ℕ)
    (μ : Y → ℚ) : Prop :=
  ∀ J : Finset ι, J.card ≤ D → ∀ a : J → Y,
    wt ν {ℓ | ∀ j : J, z ℓ j = a j} = ∏ j : J, μ (a j)

/-- A tuple list is **exactly `D`-wise independent with marginal `μ`** (Definition 4.4, p.15). -/
def ExactlyIndep {Y ι : Type} (T : TupleList Y ι) (D : ℕ) (μ : Y → ℚ) : Prop :=
  ExactlyIndepW T.ν T.z D μ

end DetCCHard


