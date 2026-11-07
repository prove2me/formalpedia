-- Prove2me | Definitions.Def_PctDistortion_abcMaximal
-- name    : PctDistortion_abcMaximal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:22.880428+00:00
-- url     : https://prove2.me/theorems/8b96dd5f-7425-457f-936a-20162b89e519
-- title:
--   ABC-maximal lotteries $\mathrm{ABC}(G)$ and $\mathrm{ABC}^\alpha(\mathcal E)$
-- statement:
--   For a simple digraph $G=(V,E)$, the set of **ABC-maximal lotteries** is the set of Alice's equilibrium strategies supported on the uncovered set:
--   $$\mathrm{ABC}(G)=\{a\in\Delta V:\ \mathrm{supp}(a)\subseteq U(G)\text{ and }(a,b)\text{ is a Nash equilibrium of }\mathcal G^{ABC}_G\text{ for some }b\in\Delta V\}.$$
--   For an election $\mathcal E$ and $\alpha\in[1/2,1)$, the **ABCα-maximal lotteries** are $\mathrm{ABC}^\alpha(\mathcal E)=\mathrm{ABC}(G^\alpha_{\mathcal E})$. The voting rule **ABCα-Maximal Lotteries** returns an arbitrary element of $\mathrm{ABC}^\alpha(\mathcal E)$.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Definitions 5–6, p.11

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_uncovered
import Definitions.Def_PctDistortion_abcValue

set_option autoImplicit false

namespace PctDistortion

/-- The set `ABC(G)` of **ABC-maximal lotteries** on `G`: Alice's equilibrium strategies of the
ABC game supported on the uncovered set, i.e. the `a` with `supp(a) ⊆ U(G)` for which `(a, b)`
is a mixed Nash equilibrium of `G^ABC_G` for some `b`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 5, p.11: "ABC(G) = {a ∈ ∆V | supp(a) ⊆ U(G) and (a, b) is a Nash equilibrium of
G^ABC_G for some b ∈ ∆V}."

**Formalization Note.** `BlottoLP.Flow.IsNashEq` requires both `a` and `b` to be mixed
strategies (points of the simplex), so `a ∈ ∆V` is part of the condition. -/
def abcMaximal {W : Type} [Fintype W] (G : Digraph W) : Set (W → ℝ) :=
  {a | (∀ w, 0 < a w → w ∈ uncovered G) ∧ ∃ b, BlottoLP.Flow.IsNashEq (abcPayoff G) a b}

/-- The **ABCα-maximal lotteries** `ABCα(E) = ABC(G^α_E)` of an election.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 6, p.11: "the ABCα-maximal lotteries of E, denoted by ABCα(E), are the ABC-maximal
lotteries of the digraph Gα_E, i.e., ABCα(E) = ABC(Gα_E). We refer to the weighted randomized
tournament rule returning an arbitrary lottery from ABCα(E) as ABCα-Maximal Lotteries." -/
def abcAlphaMaximal {V C : Type} [Fintype V] [Fintype C] (α : ℝ) (E : Election V C) :
    Set (C → ℝ) :=
  abcMaximal (alphaMajority α E)

end PctDistortion


