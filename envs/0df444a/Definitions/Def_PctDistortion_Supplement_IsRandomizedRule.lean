-- Prove2me | Definitions.Def_PctDistortion_Supplement_IsRandomizedRule
-- name    : PctDistortion_Supplement_IsRandomizedRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:27:51.991198+00:00
-- url     : https://prove2.me/theorems/fb405746-91cc-46dd-bee7-5d3471cdb66b
-- title:
--   Randomized voting rules
-- statement:
--   A **randomized voting rule** $A$ assigns to every election $\mathcal E=(V,\mathcal C,\vec\succ)$, with a finite nonempty set of voters and a finite nonempty set of candidates, a **lottery** $A(\mathcal E)\in\Delta\mathcal C$: nonnegative weights on the candidates summing to $1$.
--
--   No further condition (neutrality, anonymity) is imposed. This is the class of rules in the lower bound of Theorem 7.
--
--   **Formalization Note** `VotingRule` is the type of maps from elections (over all finite nonempty voter and candidate types) to weight functions on candidates; `IsRandomizedRule A` says every output is a point of the simplex (`BlottoLP.Flow.IsMixed`).
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §2, p.8 (lotteries and randomized voting rules)

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- The type of maps that assign to every election (every finite nonempty voter type `V` and
finite nonempty candidate type `C`) a weight function on its candidates. -/
abbrev VotingRule : Type 1 :=
  ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C], Election V C → C → ℝ

/-- `A` is a **randomized voting rule**: it maps every election `E = (V, C, ≻⃗)` to a lottery
`A(E) ∈ ∆C` over its candidates (nonnegative weights summing to `1`).

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2, p.8 (lotteries `∆C` and randomized voting rules).

**Formalization Note.** A lottery is `BlottoLP.Flow.IsMixed` (a point of the probability simplex).
No other condition (neutrality, anonymity) is imposed. -/
def IsRandomizedRule (A : VotingRule) : Prop :=
  ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C),
    BlottoLP.Flow.IsMixed (A V C E)

end PctDistortion.Supplement


