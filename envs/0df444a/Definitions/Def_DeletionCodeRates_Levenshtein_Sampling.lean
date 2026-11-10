-- Prove2me | Definitions.Def_DeletionCodeRates_Levenshtein_Sampling
-- name    : DeletionCodeRates_Levenshtein_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:19:43.865437+00:00
-- url     : https://prove2.me/theorems/52105ed6-c2a8-4c04-bd69-d7a99ca76ffc
-- title:
--   The common-witness probability of $L+1$ independent samples (setting of Lemma 8)
-- statement:
--   Let $P$ be a distribution (`PMF`) on a finite set $X$, and let $W(\boldsymbol c)$ be a set of witnesses (elements of a type `Wit`) for each $\boldsymbol c\in X$. For $k$ independent samples $\boldsymbol C_1,\dots,\boldsymbol C_k$ from $P$,
--   $$\Pr\Big[\textstyle\bigcap_{i=1}^{k}W(\boldsymbol C_i)\ne\emptyset\Big]=\sum_{f:[k]\to X,\ \bigcap_i W(f_i)\ne\emptyset}\ \prod_{i=1}^{k}P(f_i),$$
--   the probability under the product law that the samples have a common witness (`commonWitnessProb P W k`). Lemma 8 uses $k=L+1$.
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), §3.2, Lemma 8, (17), p. 9 (PDF 11)

import Mathlib

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-! # The abstract setting of the common-witness sampling lemma (Lemma 8)

Kiah, Wei, Zeng, arXiv:2609.21395 (PDF sha256 bc43cfa2…), §3.2, Lemma 8, printed p. 9 (PDF 11).
A distribution `P` on a finite set `X`, and a set of witnesses `W c` (in a witness type `Wit`)
for each `c ∈ X`. -/

open Classical in
/-- The probability `Pr[⋂_{i=1}^{k} W(C_i) ≠ ∅]` that `k` independent samples `C_1, …, C_k`
drawn from the distribution `P` on the finite set `X` have a common witness (the left side of
(17), with `k = L + 1`): the sum, over all sample tuples `f : Fin k → X`, of the product
probability `∏ᵢ P(fᵢ)` of the tuple, restricted to the tuples whose witness sets intersect. -/
noncomputable def commonWitnessProb {X Wit : Type*} [Fintype X] (P : PMF X) (W : X → Set Wit)
    (k : ℕ) : ℝ :=
  ∑ f : Fin k → X, if (∃ w : Wit, ∀ i, w ∈ W (f i)) then ∏ i, (P (f i)).toReal else 0

end DeletionCodeRates.Levenshtein


