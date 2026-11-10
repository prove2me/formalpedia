-- Prove2me | Definitions.Def_IntegerSumAmplification_Main_OrderStatistic
-- name    : IntegerSumAmplification_Main_OrderStatistic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:03:16.976559+00:00
-- url     : https://prove2.me/theorems/f8d7cc69-0fd6-4457-be41-4ab33b43b7fc
-- title:
--   Order statistics and the empirical quantile decoder
-- statement:
--   The $j$-th order statistic of a tuple is entry $j$ of its increasing ordering, retaining all repetitions. The implementation uses a sorted list and zero-based access at $j-1$; invalid ranks have a default value, but every theorem requires or concludes a valid rank. For $L$ restrictions and a level $\widehat\psi$, set
--   $$j=\lceil L\widehat\psi\rceil,\qquad H_j(x)=\operatorname{ord}_j(h_{\rho_1}(x),\ldots,h_{\rho_L}(x)).$$
--   The decoder experiment has law $(\operatorname{Law}(R))^L\times D$, so all restrictions are independent of each other and of the fresh input-label pair. The natural ceiling agrees with the integer ceiling on the positive levels used in Lemma 6.5. This defines the mathematical order statistic, not a gate-count claim about the sorting implementation.
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Lemma 6.5, printed pp. 15–16 / PDF pp. 18–19; Lemma 6.6, printed p. 17 / PDF p. 20. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_IntegerSumAmplification_Main_Residuals
open MeasureTheory

namespace IntegerSumAmplification.Main

def orderStatistic {α : Type*} [LinearOrder α] [Inhabited α] {L : ℕ}
    (a : Fin L → α) (j : ℕ) : α :=
  ((List.ofFn a).mergeSort (fun x y => x ≤ y)).getD (j - 1) default

noncomputable def quantileRank (L : ℕ) (level : ℝ) : ℕ := ⌈(L : ℝ) * level⌉₊

def quantileDecoder {n m k L : ℕ} (A : (Fin k → Bits n) → ℤ)
    (ρ : Fin L → Restriction n m k) (j : ℕ) (x : Bits n) : ℤ :=
  orderStatistic (fun l => residual A (ρ l) x) j

noncomputable def decodingLaw {n m : ℕ} (D : Measure (LabeledInput n m)) (k L : ℕ) :
    Measure ((Fin L → Restriction n m k) × LabeledInput n m) :=
  (productLaw (restrictionLaw D k) L).prod D

end IntegerSumAmplification.Main


