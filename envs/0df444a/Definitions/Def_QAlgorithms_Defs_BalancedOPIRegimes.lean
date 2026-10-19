-- Prove2me | Definitions.Def_QAlgorithms_Defs_BalancedOPIRegimes
-- name    : QAlgorithms_Defs_BalancedOPIRegimes
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:32:15.137731+00:00
-- url     : https://prove2.me/theorems/51383a76-42a8-49ed-82b0-6621c2243765
-- title:
--   BalancedOPIRegimes
-- statement:
--   BalancedOPIRegimes
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\BalancedOPIRegimes.lean

import Definitions.Def_QAlgorithms_Defs_OPIUniformity
noncomputable section

attribute [local instance] Classical.propDecidable

open Filter

namespace QAlgorithms.OPI

/-- Arbitrary unequal near-half densities; 2607.14650 pp.4–5,36–37.
beta is a nonnegative vanishing bound, not oracle-accessible exact density. -/
def NearHalfPromise {F : Type*} [Fintype F] {n : ℕ}
    (_hn : 0 < n) (_hF : 0 < Fintype.card F) (sets : Fin n → Finset F)
    (beta : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ beta k) ∧ Tendsto beta atTop (nhds 0) ∧
    ∀ i, |((sets i).card : ℝ)/Fintype.card F-1/2| ≤ beta n

/-- Growing public balanced-algorithm regime with uniform fixed margins;
2607.14650 pp.4–5,36–37, Remark 6.2. The partial branch is evaluated only
for R≤3/4, so it does not use the reciprocal at R=1. -/
def BalancedAlgorithmicRegime (n k p e : ℕ → ℕ) (s : ℝ) : Prop :=
  Tendsto n atTop atTop ∧ Tendsto p atTop atTop ∧
  (∀ j, (p j).Prime ∧ 1 ≤ e j ∧ 0 < n j ∧ 0 < k j ∧
    n j ≤ 2*k j ∧ k j ≤ n j ∧ n j ≤ p j^e j) ∧
  ∃ C : ℝ, 0 < C ∧ ∃ degree : ℕ, ∃ margin : ℝ, 0 < margin ∧
    ∃ j0 : ℕ, ∀ j ≥ j0,
      Real.logb 2 ((p j^e j : ℕ) : ℝ) ≤ C*(n j : ℝ)^degree ∧
      let R := (k j : ℝ)/n j
      if s = 1 then 3/4+margin ≤ R else
        R ≤ 3/4 ∧ 1/2 < s ∧ s < 1 ∧
          1-(Real.sqrt (s/2)+Real.sqrt ((1-s)/2))^4+margin ≤ R ∧
          binEntropy2 R+R*Real.logb 2
            (3*Real.rpow ((2*s-1)/Real.sqrt 3) ((1-R)⁻¹)) ≤ -margin

example {F : Type*} [Fintype F] {n : ℕ} (hn : 0 < n)
    (hF : 0 < Fintype.card F) (sets : Fin n → Finset F) (beta : ℕ → ℝ)
    (h : NearHalfPromise hn hF sets beta) : ∀ j, 0 ≤ beta j := h.1

end QAlgorithms.OPI


