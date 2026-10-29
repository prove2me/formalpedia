-- Prove2me | Definitions.Def_PutermanMDP_Sensitive_Coefficients
-- name    : PutermanMDP_Sensitive_Coefficients
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:12.244169+00:00
-- url     : https://prove2.me/theorems/de99eefe-4402-4ac3-871f-1cd722fa2d6e
-- title:
--   Laurent coefficients and rowwise lexicographic order
-- statement:
--   For a deterministic stationary rule $d$, let $P_d$ be its transition matrix and $r_d$ its reward vector. Define the Cesàro limiting matrix and deviation matrix by
--   $$P_d^*=\lim_{N\to\infty}\frac1{N+1}\sum_{j=0}^N P_d^j,\qquad H_d=(I-P_d+P_d^*)^{-1}(I-P_d^*).$$
--   The chapter uses the interest parameter $\rho=(1-\lambda)/\lambda$ and coefficients
--   $$y_{-1}^{d^\infty}=P_d^*r_d,\qquad y_k^{d^\infty}=(-1)^kH_d^{k+1}r_d\quad(k\ge0).$$
--   The array $Y_n$ consists of columns $-1,0,\ldots,n$; $Y$ contains all columns. An array is lexicographically at least another when in each row the two rows agree throughout, or their first differing entry is larger. This is a rowwise partial order, not entrywise dominance and not a single flattened lexicographic order.
--
--   These objects supply the algebraic formulation of the sensitivity hierarchy.
--
--   **Formalization Note** Coefficients have integer indices; indices below $-1$ are unused. The displayed coefficient formula, the definition $y_0=h$, and Appendix A.14 determine the encoding; the double counting of $h$ in the printed Eq. (10.1.7) is documented in FINDINGS. Cesàro limits cover periodic chains. The model ensures existence of these limits and nonsingularity of the matrix being inverted. The Cesàro and deviation matrices reuse the published Blackwell definitions; the latter uses the equivalent expression $(I-P_d+P_d^*)^{-1}-P_d^*$ from the proof of Theorem A.7 on printed p. 597 (PDF 613).
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 497 (PDF 513), coefficient formula following (10.1.7); pp. 501, 503–505 (PDF 517, 519–521); Eq. (8.2.2), p. 338 (PDF 354); Eq. (A.14), p. 597 (PDF 613); https://doi.org/10.1002/9780470316887

import Mathlib
import Definitions.Def_PutermanMDP_Sensitive_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix

namespace PutermanMDP.Sensitive

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- Appendix A.4: reuse the published Cesàro limiting matrix, including periodic chains. -/
noncomputable abbrev limitingMatrix (P : Matrix S S ℝ) : Matrix S S ℝ :=
  BlackwellDiscreteDP.NearOne.limitMatrix P

/-- Appendix A.5, Theorem A.7: the published deviation matrix.
On stochastic matrices its formula (I-P+P*)⁻¹-P* equals (A.14), as shown on p. 597. -/
noncomputable abbrev deviationMatrix (P : Matrix S S ℝ) : Matrix S S ℝ :=
  BlackwellDiscreteDP.NearOne.deviationMatrix P

/-- The book's y_{-1}=P* r and y_k=(-1)^k H^{k+1}r for k≥0.
The interest parameter is ρ=(1-λ)/λ, not 1-λ. Indices below -1 are unused. -/
noncomputable def coefficient {M : Model S A} (d : DecisionRule M) (k : ℤ) : S → ℝ :=
  if k = -1 then (limitingMatrix (policyMatrix d)).mulVec (rewardVector d)
  else (-1 : ℝ) ^ k.toNat •
    (deviationMatrix (policyMatrix d) ^ (k.toNat + 1)).mulVec (rewardVector d)

/-- Rowwise lexicographic comparison on columns -1,…,n. -/
def LexGEThrough (n : ℤ) (Y Z : ℤ → S → ℝ) : Prop :=
  ∀ s, (∀ k : ℤ, -1 ≤ k → k ≤ n → Y k s = Z k s) ∨
    ∃ k : ℤ, -1 ≤ k ∧ k ≤ n ∧ Z k s < Y k s ∧
      ∀ j : ℤ, -1 ≤ j → j < k → Y j s = Z j s

/-- Rowwise comparison on all columns -1,0,1,…; the all-equal case is allowed. -/
def LexGE (Y Z : ℤ → S → ℝ) : Prop :=
  ∀ s, (∀ k : ℤ, -1 ≤ k → Y k s = Z k s) ∨
    ∃ k : ℤ, -1 ≤ k ∧ Z k s < Y k s ∧
      ∀ j : ℤ, -1 ≤ j → j < k → Y j s = Z j s

end PutermanMDP.Sensitive


