-- Prove2me | Definitions.Def_IntegerSumAmplification_Main_Residuals
-- name    : IntegerSumAmplification_Main_Residuals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:02:39.867889+00:00
-- url     : https://prove2.me/theorems/0102c44d-71dc-4828-b17e-e46a01f10e04
-- title:
--   Global residuals and random residual restrictions
-- statement:
--   Let $U=\{0,1\}^n$, let $D$ be a joint law on $U\times\{0,\ldots,m-1\}$, and let $A:U^k\to\mathbb Z$. For independent $(X_i,Y_i)\sim D$, set
--   $$E=A(X_1,\ldots,X_k)-\sum_iY_i,\quad p^-=\Pr(E<0),\quad p^+=\Pr(E\le0),\quad\psi=(p^-+p^+)/2.$$
--   A restriction chooses $J$ uniformly from the $k$ positions and independent labeled contexts, and replaces position $J$ by the test input. For $\rho=(j,(x_i,y_i)_i)$ its residual is
--   $$h_\rho(x)=A(x_1,\ldots,x_{j-1},x,x_{j+1},\ldots,x_k)-\sum_{i\ne j}y_i.$$
--   Finally $b^-(x,y)=\Pr_R[h_R(x)<y]$ and $b^+(x,y)=\Pr_R[h_R(x)\le y]$. All subtraction is signed integer subtraction. The stored context includes an unused sample at $j$, whose value has no effect. For $k>0$ the restriction law is normalized counting measure on the positions times $D^k$; at $k=0$ this helper gives the zero measure and is not used by the results. Labels need not be deterministic functions of inputs.
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Definitions 6.1–6.2, printed p. 13 / PDF p. 16; standing assumptions printed p. 12 / PDF p. 15. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_IntegerSumAmplification_Main_Words
import Definitions.Def_IntegerSumAmplification_Main_CoordinateProjections
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IntegerSumAmplification.Main

abbrev LabeledInput (n m : ℕ) := Bits n × Fin m

abbrev Restriction (n m k : ℕ) := Fin k × (Fin k → LabeledInput n m)

def globalResidual {n m k : ℕ} (A : (Fin k → Bits n) → ℤ)
    (z : Fin k → LabeledInput n m) : ℤ :=
  A (fun i => (z i).1) - ∑ i, ((z i).2.val : ℤ)

noncomputable def pMinus {n m k : ℕ} (D : Measure (LabeledInput n m))
    (A : (Fin k → Bits n) → ℤ) : ℝ :=
  (productLaw D k).real {z | globalResidual A z < 0}

noncomputable def pPlus {n m k : ℕ} (D : Measure (LabeledInput n m))
    (A : (Fin k → Bits n) → ℤ) : ℝ :=
  (productLaw D k).real {z | globalResidual A z ≤ 0}

noncomputable def targetLevel {n m k : ℕ} (D : Measure (LabeledInput n m))
    (A : (Fin k → Bits n) → ℤ) : ℝ := (pMinus D A + pPlus D A) / 2

noncomputable def restrictionLaw {n m : ℕ} (D : Measure (LabeledInput n m))
    (k : ℕ) : Measure (Restriction n m k) :=
  (((k : ℝ≥0∞)⁻¹ • Measure.count) : Measure (Fin k)).prod (productLaw D k)

def residual {n m k : ℕ} (A : (Fin k → Bits n) → ℤ)
    (ρ : Restriction n m k) (x : Bits n) : ℤ :=
  A (Function.update (fun i => (ρ.2 i).1) ρ.1 x) -
    ∑ i ∈ Finset.univ.erase ρ.1, ((ρ.2 i).2.val : ℤ)

noncomputable def bMinus {n m k : ℕ} (D : Measure (LabeledInput n m))
    (A : (Fin k → Bits n) → ℤ) (z : LabeledInput n m) : ℝ :=
  (restrictionLaw D k).real {ρ | residual A ρ z.1 < (z.2.val : ℤ)}

noncomputable def bPlus {n m k : ℕ} (D : Measure (LabeledInput n m))
    (A : (Fin k → Bits n) → ℤ) (z : LabeledInput n m) : ℝ :=
  (restrictionLaw D k).real {ρ | residual A ρ z.1 ≤ (z.2.val : ℤ)}

end IntegerSumAmplification.Main


