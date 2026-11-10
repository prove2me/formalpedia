-- Prove2me | Definitions.Def_DeletionCodeRates_Levenshtein_RateFunctions
-- name    : DeletionCodeRates_Levenshtein_RateFunctions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:19:48.184734+00:00
-- url     : https://prove2.me/theorems/aab84c66-7032-4542-8da0-0da324bd61db
-- title:
--   Levenshtein's rate $R_{\mathrm{Lev}}$, $\lambda^{(1)}_{\mathrm{del}}$, the region $\mathcal D_{\mathrm{del}}$ and the rate expression $R^{(1)}_{\mathrm{del}}(\delta)$ of (2)
-- statement:
--   Logarithms are base $2$, and $h_2(x)=-x\log_2x-(1-x)\log_2(1-x)$ with $0\log0=0$ is the published `WildeQIT.binaryEntropy`.
--
--   * (1): $R_{\mathrm{Lev}}(\delta)=1+\delta-2h_2(\delta)$ (`RLev`).
--   * $\lambda^{(1)}_{\mathrm{del}}(x,y)=1+\dfrac{y^2(1+3x)}{1-x}$ (`lambdaDel`).
--   * (30): $\mathcal D_{\mathrm{del}}=\{(x,y)\in\mathbb R^2_{>0}: x(1+y)<1\}$ (`Ddel`).
--   * (2): $R^{(1)}_{\mathrm{del}}(\delta)=\sup_{(x,y)\in\mathcal D_{\mathrm{del}}}\{2\log_2(1+y)-(1-\delta)\log_2\lambda^{(1)}_{\mathrm{del}}(x,y)+2\delta\log_2x\}$ (`RDel`, with objective `rdelObjective δ x y`).
--
--   **Formalization Note.** `RDel δ` is the real `sSup` of the image of $\mathcal D_{\mathrm{del}}$. For $0<\delta<1/2$ the image is nonempty and bounded above: $\lambda^{(1)}_{\mathrm{del}}\ge1+y^2$ and $x<1/(1+y)$ give an objective below $(1-\delta)\log_2\frac{(1+y)^2}{1+y^2}\le1-\delta$. So the supremum is the paper's, not a junk value.
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), (1) p. 1 (PDF 3); Theorem 1 and (2), p. 3 (PDF 5); (30), p. 15 (PDF 17)

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-! # Levenshtein's rate expression and the rate expression `R^{(1)}_del` of Theorem 1

Kiah, Wei, Zeng, arXiv:2609.21395 (PDF sha256 bc43cfa2…), (1) p. 1 (PDF 3), Theorem 1 and (2)
p. 3 (PDF 5), (30) p. 15 (PDF 17). Logarithms are base 2 (`Real.logb 2`); the binary entropy
`h₂` is `WildeQIT.binaryEntropy` (base 2, `0 log 0 = 0`). -/

/-- Levenshtein's rate expression (1): `R_Lev(δ) = 1 + δ - 2 h₂(δ)`. -/
noncomputable def RLev (δ : ℝ) : ℝ :=
  1 + δ - 2 * WildeQIT.binaryEntropy δ

/-- `λ^{(1)}_del(x, y) = 1 + y² (1 + 3x) / (1 - x)` (p. 3). -/
noncomputable def lambdaDel (x y : ℝ) : ℝ :=
  1 + y ^ 2 * (1 + 3 * x) / (1 - x)

/-- The feasible region (30): `D_del = {(x, y) ∈ ℝ²_{>0} : x(1 + y) < 1}`. -/
def Ddel : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 * (1 + p.2) < 1}

/-- The objective of (2): `2 log₂(1 + y) - (1 - δ) log₂ λ^{(1)}_del(x, y) + 2δ log₂ x`. -/
noncomputable def rdelObjective (δ x y : ℝ) : ℝ :=
  2 * Real.logb 2 (1 + y) - (1 - δ) * Real.logb 2 (lambdaDel x y) + 2 * δ * Real.logb 2 x

/-- (2): `R^{(1)}_del(δ) = sup_{x, y > 0, x(1+y) < 1} { 2 log₂(1+y) - (1-δ) log₂ λ^{(1)}_del(x,y)
+ 2δ log₂ x }`, the real supremum of the objective over `D_del`. For `0 < δ < 1/2` the set is
nonempty and bounded above (by `1 - δ`), so the supremum is genuine. -/
noncomputable def RDel (δ : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => rdelObjective δ p.1 p.2) '' Ddel)

end DeletionCodeRates.Levenshtein


