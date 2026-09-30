-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ChartSelectionData
-- name    : WeierstrassEllipticZeta_ChartSelectionData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T20:08:35.397015+00:00
-- url     : https://prove2.me/theorems/2017e8fe-6e40-4fd8-a78c-65edc89bb9af
-- title:
--   Height and terminal-containment data for chart component selection
-- statement:
--   For fixed Weierstrass period data $L$, entire coordinates $S$, a polynomial $Q$, and natural numbers $T,e$, the structure `ChartSelectionMultiplicityData L S Q T e` records sufficient input for selecting a persistent component.
--
--   It chooses a chart $j\in\{0,1\}$, a point $z$ with nonzero chart denominator, and a base ideal $J$ of $A=\mathbb C[X_0,X_1,X_2,X_3]$. Write $\delta_j$ for the previously defined chart derivation, $Q_j$ for the chart normalization of $Q$, $v_j(z)$ for the chart orbit coordinates, and
--
--   $$P_r(J)=(\delta_j^k f:f\in J,\ 0\le k\le r),\qquad
--   \mathfrak q_z=\ker\bigl(A\xrightarrow{\operatorname{eval}_{v_j(z)}}\mathbb C\bigr).$$
--
--   The fields require $\operatorname{ht}(J)\ge2$, $Q_j\in J$, and $P_{3T}(J)\subseteq\mathfrak q_z$.
--
--   In addition, for every $i\in\{0,1,2\}$ and every prime $\mathfrak p\subseteq\mathfrak q_z$ minimal over both $P_{iT}(J)$ and $P_{(i+1)T}(J)$, the fields require
--
--   $$\operatorname{length}_{A_{\mathfrak p}}\bigl(A_{\mathfrak p}/P_{iT}(J)A_{\mathfrak p}\bigr)\le e.$$
--
--   No prime or stage is supplied as a witness in this structure. The three-step selection theorem constructs them from the height and terminal-containment hypotheses. The uniform bound covers whichever candidate the theorem selects. The earlier chart, polynomial normalization and derivative-ideal definitions are reused unchanged.
--
--   **Formalization Note.** These are explicit sufficient conditions for the preceding `ChartProlongationMultiplicityData`. No converse for arbitrary data of the previous type is asserted. Constructing the present data from the A.1 geometric hypotheses remains an Open theorem.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, p. 380: dimension-drop selection of a component common to adjacent derivative stages. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. The complete theorem gives an affine prime-height criterion: four increasing ideals, initial height at least two, all below a prime of height at most four, have a common minimal prime at adjacent stages. The chart reduction selects a stage among 0, U, 2U. Constructing the geometric height and terminal-containment data and proving the uniform total-length degree bound remain open. This is a sufficient route; no converse for arbitrary old chart data is asserted.

import Definitions.Def_WeierstrassEllipticZeta_ChartProlongationData
import Mathlib.RingTheory.Ideal.Height

noncomputable section

namespace WeierstrassEllipticZeta
open TranscendenceTheory

/-- Sufficient height and terminal-containment data for selecting a persistent
chart component among three consecutive derivative blocks. -/
structure ChartSelectionMultiplicityData (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (T e : ℕ) where
  chart : Fin 2
  z : ℂ
  chart_ne : S (extensionChartDenominator chart) z ≠ 0
  base : Ideal (MvPolynomial (Fin 4) ℂ)
  height_lower : (2 : ℕ∞) ≤ base.height
  normalized_mem : extensionChartNormalize chart Q ∈ base
  terminal : differentialProlongation (extensionChartDerivation L.g₂ L.g₃ chart)
    base (3 * T) ≤ RingHom.ker (MvPolynomial.eval (extensionChartCoordinates S chart z))
  length_le : ∀ (i : Fin 3) (p : Ideal (MvPolynomial (Fin 4) ℂ)) [p.IsPrime],
    p ≤ RingHom.ker (MvPolynomial.eval (extensionChartCoordinates S chart z)) →
    p ∈ (differentialProlongation (extensionChartDerivation L.g₂ L.g₃ chart)
      base (i.val * T)).minimalPrimes →
    p ∈ (differentialProlongation (extensionChartDerivation L.g₂ L.g₃ chart)
      base ((i.val + 1) * T)).minimalPrimes →
    Module.length (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ (differentialProlongation
        (extensionChartDerivation L.g₂ L.g₃ chart) base (i.val * T)).map
        (algebraMap (MvPolynomial (Fin 4) ℂ) (Localization.AtPrime p))) ≤ (e : ℕ∞)

end WeierstrassEllipticZeta


