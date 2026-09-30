-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_CappedChartJets
-- name    : WeierstrassEllipticZeta_CappedChartJets
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T23:42:01.683797+00:00
-- url     : https://prove2.me/theorems/709220df-0281-4fc6-a590-bf6b6760cb4f
-- title:
--   Chart jet budgets with an explicit derivative-order cap
-- statement:
--   CappedChartJetBudget is the previous finite chart-jet budget with a supplied natural-number cap N. At each of the three adjacent stages i*T and (i+1)*T, replace the derivative order t by min(t,N). Retain the same chart, available point in the prescribed finite set, minimal-prime tests, and exact localized quotient length bound e.
--
--   The definition does not assert that a proposed cap is valid. Validity means equality of each original jet ideal with its capped ideal; this is an explicit hypothesis in the remaining geometric theorem and is supplied by the separately proved uniform-cap theorem. No prime existence or multiplicity estimate is built into this definition.
-- source:
--   Supporting Noetherian specialization lemma for the A.1 formalization. Mathlib, RingTheory/Noetherian/Defs.lean, monotone_stabilizes_iff_noetherian: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Defs.html#monotone_stabilizes_iff_noetherian. Universal coefficient variables make ideal stabilization uniform over all polynomials of bounded degree; specialization preserves exact ideal membership and yields J_T=J_min(T,B(m+2*n)) in both charts. B is positive and monotone, but no numerical value or growth bound is proved. Philippon (1986), Bull. Soc. Math. France 114, 355-383, section 5, pp. 380-382, https://www.numdam.org/item/10.24033/bsmf.2060.pdf, provides the broader derivative/translation-ideal framework. This is not that paper's quantitative zero estimate. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X. The uniform A.1 degree budget and global geometric selection remain Open.

import Definitions.Def_WeierstrassEllipticZeta_FiniteChartJets

noncomputable section
namespace WeierstrassEllipticZeta

/-- The finite jet budget with every derivative order truncated at a supplied cap.
Correctness of a cap is a separate theorem, never an assumption hidden here. -/
structure CappedChartJetBudget (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T e : ℕ) (Z : Finset ℂ) where
  chart : Fin 2
  z : ℂ
  z_mem : z ∈ Z
  chart_ne : S (extensionChartDenominator chart) z ≠ 0
  length_le : ∀ (i : Fin 3) (p : Ideal (MvPolynomial (Fin 4) ℂ)) [p.IsPrime],
    p ≤ RingHom.ker (MvPolynomial.eval (extensionChartCoordinates S chart z)) →
    p ∈ (extensionChartJetIdeal L Q chart (min (i.val * T) N)).minimalPrimes →
    p ∈ (extensionChartJetIdeal L Q chart (min ((i.val + 1) * T) N)).minimalPrimes →
    Module.length (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ (extensionChartJetIdeal L Q chart (min (i.val * T) N)).map
        (algebraMap (MvPolynomial (Fin 4) ℂ) (Localization.AtPrime p))) ≤ (e : ℕ∞)

end WeierstrassEllipticZeta


