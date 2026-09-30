-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_SectionJetEvaluation
-- name    : WeierstrassEllipticZeta_SectionJetEvaluation
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T07:18:06.441258+00:00
-- url     : https://prove2.me/theorems/a07c66eb-ad8f-4647-838d-365fc22dab8e
-- title:
--   Simultaneous restriction of elliptic chart sections to finite jets
-- statement:
--   For a finite family J of point-supported chart ideals containing the elliptic cubic, define the natural linear map from the cubic chart coordinate ring to the product of polynomial quotients R/J_i. Restrict it to the span of normalized sections of bidegree (m,n) to obtain sectionEvaluation J m n. Define totalDimension J as the sum of the quotient dimensions.
--
--   These are the actual quotient restriction maps. They retain nonreduced structure and are not merely evaluations of scalar values at the support points. The definition adds no geometric hypothesis or rank assumption.
-- source:
--   Chinese remainder interpolation: Stacks Project, Lemma 10.15.4, https://stacks.math.columbia.edu/tag/00DT. The degree-minus-one representative input is the proved affine counterpart of Chiantini and Migliore, Almost maximal growth of the Hilbert function, Lemma 4.11, p.20, https://academicweb.nd.edu/~jmiglior/CM2.pdf. Apply it to the intersection of the pairwise comaximal point-supported ideals, then apply the proved bihomogeneous lifting theorem to realize all quotient classes simultaneously by one chart section. For total quotient dimension D, both section degrees >= D-1 suffice, and the restriction map has rank D, including nonreduced structure. The A.1 reduction retains the original locus, ideals, local lengths and constant; only the sum of stable truncated ranks is replaced by the equal simultaneous section-evaluation rank. No bound on D in terms of the original bidegree, geometric witness selection or uniform A.1 rank estimate is claimed proved.

import Definitions.Def_WeierstrassEllipticZeta_FiniteJetChartIdeals
import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Mathlib.LinearAlgebra.Pi

noncomputable section
namespace WeierstrassEllipticZeta

/-- Simultaneous restriction from the cubic coordinate ring to the local quotients. -/
def FiniteJetChartIdealData.chartEvaluation {L : PeriodPair} {ι : Type}
    (J : FiniteJetChartIdealData L ι) :
    FirstCubicCoordinateRing L →ₗ[ℂ] (∀ i, MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) :=
  LinearMap.pi fun i => (Ideal.Quotient.factorₐ ℂ
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (J.cubic_mem i)))).toLinearMap

/-- Evaluate a single bihomogeneous section simultaneously in every local quotient. -/
def FiniteJetChartIdealData.sectionEvaluation {L : PeriodPair} {ι : Type}
    (J : FiniteJetChartIdealData L ι) (m n : ℕ) :
    firstChartSectionSpace L m n →ₗ[ℂ] (∀ i, MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) :=
  J.chartEvaluation.comp (firstChartSectionSpace L m n).subtype

/-- Total dimension of the family of local chart quotients. -/
def FiniteJetChartIdealData.totalDimension {L : PeriodPair} {ι : Type} [Fintype ι]
    (J : FiniteJetChartIdealData L ι) : ℕ :=
  ∑ i, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i)

end WeierstrassEllipticZeta


