-- Prove2me | Definitions.Def_TwoSidedMatching_Statics_Supplement_Scale
-- name    : TwoSidedMatching_Statics_Supplement_Scale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:03:22.081931+00:00
-- url     : https://prove2.me/theorems/89b44ef6-ec16-4fb4-b237-7f89e358b23b
-- title:
--   Online Appendix pp. 6–7 — scale families, general support endpoints and virtual-surplus thresholds
-- statement:
--   A distribution is a probability law on the real line with a measurable nonnegative density, positive in its open interval support. Either support endpoint may be infinite, and endpoint densities may vanish. The CDF is the law's CDF; quantiles at probabilities strictly between zero and one are real inverse CDFs, while endpoint quantiles take their actual extended-real support values. A market is an independent buyer/seller pair. Regularity means weakly increasing virtual buyer value and seller cost in their open supports.
--
--   For positive rates $\lambda^d,\lambda^s$ and horizon $T>0$, put $L=\min\{\lambda^dT,\lambda^sT\}$. Define
--
--   $$\mu^*=\sup\bigl(\{0\}\cup\{\mu\in(0,L):V^d(\bar F^{d,-1}(\mu/(\lambda^dT)))-V^s(F^{s,-1}(\mu/(\lambda^sT)))\ge0\}\bigr).$$
--
--   All virtual-surplus tests use interior fractions, hence finite quantiles with positive density. Prices are the corresponding extended-real quantiles. The fluid value is independently the extended-real supremum of the finite objectives of (D), over all measurable, nonnegative, pointwise clearing price paths with interval-integrable revenues. No infinity subtraction occurs in a path objective.
--
--   In a scale family $F_\theta(\theta x)=F_1(x)$, the physical support moves with every $\theta>0$, and the other side's entire distribution remains fixed. Buyer IGFR reuses the published general failure-rate predicate. The seller ratio $cf(c)/F(c)$ is compared only where $F(c)>0$.
--
--   This interface retains the unbounded examples named on Online Appendix p. 7 without imposing continuity or positive endpoint densities from an imported bundle. **Formalization Note** Explicit endpoint quantiles and the interior supremum with zero are limiting conventions, not default values from a real infimum on an unbounded or empty set. Theorem 5 includes existence of a representation of each regular published Environment with nonnegative seller support and agreement of all four objects. Ordinary finite quantities are included by coercion into the extended reals.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text pp. 8–16, (1)–(2), (D); Online Appendix pp. 6–7, Theorem 5; Supplemental Note pp. 17–19, proof of Theorem 5

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid
import Definitions.Def_LariviereIGFR_Char_Setting

open MeasureTheory ProbabilityTheory

namespace TwoSidedMatching.Statics.Supplement

/-- The source's continuous distribution, with possibly infinite support endpoints. The law and density are primitive, not an optimization result.
The density need only be positive in the open support, and may vanish at endpoints. -/
structure ScaleDistribution where
  lo : EReal
  hi : EReal
  law : Measure ℝ
  pdf : ℝ → ℝ
  lo_lt_hi : lo < hi
  probability : IsProbabilityMeasure law
  measurable_pdf : Measurable pdf
  nonneg : ∀ x, 0 ≤ pdf x
  density : law = volume.withDensity (fun x => ENNReal.ofReal (pdf x))
  support : ∀ x : ℝ, (0 < cdf law x ∧ cdf law x < 1) ↔ lo < (x : EReal) ∧ (x : EReal) < hi
  positive : ∀ x : ℝ, lo < (x : EReal) → (x : EReal) < hi → 0 < pdf x

noncomputable def scaleCDF (D : ScaleDistribution) (x : ℝ) : ℝ := cdf D.law x
noncomputable def scaleSurvival (D : ScaleDistribution) (x : ℝ) : ℝ := 1 - scaleCDF D x

/-- Real inverse CDF, read only at interior quantiles. The set is nonempty
and bounded below for 0<q<1. Infinite support endpoints are handled separately. -/
noncomputable def scaleQuantile (D : ScaleDistribution) (q : ℝ) : ℝ :=
  sInf {x : ℝ | q ≤ scaleCDF D x}

/-- The inverse survival with explicit extended-real endpoints. -/
noncomputable def scaleBuyerQuantile (D : ScaleDistribution) (q : ℝ) : EReal :=
  if q ≤ 0 then D.hi else if 1 ≤ q then D.lo else (scaleQuantile D (1 - q) : EReal)

/-- The inverse CDF with explicit extended-real endpoints. -/
noncomputable def scaleSellerQuantile (D : ScaleDistribution) (q : ℝ) : EReal :=
  if q ≤ 0 then D.lo else if 1 ≤ q then D.hi else (scaleQuantile D q : EReal)

noncomputable def scaleVirtualB (D : ScaleDistribution) (x : ℝ) : ℝ :=
  x - scaleSurvival D x / D.pdf x
noncomputable def scaleVirtualS (D : ScaleDistribution) (x : ℝ) : ℝ :=
  x + scaleCDF D x / D.pdf x

structure ScaleMarket where
  buyer : ScaleDistribution
  seller : ScaleDistribution

def ScaleMarket.Regular (M : ScaleMarket) : Prop :=
  MonotoneOn (scaleVirtualB M.buyer) {x | M.buyer.lo < (x : EReal) ∧ (x : EReal) < M.buyer.hi} ∧
  MonotoneOn (scaleVirtualS M.seller) {x | M.seller.lo < (x : EReal) ∧ (x : EReal) < M.seller.hi}

/-- Only interior volume fractions are used in the virtual-surplus test, so
both real quantiles are finite and their densities strictly positive. -/
noncomputable def scaleV (M : ScaleMarket) (lamD lamS T μ : ℝ) : ℝ :=
  scaleVirtualB M.buyer (scaleQuantile M.buyer (1 - μ / (lamD * T))) -
    scaleVirtualS M.seller (scaleQuantile M.seller (μ / (lamS * T)))

noncomputable def scaleMu (M : ScaleMarket) (lamD lamS T : ℝ) : ℝ :=
  sSup ({0} ∪ {μ | μ ∈ Set.Ioo 0 (min (lamD * T) (lamS * T)) ∧
    0 ≤ scaleV M lamD lamS T μ})
noncomputable def scaleP (M : ScaleMarket) (lamD lamS T : ℝ) : EReal :=
  scaleBuyerQuantile M.buyer (scaleMu M lamD lamS T / (lamD * T))
noncomputable def scaleW (M : ScaleMarket) (lamD lamS T : ℝ) : EReal :=
  scaleSellerQuantile M.seller (scaleMu M lamD lamS T / (lamS * T))

def ScaleFeasible (M : ScaleMarket) (lamD lamS T : ℝ) (π : ℝ → ℝ × ℝ) : Prop :=
  Measurable π ∧
  (∀ t ∈ Set.Icc 0 T, 0 ≤ (π t).1 ∧ 0 ≤ (π t).2 ∧
    lamD * scaleSurvival M.buyer (π t).1 = lamS * scaleCDF M.seller (π t).2) ∧
  IntervalIntegrable (fun t => lamD * (π t).1 * scaleSurvival M.buyer (π t).1) volume 0 T ∧
  IntervalIntegrable (fun t => lamS * (π t).2 * scaleCDF M.seller (π t).2) volume 0 T

noncomputable def scaleObjective (M : ScaleMarket) (lamD lamS T : ℝ)
    (π : ℝ → ℝ × ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, lamD * (π t).1 * scaleSurvival M.buyer (π t).1) -
    (∫ t in (0 : ℝ)..T, lamS * (π t).2 * scaleCDF M.seller (π t).2)

/-- An extended-real supremum over the original nonnegative price paths in (D).
No infinity arithmetic occurs in the individual path objectives. -/
noncomputable def scaleValue (M : ScaleMarket) (lamD lamS T : ℝ) : EReal :=
  sSup {z | ∃ π, ScaleFeasible M lamD lamS T π ∧
    z = (scaleObjective M lamD lamS T π : EReal)}

/-- Use the published general IGFR notion, with the source's supported density.
No right-derivative or extra regular-density assumption is bundled in. -/
def BuyerIGFR (D : ScaleDistribution) : Prop :=
  LariviereIGFR.Char.IsIGFR D.law
    (fun x => if D.lo ≤ (x : EReal) ∧ (x : EReal) ≤ D.hi then D.pdf x else 0)

def SellerDGRFR (D : ScaleDistribution) : Prop :=
  AntitoneOn (fun c => c * D.pdf c / scaleCDF D c)
    {c | D.lo ≤ (c : EReal) ∧ (c : EReal) ≤ D.hi ∧ 0 < scaleCDF D c}

/-- The physical support moves; the CDF identity extends to every real x because
both sides vanish below zero and equal one above a finite upper endpoint. -/
def BuyerScaleFamily (M : ℝ → ScaleMarket) : Prop :=
  ∀ θ : ℝ, 0 < θ →
    (M θ).buyer.lo = 0 ∧ (M θ).buyer.hi = (θ : EReal) * (M 1).buyer.hi ∧
    (∀ v : ℝ, scaleCDF (M θ).buyer (θ * v) = scaleCDF (M 1).buyer v) ∧
    (M θ).seller = (M 1).seller

def SellerScaleFamily (M : ℝ → ScaleMarket) : Prop :=
  ∀ θ : ℝ, 0 < θ →
    (M θ).seller.lo = 0 ∧ (M θ).seller.hi = (θ : EReal) * (M 1).seller.hi ∧
    (∀ c : ℝ, scaleCDF (M θ).seller (θ * c) = scaleCDF (M 1).seller c) ∧
    (M θ).buyer = (M 1).buyer

/-- Agreement of the minimal interface with a published Environment. This is a
representation relation; existence and equality of the four objects are conclusions. -/
def RepresentsEnvironment (M : ScaleMarket) (E : TwoSidedMatching.Statics.Environment) : Prop :=
  M.buyer.lo = (E.loB : EReal) ∧ M.buyer.hi = (E.hiB : EReal) ∧
  M.seller.lo = (E.loS : EReal) ∧ M.seller.hi = (E.hiS : EReal) ∧
  (∀ x, scaleCDF M.buyer x = TwoSidedMatching.Statics.Fd E x) ∧
  (∀ x, scaleCDF M.seller x = TwoSidedMatching.Statics.Fs E x) ∧
  (∀ x ∈ Set.Icc E.loB E.hiB, M.buyer.pdf x = E.fB x) ∧
  (∀ x ∈ Set.Icc E.loS E.hiS, M.seller.pdf x = E.fS x)

end TwoSidedMatching.Statics.Supplement


