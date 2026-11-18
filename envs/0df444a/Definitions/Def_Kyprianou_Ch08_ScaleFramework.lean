-- Prove2me | Definitions.Def_Kyprianou_Ch08_ScaleFramework
-- name    : Kyprianou_Ch08_ScaleFramework
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T07:14:23.096711+00:00
-- url     : https://prove2.me/theorems/5c07096f-1cc9-409b-8fc8-3bcbdc966eae
-- title:
--   Kyprianou Chapter 8: ScaleFramework
-- statement:
--   Complete non-strict q-scale and integrated Z-scale function predicates, rightmost root Phi, scale Stieltjes measure, analytic tilt and source-to-published scale bridge.
-- source:
--   Kyprianou (2006), first edition, Chapter 8, original physical pages 219-246; source SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_ProcessAndExponent
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08

/-- Corrected Theorem 8.1(i) candidate. Pure positive drift at q=0
has constant W(x)=1/d on x>=0; monotonicity is the general assertion.
The existence and uniqueness of W remain the theorem's conclusions.
The root predicate prevents a vacuous transform domain, while explicit
IntegrableOn prevents totalisation of a divergent real integral. -/
def IsQScale (ψ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  PhiIsLargestRoot ψ q ∧
  (∀ x : ℝ, x < 0 → W x = 0) ∧
  (∀ x : ℝ, 0 ≤ W x) ∧
  ContinuousOn W (Set.Ici (0 : ℝ)) ∧
  MonotoneOn W (Set.Ici (0 : ℝ)) ∧
  (∀ β : ℝ, 0 ≤ β → Phi ψ q < β →
    IntegrableOn (fun x : ℝ => Real.exp (-β * x) * W x)
      (Set.Ioi (0 : ℝ)) volume ∧
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) * W x ∂volume) =
      (ψ β - q)⁻¹)

/-- Any strict monotonicity strengthening needs its own nondegeneracy
condition, such as exclusion of the constant q=0 deterministic-drift
scale function. Such a condition must be sourced and proved separately. -/
def HasStrictQScale (ψ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  IsQScale ψ q W ∧ StrictMonoOn W (Set.Ici (0 : ℝ))

/-- Source-domain versus published transform-domain equivalence. Neither
convexity nor the right-root properties of a genuine Levy exponent are
silently assumed for an arbitrary real-valued ψ. -/
def IsScaleTransformDomainBridge (ψ : ℝ → ℝ) (q : ℝ) : Prop :=
  PhiIsLargestRoot ψ q ∧
  ∀ β : ℝ, 0 ≤ β → (Phi ψ q < β ↔ q < ψ β)

/-- Z^(q)(x)=1+q integral_0^x W^(q)(y)dy;
W vanishes on x<0, so Z=1 there under integrability. -/
noncomputable def Zscale (q : ℝ) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + q * ∫ y in (0 : ℝ)..x, W y

/-- Integrated q-scale function, no additional smoothness assumed. -/
noncomputable def integratedScale (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, W y

/-- A scale Stieltjes MEASURE with its possible atom at 0; density is
not part of this definition. For x>=0 the cumulative mass is W(x). -/
def IsScaleMeasure (W : ℝ → ℝ) (m : Measure ℝ) : Prop :=
  m (Set.Iio (0 : ℝ)) = 0 ∧
  m {0} = ENNReal.ofReal (W 0) ∧
  ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    m (Set.Ioc a b) = ENNReal.ofReal (W b - W a)

/-- Tilt of scale functions, W_c^(p)(x)=exp(-c*x) W^(p+psi(c))(x).
Analytic extension to negative p remains a later theorem. -/
noncomputable def tiltedScale (c : ℝ) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-c * x) * W x

/-- Finite right derivative, distinct from any derivative at 0 on all R. -/
def HasScaleRightDerivative (W : ℝ → ℝ) (x d : ℝ) : Prop :=
  HasDerivWithinAt W d (Set.Ici x) x

/-- Liminf of right difference quotients at zero, taking values in
EReal so the source's +infinity is representable. It is the true right
boundary derivative only when HasExtendedRightSlope holds. -/
noncomputable def scaleRightDerivativeZero (W : ℝ → ℝ) : EReal :=
  Filter.liminf (fun h : ℝ => (((W h - W 0) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- Exact existence of a potentially infinite right slope limit.
Distinct from finite HasDerivWithinAt and the Avram limit of ordinary
interior derivatives. -/
def HasExtendedRightSlope (W : ℝ → ℝ) (d : EReal) : Prop :=
  Filter.Tendsto
    (fun h : ℝ => (((W h - W 0) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)

/-- Unproved bridge obligation for the differently defined Avram
derivZeroPlus; equality is not valid for every real function. -/
def RightSlopeAgreesWithAvram (W : ℝ → ℝ) : Prop :=
  scaleRightDerivativeZero W =
    AvramDividend.Classical.derivZeroPlus W

/-- The finite boundary W(0) and atom issue remain source theorem 8.6. -/
def AtZeroScale (W : ℝ → ℝ) : ℝ := W 0

/-- Law-bound source characterisation using the actual published Levy
process exponent, instead of treating ψ as a freely chosen function.
Theorem 8.1 must still prove the root/domain/existence properties. -/
def IsLawScale
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (W : ℝ → ℝ) : Prop :=
  IsQScale L.ψ q W

/-- Pair of source and provider predicates, with explicit equivalence
left open until the Phi-domain and monotonicity bridges are proved. -/
def HasPublishedScaleBridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P ℱ)
    (q : ℝ) : Prop :=
  IsScaleTransformDomainBridge L.ψ q ∧
    ∀ W : ℝ → ℝ,
      IsLawScale L q W ↔
        (0 ≤ q ∧ AvramDividend.Classical.IsScaleFunction L q W)

/-- Source-linked published Avram/Mathlib scale-function specification.
This reuses the published predicate (definition e6610c46-99bb-43cf-af87-4d07e25d1631)
rather than assuming existence or selecting an arbitrary W. Chapter 8 adds
strict increase and the genuine Phi(q) boundary at theorem stage; neither
is inferred here from the weaker published MonotoneOn predicate. -/
def IsPublishedScaleCandidate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (W : ℝ → ℝ) : Prop :=
  0 ≤ q ∧ AvramDividend.Classical.IsScaleFunction L q W

/-- A genuine proved part of the Avram-to-Chapter-8 bridge:
once the right-root/transform-domain equivalence is established for the
actual process exponent, the two non-strict scale characterisations agree.
The root-domain fact itself is not assumed universally or derived here. -/
theorem lawScale_iff_published_of_rootDomain
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (W : ℝ → ℝ)
    (h : IsScaleTransformDomainBridge L.ψ q) :
    IsLawScale L q W ↔ IsPublishedScaleCandidate L q W := by
  constructor
  · intro hs
    rcases hs with ⟨hroot, hneg, hnon, hcont, hmono, hLap⟩
    refine ⟨hroot.1, ?_⟩
    refine ⟨hneg, ?_, hcont, hmono, ?_⟩
    · intro y hy
      exact hnon y
    · intro beta hb hq
      simpa only [neg_mul] using hLap beta hb ((h.2 beta hb).2 hq)
  · intro hp
    rcases hp with ⟨hq, hneg, hnon, hcont, hmono, hLap⟩
    refine ⟨h.1, hneg, ?_, hcont, hmono, ?_⟩
    · intro y
      by_cases hy : 0 ≤ y
      · exact hnon y hy
      · have hlt : y < 0 := lt_of_not_ge hy
        rw [hneg y hlt]
    · intro beta hb hPhi
      simpa only [neg_mul] using hLap beta hb ((h.2 beta hb).1 hPhi)

end Kyprianou.Ch08


