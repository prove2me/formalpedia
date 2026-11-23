-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_Heterogeneous
-- name    : CarlssonPartition_Approx_Supplement_Heterogeneous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:21:22.482221+00:00
-- url     : https://prove2.me/theorems/e4fa28a8-f201-4f38-9d8a-ab42e5276486
-- title:
--   §3.4 — heterogeneous load and exact leading expressions built on the published spatial data
-- statement:
--   Reuse the published spatial instance $(R,x_0,f,m,v,q,\beta)$ and a location-dependent service kernel. The location law is constructed as $f(x)\mathbf 1_R(x)\,dx$. With $\bar s(x)$ computed from the kernel, the new load measure and workload are
--    $$
--    \mu_2(D)=\int_D(\bar s(x)vq+2\lVert x-x_0\rVert)f(x)\,dx,\quad
--    W(k,\lambda,D,g)=\frac\lambda k\int_D\bar s(x)g(x)\,dx+
--    \frac{2\lambda}{kvq}\int_D\lVert x-x_0\rVert g(x)\,dx.
--    $$
--    The load measure and primary workload use nonnegative extended integrals. A separate predicate records integrability of $\bar s g$ before real-valued formulas are interpreted. On that finite-mean domain, the file records the exact Theorem 8 expression
--    $$
--    L=\frac{\beta^2\lambda(1-1/q)^2[\int_D\sqrt g]^2}{2k^2v^2(1-W)^2},
--    $$
--    the Theorem 7 expression with $\gamma^2(1+1/q)^2/9$ in place of $\beta^2(1-1/q)^2/2$, and the workload-from-below heavy-traffic filter. These are formulas, not policy performance definitions or hypotheses of a substitute theorem. The pointwise source assumptions do not include finite spatial mean or variance; the separate finite-mean predicate makes that gap visible. Its real-valued formulas are used only with the finite spatial-mean domain; the extended workload retains infinite values.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §3.4 pp. 13–14 (PDF 14–15), proof of Theorem 9 p. ec12 (PDF 49)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Setting
import Definitions.Def_CarlssonPartition_Approx_Supplement_ServiceMarks

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory Filter
open scoped ENNReal

/-- The source demand law, constructed from the published spatial instance rather than
replacing its density by an independent measure. Standing hypotheses make it a probability. -/
def locationLaw (I : CarlssonPartition.Approx.Instance) :
    Measure CarlssonPartition.Equitable.Plane :=
  (volume.restrict I.R).withDensity (fun x => ENNReal.ofReal (I.f x))

/-- The heterogeneous service assumptions as stated on p.13, with no uniform bound. -/
def serviceStanding (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks CarlssonPartition.Equitable.Plane) : Prop :=
  I.Standing ∧ S.FiniteOn I.R

/-- The extra domain on which real-valued leading expressions faithfully represent the
spatial mean. This is NOT silently included in `serviceStanding`: pointwise moment
finiteness in the paper does not imply it. No theorem in this draft assumes this to
replace an unresolved full-domain claim. -/
def finiteMeanDomain (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks CarlssonPartition.Equitable.Plane)
    (D : Set CarlssonPartition.Equitable.Plane)
    (g : CarlssonPartition.Equitable.Plane → ℝ) : Prop :=
  IntegrableOn (fun x => S.mean x * g x) D

/-- The load measure of Theorem 9, with location-dependent on-site mean. It is an
extended integral, so an infinite spatial mean cannot turn into zero. -/
def heterogeneousMu2 (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks CarlssonPartition.Equitable.Plane)
    (D : Set CarlssonPartition.Equitable.Plane) : ℝ≥0∞ :=
  ∫⁻ x in D, ENNReal.ofReal
    ((S.mean x * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)

/-- Extended workload; meaningful for positive arrival rate, speed, capacity and fleet size. -/
def heterogeneousWorkload (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks CarlssonPartition.Equitable.Plane)
    (k : ℕ) (lam : ℝ) (D : Set CarlssonPartition.Equitable.Plane)
    (g : CarlssonPartition.Equitable.Plane → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal lam *
      (∫⁻ x in D, ENNReal.ofReal (S.mean x * g x)) / (k : ℝ≥0∞) +
    2 * ENNReal.ofReal lam *
      (∫⁻ x in D, ENNReal.ofReal (‖x - I.x0‖ * g x)) /
      ((k : ℝ≥0∞) * ENNReal.ofReal I.v * (I.q : ℝ≥0∞))

/-- Real workload formula, used only on `finiteMeanDomain`. It keeps the heterogeneous
mean rather than substituting the published instance's constant `sbar`. -/
def finiteWorkload (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks CarlssonPartition.Equitable.Plane)
    (k : ℕ) (lam : ℝ) (D : Set CarlssonPartition.Equitable.Plane)
    (g : CarlssonPartition.Equitable.Plane → ℝ) : ℝ :=
  lam * (∫ x in D, S.mean x * g x) / (k : ℝ) +
    2 * lam * (∫ x in D, ‖x - I.x0‖ * g x) /
      ((k : ℝ) * I.v * (I.q : ℝ))

/-- The exact Theorem 8 leading expression on its finite-mean domain. -/
def finiteLeading (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks CarlssonPartition.Equitable.Plane)
    (k : ℕ) (lam : ℝ) (D : Set CarlssonPartition.Equitable.Plane)
    (g : CarlssonPartition.Equitable.Plane → ℝ) : ℝ :=
  I.beta ^ 2 * lam * (1 - 1 / (I.q : ℝ)) ^ 2 *
    (∫ x in D, Real.sqrt (g x)) ^ 2 /
      (2 * (k : ℝ) ^ 2 * I.v ^ 2 * (1 - finiteWorkload I S k lam D g) ^ 2)

/-- The exact Theorem 7 lower-bound coefficient, on the same finite-mean domain.
This is a formula only; no lower-bound theorem is assumed or asserted here. -/
def finiteLowerLeading (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks CarlssonPartition.Equitable.Plane) (gamma : ℝ)
    (k : ℕ) (lam : ℝ) (D : Set CarlssonPartition.Equitable.Plane)
    (g : CarlssonPartition.Equitable.Plane → ℝ) : ℝ :=
  gamma ^ 2 / 9 * lam * (1 + 1 / (I.q : ℝ)) ^ 2 *
    (∫ x in D, Real.sqrt (g x)) ^ 2 /
      ((k : ℝ) ^ 2 * I.v ^ 2 * (1 - finiteWorkload I S k lam D g) ^ 2)

/-- Heavy traffic for finite spatial means uses the source's workload-from-below filter. -/
def finiteHeavy (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks CarlssonPartition.Equitable.Plane)
    (k : ℕ) (D : Set CarlssonPartition.Equitable.Plane)
    (g : CarlssonPartition.Equitable.Plane → ℝ) : Filter ℝ :=
  Filter.comap (fun lam => finiteWorkload I S k lam D g)
    (nhdsWithin 1 (Set.Iio 1))

end CarlssonPartition.Approx.Supplement


