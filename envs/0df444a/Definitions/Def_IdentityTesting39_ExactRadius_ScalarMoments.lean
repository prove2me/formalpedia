-- Prove2me | Definitions.Def_IdentityTesting39_ExactRadius_ScalarMoments
-- name    : IdentityTesting39_ExactRadius_ScalarMoments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:14.016852+00:00
-- url     : https://prove2.me/theorems/15ecf7e7-5b50-496e-979e-db4ccb2d1444
-- title:
--   Scalar laws, the closed moment cone, and minimum-variance extremizers
-- statement:
--   For a scalar reference coordinate $q$, a moment tuple is realized by a probability measure on $[0,1]$ with
--
--   $$(r,w,e,d)=\bigl(\mathbb EU,\mathbb E(U-q)^2,\mathbb E(U-q)_+,\mathbb E(q-U)_+\bigr).$$
--
--   The region is defined through laws, independently of the cone inequalities. The latter use $z\in[0,1]$, $s=w+2qr-q^2$, $A=e+qz$, $B=r-e-qz$, and nonnegative perspective epigraphs $s_1,s_2$: $A^2\le zs_1$, $B^2\le(1-z)s_2$, $s_1+s_2\le s$, together with the linear bounds in (2). At $q=0$ they become $e=r$ and $r^2\le w\le r$. The moment curve records $(u,(u-q)^2,(u-q)_+)$.
--
--   For §5, a separate nonnegative-law predicate requires a finite second moment; no upper support bound is imposed. Means, variances, deficits and excesses are integrals. The minimum-variance formula and its explicit two-point law implement (8), with Dirac laws at $d=0$ and $d=q$ as specified in Appendix C.1. These separate interfaces preserve the source's two different support regimes.
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.4, §3, display (2); scalar moments: §2, p.2; extremizers: §5, (8), p.6 and Appendix C.1, p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Mathlib

open MeasureTheory

noncomputable section

namespace IdentityTesting39.ExactRadius

/-- §2, p.2: the region is defined through laws, independently of the cone description. -/
def ScalarMoments (q r w e d : ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
    (∀ᵐ u ∂μ, u ∈ Set.Icc (0 : ℝ) 1) ∧
    r = ∫ u, u ∂μ ∧ w = ∫ u, (u - q)^2 ∂μ ∧
    e = ∫ u, max (u - q) 0 ∂μ ∧ d = ∫ u, max (q - u) 0 ∂μ

/-- §3, (2), in closed perspective epigraph form, including z=0 and z=1. -/
def ScalarCone (q r w e : ℝ) : Prop :=
  if q = 0 then e = r ∧ r^2 ≤ w ∧ w ≤ r
  else ∃ z s₁ s₂ : ℝ,
    z ∈ Set.Icc 0 1 ∧ 0 ≤ s₁ ∧ 0 ≤ s₂ ∧
    q*z ≤ e + q*z ∧ e + q*z ≤ z ∧
    0 ≤ r - e - q*z ∧ r - e - q*z ≤ q*(1-z) ∧
    (e + q*z)^2 ≤ z*s₁ ∧ (r-e-q*z)^2 ≤ (1-z)*s₂ ∧
    s₁+s₂ ≤ w+2*q*r-q^2 ∧ w+2*q*r-q^2 ≤ q*r+e

/-- Curve whose convex hull is the scalar moment region. -/
def momentCurve (q u : ℝ) : Fin 3 → ℝ := ![u, (u-q)^2, max (u-q) 0]

/-- §5 uses nonnegative laws with a finite second moment, not only laws on [0,1]. -/
def NonnegativeSecondMomentLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ u ∂μ, 0 ≤ u) ∧ Integrable (fun u => u^2) μ

noncomputable def scalarMean (μ : Measure ℝ) : ℝ := ∫ u, u ∂μ
noncomputable def scalarVariance (μ : Measure ℝ) : ℝ :=
  ∫ u, (u - scalarMean μ)^2 ∂μ
noncomputable def scalarDeficit (q : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ u, max (q-u) 0 ∂μ
noncomputable def scalarExcess (q : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ u, max (u-q) 0 ∂μ

/-- (8) with the deterministic endpoints handled before division. -/
def minimumVariance (q r d e : ℝ) : ℝ :=
  if d = 0 ∨ d = q then 0 else if d+e ≤ q then 4*d*e else r^2*d/(q-d)

/-- The explicit extremizer in §5 and Appendix C.1; endpoint laws are Dirac measures. -/
noncomputable def extremalLaw (q r d e : ℝ) : Measure ℝ :=
  if d = 0 then Measure.dirac (q+e)
  else if d = q then Measure.dirac 0
  else if d+e ≤ q then
    ENNReal.ofReal (d/(d+e)) • Measure.dirac (q-(d+e)) +
    ENNReal.ofReal (e/(d+e)) • Measure.dirac (q+(d+e))
  else ENNReal.ofReal (d/q) • Measure.dirac 0 +
    ENNReal.ofReal ((q-d)/q) • Measure.dirac (r*q/(q-d))

end IdentityTesting39.ExactRadius


