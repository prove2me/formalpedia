-- Prove2me | Definitions.Def_PlanarAndersonSpectrum
-- name    : PlanarAndersonSpectrum
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:03.909489+00:00
-- url     : https://prove2.me/theorems/0fc01c1f-d091-460d-b94b-543d993201ae
-- statement:
--   The block sets up the planar Anderson model on the integer lattice. Site is ℤ×ℤ, a Configuration is a real-valued function on sites (a potential), and Hilbert is the complex ℓ² space of square-summable complex functions on sites. For h, disorderLaw(h) is the infinite product measure on configurations in which each site's value is independently drawn from Lebesgue measure on the interval [−h,h] conditioned to that interval (the conditional measure given by ProbabilityTheory.cond), that is, uniform when h>0. For a configuration v and a bounded complex-linear operator H on the Hilbert space, IsAndersonOperator(v,H) says that for every u and site x=(x₁,x₂), (Hu)(x) equals the sum of u at the four nearest neighbours (x₁±1,x₂) and (x₁,x₂±1), plus v(x)·u(x). The set spectralInterval(h) is the set of complex numbers z with imaginary part zero and real part between −4−h and 4+h inclusive, i.e. the real segment [−4−h,4+h]. These are definitions only; no theorem about the spectrum is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PlanarAndersonSpectrum.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PlanarAndersonSpectrum.lean; bytes 16..701
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PlanarAnderson

abbrev Site := ℤ × ℤ
abbrev Configuration := Site → ℝ
abbrev Hilbert := lp (fun _ : Site => ℂ) 2

def disorderLaw (h : ℝ) : Measure Configuration :=
  Measure.infinitePi (fun _ : Site => ProbabilityTheory.cond volume (Set.Icc (-h) h))

def IsAndersonOperator (v : Configuration) (H : Hilbert →L[ℂ] Hilbert) : Prop :=
  ∀ (u : Hilbert) (x : Site),
    (H u) x = u (x.1 + 1, x.2) + u (x.1 - 1, x.2) +
      u (x.1, x.2 + 1) + u (x.1, x.2 - 1) + (v x : ℂ) * u x

def spectralInterval (h : ℝ) : Set ℂ :=
  {z | z.im = 0 ∧ -4 - h ≤ z.re ∧ z.re ≤ 4 + h}



end PlanarAnderson
end
end OAI


