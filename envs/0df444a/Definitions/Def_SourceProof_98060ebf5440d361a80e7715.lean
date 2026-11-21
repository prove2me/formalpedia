-- Prove2me | Definitions.Def_SourceProof_98060ebf5440d361a80e7715
-- name    : SourceProof_98060ebf5440d361a80e7715
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:02:58.014259+00:00
-- url     : https://prove2.me/theorems/b086a0c2-3aca-44cf-924b-f475b0175073
-- title:
--   LevyStochCalc source module: SourceProof_98060ebf5440d361a80e7715
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_compensatedProduct_mul` comes from the `LevyStochCalc.Poisson.CompensatedProductMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F001

open private memLp_tendsto_compensatedProduct from Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F001
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of the compensated product of two bounded mark profiles

For bounded square-integrable mark profiles `f, g : E → ℝ` and the compensated integral `J` over
the step `(a, b]` against a Poisson random measure with intensity `ν`, the compensated product
`Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν` is square integrable and centred, it is
orthogonal in `L²(P)` to `J(h)` for every square-integrable profile `h`, and, with
`⟨u, v⟩ = ∫ u v dν`,

  `E[Q(f, g) Q(f', g')] = (b − a)² (⟨f, f'⟩ ⟨g, g'⟩ + ⟨f, g'⟩ ⟨g, f'⟩)`.

The profiles `f, g` are arbitrary bounded square-integrable functions; their supports may
overlap, and no independence of their compensated integrals enters.

Each of `f, g` is approximated in `L²(ν)` by simple profiles obeying the same bound, and at simple
profiles the identities hold by `Poisson/CompensatedProduct.lean`. The Gram at simple profiles
writes the `L²(P)` distance of two compensated products through `L²(ν)` pairings, so the
compensated products of the approximants form a Cauchy sequence in `L²(P)`. The compensated
integrals of the approximants and of their products converge in `L²(P)` by the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}` at square-integrable profiles; along a
subsequence all of them converge almost surely, which identifies the `L²(P)` limit with
`Q(f, g)`. The identities then pass to the limit by continuity of the `L²` pairing, so no third or
fourth moment of the compensated integral of a general profile is needed.

## Main statements

* `LevyStochCalc.Poisson.integral_compensatedProfile_sub_sq`,
  `LevyStochCalc.Poisson.eLpNorm_compensatedProfile_sub` — the isometry at square-integrable
  profiles.
* `LevyStochCalc.Poisson.memLp_compensatedProduct` — square integrability.
* `LevyStochCalc.Poisson.integral_compensatedProduct` — the mean.
* `LevyStochCalc.Poisson.integral_compensatedProduct_mul` — the Gram.
* `LevyStochCalc.Poisson.integral_compensatedProduct_mul_compensatedProfile` — orthogonality to
  the first chaos.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Probability

/-! ### `L²` facts -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end LevyStochCalc.Probability

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The isometry -/

/-! ### Passage to the limit -/

/-! ### The moments -/


theorem _root_.Prove2MeSourceProof.h_98060ebf5440d361a80e7715 (N : PoissonRandomMeasure P ν) {f g f' g' : E → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (hf' : MemLp f' 2 ν) (hg' : MemLp g' 2 ν)
    {Cf Cg Cf' Cg' : ℝ} (hbf : ∀ e, |f e| ≤ Cf) (hbg : ∀ e, |g e| ≤ Cg)
    (hbf' : ∀ e, |f' e| ≤ Cf') (hbg' : ∀ e, |g' e| ≤ Cg') {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫ ω, compensatedProduct N f g a b ω * compensatedProduct N f' g' a b ω ∂P
      = (b - a) ^ 2 * ((∫ e, f e * f' e ∂ν) * (∫ e, g e * g' e ∂ν)
        + (∫ e, f e * g' e ∂ν) * (∫ e, g e * f' e ∂ν)) := by
  obtain ⟨F, hF⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  obtain ⟨G, hGb, hG⟩ := _root_.Prove2MeSourceProof.h_39bcf7b6426eb7b206aa98c5 hg hbg
  obtain ⟨F', hF'⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf'
  obtain ⟨G', hG'b, hG'⟩ := _root_.Prove2MeSourceProof.h_39bcf7b6426eb7b206aa98c5 hg' hbg'
  obtain ⟨hQ, hc⟩ := memLp_tendsto_compensatedProduct N hf hg hbf hbg ha hab hGb hF hG
  obtain ⟨hQ', hc'⟩ :=
    memLp_tendsto_compensatedProduct N hf' hg' hbf' hbg' ha hab hG'b hF' hG'
  have hFm : ∀ n, MemLp (F n).toFun 2 ν := fun n => (F n).memLp_toFun
  have hGm : ∀ n, MemLp (G n).toFun 2 ν := fun n => (G n).memLp_toFun
  have hF'm : ∀ n, MemLp (F' n).toFun 2 ν := fun n => (F' n).memLp_toFun
  have hG'm : ∀ n, MemLp (G' n).toFun 2 ν := fun n => (G' n).memLp_toFun
  have hP := _root_.Prove2MeSourceProof.h_a7627240d6bb04f5e392fa17
    (fun n => LevyStochCalc.Poisson.SimpleProfile.memLp_compensatedProduct N (F n) (G n) ha hab)
    (fun n => LevyStochCalc.Poisson.SimpleProfile.memLp_compensatedProduct N (F' n) (G' n) ha hab) hQ hQ' hc hc'
  have h1 := _root_.Prove2MeSourceProof.h_a7627240d6bb04f5e392fa17 hFm hF'm hf hf' hF hF'
  have h2 := _root_.Prove2MeSourceProof.h_a7627240d6bb04f5e392fa17 hGm hG'm hg hg' hG hG'
  have h3 := _root_.Prove2MeSourceProof.h_a7627240d6bb04f5e392fa17 hFm hG'm hf hg' hF hG'
  have h4 := _root_.Prove2MeSourceProof.h_a7627240d6bb04f5e392fa17 hGm hF'm hg hf' hG hF'
  have hν := ((h1.mul h2).add (h3.mul h4)).const_mul ((b - a) ^ 2)
  exact tendsto_nhds_unique (hP.congr fun n =>
    LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul N (F n) (G n) (F' n) (G' n) ha hab) hν
end LevyStochCalc.Poisson


