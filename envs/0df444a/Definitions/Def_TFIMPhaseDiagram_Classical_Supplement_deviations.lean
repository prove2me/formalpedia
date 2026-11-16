-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations
-- name    : TFIMPhaseDiagram_Classical_Supplement_deviations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:58:20.682129+00:00
-- url     : https://prove2.me/theorems/0e333127-3465-4931-96ad-67cdad3d273a
-- title:
--   Norm-topology LDP adapter for a sequence of laws
-- statement:
--   For probability laws $\mu_n$ on the Hilbert space $L^2(S)$ and a lower semicontinuous nonnegative rate $I:L^2(S)\to[0,\infty]$, this adapter uses the published general metric large deviation principle at speed $n$:
--   $$
--   -\inf_G I\le\liminf_{n\to\infty}n^{-1}\log\mu_n(G),\qquad
--   \limsup_{n\to\infty}n^{-1}\log\mu_n(F)\le-\inf_F I
--   $$
--   for every norm-open $G$ and norm-closed $F$. The laws are realized as coordinates of their canonical independent product, so the published random-element interface applies without changing any law. Nonnegativity, lower semicontinuity and the probability-law requirements are part of the predicate, rather than additional hypotheses of a source theorem.
--
--   **Formalization Note** Coordinate $k$ has source index $k+1$, with speed $k+1$. The index shift removes the irrelevant zero-speed first term. The published definition uses extended logarithms with $\log 0=-\infty$ and extended infima; conversion of rates to extended nonnegative reals is accompanied by the nonnegativity clause. This reuses the general LDP object rather than redeclaring its bounds.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 15, Definition 24 and footnote 10

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_pathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement

/-- Law-sequence adapter to the published general metric LDP, using the canonical independent
coordinate realization. Index k is source index k+1, so the speed is k+1, never zero.
The rate is required to be lower semicontinuous and nonnegative, as in footnote 10. -/
def HasNormLDP (μ : ℕ → Measure CircleL2) (I : CircleL2 → EReal) : Prop :=
  LowerSemicontinuous I ∧ (∀ x, 0 ≤ I x) ∧
  ∃ hp : ∀ k : ℕ, IsProbabilityMeasure (μ (k+1)),
    letI : ∀ k : ℕ, IsProbabilityMeasure (μ (k+1)) := hp
    ReflectedRWLDP.SamplePath.SatisfiesLDP
      (Measure.infinitePi (fun k => μ (k+1))) (fun k σ => σ k)
      edist (fun k => (k+1 : ℕ)) (fun x => (I x).toENNReal)

end TFIMPhaseDiagram.Classical.Supplement


