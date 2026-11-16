-- Prove2me | Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_randomizedAlgorithm
-- name    : DenseLanguageGeneration_PatientScope_Supplement_randomizedAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:57:53.4992+00:00
-- url     : https://prove2.me/theorems/b78f60b0-f169-4cc7-820c-e074715a569f
-- title:
--   Measurable randomized causal generators
-- statement:
--   A randomized generator consists of a probability space $(\Omega,\mathcal F,P)$ and a response function $g_\omega$ from finite lists of positive integers to a positive integer. For every history $u$ and output $x$, require
--
--   $$\{\omega:g_\omega(u)=x\}\in\mathcal F.$$
--
--   Because the output space is countable and discrete, this is precisely measurability of every response. One seed $\omega$ is used throughout a run and can encode all successive random choices. A response can use the received history and the seed, with the family fixed before play; it receives neither the secret target index nor future inputs. No correctness, density, efficiency or independence-between-rounds requirement is built into the object.
--
--   This primitive supports all randomized claims in the supplement, including the universal upper bound over every probability space and response law.
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), §4 opening and Definition 4.1, printed p.18 (PDF p.20); §2 model, printed p.7 (PDF p.9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Language

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open MeasureTheory

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- A probability space and a random causal response function. One private seed
is shared by all rounds, covering fresh per-round coins as well as correlated
choices. Each output is measurable: for the countable discrete codomain ℕ+,
measurability is equivalent to measurability of every singleton fibre.
No validity, density, target identity or computational condition is a field. -/
structure RandomizedGenerator where
  Ω : Type
  [measurableSpace : MeasurableSpace Ω]
  P : Measure Ω
  [isProbability : IsProbabilityMeasure P]
  gen : Ω → Generator ℕ+
  measurable_gen : ∀ (h : List ℕ+) (x : ℕ+), MeasurableSet {ω | gen ω h = x}

attribute [instance] RandomizedGenerator.measurableSpace RandomizedGenerator.isProbability

end DenseLanguageGeneration.PatientScope.Supplement


