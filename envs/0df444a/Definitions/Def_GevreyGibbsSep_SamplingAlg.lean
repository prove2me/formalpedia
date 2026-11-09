-- Prove2me | Definitions.Def_GevreyGibbsSep_SamplingAlg
-- name    : GevreyGibbsSep_SamplingAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:09.428249+00:00
-- url     : https://prove2.me/theorems/4c5f0852-81a8-41c7-9852-239cb02dd025
-- title:
--   Definition B.3 — classical randomized sampling algorithm
-- statement:
--   A **sampling algorithm** $A$ consists of a random seed $\omega\sim P$, drawn independently of the instance, together with query maps $Q_n$ and output maps $\Psi_n$. A run on an instance interleaves queries and oracle answers,
--   $$X_1=Q_1(\omega),\qquad O_n=\phi(p,X_n),\qquad X_{n+1}=Q_{n+1}(\omega,O_1,\dots,O_n),$$
--   and the output after $n$ queries is $\widehat X_n=\Psi_n(\omega,O_1,\dots,O_n)\in\mathbb T^d$. The first query depends on the seed alone, so warm starts are excluded.
--
--   **Formalization Note** The seed space is an arbitrary probability space. The maps are indexed from $0$: `Q n ω (O₁,…,Oₙ)` is $X_{n+1}$ and `Ψ n ω (O₁,…,Oₙ)` is $\widehat X_n$, so an output $\widehat X_0$ with no query is allowed. Query and output maps are jointly measurable in the seed and the answers, which the paper presupposes when it takes the law of $\widehat X_n$ over the seed.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.3, Eq. (B4), p.35

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_Answer

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition B.3 (sampling algorithm), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (B4), p.35:
a random seed `ω ∼ P` independent of the instance, query maps and output maps. `Q n ω (O₁, …, Oₙ)`
is the query `X_{n+1}` made after the answers `O₁, …, Oₙ` (so `X₁ = Q 0 ω ()` depends on the seed
alone), and `Ψ n ω (O₁, …, Oₙ)` is the output `X̂ₙ` after `n` queries.

**Formalization Note** The seed space is an arbitrary probability space (not a countable one).
The query and output maps are jointly measurable in the seed and the answers, which the paper
presupposes when it speaks of the law of `X̂ₙ` over the seed. An output map `Ψ 0` (output with no
query) is allowed. -/
structure SamplingAlg (d : ℕ) : Type 1 where
  /-- The seed space. -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- The law of the seed. -/
  P : Measure Ω
  [prob : IsProbabilityMeasure P]
  /-- `Q n ω O` is the `(n+1)`-st query point. -/
  Q : (n : ℕ) → Ω → (Fin n → Answer d) → Torus d
  /-- `Ψ n ω O` is the output after `n` queries. -/
  Ψ : (n : ℕ) → Ω → (Fin n → Answer d) → Torus d
  measurable_Q : ∀ n, Measurable (fun p : Ω × (Fin n → Answer d) => Q n p.1 p.2)
  measurable_Ψ : ∀ n, Measurable (fun p : Ω × (Fin n → Answer d) => Ψ n p.1 p.2)

attribute [instance] SamplingAlg.mΩ SamplingAlg.prob

end GevreyGibbsSep


