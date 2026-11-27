-- Prove2me | Definitions.Def_ProcessingNetworks_EntropyIneq_Supplement_RegularCTMC
-- name    : ProcessingNetworks_EntropyIneq_Supplement_RegularCTMC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:07:28.45896+00:00
-- url     : https://prove2.me/theorems/41ff0c81-5ce9-4dcf-b353-5776d17c2ebf
-- title:
--   Regular countable-state CTMC law with transition semigroup
-- statement:
--   Let $S$ be a countable state space. A **regular continuous-time Markov chain law** consists of a generator $\Lambda=(\Lambda_{ij})$, an initial probability distribution $\rho$, and transition probabilities $P_{ij}(t)$ for $t\ge 0$. The generator has nonnegative off-diagonal entries, strictly positive exit rates $\lambda(i)=-\Lambda_{ii}$, zero row sums, and is non-explosive. The transition probabilities satisfy
--
--   $$
--   P(0)=I,\qquad P(s+t)=P(s)P(t),\qquad P'(0+)=\Lambda.
--   $$
--
--   This law-level object is the transition-semigroup form of the regular CTMC constructed in Appendix D. It supports the stationary-process, skeleton-chain, and convergence statements in Theorems D.18--D.24.
--
--   **Formalization Note** `transition t i` is a probability mass function on $S$. The generator relation is the coordinatewise right derivative at zero. Non-explosion is the published Definition D.2 predicate, and strictly positive exit rates are built into the published generator predicate. The book states that two CTMCs with the same state space, initial distribution and generator are equal in distribution, so no sample-path realization is fixed here.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definitions D.1--D.3 and D.6, eqs. (D.1)--(D.13), pp.287--290 (PDF 303--306)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_ProcessingNetworks_CTMCFoster_jumpPMF
import Definitions.Def_ProcessingNetworks_CTMCFoster_NonExplosive

namespace ProcessingNetworks.EntropyIneq.Supplement

open MatrixAnalytic.ProductForm
open scoped NNReal

/-- A regular continuous-time Markov chain on a countable state space, represented by its
generator, initial law, and transition semigroup.

Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org),
Definitions D.1--D.3 and D.6, equations (D.1)--(D.13), pp.287--290 (PDF 303--306).

**Formalization Note** The book constructs sample paths and then observes that their law is uniquely
determined by the initial distribution and the transition semigroup. This structure records that
law-level object. `transition t i` is the conditional law at elapsed time `t` given state `i`.
The Chapman--Kolmogorov field is (D.13), and `transition_generator` is the right-derivative
identity (D.12), with negative arguments ignored by the within derivative. Regularity is exactly
Definition D.3: strictly positive exit rates are part of `IsGeneratorC`, and non-explosion is the
published `ProcessingNetworks.CTMCFoster.NonExplosive` predicate. -/
structure RegularCTMC (S : Type*) [Countable S] [DecidableEq S] where
  generator : S → S → ℝ
  isGenerator : IsGeneratorC generator
  nonexplosive : ProcessingNetworks.CTMCFoster.NonExplosive
    (ProcessingNetworks.CTMCFoster.jumpPMF isGenerator) (holdRate generator)
  initial : PMF S
  transition : ℝ≥0 → S → PMF S
  transition_zero : ∀ i, transition 0 i = PMF.pure i
  transition_add : ∀ s t i, transition (s + t) i = (transition s i).bind (transition t)
  transition_generator : ∀ i j,
    HasDerivWithinAt
      (fun t : ℝ => (transition (Real.toNNReal t) i j).toReal)
      (generator i j) (Set.Ici 0) 0

end ProcessingNetworks.EntropyIneq.Supplement


