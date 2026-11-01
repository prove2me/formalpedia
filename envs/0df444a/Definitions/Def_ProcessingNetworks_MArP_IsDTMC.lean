-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_IsDTMC
-- name    : ProcessingNetworks_MArP_IsDTMC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:38.20609+00:00
-- url     : https://prove2.me/theorems/83b25491-23a3-4c78-8600-b9c2e94bf536
-- title:
--   Discrete-time Markov chain with transition matrix $P$ and initial distribution $\mu$ (Definition C.1)
-- statement:
--   A sequence $X=\{X_n\}$ of random variables with values in a countable set $\mathcal S$ is a **discrete-time Markov chain** with transition matrix $P$ and initial distribution $\mu$ if $\mathbb P\{X_0=i\}=\mu(i)$ for all $i$ and
--   $$
--   \mathbb P\{X_0=i_0,\dots,X_n=i_n,X_{n+1}=y\}=\mathbb P\{X_0=i_0,\dots,X_n=i_n\}\,P(i_n,y)
--   $$
--   for every $n$, every path $i_0,\dots,i_n$ and every state $y$. By induction this is the book's path law $\mu_{i_0}P_{i_0i_1}\cdots P_{i_{k-1}i_k}$.
--
--   **Formalization Note** The book's $\mathbb P_\mu$ is the ambient measure of a chain with initial law $\mu$, so "for each initial distribution $\mu$" quantifies over all chains satisfying this predicate. The Markov identity is the published `ProcessingNetworks.Stability.IsJumpChain`, which adds no condition on $P$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition C.1, eq. (C.3), p.275 (PDF p.291)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation

open MeasureTheory ProbabilityTheory

namespace ProcessingNetworks.MArP

/-- `X = {X_n}` is a discrete-time Markov chain with transition matrix `P` and initial distribution
`μ` (Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2, Definition C.1, eq. (C.3),
Appendix C, p.275, PDF p.291): each `X_n` is a random variable, `P{X₀ = i} = μ(i)`, and the path law
is that of `IsJumpChain`.

**Formalization Note.** The book's `P_μ` is the ambient probability measure of a chain whose initial
law is `μ`; a statement "for each initial distribution `μ`" quantifies over all chains `X` with
`IsDTMC P μ X`. The reused `ProcessingNetworks.Stability.IsJumpChain` adds no condition: it is the
Markov property (C.3) for a general transition matrix, which may have nonzero diagonal. -/
structure IsDTMC {S Ω : Type*} [MeasurableSpace S] [MeasureSpace Ω] (P : S → PMF S) (μ : PMF S)
    (X : ℕ → Ω → S) : Prop where
  measurable : ∀ n, Measurable (X n)
  initial : ∀ i, ℙ {ω | X 0 ω = i} = μ i
  markov : ProcessingNetworks.Stability.IsJumpChain P X

end ProcessingNetworks.MArP


