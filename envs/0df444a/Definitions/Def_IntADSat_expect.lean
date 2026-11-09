-- Prove2me | Definitions.Def_IntADSat_expect
-- name    : IntADSat_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:30.323197+00:00
-- url     : https://prove2.me/theorems/b613f259-e050-467a-9fbe-fd6f37649622
-- title:
--   Expectation under $G(n,1/2)$
-- statement:
--   For a real-valued function $X$ of a simple graph on $[n]$, its **expectation** under the Erdős–Rényi graph $G\sim G(n,1/2)$ is
--
--   $$
--   \mathbb E\,X=\sum_{G}\ 2^{-\binom n2}\,X(G),
--   $$
--
--   the sum over all labelled simple graphs on $[n]$: each of the $\binom n2$ pairs is an edge independently with probability $1/2$, so every labelled graph has probability $2^{-\binom n2}$. Variances are $\operatorname{Var}X=\mathbb E[X^2]-(\mathbb E X)^2$.
--
--   **Formalization Note** The weight is the published product weight `LPCommunity.SBMRecovery.edgeWeight` at edge probability $1/2$; event probabilities in the mission are the published `LPCommunity.SBMRecovery.erProb n (1/2)`, which is the expectation of the event's indicator.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.4, p.16 (PDF 17) (the expectation and variance under $G(n,1/2)$)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting

set_option autoImplicit false
open scoped Classical

namespace IntADSat

/-- The expectation `𝔼 X` of a real function of the graph under `G ∼ G(n, 1/2)`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.4, p.16 (PDF 17)): every one of the `n(n−1)/2` pairs is an edge independently with
probability `1/2`, i.e. the uniform law on the labelled simple graphs on `Fin n`.

**Formalization Note** The weight is the published Erdős–Rényi product weight
`LPCommunity.SBMRecovery.edgeWeight` at edge probability `1/2`, so that
`expect n (indicator of E) = LPCommunity.SBMRecovery.erProb n (1/2) E`, the probability used in every
statement of the mission. -/
noncomputable def expect (n : ℕ) (X : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), LPCommunity.SBMRecovery.edgeWeight G (fun _ _ => (1 / 2 : ℝ)) * X G

end IntADSat


