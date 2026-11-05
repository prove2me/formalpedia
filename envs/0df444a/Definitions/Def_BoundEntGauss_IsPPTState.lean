-- Prove2me | Definitions.Def_BoundEntGauss_IsPPTState
-- name    : BoundEntGauss_IsPPTState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:36.420729+00:00
-- url     : https://prove2.me/theorems/4d9f1e73-f27f-410b-9e7f-8908d5d8eb53
-- title:
--   A state with positive partial transpose (ppt)
-- statement:
--   Let $\rho$ be a density operator of a bipartite system of $n$ oscillator modes on Alice's side and $m$ on Bob's side, acting on the Fock space $\mathcal F_n\otimes\mathcal F_m$. The state has **positive partial transpose** (is *ppt*) when its partial transpose $\rho^{T_A}$ with respect to Alice, taken in the Fock (number) basis, is again a density operator: a positive trace-class operator of trace one.
--
--   This is the condition "the partial transpose of $\rho$ is again a density operator" of the paper. In infinite dimension the partial transpose of a trace-class operator need not be trace class, so trace class is part of the condition.
--
--   **Formalization Note** Uses the published `IsDensity` (nuclear trace class, every finite quadratic form real and non-negative, real diagonal summing to one).
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, p. 3 (paragraph before Proposition 2)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_BoundEntGauss_aliceTranspose

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BoundEntGauss

/-- **A state with positive partial transpose (ppt).**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, p. 3 ("if the partial transpose of ρ is again a density operator").

A density operator `ρ` of an `n × m`-mode bipartite oscillator system (Alice holds the first
`n` modes, Bob the last `m`) has positive partial transpose when its partial transpose on Alice,
taken in the Fock basis, is again a density operator: trace class, positive and of trace one.

**Formalization Note.** Reading: "ppt" is `IsDensity (aliceTranspose ρ)` with the published
`Dependency50.P33.IsDensity` (nuclear trace class, every finite quadratic form real and
nonnegative, real diagonal summing to one). The partial transpose of a trace-class operator on an
infinite-dimensional space need not be trace class, so trace class is part of the condition, as in
the paper's "is again a density operator". -/
def IsPPTState {n m : ℕ} (ρ : State (Occupation (Fin n) × Occupation (Fin m))) : Prop :=
  IsDensity (aliceTranspose ρ.coefficients)

end BoundEntGauss


