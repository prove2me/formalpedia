-- Prove2me | Definitions.Def_OptimalSignalEnsembles_holevoChi
-- name    : OptimalSignalEnsembles_holevoChi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:49.603657+00:00
-- url     : https://prove2.me/theorems/65b9af4c-9b11-4810-b6ad-39e6887f2fcd
-- title:
--   Holevo quantity $\chi=S(\bar\rho)-\sum_k p_kS(\rho_k)$
-- statement:
--   For a finite ensemble $(p_k,\rho_k)_{k=1}^n$ with average state $\bar\rho = \sum_k p_k\rho_k$, the **Holevo quantity** is
--
--   $$\chi \;=\; S(\bar\rho) - \sum_{k=1}^n p_k\, S(\rho_k), \tag{1}$$
--
--   where $S(\rho) = -\operatorname{Tr}\rho\log\rho$ is the von Neumann entropy.
--
--   Holevo's theorem bounds the classical information conveyed by the ensemble by $\chi$, and the bound is asymptotically achievable; maximizing $\chi$ over the available signal states is the subject of the paper.
--
--   **Formalization Note** $S$ is the published `vonNeumannEntropy`, $-\operatorname{Re}\operatorname{Tr}(\rho\,\log\rho)$ with the matrix logarithm by functional calculus and $0\log 0 = 0$; the logarithm is natural (all results of the paper are homogeneous in the base). The value is a real number.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, eq. (1), p.2

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_avgState

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- The **Holevo quantity** of a finite ensemble, eq. (1):
`χ = S(ρ̄) − ∑ₖ pₖ S(ρₖ)`, with `S(ρ) = −Tr ρ log ρ` the von Neumann entropy and
`ρ̄ = ∑ₖ pₖ ρₖ` the average state.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, eq. (1), p.2.

**Formalization Note.** `S` is the published `ProjectiveMeasurementEquilibration.vonNeumannEntropy`,
`−Re Tr(ρ · cfc Real.log ρ)`: natural logarithm, with `0 log 0 = 0` (the paper's results are
homogeneous in the base of the logarithm). The value is a real number. -/
noncomputable def holevoChi {d : Type} [Fintype d] [DecidableEq d] {n : ℕ} (p : Fin n → ℝ)
    (ρ : Fin n → Matrix d d ℂ) : ℝ :=
  vonNeumannEntropy (avgState p ρ) - ∑ k, p k * vonNeumannEntropy (ρ k)

end OptimalSignalEnsembles


