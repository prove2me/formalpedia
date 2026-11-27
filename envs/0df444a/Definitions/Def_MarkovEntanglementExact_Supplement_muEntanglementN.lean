-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_muEntanglementN
-- name    : MarkovEntanglementExact_Supplement_muEntanglementN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:48:41.094809+00:00
-- url     : https://prove2.me/theorems/187828a0-d6c1-4ff2-8f7a-6e653ac4e958
-- title:
--   Measure of multi-agent Markov entanglement $E_i$ w.r.t. the $\mu$-weighted agent-wise TV distance
-- statement:
--   The measure of multi-agent Markov entanglement of agent $i$ under the $\mu$-weighted agent-wise total variation distance is Eq. (8) with the distance of Definition 8:
--   $$E_i(P)=\min_{P'\in\mathcal P_{\mathrm{SEP}}}\|P-P'\|_{\mu\text{-ATV}_i},$$
--   the minimum over separable $N$-agent transition matrices $\sum_jx_jP^{(j)}_1\otimes\dots\otimes P^{(j)}_N$ (Definition 10). It is the measure of Theorems 6 and 7.
--
--   **Formalization Note** Written as `sInf` over `IsSeparableN Q ∧ IsTransitionMatrix Q`; it is not the published `entanglementN`, which is the larger right-hand side of Eq. (7).
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (8) and Definition 10, p.21; Definition 14, p.40

import Mathlib
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_MarkovEntanglementExact_Supplement_muATVDistN

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- The measure of multi-agent Markov entanglement `E_i(P)` of agent `i` with respect to the
`μ`-weighted agent-wise total variation distance: Eq. (8) with the distance of Definition 8,
`E_i(P) = min_{P′ ∈ P_SEP} ‖P − P′‖_{μ−ATV_i}`, the minimum over separable `N`-agent transition
matrices (Definition 10).

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (8) and
Definition 10, p.21; Definition 8, p.19; Theorem 6, pp.21–22.

**Formalization Note.** `P_SEP` is `IsSeparableN Q ∧ IsTransitionMatrix Q` (Definition 10 with
the nonnegativity that p.12 requires of `P_SEP`). The `min` is `sInf` of a nonempty set bounded
below by `0`, attained by compactness. This is not the published `entanglementN`, which is the
larger right-hand side of Eq. (7). -/
noncomputable def muEntanglementN {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] (i : Fin N) (μ : Joint S → ℝ)
    (P : Matrix (Joint S) (Joint S) ℝ) : ℝ :=
  sInf {d : ℝ | ∃ Q : Matrix (Joint S) (Joint S) ℝ,
    IsSeparableN Q ∧ IsTransitionMatrix Q ∧ d = muATVDistN i μ P Q}

end MarkovEntanglementExact.Supplement


