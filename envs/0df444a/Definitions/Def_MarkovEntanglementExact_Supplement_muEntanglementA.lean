-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_muEntanglementA
-- name    : MarkovEntanglementExact_Supplement_muEntanglementA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:47:00.8868+00:00
-- url     : https://prove2.me/theorems/0fa7d6e7-198b-5ac9-91ac-1c595e1ad385
-- title:
--   Measure of Markov entanglement $E_A$ w.r.t. the $\mu$-weighted agent-wise TV distance
-- statement:
--   The measure of Markov entanglement of $P$ with respect to agent $A$ under the $\mu$-weighted agent-wise total variation distance is Eq. (4) with the distance of Definition 8:
--   $$E_A(P)=\min_{P'\in\mathcal P_{\mathrm{SEP}}}\|P-P'\|_{\mu\text{-ATV}_A},$$
--   the minimum over separable transition matrices. Eq. (7) of the paper is an upper bound for it. It is the measure of Theorem 5.
--
--   **Formalization Note** Written as `sInf` over `IsSeparable Q ∧ IsTransitionMatrix Q`.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, p.19 (Definition 8 plugged into Eq. (4), p.14)

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_MarkovEntanglementExact_Supplement_muATVDistA

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

variable {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]

/-- The measure of Markov entanglement `E_A(P)` with respect to the `μ`-weighted agent-wise
total variation distance for agent `A`: Eq. (4) with the distance of Definition 8,
`E_A(P) = min_{P′ ∈ P_SEP} ‖P − P′‖_{μ−ATV_A}`, the minimum over separable transition
matrices.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, p.19 ("We plug in
µ-weighted ATV to Eq. (4) and obtain the corresponding measure of Markov entanglement"), Eq. (4),
p.14; `P_SEP` as transition matrices, p.12.

**Formalization Note.** This is Eq. (4) itself, not the upper bound Eq. (7). `P_SEP` is
`IsSeparable Q ∧ IsTransitionMatrix Q`; the `min` is `sInf` of a nonempty set bounded
below by `0`, attained by compactness. -/
noncomputable def muEntanglementA (μ : SA × SB → ℝ) (P : Matrix (SA × SB) (SA × SB) ℝ) : ℝ :=
  sInf {d : ℝ | ∃ Q : Matrix (SA × SB) (SA × SB) ℝ,
    IsSeparable Q ∧ IsTransitionMatrix Q ∧ d = muATVDistA μ P Q}

end MarkovEntanglementExact.Supplement


