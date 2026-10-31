-- Prove2me | Definitions.Def_MarkovEntanglementExact_LocalValuesDecompose
-- name    : MarkovEntanglementExact_LocalValuesDecompose
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:23.159082+00:00
-- url     : https://prove2.me/theorems/2ff1927c-c64b-4141-b70c-c7b7e1d13b77
-- title:
--   The local Q-values of $P_A$, $P_B$ decompose the global Q-value
-- statement:
--   Let $P$ be a matrix on $S_A\times S_B$, let $P_A,P_B$ be matrices on $S_A$ and $S_B$, and let $\gamma$ be a discount factor. The **local values of $(P_A,P_B)$ decompose $P$** if for all local rewards $r_A,r_B$, whenever $Q$, $Q_A$, $Q_B$ solve the Bellman equations
--   $$Q=r_A\otimes e+e\otimes r_B+\gamma PQ,\qquad Q_A=r_A+\gamma P_AQ_A,\qquad Q_B=r_B+\gamma P_BQ_B,$$
--   then
--   $$Q=Q_A\otimes e+e\otimes Q_B.$$
--
--   For the marginalized chains $P^\pi_A,P^\pi_B$ of Eq. (2) this is Eq. (1) of the paper, as asserted in Theorem 1.
--
--   **Formalization Note** Vectors on the product are written entrywise through the pair index: $Q_A\otimes e+e\otimes Q_B$ at $p$ is `QA p.1 + QB p.2`.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (1), p.7, and Theorem 1, p.9

import Mathlib
import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

variable {SA SB : Type*} [Fintype SA] [Fintype SB]

/-- Eq. (1) with the local Q-values of the chains `P_A`, `P_B`: for all local rewards `r_A`,
`r_B`, the Bellman solutions `Q` of `(P, r_A ⊗ e + e ⊗ r_B)`, `Q_A` of `(P_A, r_A)` and `Q_B` of
`(P_B, r_B)` satisfy `Q = Q_A ⊗ e + e ⊗ Q_B`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (1), p.7, and the
last display of Theorem 1, p.9, with `Q^π_A = (I − γP^π_A)⁻¹ r_A`, p.8.

**Formalization Note.** The vector `Q_A ⊗ e + e ⊗ Q_B` is written entrywise through the pair
index, `Q_A p.1 + Q_B p.2`, and `r_A ⊗ e + e ⊗ r_B` as `rA p.1 + rB p.2`. -/
def LocalValuesDecompose (P : Matrix (SA × SB) (SA × SB) ℝ) (PA : Matrix SA SA ℝ)
    (PB : Matrix SB SB ℝ) (γ : ℝ) : Prop :=
  ∀ (rA : SA → ℝ) (rB : SB → ℝ) (Q : SA × SB → ℝ) (QA : SA → ℝ) (QB : SB → ℝ),
    IsBellmanQ P (fun p => rA p.1 + rB p.2) γ Q →
    IsBellmanQ PA rA γ QA →
    IsBellmanQ PB rB γ QB →
      ∀ p : SA × SB, Q p = QA p.1 + QB p.2

end MarkovEntanglementExact


