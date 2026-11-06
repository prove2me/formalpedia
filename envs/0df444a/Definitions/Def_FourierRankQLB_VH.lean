-- Prove2me | Definitions.Def_FourierRankQLB_VH
-- name    : FourierRankQLB_VH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:14.214103+00:00
-- url     : https://prove2.me/theorems/b78c1674-9344-4663-ae09-e362d614bb5c
-- title:
--   The space $V_r^{(n)}\mathbin{\widehat\otimes}H$ of Hilbert-valued amplitudes
-- statement:
--   For a complex Hilbert space $H$, the completed tensor product
--   $$
--   V_r^{(n)}\mathbin{\widehat\otimes}H\subseteq L^2(O(n),\mu_n;H),
--   $$
--   the closed span of the functions $Q\mapsto\chi_\Xi(Q)\,\xi$ with $\operatorname{rank}\Xi\le r$ and $\xi\in H$.
--
--   It contains the algorithm's state, viewed as a function of $Q$.
--
--   **Formalization Note** The completed tensor product is realized as this closure, since these pure tensors span a dense subspace of it.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.1, p.17

import Mathlib
import Definitions.Def_FourierRankQLB_chi
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory

namespace FourierRankQLB

/-- The space `V_r^{(n)} ⊗̂ H` of `H`-valued amplitudes, inside `L²(O(n), μ_n; H)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.1, p. 17.

**Formalization Note.** The completed Hilbert tensor product is realized as the `L²(O(n), μ_n; H)`
closure of the span of the pure tensors `χ_Ξ ⊗ ξ`, `rank Ξ ≤ r`, `ξ ∈ H`. Those pure tensors span a
dense subspace of `V_r ⊗̂ H`, so no tensor product is needed. -/
noncomputable def VH (n r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Submodule ℂ (Lp H 2 (haarO n)) :=
  (Submodule.span ℂ {f : Lp H 2 (haarO n) |
    ∃ (Ξ : Matrix (Fin n) (Fin n) ℝ) (ξ : H), Ξ.rank ≤ r ∧
      f =ᵐ[haarO n] fun Q => chi Ξ Q • ξ}).topologicalClosure

end FourierRankQLB


