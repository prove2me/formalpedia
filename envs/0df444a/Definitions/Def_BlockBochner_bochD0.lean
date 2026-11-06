-- Prove2me | Definitions.Def_BlockBochner_bochD0
-- name    : BlockBochner_bochD0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:44.620089+00:00
-- url     : https://prove2.me/theorems/11119b08-eb44-41e1-832d-cd6fa43b37b3
-- title:
--   The map $d_0:H\to\bigoplus_iW_i$, $d_0(f)_i=P_if$
-- statement:
--   Let $W_1,\dots,W_n$ be closed subspaces of a real Hilbert space $H$ with orthogonal projections $P_i$, and $H_1=\bigoplus_iW_i$ with $\langle(f_i),(g_i)\rangle_1=\sum_i\langle f_i,g_i\rangle$. Then $d_0:H\to H_1$, $d_0(f)_i=P_if$.
--
--   **Formalization Note** $H_1$ is the $\ell^2$ direct sum `PiLp 2`. The module also records the instance that a closed subspace of a complete space is complete.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, p.22

import Mathlib

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A closed subspace of a complete space is complete (used to form adjoints on `⊕ W_i`). -/
instance instCompleteSpaceClosedSubmodule (K : ClosedSubmodule ℝ H) :
    CompleteSpace (K : Submodule ℝ H) :=
  have : IsClosed ((K : Submodule ℝ H) : Set H) := K.isClosed'
  IsClosed.completeSpace_coe

/-- **The map `d₀ : H → ⊕_i W_i`, `d₀(f)_i = P_i f`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.3, p.22: `H₁ = ⊕_i W_i` with
`⟨(f_i), (g_i)⟩₁ = Σ_i ⟨f_i, g_i⟩_H`, and `d₀(f)_i = P_i f`.

**Formalization Note** `W_1, …, W_n` are closed subspaces (`ClosedSubmodule`), `H₁` is the `ℓ²`
direct sum `PiLp 2 (fun i => W i)`, and `P_i` is the orthogonal projection onto `W_i`. -/
noncomputable def bochD0 {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) :
    H →L[ℝ] PiLp 2 (fun i => (W i : Submodule ℝ H)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun i => (W i : Submodule ℝ H))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => (W i : Submodule ℝ H).orthogonalProjectionOnto)

end BlockBochner


