-- Prove2me | Definitions.Def_FourierRankQLB_phase
-- name    : FourierRankQLB_phase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:44.202675+00:00
-- url     : https://prove2.me/theorems/445d123f-3b91-46c3-a59c-4a1a47475e8b
-- title:
--   The membership phase $\phi_{q,\tau}$
-- statement:
--   For $q\in\mathbb R^d$ and $\tau\in\mathbb R$, the sign-valued function of the hidden matrix
--   $$
--   \phi_{q,\tau}(Q)=(-1)^{\mathbf 1[q^TQq\le\tau]} .
--   $$
--   It equals $-1$ when the threshold test returns $1$. In the Hadamard basis of the answer bit, a membership query multiplies by this phase.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 4.2, p.26 and Eq. (95), p.49

import Mathlib
import Definitions.Def_FourierRankQLB_Od

open Matrix

namespace FourierRankQLB

/-- The membership phase `ϕ_{q,τ}(Q) = (-1)^{1[qᵀQq ≤ τ]}`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 4.2, p. 26 and Eq. (95), p. 49. -/
noncomputable def phase {d : ℕ} (q : Fin d → ℝ) (τ : ℝ) (Q : Od d) : ℂ :=
  if q ⬝ᵥ ((Q : Matrix (Fin d) (Fin d) ℝ) *ᵥ q) ≤ τ then -1 else 1

end FourierRankQLB


