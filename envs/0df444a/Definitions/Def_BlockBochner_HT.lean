-- Prove2me | Definitions.Def_BlockBochner_HT
-- name    : BlockBochner_HT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:50.109689+00:00
-- url     : https://prove2.me/theorems/c590d48d-af9e-4384-8d95-ce4eefef4fd7
-- title:
--   $H_T=\bigcap_{i\notin T}W_i^\perp$
-- statement:
--   For $T\subseteq[n]$, $H_T=\bigcap_{i\notin T}W_i^\perp$, the vectors orthogonal to every discarded subspace. For spin systems these are the functions of the retained spins $X_T$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.2, p.21

import Mathlib

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **`H_T = ∩_{i∉T} W_i^⊥`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.2, p.21. -/
noncomputable def HT {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (T : Finset (Fin n)) : Submodule ℝ H :=
  ⨅ i ∈ (Tᶜ : Finset (Fin n)), (W i : Submodule ℝ H)ᗮ

end BlockBochner


