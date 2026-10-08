-- Prove2me | Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
-- name    : ShadowTomography_QuantumLB_vnEntropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:49:29.53699+00:00
-- url     : https://prove2.me/theorems/f71fad81-b1f8-431b-9d35-5ad07ddc41ef
-- title:
--   Von Neumann entropy $S(\rho)$ in bits
-- statement:
--   For a Hermitian matrix $\rho$ with eigenvalues $\lambda_1,\dots,\lambda_N$ (with multiplicity), the **von Neumann entropy** in bits is
--
--   $$
--   S(\rho) := \sum_{x=1}^{N} \lambda_x \log_2\frac{1}{\lambda_x} = -\sum_{x=1}^{N}\lambda_x\log_2\lambda_x ,
--   $$
--
--   with the convention $0\log_2 0 = 0$. On a density operator it is the Shannon entropy of the spectrum; it ranges between $0$ (pure states) and $\log_2 N$ (the maximally mixed state).
--
--   **Formalization Note** Lean's `Real.logb 2 0 = 0` implements the convention $0\log 0=0$. On a non-Hermitian matrix the definition returns $0$; every statement of this mission applies it to density operators only, so that branch is never used.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 24, proof of Theorem 19 ("where S is von Neumann entropy"; first line of the display for S(σ_i))

import Mathlib

namespace ShadowTomography.QuantumLB

/-- Von Neumann entropy in bits, `S(ρ) = ∑ₓ λₓ log₂(1/λₓ) = −∑ₓ λₓ log₂ λₓ` over the
eigenvalues `λₓ` of a Hermitian `ρ` (with `0 log 0 = 0`, since `Real.logb 2 0 = 0`).
On a non-Hermitian matrix it is `0`; every use is on a density operator. -/
noncomputable def vnEntropy {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : ℝ :=
  if h : ρ.IsHermitian then -∑ x, h.eigenvalues x * Real.logb 2 (h.eigenvalues x) else 0

end ShadowTomography.QuantumLB


