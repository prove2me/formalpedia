-- Prove2me | Definitions.Def_OptimalSignalEnsembles_avgState
-- name    : OptimalSignalEnsembles_avgState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:00.213359+00:00
-- url     : https://prove2.me/theorems/3b709552-f197-45d8-89a0-b52943099aeb
-- title:
--   Average state $\bar\rho=\sum_k p_k\rho_k$ of a finite ensemble
-- statement:
--   Let $\mathbb C^d$ be a finite-dimensional Hilbert space and consider a finite family of weights $p_1,\dots,p_n \in \mathbb R$ and matrices $\rho_1,\dots,\rho_n \in M_d(\mathbb C)$. The **average state** of the ensemble is
--
--   $$\bar\rho \;=\; \sum_{k=1}^n p_k\,\rho_k .$$
--
--   When the $p_k$ form a probability vector and the $\rho_k$ are density matrices, $\bar\rho$ is the density operator describing the system prepared in $\rho_k$ with probability $p_k$. It is the state whose entropy enters the Holevo quantity and the reference point of every relative-entropy "distance" in the paper.
--
--   **Formalization Note** The ensemble is indexed by $\mathrm{Fin}\,n$; the real weights are cast to $\mathbb C$. No condition on the weights or matrices is built into the definition.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 1, p.1; eq. (11), p.6

import Mathlib

namespace OptimalSignalEnsembles

/-- The **average state** `ρ̄ = ∑ₖ pₖ ρₖ` of a finite ensemble with weights `p : Fin n → ℝ`
and members `ρ : Fin n → Matrix d d ℂ`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 1, p.1
("an average density operator ρ = Σ_k p_k ρ_k"); also (11), p.6.

**Formalization Note.** An ensemble with `n` members is indexed by `Fin n`; the real weights
are cast to `ℂ` to scale the matrices. No condition on `p` or `ρ` is built in. -/
noncomputable def avgState {d : Type} [Fintype d] {n : ℕ} (p : Fin n → ℝ)
    (ρ : Fin n → Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ k, (p k : ℂ) • ρ k

end OptimalSignalEnsembles


