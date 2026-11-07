-- Prove2me | Definitions.Def_FermiGaussMix_gibbs
-- name    : FermiGaussMix_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:45.013462+00:00
-- url     : https://prove2.me/theorems/c0791578-ce6d-4b14-a143-ca587303e5d3
-- title:
--   The Gibbs state $\rho_\beta$ and nonnegative Gaussian operators
-- statement:
--   The Gibbs state of a Hamiltonian $H$ at inverse temperature $\beta$ is
--   $$
--   \rho_\beta=\frac{e^{-\beta H}}{\operatorname{Tr}e^{-\beta H}} .
--   $$
--   A nonnegative Gaussian operator is a nonnegative multiple $c\,\tau$ of an even fermionic Gaussian state $\tau$; the case $c=0$ is included, since the decomposition (B.63) allows a zero term.
--
--   **Formalization Note** Even Gaussian states are the published `FermiCap.Gaussian.IsEvenGaussian`, which contains the rank-deficient and pure states.
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eq. (A.13), p. 10; pp. 11, 14, 18

import Mathlib
import Definitions.Def_FermiCap_Gaussian_States

open scoped BigOperators
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- The Gibbs state `ρ_β = e^{-βH} / Tr e^{-βH}` of eq. (A.13), p.10 (Han, Zhao, Liu, arXiv:2609.35159v1). -/
noncomputable def gibbs {n : ℕ} (β : ℝ) (H : Op n) : Op n :=
  ((NormedSpace.exp ((-β : ℂ) • H)).trace)⁻¹ • NormedSpace.exp ((-β : ℂ) • H)

/-- A nonnegative Gaussian operator (pp.11, 14, Han, Zhao, Liu, arXiv:2609.35159v1): a nonnegative multiple of
an even Gaussian state.

**Formalization Note** The Gaussian state is the published `FermiCap.Gaussian.IsEvenGaussian`, which contains the
rank-deficient and pure states. `σ = 0` qualifies, as (B.63) needs ("Every nonzero `σ_z` … is therefore
Gaussian"). -/
def IsNonnegGaussian {n : ℕ} (σ : Op n) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∃ τ : Op n, IsEvenGaussian τ ∧ σ = (c : ℂ) • τ

end FermiGaussMix


