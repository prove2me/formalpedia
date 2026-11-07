-- Prove2me | Definitions.Def_FermiHubbardMix_gibbs
-- name    : FermiHubbardMix_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:29.770633+00:00
-- url     : https://prove2.me/theorems/51d2795c-d50a-48c2-a356-eb2f1b541f45
-- title:
--   Gibbs state $e^{-\beta H}/\operatorname{tr}e^{-\beta H}$, Heisenberg evolution, fermionic density operators
-- statement:
--   For an operator $H$ and $\beta\in\mathbb R$ the **Gibbs state** is
--   $$
--   \sigma=\frac{e^{-\beta H}}{\operatorname{tr}(e^{-\beta H})},
--   $$
--   with the trace on the full Fock space. The **Heisenberg evolution** of an operator $B$ is $e^{iHt}Be^{-iHt}$. A **fermionic density operator** (Definition 11.5) is a positive semidefinite even operator $\rho$ with $\operatorname{tr}\rho=1$.
--
--   The Gibbs state is the target of the sampler; the mixing theorems are stated for every fermionic density operator as initial state.
--
--   **Formalization Note** Exponentials are matrix exponentials. Evenness of $\rho$ is part of the definition (fermion-parity superselection, Remark 11.6).
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 11.5, p.52; Theorem 15.1, p.68; eq. (17), p.59

import Mathlib
import Definitions.Def_FermiHubbardMix_parityOp
open scoped BigOperators ComplexOrder
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- The Gibbs state `σ = e^{-βH} / tr(e^{-βH})` (arXiv:2604.08408, held version sha256 055b8f8f…,
Theorem 15.1, p.68; §1.1, p.3). The trace is the ordinary trace on the full Fock space.

**Formalization Note** `e^{-βH}` is the matrix exponential `NormedSpace.exp`. -/
def gibbs {N : ℕ} (β : ℝ) (H : Op N) : Op N :=
  ((NormedSpace.exp (-(β : ℂ) • H)).trace)⁻¹ • NormedSpace.exp (-(β : ℂ) • H)

/-- The Heisenberg evolution `e^{iHt} B e^{-iHt}` (arXiv:2604.08408, held version sha256
055b8f8f…, eq. (17), p.59). -/
def heis {N : ℕ} (H : Op N) (t : ℝ) (B : Op N) : Op N :=
  NormedSpace.exp ((Complex.I * t) • H) * B * NormedSpace.exp (-(Complex.I * t) • H)

/-- **Definition 11.5 (Fermionic density operator)** (arXiv:2604.08408, held version sha256
055b8f8f…, p.52): a positive semidefinite even operator `ρ` with `tr ρ = 1`. -/
def IsDensity {N : ℕ} (ρ : Op N) : Prop := ρ.PosSemidef ∧ IsEven ρ ∧ ρ.trace = 1

end FermiHubbardMix


