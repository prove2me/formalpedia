-- Prove2me | Definitions.Def_QPSpinParisi_energy
-- name    : QPSpinParisi_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:59.356473+00:00
-- url     : https://prove2.me/theorems/0887f063-2c61-49e7-81b0-c4a8b75f69c8
-- title:
--   The energy $\langle\psi|H|\psi\rangle$
-- statement:
--   The expectation $\langle\psi|H|\psi\rangle$ of a matrix $H$ in a vector $\psi$.
--
--   **Formalization Note** It is the real part of $\psi^\dagger H\psi$. For Hermitian $H$ the value is real, so nothing is lost.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.2), p.3 (PDF p.3)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The energy `⟨ψ|H|ψ⟩` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.2), p.3, PDF p.3).

**Formalization Note** It is the real part of `ψ† H ψ`. For Hermitian `H` the imaginary part is `0`, so the real
part loses nothing. -/
noncomputable def energy {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (H *ᵥ ψ)).re

end QPSpinParisi


