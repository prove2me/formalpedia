-- Prove2me | Definitions.Def_ChapterSmDiracSpinor
-- name    : ChapterSmDiracSpinor
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:07:23.205244+00:00
-- url     : https://prove2.me/theorems/1d45a92c-ecf7-4440-9a9f-76c7416d1794
-- title:
--   Chapter SmDiracSpinor
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmDiracSpinor.lean`): generated def bundle for ChapterSmDiracSpinor. See BookProof/ChapterSmDiracSpinor.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmDiracSpinor.lean

import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmDiracYukawa
import Mathlib


/-!
# The spinor Dirac operator, second quantized on the CAR algebra

`BookProof.ChapterSmDiracYukawa` puts a *general* Hermitian one-particle matrix on the CAR
algebra.  This module supplies the **concrete Dirac one-particle matrix** with its spinor
structure, taken from the `4 × 4` Majorana model already in the project
(`BookProof.ChapterCPTHamiltonian`, which formalizes `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂` and its
mass-shell identity), and second quantizes it.

## What is proved

* `diracOneParticle` — the plane-wave Dirac Hamiltonian matrix `H(k, m₁, m₂) = −i D(k,m₁,m₂)`
  on the four spinor components, with
  `diracOneParticle_hermitian` — it is Hermitian, so the Dirac sector is a legitimate input
  to the fermionic machinery;
* `diracOneParticle_sq` — the **dispersion relation** `H² = (k² + m₁² + m₂²)·1`;
* `diracOneParticle_eigenvalue_sq` — hence every eigenvalue satisfies `μ² = k² + m₁² + m₂²`:
  the relativistic energies `±√(k² + m₁² + m₂²)` (a *one-particle* spectral statement);
* `diracFieldHam` — its second quantization `Σ_{A,B} H_{AB} a†_A a_B` on the fermionic Fock
  space of the four spinor modes, `diracFieldHam_symmetric`;
* `dirac_field_esa` — essential self-adjointness of the second-quantized Dirac operator,
  through the three Faris–Lavine hypotheses of `BookProof.ChapterSmDiracYukawa`.

## Honest boundary

One plane-wave mode with its four spinor components: this is the spinor structure of the
Dirac operator, not the full field over all momenta, and not the covariant derivative `D`
with its gauge connection.  The colour/flavour and gauge structure enters only through the
one-particle matrix, which is an input here.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmDiracSpinor

open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

/-- **The one-particle Dirac Hamiltonian matrix** of a plane-wave mode: `H = −i D`, where
`D = iH` is the anti-Hermitian operator of `BookProof.ChapterCPTHamiltonian`. -/
def diracOneParticle (k : Fin 3 → ℝ) (m1 m2 : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-Complex.I) • diracHamOp k m1 m2







/-! ## The second quantization -/



/-- **The second-quantized Dirac operator** `Σ_{A,B} H_{AB} a†_A a_B` on the fermionic Fock
space of the four spinor modes. -/
def diracFieldHam (k : Fin 3 → ℝ) (m1 m2 : ℝ) : FermiFock 4 →ₗ[ℂ] FermiFock 4 :=
  fermiBilin (diracOneParticle k m1 m2)





end

end BookProof.SmDiracSpinor


