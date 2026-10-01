-- Prove2me | Definitions.Def_ChapterCPTHamiltonian
-- name    : ChapterCPTHamiltonian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:45:26.875395+00:00
-- url     : https://prove2.me/theorems/b9b632f4-5109-4e5c-ad29-84543bac6fa7
-- title:
--   Chapter CPTHamiltonian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCPTHamiltonian.lean`): generated def bundle for ChapterCPTHamiltonian. See BookProof/ChapterCPTHamiltonian.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCPTHamiltonian.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter "Real representations, CPT theorem …", §A.5 "Spinor frame and CPT theorem":
the most general Lorentz-covariant Dirac mass Hamiltonian and the mass-shell relation

This file formalizes the self-contained, finite-dimensional algebraic core of the
`book.tex` §A.5 subsection *"Spinor frame and CPT theorem"* (`book.tex` line ~6453).
There the author states that, in the space coordinates, the most general mass in the
Hamiltonian `iH` which is covariant under the connected component of the Lorentz group
is

  `iH = ∂⃗·γ⃗ γ⁰ + i γ⁰ m₁ + γ⁰ γ⁵ m₂`,

and observes that this operator is invariant under a parity–time reversal (PT)
transformation — "this is essentially the CPT theorem".

We work in the concrete `4×4` Majorana model of §A.3 (`BookProof.ChapterA3`), and
extract the two hard mathematical facts underlying the statement.  For a plane-wave
mode of spatial momentum `k⃗ = (k₀,k₁,k₂)` (so `∂ⱼ ↦ i kⱼ`), the operator becomes the
`4×4` complex matrix

  `D(k, m₁, m₂) = i (Σⱼ kⱼ γ^{j+1} γ⁰) + i m₁ γ⁰ + m₂ γ⁰ γ⁵`.

We prove:

* `diracHamOp_conjTranspose` — `Dᴴ = -D`, i.e. `iH` is **anti-Hermitian**, equivalently
  the Hamiltonian `H` is **Hermitian** (self-adjoint): the kinetic matrices `γʲγ⁰` are
  Hermitian and the two mass matrices `iγ⁰`, `γ⁰γ⁵` are anti-Hermitian, so `D = i H`
  with `H` self-adjoint.
* `diracHamOp_sq` — the **relativistic mass-shell / dispersion relation**
  `D² = -(k₀² + k₁² + k₂² + m₁² + m₂²) • 1`, i.e. the eigenvalues of `H` are
  `±√(k⃗² + m₁² + m₂²)`.  This is the algebraic reason the two mass parameters
  `m₁, m₂` are the "most general" covariant masses: the five matrices `γ¹γ⁰, γ²γ⁰,
  γ³γ⁰, iγ⁰, γ⁰γ⁵` are five **mutually anticommuting** operators whose squares are
  `+1, +1, +1, -1, -1`.

The underlying element-level Clifford identities are all reduced to the integer
matrix model of §A.3 and closed by `decide`; the surrounding physical modelling
(spinor frames, `Pin(3,1)` principal homogeneous space, field reparametrizations)
is left as prose.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix

namespace BookProof.ChapterCPTHamiltonian

open BookProof.ChapterA3

/-! ## 0. The Dirac `γ⁵` matrix -/

/-- The Dirac fifth matrix `γ⁵ = -i (iγ⁵)` (in line with `dgamma μ = -i (iγ^μ)`). -/
noncomputable def dgamma5 : Matrix (Fin 4) (Fin 4) ℂ := (-Complex.I) • mgamma5

/-! ## 1. Integer model of the five building-block matrices

All five matrices `γʲγ⁰`, `iγ⁰`, `γ⁰γ⁵` are *real* (they carry an even number of
`-i` factors), hence equal to the cast of an explicit integer matrix.  The whole
Clifford algebra of the five is closed by `decide` at the integer level. -/

/-- Kinetic block `γ^{j+1} γ⁰` at integer level: `γ^{j+1} γ⁰ = -(iγ^{j+1})(iγ⁰)`. -/
def KinZ (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℤ := -(mgammaZ j.succ * mgammaZ 0)

/-- First mass block `iγ⁰` at integer level (equals `iγ⁰ = mgammaZ 0`). -/
def MassAZ : Matrix (Fin 4) (Fin 4) ℤ := mgammaZ 0

/-- Second mass block `γ⁰γ⁵` at integer level: `γ⁰γ⁵ = -(iγ⁰)(iγ⁵)`. -/
def MassBZ : Matrix (Fin 4) (Fin 4) ℤ := -(mgammaZ 0 * mgamma5Z)





















/-! ## 2. The complex building blocks and the bridge to the integer model -/

/-- Kinetic block `γ^{j+1} γ⁰`. -/
noncomputable def Kin (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ := dgamma j.succ * dgamma 0

/-- First mass block `iγ⁰`. -/
noncomputable def MassA : Matrix (Fin 4) (Fin 4) ℂ := Complex.I • dgamma 0

/-- Second mass block `γ⁰γ⁵`. -/
noncomputable def MassB : Matrix (Fin 4) (Fin 4) ℂ := dgamma 0 * dgamma5









/-! ## 3. The Clifford algebra of the five blocks (complex level) -/















/-! ## 4. Hermiticity of the blocks -/







/-! ## 5. The Dirac Hamiltonian operator and its two headline properties -/

/-- The plane-wave form of the most general Lorentz-covariant Dirac mass Hamiltonian
`iH = ∂⃗·γ⃗ γ⁰ + i γ⁰ m₁ + γ⁰γ⁵ m₂` (with `∂ⱼ ↦ i kⱼ`):

`D(k, m₁, m₂) = i (Σⱼ kⱼ γ^{j+1}γ⁰) + i m₁ γ⁰ + m₂ γ⁰γ⁵`. -/
noncomputable def diracHamOp (k : Fin 3 → ℝ) (m1 m2 : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.I • (∑ j : Fin 3, (k j : ℂ) • Kin j)
    + (m1 : ℂ) • MassA
    + (m2 : ℂ) • MassB











/-
**The relativistic mass-shell / dispersion relation.**
`D² = -(k₀² + k₁² + k₂² + m₁² + m₂²) • 1`; the eigenvalues of the Hamiltonian `H` are
`±√(k⃗² + m₁² + m₂²)`, so `m₁, m₂` are exactly the covariant mass parameters.
-/


end BookProof.ChapterCPTHamiltonian


