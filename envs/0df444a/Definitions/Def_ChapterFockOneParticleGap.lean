-- Prove2me | Definitions.Def_ChapterFockOneParticleGap
-- name    : ChapterFockOneParticleGap
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T10:50:47.240301+00:00
-- url     : https://prove2.me/theorems/3e5cf3d8-4b1c-4d44-966e-8a3fa3670def
-- title:
--   /-! Interpretation convention: this module proves facts about the inner one-particle operator and their lift. The physic ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.FockOneParticleGap`, source chapter `BookProof/ChapterFockOneParticleGap.lean`).
--
--   /-! Interpretation convention: this module proves facts about the inner one-particle operator and their lift. The physical final Hamiltonian in QYM, QED, QG, and NS is the outer creation-left/annihilation-right enclosure of that operator. Hence inner squeezed states are not full-theory grounds; the outer vacuum is killed by the rightmost outer annihilator.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterSirkCertifiedGap
import Definitions.Def_ChapterSirkRitzSpectrum
import Mathlib

import Mathlib

/-!
# Chapter FockOneParticleGap — the one-particle edge and its free `dΓ` lift

/-!
Interpretation convention: this module proves facts about the inner one-particle
operator and their lift. The physical final Hamiltonian in QYM, QED, QG, and NS
is the outer creation-left/annihilation-right enclosure of that operator. Hence
inner squeezed states are not full-theory grounds; the outer vacuum is killed by
the rightmost outer annihilator.
-/!

`CONSOLIDATED_PLAN.md`, top work package ("Hashimoto observable to the real-Hamiltonian
gap"), asks for the composition that is genuinely missing between the finite Hashimoto/SIRK
certificate and a *Fock* mass gap:

* the **one-particle** observable, its strict positivity `h₊ ≥ μ I`, and the free
  number-operator shift `dΓ(h₊) = dΓ(h − E₀I) + μ N`;
* the **nested-band** conclusion: certified intervals with vanishing widths that all
  enclose the lowest positive one-particle energy of one *fixed* operator determine that
  energy, and a single interval whose lower end is `≥ μ` already forces `λ₁ ≥ μ`;
* the **free `dΓ` lift**: the vacuum has energy `0`, every non-vacuum finite-particle
  state has energy at least the lowest one-particle energy, and a one-particle creation
  attains it — so the Fock gap *is* the one-particle edge.

Everything is proved in the algebraic Fock space `FockAlg = Conf →₀ ℂ` of
`BookProof.FockSecondQuantization`, for the **free** (number-preserving, diagonal in the
one-particle eigenbasis) one-particle Hamiltonian: `diagCol e` is the one-particle matrix
with eigenvalues `e k`, i.e. the matrix of `h₊` in a basis that diagonalizes it.  That is
exactly the "free outer particles" hypothesis of the plan; it is stated explicitly
everywhere and nothing here applies to pair creation or other interacting terms.

## Deliverables

* `dGamma_diagCol_single`, `dGamma_diagCol_apply` — `dΓ(h₊)` is diagonal on
  configurations, with eigenvalue the configuration energy `Σ_k β_k e_k`;
* `dGamma_diagCol_vac`, `numberOp_vac` — `dΓ(h₊) Ω = 0` and `N Ω = 0`;
* `dGamma_diagCol_one_particle`, `fock_energy_one_particle` — `a†(e_k) Ω` is an
  eigenvector of energy `e k`, so the one-particle energies really are Fock energies;
* `dGamma_diagCol_shift` — the free number-operator shift
  `dΓ(h + μ) = dΓ(h) + μ N`;
* `fock_gap_quadForm`, `fock_gap_of_one_particle_gap` — the **free `dΓ` lift**: with
  `h₊ ≥ μ I ≥ 0`, the vacuum has energy `0` and every vacuum-orthogonal finite-particle
  state has energy at least `μ‖·‖²`;
* `band_endpoints_tendsto`, `le_of_band` — the nested-band conclusion for the
  one-particle edge;
* `fock_mass_gap_of_certified_bands` — the composition of the two, and
  `qcdG2M4_fock_gap_of_one_particle_enclosure` — its instance for the emitted
  `g = 2, m = 4` certificate value `1.932`.

## Honest boundary

No mass gap of the physical Yang–Mills Hamiltonian is claimed.  `1.932` remains a
*certified truncated* number.  What is proved here is the implication

  *(the certified bands enclose the lowest positive one-particle energy of the fixed
  selected operator, and one band has lower end `≥ μ > 0`)*
  ⟹ *(the free second quantization has vacuum energy `0` and every vacuum-orthogonal
  finite-particle state has energy `≥ μ`)*,

together with the exact identification of the Fock gap with the one-particle edge in the
free case.  The enclosure hypothesis itself — that the finite certificate brackets the
one-particle edge of the *infinite* selected operator — is an analytic obligation that
appears here as a hypothesis, never as a conclusion.
-/

noncomputable section

namespace BookProof.FockOneParticleGap

open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

/-! ## 1. The free (diagonal) one-particle Hamiltonian -/

/-- The one-particle matrix of an operator diagonal in the chosen basis, with eigenvalues
`e k`: `⟪e_j, h e_k⟫ = δ_{jk} e_k`.  This is `h₊` written in a basis diagonalizing it. -/
def diagCol (e : ℕ → ℝ) : ℕ → (ℕ →₀ ℂ) := fun k => Finsupp.single k ((e k : ℝ) : ℂ)

/-- The one-particle matrix of the identity, whose second quantization is the number
operator `N`. -/
def numberCol : ℕ → (ℕ →₀ ℂ) := diagCol (fun _ => 1)

/-- The total number of quanta of a configuration. -/
def confNumber (β : Conf) : ℕ := ∑ k ∈ β.support, β k

/-- The energy of a configuration for the diagonal one-particle Hamiltonian:
`E(β) = Σ_k β_k e_k`. -/
def confEnergy (e : ℕ → ℝ) (β : Conf) : ℝ := ∑ k ∈ β.support, (β k : ℝ) * e k

/-- The Fock vacuum, as an element of the algebraic Fock space. -/
def vac : FockAlg := Finsupp.single (0 : Conf) (1 : ℂ)

















/-! ## 2. The second quantization of a diagonal one-particle Hamiltonian -/

















/-! ## 3. The Fock gap of a free second quantization -/















/-! ### The Fock gap *is* the one-particle edge -/

/-- The set of energies of the non-vacuum configurations. -/
def nonvacuumEnergies (e : ℕ → ℝ) : Set ℝ :=
  {x | ∃ β : Conf, β ≠ 0 ∧ x = confEnergy e β}





/-! ## 4. Nested certified bands determine the one-particle edge -/





/-! ## 5. The composition: certified bands ⟹ Fock mass gap (free case) -/







/-! ## 6. Reading a parity-labelled certificate as a one-particle enclosure

The emitted certificate is labelled by parity sectors.  Using it for the `dGamma` theorems
above requires the **representation translation**: that the even sector ground value is the
outer-vacuum energy and the odd sector ground value is the lowest one-particle energy.  That
translation is a property of the concrete truncation, not a generic fact, so it appears
below as two explicit hypotheses; what the theorem adds is that *once they hold*, the
certified parity lower bound is a lower bound for the one-particle edge, and may then be
fed to `fock_mass_gap_of_certified_bands`. -/

section ParityTranslation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open BookProof.SirkCertifiedGap



end ParityTranslation

/-! ## 7. From the spectral edge of an actual one-particle operator to the Fock gap

The sections above take the one-particle data as the sequence of eigenvalues `e`.  This
section starts instead from a *bounded self-adjoint operator* `A` on a Hilbert space with a
Hilbert basis of eigenvectors — the situation the shift-inverted Hashimoto/SIRK route
produces — and reads its eigenvalues off the basis.  The certified bands are then required
to enclose `sInf (spectrum ℝ A)`, the actual spectral edge, and the conclusion is the Fock
gap of the free second quantization. -/

section OperatorEdge

open BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







end OperatorEdge

end BookProof.FockOneParticleGap


