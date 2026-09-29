-- Prove2me | Definitions.Def_ChapterRitzCertificate
-- name    : ChapterRitzCertificate
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T12:23:15.85556+00:00
-- url     : https://prove2.me/theorems/2e80a768-4a12-435f-8901-44af9d955d27
-- title:
--   `CONSOLIDATED_PLAN.md` (top work package, status update 2026-08-28) leaves exactly two inputs on the route from the fini ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.RitzCertificate`, source chapter `BookProof/ChapterRitzCertificate.lean`).
--
--   `CONSOLIDATED_PLAN.md` (top work package, status update 2026-08-28) leaves exactly two inputs on the route from the finite Hashimoto/SIRK computation to a gap of the infinite selected operator:
--
--   1. **the finite certificate at each order** — that the order-`m` Ritz value lies in the order-`m` emitted band, and that the emitted bands *nest*; and 2. the free/diagonal (number-preserving) hypothesis in the `dΓ` lift.
--
--   This chapter closes item 1. Nothing here is assumed about the emitter: both halves are *constructed and proved*.
--
--   * **the band, from the computation** — the order-`m` Ritz vector `x m` produces a two-sided enclosure of the spectral edge by itself. Its Rayleigh quotient `θ = ⟪x, A x⟫` is an upper bound for `sInf (spectrum ℝ A)` (Rayleigh–Ritz), and its residual `ε = ‖A x − θ x‖` gives the matching **lower** bound through *Temple's inequality*
--
--   `sInf (spectrum ℝ A) ≥ θ − ε² / (β − θ)`,
--
--   valid whenever the rest of the spectrum lies above a known `β > θ`. Both endpoints are computable from the finite Krylov/Galerkin data, so `[θ − ε²/(β−θ), θ]` is exactly an *emitted* band, and it encloses the edge of the infinite operator by a theorem, not by assumption (`temple_lower_bound`, `temple_band_mem`).
--
--   * **nesting, for free** — an arbitrary family of enclosing bands is turned into a *nested* family by running intersection, `runLo = max_{k ≤ m} lo k`, `runHi = min_{k ≤ m} hi k`. The running family is nested by construction (`runBands_nested`), still encloses everything the original family enclosed (`mem_runBand`), and its widths are no larger (`runBand_width_le`), so they still vanish (`runBand_widths_tendsto_zero`).
--
--   Composing the two with the free outer-enclosure/`dΓ` lift of `ChapterFockOneParticleGap` gives the full-theory statement: the Ritz data first certify the inner one-particle edge, then the creation-left/annihilation-right outer Hamiltonian inherits the exact vacuum and non-vacuum gap. The finite certificate alone does not establish a standalone inner Hamiltonian ground state. `fock_mass_gap_of_temple_certificates`: from finite Rayleigh/residual data alone — no band hypothesis of any kind — a Fock mass gap for the free second quantization of the selected bounded operator.
--
--   Temple's inequality needs the *spectral separation* input `hsep`: the spectrum of `A` below `β` consists of the edge alone. That is the standard (and unavoidable) side condition of every rigorous two-sided eigenvalue enclosure — a residual bound alone can never separate a cluster. It is stated explicitly in every theorem and never derived. As everywhere in this development, `1.932` remains a certified truncated number and no mass gap of the physical Yang–Mills Hamiltonian is claimed.
--
--   Everything is `sorry`-free and introduces no axioms.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

import Definitions.Def_ChapterBandEnclosure
import Mathlib

import Mathlib

/-!
# Chapter RitzCertificate — the per-order finite certificate, derived

`CONSOLIDATED_PLAN.md` (top work package, status update 2026-08-28) leaves exactly two
inputs on the route from the finite Hashimoto/SIRK computation to a gap of the infinite
selected operator:

1. **the finite certificate at each order** — that the order-`m` Ritz value lies in the
   order-`m` emitted band, and that the emitted bands *nest*; and
2. the free/diagonal (number-preserving) hypothesis in the `dΓ` lift.

This chapter closes item 1.  Nothing here is assumed about the emitter: both halves are
*constructed and proved*.

* **the band, from the computation** — the order-`m` Ritz vector `x m` produces a
  two-sided enclosure of the spectral edge by itself.  Its Rayleigh quotient
  `θ = ⟪x, A x⟫` is an upper bound for `sInf (spectrum ℝ A)` (Rayleigh–Ritz), and its
  residual `ε = ‖A x − θ x‖` gives the matching **lower** bound through *Temple's
  inequality*

  `sInf (spectrum ℝ A) ≥ θ − ε² / (β − θ)`,

  valid whenever the rest of the spectrum lies above a known `β > θ`.  Both endpoints are
  computable from the finite Krylov/Galerkin data, so `[θ − ε²/(β−θ), θ]` is exactly an
  *emitted* band, and it encloses the edge of the infinite operator by a theorem, not by
  assumption (`temple_lower_bound`, `temple_band_mem`).

* **nesting, for free** — an arbitrary family of enclosing bands is turned into a *nested*
  family by running intersection, `runLo = max_{k ≤ m} lo k`, `runHi = min_{k ≤ m} hi k`.
  The running family is nested by construction (`runBands_nested`), still encloses
  everything the original family enclosed (`mem_runBand`), and its widths are no larger
  (`runBand_width_le`), so they still vanish (`runBand_widths_tendsto_zero`).

Composing the two with the free outer-enclosure/`dΓ` lift of
`ChapterFockOneParticleGap` gives the full-theory statement: the Ritz data first
certify the inner one-particle edge, then the creation-left/annihilation-right
outer Hamiltonian inherits the exact vacuum and non-vacuum gap. The finite
certificate alone does not establish a standalone inner Hamiltonian ground state.
`fock_mass_gap_of_temple_certificates`: from finite Rayleigh/residual data alone — no band
hypothesis of any kind — a Fock mass gap for the free second quantization of the selected
bounded operator.

## Honest boundary

Temple's inequality needs the *spectral separation* input `hsep`: the spectrum of `A` below
`β` consists of the edge alone.  That is the standard (and unavoidable) side condition of
every rigorous two-sided eigenvalue enclosure — a residual bound alone can never separate a
cluster.  It is stated explicitly in every theorem and never derived.  As everywhere in this
development, `1.932` remains a certified truncated number and no mass gap of the physical
Yang–Mills Hamiltonian is claimed.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

open Filter Topology

namespace BookProof.RitzCertificate

open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure

section Temple

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **Rayleigh quotient** of a vector: the energy `⟪x, A x⟫` (real for self-adjoint
`A`).  For a unit vector this is the order-`m` Ritz value the algorithm emits. -/
def rayleigh (A : F →L[ℂ] F) (x : F) : ℝ := (inner ℂ x (A x) : ℂ).re

/-- The **residual** of a vector: `‖A x − θ x‖` with `θ` its Rayleigh quotient.  This is the
second number the finite computation emits, and it is what drives the width of the
certified band. -/
def resid (A : F →L[ℂ] F) (x : F) : ℝ := ‖A x - ((rayleigh A x : ℝ) : ℂ) • x‖









/-- The spectral separation hypothesis of a two-sided enclosure: apart from the edge `l`,
the spectrum of `A` lies above `β`. -/
def SpectralSeparation (A : F →L[ℂ] F) (l b : ℝ) : Prop :=
  l ≤ b ∧ ∀ t ∈ spectrum ℝ A, t = l ∨ b ≤ t





end Temple

section TempleBand

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







end TempleBand

/-! ## 2. Nesting for free: the running intersection of the emitted bands -/

section RunningBands

/-- The running maximum of the emitted lower endpoints. -/
def runLo (lo : ℕ → ℝ) (m : ℕ) : ℝ :=
  (Finset.range (m + 1)).sup' (Finset.nonempty_range_add_one) lo

/-- The running minimum of the emitted upper endpoints. -/
def runHi (hi : ℕ → ℝ) (m : ℕ) : ℝ :=
  (Finset.range (m + 1)).inf' (Finset.nonempty_range_add_one) hi



















end RunningBands

/-! ## 3. The composition: finite Rayleigh/residual data ⟹ Fock mass gap -/

section Composition

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]





end Composition

end BookProof.RitzCertificate

end


