-- Prove2me | Definitions.Def_ChapterFockDiagonalGapChain
-- name    : ChapterFockDiagonalGapChain
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T13:08:54.923713+00:00
-- url     : https://prove2.me/theorems/31700bfb-87aa-4875-bd4d-04f1223401f6
-- title:
--   ChapterFockDiagonalGapChain
-- statement:
--   ChapterFockDiagonalGapChain

import Definitions.Def_ChapterScalaronFockGapChain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib


/-!
# Chapter FockDiagonalGapChain — the gap chain for a diagonal one-particle energy

`CONSOLIDATED_PLAN.md`, next step 3 of the top work package, asks for the abstract gap chain
to be run for the free sectors of the enclosure doctrine, whose one-particle operator is
*diagonal in the mode basis*: the one-particle energy of the mode `k` is a number `ω_k`.
`ChapterScalaronFockGapChain` did the constant case `ω_k = m`; this chapter does the general
diagonal case, which covers a genuine dispersion relation such as `ω_k = √(p_k² + m²)`.

## Deliverables

* `modeBasis b` — the finite-mode core `finiteModeDomain b` viewed as a free module with
  basis the (orthonormal) family `b`, and `modeBasis_coe`;
* `diagOnePart b w` — the diagonal one-particle operator `e_k ↦ ω_k e_k`, and the coordinate
  formula `diagOnePart_inner` for its sesquilinear form;
* `diagOnePart_symmetricOn`, `diagOnePart_quadForm_ge` — symmetry, and the one-particle form
  gap `⟪x, D x⟫ ≥ m‖x‖²` whenever every mode energy satisfies `ω_k ≥ m`: for a diagonal
  operator the form gap is *proved*, not assumed;
* **`diag_fock_gap`, `diag_fock_mass_gap`** — the resulting unconditional nested-Fock gap and
  mass gap of `dΓ(D)`;
* **`diag_fock_gap_of_field_perturbation`**, **`diag_fock_cubic_quartic_bounded_below`** — the
  gap under the unbounded, number-changing coupling `Φ(f)` with `2‖f‖ < m`, and
  semiboundedness with the single-mode cubic couplings and their normal-ordered quartic
  partners added;
* `freeDispersion m p k = √(p_k² + m²)` with `freeDispersion_ge`, and the free massive
  sector instance **`freeField_fock_mass_gap`** on the Hermite basis of `L²(ℝ)`: for any
  assignment of momenta to modes, the relativistic one-particle energy gives the outer Fock
  space the mass gap `m`.

## Honest boundary

The gap here is an honest theorem *about the model*: once the sector's one-particle energy
is diagonal with all mode energies at least `m`, the nested-Fock gap `m` and its stability
under the listed perturbations follow with no certificate and no Ritz data.  That a physical
sector reduces to such a diagonal energy is the modelling input of the enclosure doctrine
and is not proved here.  Massless dispersion gives `m = 0`, i.e. positivity and no gap.  The
cubic/quartic statement is semiboundedness with a negative constant, on single-mode terms.
The gauge-fixed Yang–Mills chain stays conditional on its one-particle form gap, and no mass
gap of the physical Yang–Mills Hamiltonian is claimed.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.FockDiagonalGapChain

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore BookProof.ScalaronFockGapChain
open Module

section General

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## 0. Two small coercion helpers -/


/-! ## 1. The finite-mode core as a free module -/

/-- The finite-mode core `finiteModeDomain b = span ℂ (range b)` of an orthonormal basis,
with the basis `b` itself as an algebraic basis. -/
def modeBasis (b : HilbertBasis ℕ ℂ F) : Basis ℕ ℂ (finiteModeDomain b) :=
  Basis.span b.orthonormal.linearIndependent

@[simp] theorem modeBasis_coe (b : HilbertBasis ℕ ℂ F) (i : ℕ) :
    ((modeBasis b i : finiteModeDomain b) : F) = b i :=
  Basis.coe_span_apply _ i


/-! ## 2. The diagonal one-particle operator -/

/-- **The diagonal one-particle operator** `e_k ↦ ω_k e_k` on the finite-mode core: the
one-particle energy of a free sector with mode energies `ω`. -/
def diagOnePart (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) :
    finiteModeDomain b →ₗ[ℂ] finiteModeDomain b :=
  (modeBasis b).constr ℂ fun i => ((w i : ℝ) : ℂ) • modeBasis b i

@[simp] theorem diagOnePart_basis (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (i : ℕ) :
    diagOnePart b w (modeBasis b i) = ((w i : ℝ) : ℂ) • modeBasis b i :=
  (modeBasis b).constr_basis ℂ _ i


/-! ## 3. The chain -/


end General

/-! ## 4. The free massive sector -/

/-- **The relativistic one-particle energy** `ω_k = √(p_k² + m²)` of a free sector of mass
`m` whose mode `k` carries momentum `p k`. -/
def freeDispersion (m : ℝ) (p : ℕ → ℝ) (k : ℕ) : ℝ := Real.sqrt ((p k) ^ 2 + m ^ 2)


/-! ## 5. Axiom audit -/

section Audit


end Audit

end BookProof.FockDiagonalGapChain

end


