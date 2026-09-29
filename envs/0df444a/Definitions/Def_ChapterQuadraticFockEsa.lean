-- Prove2me | Definitions.Def_ChapterQuadraticFockEsa
-- name    : ChapterQuadraticFockEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-13T16:34:14.625817+00:00
-- url     : https://prove2.me/theorems/86713485-ea05-482c-bacf-b3ba6697c151
-- title:
--   Chapter ChapterQuadraticFockEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QuadraticFockEsa`, source chapter `BookProof/ChapterQuadraticFockEsa.lean`): Chapter ChapterQuadraticFockEsa
--
--   Generated def bundle for ChapterQuadraticFockEsa. See BookProof/ChapterQuadraticFockEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticFockEsa.lean

import Definitions.Def_ChapterHermiteBandCalculus
import Mathlib

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterYangMillsHermite

/-!
# The second quantization of a real quadratic Hamiltonian is essentially self-adjoint on the
# finite-occupation core

This chapter joins the two halves.  `BookProof.ChapterHermiteBandCalculus` shows that a real
quadratic Hamiltonian has a graded band matrix in the product Hermite basis;
`BookProof.ChapterGradedBandSchurEsa` shows that a graded band matrix passes the weighted
Schur gates.  What is missing is the **seam**: the matrix of the operator in the `ℕ`-indexed
product Hermite basis, and the identification of its entries with the band coefficients.

## What is proved

* `hermBasisN`, `hermBasisN_apply`, `finiteModeDomain_hermBasisN`, `coreRepHerm` — the
  product Hermite basis enumerated by `ℕ`, whose finite-mode domain is exactly the
  Gauss–polynomial core, presented as a `CoreRep`.
* `hermCol` — the matrix of a polynomial operator in that basis.
* `pgLp_hcomb`, `inner_hermiteMvLp_hcomb`, `symm_equiv_hermBasisN`, `hermCol_apply`,
  **`hermCol_eq_coef`** — the matrix element `⟪ψ_{e j}, T ψ_{e k}⟫` *is* the band
  coefficient `f_{e j}` of `T ψ_{e k}`.
* **`gradedBand_of_isBand2`** — hence a second-order band operator has a graded band matrix,
  with `D = 2` and the grading `deg k = |e k|`.
* **`dGamma_hermCol_essentiallySelfAdjointOn_core`** and
  **`dGamma_fqPoly_essentiallySelfAdjointOn_core`** — the headlines: for a symmetric
  second-order band operator, and in particular for the general real quadratic Hamiltonian
  `fqPoly P Q S b b'`, the second quantization `dΓ(H₁)` is essentially self-adjoint on the
  finite-occupation core of the Fock space over `L²(ℝᵈ)`.

The one-particle operator here is genuinely **unbounded** — a quadratic Hamiltonian has
matrix elements growing like the degree — so this is outside the reach of the unweighted
Schur gate of `BookProof.ChapterFockSchurEsa`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QuadFockEsa

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand
open BookProof.FockSecondQuantization BookProof.NavierStokesFlow
open BookProof.HermiteGalerkin BookProof.FarisLavine
open BookProof.YangMillsHermite BookProof.FullQuadratic
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

/-! ## The product Hermite basis, indexed by `ℕ` -/

theorem span_hermiteMvLp_comp (e : ℕ ≃ (Fin d →₀ ℕ)) :
    Submodule.span ℂ (Set.range (hermiteMvLp (d := d) ∘ e)) = polyGaussCore (d := d) := by
  rw [Set.range_comp, e.surjective.range_eq, Set.image_univ, span_hermiteMvLp]

/-- The product Hermite basis of `L²(ℝᵈ)`, enumerated by `ℕ`. -/
def hermBasisN (e : ℕ ≃ (Fin d →₀ ℕ)) : HilbertBasis ℕ ℂ (L2d d) :=
  HilbertBasis.mk (orthonormal_hermiteMvLp.comp e e.injective)
    (by
      rw [span_hermiteMvLp_comp e]
      have hd := polyGaussCore_dense (d := d)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

@[simp] theorem hermBasisN_apply (e : ℕ ≃ (Fin d →₀ ℕ)) (k : ℕ) :
    hermBasisN e k = hermiteMvLp (e k) := by
  rw [hermBasisN, HilbertBasis.coe_mk]
  rfl

theorem range_hermBasisN (e : ℕ ≃ (Fin d →₀ ℕ)) :
    Set.range (hermBasisN e) = Set.range (hermiteMvLp (d := d)) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨e k, by rw [hermBasisN_apply]⟩
  · rintro ⟨α, rfl⟩
    exact ⟨e.symm α, by rw [hermBasisN_apply]; simp⟩

theorem finiteModeDomain_hermBasisN (e : ℕ ≃ (Fin d →₀ ℕ)) :
    finiteModeDomain (hermBasisN e) = polyGaussCore (d := d) := by
  rw [finiteModeDomain, range_hermBasisN, span_hermiteMvLp]

/-- The finite-mode domain of the enumerated product Hermite basis is a `CoreRep`. -/
def coreRepHerm (e : ℕ ≃ (Fin d →₀ ℕ)) : CoreRep d (finiteModeDomain (hermBasisN e)) :=
  CoreRep.ofRangeEq (finiteModeDomain_hermBasisN e).symm

/-- The matrix of a polynomial operator in the enumerated product Hermite basis. -/
def hermCol (e : ℕ ≃ (Fin d →₀ ℕ)) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    ℕ → (ℕ →₀ ℂ) :=
  opCol (hermBasisN e) ((coreRepHerm e).op T)

/-! ## The matrix elements are the band coefficients -/











/-! ## A second-order band operator has a graded band matrix -/



/-! ## The headline -/





end

end BookProof.QuadFockEsa


