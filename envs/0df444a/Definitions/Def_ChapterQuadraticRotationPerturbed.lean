-- Prove2me | Definitions.Def_ChapterQuadraticRotationPerturbed
-- name    : ChapterQuadraticRotationPerturbed
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T05:05:39.912047+00:00
-- url     : https://prove2.me/theorems/73fb474f-1b5e-4fb4-bb1b-1b6d50cc8d4b
-- title:
--   Chapter QuadraticRotationPerturbed
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQuadraticRotationPerturbed.lean`): generated def bundle for ChapterQuadraticRotationPerturbed. See BookProof/ChapterQuadraticRotationPerturbed.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationPerturbed.lean

import Theorems.Thm_BookProof_QuadraticRotation_orthonormal_rotHermiteLp
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa

import Theorems.Thm_BookProof_QuadraticRotation_span_rotHermiteLp



import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterKatoRellichDeficiencyCore
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvBasis_apply
import Theorems.Thm_BookProof_QuadraticRotation_rotPoly_mulXPoly
import Theorems.Thm_BookProof_QuadraticRotation_rotPoly_momPoly
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coe
import Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_rotPoly
import Theorems.Thm_BookProof_HermiteRelative_quadOp_add_firstOrder_essentiallySelfAdjoint
import Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj_eigenvalues
import Theorems.Thm_BookProof_KatoRellich_symmetricOn_add
import Theorems.Thm_BookProof_HermiteRelative_foOp_symmetric
import Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_symmetric
import Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_essentiallySelfAdjoint


/-!
# The general inhomogeneous elliptic quadratic Hamiltonian

`BookProof.ChapterQuadraticRotationEsa` proves that for **every** real symmetric matrix `A`
the quadratic Hamiltonian

`H_A = ∑_{k,l} A_{kl} (π_k π_l + x_k x_l / 4)`,  `π_k = −i ∂/∂x_k`,

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`.
`BookProof.ChapterHermiteRelativeBound` proves that the *diagonal* Hamiltonian `H_c` with
strictly positive weights stays essentially self-adjoint after adding an arbitrary
**first-order** perturbation `B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)`, by a Kato–Rellich relative bound.

This module combines the two: for a **positive definite** real symmetric matrix `A` and
arbitrary real vectors `b, b'` the *inhomogeneous* operator

`H_A + ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)`

— a general elliptic quadratic form with cross terms, plus a general unbounded first-order
term — is essentially self-adjoint on the same core.  Neither the second-order part nor
the perturbation is diagonal, and the perturbation does not commute with `H_A`.

## The route

The first-order term is not diagonal in the rotated Hermite basis, so the eigenbasis
argument of `ChapterQuadraticRotationEsa` no longer applies directly.  Instead the
orthogonal substitution is upgraded to an honest **unitary** `rotU` of `L²(ℝᵈ)`: the
rotated Hermite functions are a Hilbert basis (`rotHermiteBasis`), and `rotU` is the
unitary carrying the plain Hermite basis onto it.  On the core it is the polynomial
substitution, `rotU_pgLp : rotU (p·G) = (p∘Oᵀ)·G`, so it preserves the core, carries
`H_c` onto `H_{O diag(c) Oᵀ}` and carries the first-order symbol with coefficient vectors
`b, b'` onto the one with `O b, O b'` (`rotPoly_foPoly`).  Essential self-adjointness is a
unitary invariant (`essentiallySelfAdjointOn_of_intertwine`), so the perturbed diagonal
theorem transfers.  Positive definiteness enters exactly once: it makes the eigenvalues of
`A` bounded below by a positive constant, which is the hypothesis of the Kato–Rellich
step.

## What is proved

* `rotHermiteBasis`, `rotU`, `rotU_hermiteMvLp`, `rotU_pgLp` — the rotation unitary of
  `L²(ℝᵈ)` and its action on the Gauss–polynomial core.
* `rotPoly_foPoly` — the first-order symbol transforms with the same matrix.
* `quadOpMat_add_firstOrder_essentiallySelfAdjoint` — the headline.
* `quadOpMat_add_firstOrder_symmetric` — the operator is symmetric on the core.
* `anisotropicOsc_add_linearPotential_essentiallySelfAdjoint` — the concrete corollary: an
  anisotropic harmonic oscillator with cross terms in a constant external field.
* `quadOpMat_stone_flow`, `quadOpMat_add_firstOrder_stone_flow` — the resulting complete
  unitary Schrödinger flows, via Stone's theorem.

## Boundaries

Positive definiteness of `A` is *not* removable by this route: in the indefinite case the
symbol of `H_A` vanishes on infinitely many multi-indices and no relative bound for the
first-order term holds (the same boundary as in `ChapterHermiteRelativeBound`).  The
unperturbed indefinite case is `quadOpMat_essentiallySelfAdjoint`; nothing here claims a
general potential bounded above by a quadratic (the Faris–Lavine class).
-/

namespace BookProof.QuadraticRotationPerturbed

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.SignFlip
open BookProof.HyperbolicQuadratic
open BookProof.HermiteRelative
open BookProof.QuadraticRotation
open BookProof.KatoRellich
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. The rotated Hermite functions as a Hilbert basis, and the rotation unitary -/

/-- The rotated product Hermite functions form a Hilbert basis of `L²(ℝᵈ)`. -/
def rotHermiteBasis {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) :
    HilbertBasis (Fin d →₀ ℕ) ℂ (L2d d) :=
  HilbertBasis.mk (orthonormal_rotHermiteLp hO)
    (by
      rw [span_rotHermiteLp hO]
      have hd := polyGaussCore_dense (d := d)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

@[simp] theorem rotHermiteBasis_apply {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (a : Fin d →₀ ℕ) : rotHermiteBasis hO a = rotHermiteLp O a := by
  rw [rotHermiteBasis, HilbertBasis.coe_mk]

/-- **The rotation unitary of `L²(ℝᵈ)`**: the unitary carrying the plain product Hermite
basis onto the rotated one. -/
def rotU {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) : L2d d ≃ₗᵢ[ℂ] L2d d :=
  (hermiteMvBasis (d := d)).repr.trans (rotHermiteBasis hO).repr.symm

theorem rotU_hermiteMvLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a : Fin d →₀ ℕ) :
    rotU hO (hermiteMvLp (d := d) a) = rotHermiteLp O a := by
  rw [rotU, LinearIsometryEquiv.trans_apply, ← hermiteMvBasis_apply,
    HilbertBasis.repr_self, HilbertBasis.repr_symm_single, rotHermiteBasis_apply]

/-- **The unitary is the polynomial substitution on the core.** -/
theorem rotU_pgLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p : MvPolynomial (Fin d) ℂ) : rotU hO (pgLp p) = pgLp (rotPoly O p) := by
  have key : ((rotU hO).toLinearEquiv.toLinearMap ∘ₗ (pgMap (d := d)))
      = (pgMap (d := d)) ∘ₗ (rotPoly O).toLinearMap := by
    apply LinearMap.ext_on (span_hermiteMv (d := d))
    rintro _ ⟨a, rfl⟩
    change rotU hO (pgLp (hermiteMv a)) = pgLp (rotPoly O (hermiteMv a))
    rw [pgLp_hermiteMv_eq, map_smul, rotU_hermiteMvLp, rotHermiteLp, smul_smul,
      mul_inv_cancel₀ (hermiteMvNorm_ne_zero a), one_smul]
  exact congrFun (congrArg (fun T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] L2d d => (T : _ → _)) key) p

theorem rotU_mem_core {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (v : polyGaussCore (d := d)) : rotU hO (v : L2d d) ∈ polyGaussCore (d := d) := by
  obtain ⟨p, hp⟩ := v.2
  rw [← hp]
  exact ⟨rotPoly O p, (rotU_pgLp hO p).symm⟩

/-! ## 2. The first-order symbol transforms with the same matrix -/

/-- The rotated coefficient vector `(O b)ₖ = ∑ᵢ O_{ki} bᵢ`. -/
def rotVec (O : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) : Fin d → ℝ :=
  fun k => ∑ i, O k i * b i

/-- **The first-order symbol transforms contravariantly with the same matrix**: the
substitution carries `∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` onto `∑ₖ ((Ob)ₖ xₖ + (Ob')ₖ πₖ)`. -/
theorem rotPoly_foPoly {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (b b' : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (foPoly b b' p) = foPoly (rotVec O b) (rotVec O b') (rotPoly O p) := by
  have hfo : ∀ (β β' : Fin d → ℝ) (q : MvPolynomial (Fin d) ℂ),
      foPoly β β' q
        = ∑ i, (((β i : ℝ) : ℂ) • mulXPoly i q + ((β' i : ℝ) : ℂ) • momPoly i q) := by
    intro β β' q
    simp [foPoly, LinearMap.sum_apply]
  have step : ∀ i : Fin d,
      rotPoly O (((b i : ℝ) : ℂ) • mulXPoly i p + ((b' i : ℝ) : ℂ) • momPoly i p)
        = ∑ k, (((O k i * b i : ℝ) : ℂ) • mulXPoly k (rotPoly O p)
            + ((O k i * b' i : ℝ) : ℂ) • momPoly k (rotPoly O p)) := by
    intro i
    rw [map_add, map_smul, map_smul, rotPoly_mulXPoly, rotPoly_momPoly hO, Finset.smul_sum,
      Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, smul_smul]
    push_cast
    ring_nf
  rw [hfo b b' p, map_sum, Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm,
    hfo (rotVec O b) (rotVec O b') (rotPoly O p)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]
  congr 1 <;>
    · congr 1
      rw [rotVec]
      push_cast
      ring

theorem rotVec_transpose {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (b : Fin d → ℝ) :
    rotVec O (rotVec Oᵀ b) = b := by
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  funext k
  simp only [rotVec, Matrix.transpose_apply]
  have : ∀ i : Fin d, O k i * ∑ j, O j i * b j = ∑ j, (O k i * O j i) * b j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_comm]
  have hj : ∀ j : Fin d, ∑ i, (O k i * O j i) * b j = (if k = j then (1 : ℝ) else 0) * b j := by
    intro j
    rw [← Finset.sum_mul]
    congr 1
    have h1 := congrFun (congrFun hOO k) j
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h1
  rw [Finset.sum_congr rfl fun j _ => hj j]
  simp

/-! ## 3. Transfer of the perturbed theorem -/

/-- The intertwining relation on the core:
`rotU (H_c + B_{b,b'}) = (H_{O diag(c) Oᵀ} + B_{Ob,Ob'}) rotU`. -/
theorem rotU_intertwine {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ)
    (b b' : Fin d → ℝ) (v : polyGaussCore (d := d)) :
    rotU hO ((quadOp c + foOp b b') v)
      = (quadOpMat (rotConj O c) + foOp (rotVec O b) (rotVec O b'))
          ⟨rotU hO (v : L2d d), rotU_mem_core hO v⟩ := by
  obtain ⟨p, hp⟩ := v.2
  have hv : (v : L2d d) = pgLp p := hp.symm
  have hvc : v = coreEquiv p := Subtype.ext hv
  have hUv : (⟨rotU hO (v : L2d d), rotU_mem_core hO v⟩ : polyGaussCore (d := d))
      = coreEquiv (rotPoly O p) := by
    refine Subtype.ext ?_
    change rotU hO (v : L2d d) = pgLp (rotPoly O p)
    rw [hv, rotU_pgLp]
  rw [hUv, hvc]
  simp only [LinearMap.add_apply, quadOp, quadOpMat, foOp, LinearMap.comp_apply,
    Submodule.subtype_apply, coreOp_coe, map_add, rotU_pgLp]
  rw [quadPolyMat_rotPoly hO, rotPoly_foPoly hO]

/-- **Essential self-adjointness of the rotated perturbed operator.** -/
theorem quadOpMat_rotConj_add_firstOrder_essentiallySelfAdjoint
    {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hc : ∀ i, c0 ≤ c i) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (quadOpMat (rotConj O c) + foOp b b') := by
  have hT := quadOp_add_firstOrder_essentiallySelfAdjoint c hc0 hc (rotVec Oᵀ b) (rotVec Oᵀ b')
  have htrans := essentiallySelfAdjointOn_of_intertwine (rotU hO)
    (quadOp c + foOp (rotVec Oᵀ b) (rotVec Oᵀ b'))
    (quadOpMat (rotConj O c) + foOp (rotVec O (rotVec Oᵀ b)) (rotVec O (rotVec Oᵀ b')))
    (rotU_mem_core hO) (fun v => rotU_intertwine hO c _ _ v) hT
  rwa [rotVec_transpose hO, rotVec_transpose hO] at htrans

/-- Positive definiteness gives a uniform positive lower bound on the eigenvalues. -/
theorem exists_lower_bound_eigenvalues {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ i, c0 ≤ hA.isHermitian.eigenvalues i := by
  classical
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
  · have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
    refine ⟨Finset.univ.inf' hne hA.isHermitian.eigenvalues, ?_,
      fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
    rw [Finset.lt_inf'_iff]
    exact fun i _ => hA.eigenvalues_pos i

/-- **The headline.**  For a positive definite real symmetric matrix `A` and arbitrary real
vectors `b, b'`, the inhomogeneous quadratic Hamiltonian

`H_A + ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)`,  `H_A = ∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)`,

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`.
Neither the quadratic part nor the perturbation is diagonal, and the perturbation is
unbounded and does not commute with `H_A`. -/
theorem quadOpMat_add_firstOrder_essentiallySelfAdjoint {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosDef) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOpMat A + foOp b b') := by
  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA.isHermitian
  obtain ⟨c0, hc0, hle⟩ := exists_lower_bound_eigenvalues hA
  rw [hAO]
  exact quadOpMat_rotConj_add_firstOrder_essentiallySelfAdjoint hO _ hc0 hle b b'

/-- The perturbed operator is symmetric on the core. -/
theorem quadOpMat_add_firstOrder_symmetric {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (quadOpMat A + foOp b b') :=
  symmetricOn_add (quadOpMat_symmetric hA) (foOp_symmetric b b')

/-- **A concrete corollary**: an anisotropic harmonic oscillator with cross terms, in a
constant external field.  Here `A` is any positive definite symmetric matrix and the
perturbation is multiplication by the linear function `x ↦ ⟨b, x⟩`. -/
theorem anisotropicOsc_add_linearPotential_essentiallySelfAdjoint
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) (b : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOpMat A + foOp b 0) :=
  quadOpMat_add_firstOrder_essentiallySelfAdjoint hA b 0

/-! ## 4. The unitary flows -/

/-- **The general quadratic Hamiltonian generates a complete unitary flow.**  For every
real symmetric matrix `A`, `H_A` is symmetric and essentially self-adjoint on the dense
Gauss–polynomial core, so it has a unique self-adjoint extension and Stone's theorem
turns that extension into the global unitary group solving the Schrödinger equation. -/
theorem quadOpMat_stone_flow {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (quadOpMat A) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense (quadOpMat_symmetric hA)
    (quadOpMat_essentiallySelfAdjoint hA)

/-- **The inhomogeneous elliptic quadratic Hamiltonian generates a complete unitary
flow.** -/
theorem quadOpMat_add_firstOrder_stone_flow {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef)
    (b b' : Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (quadOpMat A + foOp b b') T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense
    (quadOpMat_add_firstOrder_symmetric hA.isHermitian b b')
    (quadOpMat_add_firstOrder_essentiallySelfAdjoint hA b b')

end

end BookProof.QuadraticRotationPerturbed


