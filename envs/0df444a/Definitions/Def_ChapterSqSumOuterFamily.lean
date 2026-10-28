-- Prove2me | Definitions.Def_ChapterSqSumOuterFamily
-- name    : ChapterSqSumOuterFamily
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-24T12:31:54.410838+00:00
-- url     : https://prove2.me/theorems/2c3aff09-f447-48fd-9b0e-f5ce22f21579
-- title:
--   The Lean 4 theorem `ab_nonneg` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSqSumOuterFamily.lean`): generated def bundle for ChapterSqSumOuterFamily. See BookProof/ChapterSqSumOuterFamily.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqSumOuterFamily.lean

import Theorems.Thm_BookProof_SqSumFarisLavine_norm_sqSumOp_le

import Theorems.Thm_BookProof_SqSumFarisLavine_potFun_le_of_schur

import Theorems.Thm_BookProof_QgOuterFockFL_harmFried_op_core

import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_esa_self
import Theorems.Thm_BookProof_QgOuterFock_sqSumOp_symmetricOn
import Theorems.Thm_BookProof_QgOuterFock_sqSumOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_SqSumFarisLavine_sum_gradFun_sq_le_of_schur
import Theorems.Thm_BookProof_SqSumFarisLavine_commForm_sqSumOp_le
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_symmetricOn
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_norm_le


/-!
# Uniform kinetic-plus-squares families on an outer Fock space of arbitrary fibre dimension

`BookProof.ChapterQgOuterFockInteractionFL` proves Faris–Lavine essential self-adjointness
for a uniform family of kinetic-plus-squares Hamiltonians on the *quantum-gravity* outer
Fock space `⊕ₙ L²(ℝ^{84n})`: the fibre dimension `84` is hard-wired there.  Nothing in the
argument uses the number `84`, so this module repeats the development with the sequence of
sector dimensions as a parameter.  It is the instrument the Navier–Stokes thread needs
(`BookProof.ChapterNsOuterFockFarisLavine`, fibre dimension `18` per parcel), and it
specialises back to the gravity statement at `dim n = n * 84`.

## The data

A `SqFamily` is

* a sequence of sector dimensions `dim : ℕ → ℕ` — the number of field-space coordinates of
  the `n`-particle sector;
* for every `n` a finite index type `R n` of linear forms, a real signature
  `kap n : Fin (dim n) → ℝ` and coefficient vectors `vv n : R n → Fin (dim n) → ℝ`,
  defining the sector Hamiltonian

  `H_n = ½ Σ_I kap_I π_I² + ½ Σ_r L_r²`,  `L_r = Σ_I vv_{rI} x_I`

  on the Gauss–polynomial core of `L²(ℝ^{dim n})` (`BookProof.QgOuterFock.sqSumOp`);
* three **uniform** bounds: `|kap n I| ≤ km`, the row bound `Σ_I |vv n r I| ≤ a` and the
  column bound `Σ_r |vv n r I| ≤ b`, with `km`, `a`, `b` independent of `n`.

No structural restriction is placed on the linear forms: a form may mix the coordinates of
arbitrarily many different particles, so the Hamiltonian need not be a sum of one-particle
operators.

## What is proved

* `outerFock`, `outerCore`, `outerCore_dense`, `outerComparison`, `outerFriedDom`,
  `outerCore_le_friedDom` — the outer Fock space of the dimension sequence, its
  finite-particle core, and the lifted Friedrichs extension of the positive one-particle
  operator `N₁ = −Δ + ‖x‖²/4` as a Faris–Lavine comparison operator on it;
* `SqFamily.secHam`, `secHam_symmetricOn`, `secHam_essentiallySelfAdjointOn` — the sector
  Hamiltonians;
* `SqFamily.flK`, `SqFamily.flc`, `secHam_norm_le`, `secHam_commForm_le` — the two
  Faris–Lavine inequalities with constants `flK = 3km/2 + 4ab` and `flc = km/2 + 2ab`,
  **uniform in the particle number**;
* `SqFamily.outerHam`, `outerHam_symmetricOn`, `outerHam_esa` — the Hamiltonian on the
  finite-particle core;
* `SqFamily.secExt` — the sector Hamiltonians extended from the Gauss–polynomial core to
  the whole domain of the sector comparison operator;
* **`SqFamily.esa_farisLavine`** — the headline: essential self-adjointness on the domain
  of the lifted comparison operator, together with the statement that the operator so
  realized extends `outerHam` on the finite-particle core.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SqSumOuterFamily

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

/-! ## 1. The outer Fock space of a sequence of sector dimensions -/

variable (dim : ℕ → ℕ)

/-- **The outer Fock space** of a sequence of sector dimensions: the `ℓ²`-direct sum
`⊕ₙ L²(ℝ^{dim n})`. -/
abbrev outerFock : Type := lp (fun n : ℕ => L2d (dim n)) 2

/-- The finite-particle core: the algebraic direct sum of the sector Gauss–polynomial
cores. -/
def outerCore : Submodule ℂ (outerFock dim) :=
  dsCore (fun n : ℕ => polyGaussCore (d := dim n))

theorem outerCore_dense :
    Dense ((outerCore dim : Submodule ℂ (outerFock dim)) : Set (outerFock dim)) :=
  dsCore_dense fun _ => polyGaussCore_dense

/-- **The lifted comparison operator** `dΓ(N₁)`, `N₁ = −Δ + ‖x‖²/4`, in its Friedrichs
realization: positive, self-adjoint, and with `N + 1` onto the outer Fock space. -/
def outerComparison : Comparison (outerFock dim) :=
  dsComparison (fun n : ℕ => harmFried (dim n))

/-- The domain of the lifted comparison operator. -/
abbrev outerFriedDom : Submodule ℂ (outerFock dim) := (outerComparison dim).dom

/-- The lifted comparison operator on the outer Fock space. -/
abbrev outerFriedN : outerFriedDom dim →ₗ[ℂ] outerFock dim := (outerComparison dim).op

theorem outerFriedN_symmetricOn : SymmetricOn (outerFriedDom dim) (outerFriedN dim) :=
  (outerComparison dim).sym

theorem outerFriedN_quadForm_nonneg (x : outerFriedDom dim) :
    0 ≤ quadForm (outerFriedN dim) x := (outerComparison dim).pos x

/-- `N + 1` is onto the outer Fock space. -/
theorem outerFriedN_surj (f : outerFock dim) :
    ∃ x : outerFriedDom dim, outerFriedN dim x + (x : outerFock dim) = f :=
  (outerComparison dim).surj f

/-- The lifted comparison operator is essentially self-adjoint on its own domain. -/
theorem outerFriedN_esa : EssentiallySelfAdjointOn (outerFriedDom dim) (outerFriedN dim) :=
  (outerComparison dim).esa_self

set_option maxHeartbeats 1600000 in
-- the lifted domain is built from the Friedrichs completion, so unfolding it is costly
/-- The finite-particle core sits inside the domain of the lifted comparison operator. -/
theorem outerCore_le_friedDom : outerCore dim ≤ outerFriedDom dim := by
  intro x hx
  refine ⟨fun n => polyGaussCore_le_harmFriedDom (dim n) (hx.2 n), ?_⟩
  have hfun : (fun n : ℕ => opTot (harmFried (dim n)).op ((x : outerFock dim) n))
      = fun n : ℕ => (QgOuterFockFL.harmCore ⟨(x : outerFock dim) n, hx.2 n⟩ : L2d (dim n)) := by
    funext n
    rw [opTot_of_mem _ (polyGaussCore_le_harmFriedDom (dim n) (hx.2 n)),
      harmFried_op_core (dim n) ⟨(x : outerFock dim) n, hx.2 n⟩]
  rw [hfun]
  refine memLp_of_finite_support (Set.Finite.subset hx.1 fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h0
  refine hn ?_
  have hz : (⟨(x : outerFock dim) n, hx.2 n⟩ : polyGaussCore (d := dim n)) = 0 :=
    Subtype.ext h0
  rw [hz, map_zero]

/-! ## 2. Uniform families -/

/-- **A uniform family of kinetic-plus-squares Hamiltonians on the sectors of an outer Fock
space.**  The `n`-particle Hamiltonian is `½ Σ_I kap_I π_I² + ½ Σ_r L_r²` with `L_r` the
linear form of coefficient vector `vv n r`; the three bounds `km`, `a`, `b` are uniform in
the particle number `n`. -/
structure SqFamily where
  /-- The sequence of sector dimensions. -/
  dim : ℕ → ℕ
  /-- The index type of the linear forms of the `n`-particle sector. -/
  R : ℕ → Type
  [finR : ∀ n, Fintype (R n)]
  /-- The signature of the kinetic term of the `n`-particle sector. -/
  kap : ∀ n : ℕ, Fin (dim n) → ℝ
  /-- The coefficient vectors of the linear forms of the `n`-particle sector. -/
  vv : ∀ n : ℕ, R n → Fin (dim n) → ℝ
  /-- The uniform bound on the signature. -/
  km : ℝ
  /-- The uniform row (`ℓ¹`-per-form) bound. -/
  a : ℝ
  /-- The uniform column (`ℓ¹`-per-coordinate) bound. -/
  b : ℝ
  km_nonneg : 0 ≤ km
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  kap_le : ∀ (n : ℕ) (I : Fin (dim n)), |kap n I| ≤ km
  row_le : ∀ (n : ℕ) (r : R n), ∑ I : Fin (dim n), |vv n r I| ≤ a
  col_le : ∀ (n : ℕ) (I : Fin (dim n)), ∑ r : R n, |vv n r I| ≤ b

attribute [instance] SqFamily.finR

namespace SqFamily

variable (F : SqFamily)

/-- The relative-bound constant of the family. -/
def flK : ℝ := 3 / 2 * F.km + 4 * (F.a * F.b)

/-- The Faris–Lavine commutator constant of the family. -/
def flc : ℝ := F.km / 2 + 2 * (F.a * F.b)

theorem ab_nonneg : 0 ≤ F.a * F.b := mul_nonneg F.a_nonneg F.b_nonneg

theorem flK_nonneg : 0 ≤ F.flK := by
  have h := F.ab_nonneg
  have := F.km_nonneg
  rw [flK]; linarith

theorem flc_nonneg : 0 ≤ F.flc := by
  have h := F.ab_nonneg
  have := F.km_nonneg
  rw [flc]; linarith

/-- **The `n`-particle Hamiltonian of the family**, on the Gauss–polynomial core of
`L²(ℝ^{dim n})`. -/
def secHam (n : ℕ) : polyGaussCore (d := F.dim n) →ₗ[ℂ] L2d (F.dim n) :=
  sqSumOp (F.kap n) (F.vv n)

theorem secHam_symmetricOn (n : ℕ) :
    SymmetricOn (polyGaussCore (d := F.dim n)) (F.secHam n) :=
  sqSumOp_symmetricOn _ _

theorem secHam_essentiallySelfAdjointOn (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := F.dim n)) (F.secHam n) :=
  sqSumOp_essentiallySelfAdjointOn _ _

/-- **The relative bound**, with a constant uniform in the particle number. -/
theorem secHam_norm_le (n : ℕ) (u : polyGaussCore (d := F.dim n)) :
    ‖F.secHam n u‖ ≤ F.flK * ‖QgHermiteOscillator.harmCore u + (u : L2d (F.dim n))‖ := by
  have hB : ∀ x : Vd (F.dim n), potFun (F.vv n) x ≤ (F.a * F.b / 2) * ‖x‖ ^ 2 :=
    fun x => potFun_le_of_schur F.a_nonneg (F.row_le n) (F.col_le n) x
  have hB0 : (0 : ℝ) ≤ F.a * F.b / 2 := by
    have := F.ab_nonneg; linarith
  have heq : 3 / 2 * F.km + 8 * (F.a * F.b / 2) = F.flK := by rw [flK]; ring
  rw [secHam, ← heq]
  exact norm_sqSumOp_le F.km_nonneg (F.kap_le n) hB0 hB u

/-- **The Faris–Lavine commutator bound**, with a constant uniform in the particle
number. -/
theorem secHam_commForm_le (n : ℕ) (u : polyGaussCore (d := F.dim n)) :
    |commForm (F.secHam n) QgHermiteOscillator.harmCore u|
        ≤ F.flc * quadForm QgHermiteOscillator.harmCore u := by
  have hM : ∀ x : Vd (F.dim n),
      ∑ k : Fin (F.dim n), (gradFun (F.vv n) k x) ^ 2 ≤ (F.a * F.b) ^ 2 * ‖x‖ ^ 2 :=
    fun x => sum_gradFun_sq_le_of_schur F.a_nonneg F.b_nonneg (F.row_le n) (F.col_le n) x
  have heq : F.km / 2 + 2 * (F.a * F.b) = F.flc := by rw [flc]
  rw [secHam, ← heq]
  exact commForm_sqSumOp_le F.km_nonneg (F.kap_le n) F.ab_nonneg hM u

/-! ### The Hamiltonian on the outer Fock space -/

/-- **The Hamiltonian of the family on the finite-particle core of the outer Fock
space.** -/
def outerHam : outerCore F.dim →ₗ[ℂ] outerFock F.dim := dsOp (fun n : ℕ => F.secHam n)

theorem outerHam_symmetricOn : SymmetricOn (outerCore F.dim) F.outerHam :=
  dsOp_symmetricOn _ fun n => F.secHam_symmetricOn n

/-- The Carleman route applies sector by sector: the Hamiltonian is essentially
self-adjoint already on the finite-particle core. -/
theorem outerHam_esa : EssentiallySelfAdjointOn (outerCore F.dim) F.outerHam :=
  dsOp_essentiallySelfAdjointOn _ fun n => F.secHam_essentiallySelfAdjointOn n

/-- The Faris–Lavine core data of the `n`-particle Hamiltonian. -/
def secData (n : ℕ) : CoreData (L2d (F.dim n)) where
  C := harmFried (F.dim n)
  C₀ := polyGaussCore (d := F.dim n)
  gc := harmFried_isGraphCore (F.dim n)
  H₀ := F.secHam n
  K := F.flK
  hK := F.flK_nonneg
  rel := by
    intro p
    rw [harmFried_op_core (F.dim n) p]
    exact F.secHam_norm_le n p

/-- The `n`-particle Hamiltonian, extended from the Gauss–polynomial core to the whole
domain of the sector comparison operator. -/
def secExt (n : ℕ) : (harmFried (F.dim n)).dom →ₗ[ℂ] L2d (F.dim n) := (F.secData n).ext

theorem secExt_symmetricOn (n : ℕ) :
    SymmetricOn (harmFried (F.dim n)).dom (F.secExt n) :=
  (F.secData n).ext_symmetricOn (F.secHam_symmetricOn n)



theorem secExt_rel : ∀ (n : ℕ) (u : (harmFried (F.dim n)).dom),
    ‖F.secExt n u‖ ≤ F.flK * ‖(harmFried (F.dim n)).op u + (u : L2d (F.dim n))‖ :=
  fun n u => (F.secData n).ext_norm_le u







end SqFamily

end

end BookProof.SqSumOuterFamily


