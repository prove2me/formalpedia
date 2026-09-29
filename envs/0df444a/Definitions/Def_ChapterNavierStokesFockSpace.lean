-- Prove2me | Definitions.Def_ChapterNavierStokesFockSpace
-- name    : ChapterNavierStokesFockSpace
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T14:51:21.601964+00:00
-- url     : https://prove2.me/theorems/1a66d912-e80b-4211-8f7d-b00642c6bd7c
-- title:
--   The Lagrangian form of the Navier–Stokes Hamiltonian of `BookProof.ChapterNavierStokesLagrangianEsa` is a *second* quant ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesFockSpace`, source chapter `BookProof/ChapterNavierStokesFockSpace.lean`).
--
--   The Lagrangian form of the Navier–Stokes Hamiltonian of `BookProof.ChapterNavierStokesLagrangianEsa` is a *second* quantization: the Eulerian field `u` is already an operator on a Fock space, and passing to the parcel variables `X(ξ)` — one field-carrying parcel for each label `ξ` in a continuous domain — quantizes the parcels themselves. The state space is therefore a Fock space **whose one-particle space is itself a Fock space**, and the Hamiltonian is *quadratic* in the outer (parcel) creation and annihilation operators.
--
--   This module builds that state space concretely, in the occupation-number representation, together with both levels of ladder operators.
--
--   * `lpDiag`, `lpBasis` — a general diagonal operator with a real symbol on the finitely supported modes of `ℓ²(ι)`, its eigenbasis, symmetry, essential self-adjointness (`lpDiag_hasZeroDeficiencyOn`) and unboundedness (`lpDiag_not_bounded`). * `Conf M = M →₀ ℕ`, `FockL2 M = ℓ²(Conf M)`, `FockDom M` — the Fock space over the mode index `M` in the occupation-number representation and its dense domain of finite-particle, finite-mode states. * `annih m`, `creat m` — the annihilation and creation operators, with `annih_basis`, `creat_basis` (the usual `√n` factors), `creat_adjoint` (`⟪a†v, w⟫ = ⟪v, a w⟫`) and the canonical commutation relations `ccr_same`, `ccr_ne`. * `numberOp m = a†ₘ aₘ` and `numberOp_basis` — the mode occupation operator. * `FockOfFockL2 J K = FockL2 (J × Conf K)` — **the Fock space of a Fock space**: the outer one-particle modes are indexed by a parcel mode `j : J` *together with* an inner Fock (occupation) state `c : Conf K`. `outerOneParticle` shows that the outer creation operator applied to the vacuum creates exactly one parcel carrying the inner Fock state `c`.
--
--   The Hamiltonian itself, its integral over the continuous parcel domain and its essential self-adjointness are in `BookProof.ChapterNavierStokesFockEsa`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean

import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib

import Mathlib

/-!
# The Fock space of a Fock space, and its ladder operators

The Lagrangian form of the Navier–Stokes Hamiltonian of
`BookProof.ChapterNavierStokesLagrangianEsa` is a *second* quantization: the
Eulerian field `u` is already an operator on a Fock space, and passing to the
parcel variables `X(ξ)` — one field-carrying parcel for each label `ξ` in a
continuous domain — quantizes the parcels themselves.  The state space is
therefore a Fock space **whose one-particle space is itself a Fock space**, and
the Hamiltonian is *quadratic* in the outer (parcel) creation and annihilation
operators.

This module builds that state space concretely, in the occupation-number
representation, together with both levels of ladder operators.

* `lpDiag`, `lpBasis` — a general diagonal operator with a real symbol on the
  finitely supported modes of `ℓ²(ι)`, its eigenbasis, symmetry, essential
  self-adjointness (`lpDiag_hasZeroDeficiencyOn`) and unboundedness
  (`lpDiag_not_bounded`).
* `Conf M = M →₀ ℕ`, `FockL2 M = ℓ²(Conf M)`, `FockDom M` — the Fock space over
  the mode index `M` in the occupation-number representation and its dense
  domain of finite-particle, finite-mode states.
* `annih m`, `creat m` — the annihilation and creation operators, with
  `annih_basis`, `creat_basis` (the usual `√n` factors), `creat_adjoint`
  (`⟪a†v, w⟫ = ⟪v, a w⟫`) and the canonical commutation relations
  `ccr_same`, `ccr_ne`.
* `numberOp m = a†ₘ aₘ` and `numberOp_basis` — the mode occupation operator.
* `FockOfFockL2 J K = FockL2 (J × Conf K)` — **the Fock space of a Fock space**:
  the outer one-particle modes are indexed by a parcel mode `j : J` *together
  with* an inner Fock (occupation) state `c : Conf K`.  `outerOneParticle` shows
  that the outer creation operator applied to the vacuum creates exactly one
  parcel carrying the inner Fock state `c`.

The Hamiltonian itself, its integral over the continuous parcel domain and its
essential self-adjointness are in `BookProof.ChapterNavierStokesFockEsa`.
-/

namespace BookProof.NavierStokesFlow

namespace FockOfFock

open FullEsa

/-! ## Finitely supported coefficient vectors in `ℓ²(ι)` -/

section Coeff

variable {ι : Type*}

/-- A finitely supported coefficient function is square-summable. -/
theorem memℓpTwo_of_finite_support {φ : ι → ℂ} (h : (Function.support φ).Finite) :
    Memℓp φ 2 := by
  apply memℓp_gen
  refine summable_of_finite_support (Set.Finite.subset h ?_)
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz
  exact hx (by simp [hz])

/-- The finite-mode vector of `ℓ²(ι)` with the given finitely supported
coefficients. -/
def ofCoeff (φ : ι → ℂ) (h : (Function.support φ).Finite) : lpFiniteModes ι :=
  ⟨⟨φ, memℓpTwo_of_finite_support h⟩, h⟩



/-- A coefficientwise linear operator on the finite-mode domain of `ℓ²(ι)`. -/
def coeffOp (T : (ι → ℂ) → ι → ℂ)
    (hsupp : ∀ {φ : ι → ℂ}, (Function.support φ).Finite → (Function.support (T φ)).Finite)
    (hadd : ∀ φ ψ : ι → ℂ, T (φ + ψ) = T φ + T ψ)
    (hsmul : ∀ (c : ℂ) (φ : ι → ℂ), T (c • φ) = c • T φ) :
    lpFiniteModes ι →ₗ[ℂ] lpFiniteModes ι where
  toFun f := ofCoeff (T ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ)) (hsupp f.2)
  map_add' f g := by
    ext i
    have hcoef : (((f + g : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
        = ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) + ((g : lp (fun _ : ι => ℂ) 2) : ι → ℂ) := by
      ext j; simp
    change T (↑(↑(f + g : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
        = T (↑(↑f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i + T (↑(↑g : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
    rw [hcoef]
    exact congrFun (hadd _ _) i
  map_smul' c f := by
    ext i
    have hcoef : (((c • f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
        = c • ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) := by
      ext j; simp
    change T (↑(↑(c • f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
        = c • T (↑(↑f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
    rw [hcoef]
    exact congrFun (hsmul c _) i



/-- The canonical basis state `e_i` of the finite-mode domain. -/
noncomputable def lpBasis [DecidableEq ι] (i : ι) : lpFiniteModes ι :=
  ⟨lp.single 2 i 1, lpSingle_mem_lpFiniteModes i 1⟩









end Coeff

/-! ## Diagonal operators with a real symbol -/

section Diagonal

variable {ι : Type*}

/-- Coefficientwise multiplication by a real symbol. -/
def diagCoeff (c : ι → ℝ) (φ : ι → ℂ) : ι → ℂ := fun i => (c i : ℂ) * φ i

/-- The diagonal operator with real symbol `c` on the finite-mode domain of
`ℓ²(ι)`.  For an unbounded symbol it is an unbounded operator. -/
noncomputable def lpDiag (c : ι → ℝ) : lpFiniteModes ι →ₗ[ℂ] lpFiniteModes ι :=
  coeffOp (diagCoeff c)
    (fun {φ} h => h.subset (by
      intro i hi
      simp only [Function.mem_support, diagCoeff] at hi ⊢
      intro hz
      exact hi (by simp [hz])))
    (fun φ ψ => by funext i; simp [diagCoeff]; ring)
    (fun a φ => by funext i; simp [diagCoeff]; ring)











end Diagonal

/-! ## The Fock space in the occupation-number representation -/

section Fock

variable {M : Type*} [DecidableEq M]

/-- An occupation-number configuration: finitely many modes excited, each
finitely often. -/
abbrev Conf (M : Type*) := M →₀ ℕ

/-- The bosonic Fock space over the mode index `M`, in the occupation-number
representation. -/
noncomputable abbrev FockL2 (M : Type*) := lp (fun _ : Conf M => ℂ) 2

/-- The dense domain of finite-particle, finite-mode states. -/
noncomputable abbrev FockDom (M : Type*) : Submodule ℂ (FockL2 M) :=
  lpFiniteModes (Conf M)





/-- The occupation-number basis state `|n⟩`. -/
noncomputable def fockBasis (n : Conf M) : FockDom M := lpBasis n



/-- The vacuum `|0⟩`. -/
noncomputable def vacuum : FockDom M := fockBasis 0

/-! ### Annihilation and creation -/



omit [DecidableEq M] in
/-- Removing and then adding one quantum in an occupied mode is the identity. -/
theorem sub_single_add_single {m : M} {n : Conf M} (h : 1 ≤ n m) :
    (n - Finsupp.single m 1 : Conf M) + Finsupp.single m 1 = n := by
  ext j
  rcases eq_or_ne j m with rfl | hj
  · simp; omega
  · simp [hj]

/-- Coefficient form of the annihilation operator `aₘ`. -/
noncomputable def annihCoeff (m : M) (φ : Conf M → ℂ) : Conf M → ℂ :=
  fun n => (Real.sqrt (n m + 1) : ℂ) * φ (n + Finsupp.single m 1)

/-- Coefficient form of the creation operator `a†ₘ`. -/
noncomputable def creatCoeff (m : M) (φ : Conf M → ℂ) : Conf M → ℂ :=
  fun n => (Real.sqrt (n m) : ℂ) * φ (n - Finsupp.single m 1)

omit [DecidableEq M] in
theorem annihCoeff_support {m : M} {φ : Conf M → ℂ} (h : (Function.support φ).Finite) :
    (Function.support (annihCoeff m φ)).Finite := by
  refine (h.image fun n => n - Finsupp.single m 1).subset ?_
  intro n hn
  simp only [Function.mem_support, annihCoeff] at hn
  refine ⟨n + Finsupp.single m 1, ?_, by simp⟩
  simp only [Function.mem_support]
  intro hz
  exact hn (by simp [hz])

omit [DecidableEq M] in
theorem creatCoeff_support {m : M} {φ : Conf M → ℂ} (h : (Function.support φ).Finite) :
    (Function.support (creatCoeff m φ)).Finite := by
  refine (h.image fun n => n + Finsupp.single m 1).subset ?_
  intro n hn
  simp only [Function.mem_support, creatCoeff] at hn
  have hpos : 1 ≤ n m := by
    by_contra hlt
    have : n m = 0 := by omega
    apply hn
    simp [this]
  refine ⟨n - Finsupp.single m 1, ?_, ?_⟩
  · simp only [Function.mem_support]
    intro hz
    exact hn (by simp [hz])
  · exact sub_single_add_single hpos

/-- **The annihilation operator** `aₘ` on the finite-particle domain. -/
noncomputable def annih (m : M) : FockDom M →ₗ[ℂ] FockDom M :=
  coeffOp (annihCoeff m) (fun {_} h => annihCoeff_support h)
    (fun φ ψ => by funext n; simp [annihCoeff]; ring)
    (fun a φ => by funext n; simp [annihCoeff]; ring)

/-- **The creation operator** `a†ₘ` on the finite-particle domain. -/
noncomputable def creat (m : M) : FockDom M →ₗ[ℂ] FockDom M :=
  coeffOp (creatCoeff m) (fun {_} h => creatCoeff_support h)
    (fun φ ψ => by funext n; simp [creatCoeff]; ring)
    (fun a φ => by funext n; simp [creatCoeff]; ring)













/-! ### The canonical commutation relations -/





/-! ### Adjointness -/





end Fock

/-! ## The Fock space of a Fock space -/

section FockOfFockSpace

variable {J K : Type*} [DecidableEq J] [DecidableEq K]

/-- **The Fock space of a Fock space.**  The inner level is the Fock space
`FockL2 K` of the field modes `K`; a one-particle state of the *outer* level is
a parcel carrying a parcel mode `j : J` together with an inner Fock (occupation)
state `c : Conf K`, so the outer mode index is `J × Conf K`. -/
noncomputable abbrev FockOfFockL2 (J K : Type*) := FockL2 (J × Conf K)

/-- The dense finite-particle domain of the two-level Fock space. -/
noncomputable abbrev FockOfFockDom (J K : Type*) : Submodule ℂ (FockOfFockL2 J K) :=
  FockDom (J × Conf K)





end FockOfFockSpace

end FockOfFock

end BookProof.NavierStokesFlow


