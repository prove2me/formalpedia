-- Prove2me | Definitions.Def_ChapterNavierStokesSecondQuant
-- name    : ChapterNavierStokesSecondQuant
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T11:33:13.688299+00:00
-- url     : https://prove2.me/theorems/3f9582ab-0c77-40a4-95c5-ed9649fd7b9a
-- title:
--   This module supplies the *Fock-space* half of the essential-self-adjointness argument for the Navier–Stokes Hamiltonian: ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesSecondQuant`, source chapter `BookProof/ChapterNavierStokesSecondQuant.lean`).
--
--   This module supplies the *Fock-space* half of the essential-self-adjointness argument for the Navier–Stokes Hamiltonian: the passage from a one-particle comparison operator to its second quantization.
--
--   The Fock space is modelled, as in Reed–Simon Vol. I §II.4, as the Hilbert direct sum `⨁ₘ Sₘ` of the `m`-particle sectors, realized concretely as `lp S 2`. The *finite-particle domain* `fockCore D` consists of the states with finitely many non-zero sectors, each of them lying in the sector domain `D m`; when every `D m` is dense this is a dense subspace of the Fock space (`fockCore_dense`), and for infinitely many nontrivial sectors it is a *proper* one (`fockCore_ne_top`).
--
--   A sector-wise family of operators `A m : D m →ₗ[ℂ] D m` assembles into the operator `fockOp A` on the finite-particle domain — this is `dΓ` written in sectors, `dΓ(a)` acting on the `m`-particle sector as `∑_{k<m} a_k`. The headline result is
--
--   * `fockOp_hasZeroDeficiencyOn`: **if every sector operator is essentially self-adjoint on its sector domain, then the second quantization is essentially self-adjoint on the finite-particle domain.**
--
--   This is the direct-sum half of the second-quantization theorem (Reed–Simon Vol. I, Theorem VIII.33 / §VIII.10). The remaining half — that the `m`-particle sector operator `∑_{k<m} a_k` is essentially self-adjoint on the algebraic tensor power of a core for `a` — is *not* proved here in that generality; what is proved (`sectorOfEigenbasis_hasZeroDeficiencyOn` in the companion module, and `BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn` already in the project) is the case in which the one-particle operator is diagonalized by a total family of eigenvectors, which is the situation of the Navier–Stokes comparison operator in the fiber momentum representation.
--
--   Nothing here claims essential self-adjointness of the continuum Navier–Stokes generator, nor global existence for Navier–Stokes. This module is about the Fock-space bookkeeping: what sector-wise essential self-adjointness gives, and what it does not.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSecondQuant.lean

import Definitions.Def_ChapterNavierStokesFullEsa
import Mathlib

import Mathlib

/-!
# Second quantization of an essentially self-adjoint one-particle operator

This module supplies the *Fock-space* half of the essential-self-adjointness
argument for the Navier–Stokes Hamiltonian: the passage from a one-particle
comparison operator to its second quantization.

The Fock space is modelled, as in Reed–Simon Vol. I §II.4, as the Hilbert direct
sum `⨁ₘ Sₘ` of the `m`-particle sectors, realized concretely as `lp S 2`.  The
*finite-particle domain* `fockCore D` consists of the states with finitely many
non-zero sectors, each of them lying in the sector domain `D m`; when every
`D m` is dense this is a dense subspace of the Fock space (`fockCore_dense`), and
for infinitely many nontrivial sectors it is a *proper* one
(`fockCore_ne_top`).

A sector-wise family of operators `A m : D m →ₗ[ℂ] D m` assembles into the
operator `fockOp A` on the finite-particle domain — this is `dΓ` written in
sectors, `dΓ(a)` acting on the `m`-particle sector as `∑_{k<m} a_k`.  The
headline result is

* `fockOp_hasZeroDeficiencyOn`: **if every sector operator is essentially
  self-adjoint on its sector domain, then the second quantization is essentially
  self-adjoint on the finite-particle domain.**

This is the direct-sum half of the second-quantization theorem
(Reed–Simon Vol. I, Theorem VIII.33 / §VIII.10).  The remaining half — that the
`m`-particle sector operator `∑_{k<m} a_k` is essentially self-adjoint on the
algebraic tensor power of a core for `a` — is *not* proved here in that
generality; what is proved (`sectorOfEigenbasis_hasZeroDeficiencyOn` in the
companion module, and `BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn`
already in the project) is the case in which the one-particle operator is
diagonalized by a total family of eigenvectors, which is the situation of the
Navier–Stokes comparison operator in the fiber momentum representation.

## Scope

Nothing here claims essential self-adjointness of the continuum Navier–Stokes
generator, nor global existence for Navier–Stokes.  This module is about the
Fock-space bookkeeping: what sector-wise essential self-adjointness gives, and
what it does not.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace SecondQuant

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]

/-! ## The Fock space as a Hilbert direct sum of sectors -/

omit [∀ m, InnerProductSpace ℂ (S m)] in
/-- A family with finitely many non-zero members is square-summable. -/
theorem memℓp_of_finite_support {g : ∀ m, S m}
    (h : (Function.support fun m => ‖g m‖).Finite) : Memℓp g 2 := by
  apply memℓp_gen
  refine summable_of_ne_finset_zero (s := h.toFinset) ?_
  intro m hm
  have : ‖g m‖ = 0 := by
    by_contra hne
    exact hm (h.mem_toFinset.mpr (by simpa [Function.mem_support] using hne))
  simp [this]

/-- The Fock state built from a family of sector states with finitely many
non-zero members. -/
noncomputable def ofSectors (g : ∀ m, S m) (h : (Function.support fun m => ‖g m‖).Finite) :
    lp S 2 :=
  ⟨g, memℓp_of_finite_support h⟩



variable (D : ∀ m, Submodule ℂ (S m))

/-- **The finite-particle domain of the Fock space.**  States with finitely many
non-zero sectors, each sector state lying in the sector domain `D m`.  This is
`𝓕_fin(D)`. -/
def fockCore : Submodule ℂ (lp S 2) where
  carrier :=
    {f | (Function.support fun m => ‖(f : ∀ m, S m) m‖).Finite ∧ ∀ m, (f : ∀ m, S m) m ∈ D m}
  add_mem' := by
    rintro f g ⟨hf, hfD⟩ ⟨hg, hgD⟩
    constructor
    · refine (hf.union hg).subset ?_
      intro m hm
      by_contra hcon
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
      have h1 : (f : ∀ m, S m) m = 0 := by simpa using hcon.1
      have h2 : (g : ∀ m, S m) m = 0 := by simpa using hcon.2
      exact hm (by simp [h1, h2])
    · intro m
      simpa [lp.coeFn_add] using Submodule.add_mem _ (hfD m) (hgD m)
  zero_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  smul_mem' := by
    rintro c f ⟨hf, hfD⟩
    constructor
    · refine hf.subset ?_
      intro m hm
      simp only [Function.mem_support, lp.coeFn_smul, Pi.smul_apply, norm_smul] at hm ⊢
      intro hzero
      exact hm (by simp [hzero])
    · intro m
      simpa [lp.coeFn_smul] using Submodule.smul_mem _ c (hfD m)

variable {D}





/-! ### Density of the finite-particle domain -/



/-! ## Second quantization of a sector-wise family of operators -/

/-- The sector-wise action of a family of sector operators on a finite-particle
state. -/
noncomputable def sectorApply (A : ∀ m, D m →ₗ[ℂ] D m) (f : fockCore D) : ∀ m, S m :=
  fun m => ((A m ⟨(f : lp S 2) m, (f.2).2 m⟩ : D m) : S m)

theorem sectorApply_support (A : ∀ m, D m →ₗ[ℂ] D m) (f : fockCore D) :
    (Function.support fun m => ‖sectorApply A f m‖).Finite := by
  refine ((f.2).1).subset ?_
  intro m hm
  simp only [Function.mem_support] at hm ⊢
  intro hzero
  apply hm
  have hz : ((⟨(f : lp S 2) m, (f.2).2 m⟩ : D m)) = 0 := by
    ext
    simpa using hzero
  simp [sectorApply, hz]

/-- **`dΓ` in sectors.**  The second quantization of a sector-wise family of
operators, acting on the finite-particle domain. -/
noncomputable def fockOp (A : ∀ m, D m →ₗ[ℂ] D m) : fockCore D →ₗ[ℂ] fockCore D where
  toFun f := ⟨ofSectors (sectorApply A f) (sectorApply_support A f), by
    constructor
    · exact sectorApply_support A f
    · intro m; exact (A m ⟨(f : lp S 2) m, (f.2).2 m⟩).2⟩
  map_add' f g := by
    apply Subtype.ext
    apply lp.ext
    funext m
    exact congrArg Subtype.val
      ((A m).map_add ⟨(f : lp S 2) m, (f.2).2 m⟩ ⟨(g : lp S 2) m, (g.2).2 m⟩)
  map_smul' c f := by
    apply Subtype.ext
    apply lp.ext
    funext m
    exact congrArg Subtype.val ((A m).map_smul c ⟨(f : lp S 2) m, (f.2).2 m⟩)





/-! ## Essential self-adjointness lifts from the sectors to the Fock space -/



/-! ### The finite-particle domain is a *proper* subspace -/



end SecondQuant

end BookProof.NavierStokesFlow


