-- Prove2me | Definitions.Def_ChapterNavierStokesEsa
-- name    : ChapterNavierStokesEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:25:47.608439+00:00
-- url     : https://prove2.me/theorems/4a799133-ae0c-474b-a15a-0ff983a36753
-- title:
--   Companion to `BookProof.ChapterNavierStokesFlow` and `BookProof.ChapterNavierStokesCauchy`.
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesEsa`, source chapter `BookProof/ChapterNavierStokesEsa.lean`).
--
--   Companion to `BookProof.ChapterNavierStokesFlow` and `BookProof.ChapterNavierStokesCauchy`.
--
--   Those modules prove that the truncated Navier–Stokes Hamiltonian is Hermitian, that its flow `U(t) = e^{i t H_N}` is a one-parameter unitary group defined for every real time, and that the associated Cauchy problem has exactly one global solution. Essential self-adjointness (`HasZeroDeficiencyOn`) was, however, only established there for the **full** domain `D = ⊤`, where symmetry alone suffices.
--
--   The analytic content of the notion lives on a *proper* dense domain, and this module supplies it:
--
--   * `eq_zero_of_hasDerivAt_smul_of_bounded` — a bounded solution of `g' = ± g` on the real line vanishes at the origin (the elementary ODE step); * `hasZeroDeficiencyOn_of_completeUnitaryFlow` — **the headline.** If a symmetric operator `H` on a dense domain `D` generates a norm-preserving flow `U` which is defined for *every* real time and leaves `D` invariant, then the deficiency spaces of `H∗` vanish, i.e. `H` is essentially self-adjoint. This is the precise form of the statement that the plan's scoping section appeals to when it says that *the deficiency argument requires the flow to be complete* (Nelson's criterion): completeness of the flow is exactly the hypothesis, and a finite-time blow-up destroys it; * `nsHamiltonian_hasZeroDeficiencyOn_of_flow` — the truncated Navier–Stokes generator, re-derived along that route from the completeness of its own flow rather than from finite-dimensional symmetry; * `hasZeroDeficiencyOn_of_bounded_symmetric` — a bounded symmetric operator is essentially self-adjoint on **every** dense invariant domain, and `continuityHamiltonian_hasZeroDeficiencyOn_finiteModes`, its application to the infinite-dimensional `ℓ²(ℤ)` layer of `BookProof.ChapterContinuityUnitaryInfinite` on the proper dense domain of finitely supported modes. This is the first instance in the development of vanishing adjoint deficiency on a domain that is *not* the whole space, so the predicate `HasZeroDeficiencyOn` is not vacuous there.
--
--   Unchanged: nothing here is a statement about the continuum Navier–Stokes operator. The flow criterion is proved in full generality, but its hypotheses (a *complete* norm-preserving flow leaving the domain invariant) are exactly what is not known for the untruncated Navier–Stokes generator — that is the research target recorded in `BookProof.ChapterNavierStokesFlow`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow

/-!
# Essential self-adjointness from a complete flow, on a genuinely dense domain

Companion to `BookProof.ChapterNavierStokesFlow` and
`BookProof.ChapterNavierStokesCauchy`.

Those modules prove that the truncated Navier–Stokes Hamiltonian is Hermitian,
that its flow `U(t) = e^{i t H_N}` is a one-parameter unitary group defined for
every real time, and that the associated Cauchy problem has exactly one global
solution.  Essential self-adjointness (`HasZeroDeficiencyOn`) was, however, only
established there for the **full** domain `D = ⊤`, where symmetry alone suffices.

The analytic content of the notion lives on a *proper* dense domain, and this
module supplies it:

* `eq_zero_of_hasDerivAt_smul_of_bounded` — a bounded solution of `g' = ± g` on
  the real line vanishes at the origin (the elementary ODE step);
* `hasZeroDeficiencyOn_of_completeUnitaryFlow` — **the headline.** If a symmetric
  operator `H` on a dense domain `D` generates a norm-preserving flow `U` which
  is defined for *every* real time and leaves `D` invariant, then the deficiency
  spaces of `H∗` vanish, i.e. `H` is essentially self-adjoint.  This is the
  precise form of the statement that the plan's scoping section appeals to when
  it says that *the deficiency argument requires the flow to be complete*
  (Nelson's criterion): completeness of the flow is exactly the hypothesis, and
  a finite-time blow-up destroys it;
* `nsHamiltonian_hasZeroDeficiencyOn_of_flow` — the truncated Navier–Stokes
  generator, re-derived along that route from the completeness of its own flow
  rather than from finite-dimensional symmetry;
* `hasZeroDeficiencyOn_of_bounded_symmetric` — a bounded symmetric operator is
  essentially self-adjoint on **every** dense invariant domain, and
  `continuityHamiltonian_hasZeroDeficiencyOn_finiteModes`, its application to the
  infinite-dimensional `ℓ²(ℤ)` layer of
  `BookProof.ChapterContinuityUnitaryInfinite` on the proper dense domain of
  finitely supported modes.  This is the first instance in the development of
  vanishing adjoint deficiency on a domain that is *not* the whole space, so the
  predicate `HasZeroDeficiencyOn` is not vacuous there.

## Scope

Unchanged: nothing here is a statement about the continuum Navier–Stokes
operator.  The flow criterion is proved in full generality, but its hypotheses
(a *complete* norm-preserving flow leaving the domain invariant) are exactly
what is not known for the untruncated Navier–Stokes generator — that is the
research target recorded in `BookProof.ChapterNavierStokesFlow`.
-/

open scoped Matrix

namespace BookProof.NavierStokesFlow

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]















end Abstract

/-! ## Finitely supported modes of an `ℓ²` space

The *finite-particle domain* of an `ℓ²` space: the states exciting only finitely
many modes.  It is dense (every `ℓ²` state is the limit of its truncations) and,
whenever the index type is infinite, a **proper** subspace — so it is the natural
place to test statements about densely defined operators. -/

section LpFiniteModes

variable {ι : Type*}

/-- The **finitely supported modes** of `ℓ²(ι)`. -/
def lpFiniteModes (ι : Type*) : Submodule ℂ (lp (fun _ : ι => ℂ) 2) where
  carrier := {f : lp (fun _ : ι => ℂ) 2 | (Function.support ((f : ι → ℂ))).Finite}
  add_mem' := by
    intro f g hf hg
    refine Set.Finite.subset (hf.union hg) ?_
    intro k hk
    simp only [Function.mem_support, lp.coeFn_add, Pi.add_apply] at hk
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
    exact hk (by rw [hcon.1, hcon.2, add_zero])
  zero_mem' := by
    simp only [Set.mem_setOf_eq, lp.coeFn_zero]
    simp
  smul_mem' := by
    intro c f hf
    refine Set.Finite.subset hf ?_
    intro k hk
    simp only [Function.mem_support, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hk
    exact fun hzero => hk (by rw [hzero, mul_zero])

theorem mem_lpFiniteModes {f : lp (fun _ : ι => ℂ) 2} :
    f ∈ lpFiniteModes ι ↔ (Function.support ((f : ι → ℂ))).Finite := Iff.rfl

/-- Each canonical basis state `e_k` has finite support. -/
theorem lpSingle_mem_lpFiniteModes [DecidableEq ι] (k : ι) (c : ℂ) :
    lp.single 2 k c ∈ lpFiniteModes ι := by
  refine Set.Finite.subset (Set.finite_singleton k) ?_
  intro j hj
  simp only [Function.mem_support] at hj
  by_contra hne
  have hjk : j ≠ k := by simpa using hne
  exact hj (by simp [lp.single_apply, Pi.single_eq_of_ne hjk])

end LpFiniteModes

/-! ## An infinite-dimensional instance on a *proper* dense domain

The `ℓ²(ℤ)` layer of `BookProof.ChapterContinuityUnitaryInfinite` carries a
bounded self-adjoint generator, the Weyl-symmetrized continuity Hamiltonian
`H = ½(p v + v p)`.  Its natural *finite-particle* domain — the states with only
finitely many excited lattice modes — is dense but not the whole space, so the
statement `HasZeroDeficiencyOn finiteModes …` is a genuine (non-`⊤`) instance of
essential self-adjointness on a dense domain. -/

section InfiniteLattice


/-- The finitely supported modes of the lattice Hilbert space `ℓ²(ℤ)`. -/
abbrev finiteModes : Submodule ℂ L2Z := lpFiniteModes ℤ

variable {ι : Type*}

/-- **The finite-mode domain is dense**: every `ℓ²` state is the limit of its
finite truncations. -/
theorem lpFiniteModes_dense :
    Dense ((lpFiniteModes ι : Submodule ℂ (lp (fun _ : ι => ℂ) 2)) :
      Set (lp (fun _ : ι => ℂ) 2)) := by
  classical
  intro f
  refine mem_closure_of_tendsto (lp.hasSum_single (by simp) f) ?_
  filter_upwards with S
  exact Submodule.sum_mem _ fun k _ => lpSingle_mem_lpFiniteModes k _

/-- The lattice finite-mode domain is dense. -/
theorem finiteModes_dense : Dense ((finiteModes : Submodule ℂ L2Z) : Set L2Z) :=
  lpFiniteModes_dense

/-- The lattice translation preserves the finite-mode domain. -/
theorem shiftOp_mem_finiteModes (m : ℤ) {f : L2Z} (hf : f ∈ finiteModes) :
    shiftOp m f ∈ finiteModes := by
  rw [mem_lpFiniteModes] at hf ⊢
  refine Set.Finite.subset (hf.image fun k => k - m) ?_
  intro k hk
  simp only [Function.mem_support, shiftOp_apply] at hk
  exact ⟨k + m, hk, by ring⟩

/-- Multiplication by a bounded velocity field preserves the finite-mode
domain. -/
theorem velocityOp_mem_finiteModes (v : LinfZ) {f : L2Z} (hf : f ∈ finiteModes) :
    velocityOp v f ∈ finiteModes := by
  rw [mem_lpFiniteModes] at hf ⊢
  refine hf.subset fun k hk => ?_
  simp only [Function.mem_support, velocityOp_apply] at hk
  exact fun hzero => hk (by rw [hzero, mul_zero])

















end InfiniteLattice

/-! ## The truncated Navier–Stokes generator, via its complete flow

The truncation was already known to be essentially self-adjoint by symmetry
(`nsHamiltonian_hasZeroDeficiencyOn`).  Here it is re-derived along the route
that the continuum question would have to follow: from the **completeness** of
its unitary flow. -/

section Truncation

variable {n : ℕ} (d : NSTruncation n)

/-- The truncated Navier–Stokes flow, transported to the Euclidean (`ℓ²`) model
of `ℂⁿ`. -/
noncomputable def nsFlowEuclidean (t : ℝ) (psi : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (nsFlowUnitary d t *ᵥ WithLp.ofLp psi)









end Truncation

end BookProof.NavierStokesFlow


