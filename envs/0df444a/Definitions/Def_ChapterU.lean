-- Prove2me | Definitions.Def_ChapterU
-- name    : ChapterU
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:12:34.78028+00:00
-- url     : https://prove2.me/theorems/10149216-9334-40b5-b742-c40fd3383ec0
-- title:
--   Formalization of the self-contained mathematical content of Chapter U of the `unfer` source material (see `FORMALIZATION ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.U`, source chapter `BookProof/ChapterU.lean`).
--
--   Formalization of the self-contained mathematical content of Chapter U of the `unfer` source material (see `FORMALIZATION_ROADMAP.md` §U, work package N8), to be merged into `book.tex`. Deliverables:
--
--   * **U.1** (headline): the Born-rule *conditioning by projection* of a wave-function equals the classical conditional measure `ProbabilityTheory.cond` — quantum conditioning (wave-function collapse onto an event) and Bayesian conditioning are the same operation. * **U.3**: the Fock-space exponential property `Sym(M × N) ≅ Sym M ⊗ Sym N`. * **U.4**: the measure-theoretic wrapper around the (external) fact that stochastic trajectories are a.s. nowhere differentiable. * **U.5**: independent components ⇒ portfolio risk falls like `1/√n`.
--
--   U.2 (sphere→Gaussian / Gegenbauer→Hermite) is already `sorry`-free in `BookProof/PhysHSGaussian.lean`; it is a cross-reference only, no new code here.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterU.lean

import Mathlib
import Mathlib

import Mathlib

import Mathlib

/-!
# Chapter U — Unitary inference / unfer

Formalization of the self-contained mathematical content of Chapter U of the
`unfer` source material (see `FORMALIZATION_ROADMAP.md` §U, work package N8),
to be merged into `book.tex`.  Deliverables:

* **U.1** (headline): the Born-rule *conditioning by projection* of a
  wave-function equals the classical conditional measure
  `ProbabilityTheory.cond` — quantum conditioning (wave-function collapse onto
  an event) and Bayesian conditioning are the same operation.
* **U.3**: the Fock-space exponential property `Sym(M × N) ≅ Sym M ⊗ Sym N`.
* **U.4**: the measure-theoretic wrapper around the (external) fact that
  stochastic trajectories are a.s. nowhere differentiable.
* **U.5**: independent components ⇒ portfolio risk falls like `1/√n`.

U.2 (sphere→Gaussian / Gegenbauer→Hermite) is already `sorry`-free in
`BookProof/PhysHSGaussian.lean`; it is a cross-reference only, no new code here.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

namespace BookProof.ChapterU

/-! ## U.1 — Born-rule conditioning is Bayesian updating by projection -/

variable {X : Type*} [MeasurableSpace X]

/-- The Born probability measure `|Ψ|²·μ` of a wave-function. -/
noncomputable def bornMeasure (Ψ : X → ℂ) (μ : Measure X) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (‖Ψ x‖ ^ 2))

/-
The Born measure of a normalized `L²` wave-function is a probability
measure (Chapter B `born_backward`, re-packaged).
-/


/-- Conditioning by projection: zero the non-matching components, renormalize. -/
noncomputable def conditionedState (Ψ : X → ℂ) (μ : Measure X) (E : Set X) : X → ℂ :=
  fun x => (Real.sqrt ((bornMeasure Ψ μ) E).toReal)⁻¹ • E.indicator Ψ x



/-! ## U.3 — Fock-space layer: the exponential property `Sym(M ⊕ N) ≅ Sym M ⊗ Sym N` -/

section Fock

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Forward map of the exponential property: `Sym(M × N) → Sym M ⊗ Sym N`,
sending a generator `(m, n)` to `ι m ⊗ 1 + 1 ⊗ ι n`. -/
noncomputable def prodToTensor :
    SymmetricAlgebra R (M × N) →ₐ[R] (SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R N) :=
  SymmetricAlgebra.lift
    ((Algebra.TensorProduct.includeLeft.toLinearMap ∘ₗ SymmetricAlgebra.ι R M)
        ∘ₗ (LinearMap.fst R M N)
      + (Algebra.TensorProduct.includeRight.toLinearMap ∘ₗ SymmetricAlgebra.ι R N)
        ∘ₗ (LinearMap.snd R M N))

/-- Backward map of the exponential property: `Sym M ⊗ Sym N → Sym(M × N)`. -/
noncomputable def tensorToProd :
    (SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R N) →ₐ[R] SymmetricAlgebra R (M × N) :=
  Algebra.TensorProduct.lift
    (SymmetricAlgebra.lift (SymmetricAlgebra.ι R (M × N) ∘ₗ LinearMap.inl R M N))
    (SymmetricAlgebra.lift (SymmetricAlgebra.ι R (M × N) ∘ₗ LinearMap.inr R M N))
    (fun _ _ => Commute.all _ _)

theorem tensorToProd_comp_prodToTensor :
    (tensorToProd R M N).comp (prodToTensor R M N) = AlgHom.id R _ := by
  ext x; all_goals simp [ tensorToProd, prodToTensor ]

theorem prodToTensor_comp_tensorToProd :
    (prodToTensor R M N).comp (tensorToProd R M N) = AlgHom.id R _ := by
  ext x; all_goals simp [ prodToTensor, tensorToProd ]

/-- **U.3 — the exponential property of the (bosonic) Fock functor.**
`Sym(M × N) ≅ Sym M ⊗ Sym N` as `R`-algebras: the tensor product of two Fock
spaces is again a Fock space (so no infinite-dimensional tensor product is
needed).

§0 S7 / `../unfer`: this exponential law is the implemented Fock layer of the
`nested_fock_algebra` crate (the bosonic symmetric-algebra model reused by the
CCR field package `ChapterF1`). -/
noncomputable def prodEquiv :
    SymmetricAlgebra R (M × N) ≃ₐ[R] (SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R N) :=
  AlgEquiv.ofAlgHom (prodToTensor R M N) (tensorToProd R M N)
    (prodToTensor_comp_tensorToProd R M N) (tensorToProd_comp_prodToTensor R M N)

end Fock

/-! ## U.4 — Non-differentiability of stochastic trajectories (`EXTERNAL` + wrapper) -/

/-
**U.4 wrapper.** Given the (external, cited: Paley–Wiener–Zygmund 1933,
Bertoin 1994) fact that the paths are a.s. nowhere differentiable, the event
that *some* time point is a point of differentiability is null — i.e. its
complement carries full probability.  Fixing the *statement* precisely scopes
the external hypothesis; Mathlib v4.28.0 has no Brownian motion.
-/


/-
The `P(differentiable) = 0` corollary of `no_differentiable_trajectory`.
-/


/-! ## U.5 — Independent components: portfolio risk falls like `1/√n` -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-
**U.5.** For `n` independent components each of variance `σ²`, the variance
of the average `(∑ Xᵢ)/n` is `σ²/n` — the Central-Limit `1/√n` reduction of
aggregate portfolio risk (no CLT needed; only additivity of variance).
-/


/-
Standard-deviation form of `portfolio_risk_inv_sqrt`: the aggregate
standard deviation is `σ/√n`.
-/


end BookProof.ChapterU


