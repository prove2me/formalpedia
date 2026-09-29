-- Prove2me | Definitions.Def_HairerSPDE_CameronMartin
-- name    : HairerSPDE_CameronMartin
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T21:17:01.08214+00:00
-- url     : https://prove2.me/theorems/546bbe6c-1d41-4a7e-b1ee-af3f33cdcdaa
-- title:
--   The Cameron–Martin norm and space of a Gaussian measure
-- statement:
--   **The Cameron–Martin space of a Gaussian measure.**
--
--   Let $B$ be a separable Banach space with dual $B^{*}$ and let $\mu$ be a Borel probability measure on $B$ with finite second moment. Its *covariance form* is the bounded bilinear form on $B^{*}$
--
--   $$ C_\mu(\ell,\ell') \;=\; \int_B \bigl(\ell(x)-\mu[\ell]\bigr)\bigl(\ell'(x)-\mu[\ell']\bigr)\, \mu(dx), $$
--
--   which for a centred measure is Hairer's $C_\mu(\ell,\ell') = \int_B \ell(x)\ell'(x)\,\mu(dx)$ of equation (4.2).
--
--   This bundle introduces two objects built from it. The **Cameron–Martin norm** of a point $h\in B$ is
--
--   $$ \|h\|_\mu \;=\; \sup\bigl\{\, \ell(h) \;:\; \ell\in B^{*},\ C_\mu(\ell,\ell)\le 1 \,\bigr\} \;\in\; [0,\infty], $$
--
--   the supremum being taken in the extended non-negative reals, so that it is $+\infty$ exactly when $\ell \mapsto \ell(h)$ is unbounded on the unit ball of the covariance form. Because $-\ell$ is admissible whenever $\ell$ is, the supremum equals $\sup|\ell(h)|$ over the same set, and it is always attained above by $0$ (take $\ell=0$), so $\|0\|_\mu=0$.
--
--   The **Cameron–Martin space** is then
--
--   $$ H_\mu \;=\; \{\, h\in B \;:\; \|h\|_\mu<\infty \,\}. $$
--
--   This is Hairer's Definition 4.26 in the equivalent form established in Exercise 4.38 (equation (4.12)): the classical definition builds $H_\mu$ as the completion, under $\|h\|_\mu^{2}=C_\mu(h^{*},h^{*})$, of the set of $h$ admitting a representer $h^{*}\in B^{*}$ with $C_\mu(h^{*},\ell)=\ell(h)$ for all $\ell$; the supremum description above extends that norm to all of $B$ with value $+\infty$ off $H_\mu$, and so needs no completion.
--
--   The Cameron–Martin space is the object that governs which translations leave a Gaussian measure quasi-invariant, and it is the standard input to Girsanov-type change of measure, large-deviation rate functions for Gaussian measures, and Malliavin calculus.
--
--   **Formalization Note.** The covariance form is Mathlib's `covarianceBilinDual`, which is the form displayed above when the measure has a finite second moment and is set to $0$ otherwise; for Gaussian measures the finite-moment branch always applies, by Fernique's theorem. The norm takes values in `ℝ≥0∞` and membership in $H_\mu$ is expressed as finiteness of that value.
-- source:
--   M. Hairer, *An Introduction to Stochastic PDEs*, lecture notes, arXiv:0907.4178v2 (3 Jul 2023), p. 27 Definition 4.26 and p. 29 Exercise 4.38 (eq. (4.12)); covariance form (4.2), p. 20

import Mathlib

/-!
# The Cameron–Martin space of a Gaussian measure

Formalisation of the definitions in Section 4.2 of

  M. Hairer, *An Introduction to Stochastic PDEs*, arXiv:0907.4178:

Definition 4.26 (the Cameron–Martin space `H_μ` of a Gaussian measure `μ` on a separable
Banach space `B`) in the equivalent form of Exercise 4.38,

  `‖h‖_μ = sup {ℓ(h) : ℓ ∈ B*, C_μ(ℓ, ℓ) ≤ 1}`,   `H_μ = {h ∈ B : ‖h‖_μ < ∞}`,

where `C_μ` is the covariance form (4.2) of `μ`, available in Mathlib as
`ProbabilityTheory.covarianceBilinDual`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HairerSPDE

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]

/-- The Cameron–Martin norm `‖h‖_μ` of `h ∈ B` with respect to a measure `μ` on a Banach
space `B`, in the form of Hairer's Exercise 4.38:
`‖h‖_μ = sup {ℓ(h) : ℓ ∈ B*, C_μ(ℓ, ℓ) ≤ 1}`, where `C_μ = covarianceBilinDual μ` is the
covariance form (4.2). The supremum is taken in `ℝ≥0∞`, so that it is `∞` exactly when the
set of values `ℓ(h)` is unbounded on the unit ball of the covariance form. -/
noncomputable def cameronMartinNorm (μ : Measure B) (h : B) : ℝ≥0∞ :=
  ⨆ L : {L : StrongDual ℝ B // covarianceBilinDual μ L L ≤ 1},
    ENNReal.ofReal ((L : StrongDual ℝ B) h)

/-- The Cameron–Martin space `H_μ ⊆ B` of a measure `μ`, as the set of points of finite
Cameron–Martin norm (Definition 4.26 in the form of Exercise 4.38). -/
def cameronMartinSpace (μ : Measure B) : Set B := {h : B | cameronMartinNorm μ h ≠ ∞}

@[simp] lemma mem_cameronMartinSpace_iff (μ : Measure B) (h : B) :
    h ∈ cameronMartinSpace μ ↔ cameronMartinNorm μ h ≠ ∞ := Iff.rfl

end HairerSPDE


