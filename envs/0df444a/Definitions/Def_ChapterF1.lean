-- Prove2me | Definitions.Def_ChapterF1
-- name    : ChapterF1
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:22:24.531651+00:00
-- url     : https://prove2.me/theorems/5fb7e78d-33fe-4059-b72f-59d00c777006
-- title:
--   Chapter F1
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterF1.lean`): generated def bundle for ChapterF1. See BookProof/ChapterF1.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterF1.lean

import Definitions.Def_ChapterG2
import Mathlib


/-!
# Chapter F1 — the Bargmann–Fock / CCR polynomial field model (roadmap N12, §0 S7)

This file formalizes the *polynomial (Bargmann–Fock) model* of the canonical
commutation relations, following the `../unfer` design decisions (§0 S7 of the
roadmap: Hermitian field representation, quadratic ordering, BRST commutation,
`nested_fock_algebra` / `fock_sirk` crates cited in docstrings).

The one-mode Fock space is modelled by the polynomial ring `ℂ[X]`
(`Polynomial ℂ`), with the vacuum `|0⟩ := 1`.  The two ladder operators are

* annihilation `a := d/dX` (`Polynomial.derivative`), and
* creation `a† := X · (·)` (`LinearMap.mulLeft ℂ X`).

The `n`-mode model is `MvPolynomial (Fin n) ℂ` with `a_i := ∂/∂X_i`.

## Deliverables

* **F1.1 CCR** `ccr` : `[a, a†] = 1` on `ℂ[X]`; `ccr_mv` : `[a_i, a†_j] = δ_ij`.
* **F1.2 Hermitian field representation** `fieldPhi`, `fieldPi`,
  `field_ccr` : `[φ, π] = 2i·1`; the Bargmann pairing `bargmann` with
  `bargmann_creat_annih` (the adjoint relation `⟪a†p, q⟫ = ⟪p, aq⟫`, whence
  `phi_symmetric` / `pi_symmetric`).
* **F1.3 Number operator** `numberOp := a† ∘ a`, `numberOp_monomial` : `N Xⁿ = n·Xⁿ`.
* **F1.4 Quadratic ordering (HEADLINE)** `quadratic_ordering_vacuum` : `⟨0|H|0⟩ = 0`
  for `H := a† a`, contrasted with `symmetric_ordering_vacuum` : the symmetric
  ordering `(a a† + a† a)/2` gives the nonzero zero-point value `1/2` — so the
  `../unfer` quadratic-ordering normalization is a *theorem* (`orderings_differ`).
* **F1.5 BRST bridge** `field_gauge_invariant_iff` : gauge invariance =
  commutation with the BRST operator, on the `ChapterG2` model
  (cites the `fock_sirk` crate).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis**.
-/

open Polynomial Finset
open scoped BigOperators

namespace BookProof.ChapterF1

noncomputable section

/-! ## F1.1 — Canonical commutation relations -/

/-- Annihilation operator `a` on the one-mode Bargmann–Fock space `ℂ[X]`:
differentiation `d/dX` (`../unfer`: `a` is differentiation). -/
noncomputable def annih : ℂ[X] →ₗ[ℂ] ℂ[X] := Polynomial.derivative

/-- Creation operator `a†` on `ℂ[X]`: multiplication by `X`
(`../unfer`: `a†` is multiplication by the coordinate). -/
noncomputable def creat : ℂ[X] →ₗ[ℂ] ℂ[X] := LinearMap.mulLeft ℂ (X : ℂ[X])

@[simp] theorem annih_apply (p : ℂ[X]) : annih p = derivative p := rfl

@[simp] theorem creat_apply (p : ℂ[X]) : creat p = X * p := rfl





/-! ## F1.3 — Number operator -/

/-- Number operator `N := a† ∘ a` (`= X · d/dX`). -/
noncomputable def numberOp : ℂ[X] →ₗ[ℂ] ℂ[X] := creat ∘ₗ annih



/-! ## F1.2 — Hermitian field representation -/

/-- The Hermitian field operator `φ := a† + a`. -/
noncomputable def fieldPhi : ℂ[X] →ₗ[ℂ] ℂ[X] := creat + annih

/-- The conjugate momentum `π := i·(a† − a)`. -/
noncomputable def fieldPi : ℂ[X] →ₗ[ℂ] ℂ[X] := Complex.I • (creat - annih)

/-- **A.1 of `PLAN_LEAN_SPECIALIST_NS_FLOW.md` (name alias).** The position
operator of the Bargmann–Fock model is the Hermitian field `φ = a† + a`; the
Navier–Stokes plan refers to it as `positionOp`. -/
noncomputable abbrev positionOp : ℂ[X] →ₗ[ℂ] ℂ[X] := fieldPhi





/-- The **Bargmann pairing** on `ℂ[X]`: `⟪p, q⟫ = Σ n! · conj(pₙ) · qₙ`,
conjugate-linear in the first slot (Mathlib's inner-product convention).  On
monomials it is `⟪Xᵐ, Xⁿ⟫ = n!·δ_{mn}` (see `bargmann_monomial`).  The sum is
finite (over the union of the supports). -/
noncomputable def bargmann (p q : ℂ[X]) : ℂ :=
  ∑ n ∈ p.support ∪ q.support,
    (n.factorial : ℂ) * (starRingEnd ℂ) (p.coeff n) * q.coeff n









/-! ## F1.4 — Quadratic ordering and the vacuum energy (HEADLINE) -/

/-- The **quadratically-ordered** (normal-ordered) Hamiltonian `H := a† a`
(`../unfer` `nested_fock_algebra`: the quadratic-ordering rule drops the
zero-point scalar).  This is the same operator as `numberOp`. -/
noncomputable def hamiltonian : ℂ[X] →ₗ[ℂ] ℂ[X] := creat ∘ₗ annih



/-- The **symmetrically-ordered** Hamiltonian `H_sym := (a a† + a† a)/2`. -/
noncomputable def hamiltonianSym : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  (2⁻¹ : ℂ) • (annih ∘ₗ creat + creat ∘ₗ annih)





/-! ## F1.5 — BRST bridge to the gauge layer (`ChapterG2`) -/



end

end BookProof.ChapterF1


