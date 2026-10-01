-- Prove2me | Definitions.Def_ChapterF7
-- name    : ChapterF7
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:55:26.773683+00:00
-- url     : https://prove2.me/theorems/b15d72a9-652f-45a8-a797-6550d8a7aebb
-- title:
--   Chapter F7
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterF7.lean`): generated def bundle for ChapterF7. See BookProof/ChapterF7.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterF7.lean

import Mathlib


/-!
# Chapter F7 — Quantum Flow Matching: the concrete `x̂` / `p̂` model (roadmap N14, §4)

This file supplies the concrete function-space realization underlying the
algebraic Hermiticity cores of `ChapterF5.lean` (deliverables **F2.1** and
**F2.2** of the *Quantum Flow Matching* package; source `RiemannProof/QFM.tex`
§4, eqs. (4.2)–(4.6); reference implementation `../unfer/qfm/`).  It follows
§0 S7 of the roadmap (the Mehler/Kopperman generative flow).

The state space is the Schwartz space `𝓢(ℝ, ℂ)` with the (sesquilinear) `L²`
pairing `⟪f, g⟫ = ∫ conj (f x) · g x`.  On this dense domain the two elementary
observables of eq. (4.2) are:

* **position** `(x̂ Ψ)(x) = x · Ψ(x)` — multiplication by the real coordinate;
* **momentum** `(p̂ Ψ)(x) = −i Ψ′(x)` — the derivative operator.

## Deliverables

* `l2pair` — the `L²` pairing, together with its (conjugate-)bilinearity
  (`l2pair_add_left/right`, `l2pair_sub_left/right`, `l2pair_smul_left/right`)
  and the integrability helper `l2pair_integrable`.
* `IsL2Symmetric` — symmetry of an operator w.r.t. `l2pair`.
* **position is symmetric** (`position_l2Symmetric`), and more generally
  multiplication by any real function of temperate growth — the concrete
  velocity/potential operator `v(x̂)` — is symmetric (`mulOp_l2Symmetric`).
* **momentum is symmetric** (`momentum_l2Symmetric`), the concrete
  integration-by-parts fact `schwartz_integration_by_parts` (`∫ f′ g = −∫ f g′`
  for Schwartz `f, g`, boundary terms vanishing).
* **F2.1 concretely** (§4 eq. 4.2): the symmetrized product of two symmetric
  operators is symmetric (`anticomm_l2Symmetric`), hence the continuity
  Hamiltonian `H = ½(p̂ v(x̂) + v(x̂) p̂)` is Hermitian
  (`continuityHamiltonian_l2Symmetric`).
* **F2.2 concretely** (§4 eqs. 4.4–4.6): `i·[K, V]` is symmetric when `K, V`
  are (`i_comm_l2Symmetric`); with `K = ½ p̂·p̂` (`kinetic_l2Symmetric`) this is
  the conservative continuity Hamiltonian `H^c = i[K, V(x̂)]`
  (`conservativeHamiltonian_l2Symmetric`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis**.  Cites `../unfer` crate
`qfm/src/potential.rs` (the Hermitian continuity generator).
-/

open SchwartzMap MeasureTheory Complex
open scoped BigOperators

namespace BookProof.ChapterF7

noncomputable section

/-! ## The `L²` pairing -/

/-- The sesquilinear `L²` pairing on Schwartz space (conjugate-linear in the
first slot): `⟪f, g⟫ = ∫ conj (f x) · g x`. -/
def l2pair (f g : 𝓢(ℝ, ℂ)) : ℂ := ∫ x, (starRingEnd ℂ) (f x) * g x















/-- An operator on Schwartz space is **`L²`-symmetric** (Hermitian on the dense
Schwartz domain) if it moves across the `L²` pairing. -/
def IsL2Symmetric (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) : Prop :=
  ∀ f g, l2pair (T f) g = l2pair f (T g)

/-! ## Position and, more generally, real multiplication operators -/

/-- Multiplication by a real function `v` of temperate growth — the concrete
velocity/potential operator `v(x̂)`, `(v(x̂) Ψ)(x) = v(x) · Ψ(x)`. -/
def mulOp (v : ℝ → ℝ) (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hv





/-- The position operator `(x̂ Ψ)(x) = x · Ψ(x)`. -/
def position : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  mulOp (fun x => x) Function.Complex.hasTemperateGrowth_ofReal



/-! ## Momentum and integration by parts -/



/-- The momentum operator `(p̂ Ψ)(x) = −i Ψ′(x)`. -/
def momentum : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-Complex.I) • SchwartzMap.derivCLM ℂ ℂ





/-! ## F2.1 and F2.2 concretely -/









/-- The kinetic operator `K = ½ p̂·p̂`, `(K Ψ)(x) = −½ Ψ″(x)`. -/
def kinetic : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((1 : ℂ) / 2) • momentum.comp momentum





end

end BookProof.ChapterF7


