-- Prove2me | Definitions.Def_DesignTest_haarState
-- name    : DesignTest_haarState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:20.540786+00:00
-- url     : https://prove2.me/theorems/d5c26937-9b1c-413f-b859-69c83cbf5cad
-- title:
--   Pure states of $\mathbb C^d$, the Haar state measure $\mathsf H$, and uniform measures on finite lists
-- statement:
--   A **pure state** of $\mathbb C^d$ is represented by a unit vector $\psi\in\mathbb C^d$, $\|\psi\|=1$; the paper's pure state is the rank-one density matrix $|\psi\rangle\langle\psi|\in\mathcal P(d)$, which does not depend on a global phase of $\psi$. An **input** of a testing problem is a probability measure $\nu$ on pure states; a sample is a draw $\psi\sim\nu$.
--
--   The **Haar state measure** $\mathsf H$ is the unique unitarily invariant probability measure on pure states: the law of $U|0\rangle$ for a Haar-random unitary $U\in\mathsf U(d)$. Concretely it is the uniform (normalized surface) measure on the unit sphere of $\mathbb C^d\cong\mathbb R^{2d}$. For $d\ge1$ it is a probability measure.
--
--   For a finite list $\varphi_1,\dots,\varphi_L$ of pure states, the **uniform measure on the list** is
--   $$\nu_0=\frac1L\sum_{j=1}^{L}\delta_{\varphi_j},$$
--   repeated entries counting with multiplicity.
--
--   These are the inputs, the reference measure and the finite designs on which every statement of the mission is phrased.
--
--   **Formalization Note** Unit vectors are the subtype `Metric.sphere 0 1` of `EuclideanSpace ℂ (Fin d)` with its Borel σ-algebra. $\mathsf H$ is Mathlib's cone measure `Measure.toSphere` of an additive Haar measure on $\mathbb C^d$ (as a real space), divided by its total mass. Its image under $\psi\mapsto|\psi\rangle\langle\psi|$ is the unitarily invariant measure on $\mathcal P(d)$, so all moment operators agree with the paper's.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §3.1, p.13 (P(d)); Definition 3.5, p.15; Definition 3.10, p.17; proof of Theorem 4.16, p.43 (ν₀ = L⁻¹ Σ δ_{φ_j})

import Mathlib

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Pure states of `ℂ^d` as unit vectors** (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and
Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), §3.1, p.13 (`P(d)`); Definition 3.5, p.15).

**Formalization Note.** The paper's pure states are the rank-one density matrices `|ψ⟩⟨ψ| ∈ P(d)`.
Here a pure state is a unit vector `ψ` of `ℂ^d = EuclideanSpace ℂ (Fin d)`, with the Borel σ-algebra of
the subtype; `|ψ⟩⟨ψ|` is recovered from `ψ` and does not depend on the global phase. Coordinates are
indexed by `Fin d` (the page's fixed basis `{|i⟩}`, shifted to start at `0`). -/
abbrev PureVec (d : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℂ (Fin d)) 1

/-- **The Haar state measure `H`** on pure states of `ℂ^d` (STOC 2027 submission (sha256 e2f0a429…),
Definition 3.10, p.17; §3.1, p.13): the unique unitarily invariant probability measure on `P(d)`.

**Formalization Note.** It is the normalized surface measure on the unit sphere of `ℂ^d`, viewed as the
real vector space `ℝ^{2d}`: Mathlib's cone measure `Measure.toSphere` of an additive Haar measure, divided
by its total mass. The push-forward of the Haar measure on `U(d)` under `U ↦ U|0⟩` is this uniform sphere
measure, and the paper's `H` on `P(d)` is its image under `ψ ↦ |ψ⟩⟨ψ|`; every quantity in this mission
depends on `ψ` only through `|ψ⟩⟨ψ|` when it is evaluated against `H` (moment operators), so the two
encodings give the same values. For `d ≥ 1` it is a probability measure (instance below). -/
noncomputable def haarState (d : ℕ) : Measure (PureVec d) :=
  ((Measure.addHaar : Measure (EuclideanSpace ℂ (Fin d))).toSphere Set.univ)⁻¹ •
    (Measure.addHaar : Measure (EuclideanSpace ℂ (Fin d))).toSphere

instance haarState.instIsProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (haarState d) := by
  constructor
  unfold haarState
  rw [Measure.smul_apply, smul_eq_mul]
  have h0 : (Measure.addHaar : Measure (EuclideanSpace ℂ (Fin d))).toSphere Set.univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)
  exact ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)

/-- **The uniform measure on a finite list of pure states** `L⁻¹ Σ_j δ_{φ_j}` (STOC 2027 submission
(sha256 e2f0a429…), proof of Theorem 4.16, p.43: `ν₀ = L⁻¹ Σ_{j=1}^{L} δ_{φ_j}`; proof of Corollary 4.17,
p.44). Repeated entries of the list count with multiplicity. For an empty index type it is the zero
measure. -/
noncomputable def unifList {d : ℕ} {ι : Type} [Fintype ι] (φ : ι → PureVec d) :
    Measure (PureVec d) :=
  ((Fintype.card ι : ENNReal))⁻¹ • ∑ i, Measure.dirac (φ i)

end DesignTest


