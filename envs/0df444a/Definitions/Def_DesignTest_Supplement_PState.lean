-- Prove2me | Definitions.Def_DesignTest_Supplement_PState
-- name    : DesignTest_Supplement_PState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:02:43.028515+00:00
-- url     : https://prove2.me/theorems/536dc53a-b645-4443-a953-93a2616e3f74
-- title:
--   Pure states $P(d)$ as rank-one projectors and the Haar measure on $P(d)$
-- statement:
--   For a unit vector $\psi\in\mathbb C^d$ let $|\psi\rangle\langle\psi|$ be its rank-one projector. The set of **pure states** $P(d)$ is the set of all such projectors, with the Borel σ-algebra inherited from $d\times d$ complex matrices. The **Haar measure** $H$ on $P(d)$ is the law of $|\psi\rangle\langle\psi|$ for a Haar-random state $|\psi\rangle=U|0\rangle$, the unique unitarily invariant probability measure on $P(d)$.
--
--   Theorem 4.1 is stated for probability measures on $P(d)$; the classical description of a state-preparation sample is $|\psi\rangle\langle\psi|$ (Definition 3.9), which carries no global phase.
--
--   **Formalization Note.** $H$ is the push-forward of the mission's uniform sphere measure `DesignTest.haarState d` under the continuous map $\psi\mapsto|\psi\rangle\langle\psi|$ (a sanity file proves the map measurable and $H$ a probability measure).
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §3.1, p.13; Definition 3.9, p.16; Definition 3.10, p.17

import Mathlib
import Definitions.Def_DesignTest_haarState
import Definitions.Def_TroppMatrixConcentration_probability

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory

/-- The rank-one projector `|ψ⟩⟨ψ|` of a unit vector `ψ ∈ ℂ^d` (A. Kawachi, Y. Nakata, Y. Takeuchi,
*Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), §3.1, p.13), entry
`(i, j)` equal to `ψ_i · conj ψ_j`. -/
noncomputable def projOf {d : ℕ} (ψ : DesignTest.PureVec d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j =>
    (ψ : EuclideanSpace ℂ (Fin d)) i * star ((ψ : EuclideanSpace ℂ (Fin d)) j)

/-- **The pure states `P(d)`** as the set of rank-one projectors `|ψ⟩⟨ψ|` on `ℂ^d` (STOC 2027 submission
(sha256 e2f0a429…), §3.1, p.13; Definition 3.9, p.16: the classical description of `S_ψ` is the
density matrix `|ψ⟩⟨ψ|`).

**Formalization Note.** A subtype of `d × d` complex matrices with the subspace σ-algebra of the Borel
σ-algebra of matrices (`TroppMatrixConcentration.matrixMeasurableSpace`). Unlike the unit sphere
`PureVec d`, a point of `P(d)` carries no global phase. -/
abbrev PState (d : ℕ) : Type :=
  {P : Matrix (Fin d) (Fin d) ℂ // ∃ ψ : DesignTest.PureVec d, P = projOf ψ}

/-- The map `ψ ↦ |ψ⟩⟨ψ|` from unit vectors to `P(d)`. -/
noncomputable def toPState {d : ℕ} (ψ : DesignTest.PureVec d) : PState d := ⟨projOf ψ, ψ, rfl⟩

/-- **The Haar measure `H` on `P(d)`** (STOC 2027 submission (sha256 e2f0a429…), Definition 3.10, p.17):
the distribution of `|ψ⟩⟨ψ|` for a Haar-random state `|ψ⟩ = U|0⟩`, i.e. the unique unitarily invariant
probability measure on `P(d)`.

**Formalization Note.** The push-forward of the uniform sphere measure `DesignTest.haarState d` (the law
of `U|0⟩`) under the continuous map `ψ ↦ |ψ⟩⟨ψ|`. -/
noncomputable def haarProj (d : ℕ) : Measure (PState d) :=
  Measure.map toPState (DesignTest.haarState d)

end DesignTest.Supplement


