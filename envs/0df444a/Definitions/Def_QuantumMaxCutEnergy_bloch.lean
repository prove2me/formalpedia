-- Prove2me | Definitions.Def_QuantumMaxCutEnergy_bloch
-- name    : QuantumMaxCutEnergy_bloch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-08T19:23:03.501186+00:00
-- url     : https://prove2.me/theorems/d50ff8c8-e4f8-4c47-b39d-e9233d94d7ed
-- title:
--   The Bloch vector of a qubit amplitude pair
-- statement:
--   **The Bloch vector of a qubit.**
--
--   An amplitude pair $(\alpha,\beta)\in\mathbb C^2$ determines the Bloch vector
--   $$r(\alpha,\beta)=\big(2\operatorname{Re}(\bar\alpha\beta),\;2\operatorname{Im}(\bar\alpha\beta),\;|\alpha|^2-|\beta|^2\big)\in\mathbb R^3,$$
--   written in real coordinates so that no conjugation appears: the first two components are $2(\alpha_r\beta_r+\alpha_i\beta_i)$ and $2(\alpha_r\beta_i-\alpha_i\beta_r)$.
--
--   For normalised pairs, $|r|^2=(|\alpha|^2+|\beta|^2)^2=1$, so the Bloch vector lies on the unit sphere, and conversely every unit vector arises this way. This is the parametrisation used by the rank-three rounding: a Bloch assignment $r_1,\dots,r_n$ is the same data as a product state of $n$ qubits, which is why the classical relaxation objective evaluated at the Gram matrix of the $r_i$ is exactly the quantum energy of that product state.
--
--   The file also fixes the two coordinate simp lemmas used downstream.
-- source:
--   Bloch sphere parametrisation of a qubit; used to identify product states with Bloch assignments in the Anshu-Gosset-Morenz rank-three rounding (TQC 2020, doi 10.4230/LIPIcs.TQC.2020.7).

import Mathlib

/-!
# The Bloch parametrisation of a qubit

A qubit amplitude pair `(α, β) : ℂ × ℂ` determines the Bloch vector

  `bloch α β = (2 Re (ᾱβ), 2 Im (ᾱβ), |α|² − |β|²)`,

written here in real coordinates to avoid conjugation: the first two entries are
`2 (α.re β.re + α.im β.im)` and `2 (α.re β.im − α.im β.re)`.

For normalised pairs the two-qubit correlation identity holds:
`2 |βa αb − αa βb|² = 1 − ⟪bloch αa βa, bloch αb βb⟫`. This is the algebraic link between product
states and the classical relaxation objective, proved separately.
-/

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- The Bloch vector of a qubit amplitude pair. -/
noncomputable def bloch (α β : ℂ) : Fin 3 → ℝ :=
  ![2 * (α.re * β.re + α.im * β.im), 2 * (α.re * β.im - α.im * β.re),
    Complex.normSq α - Complex.normSq β]

end QuantumMaxCutEnergy


