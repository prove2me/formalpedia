-- Prove2me | Definitions.Def_DesignTest_empFrame
-- name    : DesignTest_empFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:03.325205+00:00
-- url     : https://prove2.me/theorems/46b5280b-db0c-4de5-9a95-35eef54f2c0f
-- title:
--   Overlaps $h_{ij}=|\langle\psi_i|\psi_j\rangle|^{2t}$ and the empirical frame potential $\widehat F$
-- statement:
--   For pure states $\psi,\phi$ let $h(\psi,\phi)=|\langle\psi|\phi\rangle|^{2t}$. For $m$ sampled states $\psi_1,\dots,\psi_m$, with $h_{ij}=h(\psi_i,\psi_j)$, the **empirical frame potential** is
--   $$\widehat F=\binom m2^{-1}\sum_{1\le i<j\le m}h_{ij}.$$
--
--   It is an unbiased estimator of the frame potential $F^{\mathrm{st}}_t(\nu)$ when the $\psi_i$ are independent draws from $\nu$, and it is the statistic the sample-optimal tester estimates.
--
--   **Formalization Note** Indices are `Fin m` (from $0$); unordered pairs are ordered pairs $(i,j)$ with $i<j$.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Lemma 4.12, p.37

import Mathlib
import Definitions.Def_DesignTest_haarState

set_option autoImplicit false

namespace DesignTest

/-- The overlap `h(ψ, ϕ) := |⟨ψ|ϕ⟩|^{2t}` of two pure states (STOC 2027 submission (sha256 e2f0a429…),
Lemma 4.12, p.37: `h_ij := |⟨ψ_i|ψ_j⟩|^{2t}`). -/
noncomputable def overlapPow {d : ℕ} (t : ℕ) (ψ ϕ : PureVec d) : ℝ :=
  ‖inner ℂ (ψ : EuclideanSpace ℂ (Fin d)) (ϕ : EuclideanSpace ℂ (Fin d))‖ ^ (2 * t)

/-- The unordered pairs `{i, j}`, `i < j`, of `m` sample indices, written as ordered pairs with
`i < j` (indices `Fin m`, from `0`). -/
abbrev Pair (m : ℕ) : Type := {p : Fin m × Fin m // p.1 < p.2}

/-- **The empirical frame potential** `F̂ := C(m, 2)⁻¹ Σ_{1≤i<j≤m} h_ij` of `m` sampled pure states
(STOC 2027 submission (sha256 e2f0a429…), Lemma 4.12, p.37). -/
noncomputable def empFrame {d m : ℕ} (t : ℕ) (ψ : Fin m → PureVec d) : ℝ :=
  ((Nat.choose m 2 : ℕ) : ℝ)⁻¹ * ∑ p : Pair m, overlapPow t (ψ p.1.1) (ψ p.1.2)

end DesignTest


