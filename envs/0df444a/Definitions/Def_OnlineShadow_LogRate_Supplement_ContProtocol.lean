-- Prove2me | Definitions.Def_OnlineShadow_LogRate_Supplement_ContProtocol
-- name    : OnlineShadow_LogRate_Supplement_ContProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:53:49.380956+00:00
-- url     : https://prove2.me/theorems/4de6cf4f-813b-46ec-9d01-8b4643587344
-- title:
--   Continuous-outcome online protocol on $n$ copies: one Kraus density over $\mathbb R$ per round
-- statement:
--   A **continuous-outcome online protocol** holding $n$ copies of an unknown $d$-dimensional state acts on the register $(\mathbb C^d)^{\otimes n}$. In each round, after receiving the current observable $A$, it measures the register with an instrument whose outcome $y$ ranges over $\mathbb R$: a **Kraus density** $y\mapsto K_{h,A}(y)$ of operators on $(\mathbb C^d)^{\otimes n}$ satisfying the completeness relation
--   $$\int_{\mathbb R}K_{h,A}(y)^\dagger K_{h,A}(y)\,\mathrm dy=1,$$
--   and on outcome $y$ it announces an answer $\widehat\mu_{h,A}(y)\in\mathbb R$. Both may depend on the history $h$ of earlier (observable, outcome) pairs and on $A$, but not on the unknown state.
--
--   This is the protocol model of Section 5: the measurement with compact noise of Definition 5.1, with Kraus density $K(y)=\phi_\omega(y\mathbb 1-\overline A)$ and answer $\widehat\mu=y$ (Algorithm 2), is of this form; completeness is eq. (11).
--
--   **Formalization Note** Completeness is stated entrywise: every entry of $K^\dagger K$ is Lebesgue integrable in $y$ and integrates to the corresponding entry of the identity. The Kraus density and the answer map are jointly Borel measurable in (history, observable, outcome) on histories of each fixed length (the round index), a matrix being read as its array of entries. The basis of $(\mathbb C^d)^{\otimes n}$ is indexed by `Fin n → Fin d`; there is no ancilla register.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1, p. 3; Definition 5.1, eq. (11) and Algorithm 2, p. 18

import Mathlib

open scoped Matrix
open MeasureTheory

namespace OnlineShadow.LogRate.Supplement

/-- A **continuous-outcome online protocol** holding `n` copies of a `d`-dimensional state, acting on the
register `(ℂ^d)^{⊗n}` with basis indexed by `Fin n → Fin d` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1, p.3,
and the protocol model of Definition 5.1 and Algorithm 2, pp.18–19).

In each round, after receiving the current observable `A`, the protocol measures the register with an
instrument whose outcome `y` ranges over `ℝ` (with Lebesgue measure): a **Kraus density**
`y ↦ kraus h A y` with completeness `∫ (kraus h A y)ᴴ (kraus h A y) dy = 1` (cf. eq. (11), p.18),
and on outcome `y` it announces the answer `answer h A y`. Both may depend on the history `h` of earlier
(observable, outcome) pairs and on `A`, but not on the unknown state.

**Formalization Note** Completeness is stated entrywise, each entry of `KᴴK` being Lebesgue integrable
with integral the entry of the identity, so the Bochner integral is a genuine integral (never the junk
value `0`). The Kraus density and the answer map are jointly Borel measurable in (history, observable,
outcome) on histories of each fixed length `t` (the round index), where a matrix is read as its array of
entries (product σ-algebra = Borel σ-algebra of the matrix space). This makes the success probability of
`contSuccessProb` the integral of a measurable function. Algorithm 2 (Kraus density
`ϕ_ω(y·1 − Ā)`, answer `y`) has this form. There is no ancilla register. -/
structure ContProtocol (d n : ℕ) where
  /-- Kraus density at outcome `y` in the round with history `h` and current observable `A`. -/
  kraus : List (Matrix (Fin d) (Fin d) ℂ × ℝ) → Matrix (Fin d) (Fin d) ℂ → ℝ →
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ
  /-- The answer `μ̂` announced on outcome `y`. -/
  answer : List (Matrix (Fin d) (Fin d) ℂ × ℝ) → Matrix (Fin d) (Fin d) ℂ → ℝ → ℝ
  /-- Joint measurability of the Kraus density on histories of length `t`. -/
  kraus_measurable : ∀ t : ℕ,
    Measurable (fun p : (Fin t → (Fin d → Fin d → ℂ) × ℝ) × (Fin d → Fin d → ℂ) × ℝ =>
      Matrix.of.symm (kraus (List.ofFn fun i => (Matrix.of (p.1 i).1, (p.1 i).2))
        (Matrix.of p.2.1) p.2.2))
  /-- Joint measurability of the answer map on histories of length `t`. -/
  answer_measurable : ∀ t : ℕ,
    Measurable (fun p : (Fin t → (Fin d → Fin d → ℂ) × ℝ) × (Fin d → Fin d → ℂ) × ℝ =>
      answer (List.ofFn fun i => (Matrix.of (p.1 i).1, (p.1 i).2)) (Matrix.of p.2.1) p.2.2)
  /-- Every entry of `KᴴK` is Lebesgue integrable in the outcome. -/
  integrable : ∀ h A i j, Integrable (fun y : ℝ => ((kraus h A y)ᴴ * kraus h A y) i j)
  /-- Completeness: `∫ (kraus h A y)ᴴ (kraus h A y) dy = 1`, entrywise. -/
  complete : ∀ h A i j,
    ∫ y : ℝ, ((kraus h A y)ᴴ * kraus h A y) i j = (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) i j

end OnlineShadow.LogRate.Supplement


