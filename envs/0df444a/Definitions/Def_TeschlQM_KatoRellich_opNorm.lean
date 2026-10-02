-- Prove2me | Definitions.Def_TeschlQM_KatoRellich_opNorm
-- name    : TeschlQM_KatoRellich_opNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:09:48.065097+00:00
-- url     : https://prove2.me/theorems/99ed40eb-4ddf-41c4-a70c-c541ecb2e059
-- title:
--   Operator norm of a linear operator, with value ∞ when unbounded
-- statement:
--   For a linear operator $T$ with domain $\mathfrak{D}(T)$ in a complex Hilbert space, its **norm** is
--   $$\|T\| = \sup_{0 \ne \varphi \in \mathfrak{D}(T)} \frac{\|T\varphi\|}{\|\varphi\|} \in [0, \infty].$$
--   It is finite exactly when $T$ is bounded on its domain.
--
--   It gives the norms $\|BR_A(z)\|$ of Lemmas 6.2 and 6.3.
--
--   **Formalization Note.** The value lies in `ℝ≥0∞`, so an unbounded operator has norm $\infty$ rather than a junk value. The vector $\varphi = 0$ contributes $0/0 = 0$ in `ℝ≥0∞`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 134, Section 6.1 (notation ‖BR_A(z)‖ of Lemmas 6.2, 6.3)

import Mathlib

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- The operator norm `‖T‖ = sup_{φ ∈ 𝔇(T), φ ≠ 0} ‖Tφ‖ / ‖φ‖ ∈ [0, ∞]` of a linear operator
`T : 𝔇(T) → ℌ`. It is finite exactly when `T` is bounded on its domain; the value `∞` stands for an
unbounded `T` (never a junk `0`). The term `φ = 0` contributes `0 / 0 = 0`. -/
noncomputable def opNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) : ℝ≥0∞ :=
  ⨆ φ : T.domain, (‖T φ‖₊ : ℝ≥0∞) / (‖(φ : H)‖₊ : ℝ≥0∞)

end TeschlQM.KatoRellich


