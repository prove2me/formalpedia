-- Prove2me | Definitions.Def_WildeQIT_Gentle_postMeasurementState
-- name    : WildeQIT_Gentle_postMeasurementState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:03.300684+00:00
-- url     : https://prove2.me/theorems/5eef262e-be0b-4add-bbd6-623a0aba4adb
-- title:
--   Post-measurement state $\rho'=\sqrt\Lambda\rho\sqrt\Lambda/\mathrm{Tr}\{\Lambda\rho\}$
-- statement:
--   Let $\rho$ be a density operator and $\Lambda$ a measurement operator, $0\le\Lambda\le I$. The **post-measurement state** after the outcome corresponding to $\Lambda$ is detected is
--
--   $$\rho'\equiv\frac{\sqrt\Lambda\,\rho\,\sqrt\Lambda}{\operatorname{Tr}\{\Lambda\rho\}} .$$
--
--   It is the state compared with $\rho$ in the gentle measurement lemma (Lemma 9.4.1).
--
--   **Formalization Note** $\sqrt\Lambda$ is the positive square root `CFC.sqrt`, the same square root as in the published trace norm. Lean's convention $0^{-1}=0$ gives $\rho'=0$ when $\operatorname{Tr}\{\Lambda\rho\}=0$, a case the book leaves undefined; statements using this definition assume $\operatorname{Tr}\{\Lambda\rho\}\neq0$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.4.1, eq. (9.196), p. 277

import Mathlib.Analysis.Matrix.Order

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Lemma 9.4.1, eq. (9.196),
p. 277.
-/

open Matrix
open scoped MatrixOrder

namespace WildeQIT.Gentle

/-- **Post-measurement state** (Wilde, arXiv:1106.1445v8, eq. (9.196), p. 277). For a state `ρ`
and a measurement operator `Λ` (`0 ≤ Λ ≤ I`), the state after the outcome `Λ` is detected:
`ρ′ ≡ √Λ ρ √Λ / Tr{Λρ}`.

**Formalization Note.** `√Λ` is Mathlib's positive square root `CFC.sqrt` (the same square root
as in the published `WildeQIT.traceNorm`). The trace `Tr{Λρ}` is the complex trace of `Λ * ρ`
(real for positive semi-definite `Λ`, `ρ`). Lean's `(0 : ℂ)⁻¹ = 0` makes the value `0` when
`Tr{Λρ} = 0`, a case the book leaves undefined; statements using this definition assume
`Tr{Λρ} ≠ 0`. -/
noncomputable def postMeasurementState {n : Type} [Fintype n] [DecidableEq n]
    (Λ ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  ((Λ * ρ).trace)⁻¹ • (CFC.sqrt Λ * ρ * CFC.sqrt Λ)

end WildeQIT.Gentle


