-- Prove2me | Definitions.Def_InfHorizonVP_dhSuperdiff
-- name    : InfHorizonVP_dhSuperdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:36.775955+00:00
-- url     : https://prove2.me/theorems/b8763953-b379-4466-9d7d-1d205ace578a
-- title:
--   Dini–Hadamard superdifferential $\partial^+\varphi(\bar x)$
-- statement:
--   For $\varphi:E\to[-\infty,+\infty]$ finite at $\bar x$, the **Dini–Hadamard superdifferential** is
--   $$
--   \partial^+\varphi(\bar x)=\{x^*\in E^*\mid\langle x^*,v\rangle\ge\varphi^+(\bar x;v)\ \ \forall v\in E\}.
--   $$
--   The partial superdifferential $\partial^+_xL(t,\bar x,\bar y)$ is that of $L(t,\cdot,\bar y)$ at $\bar x$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.5; §3.2, p.10

import Mathlib
import Definitions.Def_InfHorizonVP_dhUpperDeriv
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Dini–Hadamard superdifferential `∂⁺φ(x̄)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.5: "the Dini–Hadamard superdifferential of ϕ at x̄
is defined by ∂⁺ϕ(x̄) := {x* ∈ E* | ⟨x*, v⟩ ≥ ϕ⁺(x̄; v) ∀v ∈ E}." Partial version, p.10: "Then
∂⁺ₓL(t, x̄, ȳ) is the Dini–Hadamard partial superdifferential of L(t, ·, ȳ) at x̄".

**Formalization Note.** `E* = E →L[ℝ] ℝ`; `φ(x̄)` is required to be finite, as for
`dhSubdiff`. For the real-valued `L`, `∂⁺ₓL(t, x̄, ȳ)` is
`dhSuperdiff (fun z => (L t z ȳ : EReal)) x̄`. -/
def dhSuperdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → EReal) (x : E) : Set (E →L[ℝ] ℝ) :=
  {z | (∃ r : ℝ, φ x = r) ∧ ∀ v : E, dhUpperDeriv φ x v ≤ ((z v : ℝ) : EReal)}

end InfHorizonVP


