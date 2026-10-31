-- Prove2me | Definitions.Def_InfHorizonVP_dhSubdiff
-- name    : InfHorizonVP_dhSubdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:24.793106+00:00
-- url     : https://prove2.me/theorems/9ddc60fe-136f-462c-aa1e-278ded66bb69
-- title:
--   Dini–Hadamard subdifferential $\partial^-\varphi(\bar x)$
-- statement:
--   For $\varphi:E\to[-\infty,+\infty]$ finite at $\bar x$, the **Dini–Hadamard subdifferential** is
--   $$
--   \partial^-\varphi(\bar x)=\{x^*\in E^*\mid\langle x^*,v\rangle\le\varphi^-(\bar x;v)\ \ \forall v\in E\}.
--   $$
--   The partial subdifferential $\partial^-_xV(t,x)$ is that of $V(t,\cdot)$ at $x$.
--
--   **Formalization Note** $E^*$ is the space of continuous linear functionals. The page defines $\partial^-\varphi(\bar x)$ at points of the effective domain; here it is empty when $\varphi(\bar x)=\pm\infty$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.5

import Mathlib
import Definitions.Def_InfHorizonVP_dhLowerDeriv
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Dini–Hadamard subdifferential `∂⁻φ(x̄)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.5: "The Dini–Hadamard subdifferential of ϕ at x̄ is
defined by ∂⁻ϕ(x̄) := {x* ∈ E* | ⟨x*, v⟩ ≤ ϕ⁻(x̄; v) ∀v ∈ E}", for `x̄ ∈ dom ϕ` (p.5).

**Formalization Note.** `E* = E →L[ℝ] ℝ`. The page defines the lower derivative only at points of
the effective domain; here `∂⁻φ(x̄)` requires `φ(x̄)` finite (it is empty otherwise). The partial
subdifferential `∂⁻ₓV(t, x)` is `dhSubdiff (V t) x`. -/
def dhSubdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → EReal) (x : E) : Set (E →L[ℝ] ℝ) :=
  {z | (∃ r : ℝ, φ x = r) ∧ ∀ v : E, ((z v : ℝ) : EReal) ≤ dhLowerDeriv φ x v}

end InfHorizonVP


