-- Prove2me | Definitions.Def_InfHorizonVP_clarkeNormalCone
-- name    : InfHorizonVP_clarkeNormalCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:52.830524+00:00
-- url     : https://prove2.me/theorems/c5de720c-404e-4735-b4c4-b0eaa5f7eb30
-- title:
--   Clarke normal cone $N_C(\bar x)$
-- statement:
--   The **Clarke normal cone** to $C$ at $\bar x$ is the polar of the Clarke tangent cone:
--   $$
--   N_C(\bar x)=\{x^*\in E^*\mid\langle x^*,v\rangle\le0\ \ \forall v\in T_C(\bar x)\}.
--   $$
--   It appears in the Euler–Lagrange inclusions of Theorems 3.2 and 4.1 as $N_{\Gamma(t,x_0(t))}(\dot x_0(t))$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.5

import Mathlib
import Definitions.Def_InfHorizonVP_clarkeTangentCone
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Clarke normal cone `N_C(x̄)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.5: "The polar of T_C(x̄) is called the Clarke
normal cone to C at x̄, which is given by N_C(x̄) = {x* ∈ E* | ⟨x*, v⟩ ≤ 0 ∀v ∈ T_C(x̄)}."

**Formalization Note.** `E* = E →L[ℝ] ℝ`. -/
def clarkeNormalCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (x : E) : Set (E →L[ℝ] ℝ) :=
  {z | ∀ v ∈ clarkeTangentCone C x, z v ≤ 0}

end InfHorizonVP


