-- Prove2me | Definitions.Def_InfHorizonVP_hamiltonian
-- name    : InfHorizonVP_hamiltonian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:45.037923+00:00
-- url     : https://prove2.me/theorems/6fc167e0-6c9c-482e-84ab-58cb78431ffb
-- title:
--   The Hamiltonian $H(t,x,x^*)$
-- statement:
--   The **Hamiltonian** $H:\mathbb R_+\times E\times E^*\to\mathbb R\cup\{+\infty\}$ is
--   $$
--   H(t,x,x^*)=\sup_{y\in\Gamma(t,x)}\bigl\{\langle x^*,y\rangle-L(t,x,y)\bigr\}.
--   $$
--   It enters the maximum principle (iv) of Theorem 4.1.
--
--   **Formalization Note** The supremum is taken in `EReal`.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §4.1, p.12

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **The Hamiltonian `H(t, x, x*)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §4.1, p.12: "Define the Hamiltonian
H : R+ × E × E* → R ∪ {+∞} by H(t, x, x*) := sup_{y∈Γ(t,x)} {⟨x*, y⟩ − L(t, x, y)}."

**Formalization Note.** The supremum is taken in `EReal` (it is `+∞` for an unbounded family and
`-∞` for an empty `Γ(t, x)`, which (H4) excludes). -/
noncomputable def hamiltonian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (t : ℝ) (x : E) (p : E →L[ℝ] ℝ) : EReal :=
  ⨆ y ∈ Γ t x, (((p y - L t x y : ℝ)) : EReal)

end InfHorizonVP


