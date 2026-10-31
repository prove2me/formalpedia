-- Prove2me | Definitions.Def_InfHorizonVP_HypH5Prime
-- name    : InfHorizonVP_HypH5Prime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:24.724157+00:00
-- url     : https://prove2.me/theorems/da7b2bc4-822a-43f1-b4b6-5f28fd262f65
-- title:
--   Hypothesis (H′5): lower semicontinuity of $\Gamma(\cdot,x)$
-- statement:
--   **(H′5)** For every $x\in E$ the multifunction $\Gamma(\cdot,x)$ is lower semicontinuous on $\mathbb R_+$: for every $t\ge0$ and every open $O$ with $\Gamma(t,x)\cap O\neq\emptyset$, also $\Gamma(s,x)\cap O\neq\emptyset$ for all $s\ge0$ close enough to $t$.
--
--   It replaces (H5) in Theorems 3.2 and 4.1 and implies it.
--
--   **Formalization Note** The paper does not restate the definition of lower semicontinuity; the standard one is used.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.2, p.10, (H′5)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H′5): `Γ(·, x)` is lower semicontinuous.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.2, p.10: "We need another continuity assumption on Γ
that replaces (H5): (H′5) Γ(·, x) is lower semicontinuous for every x ∈ E."

**Formalization Note.** The paper does not restate the definition; the standard one is used: for
every `t ∈ ℝ₊` and every open `O` meeting `Γ(t, x)`, the set `Γ(s, x)` meets `O` for every
`s ∈ ℝ₊` near `t` (equivalently, `{s ∈ ℝ₊ | Γ(s, x) ∩ O ≠ ∅}` is relatively open in `ℝ₊`). -/
def HypH5Prime {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : ℝ → E → Set E) : Prop :=
  ∀ x : E, ∀ O : Set E, IsOpen O → ∀ t, 0 ≤ t → (Γ t x ∩ O).Nonempty →
    ∀ᶠ s in 𝓝[Ici 0] t, (Γ s x ∩ O).Nonempty

end InfHorizonVP


