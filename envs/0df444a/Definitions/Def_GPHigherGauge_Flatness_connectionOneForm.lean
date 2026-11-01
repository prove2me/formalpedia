-- Prove2me | Definitions.Def_GPHigherGauge_Flatness_connectionOneForm
-- name    : GPHigherGauge_Flatness_connectionOneForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:55:40.812551+00:00
-- url     : https://prove2.me/theorems/3a00298e-1363-43d0-9167-de31d9358e84
-- title:
--   The connection 1-form $A_\mu(x)$ of a family of edge labels
-- statement:
--   Let $G$ be a real Lie group with Lie algebra $\mathfrak g=T_1G$, and let $e_\mu$ ($\mu=1,\dots,n$) be the standard unit vectors of $\mathbb R^n$. A family of **edge labels** assigns to each direction $\mu$, base point $x\in\mathbb R^n$ and side $a\in\mathbb R$ the group element $g_\mu(x,a)\in G$ labelling the straight edge from $x$ to $x+a\,e_\mu$.
--
--   The **connection 1-form** is the velocity of the edge label at $a=0$:
--   $$A_\mu(x)=\frac{d}{da}\Big|_{a=0}g_\mu(x,a)\in\mathfrak g .$$
--
--   This is the field $A$ of the paper's ansatz $g_\mu\sim e^{aA_\mu}$: the edge of length $a$ carries the label $e^{aA_\mu}$ to first order in $a$.
--
--   **Formalization Note** Mathlib has no Lie-group exponential, so the ansatz is read as $g_\mu(x,0)=1$ together with this derivative (taken with `mfderiv`). It lies in $T_1G$ when $g_\mu(x,0)=1$, which is assumed wherever the definition is used. The value is typed in Mathlib's `GroupLieAlgebra`.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eq. (3.16) and Figure 1(c), p. 15

import Mathlib

open scoped Manifold ContDiff

namespace GPHigherGauge.Flatness

/-- The connection 1-form `A_μ(x)` of a family of edge labels.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eq. (3.16), p. 15:
"We write the labels g ∈ G, h ∈ H as exponentiated curve and surface integrals over
approximately constant differential forms, g_µ(0) = e^{∫_γ A} ∼ e^{aA_µ}, [...] Here γ denotes a
curve of length a from x = 0 to x = µ".

The edge labels are `g : Fin n → ℝⁿ → ℝ → G`, with `g μ x a` the label in `G` of the straight
edge from `x` to `x + a • e_μ` (Figure 1(c), p. 15). `A_μ(x)` is the velocity at `a = 0` of the
curve `a ↦ g μ x a`, an element of the Lie algebra `𝔤 = T₁G`.

**Formalization Note** Mathlib has no Lie-group exponential, so "g_μ ∼ e^{aA_μ}" is read as
`g μ x 0 = 1` together with this derivative definition (Reading 2). When `g μ x 0 = 1` the
`mfderiv` is taken in the chart `extChartAt 𝓘(ℝ, E) 1`, i.e. it lies in `T₁G`; the hypothesis
`g μ x 0 = 1` is imposed where the definition is used (`IsSmoothSquareLabels`). The value is
typed as `GroupLieAlgebra 𝓘(ℝ, E) G` (definitionally the model space `E`). -/
noncomputable def connectionOneForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] {n : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → G) (μ : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    GroupLieAlgebra 𝓘(ℝ, E) G :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun a => g μ x a) 0 1

end GPHigherGauge.Flatness


