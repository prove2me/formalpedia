-- Prove2me | Definitions.Def_GPHigherGauge_Flatness_IsSmoothSquareLabels
-- name    : GPHigherGauge_Flatness_IsSmoothSquareLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:55:42.347924+00:00
-- url     : https://prove2.me/theorems/4c6292c0-fcc3-41ec-9361-ea27731adfe3
-- title:
--   Edge and square labels that vary smoothly near $(x_0,0)$ with the infinitesimal form (3.16)
-- statement:
--   Let $G,H$ be real Lie groups, $g_\mu(x,a)\in G$ edge labels and $h_{\mu\nu}(x,a)\in H$ square labels on $\mathbb R^n$, and $x_0\in\mathbb R^n$. The labels **vary smoothly with the infinitesimal form (3.16) at $x_0$** when:
--   1. for every $\mu$, the map $(x,a)\mapsto g_\mu(x,a)$ is $C^\infty$ at every point of a neighbourhood of $(x_0,0)$ in $\mathbb R^n\times\mathbb R$;
--   2. for every $\mu\neq\nu$, the map $(x,a)\mapsto h_{\mu\nu}(x,a)$ is $C^\infty$ at every point of a neighbourhood of $(x_0,0)$;
--   3. for every $\mu$, $g_\mu(x,0)=1$ for all $x$ near $x_0$;
--   4. for every $\mu\neq\nu$, $h_{\mu\nu}(x_0,0)=1$;
--   5. for every $\mu\neq\nu$, $\frac{d}{da}\big|_{a=0}h_{\mu\nu}(x_0,a)=0$.
--
--   These are the paper's standing assumptions that "all labels depend smoothly on the curves and surfaces" and that $g_\mu\sim e^{aA_\mu}$, $h_{\mu\nu}\sim e^{a^2B_{\mu\nu}}$.
--
--   **Formalization Note** Squares need two distinct directions, so the conditions on $h$ are for $\mu\neq\nu$ only. The side $a$ ranges over a neighbourhood of $0$, negative values included. Smoothness is `ContMDiffAt` for the product model on $\mathbb R^n\times\mathbb R$.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, first paragraph and Eq. (3.16), p. 15

import Mathlib

open scoped Manifold ContDiff Topology
open Filter

namespace GPHigherGauge.Flatness

/-- Edge labels `g` and square labels `h` that depend smoothly on the edges and squares near the
base point `x₀` and have the infinitesimal form (3.16) there.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, p. 15:
"We assume that all labels depend smoothly on the curves and surfaces. [...] g_µ(0) = e^{∫_γ A} ∼
e^{aA_µ}, h_µν(0) = e^{∫_S B} ∼ e^{a²B_µν}. (3.16)"

`g μ x a` labels the edge from `x` to `x + a • e_μ`; `h μ ν x a` labels the square at `x`
spanned by `a • e_μ` and `a • e_ν` (Figure 1(c)). The clauses:
1. (smoothness, Reading 1) for every `μ`, `(x, a) ↦ g μ x a` is `C^∞` at every point near
   `(x₀, 0)`;
2. (smoothness, Reading 1) for every `μ ≠ ν`, `(x, a) ↦ h μ ν x a` is `C^∞` at every point near
   `(x₀, 0)`;
3. ((3.16) at `a = 0`, Reading 2) `g μ x 0 = 1` for every `μ` and all `x` near `x₀` (the edge
   of length `0` has the unit label);
4. ((3.16) at `a = 0`, Reading 2) `h μ ν x₀ 0 = 1` for `μ ≠ ν`;
5. ((3.16), `h` is of order `a²`, Reading 2) the velocity of `a ↦ h μ ν x₀ a` at `a = 0` is `0`
   for `μ ≠ ν`.

**Formalization Note** Squares need two distinct directions, so the clauses on `h` are for
`μ ≠ ν` only; `h μ μ` is unconstrained. The side `a` ranges over a neighbourhood of `0` in `ℝ`,
negative values included. Smoothness is `ContMDiffAt` with the product model on `ℝⁿ × ℝ`. The
data are local: nothing is assumed away from `(x₀, 0)` (Reading 3). -/
def IsSmoothSquareLabels {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] [ChartedSpace F H] [Group H] {n : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → G)
    (h : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ → H) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  (∀ μ : Fin n, ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)),
      ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ => g μ q.1 q.2) p) ∧
  (∀ μ ν : Fin n, μ ≠ ν → ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)),
      ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ => h μ ν q.1 q.2) p) ∧
  (∀ μ : Fin n, ∀ᶠ x in 𝓝 x₀, g μ x 0 = 1) ∧
  (∀ μ ν : Fin n, μ ≠ ν → h μ ν x₀ 0 = 1) ∧
  (∀ μ ν : Fin n, μ ≠ ν → mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun a => h μ ν x₀ a) 0 = 0)

end GPHigherGauge.Flatness


