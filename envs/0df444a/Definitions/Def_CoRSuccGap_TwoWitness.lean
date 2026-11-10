-- Prove2me | Definitions.Def_CoRSuccGap_TwoWitness
-- name    : CoRSuccGap_TwoWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:47:38.117008+00:00
-- url     : https://prove2.me/theorems/1933334c-f01b-4d1e-ad39-4936e982f49b
-- title:
--   Two-witness colourings: two distinct outside witnesses for every pair of vertices and every pair of colours
-- statement:
--   Let $V$ be a set of vertices and $\Lambda$ a palette of colours. A **colouring** $\chi$ assigns a colour $\chi(u,v)=\chi(\{u,v\})\in\Lambda$ to every unordered pair of distinct vertices. The colouring has the **two-witness property** if for all distinct $u,v\in V$ and all colours $\mu,\nu\in\Lambda$ there are two distinct vertices $z_1\neq z_2$, both in $V\setminus\{u,v\}$, with
--
--   $$
--   \chi(u,z_j)=\mu\quad\text{and}\quad\chi(z_j,v)=\nu\qquad(j=1,2).
--   $$
--
--   Lemma 3.1 shows that such colourings exist on every sufficiently large vertex set; the lower-bound argument of Section 3 fixes one, together with a hub vertex.
--
--   **Formalization Note** A colouring is `χ : Sym2 V → Λ`; its values on the diagonal pairs `s(u, u)` play no role in this or any other definition of the mission.
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), §3.1, p.17 (PDF 19) (colorings); Lemma 3.1, p.18 (PDF 20) (the property)

import Mathlib

set_option autoImplicit false

namespace CoRSuccGap

/-!
# Two-witness colourings

Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), §3.1, p.17 (PDF 19): "Fix a palette Λ of N ≥ 2 colors and a vertex set V of size n. A
coloring χ : (V choose 2) → Λ assigns a color to every unordered pair of distinct vertices. We write
χ(u, v) for χ({u, v})." Lemma 3.1, p.18 (PDF 20): "… for all distinct u, v ∈ V and all μ, ν ∈ Λ,
at least two distinct vertices z ∈ V \ {u, v} satisfy χ(u, z) = μ and χ(z, v) = ν."

**Formalization Note.**
* A colouring is `χ : Sym2 V → Λ`. Its values on the diagonal `s(u, u)` are irrelevant: every
  definition of the mission only reads χ on pairs of distinct vertices.
* `TwoWitness χ` is the property of Lemma 3.1 (two distinct witnesses outside the endpoints).
-/

/-- The two-witness property (Lemma 3.1, p.18): for all distinct `u, v` and all colours `μ, ν`
there are two distinct vertices `z₁ ≠ z₂`, both outside `{u, v}`, with `χ(u, zⱼ) = μ` and
`χ(zⱼ, v) = ν`. -/
def TwoWitness {V : Type*} {Λ : Type*} (χ : Sym2 V → Λ) : Prop :=
  ∀ u v : V, u ≠ v → ∀ μ ν : Λ, ∃ z₁ z₂ : V, z₁ ≠ z₂ ∧
    (z₁ ≠ u ∧ z₁ ≠ v ∧ χ s(u, z₁) = μ ∧ χ s(z₁, v) = ν) ∧
    (z₂ ≠ u ∧ z₂ ≠ v ∧ χ s(u, z₂) = μ ∧ χ s(z₂, v) = ν)

end CoRSuccGap


