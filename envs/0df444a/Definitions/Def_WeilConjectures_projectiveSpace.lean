-- Prove2me | Definitions.Def_WeilConjectures_projectiveSpace
-- name    : WeilConjectures_projectiveSpace
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T14:56:00.388888+00:00
-- url     : https://prove2.me/theorems/af025733-c5dd-4f00-9479-16f8c72a8747
-- title:
--   Projective space $\mathbb P^N_k$ and projective $k$-schemes
-- statement:
--   For a field $k$ and $N\ge0$, **projective $N$-space** is $\mathbb P^N_k=\operatorname{Proj}k[x_0,\dots,x_N]$, the polynomial ring being graded by total degree. Its **structure morphism** $\mathbb P^N_k\to\operatorname{Spec}k$ is the canonical map $\operatorname{Proj}A\to\operatorname{Spec}A_0$ followed by the map induced by $k\to A_0$.
--
--   A scheme $X$ with a morphism $f:X\to\operatorname{Spec}k$ is **projective over $k$** if for some $N$ there is a closed immersion $i:X\to\mathbb P^N_k$ with $f=\pi\circ i$, where $\pi$ is the structure morphism.
--
--   This supplies the word "projective" in "non-singular projective variety" in the statement of the Weil conjectures, and the projective line and projective spaces of the source's examples.
--
--   **Formalization Note** Mathlib currently has `Proj` of a graded ring but no projective space or projective morphisms; this file defines `projectiveSpace k N`, `projectiveSpace.toSpec k N` and `IsProjectiveOver k f`, using `MvPolynomial.gradedAlgebra` as a local instance. Schemes live in universe 0.
-- source:
--   Wikipedia, "Weil conjectures", https://en.wikipedia.org/wiki/Weil_conjectures (PDF snapshot supplied by the proposer, 14 pp.), section "Statement of the Weil conjectures" ("projective algebraic variety") and section "Examples" (projective line, projective space)

import Mathlib

/-!
Projective space `ℙ^N_k` over a field `k`, its structure morphism to `Spec k`,
and the notion of a `k`-scheme being projective (admitting a closed immersion into some
`ℙ^N_k` over `k`).
-/

namespace WeilConjectures

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type) [Field k]

/-- Projective `N`-space over `k`: `ℙ^N_k = Proj k[x₀, …, x_N]`, where the polynomial ring
is graded by total degree. -/
noncomputable abbrev projectiveSpace (N : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)

/-- The structure morphism `ℙ^N_k ⟶ Spec k`: the canonical map
`Proj A ⟶ Spec A₀` followed by `Spec A₀ ⟶ Spec k` induced by `k → A₀`. -/
noncomputable def projectiveSpace.toSpec (N : ℕ) : projectiveSpace k N ⟶ Spec (.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))

/-- A `k`-scheme `f : X ⟶ Spec k` is projective if there is a closed immersion
`X ⟶ ℙ^N_k` over `Spec k` for some `N`. -/
def IsProjectiveOver {X : Scheme} (f : X ⟶ Spec (.of k)) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ projectiveSpace k N),
    IsClosedImmersion i ∧ i ≫ projectiveSpace.toSpec k N = f

end WeilConjectures


