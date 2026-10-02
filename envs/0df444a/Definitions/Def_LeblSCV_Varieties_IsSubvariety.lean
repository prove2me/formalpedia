-- Prove2me | Definitions.Def_LeblSCV_Varieties_IsSubvariety
-- name    : LeblSCV_Varieties_IsSubvariety
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:08.364665+00:00
-- url     : https://prove2.me/theorems/0706f381-8bfc-4958-8fdc-b433936dd168
-- title:
--   Definition 6.5.1 — complex-analytic subvariety of an open set
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and $X \subset U$. Then $X$ is a (**complex-analytic**) **subvariety** of $U$ if near each point $p \in U$ there exist an open neighborhood $W \subset U$ of $p$ and a family $\mathcal{F}$ (possibly infinite) of holomorphic functions on $W$ such that
--   $$W \cap X = \{ z \in W : f(z) = 0 \text{ for all } f \in \mathcal{F} \} = \bigcap_{f \in \mathcal{F}} Z_f .$$
--
--   The condition is imposed at every point of $U$, not only at points of $X$, so a subvariety is closed in $U$. Subvarieties are the basic objects of the chapter: zero sets of holomorphic maps, and their singular sets.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`. "Holomorphic on the open set $W$" is `DifferentiableOn ℂ f W`, equivalent to the book's Definition 1.1.2 on open sets (Proposition 1.1.3 and Theorem 1.2.1). The family $\mathcal{F}$ is a set of functions $\mathbb{C}^n \to \mathbb{C}$ whose values off $W$ are irrelevant. Openness of $U$ and $X \subset U$ are part of the definition.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 182, Definition 6.5.1

import Mathlib

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.5.1: `X` is a (complex-analytic) **subvariety** of the open set `U ⊆ ℂⁿ`:
`X ⊆ U`, and near each point `p ∈ U` (not only each point of `X`) there are an open
neighborhood `W ⊆ U` of `p` and a family `𝓕` (possibly infinite) of functions holomorphic on
`W` with `W ∩ X = {z ∈ W : f(z) = 0 for all f ∈ 𝓕}`.
Holomorphic on the open set `W` is `DifferentiableOn ℂ` (equivalent to Definition 1.1.2). -/
def IsSubvariety {n : ℕ} (U X : Set (Fin n → ℂ)) : Prop :=
  IsOpen U ∧ X ⊆ U ∧
    ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      ∃ 𝓕 : Set ((Fin n → ℂ) → ℂ), (∀ f ∈ 𝓕, DifferentiableOn ℂ f W) ∧
        W ∩ X = {z | z ∈ W ∧ ∀ f ∈ 𝓕, f z = 0}

end LeblSCV.Varieties


