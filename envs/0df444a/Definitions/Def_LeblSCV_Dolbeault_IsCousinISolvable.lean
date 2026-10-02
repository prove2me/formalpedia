-- Prove2me | Definitions.Def_LeblSCV_Dolbeault_IsCousinISolvable
-- name    : LeblSCV_Dolbeault_IsCousinISolvable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:14:12.935986+00:00
-- url     : https://prove2.me/theorems/5ceccf1d-33db-4025-afe8-8ff91c003fd9
-- title:
--   Definition 4.6.1 — Cousin I data, solutions, and solvability
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and $\{U_\iota\}_{\iota\in I}$ an open covering of $U$. Functions $h_{\iota\kappa} \in \mathcal{O}(U_\iota\cap U_\kappa)$, given whenever $U_\iota\cap U_\kappa\ne\emptyset$, with
--   $$h_{\iota\kappa} + h_{\kappa\iota} = 0 \ \text{ in } U_\iota\cap U_\kappa, \qquad h_{\iota\kappa} + h_{\kappa\lambda} + h_{\lambda\iota} = 0 \ \text{ in } U_\iota\cap U_\kappa\cap U_\lambda,$$
--   are, together with the covering, **Cousin I data**. A **solution** of the Cousin I problem is a family $f_\iota \in \mathcal{O}(U_\iota)$ with $h_{\iota\kappa} = f_\iota - f_\kappa$ on $U_\iota\cap U_\kappa$. The Cousin I problem is **solvable on $U$** if every Cousin I data on every open covering of $U$ has a solution. It is the several-variable analogue of the Mittag-Leffler problem.
--
--   **Formalization Note.** An open covering is a family of open sets with union $U$ (`IsOpenCovering`); $h$ is a family `I → I → (Fin n → ℂ) → ℂ` of which only values on the intersections are read; holomorphic on the open set $U_\iota\cap U_\kappa$ is `DifferentiableOn ℂ` (equivalent to the book's Definition 1.1.2 on open sets), which is empty when the intersection is empty. Index types range over `Type`: every covering can be re-indexed by the set of its members, which lives in `Type`. The file defines `IsOpenCovering`, `IsCousinICocycle`, `IsCousinIData`, `IsCousinISolution` and `IsCousinISolvable`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 151, Definition 4.6.1

import Mathlib

namespace LeblSCV.Dolbeault

/-- `{V_ι}_{ι ∈ I}` is an open covering of `U`: every `V_ι` is open and their union is `U`. -/
def IsOpenCovering {n : ℕ} {I : Type} (U : Set (Fin n → ℂ)) (V : I → Set (Fin n → ℂ)) : Prop :=
  (∀ i, IsOpen (V i)) ∧ (⋃ i, V i) = U

/-- The two conditions of Definition 4.6.1 (Lebl, p. 151):
`h_{ικ} + h_{κι} = 0` in `U_ι ∩ U_κ` and `h_{ικ} + h_{κλ} + h_{λι} = 0` in `U_ι ∩ U_κ ∩ U_λ`. -/
def IsCousinICocycle {n : ℕ} {I : Type} (V : I → Set (Fin n → ℂ))
    (h : I → I → (Fin n → ℂ) → ℂ) : Prop :=
  (∀ i j, ∀ z ∈ V i ∩ V j, h i j z + h j i z = 0) ∧
    ∀ i j k, ∀ z ∈ V i ∩ V j ∩ V k, h i j z + h j k z + h k i z = 0

/-- Definition 4.6.1 (Cousin I data, Lebl, p. 151): an open covering `{U_ι}_{ι ∈ I}` of the open set
`U ⊆ ℂⁿ` and functions `h_{ικ} ∈ 𝒪(U_ι ∩ U_κ)` (holomorphic = `DifferentiableOn ℂ` on the open set
`U_ι ∩ U_κ`; the condition is empty when the intersection is empty) satisfying the two cocycle
conditions. -/
def IsCousinIData {n : ℕ} {I : Type} (U : Set (Fin n → ℂ)) (V : I → Set (Fin n → ℂ))
    (h : I → I → (Fin n → ℂ) → ℂ) : Prop :=
  IsOpenCovering U V ∧ (∀ i j, DifferentiableOn ℂ (h i j) (V i ∩ V j)) ∧ IsCousinICocycle V h

/-- Definition 4.6.1 (Lebl, p. 151): a solution of the Cousin I problem is a family of holomorphic
functions `f_ι ∈ 𝒪(U_ι)` with `h_{ικ} = f_ι - f_κ` on `U_ι ∩ U_κ`. -/
def IsCousinISolution {n : ℕ} {I : Type} (V : I → Set (Fin n → ℂ))
    (h : I → I → (Fin n → ℂ) → ℂ) (f : I → (Fin n → ℂ) → ℂ) : Prop :=
  (∀ i, DifferentiableOn ℂ (f i) (V i)) ∧ ∀ i j, ∀ z ∈ V i ∩ V j, h i j z = f i z - f j z

/-- The Cousin I problem is solvable on `U` (Lebl, pp. 152–154): every Cousin I data on every open
covering of `U` has a solution. Index sets are taken in `Type`; this loses nothing, since any open
covering can be re-indexed by the set of its members, a subset of `Set (Fin n → ℂ)`. -/
def IsCousinISolvable {n : ℕ} (U : Set (Fin n → ℂ)) : Prop :=
  ∀ (I : Type) (V : I → Set (Fin n → ℂ)) (h : I → I → (Fin n → ℂ) → ℂ),
    IsCousinIData U V h → ∃ f : I → (Fin n → ℂ) → ℂ, IsCousinISolution V h f

end LeblSCV.Dolbeault


