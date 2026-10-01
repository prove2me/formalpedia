-- Prove2me | Definitions.Def_ChapterMackeyImprimitivity
-- name    : ChapterMackeyImprimitivity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:22:33.064264+00:00
-- url     : https://prove2.me/theorems/95b0b076-b8ef-4f27-8713-8b0a6200944e
-- title:
--   Chapter MackeyImprimitivity
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMackeyImprimitivity.lean`): generated def bundle for ChapterMackeyImprimitivity. See BookProof/ChapterMackeyImprimitivity.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyImprimitivity.lean

import Mathlib


/-!
# Mackey's imprimitivity theorem (book.tex, Note 33 and Note 84)

`book.tex` states the imprimitivity theorem (Note 33, quoted from Varadarajan's
*Geometry of Quantum Theory*, Thm 6.12) as an external input, and uses it twice: for
Lemma 34 (Schur's lemma for systems of imprimitivity — proved independently in
`BookProof.ChapterSchurRepresentation`) and in Note 84, the one-to-one correspondence
between systems of imprimitivity based on `ℝ³` and representations of the little group.

This file **proves the theorem** in the transitive, discrete (finite) case: a system of
imprimitivity `(U, p)` of a group `G` over a finite transitive `G`-space `X ≅ G/H` is
unitarily equivalent to the system *induced* from the representation of the stabilizer
`H = Stab(x₀)` on the fibre `𝒦 = ran p x₀`.  This is the whole mechanism of Mackey's
theorem; the general case replaces the finite sum over `X` by an integral against a
quasi-invariant measure on `G/H`.

## The set-up

A **system of imprimitivity** (`ImprimitivitySystem`; the book's Definition 32 for a
discrete base) consists of a unitary representation `U : G →* (E ≃ₗᵢ[ℂ] E)` and a
projection-valued measure on the discrete space `X`, given by its atoms
`p : X → (E →L[ℂ] E)`: self-adjoint idempotents, pairwise orthogonal, summing to the
identity, and covariant, `U g (p x ψ) = p (g • x) (U g ψ)`, which is the book's
`U(g) π(A) U(g)⁻¹ = π(gA)`.

The **induced system** is realized concretely as the space of "fields on `X` with values
in the fibre" (`InducedSpace`): the functions `f : X → E` with `p x₀ (f x) = f x`, with
squared norm `∑ x, ‖f x‖²`.  Given a choice of coset representatives `s : X → G`
(`s x • x₀ = x`, which exists exactly because the action is transitive), the induced
representation and the induced projection-valued measure are

  `(inducedRep g f) x = U (cocycle g x) (f (g⁻¹ • x))`,  `cocycle g x = (s x)⁻¹ g (s (g⁻¹ • x))`,
  `(inducedPvm y f) x = if x = y then f x else 0`,

where the cocycle takes its values in the stabilizer `H` (`cocycle_mem_stabilizer`) and
`U` restricted to `H` preserves the fibre (`fibre_stabilizer_invariant`); so the induced
data only depend on the representation `L = U|_H` of `H` on the fibre `𝒦` — this is
Mackey's induced system `(V_L, E_L)`.

## Results

* `pvm_parseval` — Parseval's identity `∑ x, ‖p x ψ‖² = ‖ψ‖²` for the measure;
* `mackeyMap` (`W ψ x = U (s x)⁻¹ (p x ψ)`, equal to `p x₀ (U (s x)⁻¹ ψ)`), which is
  linear (`mackeyMap_add`, `mackeyMap_smul`), takes values in the induced space
  (`mackeyMap_mem_inducedSpace`), is norm-preserving (`mackeyMap_norm_sq`), injective
  (`mackeyMap_injective`) and onto the induced space (`mackeyMap_surjective`);
* `mackeyMap_intertwines_U` — `W (U g ψ) = inducedRep g (W ψ)`;
* `mackeyMap_intertwines_pvm` — `W (p y ψ) = inducedPvm y (W ψ)`;
* `mackey_imprimitivity` — all of it bundled: **every transitive system of imprimitivity
  over a finite base is unitarily equivalent to the system induced by the representation
  of the stabilizer on the fibre.**

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace
open Finset

namespace BookProof.ChapterMackeyImprimitivity

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A **system of imprimitivity** over a discrete base `X` (the book's Definition 32): a
unitary representation `U` together with the atoms `p x` of a projection-valued measure on
`X`, satisfying the covariance relation `U(g) π(A) U(g)⁻¹ = π(gA)`. -/
structure ImprimitivitySystem (G X E : Type*) [Group G] [Fintype X] [MulAction G X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The unitary representation. -/
  U : G →* (E ≃ₗᵢ[ℂ] E)
  /-- The atoms of the projection-valued measure. -/
  p : X → (E →L[ℂ] E)
  /-- Each atom is self-adjoint. -/
  selfAdjoint : ∀ x u v, ⟪p x u, v⟫_ℂ = ⟪u, p x v⟫_ℂ
  /-- Each atom is idempotent. -/
  idem : ∀ x ψ, p x (p x ψ) = p x ψ
  /-- Distinct atoms are orthogonal. -/
  orthogonal : ∀ x y, x ≠ y → ∀ ψ, p x (p y ψ) = 0
  /-- The atoms sum to the identity: `π(X) = 1`. -/
  complete : ∀ ψ, ∑ x, p x ψ = ψ
  /-- Covariance: `U(g) π(A) U(g)⁻¹ = π(gA)`. -/
  covariant : ∀ g x ψ, U g (p x ψ) = p (g • x) (U g ψ)



namespace ImprimitivitySystem

variable (S : ImprimitivitySystem G X E)









end ImprimitivitySystem

/-! ## The induced system -/

variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)

/-- The fibre over the base point: the range of the atom `p x₀`, described by the
idempotent equation `p x₀ v = v`. -/
def InducedSpace : Set (X → E) := {f | ∀ x, S.p x₀ (f x) = f x}

/-- Mackey's cocycle `(s x)⁻¹ g s(g⁻¹ x)`, with values in the stabilizer of `x₀`. -/
def cocycle (g : G) (x : X) : G := (s x)⁻¹ * g * s (g⁻¹ • x)

/-- The induced representation of `G` on fields over `X` with values in the fibre. -/
def inducedRep (g : G) (f : X → E) : X → E := fun x => S.U (cocycle s g x) (f (g⁻¹ • x))

/-- The induced projection-valued measure: multiplication by the indicator of `{y}`. -/
def inducedPvm [DecidableEq X] (y : X) (f : X → E) : X → E := fun x => if x = y then f x else 0

/-- **Mackey's intertwiner** `W ψ x = U (s x)⁻¹ (p x ψ)`. -/
def mackeyMap (ψ : E) : X → E := fun x => S.U (s x)⁻¹ (S.p x ψ)

variable {S x₀ s}





















/-! ### The cocycle and the fibre representation of the stabilizer -/







/-! ### The two intertwining relations -/





/-! ## Mackey's imprimitivity theorem -/



end BookProof.ChapterMackeyImprimitivity


