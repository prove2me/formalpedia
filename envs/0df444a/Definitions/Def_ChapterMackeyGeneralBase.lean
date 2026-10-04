-- Prove2me | Definitions.Def_ChapterMackeyGeneralBase
-- name    : ChapterMackeyGeneralBase
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:43:18.013489+00:00
-- url     : https://prove2.me/theorems/24d7a040-baf1-4da3-80bf-0c96d834f93d
-- title:
--   Chapter MackeyGeneralBase
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMackeyGeneralBase.lean`): generated def bundle for ChapterMackeyGeneralBase. See BookProof/ChapterMackeyGeneralBase.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterA4
import Mathlib


/-!
# Mackey's imprimitivity theorem over an arbitrary transitive base

`BookProof.ChapterMackeyImprimitivity` proves Mackey's theorem for a **finite** transitive
base `X` and a *chosen* section `s : X → G`.  This file removes both restrictions: the base
is an arbitrary (possibly infinite) `G`-set, the projection-valued measure is summable in
the unconditional (`HasSum`) sense — which is exactly what a projection-valued measure on a
discrete space gives — and the section is *constructed* from transitivity, so the theorem
takes only the transitivity hypothesis.

## The set-up

`ImprimitivitySystem` is the same structure as in the finite case except that the
completeness relation `∑ x, p x ψ = ψ` is replaced by `HasSum (fun x => p x ψ) ψ`.  The
induced space is the `ℓ²`-space of fibre-valued fields:

  `InducedSpace S x₀ = {f | (∀ x, p x₀ (f x) = f x) ∧ Summable fun x => ‖f x‖²}`.

## Results

(The Hilbert-space facts about unconditional sums of orthogonal families that the proof
needs are in `BookProof.ChapterOrthogonalSums`.)

* `pvm_hasSum_norm_sq` — Parseval for the projection-valued measure, `∑ x ‖p x ψ‖² = ‖ψ‖²`;
* `mackeyMap_*` — Mackey's intertwiner `W ψ x = U (s x)⁻¹ (p x ψ)` is linear, lands in the
  induced space, is isometric in the `ℓ²` sense, injective, and **onto** the induced space
  (here the square-summability of the field is exactly what makes the reconstruction
  `ψ = ∑ x U (s x) (f x)` converge);
* `mackeyMap_intertwines_U`, `mackeyMap_intertwines_pvm` — the two covariance relations;
* **`mackey_imprimitivity_general`** — Mackey's imprimitivity theorem: for *any* transitive
  `G`-space `X`, any system of imprimitivity over `X` is unitarily equivalent, through a
  section built from transitivity, to the system induced by the representation of the
  stabilizer of a base point on the fibre over it.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterMackeyGeneralBase


variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A **system of imprimitivity** over an arbitrary discrete base `X`: a unitary
representation `U` together with the atoms `p x` of a projection-valued measure on `X`
(self-adjoint, idempotent, pairwise orthogonal and unconditionally summing to the
identity), satisfying the covariance relation `U(g) π(A) U(g)⁻¹ = π(gA)`. -/
structure ImprimitivitySystem (G X E : Type*) [Group G] [MulAction G X]
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
  /-- The atoms sum to the identity, unconditionally: `π(X) = 1`. -/
  complete : ∀ ψ, HasSum (fun x => p x ψ) ψ
  /-- Covariance: `U(g) π(A) U(g)⁻¹ = π(gA)`. -/
  covariant : ∀ g x ψ, U g (p x ψ) = p (g • x) (U g ψ)

namespace ImprimitivitySystem

variable (S : ImprimitivitySystem G X E)











end ImprimitivitySystem

/-! ## The induced system -/

variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)

/-- The `ℓ²`-space of fields over `X` with values in the fibre over `x₀`. -/
def InducedSpace : Set (X → E) :=
  {f | (∀ x, S.p x₀ (f x) = f x) ∧ Summable fun x => ‖f x‖ ^ 2}

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





/-! ## Mackey's imprimitivity theorem over an arbitrary transitive base -/



/-! ## The finite theory is a special case

Every system of imprimitivity over a finite base in the sense of
`BookProof.ChapterMackeyImprimitivity` is one in the present sense, so the general theorem
above really extends the finite one (and its hypotheses are consistent). -/

/-- A system of imprimitivity over a finite base, viewed as a system over an arbitrary
base: the finite sum `∑ x, p x ψ = ψ` is an unconditional sum. -/
def ofFintype [Fintype X] (S : ChapterMackeyImprimitivity.ImprimitivitySystem G X E) :
    ImprimitivitySystem G X E where
  U := S.U
  p := S.p
  selfAdjoint := S.selfAdjoint
  idem := S.idem
  orthogonal := S.orthogonal
  complete ψ := by
    have h : ∑ x, S.p x ψ = ψ := S.complete ψ
    simpa [h] using hasSum_fintype (fun x => S.p x ψ)
  covariant := S.covariant

end BookProof.ChapterMackeyGeneralBase


