-- Prove2me | Definitions.Def_ChapterTensorGraphCore
-- name    : ChapterTensorGraphCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:35:05.852654+00:00
-- url     : https://prove2.me/theorems/ff08e5b2-6199-40a0-a675-688e26891ecf
-- title:
--   Chapter TensorGraphCore
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTensorGraphCore.lean`): generated def bundle for ChapterTensorGraphCore. See BookProof/ChapterTensorGraphCore.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTensorGraphCore.lean

import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib


/-!
# Tensor powers: a one-particle core is a core for the sector derivation

Let `A` be a symmetric operator with domain `D₂` in a complex inner product space `H`, and
let `D ≤ D₂` be a **core** for `A` in the graph-norm sense of
`BookProof.GraphCore.IsGraphCore`.  The `n`-particle sector of the second quantization of
`A` carries the *derivation*

`dΓ(A)⁽ⁿ⁾ (x₁ ⊗ ⋯ ⊗ xₙ) = Σⱼ x₁ ⊗ ⋯ ⊗ A xⱼ ⊗ ⋯ ⊗ xₙ`,

defined on the algebraic tensor power `D₂^{⊗n}`.  This module proves the **multilinear core
estimate**: the algebraic tensor power `D^{⊗n}` of the one-particle core is again a core, now
for the sector derivation.  Together with the core transfer principle
(`BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore`) this is what allows the
hypothesis "`A` is self-adjoint on `D`" to be weakened to "`A` is essentially self-adjoint on
`D`" in the second quantization theorem: one never needs `D` to be invariant under the
unitary group, nor a resolvent of `A` on `D`.

## Contents

* `IPSpace` — a bundled complex inner product space, and `IPSpace.pow` its `n`-fold
  algebraic tensor power (`Mathlib` gives the tensor product of two inner product spaces its
  inner product, so the powers are inner product spaces by recursion).
* `inclPow` — the isometric inclusion `D₂^{⊗n} → H^{⊗n}`.
* `derPow` — the sector derivation `dΓ(A)⁽ⁿ⁾` on `D₂^{⊗n}`, defined by the Leibniz recursion
  `dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾`.
* `corePow` — the algebraic tensor power `D^{⊗n}` of the one-particle core.
* `exists_core_approx` — **the multilinear core estimate**: every vector of `D₂^{⊗n}` is
  approximated in the graph norm of `dΓ(A)⁽ⁿ⁾` by vectors of `D^{⊗n}`.
* `sectorDom`, `sectorCore`, `sectorOp` — the same data seen inside `H^{⊗n}`, and
  `isGraphCore_sectorCore`, the core estimate in the form used by the transfer principle.
* `essentiallySelfAdjointOn_sectorCore` — if the sector derivation is essentially
  self-adjoint on `D₂^{⊗n}`, it is essentially self-adjoint on `D^{⊗n}`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorCore

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

/-! ## Tensor powers of an inner product space -/

/-- A bundled complex inner product space.  Bundling is what makes the recursion defining
the tensor powers (and their inner products) possible. -/
structure IPSpace where
  /-- the underlying type -/
  carrier : Type
  [nacg : NormedAddCommGroup carrier]
  [ips : InnerProductSpace ℂ carrier]

attribute [instance] IPSpace.nacg IPSpace.ips

instance : CoeSort IPSpace Type := ⟨IPSpace.carrier⟩

/-- The `n`-fold algebraic tensor power `E^{⊗n}`, with `E^{⊗0} = ℂ`. -/
@[reducible] def IPSpace.pow (E : IPSpace) : ℕ → IPSpace
  | 0 => ⟨ℂ⟩
  | (n + 1) => ⟨E.carrier ⊗[ℂ] (E.pow n).carrier⟩

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)

/-- The domain of the one-particle operator, as an inner product space in its own right. -/
@[reducible] def domSpace : IPSpace := ⟨D₂⟩

/-- The isometric inclusion `D₂^{⊗n} → H^{⊗n}`. -/
def inclPow : ∀ n : ℕ, ((domSpace Hs D₂).pow n) →ₗᵢ[ℂ] (Hs.pow n)
  | 0 => LinearIsometry.id
  | (n + 1) => TensorProduct.mapIsometry D₂.subtypeₗᵢ (inclPow n)



variable (A : D₂ →ₗ[ℂ] Hs.carrier)

/-- The **sector derivation** `dΓ(A)⁽ⁿ⁾` on the algebraic tensor power `D₂^{⊗n}`, defined by
the Leibniz recursion `dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾`.  On elementary tensors it is
`Σⱼ x₁ ⊗ ⋯ ⊗ A xⱼ ⊗ ⋯ ⊗ xₙ`. -/
def derPow : ∀ n : ℕ, ((domSpace Hs D₂).pow n) →ₗ[ℂ] (Hs.pow n)
  | 0 => 0
  | (n + 1) => TensorProduct.map A (inclPow Hs D₂ n).toLinearMap
      + TensorProduct.map D₂.subtype (derPow n)





variable (D : Submodule ℂ Hs.carrier)

/-- The algebraic tensor power `D^{⊗n}` of the one-particle core, as a subspace of
`D₂^{⊗n}`. -/
def corePow : ∀ n : ℕ, Submodule ℂ ((domSpace Hs D₂).pow n)
  | 0 => ⊤
  | (n + 1) =>
      Submodule.span ℂ
        {t | ∃ a : D₂, (a : Hs.carrier) ∈ D ∧ ∃ b ∈ corePow n, a ⊗ₜ[ℂ] b = t}



/-! ## The multilinear core estimate -/

/-- The graph map `x ↦ (x, dΓ(A)⁽ⁿ⁾ x)` of the sector derivation, with values in
`H^{⊗n} × H^{⊗n}`.  Density in the graph norm is density of the range of this map. -/
def graphPow (n : ℕ) : ((domSpace Hs D₂).pow n) →ₗ[ℂ] (Hs.pow n) × (Hs.pow n) :=
  (inclPow Hs D₂ n).toLinearMap.prod (derPow Hs D₂ A n)











/-! ## The sector inside `H^{⊗n}` -/

/-- The image of `D₂^{⊗n}` inside `H^{⊗n}`: the domain of the sector derivation. -/
def sectorDom (n : ℕ) : Submodule ℂ (Hs.pow n) :=
  LinearMap.range (inclPow Hs D₂ n).toLinearMap

/-- The image of the core tensor power `D^{⊗n}` inside `H^{⊗n}`. -/
def sectorCore (n : ℕ) : Submodule ℂ (Hs.pow n) :=
  Submodule.map (inclPow Hs D₂ n).toLinearMap (corePow Hs D₂ D n)



/-- The sector derivation `dΓ(A)⁽ⁿ⁾` as an operator on the subspace `sectorDom` of
`H^{⊗n}`. -/
def sectorOp (n : ℕ) : sectorDom Hs D₂ n →ₗ[ℂ] (Hs.pow n) :=
  derPow Hs D₂ A n ∘ₗ
    (LinearEquiv.ofInjective (inclPow Hs D₂ n).toLinearMap
      (inclPow Hs D₂ n).injective).symm.toLinearMap





/-! ## Symmetry of the sector derivation -/









/-! ## Non-vacuity -/





end

end BookProof.TensorCore


