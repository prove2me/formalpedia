-- Prove2me | Definitions.Def_QLLL_Quantum_KQSAT_QubitTensor
-- name    : QLLL_Quantum_KQSAT_QubitTensor
-- status  : Definition
-- author  : @sattath
-- created : 2026-10-06T17:43:34.91598+00:00
-- url     : https://prove2.me/theorems/ffe977d6-6167-4b45-8f70-5ca0870bfb55
-- title:
--   Tensor products of finite function spaces as function spaces on product sets
-- statement:
--   Linear identifications between tensor products of function spaces and function spaces (namespace `QLLL.QubitTensor`).
--
--   1. **Uncurrying** (`funUncurryEquiv A B`). The linear isomorphism between functions $B \to (A \to \mathbb{C})$ and functions $A \times B \to \mathbb{C}$, $F \mapsto ((a, b) \mapsto F(b)(a))$.
--   2. **Tensor product of function spaces** (`funTensorEquiv A B`). For a finite set $B$, the linear isomorphism $\mathbb{C}^A \otimes \mathbb{C}^B \cong \mathbb{C}^{A \times B}$ sending $f \otimes g$ to $(a, b) \mapsto f(a)\,g(b)$, assembled from Mathlib's `TensorProduct.piScalarRight`.
--
--   These identifications connect the function model of qubits with tensor products of subspaces. Mathlib does not state the second one directly.
-- source:
--   Not in the paper; formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Mathlib

/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The qubit model, certified against Mathlib's tensor products

`QuantumLocalLemma.Quantum.KQSAT.Basic` models the state space of `n` qubits as
`(Fin n → Fin 2) → ℂ`, functions on bit strings, with locality expressed as
a bipartition of the index type. That is an encoding, not a definition imported
from a library, so on its own it asks the reader to accept that it is the
`n`-qubit space.

This file removes that gap in two steps.

* `qubitsEquiv` : the encoding really is the `n`-fold tensor product,
  `(⨂[ℂ] i : Fin n, (Fin 2 → ℂ)) ≃ₗ[ℂ] ((Fin n → Fin 2) → ℂ)`, with
  `qubitsEquiv_tprod` and `qubitsEquiv_symm_single` pinning down the
  identification on elementary tensors and on computational basis states.

* `funTensorEquiv` and `map_funTensorEquiv_tensorProd` : the two-factor splitting used
  throughout `QuantumLocalLemma.Quantum.KQSAT.Basic` really is the tensor product, and the subspace
  `liftL Y ⊓ liftR W` used there really is `Y ⊗ W`. So the product rule may be
  routed through the standard statement about tensor products of submodules
  (`TensorProduct.range_mapIncl_inf_range_mapIncl`) rather than through the Kronecker computation
  in `QuantumLocalLemma.Quantum.KQSAT.Basic`.

Mathlib has no identification of a `PiTensorProduct` of function spaces with
functions on the product index; the nearest is
`PiTensorProduct.ofFinsuppEquiv'`, stated for `Finsupp`.
-/

open TensorProduct
open QLLL.QSAT

namespace QLLL.QubitTensor

/-! ## The `n`-qubit space is the `n`-fold tensor product -/

/-! ## The two-factor splitting is the tensor product -/

/-- Uncurrying with a swap, as a linear equivalence. The argument order is the
one produced by `TensorProduct.piScalarRight`. -/
def funUncurryEquiv (A B : Type*) : (B → A → ℂ) ≃ₗ[ℂ] ((A × B) → ℂ) where
  toFun F := fun p => F p.2 p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := fun b a => f (a, b)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tensor product of two finite function spaces is the function space on
the product index. Mathlib does not state this; it is assembled from
`TensorProduct.piScalarRight`. -/
noncomputable def funTensorEquiv (A B : Type*)
    [Fintype B] [DecidableEq B] :
    ((A → ℂ) ⊗[ℂ] (B → ℂ)) ≃ₗ[ℂ] ((A × B) → ℂ) :=
  (TensorProduct.piScalarRight ℂ ℂ (A → ℂ) B) ≪≫ₗ funUncurryEquiv A B

section Transport

variable {A B : Type*} [Fintype B] [DecidableEq B]

end Transport

/-! ## The product rule, via the standard statement

With the identification in place, the dimension count behind the paper's
Lemma 11 follows from `TensorProduct.range_mapIncl_inf_range_mapIncl` and
`Module.finrank_tensorProduct`, with no Kronecker products and no trace
computation. `QLLL.QSAT.finrank_inf_liftL_liftR` proves the same thing the other
way; having both is a cross-check on the model.
-/

/-! ## The identification is isometric

Mathlib does put the Hilbert inner product on the *algebraic* tensor product
(`TensorProduct.instInnerProductSpace`), and `OrthonormalBasis.tensorProduct`
builds the product orthonormal basis, so for two factors the identification is
isometric essentially for free. That matters because it is what carries
"orthogonal projector" and "orthogonal complement" across the identification,
which a purely linear isomorphism would not.

`euclideanTensorIsometry_eq_funTensorEquiv` shows the isometry is the *same
underlying map* as `funTensorEquiv` above, read through `WithLp.linearEquiv`. So
the configuration model is not merely linearly isomorphic to the tensor product;
it is the isometric identification, up to the `WithLp` type synonym.

Two limits are worth recording. Mathlib puts no inner product on
`PiTensorProduct`, and `⨂[𝕜] i, E i` already carries a `SeminormedAddCommGroup`
from `PiTensorProduct.projectiveSeminorm`, the projective tensor norm rather than
the Hilbert one, so the `n`-fold Hilbert structure cannot be added as an instance
on that type at all. What is stated here instead is
`inner_qubitsEuclidEquiv_tprod`, the defining property
`⟪⊗ᵢ fᵢ, ⊗ᵢ gᵢ⟫ = ∏ᵢ ⟪fᵢ, gᵢ⟫`, which needs no new instance.

Also, `WithLp` is a structure, so `EuclideanSpace ℂ A` is not definitionally
`A → ℂ`, and there is deliberately no isometry between them for `p = 2` (the bare
function type carries the sup norm). Making the state space of
`QuantumLocalLemma.Quantum.KQSAT.Basic`
carry an inner product would therefore be a change of type, not an addition of
lemmas. It is not done here because nothing in the local lemma needs it: the
physical projectors of `QuantumLocalLemma.Quantum.KQSAT.Projector` already obtain self-adjointness
by
transporting to `EuclideanSpace` locally.
-/

section Isometric

open scoped ComplexOrder

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ### The `n`-fold case, without new instances -/

end Isometric

end QLLL.QubitTensor


