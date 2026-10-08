-- Prove2me | Definitions.Def_QLLL_Quantum_KQSAT_PiTensor
-- name    : QLLL_Quantum_KQSAT_PiTensor
-- status  : Definition
-- author  : @sattath
-- created : 2026-10-06T17:44:27.895809+00:00
-- url     : https://prove2.me/theorems/ae66bb09-6166-4629-989c-e78321566eb2
-- title:
--   $n$ qubits as Mathlib's tensor power of $\mathbb{C}^2$, and extension of local constraints
-- statement:
--   Definitions for stating the $k$-QSAT corollary on Mathlib's tensor product (namespace `QLLL.PiQSAT`).
--
--   1. **Single qubit** (`Q`). The space $\mathbb{C}^2$, as functions `Fin 2 → ℂ`.
--   2. **Qubits** (`Qubits ι`). The tensor power $\bigotimes_{j \in \iota} \mathbb{C}^2$, Mathlib's `PiTensorProduct`.
--   3. **Computational basis** (`localEquiv ι`). The linear identification of $\bigotimes_{j \in \iota} \mathbb{C}^2$ with functions $\{0,1\}^{\iota} \to \mathbb{C}$ given by the product basis.
--   4. **Splitting** (`split S`). The isomorphism $\mathcal{Q}^{\otimes S} \otimes \mathcal{Q}^{\otimes S^c} \cong \mathcal{Q}^{\otimes n}$, built from Mathlib's `PiTensorProduct.tmulEquiv` and `PiTensorProduct.reindex`.
--   5. **Extension of a subspace** (`extend S Y`). For a subspace $Y$ of $\mathcal{Q}^{\otimes S}$, the subspace $Y \otimes \mathcal{Q}^{\otimes S^c}$ of the $n$-qubit space.
--   6. **Extension of an operator** (`extendOp S P`). For an operator $P$ on $\mathcal{Q}^{\otimes S}$, the operator $P \otimes I$ on the $n$-qubit space.
--
--   These definitions let the $k$-QSAT corollary be stated with Mathlib's own tensor product instead of the function model used elsewhere in the project.
-- source:
--   Not in the paper; Mathlib PiTensorProduct formulation of Corollary 16 of Ambainis–Kempe–Sattath (arXiv:0911.1696), companion formalization, see blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_QubitTensor
import Mathlib

/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# Corollary 16 on Mathlib's tensor product

Elsewhere in the project the `n`-qubit space is the configuration model
`(Fin n → Fin 2) → ℂ`. This file states the `k`-QSAT corollary directly on Mathlib's
tensor power `⨂[ℂ] i : Fin n, (Fin 2 → ℂ)`, so that its hypotheses and conclusion use only
Mathlib's definitions.

A constraint on the qubits in `S` lives on `⨂[ℂ] i : S, (Fin 2 → ℂ)`. It is extended to all
qubits through the splitting `(⨂ S) ⊗ (⨂ Sᶜ) ≃ ⨂ (Fin n)` built from Mathlib's
`PiTensorProduct.tmulEquiv` and `PiTensorProduct.reindex`: a subspace `Y` becomes `Y ⊗ ⊤`,
and an operator `P` becomes `P ⊗ id`. The results are transported from the configuration
model, where `map_extend` identifies extension with `QSAT.lift`.

## Main results

* `QLLL.PiQSAT.inf_extend_ne_bot` : Corollary 16 for subspaces.
* `QLLL.PiQSAT.inf_ker_extendOp_ne_bot` : Corollary 16 for local operators of rank at
  most `r`: the extended operators have a common nonzero vector in their kernels.
-/

open TensorProduct Module
open QLLL QLLL.QSAT QLLL.QubitTensor

namespace QLLL.PiQSAT

/-- The single-qubit space `ℂ²`. -/
abbrev Q := Fin 2 → ℂ

/-- Qubits indexed by `ι`, as Mathlib's tensor power of `ℂ²`. -/
abbrev Qubits (ι : Type*) := ⨂[ℂ] _i : ι, Q

/-- The computational-basis identification of `⨂ ι` with functions on bit strings. -/
noncomputable def localEquiv (ι : Type*) [Fintype ι] :
    Qubits ι ≃ₗ[ℂ] ((ι → Fin 2) → ℂ) :=
  (Basis.piTensorProduct (fun _ : ι => Pi.basisFun ℂ (Fin 2))).equivFun

variable {n : ℕ}

/-- Splitting the qubits into those in `S` and those outside `S`. -/
noncomputable def split (S : Finset (Fin n)) :
    Qubits {i // i ∈ S} ⊗[ℂ] Qubits {i // i ∉ S} ≃ₗ[ℂ] Qubits (Fin n) :=
  (PiTensorProduct.tmulEquiv ℂ Q).trans
    (PiTensorProduct.reindex ℂ (fun _ => Q) (Equiv.sumCompl (· ∈ S)))

/-- A constraint `Y` on the qubits in `S`, extended to all `n` qubits as `Y ⊗ ⊤`. -/
noncomputable def extend (S : Finset (Fin n)) (Y : Submodule ℂ (Qubits {i // i ∈ S})) :
    Submodule ℂ (Qubits (Fin n)) :=
  (LinearMap.range (TensorProduct.mapIncl Y (⊤ : Submodule ℂ (Qubits {i // i ∉ S})))).map
    (split S).toLinearMap

/-- A local operator `P` on the qubits in `S`, extended to all `n` qubits as `P ⊗ id`. -/
noncomputable def extendOp (S : Finset (Fin n)) (P : Module.End ℂ (Qubits {i // i ∈ S})) :
    Module.End ℂ (Qubits (Fin n)) :=
  (split S).conj (P.rTensor (Qubits {i // i ∉ S}))

end QLLL.PiQSAT


