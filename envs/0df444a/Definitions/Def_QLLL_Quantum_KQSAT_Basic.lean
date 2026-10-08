-- Prove2me | Definitions.Def_QLLL_Quantum_KQSAT_Basic
-- name    : QLLL_Quantum_KQSAT_Basic
-- status  : Definition
-- author  : @sattath
-- created : 2026-10-06T17:42:02.502632+00:00
-- url     : https://prove2.me/theorems/d3b5e302-c9cb-439f-ac70-7d07f1bf53b9
-- title:
--   The $n$-qubit space as functions on bit strings, slices, and subspaces supported on a set of qubits
-- statement:
--   Definitions for $k$-QSAT in the configuration model (namespace `QLLL.QSAT`).
--
--   1. **Configurations and states** (`Cfg`, `H`, `CfgIn`, `CfgOut`, `HIn`). Configurations of $n$ qubits are bit strings $\{0,1\}^n$, and the state space is $\mathcal{H}_n = \mathbb{C}^{\{0,1\}^n}$. For a set $S$ of qubits, `CfgIn S` and `CfgOut S` are the configurations of the qubits in $S$ and outside $S$, and `HIn S` $= \mathbb{C}^{\{0,1\}^S}$ is the local state space.
--   2. **Splitting and slices** (`cfgEquiv`, `splitEquiv`, `sliceMap`). A configuration splits into its $S$ part and its $S^c$ part; fixing the configuration $b$ outside $S$ turns a state into a function of the configuration inside $S$, its $S$-slice at $b$.
--   3. **Lifted subspaces** (`lift`). For a subspace $Y$ of the local space on $S$, `lift S Y` is the space of states all of whose $S$-slices lie in $Y$; in tensor language, $Y \otimes \mathbb{C}^{\{0,1\}^{S^c}}$.
--   4. **Support** (`IsSupportedOn`). A subspace of $\mathcal{H}_n$ is supported on $S$ if it equals `lift S Y` for some local subspace $Y$, that is, it is cut out by a constraint on the qubits $S$.
--   5. **Two-factor versions** (`colSlice`, `rowSlice`, `liftL`, `liftR`). For finite sets $A, B$ and functions on $A \times B$: column and row slices, and the functions all of whose column (resp. row) slices lie in a given subspace, i.e. $Y \otimes \mathbb{C}^B$ and $\mathbb{C}^A \otimes W$.
--   6. **Auxiliary identifications** (`CfgMid`, `combIn`, `combOut`, `relSlice`, `inComplEquivOut`, `outComplEquivIn`) used to compare slices at nested sets of qubits.
--
--   **Formalization Note** Qubits are modelled as functions on bit strings rather than by Mathlib's `PiTensorProduct`; the identification of the two models is proved in the source project (`QuantumLocalLemma/Quantum/KQSAT/QubitTensor.lean`) and enters the platform inside the proof of `QLLL.PiQSAT.inf_extend_ne_bot`, the statement of the corollary on Mathlib's tensor product.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Definition 10 and Lemma 11 (k-local constraints and their satisfying spaces)

import Definitions.Def_QLLL_LocalLemma_Basic
import Mathlib

/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# k-QSAT and the locality structure

Towards Corollary 16 of arXiv:0911.1696: a `k`-QSAT instance of projectors of
rank at most `r` in which every qubit appears in at most `2 ^ k / (e * r * k)`
projectors is satisfiable.

## Design

The paper works in `⨂ i, H i`. We avoid `PiTensorProduct` entirely by using the
configuration model: the state space of `n` qubits is the space of functions
from bit strings to `ℂ`,
``
H n = (Fin n → Fin 2) → ℂ
``
which is *the same* finite dimensional space, but with locality expressed as an
explicit bipartition of the index type rather than as a tensor factorisation.
Every dimension is then a cardinality.

A constraint supported on a set `S` of qubits is a subspace of the form
`lift S Y`: those `f` all of whose `S`-slices lie in `Y`. This is the
configuration-model description of `Y ⊗ (everything else)`.

## Main results

* `IsSupportedOn.mono` : support is monotone in the set of qubits.
* `finrank_inf_liftL_liftR` : the product rule `dim (U ⊗ W) = dim U * dim W`, in
  the configuration model.
* `relDim_inf_of_isSupportedOn_compl` : a subspace cut out on `S` and one cut out
  on `Sᶜ` are R-independent. This is the crux of the paper's Lemma 11.
* `mutuallyIndepOn_of_isSupportedOn` : Lemma 11, mutual R-independence.
* `inf_ne_bot_of_degree_le`, `inf_lift_ne_bot` : Corollary 16.
-/

namespace QLLL.QSAT

open Finset Module

variable {n : ℕ}

/-- Configurations of `n` qubits, i.e. bit strings. -/
abbrev Cfg (n : ℕ) := Fin n → Fin 2

/-- The state space of `n` qubits, in the configuration model. -/
abbrev H (n : ℕ) := Cfg n → ℂ

/-- Configurations of the qubits in `S`. -/
abbrev CfgIn (S : Finset (Fin n)) := {i // i ∈ S} → Fin 2

/-- Configurations of the qubits outside `S`. -/
abbrev CfgOut (S : Finset (Fin n)) := {i // i ∉ S} → Fin 2

/-- The state space of the qubits in `S`. -/
abbrev HIn (S : Finset (Fin n)) := CfgIn S → ℂ

/-- Splitting a configuration into its `S` part and its `Sᶜ` part. -/
def cfgEquiv (S : Finset (Fin n)) : Cfg n ≃ CfgIn S × CfgOut S :=
  Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Fin 2

/-- Fixing the configuration `b` outside `S` and reading off the resulting
function of the configuration inside `S`. -/
def sliceMap (S : Finset (Fin n)) (b : CfgOut S) : H n →ₗ[ℂ] HIn S :=
  LinearMap.funLeft ℂ ℂ fun a => (cfgEquiv S).symm (a, b)

/-- The subspace of `H n` cut out on the qubits `S` by a subspace `Y` of the
local state space: all slices must lie in `Y`. In tensor language this is
`Y ⊗ (everything outside S)`. -/
def lift (S : Finset (Fin n)) (Y : Submodule ℂ (HIn S)) : Submodule ℂ (H n) :=
  ⨅ b : CfgOut S, Submodule.comap (sliceMap S b) Y

/-- A subspace is supported on `S` when it is cut out by a constraint on `S`. -/
def IsSupportedOn (S : Finset (Fin n)) (P : Submodule ℂ (H n)) : Prop :=
  ∃ Y, P = lift S Y

/-! ### Support is monotone

Enlarging the set of qubits. If `S ⊆ T`, a `T`-configuration splits into its
`S`-part and its `T \ S`-part, and a configuration outside `S` splits into its
`T \ S`-part and its part outside `T`. Slicing at `S` therefore factors as
slicing at `T` followed by a relative slice, which is all that is needed. -/

/-- Configurations of the qubits in `T` but not in `S`. -/
abbrev CfgMid (S T : Finset (Fin n)) := {i // i ∈ T ∧ i ∉ S} → Fin 2

/-- Glue an `S`-configuration and a `T \ S`-configuration into a
`T`-configuration. -/
def combIn {S T : Finset (Fin n)} (a : CfgIn S) (d : CfgMid S T) : CfgIn T :=
  fun i => if h : i.1 ∈ S then a ⟨i.1, h⟩ else d ⟨i.1, i.2, h⟩

/-- Glue a `T \ S`-configuration and a configuration outside `T` into a
configuration outside `S`. -/
def combOut {S T : Finset (Fin n)} (d : CfgMid S T) (c : CfgOut T) : CfgOut S :=
  fun i => if h : i.1 ∈ T then d ⟨i.1, h, i.2⟩ else c ⟨i.1, h⟩

/-- Slicing at `S` relative to `T`: fix a configuration on `T \ S` and read off
the `S`-part. -/
def relSlice {S T : Finset (Fin n)} (d : CfgMid S T) : HIn T →ₗ[ℂ] HIn S :=
  LinearMap.funLeft ℂ ℂ fun a => combIn a d

/-! ## The crux, in Kronecker form

Locality in the configuration model is a Kronecker product: reindexing
`Cfg n ≃ CfgIn S × CfgOut S` turns an operator supported on `S` into a matrix of
the form `p ⊗ₖ 1`, and one supported on `Sᶜ` into `1 ⊗ₖ q`. The dimension count
behind the paper's Lemma 11 then reduces to Kronecker algebra, all of which is
already in Mathlib: `Matrix.mul_kronecker_mul`, `Matrix.one_kronecker`,
`Matrix.trace_kronecker`.

This formulation supersedes an earlier one in terms of `Submodule.map₂`. It is
shorter because it needs exactly one fact Mathlib lacks, recorded below, rather
than a theory of product subspaces.

The same modelling convention (configurations, ground spaces as `Submodule`s,
local terms as orthogonal projectors via `Submodule.starProjection`) is used by
TNLean for parent Hamiltonians of matrix product states.
-/

section Crux

open scoped Kronecker

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

end Crux

/-! ## The product rule for an abstract two-factor split

Stated for the concrete product index type `A × B`, so that it can be
instantiated at the splitting `Cfg n ≃ CfgIn S × CfgOut S` in either order.
-/

section Split

open scoped Kronecker

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The slice of a function on `A × B` at a fixed second coordinate. -/
def colSlice (b : B) : ((A × B) → ℂ) →ₗ[ℂ] (A → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun a => (a, b)

/-- The slice at a fixed first coordinate. -/
def rowSlice (a : A) : ((A × B) → ℂ) →ₗ[ℂ] (B → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun b => (a, b)

/-- The functions all of whose column slices lie in `Y`. -/
def liftL (Y : Submodule ℂ (A → ℂ)) : Submodule ℂ ((A × B) → ℂ) :=
  ⨅ b : B, Submodule.comap (colSlice b) Y

/-- The functions all of whose row slices lie in `W`. -/
def liftR (W : Submodule ℂ (B → ℂ)) : Submodule ℂ ((A × B) → ℂ) :=
  ⨅ a : A, Submodule.comap (rowSlice a) W

end Split

/-! ## Transporting the product rule to the qubit splitting -/

section Transport

variable {n : ℕ} {S : Finset (Fin n)}

/-- `H n` viewed through the splitting at `S`. -/
def splitEquiv (S : Finset (Fin n)) : ((CfgIn S × CfgOut S) → ℂ) ≃ₗ[ℂ] H n :=
  LinearEquiv.funCongrLeft ℂ ℂ (cfgEquiv S)

/-! ### The complementary side

`CfgOut S` and `CfgIn Sᶜ` carry the same data, as do `CfgIn S` and `CfgOut Sᶜ`,
so a subspace supported on `Sᶜ` is a right lift for the splitting at `S`. -/

/-- Configurations in `Sᶜ` and configurations outside `S` are the same data. -/
def inComplEquivOut (S : Finset (Fin n)) : CfgIn Sᶜ ≃ CfgOut S where
  toFun a i := a ⟨i.1, Finset.mem_compl.mpr i.2⟩
  invFun b i := b ⟨i.1, Finset.mem_compl.mp i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Configurations outside `Sᶜ` and configurations in `S` are the same data. -/
def outComplEquivIn (S : Finset (Fin n)) : CfgOut Sᶜ ≃ CfgIn S where
  toFun b i := b ⟨i.1, Finset.notMem_compl.mpr i.2⟩
  invFun a i := a ⟨i.1, Finset.notMem_compl.mp i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Transport

/-! ## Corollary 16: k-QSAT

The combinatorial half is identical to the classical case in `QuantumLocalLemma.Classical.KSAT`:
constraints on `k` qubits each, every qubit touched by at most `D` constraints,
so each constraint overlaps at most `k (D - 1)` others.
-/

end QLLL.QSAT


