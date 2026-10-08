-- Prove2me | Definitions.Def_QLLL_Quantum_KQSAT_Projector
-- name    : QLLL_Quantum_KQSAT_Projector
-- status  : Definition
-- author  : @sattath
-- created : 2026-10-06T17:43:24.734305+00:00
-- url     : https://prove2.me/theorems/62d8ad72-d813-4f00-b9a8-8e050c659039
-- title:
--   $k$-QSAT instances given by local projectors, their satisfying space, and satisfiability
-- statement:
--   Definitions for $k$-QSAT instances (namespace `QLLL.QSAT`).
--
--   1. **Instance** (`QSATInstance n k`). A $k$-QSAT instance on $n$ qubits: a number $m$ of constraints and, for each constraint $i$, a set $q_i$ of exactly $k$ qubits and a matrix $\Pi_i$ on $\mathbb{C}^{\{0,1\}^{q_i}}$ that is idempotent ($\Pi_i^2 = \Pi_i$) and self-adjoint ($\Pi_i^\dagger = \Pi_i$), i.e. an orthogonal projector, expressed with Mathlib's `IsStarProjection`.
--   2. **Satisfying space** (`satisfyingSpace`). The subspace of $\mathcal{H}_n$ of states annihilated by every $\Pi_i \otimes I$, the intersection of the lifted kernels.
--   3. **Satisfiability** (`Satisfiable`). The instance is satisfiable if its satisfying space is nonzero, that is, some nonzero state is annihilated by every constraint.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Section 1 (definition of k-QSAT) and Definition 10

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Mathlib

/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# Physical projectors and a k-QSAT instance

`QuantumLocalLemma.Quantum.KQSAT.Basic` proves Corollary 16 with the support and dimension facts as
*hypotheses*: it assumes each constraint subspace is supported on its qubit set
and has large enough relative dimension. That is the content of the corollary but
not a formulation of k-QSAT, because no projector appears anywhere.

This file supplies the missing layer.

* `exists_selfAdjoint_isIdempotentElem` : every subspace is the range of a
  *physical* projector, an idempotent and self-adjoint matrix, namely the
  orthogonal projection onto it. So projectors here are quantum projectors, not
  merely algebraic idempotents.
* `finrank_ker_mulVecLin` : rank-nullity, giving the dimension of a satisfying
  space from the rank of its projector.
* `QSATInstance` and `QSATInstance.Satisfiable` : a k-QSAT instance is a family
  of projectors, each acting on `k` qubits, and it is satisfiable when some
  nonzero state is annihilated by all of them.
* `satisfiable_of_degree_le` : Corollary 16 with support and dimension *derived*
  from the projectors rather than assumed.
-/

namespace QLLL.QSAT

open scoped Matrix Kronecker
open WithLp (toLp ofLp)

section IdempotentKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end IdempotentKernel

/-! ## Frustration-freeness

The zero-energy space of a sum of physical projectors is exactly the set of
states satisfying every constraint. This is what links `Satisfiable` below to
the Hamiltonian phrasing of QSAT.
-/

section FrustrationFree

open scoped ComplexOrder

end FrustrationFree

/-! ## Amplifying a local projector to the whole space

A `k`-QSAT constraint is a projector on the `k` qubits it acts on. To write the
Hamiltonian as a single operator these have to be amplified to the common space
`H n`, which is tensoring with the identity on the other qubits.
-/

section Amplify

variable {n : ℕ} {S : Finset (Fin n)} {p : Matrix (CfgIn S) (CfgIn S) ℂ}

end Amplify

/-! ## A k-QSAT instance -/

variable {n : ℕ}

/-- A `k`-QSAT instance on `n` qubits: for each constraint, the `k` qubits it
acts on together with a projector on those qubits, required to be an orthogonal
projector in Mathlib's sense (`IsStarProjection`: idempotent and self-adjoint). -/
structure QSATInstance (n k : ℕ) where
  /-- The number of constraints. -/
  size : ℕ
  /-- The qubits each constraint acts on. -/
  qubits : Fin size → Finset (Fin n)
  /-- Each constraint is `k`-local. -/
  card_qubits : ∀ i, (qubits i).card = k
  /-- The projector of each constraint, on its own qubits. -/
  proj : (i : Fin size) → Matrix (CfgIn (qubits i)) (CfgIn (qubits i)) ℂ
  /-- Each constraint is an orthogonal projector: idempotent and self-adjoint
  (for matrices, `star` is the conjugate transpose). -/
  isStarProjection : ∀ i, IsStarProjection (proj i)

namespace QSATInstance

variable {k : ℕ}

/-- The satisfying space: the states annihilated by every projector. -/
def satisfyingSpace (I : QSATInstance n k) : Submodule ℂ (H n) :=
  Finset.univ.inf fun i => lift (I.qubits i) (LinearMap.ker (I.proj i).mulVecLin)

/-- An instance is satisfiable when some nonzero state satisfies every
constraint. -/
def Satisfiable (I : QSATInstance n k) : Prop := I.satisfyingSpace ≠ ⊥

end QSATInstance

/-! ## The Hamiltonian formulation

QSAT is normally posed as: is the local Hamiltonian `H = ∑ Πᵢ` frustration free,
i.e. does it have a zero-energy state? The results above make that equivalent to
the subspace statement used for the local lemma.
-/

namespace QSATInstance

variable {k : ℕ}

end QSATInstance

end QLLL.QSAT


