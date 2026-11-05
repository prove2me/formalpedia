-- Prove2me | Definitions.Def_FermionModewise_IsCAR
-- name    : FermionModewise_IsCAR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:22.906884+00:00
-- url     : https://prove2.me/theorems/c76c7d83-a7d8-456b-92ea-778e9709a787
-- title:
--   Canonical anticommutation relations
-- statement:
--   Let $\iota$ be a finite set, so that operators are complex matrices on $\mathbb C^\iota$, and let $(b_i)_{i\in\mu}$ be a family of such operators indexed by a set of modes $\mu$. The family satisfies the **canonical anticommutation relations** (CAR) if, for all modes $i,j$,
--   $$\{b_i,b_j\}=b_ib_j+b_jb_i=0,\qquad \{b_i,b_j^\dagger\}=b_ib_j^\dagger+b_j^\dagger b_i=\delta_{ij}\,\mathbb 1 .$$
--   The relation $\{b_i^\dagger,b_j^\dagger\}=0$ follows by taking adjoints.
--
--   This is the algebraic setting of every statement in the mission: $b_i$ annihilates a fermion in mode $i$ and $b_i^\dagger$ creates one.
--
--   **Formalization Note.** Any finite-dimensional representation is allowed, not only the Fock space of dimension $2^{|\mu|}$. The mode set $\mu$ may be empty.
-- source:
--   Botero–Reznik, BCS-like Modewise Entanglement of Fermion Gaussian States, arXiv:quant-ph/0404176v3, p.3 (anticommutation relations before (4))

import Mathlib

open Matrix

namespace FermionModewise

/-- **Canonical anticommutation relations** (Botero–Reznik, *BCS-like Modewise Entanglement of
Fermion Gaussian States*, arXiv:quant-ph/0404176v3, p.3): a family `b : μ → Matrix ι ι ℂ` of
annihilation operators on the finite-dimensional space `ℂ^ι` satisfies
`{b_i, b_j} = 0` and `{b_i, b_j†} = δ_ij`.

**Formalization Note.** Operators are complex matrices on an arbitrary finite type `ι` (any
finite-dimensional representation, not only the Fock space), and `ᴴ` is the adjoint. The
relation `{b_i†, b_j†} = 0` of the page is the adjoint of the first clause and is not repeated.
The mode type `μ` is an arbitrary type with decidable equality (it may be empty). -/
def IsCAR {ι μ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq μ]
    (b : μ → Matrix ι ι ℂ) : Prop :=
  (∀ i j, b i * b j + b j * b i = 0) ∧
    (∀ i j, b i * (b j)ᴴ + (b j)ᴴ * b i = if i = j then 1 else 0)

end FermionModewise


