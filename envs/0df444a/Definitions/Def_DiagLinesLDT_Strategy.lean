-- Prove2me | Definitions.Def_DiagLinesLDT_Strategy
-- name    : DiagLinesLDT_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:03.938767+00:00
-- url     : https://prove2.me/theorems/02387091-36ad-4609-85ef-3762c4f5d36b
-- title:
--   Projective strategy for the reduced test (Definition 2.4)
-- statement:
--   A **projective strategy** with parameters $(m,d)$ consists of finite-dimensional Hilbert spaces $\mathcal H_{\mathrm{Alice}},\mathcal H_{\mathrm{Bob}}$, a unit vector $|\psi\rangle\in\mathcal H_{\mathrm{Alice}}\otimes\mathcal H_{\mathrm{Bob}}$, and for each player $w$:
--
--   1. for every $u\in\mathbb F_q^m$, a projective measurement $\{A^{w,u}_a\}_{a\in\mathbb F_q}$ on $\mathcal H_w$;
--   2. for every axis-parallel line $\ell\subseteq\mathbb F_q^m$, a projective measurement $\{B^{w,\ell}_f\}_f$ on $\mathcal H_w$, with outcomes the legal answers $f:\ell\to\mathbb F_q$ of degree at most $d$.
--
--   This is the object quantified over in the goal theorem.
--
--   **Formalization Note** The Hilbert spaces are $\mathbb C^{\iota_A}$ and $\mathbb C^{\iota_B}$ with operators as matrices, and the tensor product is indexed by $\iota_A\times\iota_B$ with Alice's factor on the left. The data and the predicate `IsProjective` are separate, so a concrete strategy can be defined before its projectivity is proved. A projective measurement is the published `MIPRE.IsPVM`: Hermitian idempotents summing to the identity, with zero outcomes allowed; mutual orthogonality follows from these.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Definition 2.4, p.5

import Mathlib
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_DiagLinesLDT_AxisLine

namespace DiagLinesLDT

/-- The data of a two-prover strategy for the reduced test with parameters `(m, d)`: a vector on
`ℂ^ιA ⊗ ℂ^ιB`, and for each player a point family `A^{w,u}_a` and a line family `B^{w,ℓ}_f`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Definition 2.4, p.5.

**Formalization Note** `H_Alice = ℂ^ιA` and `H_Bob = ℂ^ιB` with operators as matrices; every
finite-dimensional Hilbert space is one of these. The tensor product is `ιA × ιB`, Alice's factor
left. Normalization and projectivity are the predicate `Strategy.IsProjective`. -/
structure Strategy (F : Type*) [Field F] (m d : ℕ) (ιA ιB : Type*) where
  /-- The shared state `|ψ⟩`. -/
  state : ιA × ιB → ℂ
  /-- Alice's point measurements `A^{Alice,u}_a`. -/
  pointA : (Fin m → F) → F → Matrix ιA ιA ℂ
  /-- Alice's line measurements `B^{Alice,ℓ}_f`. -/
  lineA : (ℓ : AxisLine F m) → LegalAnswer d ℓ → Matrix ιA ιA ℂ
  /-- Bob's point measurements `A^{Bob,u}_a`. -/
  pointB : (Fin m → F) → F → Matrix ιB ιB ℂ
  /-- Bob's line measurements `B^{Bob,ℓ}_f`. -/
  lineB : (ℓ : AxisLine F m) → LegalAnswer d ℓ → Matrix ιB ιB ℂ

/-- A **projective strategy** (Definition 2.4, p.5): `|ψ⟩` is a unit vector, and every point and line
family of both players is a projective measurement (`MIPRE.IsPVM`: Hermitian idempotents summing to
the identity; zero outcomes are allowed). -/
structure Strategy.IsProjective {F : Type*} [Field F] [Fintype F] {m d : ℕ}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (S : Strategy F m d ιA ιB) : Prop where
  /-- The state is normalized. -/
  state_norm : ∑ x, ‖S.state x‖ ^ 2 = 1
  /-- Alice's point families are projective. -/
  pointA_pvm : ∀ u, MIPRE.IsPVM (S.pointA u)
  /-- Alice's line families are projective. -/
  lineA_pvm : ∀ ℓ, MIPRE.IsPVM (S.lineA ℓ)
  /-- Bob's point families are projective. -/
  pointB_pvm : ∀ u, MIPRE.IsPVM (S.pointB u)
  /-- Bob's line families are projective. -/
  lineB_pvm : ∀ ℓ, MIPRE.IsPVM (S.lineB ℓ)

end DiagLinesLDT


