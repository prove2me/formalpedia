-- Prove2me | Definitions.Def_QuadraticRE_Supplement_CircuitEnc
-- name    : QuadraticRE_Supplement_CircuitEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:52:30.937884+00:00
-- url     : https://prove2.me/theorems/55a1afca-cfbd-4af3-972c-e5de803f7e5c
-- title:
--   Encoding constructions for circuit representations and the one-input-per-monomial property
-- statement:
--   The public parameters of a construction for circuit representations are a circuit $C$ and $1^\lambda$ with $\lambda\ge1$, encoded with every number in unary. A construction (the published `QuadraticRE.Construction`) assigns to them an explicit polynomial description $E_{C,\lambda}$, a decoder and a simulator on uniform coins.
--
--   1. A description has **at most one original input bit per monomial** if every monomial of every coordinate contains at most one input variable (counted with multiplicity); tape variables are unrestricted.
--   2. Given a construction $K$ and a circuit family $(C_\kappa)_{\kappa}$, the **induced family of encodings** has at index $\kappa$ the parameters $(C_\kappa,1^{\max\{\kappa,1\}})$, the encoder $E_{C_\kappa,\kappa}$, the function computed by $C_\kappa$ and the constructed simulator. Computational privacy of this family is the published `QuadraticRE.CompPrivate` (Definition 3.7).
--
--   These objects state Theorem 4.13.
--
--   **Formalization Note** The index $\kappa=0$ is mapped to $\lambda=1$; negligibility only concerns large $\kappa$.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Definition 3.7, pp.15–16; Theorem 4.13, p.31

import Mathlib
import Definitions.Def_QuadraticRE_CompPrivate
import Definitions.Def_QuadraticRE_Supplement_Circuit

namespace QuadraticRE.Supplement

open QuadraticRE

/-- The public parameters `(C, 1^λ)` of an encoding construction for circuit representations
(Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…),
Definition 3.7, p.15, and Theorem 4.13, p.31), with `λ ≥ 1`. -/
structure CParam where
  C : Circuit
  lam : ℕ
  hlam : 1 ≤ lam

/-- The bit encoding of `(C, 1^λ)`: all numbers in unary, so its length is polynomially related to
`σ + λ`. -/
def encCParam (p : CParam) : List Bool := encTokens (circuitTokens p.C ++ [p.lam])

/-- Every monomial of the expanded polynomial description contains at most one original input bit
(Theorem 4.13, p.31): at most one `Sum.inl` variable per monomial, counted with multiplicity. -/
def OneInputPerMonomial {N ρ ℓ : ℕ} (D : Desc N ρ ℓ) : Prop :=
  ∀ i, ∀ m ∈ D.coords i, m.countP (fun v => v.isLeft) ≤ 1

/-- The family `(E_λ)` that a construction `K` for circuit representations produces on a circuit
family `(C_λ)`, as an `EncFamily` (the base mission's container for Definition 3.7's computational
privacy): at index `κ` the parameters are `(C_κ, 1^{max κ 1})`, the encoder is the description
`K.desc`, the function is the one `C_κ` computes, and the simulator is `K.sim`.

**Formalization Note.** Families are indexed by `κ : ℕ`; the index `κ = 0` is mapped to `λ = 1`, which
is harmless because negligibility only concerns large `κ`. -/
def circuitFamily (K : Construction (Par := CParam) (fun p => p.C.N) (fun p => p.C.b))
    (Cs : ℕ → Circuit) : EncFamily where
  N κ := (Cs κ).N
  ρ κ := K.ρ ⟨Cs κ, max κ 1, le_max_right _ _⟩
  ℓ κ := K.ℓ ⟨Cs κ, max κ 1, le_max_right _ _⟩
  b κ := (Cs κ).b
  τ κ := K.τ ⟨Cs κ, max κ 1, le_max_right _ _⟩
  E κ := (K.desc ⟨Cs κ, max κ 1, le_max_right _ _⟩).eval
  f κ := (Cs κ).eval
  sim κ := K.sim ⟨Cs κ, max κ 1, le_max_right _ _⟩

end QuadraticRE.Supplement


