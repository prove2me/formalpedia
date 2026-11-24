-- Prove2me | Definitions.Def_HodgeComputerCycleQ2Character
-- name    : HodgeComputerCycleQ2Character
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-24T00:02:25.300402+00:00
-- url     : https://prove2.me/theorems/b273cb89-0437-4f70-9bfc-637fd70f125b
-- title:
--   Sixth-root character grading on the ambient ring
-- statement:
--   On the six variables $(X_0,X_1,X_2,Y_0,Y_1,Y_2)$ assign the sixth-root weights $(2,1,0,3,2,1)$. The weight of a monomial is the corresponding integer linear combination of its exponents.
--
--   A polynomial $\varphi$ is of character $\chi\in\mathbb{Z}/6\mathbb{Z}$ when every monomial in its support has weight congruent to $\chi$ modulo $6$. The two monomials of the sparse source $\Delta$ both have character $1$, and $F$ has character $0$, so the graded residue equation stays inside a single character class once the denominator $S$ does.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_graded_linear_system, https://prove2.me/theorems/0582016f-408c-4e7a-90fd-8ea1ed63a4a8. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPolynomial.Basic

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

/-- Sixth-root weights `(2,1,0,3,2,1)` on `(X₀,X₁,X₂,Y₀,Y₁,Y₂)`. -/
def HodgeComputer.CycleQ2.sixthRootWeight : Fin 6 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 1

/-- `φ` lies in a single character class modulo `6`. -/
def HodgeComputer.CycleQ2.IsCharacter (χ : ZMod 6) (φ : AmbientPoly 5) : Prop :=
  ∀ ⦃d : Fin 6 →₀ ℕ⦄, coeff d φ ≠ 0 →
    (↑(Finsupp.weight (R := ℕ) sixthRootWeight d) : ZMod 6) = χ


