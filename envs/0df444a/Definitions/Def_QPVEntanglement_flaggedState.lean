-- Prove2me | Definitions.Def_QPVEntanglement_flaggedState
-- name    : QPVEntanglement_flaggedState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:09.454299+00:00
-- url     : https://prove2.me/theorems/0ea9e384-597f-4d72-80cb-e62e2ceb83a1
-- title:
--   Classically flagged mixtures of pure states (Definition 1)
-- statement:
--   A register $C$ is **classical** in a joint state if the state has the form $\rho_{CQ}=\sum_c p_c|c\rangle\langle c|_C\otimes\rho^c_Q$ — the joint form, not merely a diagonal marginal. A **classically flagged mixture of pure states** with flag $C\subseteq A_1=C\otimes A_1'$ is
--
--   $$\rho_{OA_1A_2}=\sum_c p_c|c\rangle\langle c|_C\otimes|\psi_c\rangle\langle\psi_c|_{OA_1'A_2}.$$
--
--   The module also provides the records held on the left or right side, the two-record form of Corollary 2 (eq. (18)), record sectors and blocks, and flag-controlled operators $\sum_c|c\rangle\langle c|\otimes U_c$.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Definition 1, p.27; eqs. (8), (10), (18), pp.33–35

import Mathlib
import Definitions.Def_QPVEntanglement_bellOverlap

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement

/-- `(p_c)_c` is a probability vector. -/
def IsProbVec {C : Type*} [Fintype C] (p : C → ℝ) : Prop := (∀ c, 0 ≤ p c) ∧ ∑ c, p c = 1

/-- `ψ` is a unit vector. -/
def IsUnitVec {Q : Type*} [Fintype Q] (ψ : Q → ℂ) : Prop := star ψ ⬝ᵥ ψ = 1

/-- `ρ` is a density matrix (positive semidefinite, trace one). -/
def IsDensity {Q : Type*} [Fintype Q] (ρ : Matrix Q Q ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- The pure state `|ψ⟩⟨ψ|`. -/
noncomputable def pureDensity {Q : Type*} (ψ : Q → ℂ) : Matrix Q Q ℂ := Matrix.vecMulVec ψ (star ψ)

/-- The classical-quantum state `Σ_c p_c |c⟩⟨c|_C ⊗ ρ_c` on `C × Q` (Definition 1, p.27): the
**joint** form, not merely a diagonal marginal of `C`. -/
noncomputable def cqState {C Q : Type*} [DecidableEq C] (p : C → ℝ) (ρ : C → Matrix Q Q ℂ) :
    Matrix (C × Q) (C × Q) ℂ :=
  fun x y => if x.1 = y.1 then (p x.1 : ℂ) * ρ x.1 x.2 y.2 else 0

/-- **A classically flagged mixture of pure states** with the flag `C` a subregister of
`A₁ = C ⊗ A₁'` (Definition 1, p.27; eqs. (8), (10), p.33–34). Behera–Goyal, arXiv:2609.39234
(sha256 bdf2928d…), Definition 1, p.27:

`ρ_{OA₁A₂} = Σ_c p_c |c⟩⟨c|_C ⊗ |ψ_c⟩⟨ψ_c|_{OA₁'A₂}`

as a matrix on `O × ((C × A₁') × A₂)`. -/
noncomputable def flaggedState {O C A1 A2 : Type*} [DecidableEq C] (p : C → ℝ)
    (ψ : C → O × (A1 × A2) → ℂ) : Matrix (O × ((C × A1) × A2)) (O × ((C × A1) × A2)) ℂ :=
  fun x y => if x.2.1.1 = y.2.1.1 then
    (p x.2.1.1 : ℂ) * ψ x.2.1.1 (x.1, (x.2.1.2, x.2.2)) * star (ψ x.2.1.1 (y.1, (y.2.1.2, y.2.2)))
    else 0

/-- A classical record held on the left: `Σ_c p_c |c⟩⟨c|_C ⊗ ω_c` with `C` a subregister of the
left party, as a matrix on `(C × A) × B` (Definition 1 and Lemma 1, p.27). -/
noncomputable def recordOnLeft {C A B : Type*} [DecidableEq C] (p : C → ℝ)
    (ω : C → Matrix (A × B) (A × B) ℂ) : Matrix ((C × A) × B) ((C × A) × B) ℂ :=
  fun x y => if x.1.1 = y.1.1 then (p x.1.1 : ℂ) * ω x.1.1 (x.1.2, x.2) (y.1.2, y.2) else 0

/-- A classical record held on the right: `Σ_c p_c |c⟩⟨c|_C ⊗ ω_c` on `A × (C × B)`. -/
noncomputable def recordOnRight {C A B : Type*} [DecidableEq C] (p : C → ℝ)
    (ω : C → Matrix (A × B) (A × B) ℂ) : Matrix (A × (C × B)) (A × (C × B)) ℂ :=
  fun x y => if x.2.1 = y.2.1 then (p x.2.1 : ℂ) * ω x.2.1 (x.1, x.2.2) (y.1, y.2.2) else 0

/-- Classical records on both sides (Corollary 2, eq. (18), p.35):
`Σ_{c=(c₀,c₁)} p_c |c₀⟩⟨c₀|_{C₀} ⊗ |c₁⟩⟨c₁|_{C₁} ⊗ |ψ_c⟩⟨ψ_c|_{OA₀'A₁'}` on
`O × ((C₀ × A₀') × (C₁ × A₁'))`. -/
noncomputable def flaggedState2 {O C0 C1 A0 A1 : Type*} [DecidableEq C0] [DecidableEq C1]
    (p : C0 × C1 → ℝ) (ψ : C0 × C1 → O × (A0 × A1) → ℂ) :
    Matrix (O × ((C0 × A0) × (C1 × A1))) (O × ((C0 × A0) × (C1 × A1))) ℂ :=
  fun x y => if x.2.1.1 = y.2.1.1 ∧ x.2.2.1 = y.2.2.1 then
    (p (x.2.1.1, x.2.2.1) : ℂ) * ψ (x.2.1.1, x.2.2.1) (x.1, (x.2.1.2, x.2.2.2)) *
      star (ψ (x.2.1.1, x.2.2.1) (y.1, (y.2.1.2, y.2.2.2)))
    else 0

/-- The operator `|c₀⟩⟨c₀| ⊗ |c₁⟩⟨c₁| ⊗ X` on `(C₀ × A₀) × (C₁ × A₁)`: an input with definite
record value `c`. -/
noncomputable def flagSector {C0 C1 A0 A1 : Type*} [DecidableEq C0] [DecidableEq C1]
    (c : C0 × C1) (X : Matrix (A0 × A1) (A0 × A1) ℂ) :
    Matrix ((C0 × A0) × (C1 × A1)) ((C0 × A0) × (C1 × A1)) ℂ :=
  fun x y => if x.1.1 = c.1 ∧ y.1.1 = c.1 ∧ x.2.1 = c.2 ∧ y.2.1 = c.2 then
    X (x.1.2, x.2.2) (y.1.2, y.2.2) else 0

/-- The block of record value `c` of a state on `O × ((C₀ × B₀) × (C₁ × B₁))`, i.e.
`⟨c|τ|c⟩` on `O × (B₀ × B₁)` (unnormalized: its trace is the probability of `c`). -/
noncomputable def sectorBlock {O C0 C1 B0 B1 : Type*} (c : C0 × C1)
    (τ : Matrix (O × ((C0 × B0) × (C1 × B1))) (O × ((C0 × B0) × (C1 × B1))) ℂ) :
    Matrix (O × (B0 × B1)) (O × (B0 × B1)) ℂ :=
  fun x y => τ (x.1, ((c.1, x.2.1), (c.2, x.2.2))) (y.1, ((c.1, y.2.1), (c.2, y.2.2)))

/-- A flag-respecting operator `Σ_c |c⟩⟨c|_C ⊗ U_c` on `C × A'` ("`U_j` does not scramble the
classical flag register", Theorem 6, p.34). -/
noncomputable def flagControlled {C A : Type*} [DecidableEq C] (U : C → Matrix A A ℂ) :
    Matrix (C × A) (C × A) ℂ :=
  fun x y => if x.1 = y.1 then U x.1 x.2 y.2 else 0

end QPVEntanglement


