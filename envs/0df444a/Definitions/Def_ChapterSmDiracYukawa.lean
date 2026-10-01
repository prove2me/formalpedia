-- Prove2me | Definitions.Def_ChapterSmDiracYukawa
-- name    : ChapterSmDiracYukawa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:38:35.66988+00:00
-- url     : https://prove2.me/theorems/4b281d05-ec26-411a-bd53-a51143b59178
-- title:
--   Chapter SmDiracYukawa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmDiracYukawa.lean`): generated def bundle for ChapterSmDiracYukawa. See BookProof/ChapterSmDiracYukawa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmDiracYukawa.lean

import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavineCore
import Mathlib


/-!
# The Standard-Model Dirac and Yukawa operators on the CAR algebra, and their Faris–Lavine
certificate

This module closes, for the **fermionic sector in a finite mode truncation**, two of the
honest boundaries that the Standard-Model wave of `CONSOLIDATED_PLAN.md` (§D6b-SM) left
open:

* *“the Dirac and Yukawa operators are not formalized (they need the CAR/Grassmann algebra)
  — only the mixing algebra they rest on is”*: the CAR algebra is
  `BookProof.ChapterSmCarAlgebra`, and here the two operators are **defined on it** —
  `smDirac` is the second quantization `Σ_{i,j} h_{ij} a†_i a_j` of a Hermitian one-particle
  Dirac matrix, `smYukawa` is the Higgs-background Yukawa bilinear
  `Σ_{i,j} (φ M)_{ij} a†_i a_j + h.c.` with the mass matrix `M = U_L V† D U_R†` of
  §D6b-SM.1, and the *mixing algebra* of `BookProof.ChapterSmOneParticle` is what bounds it
  (`yukawa_entry_bound`: no mixing angle can amplify a Yukawa coupling beyond the sum of the
  masses);
* *“the three Faris–Lavine hypotheses of §D6b-SM.3 remain symbolic and are not Lean
  theorems”*: for this sector they now are.  `sm_fermi_fl_i`, `sm_fermi_fl_ii` and
  `sm_fermi_fl_iii` are the relative bound `±h ≤ c₁N`, the first-commutator bound
  `|⟨ψ,[h,N]ψ⟩| ≤ c₂⟨ψ,Nψ⟩` and the double-commutator bound
  `|⟨ψ,[N,[N,h]]ψ⟩| ≤ c₃⟨ψ,N²ψ⟩`, with **explicit constants** built from the `ℓ¹` norm of
  the one-particle matrix and the mode energies; `sm_fermi_esa` feeds them to the project's
  proof of Faris–Lavine Corollary 1.1,
  `BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`, and concludes
  essential self-adjointness of the fermionic Hamiltonian.

The comparison operator is the one §D6b-SM.2 prescribes for the fermionic block —
`N = Σ_i ω_i a†_i a_i + c₀` with `ω_i ≥ 0`, `c₀ ≥ 1`, the second quantization of the
one-particle oscillator `−Δ + |x|² + 1 ≥ 1`.

## Honest boundary

The mode set is finite, so the fermionic Hamiltonian is a bounded operator and its essential
self-adjointness, while genuinely obtained through the Faris–Lavine route with the
hypotheses verified one by one, is not by itself a hard analytic fact; what the module
delivers is the *operators* and the *certificate in Lean*, not a continuum limit.  The
spinor/Lorentz structure of `γ⁰γ·D`, the ghost/BRST sector, Majorana masses and the
measured CKM/PMNS parameters remain outside; and nothing here bears on the bosonic sector,
whose inner operator is a positive sum of squares and is treated by Friedrichs in
`BookProof.ChapterSmHamiltonian` / `BookProof.ChapterSmOuterFock`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmDiracYukawa

open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

/-! ## 1. Diagonal operators on the fermionic Fock space -/

/-- A real diagonal operator in the occupation basis. -/
def diagOp (d : Finset (Fin n) → ℝ) : FermiFock n →ₗ[ℂ] FermiFock n where
  toFun ψ := WithLp.toLp 2 (fun S => (d S : ℂ) * ψ S)
  map_add' x y := by ext S; simp [mul_add]
  map_smul' c x := by ext S; simp [mul_left_comm]

















/-! ## 2. The fermionic comparison operator `N` of §D6b-SM.2 -/

/-- The diagonal weight of the fermionic comparison operator: the sum of the oscillator
energies of the occupied modes, plus the shift `c₀`. -/
def smFermiWeight (om : Fin n → ℝ) (c0 : ℝ) (S : Finset (Fin n)) : ℝ := (∑ i ∈ S, om i) + c0

/-- **The fermionic comparison operator** `N = Σ_i ω_i a†_i a_i + c₀` of §D6b-SM.2: the
second quantization of the one-particle oscillator `−Δ + |x|² + 1`, shifted so that
`N ≥ 1`. -/
def smFermiN (om : Fin n → ℝ) (c0 : ℝ) : FermiFock n →ₗ[ℂ] FermiFock n :=
  fermiEnergy om + (c0 : ℂ) • LinearMap.id







/-! ## 3. The Dirac and Yukawa operators -/

/-- **The Dirac operator of the fermionic sector**: the second quantization
`Σ_{i,j} h_{ij} a†_i a_j` of the one-particle Dirac matrix `h`. -/
def smDirac (hD : Matrix (Fin n) (Fin n) ℂ) : FermiFock n →ₗ[ℂ] FermiFock n := fermiBilin hD

/-- **The Yukawa operator** in a Higgs background `z`: the fermion bilinear `z M` plus its
Hermitian conjugate, second quantized.  `M` is the Yukawa mass matrix of §D6b-SM.1; `z` is
the (complex) value of the Higgs field multiplying it. -/
def smYukawa (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : FermiFock n →ₗ[ℂ] FermiFock n :=
  fermiBilin (z • M + (z • M).conjTranspose)

/-- The one-particle matrix of the full fermionic Hamiltonian `h_Dirac + h_Yukawa`. -/
def smFermiMatrix (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  hD + (z • M + (z • M).conjTranspose)





/-- **The fermionic Hamiltonian of the Standard-Model sector**: Dirac plus Yukawa. -/
def smFermiHam (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : FermiFock n →ₗ[ℂ] FermiFock n :=
  fermiBilin (smFermiMatrix hD M z)







/-! ## 4. The mixing algebra bounds the Yukawa operator -/





/-! ## 5. The three Faris–Lavine hypotheses of §D6b-SM.3, for the fermionic sector -/

/-- The domain on which the fermionic operators are defined: all of the (finite-dimensional)
Fock space. -/
abbrev fullDom (n : ℕ) : Submodule ℂ (FermiFock n) := ⊤

/-- An everywhere-defined operator, read as an unbounded operator on the full domain. -/
def onFull (T : FermiFock n →ₗ[ℂ] FermiFock n) : fullDom n →ₗ[ℂ] FermiFock n :=
  T ∘ₗ (fullDom n).subtype



variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

/-- The constant `c₁`: the `ℓ¹` norm of the one-particle matrix of `h_Dirac + h_Yukawa`. -/
def smFermiBound (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ‖smFermiMatrix hD M z i j‖



/-- The constant `Ω`: the upper bound on the comparison operator. -/
def smFermiOm (om : Fin n → ℝ) (c0 : ℝ) : ℝ := (∑ i : Fin n, om i) + c0





















/-- The double commutator `[N, [N, h]]`, as an everywhere-defined operator. -/
def dcommOp (H N : FermiFock n →ₗ[ℂ] FermiFock n) : FermiFock n →ₗ[ℂ] FermiFock n :=
  ⁅N, ⁅N, H⁆⁆









end

end BookProof.SmDiracYukawa


