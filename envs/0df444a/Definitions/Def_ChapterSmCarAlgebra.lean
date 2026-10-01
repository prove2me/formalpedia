-- Prove2me | Definitions.Def_ChapterSmCarAlgebra
-- name    : ChapterSmCarAlgebra
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:51:48.684499+00:00
-- url     : https://prove2.me/theorems/2ec50b24-ca02-4bc2-8652-a78982f80d5c
-- title:
--   Chapter SmCarAlgebra
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmCarAlgebra.lean`): generated def bundle for ChapterSmCarAlgebra. See BookProof/ChapterSmCarAlgebra.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmCarAlgebra.lean

import Mathlib


/-!
# The CAR algebra of the Standard-Model fermions, on a finite mode set

This module removes one of the honest boundaries recorded for the Standard-Model wave of
`CONSOLIDATED_PLAN.md` (§D6b-SM): *“the Dirac and Yukawa operators are not formalized (they
need the CAR/Grassmann algebra) — only the mixing algebra they rest on is”*.  What was
missing was the algebra itself: a Hilbert space carrying creation and annihilation operators
with the canonical **anticommutation** relations.  That is what is built here, for a finite
set of fermionic modes `Fin n`.

## The construction

The fermionic Fock space over `n` modes is the `2ⁿ`-dimensional occupation-number space

```
FermiFock n = ℓ²( Finset (Fin n) )
```

— one orthonormal basis vector `occ S` for each *occupied set* `S ⊆ {0, …, n-1}`, which is
the Lean rendering of the Grassmann degrees of freedom `ζ_F ∈ Z₂^{D_F}` of §D6b-SM.1.  The
annihilation and creation operators carry the Jordan–Wigner sign `jwSign i S = (-1)^{#{j ∈ S
: j < i}}`, which is exactly what makes them *anti*commute rather than commute:

```
(a_i ψ)(S) = if i ∈ S then 0 else jwSign i S * ψ (insert i S)
(a†_i ψ)(S) = if i ∈ S then jwSign i (S.erase i) * ψ (S.erase i) else 0
```

## What is proved

* `car_annih_creat_self` — `a_i a†_i + a†_i a_i = 1`;
* `car_annih_creat_of_ne`, `car_annih_annih`, `car_creat_creat` — the three vanishing
  anticommutators `{a_i, a†_j} = 0 (i ≠ j)`, `{a_i, a_j} = 0`, `{a†_i, a†_j} = 0`
  (including `a_i² = 0`, `(a†_i)² = 0`: the Pauli principle);
* `inner_creat_left`, `inner_annih_left` — `a†_i` is the adjoint of `a_i`;
* `norm_annih_le`, `norm_creat_le` — both are contractions, so every polynomial in them is
  a bounded operator (this is the technical reason the fermionic sector needs no
  Faris–Lavine analysis of its own once the mode set is finite);
* `occupation_apply` — `a†_i a_i` is the occupation-number operator of mode `i`;
* `fermiBilin` — the second quantization `Σ_{i,j} h_{ij} a†_i a_j` of a one-particle matrix,
  with `fermiBilin_symmetric` (Hermitian `h` gives a symmetric operator) and
  `norm_fermiBilin_le` (the `ℓ¹` bound on its norm);
* `fermiEnergy`, `fermiEnergy_apply`, `fermiEnergy_occ` — the diagonal case: the exact
  **spectrum** `Σ_{i ∈ S} m i` of the free fermionic Hamiltonian on the occupation basis;
* `fermi_mass_gap` — a **gap theorem**: if every mode energy is at least `μ ≥ 0`, then every
  state orthogonal to the Fock vacuum has energy at least `μ`.

## Honest boundary

The mode set is finite: this is the CAR algebra of a *truncated* fermion field, which is
what the Standard-Model chapters need in order to write `h_Dirac` and `h_Yukawa` as
operators (`BookProof.ChapterSmDiracYukawa`).  The continuum CAR algebra over an
infinite-dimensional one-particle space, the Lorentz/spinor structure of `γ⁰γ·D`, and the
ghost/BRST sector are not built here.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmCar

open Finset

variable {n : ℕ}

/-! ## 1. The occupation-number Hilbert space -/

/-- **The fermionic Fock space over `n` modes**: the `2ⁿ`-dimensional Hilbert space with one
orthonormal basis vector for each occupied set. -/
abbrev FermiFock (n : ℕ) : Type := EuclideanSpace ℂ (Finset (Fin n))

/-- The occupation basis vector `|S⟩`. -/
noncomputable def occ (S : Finset (Fin n)) : FermiFock n := EuclideanSpace.single S 1

/-- The Fock vacuum `|∅⟩`. -/
noncomputable def vac : FermiFock n := occ ∅









/-- **The Jordan–Wigner sign** `(-1)^{#{j ∈ S : j < i}}`: the sign that makes the operators
below anticommute. -/
def jwSign (i : Fin n) (S : Finset (Fin n)) : ℂ :=
  (-1) ^ (S.filter (fun j => j < i)).card









/-! ## 2. Annihilation and creation -/

/-- **The annihilation operator** `a_i`. -/
noncomputable def annih (i : Fin n) : FermiFock n →ₗ[ℂ] FermiFock n where
  toFun ψ := WithLp.toLp 2 (fun S => if i ∈ S then 0 else jwSign i S * ψ (insert i S))
  map_add' x y := by ext S; by_cases h : i ∈ S <;> simp [h, mul_add]
  map_smul' c x := by ext S; by_cases h : i ∈ S <;> simp [h, mul_left_comm]

/-- **The creation operator** `a†_i`. -/
noncomputable def creat (i : Fin n) : FermiFock n →ₗ[ℂ] FermiFock n where
  toFun ψ := WithLp.toLp 2
    (fun S => if i ∈ S then jwSign i (S.erase i) * ψ (S.erase i) else 0)
  map_add' x y := by ext S; by_cases h : i ∈ S <;> simp [h, mul_add]
  map_smul' c x := by ext S; by_cases h : i ∈ S <;> simp [h, mul_left_comm]





/-! ## 3. The canonical anticommutation relations -/









/-! ## 4. Adjointness and contractivity -/

/-- The involution of occupation sets that adds or removes the mode `i`. -/
def flipOcc (i : Fin n) : Finset (Fin n) ≃ Finset (Fin n) :=
  Function.Involutive.toPerm (fun S => if i ∈ S then S.erase i else insert i S) (by
    intro S
    by_cases h : i ∈ S
    · simp [h, Finset.insert_erase h]
    · simp [h, Finset.erase_insert h])











/-! ## 5. Occupation numbers, second quantization, and the spectrum -/



/-- **The second quantization of a one-particle matrix**, in the creation-left /
annihilation-right spelling of the programme's doctrine: `Σ_{i,j} h_{ij} a†_i a_j`. -/
noncomputable def fermiBilin (h : Matrix (Fin n) (Fin n) ℂ) : FermiFock n →ₗ[ℂ] FermiFock n :=
  ∑ i : Fin n, ∑ j : Fin n, h i j • (creat i ∘ₗ annih j)







/-- **The free fermionic Hamiltonian** `Σ_i m_i a†_i a_i` with real mode energies. -/
noncomputable def fermiEnergy (m : Fin n → ℝ) : FermiFock n →ₗ[ℂ] FermiFock n :=
  fermiBilin (Matrix.diagonal fun i => (m i : ℂ))











/-! ## 6. Two worked values, to pin the conventions -/





end BookProof.SmCar


