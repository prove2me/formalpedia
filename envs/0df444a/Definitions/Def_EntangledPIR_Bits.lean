-- Prove2me | Definitions.Def_EntangledPIR_Bits
-- name    : EntangledPIR_Bits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:56.527007+00:00
-- url     : https://prove2.me/theorems/eb134be1-74df-4e8f-b1c6-a2ab0e615d24
-- title:
--   Bit strings, $X^a$, $Z^a$, $a\cdot b$, and the Hadamard-basis projectors
-- statement:
--   Notation for $d$ qubits. Their computational basis is $\{0,1\}^d$, with $\oplus$ the coordinatewise XOR and $a\cdot b=a_1b_1+\dots+a_db_d$ modulo two. The operators are:
--
--   1. $X^a=X^{a_1}\otimes\dots\otimes X^{a_d}$, the permutation $q\mapsto q\oplus a$;
--   2. $Z^a=Z^{a_1}\otimes\dots\otimes Z^{a_d}$, the diagonal matrix with entries $(-1)^{a\cdot q}$;
--   3. $H^{\otimes d}|f\rangle$, with entries $2^{-d/2}(-1)^{f\cdot q}$, and its projector $H^{\otimes d}|f\rangle\langle f|H^{\otimes d}$;
--   4. the projectors $|J\rangle\langle J|$ of the computational basis.
--
--   These are the objects from which the lookup and its test are built.
--
--   **Formalization Note** The integer `bdot a b` is only used as an exponent of $-1$, so its parity is the paper's $a\cdot b$.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), §2, Notation, p.9

import Mathlib

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), §2,
Notation, p.9: bit strings, `X^a`, `Z^a`, `a · b`, and the projectors of the Hadamard basis.
-/

open Matrix

namespace EntangledPIR

/-- A bit string in `{0,1}^d`. `d` qubits have the computational basis `Bits d`, and an operator
on them is a `Matrix (Bits d) (Bits d) ℂ`. -/
abbrev Bits (d : ℕ) : Type := Fin d → Bool

/-- Coordinatewise XOR `a ⊕ b`. -/
def bxor {d : ℕ} (a b : Bits d) : Bits d := fun i => xor (a i) (b i)

/-- The all-zero string `0^d`. -/
def bzero (d : ℕ) : Bits d := fun _ => false

/-- XOR of a finite family, `⊕_{i ∈ s} f i`: a coordinate is one iff an odd number of the
strings have that coordinate one. -/
def bigXor {ι : Type} {d : ℕ} (s : Finset ι) (f : ι → Bits d) : Bits d :=
  fun b => decide (Odd (s.filter (fun i => f i b = true)).card)

/-- The integer `a_1 b_1 + ⋯ + a_d b_d`; the paper's `a · b` is its value modulo two, p.9, and it
is only used as the exponent of `-1`. -/
def bdot {d : ℕ} (a b : Bits d) : ℕ := ∑ i, if a i && b i then 1 else 0

/-- `X^a = X^{a_1} ⊗ ⋯ ⊗ X^{a_d}`, p.9: the permutation matrix of `q ↦ q ⊕ a`. -/
def pauliXs {d : ℕ} (a : Bits d) : Matrix (Bits d) (Bits d) ℂ :=
  Matrix.of fun p q => if p = bxor q a then 1 else 0

/-- `Z^a = Z^{a_1} ⊗ ⋯ ⊗ Z^{a_d}`, p.9: the diagonal matrix with entries `(-1)^{a · q}`. -/
def pauliZs {d : ℕ} (a : Bits d) : Matrix (Bits d) (Bits d) ℂ :=
  Matrix.diagonal fun q => (-1) ^ bdot a q

/-- The vector `H^{⊗d}|f⟩`, with entries `2^{-d/2} (-1)^{f · q}`. -/
noncomputable def hadVec {d : ℕ} (f : Bits d) : Bits d → ℂ :=
  fun q => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ d * (-1) ^ bdot f q

/-- The projector `H^{⊗d}|f⟩⟨f|H^{⊗d}` of the measurement in the Hadamard basis, p.9. -/
noncomputable def hadProj {d : ℕ} (f : Bits d) : Matrix (Bits d) (Bits d) ℂ :=
  Matrix.vecMulVec (hadVec f) (star (hadVec f))

/-- The projector `|J⟩⟨J|` of the computational basis. -/
def basisProj {d : ℕ} (J : Bits d) : Matrix (Bits d) (Bits d) ℂ :=
  Matrix.of fun p q => if p = J ∧ q = J then 1 else 0

end EntangledPIR


