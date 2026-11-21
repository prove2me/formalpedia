-- Prove2me | Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
-- name    : KnillLaflammeLean_QuantumInfo_KnillLaflamme
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:47:48.238596+00:00
-- url     : https://prove2.me/theorems/debb09b1-28bf-4892-92db-9769a1ea1608
-- title:
--   Knill Laflamme
-- statement:
--   Definitions and structural lemmas for Knill Laflamme, from Zayn Blore's pinned Knill–Laflamme quantum error correction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Theorems.Thm_QuantumInfo_Channel_id_apply
attribute [local simp] QuantumInfo.Channel.id_apply


set_option autoImplicit false
@[expose] public section
@[expose] public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
namespace QuantumInfo
variable {n : Type*} [Fintype n]
structure IsCodeProjector (P : Matrix n n ℂ) : Prop where
  conjTranspose_eq : Pᴴ = P
  mul_self : P * P = P
namespace IsCodeProjector
variable {P : Matrix n n ℂ} (hP : IsCodeProjector P)
include hP
end IsCodeProjector
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
def KnillLaflamme (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) (c : Matrix ι ι ℂ) : Prop :=
  ∀ i j, P * (E i)ᴴ * E j * P = c i j • P
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}
section Orthogonal
omit [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [DecidableEq κ]
variable (P : Matrix n n ℂ) (F : κ → Matrix n n ℂ) (d : κ → ℝ)
noncomputable def recoveryOp (k : κ) : Matrix n n ℂ :=
  if d k = 0 then 0 else (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ) • (P * (F k)ᴴ)
noncomputable def errorImageProj (k : κ) : Matrix n n ℂ :=
  if d k = 0 then 0 else (((d k)⁻¹ : ℝ) : ℂ) • (F k * P * (F k)ᴴ)
variable [Fintype κ]
noncomputable def recoveryProj : Matrix n n ℂ :=
  ∑ k, (recoveryOp P F d k)ᴴ * recoveryOp P F d k
noncomputable def recoveryKraus : Option κ → Matrix n n ℂ
  | some k => recoveryOp P F d k
  | none => 1 - recoveryProj P F d
variable {P F d}
omit [DecidableEq n] [Fintype κ] [DecidableEq κ] in
theorem recoveryOp_conjTranspose_mul_self (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k) (k : κ) :
    (recoveryOp P F d k)ᴴ * recoveryOp P F d k = errorImageProj P F d k := by
  unfold recoveryOp errorImageProj
  split_ifs with hk
  · simp
  · rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul,
      conjTranspose_conjTranspose, hP.conjTranspose_eq]
    congr 1
    · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (hd k)]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hP.mul_self, ← Matrix.mul_assoc]
omit [DecidableEq n] [Fintype κ] in
theorem errorImageProj_mul
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) (k l : κ) :
    errorImageProj P F d k * errorImageProj P F d l
      = if k = l then errorImageProj P F d k else 0 := by
  unfold errorImageProj
  by_cases hk : d k = 0
  · simp [hk]
  by_cases hl : d l = 0
  · have hkl : k ≠ l := fun h => hk (h ▸ hl)
    simp [hl, hkl]
  rw [if_neg hk, if_neg hl, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have key : F k * P * (F k)ᴴ * (F l * P * (F l)ᴴ) = F k * (P * (F k)ᴴ * F l * P) * (F l)ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [key, hF k l]
  split_ifs with hkl
  · subst hkl
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    exact_mod_cast (by field_simp : (d k)⁻¹ * (d k)⁻¹ * d k = (d k)⁻¹)
  · simp
omit [DecidableEq n] [Fintype κ] [DecidableEq κ] in
theorem errorImageProj_conjTranspose (hP : IsCodeProjector P) (k : κ) :
    (errorImageProj P F d k)ᴴ = errorImageProj P F d k := by
  unfold errorImageProj
  split_ifs
  · simp
  · rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, conjTranspose_mul,
      conjTranspose_mul, conjTranspose_conjTranspose, hP.conjTranspose_eq, Matrix.mul_assoc]
omit [DecidableEq n] [DecidableEq κ] in
theorem recoveryProj_eq (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k) :
    recoveryProj P F d = ∑ k, errorImageProj P F d k := by
  unfold recoveryProj
  exact Finset.sum_congr rfl fun k _ => recoveryOp_conjTranspose_mul_self hP hd k
omit [DecidableEq n] in
theorem recoveryProj_mul_self (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) :
    recoveryProj P F d * recoveryProj P F d = recoveryProj P F d := by
  rw [recoveryProj_eq hP hd, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum]
  simp only [errorImageProj_mul hF]
  simp
omit [DecidableEq n] [DecidableEq κ] in
theorem recoveryProj_conjTranspose (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k) :
    (recoveryProj P F d)ᴴ = recoveryProj P F d := by
  rw [recoveryProj_eq hP hd, conjTranspose_sum]
  exact Finset.sum_congr rfl fun k _ => errorImageProj_conjTranspose hP k
theorem recoveryKraus_tp (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) :
    ∑ o : Option κ, (recoveryKraus P F d o)ᴴ * recoveryKraus P F d o = 1 := by
  rw [Fintype.sum_option]
  have h1 : ∑ k, (recoveryKraus P F d (some k))ᴴ * recoveryKraus P F d (some k)
      = recoveryProj P F d := rfl
  rw [h1]
  show (1 - recoveryProj P F d)ᴴ * (1 - recoveryProj P F d) + recoveryProj P F d = 1
  rw [conjTranspose_sub, conjTranspose_one, recoveryProj_conjTranspose hP hd]
  have hQ := recoveryProj_mul_self hP hd hF
  simp only [sub_mul, mul_sub, one_mul, mul_one, hQ]
  abel
noncomputable def recoveryChannel (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) :
    Channel n n (Option κ) where
  kraus := recoveryKraus P F d
  tp := recoveryKraus_tp hP hd hF
end Orthogonal
section Canonical
variable (hc' : c.IsHermitian)
noncomputable def klUnitary : Matrix ι ι ℂ := hc'.eigenvectorUnitary
noncomputable def canonicalError (E : ι → Matrix n n ℂ) (k : ι) : Matrix n n ℂ :=
  ∑ i, klUnitary hc' i k • E i
end Canonical
section Converse
end Converse
section Encoder
variable {L : Type*} [Fintype L] [DecidableEq L] {V : Matrix n L ℂ}
def EncoderKL (V : Matrix n L ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∀ i j, ∃ γ : ℂ, Vᴴ * (E i)ᴴ * E j * V = γ • 1
end Encoder
end QuantumInfo
end


