-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
-- name    : QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:24:38.301018+00:00
-- url     : https://prove2.me/theorems/29260e20-8f51-4785-8a40-31d4ad418190
-- title:
--   LPSHecke Representatives
-- statement:
--   Definitions and structural lemmas for LPSHecke Representatives, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
lemma lpsHeckeFiniteColumn (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det=(p:ℤ))
    (hcol : (A 0 0 : ZMod p)≠0 ∨ (A 1 0 : ZMod p)≠0) :
    ∃ j : Fin p, (p:ℤ) ∣ A 0 1-A 0 0*(j.val:ℤ) ∧
      (p:ℤ) ∣ A 1 1-A 1 0*(j.val:ℤ) := by
  have hd : (A 0 0 : ZMod p)*(A 1 1 : ZMod p)-
      (A 0 1 : ZMod p)*(A 1 0 : ZMod p)=0 := by
    have h := congrArg (fun x : ℤ => (x : ZMod p)) hA
    simpa [Matrix.det_fin_two] using h
  rcases hcol with ha | hc
  · let u : ZMod p := (A 0 1 : ZMod p)/(A 0 0 : ZMod p)
    let j : Fin p := ⟨u.val,ZMod.val_lt u⟩
    have hj : (j.val : ZMod p)=u := ZMod.natCast_zmod_val u
    refine ⟨j,?_,?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hj]
      dsimp [u]
      field_simp
      ring
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hj]
      dsimp [u]
      field_simp
      linear_combination hd
  · let u : ZMod p := (A 1 1 : ZMod p)/(A 1 0 : ZMod p)
    let j : Fin p := ⟨u.val,ZMod.val_lt u⟩
    have hj : (j.val : ZMod p)=u := ZMod.natCast_zmod_val u
    refine ⟨j,?_,?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hj]
      dsimp [u]
      field_simp
      linear_combination -hd
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hj]
      dsimp [u]
      field_simp
      ring
def lpsHeckeUpperMatrix (p : ℕ) : Option (Fin p)→Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p:ℤ),0;0,1]
  | some j => !![1,(j.val:ℤ);0,(p:ℤ)]
lemma lpsHeckeUpperMatrix_det (p : ℕ) (j : Option (Fin p)) :
    (lpsHeckeUpperMatrix p j).det=(p:ℤ) := by
  cases j <;> simp [lpsHeckeUpperMatrix,Matrix.det_fin_two]
lemma lpsHeckeFactorFinite (p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin p)
    (h0 : (p:ℤ) ∣ A 0 1-A 0 0*(j.val:ℤ))
    (h1 : (p:ℤ) ∣ A 1 1-A 1 0*(j.val:ℤ)) :
    A= !![A 0 0,(A 0 1-A 0 0*(j.val:ℤ))/(p:ℤ);
      A 1 0,(A 1 1-A 1 0*(j.val:ℤ))/(p:ℤ)] * lpsHeckeUpperMatrix p (some j) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two,
      Int.ediv_mul_cancel h0,Int.ediv_mul_cancel h1]
lemma lpsHeckeFactorInfinity (p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (h0 : (p:ℤ) ∣ A 0 0) (h1 : (p:ℤ) ∣ A 1 0) :
    A= !![A 0 0/(p:ℤ),A 0 1;A 1 0/(p:ℤ),A 1 1] * lpsHeckeUpperMatrix p none := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two,
      Int.ediv_mul_cancel h0,Int.ediv_mul_cancel h1]
lemma lpsHeckeFactorSL (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det=(p:ℤ)) :
    ∃ (j : Option (Fin p)) (δ : SL(2,ℤ)), A=(δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j := by
  have hp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hh (D : Matrix (Fin 2) (Fin 2) ℤ) (j : Option (Fin p))
      (h : A=D*lpsHeckeUpperMatrix p j) : D.det=1 := by
    have hd := congrArg Matrix.det h
    rw [hA,Matrix.det_mul,lpsHeckeUpperMatrix_det] at hd
    apply mul_right_cancel₀ hp
    simpa only [one_mul] using hd.symm
  by_cases h0 : (A 0 0 : ZMod p)=0
  · by_cases h1 : (A 1 0 : ZMod p)=0
    · let D : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0/(p:ℤ),A 0 1;A 1 0/(p:ℤ),A 1 1]
      have he := lpsHeckeFactorInfinity p A
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1)
      exact ⟨none,⟨D,hh D none he⟩,he⟩
    · obtain ⟨j,hj0,hj1⟩ := lpsHeckeFiniteColumn p A hA (Or.inr h1)
      let D : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0,(A 0 1-A 0 0*(j.val:ℤ))/(p:ℤ);
        A 1 0,(A 1 1-A 1 0*(j.val:ℤ))/(p:ℤ)]
      have he := lpsHeckeFactorFinite p A j hj0 hj1
      exact ⟨some j,⟨D,hh D (some j) he⟩,he⟩
  · obtain ⟨j,hj0,hj1⟩ := lpsHeckeFiniteColumn p A hA (Or.inl h0)
    let D : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0,(A 0 1-A 0 0*(j.val:ℤ))/(p:ℤ);
      A 1 0,(A 1 1-A 1 0*(j.val:ℤ))/(p:ℤ)]
    have he := lpsHeckeFactorFinite p A j hj0 hj1
    exact ⟨some j,⟨D,hh D (some j) he⟩,he⟩
lemma lpsHeckeFactorGamma0 (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=(p:ℤ)) (hc : (N:ℤ) ∣ A 1 0) :
    ∃ (j : Option (Fin p)) (δ : SL(2,ℤ)), δ∈CongruenceSubgroup.Gamma0 N ∧
      A=(δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j := by
  obtain ⟨j,δ,he⟩ := lpsHeckeFactorSL p A hA
  refine ⟨j,δ,?_,he⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  have hz : (A 1 0 : ZMod N)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hc
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) he
  cases j with
  | none =>
    simp [Matrix.mul_apply,Fin.sum_univ_two,lpsHeckeUpperMatrix] at h
    have hZ := congrArg (fun x : ℤ => (x : ZMod N)) h
    push_cast at hZ
    rw [hz] at hZ
    exact ((ZMod.isUnit_iff_coprime p N).mpr hNp).mul_left_eq_zero.mp hZ.symm
  | some j =>
    simp [Matrix.mul_apply,Fin.sum_univ_two,lpsHeckeUpperMatrix] at h
    simpa only [h] using hz
lemma lpsHeckeRightFactor (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    ∃ (j : Option (Fin p)) (δ : SL(2,ℤ)), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
        (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j := by
  apply lpsHeckeFactorGamma0 N p hNp
  · rw [Matrix.det_mul,lpsHeckeUpperMatrix_det,γ.det_coe,mul_one]
  · have hc : (N:ℤ) ∣ γ 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
        (CongruenceSubgroup.Gamma0_mem.mp hγ)
    cases i with
    | none => simpa [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] using hc
    | some i =>
      simpa [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] using dvd_mul_of_dvd_right hc (p:ℤ)
noncomputable def lpsHeckeRightIndex (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) : Option (Fin p) :=
  (lpsHeckeRightFactor N p hNp γ hγ i).choose
noncomputable def lpsHeckeUpperGL (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) : GL (Fin 2) R :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((lpsHeckeUpperMatrix p i).map (Int.castRingHom R)) (by
      rw [Int.coe_castRingHom,←Int.cast_det,lpsHeckeUpperMatrix_det]
      exact_mod_cast (Fact.out : p.Prime).ne_zero)
end QEC.Coding.TannerLiftedProduct


