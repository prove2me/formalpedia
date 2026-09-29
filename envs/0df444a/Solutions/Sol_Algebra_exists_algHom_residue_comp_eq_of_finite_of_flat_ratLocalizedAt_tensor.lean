-- Prove2me | solution 1 for Algebra.exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bf2f17fa-751b-5f1a-98e8-ccdbbe8af497

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

universe u

namespace TWOC2DEngine

open Polynomial TensorProduct

def algHomInt {R T : Type u} [Ring R] [Ring T] [Algebra ℤ R] [Algebra ℤ T] (f : R →+* T) :
    R →ₐ[ℤ] T :=
  { f with commutes' := fun r => by rw [eq_intCast, eq_intCast]; exact map_intCast f r }

@[scoped simp] theorem algHomInt_apply {R T : Type u} [Ring R] [Ring T] [Algebra ℤ R] [Algebra ℤ T]
    (f : R →+* T) (x : R) : algHomInt f x = f x := rfl

section RatLoc

variable {L : Type*} [Field L] [CharZero L] (B : ValuationSubring L) {ℓ : ℕ}

theorem ratCast_mem_of_mem_ratLocalizedAt (hℓ : ℓ.Prime) (hB : B.LiesOverPrime ℓ)
    (x : ℚ) (hx : x ∈ GaloisRep.ratLocalizedAt ℓ) : (x : L) ∈ B := by
  have hcop : x.den.Coprime ℓ := hx
  have hndvd : ¬ (ℓ : ℤ) ∣ (x.den : ℤ) := by
    intro h
    have h' : ℓ ∣ x.den := Int.natCast_dvd_natCast.mp h
    exact hℓ.one_lt.ne' ((Nat.coprime_comm.mp hcop).eq_one_of_dvd h')
  obtain ⟨w, hw⟩ := (ValuationSubring.intCast_isUnit_of_not_dvd hℓ hB hndvd).exists_right_inv
  have hwL : ((x.den : ℤ) : L) * (w : L) = 1 := by
    have h := congrArg (fun z : ↥B => (z : L)) hw
    simpa using h
  have hden : (x.den : L) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have key : (x : L) = ((x.num : ℤ) : L) * (w : L) := by
    have h1 : (x : L) * (x.den : L) = ((x.num : ℤ) : L) := by
      rw [Rat.cast_def, div_mul_cancel₀ _ hden]
    calc (x : L) = (x : L) * (((x.den : ℤ) : L) * (w : L)) := by rw [hwL, mul_one]
      _ = ((x : L) * (x.den : L)) * (w : L) := by rw [Int.cast_natCast, mul_assoc]
      _ = ((x.num : ℤ) : L) * (w : L) := by rw [h1]
  rw [key]
  exact mul_mem (intCast_mem B x.num) w.2

noncomputable def ratLocToPlace (hℓ : ℓ.Prime) (hB : B.LiesOverPrime ℓ) :
    ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥B :=
  ((Rat.castHom L).comp (GaloisRep.ratLocalizedAt ℓ).subtype).codRestrict B
    (fun x => ratCast_mem_of_mem_ratLocalizedAt B hℓ hB (x : ℚ) x.2)

theorem moduleFinite_baseChange_of_ratLocalizedAt (hℓ : ℓ.Prime) (hB : B.LiesOverPrime ℓ)
    (H : Type*) [CommRing H]
    (hff : Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ) (↥(GaloisRep.ratLocalizedAt ℓ) ⊗[ℤ] H)) :
    Module.Finite ↥B (↥B ⊗[ℤ] H) := by
  letI : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥B := (ratLocToPlace B hℓ hB).toAlgebra
  haveI : Module.Finite ↥B
      (↥B ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] (↥(GaloisRep.ratLocalizedAt ℓ) ⊗[ℤ] H)) :=
    inferInstance
  exact Module.Finite.equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ↥(GaloisRep.ratLocalizedAt ℓ) ↥B ↥B H)

end RatLoc

section Flat

variable {L : Type*} [Field L] (B : ValuationSubring L) (H : Type*) [CommRing H]

theorem algebraMap_mul_eq_rTensor (b : ↥B) (x : ↥B ⊗[ℤ] H) :
    algebraMap ↥B (↥B ⊗[ℤ] H) b * x = (LinearMap.mulLeft ℤ b).rTensor H x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero]
  | tmul a h =>
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.rTensor_tmul,
        LinearMap.mulLeft_apply]
  | add x y hx hy => rw [mul_add, map_add, hx, hy]

variable [Module.Flat ℤ H]

theorem algebraMap_mem_nonZeroDivisors {b : ↥B} (hb : b ≠ 0) :
    algebraMap ↥B (↥B ⊗[ℤ] H) b ∈ nonZeroDivisors (↥B ⊗[ℤ] H) := by
  have hinj : Function.Injective ((LinearMap.mulLeft ℤ b).rTensor H) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (mul_right_injective₀ hb)
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx => ?_
  rw [mul_comm, algebraMap_mul_eq_rTensor] at hx
  exact hinj (hx.trans (map_zero _).symm)

end Flat

section Surj

variable {L : Type*} [Field L] [IsAlgClosed L] (B : ValuationSubring L)
  {D : Type*} [CommRing D] [IsDomain D] (i : ↥B →+* D)

theorem exists_apply_eq_of_monic_of_eval₂_eq_zero :
    ∀ (n : ℕ) (f : (↥B)[X]), f.Monic → f.natDegree = n → ∀ c : D, f.eval₂ i c = 0 →
      ∃ b : ↥B, i b = c := by
  have hinjBL : Function.Injective (algebraMap ↥B L) := IsFractionRing.injective ↥B L
  intro n
  induction n with
  | zero =>
      intro f hf hn c hc
      have h1 : f = 1 := hf.natDegree_eq_zero.mp hn
      rw [h1, eval₂_one] at hc
      exact absurd hc one_ne_zero
  | succ n ih =>
      intro f hf hn c hc

      have hdeg : (f.map (algebraMap ↥B L)).degree ≠ 0 := by
        rw [hf.degree_map, degree_eq_natDegree hf.ne_zero, hn]
        exact_mod_cast Nat.succ_ne_zero n
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg

      have hint : IsIntegral ↥B r := ⟨f, hf, by rwa [IsRoot.def, eval_map] at hr⟩
      obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint

      have hfb : f.IsRoot b := by
        rw [IsRoot.def]
        apply hinjBL
        rw [map_zero, ← eval₂_at_apply, hb, ← eval_map]
        exact hr

      have hfac : (X - C b) * (f /ₘ (X - C b)) = f := mul_divByMonic_eq_iff_isRoot.mpr hfb
      set g := f /ₘ (X - C b) with hg
      have hgm : g.Monic := (monic_X_sub_C b).of_mul_monic_left (by rw [hfac]; exact hf)
      have hgn : g.natDegree = n := by
        have h := (monic_X_sub_C b).natDegree_mul hgm
        rw [hfac, hn, natDegree_X_sub_C] at h
        omega
      have hc' : (X - C b).eval₂ i c * g.eval₂ i c = 0 := by rw [← eval₂_mul, hfac, hc]
      rcases mul_eq_zero.mp hc' with h0 | h0
      · refine ⟨b, ?_⟩
        rw [eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero] at h0
        exact h0.symm
      · exact ih g hgm hgn c h0

theorem surjective_of_isIntegral (hi : i.IsIntegral) : Function.Surjective i := fun c => by
  obtain ⟨f, hf, hfc⟩ := hi c
  exact exists_apply_eq_of_monic_of_eval₂_eq_zero B i f.natDegree f hf rfl c hfc

end Surj

section Lift

variable {L : Type*} [Field L] (B : ValuationSubring L)
  {S' : Type*} [CommRing S'] (i : ↥B →+* S')

theorem mk_comp_injective_of_mem_minimalPrimes
    (hnzd : ∀ b : ↥B, b ≠ 0 → i b ∈ nonZeroDivisors S')
    {𝔮 : Ideal S'} (h𝔮 : 𝔮 ∈ minimalPrimes S') :
    Function.Injective ((Ideal.Quotient.mk 𝔮).comp i) := by
  intro b₁ b₂ h
  by_contra hne
  change Ideal.Quotient.mk 𝔮 (i b₁) = Ideal.Quotient.mk 𝔮 (i b₂) at h
  have hmem : i b₁ - i b₂ ∈ 𝔮 := Ideal.Quotient.eq.mp h
  rw [← map_sub] at hmem
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔮) hmem
    (hnzd _ (sub_ne_zero.mpr hne))

variable [IsAlgClosed L]

theorem mk_comp_bijective_of_mem_minimalPrimes (hint : i.IsIntegral)
    (hnzd : ∀ b : ↥B, b ≠ 0 → i b ∈ nonZeroDivisors S')
    {𝔮 : Ideal S'} (h𝔮 : 𝔮 ∈ minimalPrimes S') :
    Function.Bijective ((Ideal.Quotient.mk 𝔮).comp i) := by
  haveI : 𝔮.IsPrime := h𝔮.1.1
  exact ⟨mk_comp_injective_of_mem_minimalPrimes B i hnzd h𝔮,
    surjective_of_isIntegral B ((Ideal.Quotient.mk 𝔮).comp i)
      (RingHom.IsIntegral.trans _ _ hint
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective))⟩

theorem exists_ringHom_forall_sub_mem (hint : i.IsIntegral)
    (hnzd : ∀ b : ↥B, b ≠ 0 → i b ∈ nonZeroDivisors S')
    (𝔪₀ : Ideal S') [𝔪₀.IsPrime] :
    ∃ lam : S' →+* ↥B, (∀ b : ↥B, lam (i b) = b) ∧ ∀ s : S', s - i (lam s) ∈ 𝔪₀ := by
  obtain ⟨𝔮, h𝔮, hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S') ≤ 𝔪₀)
  haveI : 𝔮.IsPrime := h𝔮.1.1
  set e := RingEquiv.ofBijective _ (mk_comp_bijective_of_mem_minimalPrimes B i hint hnzd h𝔮)
    with he
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔮), fun b => ?_, fun s => hle ?_⟩
  · show e.symm (e b) = b
    exact e.symm_apply_apply b
  · apply Ideal.Quotient.eq.mp
    show Ideal.Quotient.mk 𝔮 s = e (e.symm (Ideal.Quotient.mk 𝔮 s))
    exact (e.apply_symm_apply _).symm

theorem exists_ringHom_forall_apply_eq (hint : i.IsIntegral)
    (hnzd : ∀ b : ↥B, b ≠ 0 → i b ∈ nonZeroDivisors S')
    {K : Type*} [CommRing K] [IsDomain K] (ψ : S' →+* K) :
    ∃ lam : S' →+* ↥B, (∀ b : ↥B, lam (i b) = b) ∧ ∀ s : S', ψ s = ψ (i (lam s)) := by
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨lam, h1, h2⟩ := exists_ringHom_forall_sub_mem B i hint hnzd (RingHom.ker ψ)
  refine ⟨lam, h1, fun s => ?_⟩
  have h := h2 s
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
  exact h

end Lift

section Tensor

variable {L : Type*} [Field L] [IsAlgClosed L] (B : ValuationSubring L)
  (H : Type*) [CommRing H] [Module.Flat ℤ H]

theorem exists_ringHom_forall_apply_algebraMap_eq (hfin : Module.Finite ↥B (↥B ⊗[ℤ] H))
    {K : Type*} [CommRing K] [IsDomain K] (ψ : (↥B ⊗[ℤ] H) →+* K) :
    ∃ lam : (↥B ⊗[ℤ] H) →+* ↥B, (∀ b : ↥B, lam (algebraMap ↥B (↥B ⊗[ℤ] H) b) = b) ∧
      ∀ s : ↥B ⊗[ℤ] H, ψ s = ψ (algebraMap ↥B (↥B ⊗[ℤ] H) (lam s)) := by
  haveI : Module.Finite ↥B (↥B ⊗[ℤ] H) := hfin
  exact exists_ringHom_forall_apply_eq B (algebraMap ↥B (↥B ⊗[ℤ] H))
    (fun x => Algebra.IsIntegral.isIntegral (R := ↥B) x)
    (fun b hb => algebraMap_mem_nonZeroDivisors B H hb) ψ

theorem exists_ringHom_forall_sub_algebraMap_mem (hfin : Module.Finite ↥B (↥B ⊗[ℤ] H))
    (𝔪₀ : Ideal (↥B ⊗[ℤ] H)) [𝔪₀.IsPrime] :
    ∃ lam : (↥B ⊗[ℤ] H) →+* ↥B, (∀ b : ↥B, lam (algebraMap ↥B (↥B ⊗[ℤ] H) b) = b) ∧
      ∀ s : ↥B ⊗[ℤ] H, s - algebraMap ↥B (↥B ⊗[ℤ] H) (lam s) ∈ 𝔪₀ := by
  haveI : Module.Finite ↥B (↥B ⊗[ℤ] H) := hfin
  exact exists_ringHom_forall_sub_mem B (algebraMap ↥B (↥B ⊗[ℤ] H))
    (fun x => Algebra.IsIntegral.isIntegral (R := ↥B) x)
    (fun b hb => algebraMap_mem_nonZeroDivisors B H hb) 𝔪₀

end Tensor

section Engine

variable {L : Type} [Field L] (B : ValuationSubring L)
variable (H : Type) [CommRing H]

noncomputable def chiTilde (χ : H →+* IsLocalRing.ResidueField ↥B) :
    (↥B ⊗[ℤ] H) →ₐ[ℤ] IsLocalRing.ResidueField ↥B :=
  Algebra.TensorProduct.lift (algHomInt (IsLocalRing.residue ↥B)) (algHomInt χ)
    (fun _ _ => Commute.all _ _)

@[scoped simp] theorem chiTilde_one_tmul (χ : H →+* IsLocalRing.ResidueField ↥B) (h : H) :
    chiTilde B H χ ((1 : ↥B) ⊗ₜ[ℤ] h) = χ h := by
  unfold chiTilde
  rw [Algebra.TensorProduct.lift_tmul, algHomInt_apply, algHomInt_apply, map_one, one_mul]

theorem chiTilde_algebraMap (χ : H →+* IsLocalRing.ResidueField ↥B) (b : ↥B) :
    chiTilde B H χ (algebraMap ↥B (↥B ⊗[ℤ] H) b) = IsLocalRing.residue ↥B b := by
  have h1 : algebraMap ↥B (↥B ⊗[ℤ] H) b = b ⊗ₜ[ℤ] (1 : H) :=
    Algebra.TensorProduct.algebraMap_apply b
  rw [h1]
  unfold chiTilde
  rw [Algebra.TensorProduct.lift_tmul, algHomInt_apply, algHomInt_apply, map_one, mul_one]

theorem lift_residue_of_supply
    (supply : ∀ {K : Type} [CommRing K] [IsDomain K] (ψ : (↥B ⊗[ℤ] H) →+* K),
      ∃ lam : (↥B ⊗[ℤ] H) →+* ↥B,
        (∀ b : ↥B, lam (algebraMap ↥B (↥B ⊗[ℤ] H) b) = b) ∧
        ∀ s : ↥B ⊗[ℤ] H, ψ s = ψ (algebraMap ↥B (↥B ⊗[ℤ] H) (lam s)))
    (χ : H →+* IsLocalRing.ResidueField ↥B) :
    ∃ φ : H →+* ↥B, ∀ h : H, χ h = IsLocalRing.residue ↥B (φ h) := by
  obtain ⟨lam, -, hlam⟩ := supply (chiTilde B H χ).toRingHom
  refine ⟨lam.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ↥B) (B := H)).toRingHom,
    fun h => ?_⟩
  have h7 := hlam ((1 : ↥B) ⊗ₜ[ℤ] h)
  have h7' : chiTilde B H χ ((1 : ↥B) ⊗ₜ[ℤ] h)
      = chiTilde B H χ (algebraMap ↥B (↥B ⊗[ℤ] H) (lam ((1 : ↥B) ⊗ₜ[ℤ] h))) := h7
  rw [chiTilde_one_tmul, chiTilde_algebraMap] at h7'
  have h8 : (lam.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ↥B) (B := H)).toRingHom) h
      = lam ((1 : ↥B) ⊗ₜ[ℤ] h) := rfl
  rw [h8]
  exact h7'

end Engine

section Dock

variable {L : Type} [Field L] [IsAlgClosed L] (B : ValuationSubring L)
  (H : Type) [CommRing H] [Module.Flat ℤ H]

private theorem supply_adapter (hfin : Module.Finite ↥B (↥B ⊗[ℤ] H))
    {K : Type} [CommRing K] [IsDomain K] (ψ : (↥B ⊗[ℤ] H) →+* K) :
    ∃ lam : (↥B ⊗[ℤ] H) →+* ↥B, (∀ b : ↥B, lam (algebraMap ↥B (↥B ⊗[ℤ] H) b) = b) ∧
      ∀ s : ↥B ⊗[ℤ] H, ψ s = ψ (algebraMap ↥B (↥B ⊗[ℤ] H) (lam s)) :=
  exists_ringHom_forall_apply_algebraMap_eq B H hfin ψ

theorem lift_residue_of_flat_of_finite (hfin : Module.Finite ↥B (↥B ⊗[ℤ] H))
    (χ : H →+* IsLocalRing.ResidueField ↥B) :
    ∃ φ : H →+* ↥B, ∀ h : H, χ h = IsLocalRing.residue ↥B (φ h) :=
  lift_residue_of_supply B H (supply_adapter B H hfin) χ

end Dock

end TWOC2DEngine
p2m_reactivate "P2MW.S_Algebra_exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor.TWOC2DEngine"

end
p2m_reactivate "P2MW.S_Algebra_exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor.TWOC2DEngine"

theorem solution
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (H : Type) [CommRing H] [Algebra ℤ H]
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H))
    (hflat : Module.Flat ℤ H)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime ℓ)
    (χ : H →ₐ[ℤ] IsLocalRing.ResidueField ↥B) :
    ∃ φ : H →ₐ[ℤ] ↥B, ∀ h : H, χ h = IsLocalRing.residue ↥B (φ h) := by

  have hmod : (Algebra.toModule : Module ℤ H) = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  try rw [hmod] at hfin
  try rw [hmod] at hflat
  haveI := hflat
  have hfin' : Module.Finite ↥B (↥B ⊗[ℤ] H) :=
    TWOC2DEngine.moduleFinite_baseChange_of_ratLocalizedAt B hℓ hB H hfin
  obtain ⟨φ', hφ'⟩ := TWOC2DEngine.lift_residue_of_flat_of_finite B H hfin'
    (χ : H →+* IsLocalRing.ResidueField ↥B)
  exact ⟨TWOC2DEngine.algHomInt φ', hφ'⟩

end S_Algebra_exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor
end P2MW
export P2MW.S_Algebra_exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor (solution)
