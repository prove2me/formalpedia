-- Prove2me | solution 1 for ArtinL.Abelian.galois_primesOver_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/69b33b1c-6568-5ca2-bfe7-1de64ede54f2

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_galois_primesOver_dictionary

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Pointwise Classical
open IsDedekindDomain
namespace ArtinL
p2m_export "ArtinL" "Abelian.restrictScalars_fixingSubgroupEquiv"
namespace C3
p2m_open "ArtinL"
open scoped Pointwise

section inertia_smul
variable {M R : Type*} [Group M] [Ring R] [MulSemiringAction M R]

theorem mem_inertia_smul_iff (I : Ideal R) (g σ : M) : σ ∈ (g • I).inertia M ↔ g⁻¹ * σ * g ∈ I.inertia M := by
  constructor
  · intro h x
    have := h (g • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul, ← mul_smul,
      ← mul_smul] at this
    rw [Submodule.mem_toAddSubgroup]
    simpa [mul_assoc] using this
  · intro h x
    have := h (g⁻¹ • x)
    rw [Submodule.mem_toAddSubgroup] at this
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, ← mul_smul]
    simpa [mul_smul, mul_assoc] using this

theorem mem_stabilizer_smul_iff (I : Ideal R) (g σ : M) :
    σ ∈ MulAction.stabilizer M (g • I) ↔ g⁻¹ * σ * g ∈ MulAction.stabilizer M I := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]

end inertia_smul

section transfer
variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F]
  (K : IntermediateField ℚ F)

theorem restrictScalars_smul (σ' : F ≃ₐ[↥K] F) (x : 𝓞 F) : σ'.restrictScalars ℚ • x = σ' • x := rfl

theorem mem_inertia_iff_restrictScalars (Q : Ideal (𝓞 F)) (σ' : F ≃ₐ[↥K] F) :
    σ' ∈ Q.inertia (F ≃ₐ[↥K] F) ↔ σ'.restrictScalars ℚ ∈ Q.inertia (F ≃ₐ[ℚ] F) := Iff.rfl

theorem mem_stabilizer_iff_restrictScalars (Q : Ideal (𝓞 F)) (σ' : F ≃ₐ[↥K] F) :
    σ' ∈ MulAction.stabilizer (F ≃ₐ[↥K] F) Q ↔ σ'.restrictScalars ℚ ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q := Iff.rfl

variable [IsGalois ℚ F]

theorem exists_restrictScalars_eq_of_mem (H : Subgroup (F ≃ₐ[ℚ] F)) (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H) :
    ∃ σ' : F ≃ₐ[↥(IntermediateField.fixedField H)] F, σ'.restrictScalars ℚ = σ :=
  ⟨IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)
      ⟨σ, (IntermediateField.fixingSubgroup_fixedField H).symm ▸ hσ⟩,
    ArtinL.Abelian.restrictScalars_fixingSubgroupEquiv _ _⟩

theorem restrictScalars_mem (H : Subgroup (F ≃ₐ[ℚ] F)) (σ' : F ≃ₐ[↥(IntermediateField.fixedField H)] F) :
    σ'.restrictScalars ℚ ∈ H :=
  (IntermediateField.fixingSubgroup_fixedField H).le fun x => σ'.commutes x

end transfer

end ArtinL.C3

namespace ArtinL
p2m_export "ArtinL" "Abelian.restrictScalars_fixingSubgroupEquiv"
namespace C3
p2m_open "ArtinL"
open scoped Pointwise

section frob
variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
  (K : IntermediateField ℚ F) {p : ℕ} (hp : p.Prime)
  (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})]

include hp in

theorem card_int_quot_under : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  have hQu : Q.under ℤ = Ideal.span {(p : ℤ)} := (‹Q.LiesOver (Ideal.span {(p : ℤ)})›.over).symm
  rw [hQu, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem liesOver_of_under_eq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K)) (hv : Q.under (𝓞 ↥K) = v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  rw [← hv, Ideal.under_under]
  exact Ideal.LiesOver.over

include hp in

theorem card_quot_place (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K)) (hv : Q.under (𝓞 ↥K) = v.asIdeal) :
    Nat.card (𝓞 ↥K ⧸ v.asIdeal) = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal := by
  haveI := liesOver_of_under_eq F K (p := p) Q v hv
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_eq_pow_inertiaDeg' _ hp]

include hp in

theorem frob_pow_smul_sub_pow_mem (j : ℕ) (x : 𝓞 F) :
    (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j) • x - x ^ (p ^ j) ∈ Q := by
  have hF : IsArithFrobAt ℤ (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) Q := IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q
  have hstab := hF.mem_stabilizer
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p := card_int_quot_under F hp Q
  have hQ : arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q • Q = Q := MulAction.mem_stabilizer_iff.1 hstab
  have hx : (Ideal.Quotient.mk Q) (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q • x) = (Ideal.Quotient.mk Q) (x ^ p) := by
    have := hF x
    rw [hcard, ← Ideal.Quotient.eq] at this
    exact this
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_smul, pow_succ, pow_mul]
    rw [← Ideal.Quotient.eq] at ih ⊢
    have h1 : (Ideal.Quotient.mk Q) ((arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) • ((arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j) • x)) =
        (Ideal.Quotient.mk Q) ((arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) • (x ^ p ^ j)) := by
      rw [Ideal.Quotient.eq, ← smul_sub]
      have := Ideal.smul_mem_pointwise_smul (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) _ Q ((Ideal.Quotient.eq).1 ih)
      rwa [hQ] at this
    rw [h1, smul_pow', map_pow, hx, ← map_pow, ← pow_mul, ← pow_mul, mul_comm]

include hp in

theorem isArithFrobAt_of_inv_mul_frob_pow_mem (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K)) (hv : Q.under (𝓞 ↥K) = v.asIdeal)
    (σ' : F ≃ₐ[↥K] F)
    (h : (σ'.restrictScalars ℚ)⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈
      Q.inertia (F ≃ₐ[ℚ] F)) :
    IsArithFrobAt (𝓞 ↥K) σ' Q := by
  intro x
  change σ' • x - x ^ Nat.card (𝓞 ↥K ⧸ Q.under (𝓞 ↥K)) ∈ Q
  rw [hv, card_quot_place F K hp Q v hv, ← restrictScalars_smul]
  set ι := (σ'.restrictScalars ℚ)⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal with hι
  have hσ : σ'.restrictScalars ℚ = arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal * ι⁻¹ := by
    rw [hι]; group
  rw [hσ, mul_smul]

  have h1 : ι⁻¹ • x - x ∈ Q := (Q.inertia (F ≃ₐ[ℚ] F)).inv_mem h x
  have hstab := (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q).mem_stabilizer
  have h2 : (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) • (ι⁻¹ • x) -
      (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) • x ∈ Q := by
    rw [← smul_sub]
    have hstabj : arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈
        MulAction.stabilizer (F ≃ₐ[ℚ] F) Q := Subgroup.pow_mem _ hstab _
    have := Ideal.smul_mem_pointwise_smul (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) _ Q h1
    rwa [MulAction.mem_stabilizer_iff.1 hstabj] at this
  have h3 := frob_pow_smul_sub_pow_mem F hp Q ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) x
  have := Q.add_mem h2 h3
  simpa using this

end frob

end ArtinL.C3

namespace ArtinL
p2m_export "ArtinL" "Abelian.restrictScalars_fixingSubgroupEquiv"
namespace Abelian
p2m_export "ArtinL.Abelian" "restrictScalars_fixingSubgroupEquiv"
namespace C5
p2m_open "ArtinL.Abelian ArtinL"

open IsDedekindDomain NumberField Polynomial

variable (K : Type) [Field K] [NumberField K]

noncomputable def charOf (v : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ v.asIdeal)

theorem charOf_prime (v : HeightOneSpectrum (𝓞 K)) : (charOf K v).Prime := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI := Ideal.Quotient.field v.asIdeal
  exact CharP.char_is_prime (𝓞 K ⧸ v.asIdeal) _

theorem natCast_mem_iff (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime) :
    ((p : ℕ) : 𝓞 K) ∈ v.asIdeal ↔ charOf K v = p := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (𝓞 K ⧸ v.asIdeal) (charOf K v)]
  constructor
  · intro h
    exact (Nat.prime_dvd_prime_iff_eq (charOf_prime K v) hp).1 h
  · rintro rfl
    exact dvd_rfl

theorem charOf_mem (v : HeightOneSpectrum (𝓞 K)) : ((charOf K v : ℕ) : 𝓞 K) ∈ v.asIdeal :=
  (natCast_mem_iff K v _ (charOf_prime K v)).2 rfl

private noncomputable def _root_.ArtinL.Abelian.C5.under (v : HeightOneSpectrum (𝓞 K)) : Nat.Primes := ⟨charOf K v, charOf_prime K v⟩

p2m_export "ArtinL.Abelian.C5" "under"
theorem under_eq_iff (v : HeightOneSpectrum (𝓞 K)) (p : Nat.Primes) :
    under K v = p ↔ ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  rw [natCast_mem_iff K v p p.2, under]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem liesOver_of_mem (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI := v.isMaximal
  haveI := v.isPrime
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  haveI : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ v.asIdeal
  rwa [map_natCast]

theorem finite_fibre (p : Nat.Primes) : Finite {v : HeightOneSpectrum (𝓞 K) // under K v = p} := by
  haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 p.2)) (by simpa using p.2.ne_zero)
  have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal)
      ((fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) ⁻¹' ((Ideal.span {((p : ℕ) : ℤ)}).primesOver (𝓞 K))) :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  have hfin : {w : HeightOneSpectrum (𝓞 K) | under K w = p}.Finite :=
    ((IsDedekindDomain.primesOver_finite (Ideal.span {((p : ℕ) : ℤ)}) (𝓞 K)).preimage hinj).subset
      fun w hw => by
        have hw' : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := (under_eq_iff K w p).1 hw
        exact ⟨w.isPrime, liesOver_of_mem K w p p.2 hw'⟩
  exact hfin.to_subtype

theorem natCast_pow_cpow (p f : ℕ) (w : ℂ) : (((p ^ f : ℕ) : ℂ)) ^ w = (((p : ℕ) : ℂ) ^ w) ^ f := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

theorem absNorm_eq (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal := by
  haveI := liesOver_of_mem K v p hp hv
  have h := Ideal.absNorm_eq_pow_inertiaDeg v.asIdeal (p := (p : ℤ)) (Nat.prime_iff_prime_int.1 hp)
  simpa using h

end ArtinL.Abelian.C5

namespace ArtinL
p2m_export "ArtinL" "Abelian.restrictScalars_fixingSubgroupEquiv"
namespace Abelian
p2m_export "ArtinL.Abelian" "restrictScalars_fixingSubgroupEquiv"
namespace C3
p2m_open "ArtinL.Abelian ArtinL"

open IsDedekindDomain NumberField

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
  (H : Subgroup (F ≃ₐ[ℚ] F))

noncomputable def resK : (F ≃ₐ[↥(IntermediateField.fixedField H)] F) →* (F ≃ₐ[ℚ] F) where
  toFun σ := σ.restrictScalars ℚ
  map_one' := rfl
  map_mul' _ _ := rfl

theorem resK_apply (σ : F ≃ₐ[↥(IntermediateField.fixedField H)] F) (x : F) : resK F H σ x = σ x := rfl

theorem mem_H_resK (σ : F ≃ₐ[↥(IntermediateField.fixedField H)] F) : resK F H σ ∈ H :=
  (IntermediateField.fixingSubgroup_fixedField H).le fun x => σ.commutes x

theorem resK_injective : Function.Injective (resK F H) := fun σ τ h =>
  AlgEquiv.ext fun x => by rw [← resK_apply F H σ x, h, resK_apply]

theorem exists_resK_eq (h : F ≃ₐ[ℚ] F) (hh : h ∈ H) : ∃ σ : F ≃ₐ[↥(IntermediateField.fixedField H)] F, resK F H σ = h := by
  have hh' : h ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_fixedField H]; exact hh
  refine ⟨{ h with commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh' x.1 x.2 }, ?_⟩
  apply AlgEquiv.ext
  intro x
  rfl

theorem mem_inertia_iff_resK (Q : Ideal (𝓞 F)) (σ : F ≃ₐ[↥(IntermediateField.fixedField H)] F) :
    σ ∈ Q.inertia (F ≃ₐ[↥(IntermediateField.fixedField H)] F) ↔ resK F H σ ∈ Q.inertia (F ≃ₐ[ℚ] F) :=
  Iff.rfl

theorem resK_smul_ideal (σ : F ≃ₐ[↥(IntermediateField.fixedField H)] F) (Q : Ideal (𝓞 F)) : resK F H σ • Q = σ • Q := rfl

theorem mem_stabilizer_iff_resK (Q : Ideal (𝓞 F)) (σ : F ≃ₐ[↥(IntermediateField.fixedField H)] F) :
    σ ∈ MulAction.stabilizer (F ≃ₐ[↥(IntermediateField.fixedField H)] F) Q ↔
      resK F H σ ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q :=
  Iff.rfl

theorem H_inf_inertia_eq_map (Q : Ideal (𝓞 F)) :
    H ⊓ Q.inertia (F ≃ₐ[ℚ] F) = (Q.inertia (F ≃ₐ[↥(IntermediateField.fixedField H)] F)).map (resK F H) := by
  ext g
  constructor
  · rintro ⟨hg, hg'⟩
    obtain ⟨σ, rfl⟩ := exists_resK_eq F H g hg
    exact ⟨σ, (mem_inertia_iff_resK F H Q σ).2 hg', rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨mem_H_resK F H σ, (mem_inertia_iff_resK F H Q σ).1 hσ⟩

theorem card_H_inf_inertia (Q : Ideal (𝓞 F)) :
    Nat.card ↥(H ⊓ Q.inertia (F ≃ₐ[ℚ] F)) = Nat.card ↥(Q.inertia (F ≃ₐ[↥(IntermediateField.fixedField H)] F)) := by
  rw [H_inf_inertia_eq_map, Subgroup.card_map_of_injective (resK_injective F H)]

theorem H_inf_stabilizer_eq_map (Q : Ideal (𝓞 F)) :
    H ⊓ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q =
      (MulAction.stabilizer (F ≃ₐ[↥(IntermediateField.fixedField H)] F) Q).map (resK F H) := by
  ext g
  constructor
  · rintro ⟨hg, hg'⟩
    obtain ⟨σ, rfl⟩ := exists_resK_eq F H g hg
    exact ⟨σ, (mem_stabilizer_iff_resK F H Q σ).2 hg', rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨mem_H_resK F H σ, (mem_stabilizer_iff_resK F H Q σ).1 hσ⟩

theorem card_H_inf_stabilizer (Q : Ideal (𝓞 F)) :
    Nat.card ↥(H ⊓ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) =
      Nat.card ↥(MulAction.stabilizer (F ≃ₐ[↥(IntermediateField.fixedField H)] F) Q) := by
  rw [H_inf_stabilizer_eq_map, Subgroup.card_map_of_injective (resK_injective F H)]

theorem smul_algebraMap_of_mem (h : F ≃ₐ[ℚ] F) (hh : h ∈ H) (x : 𝓞 ↥(IntermediateField.fixedField H)) :
    h • algebraMap (𝓞 ↥(IntermediateField.fixedField H)) (𝓞 F) x = algebraMap (𝓞 ↥(IntermediateField.fixedField H)) (𝓞 F) x := by
  apply Subtype.ext
  exact (IntermediateField.mem_fixedField_iff H ((x : ↥(IntermediateField.fixedField H)) : F)).1 (x : ↥(IntermediateField.fixedField H)).2 h hh

theorem under_smul_eq_of_mem (h : F ≃ₐ[ℚ] F) (hh : h ∈ H) (Q : Ideal (𝓞 F)) :
    (h • Q).under (𝓞 ↥(IntermediateField.fixedField H)) = Q.under (𝓞 ↥(IntermediateField.fixedField H)) := by
  ext x
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    smul_algebraMap_of_mem F H h⁻¹ (inv_mem hh)]

theorem exists_mem_H_smul_eq (Q Q' : Ideal (𝓞 F)) [Q.IsMaximal] [Q'.IsMaximal]
    (h : Q.under (𝓞 ↥(IntermediateField.fixedField H)) = Q'.under (𝓞 ↥(IntermediateField.fixedField H))) :
    ∃ h : F ≃ₐ[ℚ] F, h ∈ H ∧ Q' = h • Q := by
  haveI : Finite (F ≃ₐ[↥(IntermediateField.fixedField H)] F) := Finite.of_injective (resK F H) (resK_injective F H)
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 ↥(IntermediateField.fixedField H)) (𝓞 F)
    (F ≃ₐ[↥(IntermediateField.fixedField H)] F) Q Q' h
  exact ⟨resK F H g, mem_H_resK F H g, by rw [resK_smul_ideal]; exact hg⟩

theorem exists_smul_eq_of_liesOver {p : ℕ} (hp : p.Prime) (P Q : Ideal (𝓞 F)) [P.IsMaximal] [Q.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] [Q.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ x : F ≃ₐ[ℚ] F, Q = x • P :=
  Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 F) (F ≃ₐ[ℚ] F) P Q
    ((Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)})).symm.trans (Ideal.LiesOver.over (P := Q)))

theorem card_quot_place (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) {p : ℕ} (hp : p.Prime)
    (hv : ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal) :
    Nat.card (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal := by
  haveI : NumberField ↥(IntermediateField.fixedField H) :=
    { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI := ArtinL.Abelian.C5.liesOver_of_mem ↥(IntermediateField.fixedField H) v p hp hv
  have h := Ideal.absNorm_eq_pow_inertiaDeg v.asIdeal (p := (p : ℤ)) (Nat.prime_iff_prime_int.1 hp)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  simpa using h

theorem card_int_quot_under (Q : Ideal (𝓞 F)) {p : ℕ} (hp : p.Prime) [hQ : Q.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← hQ.over, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem isSeparable_residue_int {p : ℕ} (hp : p.Prime) (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})] :
    @Algebra.IsSeparable (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 F ⧸ Q) _ _ _ := by
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  letI := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
  letI := Ideal.Quotient.field Q
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) := Finite.of_equiv (ZMod p) (Int.quotientSpanNatEquivZMod p).symm.toEquiv
  haveI : PerfectField (ℤ ⧸ Ideal.span {(p : ℤ)}) := PerfectField.ofFinite
  haveI : Algebra.IsAlgebraic (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 F ⧸ Q) := Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem isSeparable_residue_place (Q : Ideal (𝓞 F)) [Q.IsMaximal]
    (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) [Q.LiesOver v.asIdeal] :
    @Algebra.IsSeparable (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) (𝓞 F ⧸ Q) _ _ _ := by
  haveI := v.isMaximal
  haveI : NumberField ↥(IntermediateField.fixedField H) :=
    { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  letI := Ideal.Quotient.field v.asIdeal
  letI := Ideal.Quotient.field Q
  haveI : Finite (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  haveI : PerfectField (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) := PerfectField.ofFinite
  haveI : Algebra.IsAlgebraic (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) (𝓞 F ⧸ Q) := Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem inertiaDeg_mul_card_mul_card (Q : Ideal (𝓞 F)) [Q.IsMaximal] {p : ℕ} (hp : p.Prime) [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)))
    (hv : Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) :
    (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal *
        Nat.card ↥(H ⊓ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) * Nat.card ↥(Q.inertia (F ≃ₐ[ℚ] F)) =
      Nat.card ↥(MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) * Nat.card ↥(H ⊓ Q.inertia (F ≃ₐ[ℚ] F)) := by
  haveI := v.isMaximal
  haveI : NumberField ↥(IntermediateField.fixedField H) :=
    { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  haveI hQv : Q.LiesOver v.asIdeal := ⟨hv.symm⟩
  haveI : Finite (F ≃ₐ[↥(IntermediateField.fixedField H)] F) := Finite.of_injective (resK F H) (resK_injective F H)
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  haveI := isSeparable_residue_int F hp Q
  haveI := isSeparable_residue_place F H Q v

  have hI := Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[ℚ] F) (Ideal.span {(p : ℤ)}) Q
  have hD := Ideal.card_stabilizer_eq (G := F ≃ₐ[ℚ] F) (Ideal.span {(p : ℤ)}) Q
  have hIK := Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[↥(IntermediateField.fixedField H)] F) v.asIdeal Q
  have hDK := Ideal.card_stabilizer_eq (G := F ≃ₐ[↥(IntermediateField.fixedField H)] F) v.asIdeal Q
  rw [card_H_inf_stabilizer, card_H_inf_inertia, hI, hD, hIK, hDK]

  haveI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    constructor
    rw [Ideal.LiesOver.over (P := Q) (p := Ideal.span {(p : ℤ)}), ← hv, Ideal.under_under]
  have htower := Ideal.inertiaDeg_algebra_tower (Ideal.span {(p : ℤ)}) v.asIdeal Q
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) Q (F ≃ₐ[ℚ] F),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q (F ≃ₐ[↥(IntermediateField.fixedField H)] F),
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := Ideal.span {(p : ℤ)}) (q := Q),
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := v.asIdeal) (q := Q), htower]
  ring

section calculus
variable {F}
variable (Q : Ideal (𝓞 F))

theorem smul_sub_smul_mem_of_mem_stabilizer (g : F ≃ₐ[ℚ] F) (hg : g ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q)
    {x y : 𝓞 F} (h : x - y ∈ Q) : g • x - g • y ∈ Q := by
  rw [← smul_sub]
  have := Ideal.smul_mem_pointwise_smul g _ Q h
  rwa [MulAction.mem_stabilizer_iff.1 hg] at this

theorem inv_mul_mem_inertia_of_forall (g h : F ≃ₐ[ℚ] F) (hg : g ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q)
    (hgh : ∀ x : 𝓞 F, h • x - g • x ∈ Q) : g⁻¹ * h ∈ Q.inertia (F ≃ₐ[ℚ] F) := by
  intro x
  have h1 := smul_sub_smul_mem_of_mem_stabilizer Q g⁻¹ (inv_mem hg) (hgh x)
  rw [smul_smul, smul_smul, inv_mul_cancel, one_smul] at h1
  exact h1

theorem forall_sub_mem_of_inv_mul_mem_inertia (g h : F ≃ₐ[ℚ] F) (hg : g ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q)
    (h' : g⁻¹ * h ∈ Q.inertia (F ≃ₐ[ℚ] F)) : ∀ x : 𝓞 F, h • x - g • x ∈ Q := by
  intro x
  have h1 : (g⁻¹ * h) • x - x ∈ Q := h' x
  have h2 := smul_sub_smul_mem_of_mem_stabilizer Q g hg h1
  rwa [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul] at h2

theorem pow_smul_sub_pow_mem_of (g : F ≃ₐ[ℚ] F) (hg : g ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) {q : ℕ}
    (hq : ∀ x : 𝓞 F, g • x - x ^ q ∈ Q) (n : ℕ) (x : 𝓞 F) : g ^ n • x - x ^ q ^ n ∈ Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, pow_succ, pow_mul]
    have h1 : g • (g ^ n • x) - g • (x ^ q ^ n) ∈ Q := smul_sub_smul_mem_of_mem_stabilizer Q g hg ih
    have h2 : g • (x ^ q ^ n) - (x ^ q ^ n) ^ q ∈ Q := hq _
    have := Q.add_mem h1 h2
    rw [sub_add_sub_cancel] at this
    exact this

end calculus

theorem dvd_of_pow_sub_one_dvd {p f j : ℕ} (hp : 2 ≤ p) (hf : 0 < f) (h : p ^ f - 1 ∣ p ^ j - 1) : f ∣ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.lt_or_ge j f with hjf | hjf
    ·
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact dvd_zero f
      · exfalso
        have hlt : p ^ j - 1 < p ^ f - 1 := by
          have := Nat.pow_lt_pow_right (by omega : 1 < p) hjf
          have h1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
          omega
        have hpos : 0 < p ^ j - 1 := by
          have := Nat.one_lt_pow hj.ne' (by omega : 1 < p)
          omega
        exact absurd (Nat.le_of_dvd hpos h) (not_le.2 hlt)
    ·
      have hsplit : p ^ j - 1 = p ^ (j - f) * (p ^ f - 1) + (p ^ (j - f) - 1) := by
        have h1 : 1 ≤ p ^ (j - f) := Nat.one_le_pow _ _ (by omega)
        have h2 : 1 ≤ p ^ f := Nat.one_le_pow _ _ (by omega)
        have : p ^ j = p ^ (j - f) * p ^ f := by rw [← pow_add, Nat.sub_add_cancel hjf]
        rw [this, Nat.mul_sub_one]
        have h3 : p ^ (j - f) ≤ p ^ (j - f) * p ^ f := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have hdvd : p ^ f - 1 ∣ p ^ (j - f) - 1 := by
        have h' := h
        rw [hsplit] at h'
        exact (Nat.dvd_add_right (dvd_mul_left _ _)).1 h'
      rcases eq_or_lt_of_le hjf with rfl | hlt
      · exact dvd_rfl
      · have := ih (j - f) (by omega) hdvd
        have : f ∣ j - f + f := dvd_add this dvd_rfl
        rwa [Nat.sub_add_cancel hjf] at this

theorem inv_mul_frob_pow_mem_inertia_of_isArithFrobAt (Q : Ideal (𝓞 F)) [Q.IsMaximal] {p : ℕ} (hp : p.Prime)
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)))
    (hv : Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal)
    (τ : F ≃ₐ[↥(IntermediateField.fixedField H)] F) (hτ : IsArithFrobAt (𝓞 ↥(IntermediateField.fixedField H)) τ Q) :
    (resK F H τ)⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈
      Q.inertia (F ≃ₐ[ℚ] F) := by
  have hstab : resK F H τ ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q := hτ.mem_stabilizer
  apply inv_mul_mem_inertia_of_forall Q _ _ hstab
  intro x
  have h1 := ArtinL.C3.frob_pow_smul_sub_pow_mem F hp Q ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) x
  have h2 : resK F H τ • x - x ^ p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈ Q := by
    have := hτ x
    change τ • x - x ^ Nat.card (𝓞 ↥(IntermediateField.fixedField H) ⧸ Q.under (𝓞 ↥(IntermediateField.fixedField H))) ∈ Q at this
    rwa [hv, ArtinL.C3.card_quot_place F (IntermediateField.fixedField H) hp Q v hv] at this
  have := Q.sub_mem h1 h2
  rwa [sub_sub_sub_cancel_right] at this

theorem inertiaDeg_dvd_of_forall_smul_sub_pow_mem (Q : Ideal (𝓞 F)) [Q.IsMaximal] {p : ℕ} (hp : p.Prime)
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)))
    (hv : Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) (j : ℕ)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H) (hpow : ∀ x : 𝓞 F, σ • x - x ^ p ^ j ∈ Q) :
    (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j := by
  haveI := v.isMaximal
  haveI : NumberField ↥(IntermediateField.fixedField H) :=
    { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Fintype (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) := Fintype.ofFinite _

  have hfix : ∀ y : 𝓞 ↥(IntermediateField.fixedField H),
      (Ideal.Quotient.mk v.asIdeal y) ^ p ^ j = Ideal.Quotient.mk v.asIdeal y := by
    intro y
    rw [← map_pow, eq_comm, Ideal.Quotient.eq, ← hv, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
    have := hpow (algebraMap _ (𝓞 F) y)
    rwa [smul_algebraMap_of_mem F H σ hσ] at this
  have hunits : ∀ u : (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal)ˣ, u ^ (p ^ j - 1) = 1 := by
    intro u
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal)
    have h1 := hfix y
    rw [hy] at h1
    have hj : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
    apply Units.ext
    have : (u : 𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) ^ (p ^ j - 1) * u = u := by
      rw [← pow_succ, Nat.sub_add_cancel hj, h1]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ u.ne_zero (this.trans (one_mul _).symm)
  have hdvd := (FiniteField.forall_pow_eq_one_iff (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) (p ^ j - 1)).1 hunits
  have hcard : Fintype.card (𝓞 ↥(IntermediateField.fixedField H) ⧸ v.asIdeal) = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal := by
    rw [Fintype.card_eq_nat_card, ArtinL.C3.card_quot_place F (IntermediateField.fixedField H) hp Q v hv]
  rw [hcard] at hdvd
  haveI := ArtinL.C3.liesOver_of_under_eq F (IntermediateField.fixedField H) (p := p) Q v hv
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  exact dvd_of_pow_sub_one_dvd hp.two_le (Ideal.inertiaDeg'_pos (Ideal.span {(p : ℤ)}) v.asIdeal) hdvd

theorem exists_mem_H_inv_mul_frob_pow_mem_inertia_iff (Q : Ideal (𝓞 F)) [Q.IsMaximal] {p : ℕ} (hp : p.Prime)
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)))
    (hv : Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) (j : ℕ) :
    (∃ σ : F ≃ₐ[ℚ] F, σ ∈ H ∧ σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j ∈ Q.inertia (F ≃ₐ[ℚ] F)) ↔
      (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j := by
  have hφstab : arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q :=
    (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q).mem_stabilizer
  constructor
  · rintro ⟨σ, hσH, hσ⟩

    have hσstab : σ ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q := by
      have h1 : σ = arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j * (σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j)⁻¹ := by group
      rw [h1]
      exact mul_mem (pow_mem hφstab j) (inv_mem (Ideal.inertia_le_stabilizer Q hσ))
    have hcong := forall_sub_mem_of_inv_mul_mem_inertia Q σ _ hσstab hσ
    refine inertiaDeg_dvd_of_forall_smul_sub_pow_mem F H Q hp v hv j σ hσH fun x => ?_
    have := Q.sub_mem (ArtinL.C3.frob_pow_smul_sub_pow_mem F hp Q j x) (hcong x)
    rwa [sub_sub_sub_cancel_left] at this
  · rintro ⟨m, rfl⟩
    haveI : Finite (F ≃ₐ[↥(IntermediateField.fixedField H)] F) := Finite.of_injective (resK F H) (resK_injective F H)
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      have h := (Ideal.LiesOver.over (P := (⊥ : Ideal (𝓞 F))) (p := Ideal.span {(p : ℤ)}))
      rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int] at h
      exact (show Ideal.span {(p : ℤ)} ≠ ⊥ by simpa using hp.ne_zero) h
    haveI : Finite (𝓞 F ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
    set τ := arithFrobAt (𝓞 ↥(IntermediateField.fixedField H)) (F ≃ₐ[↥(IntermediateField.fixedField H)] F) Q with hτdef
    have hτ : IsArithFrobAt (𝓞 ↥(IntermediateField.fixedField H)) τ Q := IsArithFrobAt.arithFrobAt _ _ Q
    refine ⟨resK F H τ ^ m, pow_mem (mem_H_resK F H τ) m, ?_⟩
    have hstab : resK F H τ ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q := hτ.mem_stabilizer
    apply inv_mul_mem_inertia_of_forall Q _ _ (pow_mem hstab m)
    intro x
    have hq : ∀ x : 𝓞 F, resK F H τ • x - x ^ p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈ Q := by
      intro x
      have := hτ x
      change τ • x - x ^ Nat.card (𝓞 ↥(IntermediateField.fixedField H) ⧸ Q.under (𝓞 ↥(IntermediateField.fixedField H))) ∈ Q at this
      rwa [hv, ArtinL.C3.card_quot_place F (IntermediateField.fixedField H) hp Q v hv] at this
    have h1 := pow_smul_sub_pow_mem_of Q (resK F H τ) hstab hq m x
    have h2 := ArtinL.C3.frob_pow_smul_sub_pow_mem F hp Q ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal * m) x
    rw [← pow_mul] at h1
    have := Q.sub_mem h2 h1
    rwa [sub_sub_sub_cancel_right] at this

end ArtinL.Abelian.C3

theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 F)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal →
          ∃ x : F ≃ₐ[ℚ] F, (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) ∧
    (∀ x y : F ≃ₐ[ℚ] F,
        (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) =
            (y • P).under (𝓞 ↥(IntermediateField.fixedField H)) ↔
          ∃ h ∈ H, ∃ d ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) P, y = h * x * d) ∧
    (∀ (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})]
        (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))),
        Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal →
          (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal *
              Nat.card ↥(H ⊓ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) * Nat.card ↥(Q.inertia (F ≃ₐ[ℚ] F)) =
            Nat.card ↥(MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) * Nat.card ↥(H ⊓ Q.inertia (F ≃ₐ[ℚ] F)) ∧
          ∀ j : ℕ, (∃ σ : F ≃ₐ[ℚ] F, σ ∈ H ∧ σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j ∈ Q.inertia (F ≃ₐ[ℚ] F)) ↔
            (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j) ∧
    (∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal →
          0 < (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) := by
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  haveI : NumberField ↥(IntermediateField.fixedField H) :=
    { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

  have hmaxsmul : ∀ (x : F ≃ₐ[ℚ] F) (Q : Ideal (𝓞 F)) [Q.IsMaximal], (x • Q).IsMaximal := by
    intro x Q hQ
    rw [Ideal.pointwise_smul_def]
    exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv (F ≃ₐ[ℚ] F) (𝓞 F) x)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    obtain ⟨Q, hQmax, hQv⟩ := LanglandsTunnell.P2.Artin.exists_prime_over ↥(IntermediateField.fixedField H) F v
    haveI := hQmax
    haveI := ArtinL.Abelian.C5.liesOver_of_mem ↥(IntermediateField.fixedField H) v p hp hv
    haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
      constructor
      rw [← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField H)) Q, hQv]
      exact Ideal.LiesOver.over
    obtain ⟨x, rfl⟩ := ArtinL.Abelian.C3.exists_smul_eq_of_liesOver F hp P Q
    exact ⟨x, hQv⟩
  ·
    intro x y
    constructor
    · intro hxy
      haveI := hmaxsmul x P
      haveI := hmaxsmul y P
      obtain ⟨h, hh, hy⟩ := ArtinL.Abelian.C3.exists_mem_H_smul_eq F H (x • P) (y • P) hxy
      refine ⟨h, hh, (h * x)⁻¹ * y, ?_, by group⟩
      rw [MulAction.mem_stabilizer_iff, mul_smul, hy, smul_smul, smul_smul, show (h * x)⁻¹ * h * x = 1 by group, one_smul]
    · rintro ⟨h, hh, d, hd, rfl⟩
      rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 hd, ArtinL.Abelian.C3.under_smul_eq_of_mem F H h hh]
  ·
    intro Q _ _ v hv
    exact ⟨ArtinL.Abelian.C3.inertiaDeg_mul_card_mul_card F H Q hp v hv,
      ArtinL.Abelian.C3.exists_mem_H_inv_mul_frob_pow_mem_inertia_iff F H Q hp v hv⟩
  ·
    intro v hv
    haveI := ArtinL.Abelian.C5.liesOver_of_mem ↥(IntermediateField.fixedField H) v p hp hv
    exact Ideal.inertiaDeg'_pos (Ideal.span {(p : ℤ)}) v.asIdeal

end S_ArtinL_Abelian_galois_primesOver_dictionary
end P2MW
export P2MW.S_ArtinL_Abelian_galois_primesOver_dictionary (solution)
