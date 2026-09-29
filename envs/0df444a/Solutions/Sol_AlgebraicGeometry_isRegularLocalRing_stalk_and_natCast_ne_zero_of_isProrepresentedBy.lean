-- Prove2me | solution 1 for AlgebraicGeometry.isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6001b8c6-b07a-512b-9f91-162f6003afb1

import Mathlib
import Theorems.Thm_IsLocalRing_exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq
import Theorems.Thm_AlgebraicGeometry_finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open IsLocalRing

namespace P2M
namespace ProrepRegular

def ProRep (S Onr R : Type) [CommRing S] [CommRing Onr] [IsLocalRing Onr] [CommRing R] [Algebra Onr R]
    (xbar : S →+* ResidueField Onr) (resR : R →+* ResidueField Onr) (φ : S →+* R) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
      (resA : A →+* ResidueField Onr), Function.Surjective resA →
      resA.comp (algebraMap Onr A) = residue Onr →
    ∀ ψ : S →+* A, resA.comp ψ = xbar →
      ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧ χ.toRingHom.comp φ = ψ

section General

theorem isLocalRing_quotient {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R) :
    IsLocalRing (R ⧸ I) := by
  have hne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hI))
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

theorem isArtinianRing_quotient {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ maximalIdeal R) (hI2 : maximalIdeal R ^ 2 ≤ I) : IsArtinianRing (R ⧸ I) := by
  haveI := isLocalRing_quotient hI
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨inferInstance, Ring.krullDimLE_zero_iff.mpr fun P hP => ?_⟩

  have hle : (maximalIdeal R).map (Ideal.Quotient.mk I) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have h2 : Ideal.Quotient.mk I (r * r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hI2 (by simpa [pow_two] using Ideal.mul_mem_mul hr hr))
    have : (Ideal.Quotient.mk I r) ^ 2 ∈ P := by
      rw [pow_two, ← map_mul, h2]; exact P.zero_mem
    exact hP.mem_of_pow_mem 2 this

  have hne : (maximalIdeal R).map (Ideal.Quotient.mk I) ≠ ⊤ := by
    intro htop
    have h := congrArg (Ideal.comap (Ideal.Quotient.mk I)) htop
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top] at h
    have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := Ideal.mk_ker
    rw [hker, sup_eq_left.mpr hI] at h
    exact (maximalIdeal.isMaximal R).ne_top h
  have hmax : ((maximalIdeal R).map (Ideal.Quotient.mk I)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      (maximalIdeal.isMaximal R)).resolve_left hne
  exact hmax.eq_of_le hP.ne_top hle ▸ hmax

theorem add_pow_of_sq_eq_zero {A : Type*} [CommRing A] (x δ : A) (hδ : δ * δ = 0) (n : ℕ) :
    (x + δ) ^ n = x ^ n + n * x ^ (n - 1) * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, Nat.cast_succ]
    have : (n : A) * x ^ (n - 1) * δ * δ = 0 := by rw [mul_assoc, hδ, mul_zero]
    rw [this, add_zero]
    rcases n with _ | n
    · simp
    · simp only [Nat.cast_succ, add_tsub_cancel_right]
      ring

theorem charP_residueField {S : Type*} [CommRing S] [IsLocalRing S] {q : ℕ} [hq : Fact q.Prime]
    (h : ((q : ℕ) : S) ∈ maximalIdeal S) : CharP (ResidueField S) q :=
  (CharP.charP_iff_prime_eq_zero hq.out).mpr (by
    rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h)

theorem exists_sub_pow_mem {S : Type*} [CommRing S] [IsLocalRing S] {q : ℕ} [hq : Fact q.Prime]
    [Finite (ResidueField S)] [CharP (ResidueField S) q] (s : S) :
    ∃ t : S, s - t ^ q ∈ maximalIdeal S := by
  have hinj : Function.Injective (frobenius (ResidueField S) q) := frobenius_inj _ _
  have hsurj : Function.Surjective (frobenius (ResidueField S) q) := Finite.surjective_of_injective hinj
  obtain ⟨u, hu⟩ := hsurj (residue S s)
  obtain ⟨t, rfl⟩ := residue_surjective u
  refine ⟨t, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, map_pow, ← hu, frobenius_def, sub_self]

end General

section Core

variable {q : ℕ} [hq : Fact q.Prime]
variable {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
variable {Onr : Type} [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
variable {R : Type} [CommRing R] [IsRegularLocalRing R] [Algebra Onr R]
variable (xbar : S →+* ResidueField Onr) (resR : R →+* ResidueField Onr) (φ : S →+* R)

theorem maximalIdeal_Onr_eq (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    maximalIdeal Onr = Ideal.span {((q : ℕ) : Onr)} := by
  have h : algebraMap ℤ_[q] Onr (q : ℤ_[q]) = ((q : ℕ) : Onr) := map_natCast _ _
  rw [← h]; exact (IsLocalRing.eq_maximalIdeal hOnr_max).symm

theorem natCast_mem_maximalIdeal_Onr (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : Onr) ∈ maximalIdeal Onr := by
  rw [maximalIdeal_Onr_eq hOnr_max]; exact Ideal.mem_span_singleton_self _

theorem charP_k (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    CharP (ResidueField Onr) q :=
  charP_residueField (natCast_mem_maximalIdeal_Onr hOnr_max)

theorem natCast_mem_maximalIdeal_S [CharP (ResidueField Onr) q] (hxbar : RingHom.ker xbar = maximalIdeal S) :
    ((q : ℕ) : S) ∈ maximalIdeal S := by
  rw [← hxbar, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

theorem resR_surjective (hresR : resR.comp (algebraMap Onr R) = residue Onr) : Function.Surjective resR := by
  intro u
  obtain ⟨o, rfl⟩ := residue_surjective u
  exact ⟨algebraMap Onr R o, by rw [← RingHom.comp_apply, hresR]⟩

theorem ker_resR (hresR : resR.comp (algebraMap Onr R) = residue Onr) : RingHom.ker resR = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resR (resR_surjective resR hresR))

theorem mem_maximalIdeal_R_iff (hresR : resR.comp (algebraMap Onr R) = residue Onr) (r : R) :
    r ∈ maximalIdeal R ↔ resR r = 0 := by
  rw [← ker_resR resR hresR, RingHom.mem_ker]

theorem map_le (hxbar : RingHom.ker xbar = maximalIdeal S)
    (hresR : resR.comp (algebraMap Onr R) = residue Onr) (hφ : resR.comp φ = xbar) :
    (maximalIdeal S).map φ ≤ maximalIdeal R := by
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  rw [Ideal.mem_comap, mem_maximalIdeal_R_iff resR hresR, ← RingHom.comp_apply, hφ, ← RingHom.mem_ker, hxbar]
  exact hs

theorem natCast_mem_maximalIdeal_R [CharP (ResidueField Onr) q]
    (hresR : resR.comp (algebraMap Onr R) = residue Onr) : ((q : ℕ) : R) ∈ maximalIdeal R := by
  rw [mem_maximalIdeal_R_iff resR hresR, map_natCast, CharP.cast_eq_zero]

theorem maximalIdeal_eq_map [Finite (ResidueField S)]
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    (hxbar : RingHom.ker xbar = maximalIdeal S)
    (hresR : resR.comp (algebraMap Onr R) = residue Onr) (hφ : resR.comp φ = xbar)
    (huniv : ProRep S Onr R xbar resR φ) :
    maximalIdeal R = (maximalIdeal S).map φ := by
  classical
  haveI : CharP (ResidueField Onr) q := charP_k hOnr_max
  have hqS : ((q : ℕ) : S) ∈ maximalIdeal S := natCast_mem_maximalIdeal_S xbar hxbar
  haveI : CharP (ResidueField S) q := charP_residueField hqS
  set 𝔪 := maximalIdeal R with h𝔪
  set N : Ideal R := (maximalIdeal S).map φ with hN
  have hNle : N ≤ 𝔪 := map_le xbar resR φ hxbar hresR hφ

  set I : Ideal R := N ⊔ 𝔪 ^ 2 with hI
  have hIle : I ≤ 𝔪 := sup_le hNle (Ideal.pow_le_self two_ne_zero)
  have hI2 : 𝔪 ^ 2 ≤ I := le_sup_right
  haveI hAloc : IsLocalRing (R ⧸ I) := isLocalRing_quotient hIle
  haveI hAart : IsArtinianRing (R ⧸ I) := isArtinianRing_quotient hIle hI2

  have hIker : ∀ a ∈ I, resR a = 0 := fun a ha => (mem_maximalIdeal_R_iff resR hresR a).mp (hIle ha)
  set resA : R ⧸ I →+* ResidueField Onr := Ideal.Quotient.lift I resR hIker with hresA
  have hresA_mk : ∀ r, resA (Ideal.Quotient.mk I r) = resR r := fun r => Ideal.Quotient.lift_mk I resR hIker
  have hresA_surj : Function.Surjective resA := by
    intro u; obtain ⟨r, rfl⟩ := resR_surjective resR hresR u; exact ⟨Ideal.Quotient.mk I r, hresA_mk r⟩
  have hresA_comp : resA.comp (algebraMap Onr (R ⧸ I)) = residue Onr := by
    ext o
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply Onr R (R ⧸ I), Ideal.Quotient.algebraMap_eq, hresA_mk,
      ← RingHom.comp_apply, hresR]

  have hqR' : ((q : ℕ) : R) = φ ((q : ℕ) : S) := (map_natCast φ q).symm
  have hqI : ((q : ℕ) : R) ∈ I := le_sup_left (α := Ideal R) (hqR' ▸ Ideal.mem_map_of_mem φ hqS)
  have hqA : ((q : ℕ) : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hqI

  have hσker : ∀ o ∈ maximalIdeal Onr, algebraMap Onr (R ⧸ I) o = 0 := by
    intro o ho
    rw [maximalIdeal_Onr_eq hOnr_max, Ideal.mem_span_singleton] at ho
    obtain ⟨c, rfl⟩ := ho
    rw [map_mul, map_natCast, hqA, zero_mul]
  set σ : ResidueField Onr →+* R ⧸ I := Ideal.Quotient.lift (maximalIdeal Onr) (algebraMap Onr (R ⧸ I)) hσker
    with hσ
  have hσ_res : ∀ o, σ (residue Onr o) = algebraMap Onr (R ⧸ I) o := fun o =>
    Ideal.Quotient.lift_mk (maximalIdeal Onr) (algebraMap Onr (R ⧸ I)) hσker
  have hresA_σ : ∀ u, resA (σ u) = u := by
    intro u; obtain ⟨o, rfl⟩ := residue_surjective u
    rw [hσ_res, ← RingHom.comp_apply, hresA_comp]

  let χ₁ : R →ₐ[Onr] R ⧸ I := Ideal.Quotient.mkₐ Onr I
  let χ₂ : R →ₐ[Onr] R ⧸ I :=
    { σ.comp resR with
      commutes' := fun o => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
          RingHom.coe_comp, Function.comp_apply]
        rw [← RingHom.comp_apply resR, hresR, hσ_res] }
  have hχ₁ : ∀ r, χ₁ r = Ideal.Quotient.mk I r := fun r => rfl
  have hχ₂ : ∀ r, χ₂ r = σ (resR r) := fun r => rfl

  set ψ : S →+* R ⧸ I := (Ideal.Quotient.mk I).comp φ with hψ
  have hψ_cent : resA.comp ψ = xbar := by
    ext s; rw [RingHom.comp_apply, hψ, RingHom.comp_apply, hresA_mk, ← RingHom.comp_apply, hφ]

  have hψ_m : ∀ s ∈ maximalIdeal S, ψ s = 0 := fun s hs => by
    rw [hψ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact le_sup_left (α := Ideal R) (Ideal.mem_map_of_mem φ hs)
  have hσx_m : ∀ s ∈ maximalIdeal S, σ (xbar s) = 0 := fun s hs => by
    have : xbar s = 0 := by rw [← RingHom.mem_ker, hxbar]; exact hs
    rw [this, map_zero]

  have hkey : ∀ s, σ (resR (φ s)) = ψ s := by
    intro s
    obtain ⟨t, ht⟩ := exists_sub_pow_mem (q := q) s

    set a := ψ t with ha
    set b := σ (resR (φ t)) with hb
    have hab : resA (a - b) = 0 := by
      rw [map_sub, ha, hb, hresA_σ, ← RingHom.comp_apply, hψ_cent, ← RingHom.comp_apply, hφ, sub_self]

    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (a - b)
    have hdm : d ∈ 𝔪 := by
      rw [h𝔪, mem_maximalIdeal_R_iff resR hresR, ← hresA_mk, hd, hab]
    have hδ2 : (a - b) * (a - b) = 0 := by
      rw [← hd, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hI2 (by simpa [pow_two] using Ideal.mul_mem_mul hdm hdm)
    have hpow : a ^ q = b ^ q := by
      have := add_pow_of_sq_eq_zero b (a - b) hδ2 q
      rw [add_sub_cancel, hqA, zero_mul, zero_mul, add_zero] at this
      exact this

    have h1 : ψ s = a ^ q := by
      have := hψ_m _ ht
      rw [map_sub, map_pow, sub_eq_zero] at this
      rw [this]
    have h2 : σ (resR (φ s)) = b ^ q := by
      have e1 : resR (φ s) = xbar s := by rw [← RingHom.comp_apply, hφ]
      have e2 : resR (φ t) = xbar t := by rw [← RingHom.comp_apply, hφ]
      have := hσx_m _ ht
      rw [map_sub, map_pow, map_sub, map_pow, sub_eq_zero] at this
      rw [e1, this, hb, e2]
    rw [h1, h2, hpow]
  have hχ₂φ : χ₂.toRingHom.comp φ = ψ := by
    ext s; exact hkey s
  have hχ₁φ : χ₁.toRingHom.comp φ = ψ := by
    ext s; rfl
  have hres₁ : resA.comp χ₁.toRingHom = resR := by
    ext r; exact hresA_mk r
  have hres₂ : resA.comp χ₂.toRingHom = resR := by
    ext r; exact hresA_σ (resR r)

  obtain ⟨χ, -, hχuniq⟩ := huniv (R ⧸ I) resA hresA_surj hresA_comp ψ hψ_cent
  have h12 : χ₁ = χ₂ := (hχuniq χ₁ ⟨hres₁, hχ₁φ⟩).trans (hχuniq χ₂ ⟨hres₂, hχ₂φ⟩).symm

  have h𝔪I : 𝔪 ≤ I := by
    intro r hr
    have h := congrArg (fun χ : R →ₐ[Onr] R ⧸ I => χ r) h12
    simp only [hχ₁, hχ₂] at h
    rw [(mem_maximalIdeal_R_iff resR hresR r).mp hr, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  have hfg : (𝔪 : Submodule R R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance 𝔪
  have hjac : (𝔪 : Ideal R) ≤ (⊥ : Ideal R).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hle : 𝔪 ≤ N ⊔ 𝔪 • 𝔪 := by
    have : 𝔪 ^ 2 = 𝔪 • 𝔪 := by rw [pow_two]; rfl
    rw [← this]; exact h𝔪I
  exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hle) hNle

theorem ringKrullDim_le [Finite (ResidueField S)]
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    (hxbar : RingHom.ker xbar = maximalIdeal S)
    (hresR : resR.comp (algebraMap Onr R) = residue Onr) (hφ : resR.comp φ = xbar)
    (huniv : ProRep S Onr R xbar resR φ) :
    ringKrullDim R ≤ ringKrullDim S := by
  have hunr := maximalIdeal_eq_map xbar resR φ hOnr_max hxbar hresR hφ huniv
  letI : Algebra S R := φ.toAlgebra
  have halg : algebraMap S R = φ := rfl

  haveI : (maximalIdeal R).LiesOver (maximalIdeal S) := by
    refine ⟨?_⟩
    have hle : maximalIdeal S ≤ (maximalIdeal R).under S := by
      intro s hs
      rw [Ideal.under_def, Ideal.mem_comap, halg]
      exact map_le xbar resR φ hxbar hresR hφ (Ideal.mem_map_of_mem φ hs)
    exact ((maximalIdeal.isMaximal S).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle)
  have h := Ideal.height_le_height_add_of_liesOver (maximalIdeal S) (maximalIdeal R)

  rw [halg, ← hunr, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  calc ringKrullDim R = (maximalIdeal R).height := (maximalIdeal_height_eq_ringKrullDim).symm
    _ ≤ (maximalIdeal S).height := by exact_mod_cast h
    _ = ringKrullDim S := maximalIdeal_height_eq_ringKrullDim

theorem isLocalRing_tsze (k : Type) [Field k] (r : ℕ) : IsLocalRing (TrivSqZeroExt k (Fin r → k)) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases h : a.fst = 0
  · right
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h, sub_zero]
    exact isUnit_one
  · left
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact Ne.isUnit h

theorem isArtinianRing_tsze (k : Type) [Field k] (r : ℕ) : IsArtinianRing (TrivSqZeroExt k (Fin r → k)) := by
  haveI : Module.Finite k (TrivSqZeroExt k (Fin r → k)) := inferInstanceAs (Module.Finite k (k × (Fin r → k)))
  exact IsArtinianRing.of_finite k _

theorem exists_tan_map [Finite (ResidueField S)]
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    (hxbar : RingHom.ker xbar = maximalIdeal S)
    (hresR : resR.comp (algebraMap Onr R) = residue Onr)
    (huniv : ProRep S Onr R xbar resR φ)
    (ι : ResidueField S →+* ResidueField Onr) (hι : ∀ s, ι (residue S s) = xbar s)
    (r : ℕ) (t : Fin r → S) (ht : ∀ i, t i ∈ maximalIdeal S)
    (L : S → (Fin r → ResidueField Onr))
    (hL_add : ∀ m m', m ∈ maximalIdeal S → m' ∈ maximalIdeal S → L (m + m') = L m + L m')
    (hL_mul : ∀ a m, m ∈ maximalIdeal S → L (a * m) = ι (residue S a) • L m)
    (hL_sq : ∀ m ∈ maximalIdeal S ^ 2, L m = 0)
    (hL_q : L ((q : ℕ) : S) = 0)
    (hL_t : ∀ i, L (t i) = Pi.single i 1) :
    ∃ Λ : R →+ (Fin r → ResidueField Onr),
      (∀ a m, m ∈ maximalIdeal R → Λ (a * m) = resR a • Λ m) ∧
      Λ ((q : ℕ) : R) = 0 ∧
      ∀ i, Λ (φ (t i)) = Pi.single i 1 := by
  classical
  haveI : CharP (ResidueField Onr) q := charP_k hOnr_max
  have hqS : ((q : ℕ) : S) ∈ maximalIdeal S := natCast_mem_maximalIdeal_S xbar hxbar
  haveI : CharP (ResidueField S) q := charP_residueField hqS

  letI : Fintype (ResidueField S) := Fintype.ofFinite _
  set Q : ℕ := Fintype.card (ResidueField S) with hQ
  obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField S) q
  have hQpow : Q = q ^ (n : ℕ) := hn
  have h2Q : 2 ≤ Q := Fintype.one_lt_card

  have hL0 : L 0 = 0 := by
    have := hL_add 0 0 (zero_mem _) (zero_mem _)
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hL_neg : ∀ m, m ∈ maximalIdeal S → L (-m) = -L m := fun m hm => by
    have := hL_add m (-m) hm (neg_mem hm)
    rw [add_neg_cancel, hL0] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hL_sub : ∀ m m', m ∈ maximalIdeal S → m' ∈ maximalIdeal S → L (m - m') = L m - L m' := fun m m' hm hm' => by
    rw [sub_eq_add_neg, hL_add m (-m') hm (neg_mem hm'), hL_neg m' hm', sub_eq_add_neg]
  have hL_qmul : ∀ c : S, L ((q : ℕ) * c) = 0 := fun c => by
    rw [mul_comm, hL_mul c _ hqS, hL_q, smul_zero]

  have hres_pow : ∀ s : S, residue S (s ^ Q) = residue S s := fun s => by
    rw [map_pow, hQ, FiniteField.pow_card]
  have hsQ : ∀ s : S, s - s ^ Q ∈ maximalIdeal S := fun s => by
    rw [← residue_eq_zero_iff, map_sub, hres_pow, sub_self]

  set D : S → (Fin r → ResidueField Onr) := fun s => L (s - s ^ Q) with hD
  have hD_add : ∀ s u, D (s + u) = D s + D u := fun s u => by
    obtain ⟨c, hc⟩ := exists_add_pow_prime_pow_eq hq.out s u n
    have : (s + u) - (s + u) ^ Q = (s - s ^ Q) + (u - u ^ Q) - (q : ℕ) * (s * u * c) := by
      rw [hQpow, hc]; ring
    simp only [hD]
    rw [this, hL_sub _ _ (add_mem (hsQ s) (hsQ u)) (Ideal.mul_mem_right _ _ hqS),
      hL_add _ _ (hsQ s) (hsQ u), hL_qmul, sub_zero]
  have hD_mul : ∀ s u, D (s * u) = ι (residue S s) • D u + ι (residue S u) • D s := fun s u => by
    have : s * u - (s * u) ^ Q = s * (u - u ^ Q) + u ^ Q * (s - s ^ Q) := by ring
    simp only [hD]
    rw [this, hL_add _ _ (Ideal.mul_mem_left _ _ (hsQ u)) (Ideal.mul_mem_left _ _ (hsQ s)),
      hL_mul _ _ (hsQ u), hL_mul _ _ (hsQ s), hres_pow]
  have hD_one : D 1 = 0 := by simp only [hD]; rw [one_pow, sub_self, hL0]
  have hD_zero : D 0 = 0 := by simp only [hD]; rw [zero_pow (by omega), sub_self, hL0]
  have hD_t : ∀ i, D (t i) = Pi.single i 1 := fun i => by
    simp only [hD]
    have hsq : t i ^ Q ∈ maximalIdeal S ^ 2 := by
      have : t i ^ Q = t i ^ 2 * t i ^ (Q - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (ht i) 2)
    rw [hL_sub _ _ (ht i) (Ideal.pow_le_self two_ne_zero hsq), hL_sq _ hsq, sub_zero, hL_t]

  set A := TrivSqZeroExt (ResidueField Onr) (Fin r → ResidueField Onr)
  haveI : IsLocalRing A := isLocalRing_tsze (ResidueField Onr) r
  haveI : IsArtinianRing A := isArtinianRing_tsze (ResidueField Onr) r
  have halgA : ∀ o : Onr, algebraMap Onr A o = TrivSqZeroExt.inl (residue Onr o) := fun o => rfl
  set resA : A →+* ResidueField Onr :=
    (TrivSqZeroExt.fstHom (ResidueField Onr) (ResidueField Onr) (Fin r → ResidueField Onr)).toRingHom with hresA
  have hresA_apply : ∀ a : A, resA a = a.fst := fun a => rfl
  have hresA_surj : Function.Surjective resA := fun u => ⟨TrivSqZeroExt.inl u, rfl⟩
  have hresA_comp : resA.comp (algebraMap Onr A) = residue Onr := by
    ext o; rfl

  let ψ : S →+* A :=
    { toFun := fun s => (ι (residue S s), D s)
      map_one' := by
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [TrivSqZeroExt.fst_one, map_one, map_one]; rfl
        · rw [TrivSqZeroExt.snd_one]; exact hD_one
      map_mul' := fun s u => by
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [TrivSqZeroExt.fst_mul, map_mul, map_mul]; rfl
        · change D (s * u) = ι (residue S s) • D u + MulOpposite.op (ι (residue S u)) • D s
          rw [op_smul_eq_smul, hD_mul]
      map_zero' := by
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [TrivSqZeroExt.fst_zero, map_zero, map_zero]; rfl
        · rw [TrivSqZeroExt.snd_zero]; exact hD_zero
      map_add' := fun s u => by
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [TrivSqZeroExt.fst_add, map_add, map_add]; rfl
        · rw [TrivSqZeroExt.snd_add]; exact hD_add s u }
  have hψ_fst : ∀ s, (ψ s).fst = ι (residue S s) := fun s => rfl
  have hψ_snd : ∀ s, (ψ s).snd = D s := fun s => rfl
  have hψ_cent : resA.comp ψ = xbar := by
    ext s; rw [RingHom.comp_apply, hresA_apply, hψ_fst, hι]

  obtain ⟨χ, ⟨hχres, hχφ⟩, -⟩ := huniv A resA hresA_surj hresA_comp ψ hψ_cent
  have hχ_fst : ∀ x : R, (χ x).fst = resR x := fun x => by
    rw [← hresA_apply, ← hχres]; rfl
  refine ⟨(TrivSqZeroExt.sndHom (ResidueField Onr) (Fin r → ResidueField Onr)).toAddMonoidHom.comp
    χ.toRingHom.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a m hm
    change (χ (a * m)).snd = resR a • (χ m).snd
    have hm0 : (χ m).fst = 0 := by rw [hχ_fst]; exact (mem_maximalIdeal_R_iff resR hresR m).mp hm
    rw [map_mul, TrivSqZeroExt.snd_mul, hm0, MulOpposite.op_zero, zero_smul, add_zero, hχ_fst]
  · change (χ ((q : ℕ) : R)).snd = 0
    rw [map_natCast, TrivSqZeroExt.snd_natCast]
  · intro i
    change (χ (φ (t i))).snd = Pi.single i 1
    have : χ (φ (t i)) = ψ (t i) := by rw [← hχφ]; rfl
    rw [this, hψ_snd, hD_t]

theorem le_spanFinrank_of_tan
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    (hresR : resR.comp (algebraMap Onr R) = residue Onr)
    (r : ℕ) (Λ : R →+ (Fin r → ResidueField Onr))
    (hΛ_mul : ∀ a m, m ∈ maximalIdeal R → Λ (a * m) = resR a • Λ m)
    (hΛ_e : ∀ i, ∃ m ∈ maximalIdeal R, Λ m = Pi.single i 1) :
    r ≤ (maximalIdeal R).spanFinrank ∧
      (((q : ℕ) : R) ∉ maximalIdeal R ^ 2 → Λ ((q : ℕ) : R) = 0 → r + 1 ≤ (maximalIdeal R).spanFinrank) := by
  classical
  haveI : CharP (ResidueField Onr) q := charP_k hOnr_max
  set 𝔪 : Ideal R := maximalIdeal R with h𝔪
  have hfg : (𝔪 : Submodule R R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance 𝔪
  set G : Set R := (𝔪 : Submodule R R).generators with hG
  have hGfin : G.Finite := Submodule.FG.finite_generators hfg
  have hGspan : Ideal.span G = 𝔪 := Submodule.span_generators _
  have hGcard : G.ncard = 𝔪.spanFinrank := Submodule.FG.generators_ncard hfg
  have hGsub : G ⊆ 𝔪 := fun g hg => hGspan ▸ Ideal.subset_span hg
  set GF : Finset R := hGfin.toFinset with hGF
  have hGFcoe : (GF : Set R) = G := hGfin.coe_toFinset
  have hGFcard : GF.card = 𝔪.spanFinrank := by
    rw [← hGcard, ← hGFcoe, Set.ncard_coe_finset]

  set v : GF → (Fin r → ResidueField Onr) := fun g => Λ g with hv
  have hspan : ∀ m ∈ 𝔪, Λ m ∈ Submodule.span (ResidueField Onr) (Set.range v) := by
    intro m hm
    rw [← hGspan] at hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span ⟨⟨x, hGfin.mem_toFinset.mpr hx⟩, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x hx hpx =>
      have hx' : x ∈ 𝔪 := hGspan ▸ hx
      rw [smul_eq_mul, hΛ_mul a x hx']
      exact Submodule.smul_mem _ _ hpx
  have htop : ⊤ ≤ Submodule.span (ResidueField Onr) (Set.range v) := by
    rw [← (Pi.basisFun (ResidueField Onr) (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨m, hm, hme⟩ := hΛ_e i
    rw [Pi.basisFun_apply, ← hme]
    exact hspan m hm
  have hr : r ≤ 𝔪.spanFinrank := by
    have h1 : Module.finrank (ResidueField Onr) (Fin r → ResidueField Onr) = r := Module.finrank_fin_fun _
    have h2 := finrank_range_le_card (R := ResidueField Onr) v
    rw [Set.finrank, eq_top_iff.mpr htop, finrank_top, h1, Fintype.card_coe, hGFcard] at h2
    exact h2
  refine ⟨hr, fun hq2 hΛq => ?_⟩
  by_contra hlt
  have heq : 𝔪.spanFinrank = r := by omega

  have hli : LinearIndependent (ResidueField Onr) v := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank htop
    rw [Fintype.card_coe, hGFcard, heq, Module.finrank_fin_fun]

  have hqm : ((q : ℕ) : R) ∈ Submodule.span R (GF : Set R) := by
    rw [hGFcoe]
    change ((q : ℕ) : R) ∈ Ideal.span G
    rw [hGspan]
    exact natCast_mem_maximalIdeal_R resR hresR
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hqm

  have hsum : ∑ x : GF, resR (f x) • v x = 0 := by
    have : ∀ a ∈ GF, Λ (f a • a) = resR (f a) • Λ a := fun a ha =>
      by rw [smul_eq_mul, hΛ_mul _ _ (hGsub (hGFcoe ▸ (Finset.mem_coe.mpr ha)))]
    calc ∑ x : GF, resR (f x) • v x = ∑ a ∈ GF, resR (f a) • Λ a :=
          Finset.sum_coe_sort GF (fun a => resR (f a) • Λ a)
      _ = ∑ a ∈ GF, Λ (f a • a) := (Finset.sum_congr rfl this).symm
      _ = Λ (∑ a ∈ GF, f a • a) := (map_sum Λ _ _).symm
      _ = 0 := by rw [hf, hΛq]
  have hcoef : ∀ x : GF, resR (f x) = 0 := Fintype.linearIndependent_iff.mp hli _ hsum

  apply hq2
  rw [← hf, pow_two]
  refine Ideal.sum_mem _ fun a ha => ?_
  rw [smul_eq_mul]
  refine Ideal.mul_mem_mul ?_ (hGsub (hGFcoe ▸ (Finset.mem_coe.mpr ha)))
  rw [h𝔪, mem_maximalIdeal_R_iff resR hresR]
  exact hcoef ⟨a, ha⟩

theorem natCast_notMem_sq [Finite (ResidueField S)]
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    (hxbar : RingHom.ker xbar = maximalIdeal S)
    (hresR : resR.comp (algebraMap Onr R) = residue Onr)
    (huniv : ProRep S Onr R xbar resR φ)
    (hqS2 : ((q : ℕ) : S) ∉ maximalIdeal S ^ 2) :
    ((q : ℕ) : R) ∉ maximalIdeal R ^ 2 := by
  classical
  haveI : CharP (ResidueField Onr) q := charP_k hOnr_max
  have hqS : ((q : ℕ) : S) ∈ maximalIdeal S := natCast_mem_maximalIdeal_S xbar hxbar
  haveI : CharP (ResidueField S) q := charP_residueField hqS

  set J : Ideal Onr := maximalIdeal Onr ^ 2 with hJ
  have hJle : J ≤ maximalIdeal Onr := Ideal.pow_le_self two_ne_zero
  haveI : IsLocalRing (Onr ⧸ J) := isLocalRing_quotient hJle
  haveI : IsArtinianRing (Onr ⧸ J) := isArtinianRing_quotient hJle le_rfl
  have hJker : ∀ a ∈ J, residue Onr a = 0 := fun a ha => (residue_eq_zero_iff a).mpr (hJle ha)
  set resD : Onr ⧸ J →+* ResidueField Onr := Ideal.Quotient.lift J (residue Onr) hJker with hresD
  have hresD_mk : ∀ o, resD (Ideal.Quotient.mk J o) = residue Onr o := fun o => Ideal.Quotient.lift_mk J _ hJker
  have hresD_surj : Function.Surjective resD := fun u => by
    obtain ⟨o, rfl⟩ := residue_surjective u; exact ⟨Ideal.Quotient.mk J o, hresD_mk o⟩
  have hresD_comp : resD.comp (algebraMap Onr (Onr ⧸ J)) = residue Onr := by
    ext o; rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, hresD_mk]
  have hkerD : RingHom.ker resD = maximalIdeal (Onr ⧸ J) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resD hresD_surj)
  have hmemD : ∀ d, d ∈ maximalIdeal (Onr ⧸ J) → ∃ o ∈ maximalIdeal Onr, Ideal.Quotient.mk J o = d := by
    intro d hd
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective d
    refine ⟨o, ?_, rfl⟩
    rw [← hkerD, RingHom.mem_ker, hresD_mk, residue_eq_zero_iff] at hd
    exact hd
  have hDsq : maximalIdeal (Onr ⧸ J) ^ 2 = ⊥ := by
    rw [eq_bot_iff, pow_two, Ideal.mul_le]
    intro d hd d' hd'
    obtain ⟨o, ho, rfl⟩ := hmemD d hd
    obtain ⟨o', ho', rfl⟩ := hmemD d' hd'
    rw [← map_mul, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hJ, pow_two]
    exact Ideal.mul_mem_mul ho ho'

  obtain ⟨ψ, hψ⟩ := IsLocalRing.exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq (q := q) hqS2 hDsq resD
    hresD_surj xbar hxbar

  obtain ⟨χ, ⟨hχres, -⟩, -⟩ := huniv (Onr ⧸ J) resD hresD_surj hresD_comp ψ hψ

  have hχloc : (maximalIdeal R).map χ.toRingHom ≤ maximalIdeal (Onr ⧸ J) := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap, ← hkerD, RingHom.mem_ker, ← RingHom.comp_apply, hχres]
    exact (mem_maximalIdeal_R_iff resR hresR m).mp hm
  intro hq2
  have h0 : χ ((q : ℕ) : R) = 0 := by
    have : χ.toRingHom ((q : ℕ) : R) ∈ (maximalIdeal R ^ 2).map χ.toRingHom := Ideal.mem_map_of_mem _ hq2
    rw [Ideal.map_pow] at this
    have := Ideal.pow_right_mono hχloc 2 this
    rw [hDsq, Ideal.mem_bot] at this
    exact this

  rw [map_natCast, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem, hJ,
    maximalIdeal_Onr_eq hOnr_max, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h0
  obtain ⟨c, hc⟩ := h0
  have hq0 : ((q : ℕ) : Onr) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  have hunit : IsUnit ((q : ℕ) : Onr) := by
    refine isUnit_iff_exists_inv.mpr ⟨c, ?_⟩
    have : ((q : ℕ) : Onr) * (1 - (q : ℕ) * c) = 0 := by rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, ← hc, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hq0
    · exact (sub_eq_zero.mp h).symm
  exact (mem_maximalIdeal _).mp (natCast_mem_maximalIdeal_Onr hOnr_max) hunit

theorem main [Finite (ResidueField S)]
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    (hxbar : RingHom.ker xbar = maximalIdeal S)
    (hresR : resR.comp (algebraMap Onr R) = residue Onr) (hφ : resR.comp φ = xbar)
    (huniv : ProRep S Onr R xbar resR φ) (hqR : ((q : ℕ) : R) ≠ 0) :
    IsRegularLocalRing S ∧ ((q : ℕ) : S) ≠ 0 := by
  classical
  haveI : CharP (ResidueField Onr) q := charP_k hOnr_max
  have hqS : ((q : ℕ) : S) ∈ maximalIdeal S := natCast_mem_maximalIdeal_S xbar hxbar
  haveI : CharP (ResidueField S) q := charP_residueField hqS
  refine ⟨?_, fun h => hqR (by rw [← map_natCast φ, h, map_zero])⟩

  have hkerle : ∀ a ∈ maximalIdeal S, xbar a = 0 := fun a ha => by rwa [← RingHom.mem_ker, hxbar]
  set ι : ResidueField S →+* ResidueField Onr := Ideal.Quotient.lift (maximalIdeal S) xbar hkerle with hιdef
  have hι : ∀ s, ι (residue S s) = xbar s := fun s => Ideal.Quotient.lift_mk _ _ hkerle

  set 𝔫 : Ideal S := maximalIdeal S with h𝔫
  set qbar : CotangentSpace S := 𝔫.toCotangent ⟨(q : ℕ), hqS⟩ with hqbar
  set LS : Submodule (ResidueField S) (CotangentSpace S) := Submodule.span (ResidueField S) {qbar} with hLS
  set r : ℕ := Module.finrank (ResidueField S) (CotangentSpace S ⧸ LS) with hr
  let b := Module.finBasis (ResidueField S) (CotangentSpace S ⧸ LS)
  set πT : 𝔫 → CotangentSpace S ⧸ LS := fun m => LS.mkQ (𝔫.toCotangent m) with hπT
  have hπT_surj : Function.Surjective πT :=
    (Submodule.mkQ_surjective LS).comp (Ideal.toCotangent_surjective 𝔫)
  have hπT_add : ∀ x y, πT (x + y) = πT x + πT y := fun x y => by simp only [hπT, map_add]
  have hπT_smul : ∀ (a : S) (x : 𝔫), πT (a • x) = residue S a • πT x := fun a x => by
    simp only [hπT]
    rw [map_smul, ← IsScalarTower.algebraMap_smul (ResidueField S) a (𝔫.toCotangent x), map_smul]
    rfl

  choose t' ht' using fun i => hπT_surj (b i)
  set t : Fin r → S := fun i => (t' i : S) with htdef
  have ht : ∀ i, t i ∈ 𝔫 := fun i => (t' i).2

  set L0 : 𝔫 → (Fin r → ResidueField Onr) := fun x i => ι (b.repr (πT x) i) with hL0
  have hL0_add : ∀ x y, L0 (x + y) = L0 x + L0 y := fun x y => by
    funext i; simp only [hL0, hπT_add, map_add, Finsupp.add_apply, Pi.add_apply]
  have hL0_smul : ∀ (a : S) (x : 𝔫), L0 (a • x) = ι (residue S a) • L0 x := fun a x => by
    funext i; simp only [hL0, hπT_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
  set L : S → (Fin r → ResidueField Onr) := fun s => if h : s ∈ 𝔫 then L0 ⟨s, h⟩ else 0 with hLdef
  have hL_of : ∀ (s : S) (h : s ∈ 𝔫), L s = L0 ⟨s, h⟩ := fun s h => by simp only [hLdef, dif_pos h]
  have hL_add : ∀ m m', m ∈ 𝔫 → m' ∈ 𝔫 → L (m + m') = L m + L m' := fun m m' hm hm' => by
    rw [hL_of _ (add_mem hm hm'), hL_of _ hm, hL_of _ hm', ← hL0_add]; rfl
  have hL_mul : ∀ a m, m ∈ 𝔫 → L (a * m) = ι (residue S a) • L m := fun a m hm => by
    rw [hL_of _ (Ideal.mul_mem_left _ a hm), hL_of _ hm, ← hL0_smul]; rfl
  have hL_sq : ∀ m ∈ 𝔫 ^ 2, L m = 0 := fun m hm => by
    have hm1 : m ∈ 𝔫 := Ideal.pow_le_self two_ne_zero hm
    rw [hL_of _ hm1]
    funext i
    simp only [hL0, hπT]
    rw [(Ideal.toCotangent_eq_zero 𝔫 ⟨m, hm1⟩).mpr hm, map_zero, map_zero, Finsupp.zero_apply, map_zero]
    rfl
  have hL_q : L ((q : ℕ) : S) = 0 := by
    rw [hL_of _ hqS]
    funext i
    simp only [hL0, hπT]
    have : LS.mkQ (𝔫.toCotangent ⟨(q : ℕ), hqS⟩) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hLS]
      exact Submodule.mem_span_singleton_self _
    rw [this, map_zero, Finsupp.zero_apply, map_zero]
    rfl
  have hL_t : ∀ i, L (t i) = Pi.single i 1 := fun i => by
    rw [hL_of _ (ht i)]
    funext j
    simp only [hL0]
    have : πT ⟨t i, ht i⟩ = b i := by rw [← ht' i]
    rw [this, Module.Basis.repr_self, Finsupp.single_eq_pi_single,
      Pi.apply_single (fun _ => ι) (fun _ => map_zero ι) i 1 j, map_one]

  obtain ⟨Λ, hΛ_mul, hΛq, hΛt⟩ := exists_tan_map xbar resR φ hOnr_max hxbar hresR huniv ι hι r t ht L hL_add
    hL_mul hL_sq hL_q hL_t
  have hΛ_e : ∀ i, ∃ m ∈ maximalIdeal R, Λ m = Pi.single i 1 := fun i =>
    ⟨φ (t i), map_le xbar resR φ hxbar hresR hφ (Ideal.mem_map_of_mem φ (ht i)), hΛt i⟩
  obtain ⟨hr_le, hr1⟩ := le_spanFinrank_of_tan resR hOnr_max hresR r Λ hΛ_mul hΛ_e

  have hembS : 𝔫.spanFinrank = r + Module.finrank (ResidueField S) LS := by
    rw [h𝔫, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← Submodule.finrank_quotient_add_finrank LS]
  have hemb : 𝔫.spanFinrank ≤ (maximalIdeal R).spanFinrank := by
    by_cases hq2 : ((q : ℕ) : S) ∈ 𝔫 ^ 2
    · have hLS0 : LS = ⊥ := by
        rw [hLS, Submodule.span_singleton_eq_bot, hqbar]
        exact (Ideal.toCotangent_eq_zero 𝔫 _).mpr hq2
      rw [hembS, hLS0, finrank_bot, add_zero]
      exact hr_le
    · have h1 : Module.finrank (ResidueField S) LS ≤ 1 := by
        rw [hLS]
        exact (finrank_span_le_card ({qbar} : Set (CotangentSpace S))).trans (by simp)
      have h2 := hr1 (natCast_notMem_sq xbar resR φ hOnr_max hxbar hresR huniv hq2) hΛq
      rw [hembS]; omega

  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le S ?_
  calc ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := by
        exact_mod_cast hemb
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim S := ringKrullDim_le xbar resR φ hOnr_max hxbar hresR hφ huniv

end Core

end P2M.ProrepRegular

open CategoryTheory AlgebraicGeometry

theorem solution
    {q : ℕ} [Fact q.Prime]
    {Y : Scheme.{0}} (πY : Y ⟶ Spec (CommRingCat.of ℤ_[q])) [LocallyOfFiniteType πY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyq : πY y = IsLocalRing.closedPoint ℤ_[q])
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    (xbar : Y.presheaf.stalk y →+* IsLocalRing.ResidueField Onr)
    (hxbar : RingHom.ker xbar = IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
    (R : Type) [CommRing R] [IsRegularLocalRing R] [Algebra Onr R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (φ : Y.presheaf.stalk y →+* R) (hφ : resR.comp φ = xbar)
    (huniv :
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
          (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
          resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
        ∀ ψ : Y.presheaf.stalk y →+* A, resA.comp ψ = xbar →
          ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧ χ.toRingHom.comp φ = ψ))
    (hqR : ((q : ℕ) : R) ≠ 0) :
    IsRegularLocalRing (Y.presheaf.stalk y) ∧ ((q : ℕ) : Y.presheaf.stalk y) ≠ 0 := by

  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian πY

  haveI : Finite (IsLocalRing.ResidueField ℤ_[q]) := Finite.of_equiv _ (PadicInt.residueField (p := q)).toEquiv.symm
  haveI : Finite (IsLocalRing.ResidueField (Y.presheaf.stalk y)) :=
    AlgebraicGeometry.finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType πY y hy hyq
  exact P2M.ProrepRegular.main xbar resR φ hOnr_max hxbar hresR hφ huniv hqR

end S_AlgebraicGeometry_isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy
end P2MW
export P2MW.S_AlgebraicGeometry_isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy (solution)
