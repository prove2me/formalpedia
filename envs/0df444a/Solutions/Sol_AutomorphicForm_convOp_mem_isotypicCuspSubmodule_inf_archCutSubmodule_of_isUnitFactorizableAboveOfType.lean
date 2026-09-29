-- Prove2me | solution 1 for AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b2e65765-1e17-5d02-ad9e-cf2c4998897c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

section

open NumberField IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsFactorizableTestFn IsIsotypicCuspFormAt isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule convOp convOp_apply convOp_zero convOp_smul convOp_add IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant rowIsometryInclAt₀ ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff archRowIsometryInclAt₀ glArch_rowIsometryInclAt₀ adelicGLHaar_mul_right_centreCutSiegelSet_lt_top CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup isKfSmooth_iff lsXiMemberAt_iff unipotentGL2 HeckeEigensystem rightConv rowIsometrySubgroup₀ archComponent_archGLIncl_self continuous_and_hasCompactSupport_of_isFactorizableTestFn continuous_unipotentGL2 continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre IsBoundedOnSiegelWindows"
namespace LevelFiniteFactor
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K]

private theorem exists_heightOneSpectrum_comap_eq_span (p : ℕ) (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 K),
      Ideal.comap (algebraMap ℤ (𝓞 K)) P.asIdeal = Ideal.span {(p : ℤ)} := by
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp0).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQprime, hQcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K)) (Ideal.comap_bot_le_of_injective _ hinj)
  refine ⟨⟨Q, hQprime, fun hQ => ?_⟩, hQcomap⟩
  rw [hQ, Ideal.comap_bot_of_injective _ hinj] at hQcomap
  exact hp0 (Ideal.span_singleton_eq_bot.1 hQcomap.symm)

private theorem ne_bot_of_forall_dvd_mem {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ N → p ∈ S) : N ≠ ⊥ := by
  rintro rfl
  have hall : ∀ p : HeightOneSpectrum (𝓞 K), p ∈ S := fun p =>
    hNS p (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  choose P hP using fun q : {p : ℕ | Nat.Prime p} =>
    exists_heightOneSpectrum_comap_eq_span (K := K) q.1 q.2
  haveI : Infinite {p : ℕ | Nat.Prime p} := Set.infinite_coe_iff.2 Nat.infinite_setOf_prime
  refine not_injective_infinite_finite (fun q : {p : ℕ | Nat.Prime p} => (⟨P q, hall (P q)⟩ : S))
    fun q₁ q₂ h => ?_
  have h' : P q₁ = P q₂ := congrArg Subtype.val h
  have hspan : Ideal.span {((q₁ : ℕ) : ℤ)} = Ideal.span {((q₂ : ℕ) : ℤ)} := by
    rw [← hP q₁, ← hP q₂, h']
  have hq := Int.eq_of_associated_of_nonneg (Ideal.span_singleton_eq_span_singleton.1 hspan)
    (by positivity) (by positivity)
  exact Subtype.ext (by exact_mod_cast hq)

end AutomorphicForm.LevelFiniteFactor

end

section

open NumberField IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsFactorizableTestFn IsIsotypicCuspFormAt isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule convOp convOp_apply convOp_zero convOp_smul convOp_add IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant rowIsometryInclAt₀ ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff archRowIsometryInclAt₀ glArch_rowIsometryInclAt₀ adelicGLHaar_mul_right_centreCutSiegelSet_lt_top CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup isKfSmooth_iff lsXiMemberAt_iff unipotentGL2 HeckeEigensystem rightConv rowIsometrySubgroup₀ archComponent_archGLIncl_self continuous_and_hasCompactSupport_of_isFactorizableTestFn continuous_unipotentGL2 continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre IsBoundedOnSiegelWindows"
namespace LevelFiniteFactor
p2m_open "AutomorphicForm"

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
private theorem map_algebraMap_ne_bot {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ :=
  fun h => hNK ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective K L)).1 h)

end AutomorphicForm.LevelFiniteFactor

end

section T3ppBound

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

namespace Q09StabH

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem idealBound_map_eq_one_of_not_mem {NK : Ideal (𝓞 K)} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {SL : Finset (HeightOneSpectrum (𝓞 L))} (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ SK → w ∈ SL)
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK) (hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ SL) :
    idealBound (𝓞 L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) w = 1 := by
  apply idealBound_eq_one_of_not_dvd hN
  intro hdvd
  refine hw (hSL w (hNS _ ?_))
  show (w.asIdeal.under (𝓞 K)) ∣ NK
  rw [Ideal.dvd_iff_le] at hdvd ⊢
  exact Ideal.le_comap_map.trans (Ideal.comap_mono hdvd)

end Q09StabH

end T3ppBound

section CTpart

noncomputable section

namespace Q09

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

private noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

private theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

private theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

private theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  rw [hmk, map_mul, ← mul_assoc, out_mul_cosetCoord]

private theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ (k : H), ∀ v ∈ P, ρ k v ∈ P)
    (S : P →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : P) (x : G), S ⟨ρ k v, hP k v v.2⟩ x = S v (x * ι k)) (v : P) :
    S v ∈ AutomorphicForm.typeSubmodule ι ρ := by
  classical

  let ℓ : G ⧸ ι.range → (P →ₗ[ℂ] ℂ) := fun c =>
    { toFun := fun p => S p c.out
      map_add' := fun p q => by rw [map_add]; rfl
      map_smul' := fun a p => by rw [map_smul]; rfl }
  have hext : ∀ c, ∃ g : W →ₗ[ℂ] ℂ, g.comp P.subtype = ℓ c := fun c => LinearMap.exists_extend (ℓ c)
  let ℓ' : G ⧸ ι.range → (W →ₗ[ℂ] ℂ) := fun c => (hext c).choose
  have hℓ' : ∀ c (p : P), ℓ' c (p : W) = S p c.out := fun c p => by
    have := LinearMap.congr_fun (hext c).choose_spec p
    simpa [ℓ] using this

  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) w)
      map_add' := fun w₁ w₂ => funext fun x => by simp only [map_add, Pi.add_apply]
      map_smul' := fun a w => funext fun x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hT : AutomorphicForm.IsRightEquivariant ι ρ T := by
    intro k w x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (ρ k w)) =
      ℓ' (QuotientGroup.mk (x * ι k)) (ρ (cosetCoord ι (x * ι k)) w)
    have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq]
      exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
    rw [hmk, cosetCoord_mul hι, map_mul]
    rfl
  have hTS : T (v : W) = S v := by
    funext x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (v : W)) = S v x
    have hmem : ρ (cosetCoord ι x) (v : W) ∈ P := hP _ _ v.2
    have h1 := hℓ' (QuotientGroup.mk x) ⟨_, hmem⟩
    simp only at h1
    rw [h1, hS (cosetCoord ι x) v, out_mul_cosetCoord]
  rw [← hTS]
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT _

end TypePiece

section PiRep

variable {H : Type*} [Group H]
variable {A : Type*} {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]

private def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

private theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

private theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
    (v : W a) : piRep ρ k (Pi.single a v) = Pi.single a (ρ a k v) := by
  funext b
  rw [piRep_apply]
  by_cases hb : b = a
  · subst hb
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hb, map_zero]

end PiRep

section Transport

variable {H G : Type*} [Group H] [Group G]

private theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] (ι : H →* G)
    (ρ : ∀ a, Representation ℂ H (W a)) :
    typeSubmodule ι (piRep ρ) ≤ ⨆ a, typeSubmodule ι (ρ a) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  show T v ∈ ⨆ a, typeSubmodule ι (ρ a)
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ?_
  have hTa : IsRightEquivariant ι (ρ a) (T.comp (LinearMap.single ℂ W a)) := by
    intro k w x
    show T (Pi.single a (ρ a k w)) x = T (Pi.single a w) (x * ι k)
    rw [← piRep_single]
    exact hT k (Pi.single a w) x
  exact mem_typeSubmodule_of_isRightEquivariant hTa (v a)

private theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

private theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) {θ : G → ℂ} (hθ : θ ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ θ ∈ LinearMap.range Φ := by
  classical
  have h1 : θ ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hθ
  obtain ⟨t, ht, hθt⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hgen : ∀ f : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (f : G → ℂ) ∈ LinearMap.range T := fun f => by
    have hf := ht f.2
    rw [Set.mem_iUnion] at hf
    obtain ⟨j, T, hT, hfT⟩ := hf
    exact ⟨j, T, hT, hfT⟩
  choose i T hT hfT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · refine (Submodule.span_le.mpr ?_) hθt
    intro f hf
    obtain ⟨v, hv⟩ := hfT ⟨f, hf⟩
    refine ⟨Pi.single (⟨f, hf⟩ : t) v, ?_⟩
    rw [hΦ, Finset.sum_eq_single (⟨f, hf⟩ : t)]
    · rw [Pi.single_eq_same]
      exact hv
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G) {ι' : H →* G'}
    (hι' : Function.Injective ι') (ρ : ∀ j, Representation ℂ H (W j)) (P₀ : Submodule ℂ (G → ℂ))
    (hP₀ : ∀ (k : H), ∀ θ ∈ P₀, (fun x => θ (x * ι k)) ∈ P₀) (A : P₀ →ₗ[ℂ] (G' → ℂ))
    (hA : ∀ (k : H) (θ : P₀) (y : G'), A ⟨fun x => (θ : G → ℂ) (x * ι k), hP₀ k θ θ.2⟩ y =
      A θ (y * ι' k))
    (θ : P₀) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    A θ ∈ ⨆ j, typeSubmodule ι' (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, v, hv⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hθ
  have hQ : ∀ (k : H), ∀ w ∈ P₀.comap Φ, piRep (fun a => ρ (i a)) k w ∈ P₀.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι k) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hP₀ k _ hw
  let ΦQ : P₀.comap Φ →ₗ[ℂ] P₀ :=
    LinearMap.codRestrict P₀ (Φ.comp (P₀.comap Φ).subtype) fun w => w.2
  have hΦQ : ∀ w : P₀.comap Φ, ((ΦQ w : P₀) : G → ℂ) = Φ (w : ∀ a : t, W (i a)) := fun _ => rfl
  let S : P₀.comap Φ →ₗ[ℂ] (G' → ℂ) := A.comp ΦQ
  have hS : ∀ (k : H) (w : P₀.comap Φ) (y : G'),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ y = S w (y * ι' k) := by
    intro k w y
    have h1 : ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ =
        ⟨fun x => ((ΦQ w : P₀) : G → ℂ) (x * ι k), hP₀ k _ (ΦQ w).2⟩ := by
      apply Subtype.ext
      funext x
      exact hΦ k w x
    show A (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩) y = A (ΦQ w) (y * ι' k)
    rw [h1]
    exact hA k (ΦQ w) y
  have hv' : v ∈ P₀.comap Φ := by
    rw [Submodule.mem_comap, hv]
    exact θ.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hι' (fun a => ρ (i a)) (P₀.comap Φ)
    hQ S hS ⟨v, hv'⟩
  have hSv : S ⟨v, hv'⟩ = A θ := by
    show A (ΦQ ⟨v, hv'⟩) = A θ
    congr 1
    exact Subtype.ext hv
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι' (ρ j)) (i a)) hmem

end Transport

section ConvTransport

open MeasureTheory

variable {H G : Type*} [Group H] [Group G]

private theorem conv_integrand_eq (u θ : G → ℂ) (k y x : G) :
    u (y * k * (k⁻¹ * x)) * θ (k⁻¹ * x)⁻¹ = u (y * x) * θ (x⁻¹ * k) := by
  rw [mul_assoc, mul_inv_cancel_left, mul_inv_rev, inv_inv]

variable [MeasurableSpace G] (μ : Measure G) (u : G → ℂ)

private def convDomain : Submodule ℂ (G → ℂ) where
  carrier := {θ | ∀ y : G, Integrable (fun x => u (y * x) * θ x⁻¹) μ}
  zero_mem' := by
    intro y
    simp
  add_mem' := by
    intro θ₁ θ₂ h₁ h₂ y
    have e : (fun x => u (y * x) * (θ₁ + θ₂) x⁻¹) =
        fun x => u (y * x) * θ₁ x⁻¹ + u (y * x) * θ₂ x⁻¹ :=
      funext fun x => by simp only [Pi.add_apply, mul_add]
    rw [e]
    exact (h₁ y).add (h₂ y)
  smul_mem' := by
    intro c θ h y
    have e : (fun x => u (y * x) * (c • θ) x⁻¹) = fun x => c * (u (y * x) * θ x⁻¹) :=
      funext fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [e]
    exact (h y).const_mul c

private theorem mem_convDomain_iff (θ : G → ℂ) :
    θ ∈ convDomain μ u ↔ ∀ y : G, Integrable (fun x => u (y * x) * θ x⁻¹) μ :=
  Iff.rfl

private def convOpOn : convDomain μ u →ₗ[ℂ] (G → ℂ) where
  toFun θ := fun y => ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ
  map_add' θ₁ θ₂ := funext fun y => by
    have h₁ := (mem_convDomain_iff μ u _).mp θ₁.2 y
    have h₂ := (mem_convDomain_iff μ u _).mp θ₂.2 y
    show (∫ x, u (y * x) * ((θ₁ : G → ℂ) + (θ₂ : G → ℂ)) x⁻¹ ∂μ) =
      (∫ x, u (y * x) * (θ₁ : G → ℂ) x⁻¹ ∂μ) + ∫ x, u (y * x) * (θ₂ : G → ℂ) x⁻¹ ∂μ
    rw [← integral_add h₁ h₂]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply, mul_add])
  map_smul' c θ := funext fun y => by
    show (∫ x, u (y * x) * (c • (θ : G → ℂ)) x⁻¹ ∂μ) = c * ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ
    have e : (∫ x, u (y * x) * (c • (θ : G → ℂ)) x⁻¹ ∂μ) = ∫ x, c * (u (y * x) * (θ : G → ℂ) x⁻¹) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm])
    rw [e]
    exact integral_const_mul c _

private theorem convOpOn_apply (θ : convDomain μ u) (y : G) :
    convOpOn μ u θ y = ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ :=
  rfl

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

private theorem comp_mul_mem_convDomain {θ : G → ℂ} (hθ : θ ∈ convDomain μ u) (k : G) :
    (fun x => θ (x * k)) ∈ convDomain μ u := by
  rw [mem_convDomain_iff] at hθ ⊢
  intro y
  refine ((hθ (y * k)).comp_mul_left k⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
  exact conv_integrand_eq u θ k y x

private theorem convOpOn_comp_mul (θ : convDomain μ u) (k : G)
    (hk : (fun x => (θ : G → ℂ) (x * k)) ∈ convDomain μ u) (y : G) :
    convOpOn μ u ⟨fun x => (θ : G → ℂ) (x * k), hk⟩ y = convOpOn μ u θ (y * k) := by
  simp only [convOpOn_apply]
  rw [← integral_mul_left_eq_self (fun x => u (y * k * x) * (θ : G → ℂ) x⁻¹) k⁻¹]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (conv_integrand_eq u (θ : G → ℂ) k y x).symm)

private theorem convOpOn_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] {ι : H →* G} (hι : Function.Injective ι) (ρ : ∀ j, Representation ℂ H (W j))
    (θ : convDomain μ u) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    convOpOn μ u θ ∈ ⨆ j, typeSubmodule ι (ρ j) :=
  mem_iSup_typeSubmodule_of_intertwines ι hι ρ (convDomain μ u)
    (fun k _ hθ' => comp_mul_mem_convDomain μ u hθ' (ι k)) (convOpOn μ u)
    (fun k θ' y => convOpOn_comp_mul μ u θ' (ι k) _ y) θ hθ

end ConvTransport

end Q09

end

end CTpart

section CONV1part

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm IsDedekindDomain MeasureTheory FLT.SmoothVectors"
open scoped ProbabilityTheory

noncomputable section

namespace Q09StabH
namespace ConvLeg

private abbrev pinsL (L : Type) [Field L] [NumberField L] (X : Set (AdelicGL2 (𝓞 L) L)) : CarrierPins L :=
  productionPinsOf L X (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
    (adelicBox L)

private abbrev window (L : Type) [Field L] [NumberField L] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    Set (AdelicGL2 (𝓞 L) L) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂

section Pins

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem mem_Z (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) : z ∈ (pinsL L X).Z := by
  show z ∈ (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)
  exact Subgroup.mem_top z

private def toZ (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) : (pinsL L X).Z := ⟨z, mem_Z X z⟩

@[scoped simp] private theorem coe_toZ (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((toZ X z : (pinsL L X).Z) : (AdeleRing (𝓞 L) L)ˣ) = z := rfl

private theorem toZ_coe (X : Set (AdelicGL2 (𝓞 L) L)) (z : (pinsL L X).Z) : toZ X (z : (AdeleRing (𝓞 L) L)ˣ) = z :=
  Subtype.ext rfl

end Pins

section Interchange

private noncomputable def integralCLM {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] :
    C(Y, ℂ) →L[ℝ] ℂ :=
  haveI : IsFiniteMeasureOnCompacts ρ :=
    isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace.mp inferInstance
  have hint : ∀ F : C(Y, ℂ), Integrable (fun y => F y) ρ := fun F =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  LinearMap.mkContinuous
    { toFun := fun F => ∫ y, F y ∂ρ
      map_add' := fun F₁ F₂ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint F₁) (hint F₂)
      map_smul' := fun r F => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul r fun y => F y }
    (ρ.real Set.univ) fun F => by
      refine (norm_integral_le_of_norm_le_const (μ := ρ)
        (Filter.Eventually.of_forall fun y => F.norm_coe_le_norm y)).trans ?_
      rw [mul_comm]

private theorem integralCLM_apply {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ]
    (F : C(Y, ℂ)) : integralCLM ρ F = ∫ y, F y ∂ρ :=
  rfl

section Slices

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {Q : Type*} [TopologicalSpace Q] (S : Set Q)
  {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ} (hf : Continuous f)
  (g : G)

private def sliceFn : C(G × S, ℂ) :=
  ⟨fun p => φ (u p.2 * g * p.1) * f p.1, by fun_prop⟩

private noncomputable def slice (x : G) : C(S, ℂ) :=
  (sliceFn S hu hφ hf g).curry x

private theorem slice_apply (x : G) (q : S) : slice S hu hφ hf g x q = φ (u q * g * x) * f x :=
  rfl

private theorem continuous_slice : Continuous (slice S hu hφ hf g) :=
  (sliceFn S hu hφ hf g).curry.continuous

private theorem hasCompactSupport_slice (hfs : HasCompactSupport f) :
    HasCompactSupport (slice S hu hφ hf g) := by
  refine hfs.mono fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro hfx
  apply hx
  ext q
  rw [slice_apply, hfx, mul_zero, ContinuousMap.zero_apply]

end Slices

private theorem integral_integral_eq_zero
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {Q : Type*} [TopologicalSpace Q] [T2Space Q] [MeasurableSpace Q] [OpensMeasurableSpace Q]
    (ν : Measure Q) [IsFiniteMeasure ν] {S : Set Q} (hS : IsCompact S) (hνS : ∀ᵐ q ∂ν, q ∈ S)
    {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (g : G)
    (hzero : ∀ h : G, ∫ q, φ (u q * h) ∂ν = 0) :
    ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) ∂ν = 0 := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hνS

  have hsub : ∀ h : Q → ℂ, ∫ q : S, h q ∂(ν.comap Subtype.val) = ∫ q, h q ∂ν := fun h => by
    rw [integral_subtype_comap hSm, hres]
  have hΦi : Integrable (slice S hu hφ hf g) μ :=
    (continuous_slice S hu hφ hf g).integrable_of_hasCompactSupport
      (hasCompactSupport_slice S hu hφ hf g hfs)

  have hJΦ : ∀ x, integralCLM (ν.comap (Subtype.val : S → Q)) (slice S hu hφ hf g x) = 0 :=
    fun x => by
      rw [integralCLM_apply]
      simp only [slice_apply]
      rw [hsub fun q => φ (u q * g * x) * f x, integral_mul_const]
      simp only [mul_assoc]
      rw [hzero (g * x), zero_mul]

  have hev : ∀ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q = ∫ x, φ (u q * g * x) * f x ∂μ :=
    fun q => by
      rw [ContinuousMap.integral_apply hΦi q]
      simp only [slice_apply]
  calc ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) ∂ν
      = ∫ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q ∂(ν.comap (Subtype.val : S → Q)) := by
        rw [← hsub fun q => ∫ x, φ (u q * g * x) * f x ∂μ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hev q).symm)
    _ = integralCLM (ν.comap (Subtype.val : S → Q)) (∫ x, slice S hu hφ hf g x ∂μ) :=
        (integralCLM_apply _ _).symm
    _ = ∫ x, integralCLM (ν.comap (Subtype.val : S → Q)) (slice S hu hφ hf g x) ∂μ :=
        (ContinuousLinearMap.integral_comp_comm _ hΦi).symm
    _ = 0 := by simp only [hJΦ, integral_zero]

end Interchange

section Conv

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem isFactorizableTestFn_of_tier {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) : IsFactorizableTestFn L φ := by
  obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := hφ.1.2
  exact ⟨φa, φf, h₁, h₂, h₆⟩

private theorem rightConv_mul_eq_of_tier {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) (u : AdelicGL2 (𝓞 L) L → ℂ)
    (g : AdelicGL2 (𝓞 L) L) {k : AdelicGL2 (𝓞 L) L} (hk : k ∈ U) :
    rightConv L u φ (g * k) = rightConv L u φ g := by
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply L u φ g k]
  have hφk : (fun y => φ (k⁻¹ * y)) = φ := funext fun y => (hφ.1.1 k⁻¹ (inv_mem hk) y).1
  rw [hφk]

private theorem measurableSet_window (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    (letI := glBorel (Fin 2) (𝓞 L) L; MeasurableSet (window L c v d₁ d₂ T)) := by
  letI := glBorel (Fin 2) (𝓞 L) L
  haveI := borelSpace_glBorel (Fin 2) (𝓞 L) L
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet L c v d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet L c v d₁ d₂ := by
    ext g
    simp [Set.mem_preimage]
  rw [himg]
  exact measurable_mul_const x⁻¹ (measurableSet_centreCutSiegelSet (F := L) c v d₁ d₂)

private theorem measure_window_lt_top {c : ℝ} (hc : 0 < c) (v : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 L) L)) :
    (letI := glBorel (Fin 2) (𝓞 L) L; adelicGLHaar (Fin 2) (𝓞 L) L (window L c v d₁ d₂ T) < ⊤) := by
  letI := glBorel (Fin 2) (𝓞 L) L
  refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
  exact adelicGLHaar_mul_right_centreCutSiegelSet_lt_top L hc v hd₁ d₂ x

private theorem isIsotypicCuspFormAt_rightConv_of_hecke
    (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (c' v' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 L) L)) (hd' : d₁' < d₂')
    (hcov' : CoversModCentre L (window L c' v' d₁' d₂' T'))
    (ξ : (pinsL L (window L c v d₁ d₂ T)).Z →* ℂˣ) (ξ' : (pinsL L (window L c' v' d₁' d₂' T')).Z →* ℂˣ)
    (hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' (toZ _ z) = ξ (toZ _ z))
    {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    {tys : ArchTypeFamily L} {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : IsIsotypicCuspFormAt L (pinsL L (window L c' v' d₁' d₂' T')) ξ' N S Ψ u)
    (hhecke : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      IsHeckeCosetEigenfunctionAt L ((pinsL L (window L c v d₁ d₂ T)).U N) ((pinsL L (window L c v d₁ d₂ T)).gen w)
        w (rightConv L u φ) (Ψ.a w)) :
    IsIsotypicCuspFormAt L (pinsL L (window L c v d₁ d₂ T)) ξ N S Ψ (rightConv L u φ) := by
  have hfact : IsFactorizableTestFn L φ := isFactorizableTestFn_of_tier hφ
  obtain ⟨hφc, hφs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hfact
  have hucont : Continuous u := hu.continuous
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := adeleBorel (𝓞 L) L
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L
  haveI : IsProbabilityMeasure ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) :=
    isProbabilityMeasure_cond_adelicBox L

  have hls : IsLsXiFunction (𝓞 L) L (pinsL L (window L c' v' d₁' d₂' T')).Z ξ' u :=
    ((lsXiMemberAt_iff (𝓞 L) L _ _ ξ' _ u).mp hu.smoothCusp.1.1).1

  have hlevel : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      rightConv L u φ (g * k) = rightConv L u φ g := fun g k hk => rightConv_mul_eq_of_tier hφ u g hk

  have hcont : Continuous (rightConv L u φ) :=
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn L u hucont φ hfact).1
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hcont, hlevel, hhecke, ?_⟩
  ·

    refine (lsXiMemberAt_iff (𝓞 L) L _ _ ξ _ _).mpr ⟨⟨?_, ?_⟩, ?_⟩
    · intro γ g
      show (∫ x, u (globalPoints (𝓞 L) L γ * g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [mul_assoc, hls.left_invariant])
    · intro z g
      have hz : ∀ y : AdelicGL2 (𝓞 L) L,
          u (centralScalar (𝓞 L) L (z : (AdeleRing (𝓞 L) L)ˣ) * y) =
            ((ξ' (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) : ℂˣ) : ℂ) * u y :=
        fun y => hls.central_transform (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) y
      have hval : ((ξ' (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) : ℂˣ) : ℂ) = ((ξ z : ℂˣ) : ℂ) := by
        rw [hξ, toZ_coe]
      show (∫ x, u (centralScalar (𝓞 L) L (z : (AdeleRing (𝓞 L) L)ˣ) * g * x) * φ x
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        ((ξ z : ℂˣ) : ℂ) * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
      rw [← hval]
      exact (integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [mul_assoc, hz, mul_assoc])).trans (integral_const_mul _ _)
    ·
      have hbdd : IsBoundedOnSiegelWindows L (rightConv L u φ) :=
        isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre L c' v' d₁' d₂' T' hd'
          hcov' ξ' u hu.smoothCusp.1 hucont φ hfact
      obtain ⟨C, hC⟩ := hbdd c v d₁ d₂ T hc hd₁
      have hlt : adelicGLHaar (Fin 2) (𝓞 L) L (window L c v d₁ d₂ T) < ⊤ := measure_window_lt_top hc v hd₁ d₂ T
      haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (window L c v d₁ d₂ T)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hlt⟩
      show MemLp (rightConv L u φ) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (window L c v d₁ d₂ T))
      refine MemLp.of_bound hcont.aestronglyMeasurable C ?_
      exact ae_restrict_of_forall_mem (measurableSet_window c v d₁ d₂ T) hC
  ·
    intro g
    obtain ⟨S₀, hS₀, hBS⟩ := exists_isCompact_adelicBox_subset L
    have hνS : ∀ᵐ q ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]), q ∈ S₀ :=
      (ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox L)).mono fun q hq => hBS hq
    have hcusp : ∀ h : AdelicGL2 (𝓞 L) L,
        ∫ q, u (unipotentGL2 q * h) ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]) = 0 :=
      fun h => hu.smoothCusp.1.2 h
    show ∫ q, rightConv L u φ (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]) = 0
    exact integral_integral_eq_zero (adelicGLHaar (Fin 2) (𝓞 L) L) ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) hS₀
      hνS continuous_unipotentGL2 hucont hφc hφs g hcusp
  ·
    rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup]
    refine ⟨(levelOne (𝓞 L) L N).comap (finiteAdelicGL2Subgroup L).subtype, ?_, ?_⟩
    · rw [Subgroup.coe_comap, Subgroup.coe_subtype]
      exact (isOpen_levelOne (𝓞 L) L hN).preimage continuous_subtype_val
    · intro w hw
      rw [Subgroup.smul_def]
      exact RightTranslationFn.ext fun x =>
        hlevel x w (Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mp hw, w.2⟩)
  ·
    intro w hw g
    have hce : ∀ y : AdelicGL2 (𝓞 L) L,
        u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * y) =
          Ψ.toRawCentral.b w * u y :=
      fun y => hu.central_eigen w hw y
    show (∫ x, u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * g * x) * φ x
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      Ψ.toRawCentral.b w * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [mul_assoc, hce, mul_assoc])).trans (integral_const_mul _ _)

end Conv

end Q09StabH.ConvLeg
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end CONV1part
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section CONV2part

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm AutomorphicForm.SmoothCusp AdelicDock IsDedekindDomain MeasureTheory"

noncomputable section

namespace Q09StabH
namespace ConvLeg

section OnePlace

variable {L : Type} [Field L] [NumberField L]

private def placeAt (w : HeightOneSpectrum (𝓞 L)) : GL (Fin 2) (w.adicCompletion L) →* AdelicGL2 (𝓞 L) L :=
  (finEmbed (𝓞 L) L).comp (localEmbed (𝓞 L) L w)

variable (w : HeightOneSpectrum (𝓞 L))

private theorem glArch_placeAt (m : GL (Fin 2) (w.adicCompletion L)) : glArch (𝓞 L) L (placeAt w m) = 1 :=
  glArch_finEmbed (𝓞 L) L _

private theorem finComponent_glFin_placeAt_self (m : GL (Fin 2) (w.adicCompletion L)) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L (placeAt w m)) = m := by
  show finComponent (𝓞 L) L w (glFin (𝓞 L) L (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m))) = m
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem finComponent_glFin_placeAt_of_ne (m : GL (Fin 2) (w.adicCompletion L)) {w' : HeightOneSpectrum (𝓞 L)}
    (h : w' ≠ w) : finComponent (𝓞 L) L w' (glFin (𝓞 L) L (placeAt w m)) = 1 := by
  show finComponent (𝓞 L) L w' (glFin (𝓞 L) L (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 L) L w m h]

variable {w}

private theorem adelicGL2_ext {a b : AdelicGL2 (𝓞 L) L} (h₁ : glArch (𝓞 L) L a = glArch (𝓞 L) L b)
    (h₂ : ∀ w' : HeightOneSpectrum (𝓞 L),
      finComponent (𝓞 L) L w' (glFin (𝓞 L) L a) = finComponent (𝓞 L) L w' (glFin (𝓞 L) L b)) : a = b := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  refine Prod.ext ?_ ?_
  · have h := congrArg
      (fun g : GL (Fin 2) (InfiniteAdeleRing L) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) h₁
    simpa only [glArch_apply] using h
  · refine FiniteAdeleRing.ext L fun w' => ?_
    have h := congrArg
      (fun g : GL (Fin 2) (w'.adicCompletion L) => (g : Matrix (Fin 2) (Fin 2) (w'.adicCompletion L)) i j) (h₂ w')
    simpa only [finComponent_apply, glFin_apply] using h

private theorem placeAt_mul_eq_mul_placeAt (m : GL (Fin 2) (w.adicCompletion L)) {y : AdelicGL2 (𝓞 L) L}
    (hy : finComponent (𝓞 L) L w (glFin (𝓞 L) L y) = 1) : placeAt w m * y = y * placeAt w m := by
  refine adelicGL2_ext ?_ fun w' => ?_
  · simp only [map_mul, glArch_placeAt, one_mul, mul_one]
  · simp only [map_mul]
    by_cases h : w' = w
    · subst h
      rw [finComponent_glFin_placeAt_self, hy, mul_one, one_mul]
    · rw [finComponent_glFin_placeAt_of_ne w m h, one_mul, mul_one]

private theorem finComponent_glFin_mul_inv_placeAt (x : AdelicGL2 (𝓞 L) L) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L (x * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)))⁻¹)) = 1 := by
  simp only [map_mul, map_inv, finComponent_glFin_placeAt_self, mul_inv_cancel]

private theorem heckeGen_eq_placeAt :
    heckeGen (𝓞 L) L w = placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) := by
  refine adelicGL2_ext ?_ fun w' => ?_
  · rw [glArch_placeAt]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glArch_apply, Units.val_one]
    exact heckeGenAt_fst _ i j
  · by_cases h : w' = w
    · subst h
      rw [finComponent_glFin_placeAt_self]
    · rw [finComponent_glFin_placeAt_of_ne w _ h]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [finComponent_apply, glFin_apply, Units.val_one]
      exact heckeGenAt_snd_apply_of_ne _ h i j

private theorem normalise_aux {G : Type*} [Group G] {p q h y u₁ u₂ : G} (hy : y = u₁ * p⁻¹) (hq : q = p * h)
    (hcomm : q * y = y * q) : u₁ * h * u₂ = q * (y * u₂) := by
  subst hy
  calc u₁ * h * u₂ = (u₁ * p⁻¹) * (p * h) * u₂ := by group
    _ = (u₁ * p⁻¹) * q * u₂ := by rw [hq]
    _ = q * (u₁ * p⁻¹) * u₂ := by rw [← hcomm]
    _ = q * (u₁ * p⁻¹ * u₂) := by rw [mul_assoc]

private theorem mul_heckeGen_mul_eq (u₁ u₂ : AdelicGL2 (𝓞 L) L) :
    u₁ * heckeGen (𝓞 L) L w * u₂ =
      placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u₁) *
          finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) *
        ((u₁ * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u₁)))⁻¹) * u₂) :=
  normalise_aux rfl (by rw [map_mul, ← heckeGen_eq_placeAt])
    (placeAt_mul_eq_mul_placeAt _ (finComponent_glFin_mul_inv_placeAt u₁))

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) N w = 1)
    (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) (hM : ∀ i j, M i j ∈ w.adicCompletionIntegers L) :
    IsLocalLevelOne (𝓞 L) L w N M :=
  ⟨hM, by rw [hb]; exact hM 1 0, by rw [hb]; exact sub_mem (hM 1 1) (one_mem _)⟩

private theorem placeAt_mem_of_integral {N : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) N w = 1)
    (m : GL (Fin 2) (w.adicCompletion L))
    (hm : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L)
    (hm' : ∀ i j, ((m⁻¹ : GL (Fin 2) (w.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L) :
    placeAt w m ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m) ∈ levelOne (𝓞 L) L N
    rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    exact ⟨isLocalLevelOne_of_integral hb _ hm, isLocalLevelOne_of_integral hb _ hm'⟩
  · show glArch (𝓞 L) L (placeAt w m) = 1
    exact glArch_placeAt w m

private theorem finComponent_integral_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (i j : Fin 2) :
    (finComponent (𝓞 L) L w (glFin (𝓞 L) L k) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L := by
  rw [finComponent_apply]
  have h : (glFin (𝓞 L) L k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈ integralFiniteAdeles (𝓞 L) L :=
    (mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hk)).1.integral i j
  exact h w

private theorem finComponent_inv_integral_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (i j : Fin 2) :
    (((finComponent (𝓞 L) L w (glFin (𝓞 L) L k))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L := by
  rw [← map_inv, ← map_inv]
  exact finComponent_integral_of_mem_levelOne (inv_mem hk) i j

end OnePlace
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section Hecke

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem isHeckeCosetEigenfunctionAt_rightConv {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N w = 1) {tys : ArchTypeFamily L} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (hsupp : ∀ x : AdelicGL2 (𝓞 L) L, φ x ≠ 0 →
      (∀ i j, (finComponent (𝓞 L) L w (glFin (𝓞 L) L x) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
          w.adicCompletionIntegers L) ∧
      (∀ i j, (((finComponent (𝓞 L) L w (glFin (𝓞 L) L x))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L))
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hucont : Continuous u)
    (hinv : ∀ h : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, u (h * k) = u h)
    {a : ℂ}
    (heu : IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w) w
      u a) :
    IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w) w
      (rightConv L u φ) a := by
  obtain ⟨reps, hsys, heig⟩ := heu
  obtain ⟨hφc, hφs⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ (isFactorizableTestFn_of_tier hφ)
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

  have hdc : ∀ i, ∃ u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      ∃ u₂ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, u₁ * heckeGen (𝓞 L) L w * u₂ = reps i :=
    fun i => HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
  choose u₁ hu₁ u₂ hu₂ hrep using hdc

  obtain ⟨r, hr⟩ : ∃ r : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L, ∀ i,
      r i = placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i)) *
        finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L, ∀ i,
      s i = (u₁ i * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i))))⁻¹) * u₂ i :=
    ⟨_, fun _ => rfl⟩
  have hreps : reps = fun i => r i * s i := funext fun i => by
    show reps i = r i * s i
    rw [← hrep i, hr, hs]
    exact mul_heckeGen_mul_eq (u₁ i) (u₂ i)
  have hsU : ∀ i, s i ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := fun i => by
    rw [hs]
    have hp : placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i))) ∈
        levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
      placeAt_mem_of_integral hb _ (finComponent_integral_of_mem_levelOne (Subgroup.mem_inf.mp (hu₁ i)).1)
        (finComponent_inv_integral_of_mem_levelOne (Subgroup.mem_inf.mp (hu₁ i)).1)
    exact mul_mem (mul_mem (hu₁ i) (inv_mem hp)) (hu₂ i)

  have heig' : ∀ h : AdelicGL2 (𝓞 L) L, (∑ i, u (h * r i)) = a * u h := fun h => by
    have h1 := heig h
    rw [hreps, heckeCosetSum_mul_right L (fun g k hk => hinv g k hk) r s hsU h] at h1
    exact h1

  have hlevel : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      rightConv L u φ (g * k) = rightConv L u φ g := fun g k hk => rightConv_mul_eq_of_tier hφ u g hk

  have hL1 : ∀ h : AdelicGL2 (𝓞 L) L,
      Integrable (fun x => u (h * x) * φ x) (adelicGLHaar (Fin 2) (𝓞 L) L) := fun h =>
    ((hucont.comp (continuous_const.mul continuous_id)).mul hφc).integrable_of_hasCompactSupport hφs.mul_left

  have hpt : ∀ (g x : AdelicGL2 (𝓞 L) L), (∑ i, u (g * r i * x) * φ x) = a * (u (g * x) * φ x) := by
    intro g x
    by_cases hx : φ x = 0
    · simp only [hx, mul_zero, Finset.sum_const_zero]
    obtain ⟨hx₁, hx₂⟩ := hsupp x hx
    have hxw : placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)) ∈
        levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
      placeAt_mem_of_integral hb _ hx₁ hx₂

    obtain ⟨x', hx'⟩ : ∃ x' : AdelicGL2 (𝓞 L) L,
        x' = x * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)))⁻¹ := ⟨_, rfl⟩
    have hxx : x = x' * placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)) := by
      rw [hx', inv_mul_cancel_right]
    have hx'w : finComponent (𝓞 L) L w (glFin (𝓞 L) L x') = 1 := by
      rw [hx']
      exact finComponent_glFin_mul_inv_placeAt x
    have hterm : ∀ i, u (g * r i * x) = u (g * x' * r i) := fun i => by
      have hcr : r i * x' = x' * r i := by
        rw [hr]
        exact placeAt_mul_eq_mul_placeAt _ hx'w
      rw [hxx, ← mul_assoc, hinv _ _ hxw, mul_assoc, hcr, ← mul_assoc]
    rw [← Finset.sum_mul, ← mul_assoc]
    congr 1
    simp only [hterm]
    rw [heig' (g * x'), hxx, ← mul_assoc, hinv _ _ hxw]

  refine ⟨reps, hsys, fun g => ?_⟩
  have hsum : heckeCosetSum L reps (rightConv L u φ) g = heckeCosetSum L r (rightConv L u φ) g := by
    rw [hreps]
    exact heckeCosetSum_mul_right L (fun h k hk => hlevel h k hk) r s hsU g
  rw [hsum]
  show (∑ i, ∫ x, u (g * r i * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
    a * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
  have hswap : (∑ i, ∫ x, u (g * r i * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x, (∑ i, u (g * r i * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
    (integral_finsetSum Finset.univ fun i _ => hL1 (g * r i)).symm
  have hpt' : (∫ x, (∑ i, u (g * r i * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x, a * (u (g * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hpt g x)
  rw [hswap, hpt', integral_const_mul]

end Hecke
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end Q09StabH.ConvLeg
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end CONV2part
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section CONV3part

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm IsDedekindDomain MeasureTheory"
open scoped TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace Q09StabH
namespace ConvLeg

section Dictionary

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

private theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v (semiLocalEval K L v a) w = AdelicLevel.finAdeleEval (𝓞 L) L w.1 a := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w' : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w'.1 a)) w =
    AdelicLevel.finAdeleEval (𝓞 L) L w.1 a
  rw [AlgEquiv.apply_symm_apply]

private theorem forall_of_mem_semiLocalIntegers (t : L ⊗[K] v.adicCompletion K) (ht : t ∈ semiLocalIntegers K L v)
    (w : v.Extension (𝓞 L)) : semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi] at ht
  exact ht w

end Dictionary
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section Discharge

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem finComponent_integral_of_ne_zero {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w.under (𝓞 K) ∉ SK) (x : AdelicGL2 (𝓞 L) L) (hx : φ x ≠ 0) :
      (∀ i j, (finComponent (𝓞 L) L w (glFin (𝓞 L) L x) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
          w.adicCompletionIntegers L) ∧
      (∀ i j, (((finComponent (𝓞 L) L w (glFin (𝓞 L) L x))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L)
    := by
  obtain ⟨φa, φf, φS, -, -, -, -, h₅, h₆⟩ := hφ.1.2
  have hf : φf (glFin (𝓞 L) L x) ≠ 0 := fun h0 => hx (by rw [h₆ x, h0, mul_zero])
  have hmem : semiLocalComponent K L (w.under (𝓞 K)) (glFin (𝓞 L) L x) ∈
      semiLocalIntegralSet K L (w.under (𝓞 K)) := by
    by_contra hc
    exact hf (h₅ _ ⟨w.under (𝓞 K), hw, hc⟩)
  unfold semiLocalIntegralSet at hmem
  obtain ⟨hm, hm'⟩ := mem_integralUnitsSet.mp hmem

  let wE : {w' : HeightOneSpectrum (𝓞 L) // w'.under (𝓞 K) = w.under (𝓞 K)} := ⟨w, rfl⟩
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h : semiLocalHomeomorph K L (w.under (𝓞 K))
        (semiLocalEval K L (w.under (𝓞 K))
          ((glFin (𝓞 L) L x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) wE ∈
        w.adicCompletionIntegers L :=
      forall_of_mem_semiLocalIntegers K L (w.under (𝓞 K)) _ (hm i j) wE
    rw [semiLocalHomeomorph_semiLocalEval] at h
    exact h
  · have hm'' := hm' i j
    rw [← map_inv (semiLocalComponent K L (w.under (𝓞 K))) (glFin (𝓞 L) L x)] at hm''
    have h : semiLocalHomeomorph K L (w.under (𝓞 K))
        (semiLocalEval K L (w.under (𝓞 K))
          ((((glFin (𝓞 L) L x)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) wE ∈
        w.adicCompletionIntegers L :=
      forall_of_mem_semiLocalIntegers K L (w.under (𝓞 K)) _ hm'' wE
    rw [semiLocalHomeomorph_semiLocalEval] at h
    rw [← map_inv (finComponent (𝓞 L) L w) (glFin (𝓞 L) L x)]
    exact h

private theorem isIsotypicCuspFormAt_rightConv_of_tier
    (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (c' v' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 L) L)) (hd' : d₁' < d₂')
    (hcov' : CoversModCentre L (window L c' v' d₁' d₂' T'))
    (ξ : (pinsL L (window L c v d₁ d₂ T)).Z →* ℂˣ) (ξ' : (pinsL L (window L c' v' d₁' d₂' T')).Z →* ℂˣ)
    (hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' (toZ _ z) = ξ (toZ _ z))
    {NK : Ideal (𝓞 K)} (hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥)
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {SL : Finset (HeightOneSpectrum (𝓞 L))}
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ SK → w ∈ SL)
    (hbound : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      idealBound (𝓞 L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) w = 1)
    (Ψ : HeckeEigensystem L ℂ) {tys : ArchTypeFamily L} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ)
    {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : IsIsotypicCuspFormAt L (pinsL L (window L c' v' d₁' d₂' T')) ξ'
      (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ u) :
    IsIsotypicCuspFormAt L (pinsL L (window L c v d₁ d₂ T)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
      (rightConv L u φ) :=
  isIsotypicCuspFormAt_rightConv_of_hecke c v d₁ d₂ T hc hd₁ c' v' d₁' d₂' T' hd' hcov' ξ ξ' hξ hN SL Ψ hφ hu
    fun w hw =>
      isHeckeCosetEigenfunctionAt_rightConv (hbound w hw) hφ
        (fun x hx => finComponent_integral_of_ne_zero hφ (fun h => hw (hSL w h)) x hx)
        hu.continuous hu.level_invariant (hu.hecke_eigen w hw)

end Discharge
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section Arch

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem rightConv_mem_archCutSubmodule {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ)
    (hinj : ∀ w : InfinitePlace L, Function.Injective (rowIsometryInclAt₀ L w))
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : Continuous u) : rightConv L u φ ∈ archCutSubmodule L tys := by
  obtain ⟨hφc, hφs⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ (isFactorizableTestFn_of_tier hφ)
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  have hdom : (fun x => φ x⁻¹) ∈ Q09.convDomain (adelicGLHaar (Fin 2) (𝓞 L) L) u := by
    rw [Q09.mem_convDomain_iff]
    intro y
    simp only [inv_inv]
    exact ((hu.comp (continuous_const.mul continuous_id)).mul hφc).integrable_of_hasCompactSupport
      hφs.mul_left
  have hconv : Q09.convOpOn (adelicGLHaar (Fin 2) (𝓞 L) L) u ⟨fun x => φ x⁻¹, hdom⟩ = rightConv L u φ := by
    funext y
    rw [Q09.convOpOn_apply]
    show (∫ x, u (y * x) * (fun x => φ x⁻¹) x⁻¹ ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x, u (y * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
    simp only [inv_inv]
  rw [mem_archCutSubmodule_iff]
  intro w
  rw [← hconv]
  exact Q09.convOpOn_mem_iSup_typeSubmodule _ u (hinj w) (fun i => (tys.rep w i).ρ) _
    ((mem_archCutSubmodule_iff L tys _).mp hφ.2.1 w)

end Arch
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end Q09StabH.ConvLeg
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end CONV3part
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section

p2m_open "NumberField NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

namespace Q09RowIso

variable (F : Type) [Field F]

private theorem archComponent_archRowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (archRowIsometryInclAt₀ F w k) = (k : GL (Fin 2) w.Completion) :=
  archComponent_archGLIncl_self F w (k : GL (Fin 2) w.Completion)

private theorem archRowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (archRowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_archRowIsometryInclAt₀ F w a
  have hb := archComponent_archRowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

variable [NumberField F]

private theorem archComponent_glArch_rowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k))
      = (k : GL (Fin 2) w.Completion) := by
  rw [glArch_rowIsometryInclAt₀]
  exact archComponent_archRowIsometryInclAt₀ F w k

private theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_glArch_rowIsometryInclAt₀ F w a
  have hb := archComponent_glArch_rowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

private theorem forall_rowIsometryInclAt₀_injective :
    ∀ w : InfinitePlace F, Function.Injective (rowIsometryInclAt₀ F w) :=
  rowIsometryInclAt₀_injective F

end Q09RowIso
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section T3ppGlue

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

namespace Q09StabH

variable {L : Type} [Field L] [NumberField L]

private theorem convOp_mem_isotypicCuspSubmodule_of_forms {pins : CarrierPins L} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 L)} {S : Finset (HeightOneSpectrum (𝓞 L))} {Ψ : HeckeEigensystem L ℂ}
    {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hconv : ∀ v : AdelicGL2 (𝓞 L) L → ℂ, IsIsotypicCuspFormAt L pins ξ N S Ψ v →
      IsIsotypicCuspFormAt L pins ξ N S Ψ (rightConv L v φ))
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ∈ isotypicCuspSubmodule L pins ξ N S Ψ) :
    convOp L φ u ∈ isotypicCuspSubmodule L pins ξ N S Ψ := by
  refine Submodule.span_induction (p := fun u _ => convOp L φ u ∈ isotypicCuspSubmodule L pins ξ N S Ψ)
    ?_ ?_ ?_ ?_ hu
  · intro g hg
    rw [convOp_apply]
    exact (hconv g hg).mem_isotypicCuspSubmodule
  · simp only [convOp_zero, Submodule.zero_mem]
  · intro x y hx hy ihx ihy
    rw [convOp_add (K := L) hφc hφs (continuous_of_mem_isotypicCuspSubmodule hx)
      (continuous_of_mem_isotypicCuspSubmodule hy)]
    exact Submodule.add_mem _ ihx ihy
  · intro a x _ ih
    rw [convOp_smul]
    exact Submodule.smul_mem _ a ih

end Q09StabH
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end T3ppGlue
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hdL : d₁L < d₂L) (hcL : 0 < cL) (hd₁L : 0 < d₁L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (ξL : (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ)
    (tysL : ArchTypeFamily L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsUnitFactorizableAboveOfType K L tysL
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ) :
    ∀ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL,
      convOp L φ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL := by
  intro u hu
  rw [Submodule.mem_inf] at hu ⊢
  have hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ :=
    AutomorphicForm.LevelFiniteFactor.map_algebraMap_ne_bot
      (AutomorphicForm.LevelFiniteFactor.ne_bot_of_forall_dvd_mem hNS)
  obtain ⟨hφc, hφs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ
    (Q09StabH.ConvLeg.isFactorizableTestFn_of_tier hφ)
  refine ⟨Q09StabH.convOp_mem_isotypicCuspSubmodule_of_forms hφc hφs (fun v hv => ?_) hu.1, ?_⟩
  · exact Q09StabH.ConvLeg.isIsotypicCuspFormAt_rightConv_of_tier cL uL d₁L d₂L TL hcL hd₁L cL uL d₁L d₂L TL hdL
      hcovL ξL ξL (fun _ => rfl) hN hSL (fun w hw => Q09StabH.idealBound_map_eq_one_of_not_mem hSL hNS hN hw) Ψ hφ hv
  · rw [AutomorphicForm.convOp_apply]
    exact Q09StabH.ConvLeg.rightConv_mem_archCutSubmodule hφ (Q09RowIso.rowIsometryInclAt₀_injective L)
      (AutomorphicForm.continuous_of_mem_isotypicCuspSubmodule hu.1)

end
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
end P2MW
export P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType (solution)
