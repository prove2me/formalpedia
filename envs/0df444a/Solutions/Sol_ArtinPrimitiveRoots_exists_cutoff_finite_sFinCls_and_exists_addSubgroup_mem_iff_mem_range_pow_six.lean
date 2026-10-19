-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_finite_sFinCls_and_exists_addSubgroup_mem_iff_mem_range_pow_six
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T09:15:52.114817+00:00
-- url     : https://prove2.me/submissions/d855723b-2d97-45cf-9fb8-0822c0603c5f

import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_M4aHerbrand_prod_idelicArtinMap_single_eq_one
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
import Theorems.Thm_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_NumberField_denseRange_algebraMap_pi_adicCompletion
import Theorems.Thm_NumberField_isOpen_range_powMonoidHom_units_adicCompletion
import Theorems.Thm_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Theorems.Thm_NumberField_exists_pow_eq_of_forall_mem_range_powMonoidHom
import Theorems.Thm_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top
import Definitions.Def_ArtinHeckeSModel
import Mathlib

section
section
/-! C0Z: the library's idelic Artin map for an abelian extension, and ideles at one place. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

/-! ### Generic part: any abelian extension `K/E` of `Type`-level number fields -/

section Generic

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
  [IsGalois E K]

/-- Ramified primes divide a fixed nonzero ideal (to be proved from the different). -/
theorem exists_ramified_dvd :
    ∃ 𝔣 : Ideal (𝓞 E), 𝔣 ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 E),
      (primeAbove E K v).inertia (K ≃ₐ[E] K) ≠ ⊥ → v.asIdeal ∣ 𝔣 := by
  classical
  have hD : differentIdeal (𝓞 E) (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  refine ⟨(differentIdeal (𝓞 E) (𝓞 K)).comap (algebraMap (𝓞 E) (𝓞 K)), ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · intro v hv
    have hP : primeAbove E K v ∣ differentIdeal (𝓞 E) (𝓞 K) := by
      rw [dvd_differentIdeal_iff]
      intro hun
      apply hv
      have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[E] K) v.asIdeal (primeAbove E K v)
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove E K v) (K ≃ₐ[E] K),
        Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at h1
      exact Subgroup.eq_bot_of_card_eq _ h1
    rw [Ideal.dvd_iff_le] at hP ⊢
    calc (differentIdeal (𝓞 E) (𝓞 K)).comap (algebraMap (𝓞 E) (𝓞 K))
        ≤ (primeAbove E K v).comap (algebraMap (𝓞 E) (𝓞 K)) := Ideal.comap_mono hP
      _ = v.asIdeal := under_primeAbove E K v

theorem exists_admissible :
    ∃ 𝔣 : Ideal (𝓞 E), NumberField.NormIndex.IsAdmissibleModulusOfDegree E K
      (Module.finrank E K) 𝔣 := by
  obtain ⟨𝔣, h0, hram⟩ := exists_ramified_dvd E K
  obtain ⟨𝔣', -, -, h⟩ :=
    exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E K 𝔣 h0 hram (Module.finrank E K)
  exact ⟨𝔣', h⟩

/-- The four defining properties of the idelic Artin map, as the library states them. -/
def IsIdelicArtin [IsMulCommutative (K ≃ₐ[E] K)] (𝔣 : Ideal (𝓞 E))
    (r : (AdeleRing (𝓞 E) E)ˣ →* (K ≃ₐ[E] K)) : Prop :=
  principalIdeles (𝓞 E) E ≤ r.ker ∧
  r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E K).idelicNorm.range ∧
  Function.Surjective r ∧
  ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
    r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E K v ^ placeOrd E (projFin E u) v

theorem exists_idelicArtin [IsMulCommutative (K ≃ₐ[E] K)] :
    ∃ 𝔣 r, NumberField.NormIndex.IsAdmissibleModulusOfDegree E K (Module.finrank E K) 𝔣 ∧
      IsIdelicArtin E K 𝔣 r := by
  obtain ⟨𝔣, h𝔣⟩ := exists_admissible E K
  obtain ⟨r, h1, h2, h3, h4⟩ :=
    exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
      E K 𝔣 h𝔣
  exact ⟨𝔣, r, h𝔣, h1, h2, h3, h4⟩

/-- Chosen modulus and Artin map. -/
def artinMod [IsMulCommutative (K ≃ₐ[E] K)] : Ideal (𝓞 E) := (exists_idelicArtin E K).choose
def artinMap [IsMulCommutative (K ≃ₐ[E] K)] : (AdeleRing (𝓞 E) E)ˣ →* (K ≃ₐ[E] K) :=
  (exists_idelicArtin E K).choose_spec.choose
theorem artinMap_spec [IsMulCommutative (K ≃ₐ[E] K)] :
    NumberField.NormIndex.IsAdmissibleModulusOfDegree E K (Module.finrank E K) (artinMod E K) ∧
      IsIdelicArtin E K (artinMod E K) (artinMap E K) :=
  (exists_idelicArtin E K).choose_spec.choose_spec

/-- No infinite place of `K` has a nontrivial decomposition group when `E` is totally complex. -/
theorem hinf_of_isTotallyComplex (hcx : ∀ v : InfinitePlace E, v.IsComplex) :
    ∀ (w : InfinitePlace K) (g : K ≃ₐ[E] K), g ∈ NumberField.InfPlaceDecomp.decomp E K w → g = 1 := by
  intro w g hg
  have hun : w.IsUnramified E :=
    InfinitePlace.isUnramified_iff.mpr (Or.inr (hcx _))
  have hcard := (InfinitePlace.isUnramified_iff_card_stabilizer_eq_one (k := E)).mp hun
  have : Subsingleton (MulAction.stabilizer (K ≃ₐ[E] K) w) := by
    exact ((Nat.card_eq_one_iff_unique).mp hcard).1
  exact congrArg Subtype.val (Subsingleton.elim (⟨g, hg⟩ : MulAction.stabilizer (K ≃ₐ[E] K) w) 1)

end Generic

/-! ### The idele supported at one finite place -/

section Single

variable (E : Type) [Field E] [NumberField E]

open scoped Classical

/-- The finite adele equal to `x` at `v` and `1` elsewhere. -/
def fsingle (v : HeightOneSpectrum (𝓞 E)) (x : v.adicCompletion E) : FiniteAdeleRing (𝓞 E) E :=
  RestrictedProduct.mulSingle _ v x

theorem fsingle_apply (v w : HeightOneSpectrum (𝓞 E)) (x : v.adicCompletion E) :
    (fsingle E v x) w = Pi.mulSingle (M := fun w => w.adicCompletion E) v x w := rfl

theorem fsingle_mul (v : HeightOneSpectrum (𝓞 E)) (x y : v.adicCompletion E) :
    fsingle E v x * fsingle E v y = fsingle E v (x * y) := by
  apply RestrictedProduct.ext
  intro w
  show (fsingle E v x) w * (fsingle E v y) w = (fsingle E v (x * y)) w
  rw [fsingle_apply, fsingle_apply, fsingle_apply, Pi.mulSingle_mul]
  rfl

theorem fsingle_one (v : HeightOneSpectrum (𝓞 E)) : fsingle E v 1 = 1 := by
  apply RestrictedProduct.ext
  intro w
  show (fsingle E v 1) w = 1
  rw [fsingle_apply, Pi.mulSingle_one]; rfl

/-- `single v z`: the idele equal to `z` at `v` and `1` at every other place. -/
def single (v : HeightOneSpectrum (𝓞 E)) : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ where
  toFun z :=
    { val := (1, fsingle E v (z : v.adicCompletion E))
      inv := (1, fsingle E v ((z⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E))
      val_inv := by
        refine Prod.ext (mul_one _) ?_
        show fsingle E v _ * fsingle E v _ = 1
        rw [fsingle_mul, Units.mul_inv, fsingle_one]
      inv_val := by
        refine Prod.ext (mul_one _) ?_
        show fsingle E v _ * fsingle E v _ = 1
        rw [fsingle_mul, Units.inv_mul, fsingle_one] }
  map_one' := by
    apply Units.ext
    refine Prod.ext rfl ?_
    show fsingle E v 1 = 1
    exact fsingle_one E v
  map_mul' z z' := by
    apply Units.ext
    refine Prod.ext (mul_one _).symm ?_
    show fsingle E v ((z * z' : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      fsingle E v (z : v.adicCompletion E) * fsingle E v (z' : v.adicCompletion E)
    rw [fsingle_mul, Units.val_mul]

theorem finPart_single (v : HeightOneSpectrum (𝓞 E)) (z : (v.adicCompletion E)ˣ) :
    finPart v (single E v z) = z := by
  apply Units.ext
  show (fsingle E v (z : v.adicCompletion E)) v = z
  rw [fsingle_apply, Pi.mulSingle_eq_same]

theorem single_mem (v : HeightOneSpectrum (𝓞 E)) (z : (v.adicCompletion E)ˣ) :
    single E v z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) := by
  refine ⟨?_, fun w hw => ?_⟩
  · exact Units.ext rfl
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    apply Units.ext
    show (fsingle E v (z : v.adicCompletion E)) w = 1
    rw [fsingle_apply, Pi.mulSingle_eq_of_ne hw]

end Single

end C0Z

end
end
end

section
section
/-! C0Z: Kummer characters `σ ↦ σβ/β ∈ μ_ℓ(F)` for any Galois extension `M/F` and any
`β ∈ Mˣ` with `β^ℓ ∈ F`, when `μ_ℓ ⊂ F`; Kummer fields. -/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace C0Z

variable {F : Type} [Field F] {ℓ : ℕ} [NeZero ℓ]

/-- Every `ℓ`-th root of unity of an `F`-field comes from `F`. -/
theorem exists_of_pow_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
    (x : M) (hx : x ^ ℓ = 1) : ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = x := by
  have hζM := hζ.map_of_injective (FaithfulSMul.algebraMap_injective F M)
  obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], by rw [map_pow, hi]⟩

variable {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
include hζ

/-- A Kummer generator: a nonzero `β` with `β^ℓ ∈ F`. -/
structure KGen (M : Type*) [Field M] [Algebra F M] (ℓ : ℕ) where
  β : M
  ne_zero : β ≠ 0
  pow_mem : ∃ a : F, β ^ ℓ = algebraMap F M a

variable {M}

theorem ratio_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : (σ g.β / g.β) ^ ℓ = 1 := by
  obtain ⟨a, ha⟩ := g.pow_mem
  rw [div_pow, ← map_pow, ha, AlgEquiv.commutes, ← ha, div_self (pow_ne_zero _ g.ne_zero)]

theorem ratio_mem (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = σ g.β / g.β :=
  exists_of_pow_eq_one hζ M _ (ratio_pow hζ g σ)

/-- The value of the Kummer character in `F`. -/
def kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : F := (ratio_mem hζ g σ).choose

theorem kval_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : kval hζ g σ ^ ℓ = 1 :=
  (ratio_mem hζ g σ).choose_spec.1

theorem algebraMap_kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M (kval hζ g σ) = σ g.β / g.β :=
  (ratio_mem hζ g σ).choose_spec.2

theorem fix_ratio (g : KGen (F := F) M ℓ) (σ τ : M ≃ₐ[F] M) :
    σ (τ g.β / g.β) = τ g.β / g.β := by
  rw [← algebraMap_kval hζ g τ, AlgEquiv.commutes]

/-- The Kummer character `σ ↦ σβ/β`, valued in `μ_ℓ(F)`. -/
def kch (g : KGen (F := F) M ℓ) : (M ≃ₐ[F] M) →* rootsOfUnity ℓ F where
  toFun σ := rootsOfUnity.mkOfPowEq (kval hζ g σ) (kval_pow hζ g σ)
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, OneMemClass.coe_one, Units.val_one]
    apply FaithfulSMul.algebraMap_injective F M
    rw [algebraMap_kval hζ, map_one, AlgEquiv.one_apply, div_self g.ne_zero]
  map_mul' σ τ := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, Subgroup.coe_mul, Units.val_mul]
    apply FaithfulSMul.algebraMap_injective F M
    rw [map_mul, algebraMap_kval hζ, algebraMap_kval hζ, algebraMap_kval hζ, AlgEquiv.mul_apply]
    have h1 : τ g.β = (τ g.β / g.β) * g.β := by field_simp [g.ne_zero]
    conv_lhs => rw [h1, map_mul, fix_ratio hζ g σ τ]
    field_simp [g.ne_zero]

theorem algebraMap_kch (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M ((kch hζ g σ : Fˣ) : F) = σ g.β / g.β := by
  simp only [kch, MonoidHom.coe_mk, OneHom.coe_mk, rootsOfUnity.coe_mkOfPowEq]
  exact algebraMap_kval hζ g σ

theorem kch_eq_iff (g g' : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    kch hζ g σ = kch hζ g' σ ↔ σ g.β / g.β = σ g'.β / g'.β := by
  rw [← algebraMap_kch hζ, ← algebraMap_kch hζ]
  constructor
  · intro h; rw [h]
  · intro h
    apply Subtype.ext; apply Units.ext
    exact FaithfulSMul.algebraMap_injective F M h

/-- Product of generators. -/
def KGen.mul (g g' : KGen (F := F) M ℓ) : KGen (F := F) M ℓ where
  β := g.β * g'.β
  ne_zero := mul_ne_zero g.ne_zero g'.ne_zero
  pow_mem := by
    obtain ⟨a, ha⟩ := g.pow_mem
    obtain ⟨a', ha'⟩ := g'.pow_mem
    exact ⟨a * a', by rw [mul_pow, ha, ha', map_mul]⟩

theorem kch_mul (g g' : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    kch hζ (g.mul g') σ = kch hζ g σ * kch hζ g' σ := by
  apply Subtype.ext; apply Units.ext
  apply FaithfulSMul.algebraMap_injective F M
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_kch hζ]
  simp only [KGen.mul, map_mul]
  field_simp [g.ne_zero, g'.ne_zero]

/-- The character depends only on `β^ℓ`. -/
theorem kch_eq_of_pow_eq (g g' : KGen (F := F) M ℓ) (h : g.β ^ ℓ = g'.β ^ ℓ) :
    kch hζ g = kch hζ g' := by
  ext σ
  have := (kch_eq_iff hζ g g' σ).mpr
  rw [this]
  have hr : (g'.β / g.β) ^ ℓ = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ g'.ne_zero)]
  obtain ⟨y, -, hy⟩ := exists_of_pow_eq_one hζ M _ hr
  have hg' : g'.β = algebraMap F M y * g.β := by rw [hy]; field_simp [g.ne_zero]
  rw [hg', map_mul, AlgEquiv.commutes]
  have hy0 : algebraMap F M y ≠ 0 := by
    rw [hy]; exact div_ne_zero g'.ne_zero g.ne_zero
  field_simp [g.ne_zero, hy0]

/-- Restriction to a normal subextension. -/
theorem kch_restrict (L : Type*) [Field L] [Algebra F L] [Algebra L M] [IsScalarTower F L M]
    [Normal F L] (g : KGen (F := F) L ℓ) (σ : M ≃ₐ[F] M) :
    kch hζ g (AlgEquiv.restrictNormalHom L σ) =
      kch hζ (M := M) ⟨algebraMap L M g.β, by simpa using g.ne_zero, by
        obtain ⟨a, ha⟩ := g.pow_mem
        exact ⟨a, by rw [← map_pow, ha, ← IsScalarTower.algebraMap_apply]⟩⟩ σ := by
  apply Subtype.ext; apply Units.ext
  apply FaithfulSMul.algebraMap_injective F M
  rw [IsScalarTower.algebraMap_apply F L M, algebraMap_kch hζ, algebraMap_kch hζ, map_div₀]
  congr 1
  exact AlgEquiv.restrictNormal_commutes σ L g.β

end C0Z

end
end
end

section
section
/-! C0Z: the Kummer fields `F(a^{1/ℓ})` and `F(a^{1/ℓ}, a'^{1/ℓ})` as splitting fields. -/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace C0Z

variable (F : Type) [Field F] (ℓ : ℕ)

/-- `F(a^{1/ℓ})`. -/
def KF (a : Fˣ) : Type := (X ^ ℓ - C (a : F)).SplittingField

/-- `F(a^{1/ℓ}, a'^{1/ℓ})`. -/
def KF2 (a a' : Fˣ) : Type := ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))).SplittingField

variable (a a' : Fˣ)

instance : Field (KF F ℓ a) := inferInstanceAs (Field (SplittingField _))
instance : Algebra F (KF F ℓ a) := inferInstanceAs (Algebra F (SplittingField _))
instance : Field (KF2 F ℓ a a') := inferInstanceAs (Field (SplittingField _))
instance : Algebra F (KF2 F ℓ a a') := inferInstanceAs (Algebra F (SplittingField _))
instance : IsSplittingField F (KF F ℓ a) (X ^ ℓ - C (a : F)) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance : IsSplittingField F (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance : FiniteDimensional F (KF F ℓ a) := IsSplittingField.finiteDimensional _ (X ^ ℓ - C (a : F))
instance : FiniteDimensional F (KF2 F ℓ a a') :=
  IsSplittingField.finiteDimensional _ ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
instance : Normal F (KF F ℓ a) := Normal.of_isSplittingField (X ^ ℓ - C (a : F))
instance : Normal F (KF2 F ℓ a a') :=
  Normal.of_isSplittingField ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))

section CharZero

variable [CharZero F]

instance : IsGalois F (KF F ℓ a) := { }
instance : IsGalois F (KF2 F ℓ a a') := { }

end CharZero

instance [NumberField F] : NumberField (KF F ℓ a) := NumberField.of_module_finite F _
instance [NumberField F] : NumberField (KF2 F ℓ a a') := NumberField.of_module_finite F _

variable {F ℓ}

theorem exists_root_of_splits {M : Type*} [Field M] [Algebra F M] (hℓ : ℓ ≠ 0)
    (hs : Splits ((X ^ ℓ - C (a : F)).map (algebraMap F M))) : ∃ β : M, β ^ ℓ = algebraMap F M a := by
  have hdeg : ((X ^ ℓ - C (a : F)).map (algebraMap F M)).degree ≠ 0 := by
    rw [degree_map]
    exact degree_ne_of_natDegree_ne (by rw [natDegree_X_pow_sub_C]; exact hℓ)
  obtain ⟨β, hβ⟩ := hs.exists_eval_eq_zero hdeg
  refine ⟨β, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
    eval_C] at hβ
  exact sub_eq_zero.mp hβ

/-- A Kummer generator from a root of `X^ℓ - a`. -/
def kgenOf {M : Type*} [Field M] [Algebra F M] {β : M} (hβ : β ^ ℓ = algebraMap F M a)
    (hℓ : ℓ ≠ 0) : KGen (F := F) M ℓ where
  β := β
  ne_zero := by
    rintro rfl
    rw [zero_pow hℓ, eq_comm, map_eq_zero] at hβ
    exact a.ne_zero hβ
  pow_mem := ⟨a, hβ⟩

theorem splits_KF (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a : F)).map (algebraMap F (KF F ℓ a))) :=
  IsSplittingField.splits (KF F ℓ a) (X ^ ℓ - C (a : F))

theorem ne_zero_X_pow_sub_C (hℓ : ℓ ≠ 0) : (X ^ ℓ - C (a : F)) ≠ 0 :=
  X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hℓ) _

theorem splits_KF2_left (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a : F)).map (algebraMap F (KF2 F ℓ a a'))) := by
  have h := IsSplittingField.splits (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
  refine h.of_dvd ?_ (Polynomial.map_dvd _ (dvd_mul_right _ _))
  rw [Polynomial.map_ne_zero_iff (algebraMap F _).injective]
  exact mul_ne_zero (ne_zero_X_pow_sub_C a hℓ) (ne_zero_X_pow_sub_C a' hℓ)

theorem splits_KF2_right (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a' : F)).map (algebraMap F (KF2 F ℓ a a'))) := by
  have h := IsSplittingField.splits (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
  refine h.of_dvd ?_ (Polynomial.map_dvd _ (dvd_mul_left _ _))
  rw [Polynomial.map_ne_zero_iff (algebraMap F _).injective]
  exact mul_ne_zero (ne_zero_X_pow_sub_C a hℓ) (ne_zero_X_pow_sub_C a' hℓ)

theorem root_pow_of_mem_rootSet {M : Type*} [Field M] [Algebra F M] {b : F} {r : M}
    (hr : aeval r (X ^ ℓ - C b) = 0) : r ^ ℓ = algebraMap F M b := by
  simpa [sub_eq_zero] using hr

section Comm

variable [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
include hζ

/-- A root of `X^ℓ - a` is a multiple of a fixed generator by an element of `F`. -/
theorem eq_smul_of_pow_eq {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ) {r : M}
    (hr : r ^ ℓ = g.β ^ ℓ) : ∃ c : F, r = algebraMap F M c * g.β := by
  have h1 : (r / g.β) ^ ℓ = 1 := by rw [div_pow, hr, div_self (pow_ne_zero _ g.ne_zero)]
  obtain ⟨c, -, hc⟩ := exists_of_pow_eq_one hζ M _ h1
  exact ⟨c, by rw [hc]; field_simp [g.ne_zero]⟩

theorem fixes_of_kch_eq_one {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : kch hζ g σ = 1) : σ g.β = g.β := by
  have := algebraMap_kch hζ g σ
  rw [h, OneMemClass.coe_one, Units.val_one, map_one, eq_comm, div_eq_one_iff_eq g.ne_zero] at this
  exact this

theorem fixes_root {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : σ g.β = g.β) {r : M} (hr : r ^ ℓ = g.β ^ ℓ) : σ r = r := by
  obtain ⟨c, rfl⟩ := eq_smul_of_pow_eq hζ g hr
  rw [map_mul, AlgEquiv.commutes, h]

/-- The Galois group of `F(a^{1/ℓ}, a'^{1/ℓ})/F` is abelian. -/
theorem isMulCommutative_KF2 : IsMulCommutative (KF2 F ℓ a a' ≃ₐ[F] KF2 F ℓ a a') := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨β, hβ⟩ := exists_root_of_splits a hℓ (splits_KF2_left a a' hℓ)
  obtain ⟨β', hβ'⟩ := exists_root_of_splits a' hℓ (splits_KF2_right a a' hℓ)
  let g := kgenOf a hβ hℓ
  let g' := kgenOf a' hβ' hℓ
  have hinj : ∀ σ : KF2 F ℓ a a' ≃ₐ[F] KF2 F ℓ a a', kch hζ g σ = 1 → kch hζ g' σ = 1 → σ = 1 := by
    intro σ h1 h2
    have f1 := fixes_of_kch_eq_one hζ g σ h1
    have f2 := fixes_of_kch_eq_one hζ g' σ h2
    apply AlgEquiv.coe_toAlgHom_injective
    refine AlgHom.ext_of_adjoin_eq_top
      (IsSplittingField.adjoin_rootSet (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))))
      fun r hr => ?_
    rw [mem_rootSet] at hr
    show σ r = r
    rw [map_mul, mul_eq_zero] at hr
    rcases hr.2 with h | h
    · exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet h]; exact hβ.symm)
    · exact fixes_root hζ g' σ f2 (by rw [root_pow_of_mem_rootSet h]; exact hβ'.symm)
  refine ⟨⟨fun σ τ => ?_⟩⟩
  have : σ * τ * (τ * σ)⁻¹ = 1 := hinj _
    (by rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, mul_comm])
    (by rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, mul_comm])
  exact mul_inv_eq_one.mp this

/-- The Galois group of `F(a^{1/ℓ})/F` is abelian. -/
theorem isMulCommutative_KF : IsMulCommutative (KF F ℓ a ≃ₐ[F] KF F ℓ a) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨β, hβ⟩ := exists_root_of_splits a hℓ (splits_KF a hℓ)
  let g := kgenOf a hβ hℓ
  have hinj : ∀ σ : KF F ℓ a ≃ₐ[F] KF F ℓ a, kch hζ g σ = 1 → σ = 1 := by
    intro σ h1
    have f1 := fixes_of_kch_eq_one hζ g σ h1
    apply AlgEquiv.coe_toAlgHom_injective
    refine AlgHom.ext_of_adjoin_eq_top
      (IsSplittingField.adjoin_rootSet (KF F ℓ a) (X ^ ℓ - C (a : F))) fun r hr => ?_
    rw [mem_rootSet] at hr
    show σ r = r
    exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet hr.2]; exact hβ.symm)
  refine ⟨⟨fun σ τ => ?_⟩⟩
  have : σ * τ * (τ * σ)⁻¹ = 1 := hinj _
    (by rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, mul_comm])
  exact mul_inv_eq_one.mp this

theorem eq_one_of_kch_KF (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a)
    (h : kch hζ g σ = 1) : σ = 1 := by
  have f1 := fixes_of_kch_eq_one hζ g σ h
  apply AlgEquiv.coe_toAlgHom_injective
  refine AlgHom.ext_of_adjoin_eq_top
    (IsSplittingField.adjoin_rootSet (KF F ℓ a) (X ^ ℓ - C (a : F))) fun r hr => ?_
  rw [mem_rootSet] at hr
  show σ r = r
  exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet hr.2]; exact hg.symm)

theorem kch_KF_injective (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) : Function.Injective (kch hζ g) :=
  (injective_iff_map_eq_one _).mpr fun σ h => eq_one_of_kch_KF a hζ g hg σ h

end Comm

end C0Z

end
end
end

section
section
/-! C0Z: the local Kummer symbol `(a, b)_v ∈ μ_ℓ(F)` from the idelic Artin map, and its
multiplicativity in `a`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- The chosen root of `X^ℓ - a` in `F(a^{1/ℓ})`. -/
def rootKF (a : Fˣ) : KGen (F := F) (KF F ℓ a) ℓ :=
  kgenOf a (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
    (NeZero.ne ℓ)

/-- The local symbol `(a, ·)_v : F_vˣ → μ_ℓ(F)`. -/
def sym (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) : (v.adicCompletion F)ˣ →* rootsOfUnity ℓ F :=
  haveI := isMulCommutative_KF a hζ
  (kch hζ (rootKF F a)).comp ((artinMap F (KF F ℓ a)).comp (single F v))

/-- The symbol can be computed in any abelian extension `M ⊇ F(a^{1/ℓ})`, with any root of
`X^ℓ - a` in `M`. -/
theorem sym_eq_of_le (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (M : Type) [Field M] [NumberField M]
    [Algebra F M] [IsGalois F M] [IsMulCommutative (M ≃ₐ[F] M)] (ι : KF F ℓ a →ₐ[F] M)
    (g : KGen (F := F) M ℓ) (hg : g.β ^ ℓ = algebraMap F M a) (b : (v.adicCompletion F)ˣ) :
    sym F hζ v a b = kch hζ g (artinMap F M (single F v b)) := by
  haveI := isMulCommutative_KF a hζ
  letI : Algebra (KF F ℓ a) M := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F (KF F ℓ a) M := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec F M
  obtain ⟨h𝔣L, hL1, hL2, hL3, hL4⟩ := artinMap_spec F (KF F ℓ a)
  have hres := restrictNormalHom_idelicArtinMap_eq F M (KF F ℓ a) _ h𝔣 _ h1 h2 h3 h4 _ h𝔣L _
    hL1 hL2 hL3 hL4 (single F v b)
  simp only [sym, MonoidHom.coe_comp, Function.comp_apply]
  rw [← hres, kch_restrict hζ (KF F ℓ a) (rootKF F a)]
  rw [kch_eq_of_pow_eq hζ _ g ?_]
  show (algebraMap (KF F ℓ a) M (rootKF F a).β) ^ ℓ = g.β ^ ℓ
  have : (rootKF F a).β ^ ℓ = algebraMap F (KF F ℓ a) a :=
    (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
  rw [← map_pow, this, ← IsScalarTower.algebraMap_apply, hg]

theorem sym_mul (v : HeightOneSpectrum (𝓞 F)) (a a' : Fˣ) (b : (v.adicCompletion F)ˣ) :
    sym F hζ v (a * a') b = sym F hζ v a b * sym F hζ v a' b := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  haveI := isMulCommutative_KF2 a a' hζ
  obtain ⟨β, hβ⟩ := exists_root_of_splits a hℓ (splits_KF2_left a a' hℓ)
  obtain ⟨β', hβ'⟩ := exists_root_of_splits a' hℓ (splits_KF2_right a a' hℓ)
  let g := kgenOf a hβ hℓ
  let g' := kgenOf a' hβ' hℓ
  have hgg : (g.mul g').β ^ ℓ = algebraMap F (KF2 F ℓ a a') ((a * a' : Fˣ) : F) := by
    show (β * β') ^ ℓ = _
    rw [mul_pow, hβ, hβ', Units.val_mul, map_mul]
  have hs3 : Splits ((X ^ ℓ - C ((a * a' : Fˣ) : F)).map (algebraMap F (KF2 F ℓ a a'))) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (FaithfulSMul.algebraMap_injective F (KF2 F ℓ a a'))) hgg
  let ι1 := IsSplittingField.lift (KF F ℓ a) (X ^ ℓ - C (a : F)) (splits_KF2_left a a' hℓ)
  let ι2 := IsSplittingField.lift (KF F ℓ a') (X ^ ℓ - C (a' : F)) (splits_KF2_right a a' hℓ)
  let ι3 := IsSplittingField.lift (KF F ℓ (a * a')) (X ^ ℓ - C ((a * a' : Fˣ) : F)) hs3
  rw [sym_eq_of_le F hζ v (a * a') (KF2 F ℓ a a') ι3 (g.mul g') hgg,
    sym_eq_of_le F hζ v a (KF2 F ℓ a a') ι1 g hβ, sym_eq_of_le F hζ v a' (KF2 F ℓ a a') ι2 g' hβ',
    kch_mul]

/-- The local symbol as a pairing `Fˣ × F_vˣ → μ_ℓ(F)`. -/
def symHom (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* (v.adicCompletion F)ˣ →* rootsOfUnity ℓ F where
  toFun a := sym F hζ v a
  map_one' := by
    ext b
    have h := sym_mul F hζ v 1 1 b
    rw [one_mul] at h
    have : sym F hζ v 1 b = 1 := by
      have h' : sym F hζ v 1 b * sym F hζ v 1 b = sym F hζ v 1 b * 1 := by rw [mul_one, ← h]
      exact mul_left_cancel h'
    rw [this]; rfl
  map_mul' a a' := by ext b; simp only [MonoidHom.mul_apply]; rw [sym_mul]

@[simp] theorem symHom_apply (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (b : (v.adicCompletion F)ˣ) :
    symHom F hζ v a b = sym F hζ v a b := rfl

end C0Z

end
end
end

section
section
/-! C0Y: the local-symbol package and the `S`-pairing built from it. -/

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace C0Y

variable (F : Type) [Field F] [NumberField F]

/-- The embedding `Fˣ → F_vˣ`. -/
def emb (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F) : F →* v.adicCompletion F)

/-- The properties of the local `ℓ`-th Hilbert symbols used for C0-H. -/
structure SymbolPkg (ℓ : ℕ) where
  h : (v : HeightOneSpectrum (𝓞 F)) → Fˣ →* (v.adicCompletion F)ˣ →* rootsOfUnity ℓ F
  steinberg : ∀ v (a : Fˣ), h v a (emb F v (-a)) = 1
  prod_eq_one : ∀ (a b : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ v ∉ T, h v a (emb F v b) = 1) → ∏ v ∈ T, h v a (emb F v b) = 1
  nondeg : ∀ v (a : Fˣ), (∀ b, h v a b = 1) →
    emb F v a ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range
  unit_unit : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∉ v.asIdeal → ∀ a b : Fˣ,
    v.valuation F (a : F) = 1 → v.valuation F (b : F) = 1 → h v a (emb F v b) = 1
  tame : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∉ v.asIdeal → ∀ (a π : Fˣ) (ω : F),
    v.valuation F (a : F) = 1 → v.valuation F (π : F) = WithZero.exp (-1 : ℤ) → ω ^ ℓ = 1 →
    v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / ℓ) - ω) < 1 →
    (((h v a (emb F v π) : Fˣ)) : F) = ω

variable {F} {ℓ : ℕ} (P : SymbolPkg F ℓ)

/-- The symbol at `v` restricted to global elements, as a pairing on `Fˣ`. -/
def SymbolPkg.hv (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* Fˣ →* rootsOfUnity ℓ F where
  toFun a := (P.h v a).comp (emb F v)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem SymbolPkg.hv_apply (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    P.hv v a b = P.h v a (emb F v b) := rfl

theorem rootsOfUnity_pow_eq_one {M : Type*} [CommMonoid M] (z : rootsOfUnity ℓ M) : z ^ ℓ = 1 := by
  have := z.2
  rw [mem_rootsOfUnity] at this
  exact Subtype.ext (by simpa using this)

/-- The symbol vanishes on local `ℓ`-th powers in the second slot. -/
theorem SymbolPkg.h_pow (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (c : (v.adicCompletion F)ˣ) :
    P.h v a (c ^ ℓ) = 1 := by
  rw [map_pow]; exact rootsOfUnity_pow_eq_one _

theorem SymbolPkg.h_of_mem_range (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ)
    {b : (v.adicCompletion F)ˣ}
    (hb : b ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range) :
    P.h v a b = 1 := by
  obtain ⟨c, rfl⟩ := hb; exact P.h_pow v a c

theorem skew_of_steinberg {G M : Type*} [CommGroup G] [CommGroup M] (f : G →* G →* M) (n : G)
    (hs : ∀ a, f a (n * a) = 1) (a b : G) : f a b * f b a = 1 := by
  have h := hs (a * b)
  have ha := hs a
  have hb := hs b
  simp only [map_mul, MonoidHom.mul_apply] at h ha hb
  calc f a b * f b a = (f a n * f a a) * (f b n * f b b) * (f a b * f b a) := by
        rw [ha, hb, one_mul, one_mul]
    _ = 1 := by rw [← h]; ac_rfl

theorem SymbolPkg.steinberg' (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    P.hv v a ((-1) * a) = 1 := by
  rw [neg_one_mul]; exact P.steinberg v a

/-- Local skew-symmetry, from Steinberg. -/
theorem SymbolPkg.skew (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    P.hv v a b * P.hv v b a = 1 :=
  skew_of_steinberg (P.hv v) (-1) (P.steinberg' v) a b

/-- Local alternation, when `-1` is an `ℓ`-th power. -/
theorem SymbolPkg.alt (v : HeightOneSpectrum (𝓞 F)) {c : Fˣ} (hc : c ^ ℓ = -1) (a : Fˣ) :
    P.hv v a a = 1 := by
  have h := P.steinberg' v a
  rw [map_mul, ← hc, map_pow, rootsOfUnity_pow_eq_one, one_mul] at h
  exact h

/-- The `S`-part `H_S = ∏_{v ∈ S} (·,·)_v`. -/
def SymbolPkg.HS (S : Finset (HeightOneSpectrum (𝓞 F))) : Fˣ →* Fˣ →* rootsOfUnity ℓ F :=
  ∏ v ∈ S, P.hv v

theorem SymbolPkg.HS_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (a b : Fˣ) :
    P.HS S a b = ∏ v ∈ S, P.hv v a b := by
  simp [SymbolPkg.HS, MonoidHom.finset_prod_apply]

theorem SymbolPkg.HS_alt (S : Finset (HeightOneSpectrum (𝓞 F))) {c : Fˣ} (hc : c ^ ℓ = -1)
    (a : Fˣ) : P.HS S a a = 1 := by
  rw [P.HS_apply]; exact Finset.prod_eq_one fun v _ => P.alt v hc a

theorem SymbolPkg.HS_skew (S : Finset (HeightOneSpectrum (𝓞 F))) (a b : Fˣ) :
    P.HS S a b * P.HS S b a = 1 := by
  rw [P.HS_apply, P.HS_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun v _ => P.skew v a b

/-- `S`-units are isotropic (Hilbert reciprocity + unramified symbols outside `S`). -/
theorem SymbolPkg.HS_unit (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v ∈ S) (u u' : Fˣ)
    (hu : ∀ v ∉ S, v.valuation F (u : F) = 1) (hu' : ∀ v ∉ S, v.valuation F (u' : F) = 1) :
    P.HS S u u' = 1 := by
  rw [P.HS_apply]
  refine P.prod_eq_one u u' S fun v hv => P.unit_unit v (fun h => hv (hSℓ v h)) u u' (hu v hv)
    (hu' v hv)

/-- The local `ℓ`-th powers at `S`. -/
def locPow (ℓ : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, ((powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range.comap
    (emb F v))

theorem mem_locPow {S : Finset (HeightOneSpectrum (𝓞 F))} {x : Fˣ} :
    x ∈ locPow ℓ S ↔ ∀ v ∈ S,
      emb F v x ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
  simp [locPow, Subgroup.mem_iInf]

theorem SymbolPkg.HS_locPow_right (S : Finset (HeightOneSpectrum (𝓞 F))) (x y : Fˣ)
    (hy : y ∈ locPow ℓ S) : P.HS S x y = 1 := by
  rw [P.HS_apply]
  exact Finset.prod_eq_one fun v hv => P.h_of_mem_range v x (mem_locPow.mp hy v hv)

theorem SymbolPkg.HS_locPow_left (S : Finset (HeightOneSpectrum (𝓞 F))) (x y : Fˣ)
    (hx : x ∈ locPow ℓ S) : P.HS S x y = 1 := by
  have := P.HS_skew S x y
  rw [P.HS_locPow_right S y x hx, mul_one] at this
  exact this

end C0Y

end
end
end

section
section
/-! C0Z: the product formula for the Kummer symbols. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative

noncomputable section

namespace C0Z

variable {F : Type} [Field F] [NumberField F]

theorem finite_valuation_ne_one (b : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (b : F) ≠ 1}.Finite := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) (b : F)
  simp only at hnd
  have hd0 : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hnd
    rcases hnd with h | h
    · exact b.ne_zero h
    · exact hd0 ((FaithfulSMul.algebraMap_injective (𝓞 F) F) (by rw [h, map_zero]))
  refine ((Ideal.finite_factors (I := Ideal.span {n}) (by simpa using hn0)).union
    (Ideal.finite_factors (I := Ideal.span {(d : 𝓞 F)}) (by simpa using hd0))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, Ideal.dvd_span_singleton] at hcon
  have h1 : v.valuation F (algebraMap (𝓞 F) F n) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hcon.1
  have h2 : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hcon.2
  apply hv
  have := congrArg (v.valuation F) hnd
  rw [map_mul, h1, h2, mul_one] at this
  exact this

variable (F) {ℓ : ℕ} [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)

/-- Product formula: if the symbols vanish outside `T`, their product over `T` is `1`. -/
theorem prod_sym_eq_one (hcx : ∀ w : InfinitePlace F, w.IsComplex) (a b : Fˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v ∉ T, sym F hζ v a (C0Y.emb F v b) = 1) :
    ∏ v ∈ T, sym F hζ v a (C0Y.emb F v b) = 1 := by
  classical
  haveI := isMulCommutative_KF a hζ
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec F (KF F ℓ a)
  have hf0 : artinMod F (KF F ℓ a) ≠ ⊥ := h𝔣.1
  set A := (Ideal.finite_factors (I := artinMod F (KF F ℓ a)) hf0).toFinset ∪
    (finite_valuation_ne_one b).toFinset
  set T' := T ∪ A
  have hlib := prod_idelicArtinMap_single_eq_one F (KF F ℓ a) _ h𝔣 _ h1 h2 h3 h4
    (hinf_of_isTotallyComplex F (KF F ℓ a) hcx) b
    (fun v => single F v (C0Y.emb F v b)) (fun v => single_mem F v _)
    (fun v => finPart_single F v _) T'
    (fun v hv => Finset.mem_union_right _ (Finset.mem_union_left _ (by simpa using hv)))
    (fun v hv => by
      by_contra h
      exact hv (Finset.mem_union_right _ (Finset.mem_union_right _ (by simpa using h))))
  have hT' : ∏ v ∈ T', sym F hζ v a (C0Y.emb F v b) = 1 := by
    simp only [sym, MonoidHom.coe_comp, Function.comp_apply]
    rw [← map_prod, hlib, map_one]
  rw [← hT', ← Finset.prod_subset (Finset.subset_union_left (s₂ := A))]
  intro v _ hv
  exact hT v hv

end C0Z

end
end
end

section
section
/-! C0Z: the local image of the Artin map (decomposition and inertia groups). -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

section Generic

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
  [IsGalois E K]

/-- A place of `K` above a given place of `E`. -/
theorem exists_under (v : HeightOneSpectrum (𝓞 E)) :
    ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) = v := by
  refine ⟨⟨primeAbove E K v, (primeAbove_isMaximal E K v).isPrime, primeAbove_ne_bot E K v⟩, ?_⟩
  ext1
  exact under_primeAbove E K v

/-- Ideles trivial away from `v` are `single`s. -/
theorem eq_single_of_mem (v : HeightOneSpectrum (𝓞 E)) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) :
    x = single E v (finPart v x) := by
  classical
  obtain ⟨hinf, hfin⟩ := hx
  apply Units.ext
  refine Prod.ext ?_ ?_
  · exact congrArg Units.val hinf
  · apply RestrictedProduct.ext
    intro w
    show (x : AdeleRing (𝓞 E) E).2 w = (fsingle E v ((finPart v x : (v.adicCompletion E)ˣ) :
      v.adicCompletion E)) w
    rw [fsingle_apply]
    by_cases hw : w = v
    · subst hw
      rw [Pi.mulSingle_eq_same]
      rfl
    · rw [Pi.mulSingle_eq_of_ne hw]
      exact congrArg Units.val (hfin w hw)

variable [IsMulCommutative (K ≃ₐ[E] K)]

/-- The local Artin map at `v` lands in the decomposition group, and onto it. -/
theorem range_single_eq_decomp (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K))
    (hw : w.under (𝓞 E) = v) :
    ((artinMap E K).comp (single E v)).range = NumberField.PlaceDecomp.decomp E K w := by
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec E K
  have hdec := (map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia E K _ h𝔣 _
    h1 h2 h3 h4 v w hw).1
  rw [← hdec]
  ext σ
  simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, Subgroup.mem_map]
  constructor
  · rintro ⟨b, rfl⟩; exact ⟨single E v b, single_mem E v b, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨finPart v x, by rw [← eq_single_of_mem E v x hx]⟩

/-- Local units go to the inertia group. -/
theorem single_unit_mem_inertia (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K))
    (hw : w.under (𝓞 E) = v) (b : (v.adicCompletion E)ˣ)
    (hb : Valued.v (b : v.adicCompletion E) = 1) :
    artinMap E K (single E v b) ∈ w.asIdeal.inertia (K ≃ₐ[E] K) := by
  classical
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec E K
  have hin := (map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia E K _ h𝔣 _
    h1 h2 h3 h4 v w hw).2
  rw [← hin]
  refine ⟨single E v b, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_unitIdelesTrivialOn_iff]
  refine ⟨fun u hu => ?_, (single_mem E v b).1, (single_mem E v b).2⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at hu
  subst hu
  have hval : ∀ c : (u.adicCompletion E)ˣ, Valued.v (c : u.adicCompletion E) = 1 →
      ((single E u c : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 u ∈
        u.adicCompletionIntegers E := by
    intro c hc
    show (fsingle E u (c : u.adicCompletion E)) u ∈ _
    rw [fsingle_apply, Pi.mulSingle_eq_same, HeightOneSpectrum.mem_adicCompletionIntegers, hc]
  refine ⟨hval b hb, ?_⟩
  rw [← map_inv]
  apply hval
  rw [Units.val_inv_eq_inv_val, map_inv₀, hb, inv_one]

end Generic

end C0Z

end
end
end

section
section
/-! C0Z: local nondegeneracy of the Kummer symbol. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

theorem rootKF_pow (a : Fˣ) : (rootKF F a).β ^ ℓ = algebraMap F (KF F ℓ a) a :=
  (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec

/-- If `(a, ·)_v` is trivial then the decomposition group is trivial. -/
theorem decomp_eq_bot (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ)
    (h : ∀ b, sym F hζ v a b = 1) (w : HeightOneSpectrum (𝓞 (KF F ℓ a)))
    (hw : w.under (𝓞 F) = v) :
    haveI := isMulCommutative_KF a hζ
    NumberField.PlaceDecomp.decomp F (KF F ℓ a) w = ⊥ := by
  haveI := isMulCommutative_KF a hζ
  rw [← range_single_eq_decomp F (KF F ℓ a) v w hw, eq_bot_iff]
  rintro σ ⟨b, rfl⟩
  rw [Subgroup.mem_bot]
  apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
  rw [map_one]
  exact h b

/-- **Local nondegeneracy**: if `(a, b)_v = 1` for all `b ∈ F_vˣ` then `a` is a local `ℓ`-th
power. -/
theorem sym_nondeg (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (h : ∀ b, sym F hζ v a b = 1) :
    C0Y.emb F v a ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
  haveI := isMulCommutative_KF a hζ
  obtain ⟨w, hw⟩ := exists_under F (KF F ℓ a) v
  have hD := decomp_eq_bot F hζ v a h w hw
  subst hw
  set K := KF F ℓ a
  set y : w.adicCompletion K := algebraMap K (w.adicCompletion K) (rootKF F a).β
  have hy := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom F K w
    y).mp (fun σ => by
      have : (σ : K ≃ₐ[F] K) = 1 := by
        have h2 : (σ : K ≃ₐ[F] K) ∈ (⊥ : Subgroup (K ≃ₐ[F] K)) := by rw [← hD]; exact σ.2
        exact Subgroup.mem_bot.mp h2
      have hσ : σ = 1 := Subtype.ext this
      rw [hσ, one_smul])
  obtain ⟨c, hc⟩ := hy
  set φ := HeightOneSpectrum.Extension.adicCompletionSemialgHom F K
    (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 F) w).Extension (𝓞 K))
  have hφa : φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) a) =
      algebraMap K (w.adicCompletion K) (algebraMap F K a) := φ.commutes a
  have hcpow : φ (c ^ ℓ) = φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) a) := by
    rw [map_pow, hc, hφa, ← map_pow, rootKF_pow]
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hc' := hinj hcpow
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne ℓ), eq_comm, map_eq_zero] at hc'
    exact a.ne_zero hc'
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [hc']
  rfl

end C0Z

end
end
end

section
section
/-! C0Z: the Steinberg relation `(a, -a)_v = 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)
include hζ

/-- The Galois group of `F(a^{1/ℓ})` has order dividing `ℓ`. -/
theorem card_gal_dvd (a : Fˣ) : Nat.card (KF F ℓ a ≃ₐ[F] KF F ℓ a) ∣ ℓ := by
  have h1 := Subgroup.card_dvd_of_injective _ (kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a))
  have h2 : Nat.card (rootsOfUnity ℓ F) = ℓ := hζ.card_rootsOfUnity
  rw [h2] at h1
  exact h1

/-- When the Galois group has order `ℓ`: `∏_σ σ(-α) = -a`. -/
theorem prod_neg_root (a : Fˣ) (hcard : Nat.card (KF F ℓ a ≃ₐ[F] KF F ℓ a) = ℓ) :
    ∏ σ : (KF F ℓ a ≃ₐ[F] KF F ℓ a), σ (-(rootKF F a).β) = algebraMap F (KF F ℓ a) (-(a : F)) := by
  classical
  set K := KF F ℓ a
  set α := (rootKF (ℓ := ℓ) F a).β
  have hζK := hζ.map_of_injective (FaithfulSMul.algebraMap_injective F K)
  -- `σ α = ζ^{e σ} α`
  have hex : ∀ σ : K ≃ₐ[F] K, ∃ i < ℓ, ζ ^ i = ((kch hζ (rootKF F a) σ : Fˣ) : F) := by
    intro σ
    exact hζ.eq_pow_of_pow_eq_one (kval_pow hζ (rootKF F a) σ)
  choose e he heq using hex
  have hσ : ∀ σ : K ≃ₐ[F] K, σ α = algebraMap F K ζ ^ e σ * α := by
    intro σ
    rw [← map_pow, heq σ, algebraMap_kch, div_mul_cancel₀ _ (rootKF F a).ne_zero]
  let ef : (K ≃ₐ[F] K) → Fin ℓ := fun σ => ⟨e σ, he σ⟩
  have hinj : Function.Injective ef := by
    intro σ τ h
    have h' : e σ = e τ := congrArg Fin.val h
    apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
    apply Subtype.ext; apply Units.ext
    rw [← heq σ, ← heq τ, h']
  have hbij : Function.Bijective ef := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard]
  have key : (X ^ ℓ - C (algebraMap F K a)) =
      ∏ i ∈ Finset.range ℓ, (X - C (algebraMap F K ζ ^ i * α)) :=
    X_pow_sub_C_eq_prod hζK (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (rootKF_pow F a)
  have hev := congrArg (Polynomial.eval 0) key
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod, zero_sub] at hev
  rw [zero_pow (NeZero.ne ℓ), zero_sub] at hev
  calc ∏ σ : K ≃ₐ[F] K, σ (-α) = ∏ σ : K ≃ₐ[F] K, -(algebraMap F K ζ ^ (ef σ : ℕ) * α) := by
        refine Finset.prod_congr rfl fun σ _ => ?_
        rw [map_neg, hσ]
    _ = ∏ i : Fin ℓ, -(algebraMap F K ζ ^ (i : ℕ) * α) :=
        Fintype.prod_bijective ef hbij _ _ fun σ => rfl
    _ = ∏ i ∈ Finset.range ℓ, -(algebraMap F K ζ ^ i * α) :=
        Fin.prod_univ_eq_prod_range (fun i => -(algebraMap F K ζ ^ i * α)) ℓ
    _ = algebraMap F K (-(a : F)) := by
        rw [map_neg, hev]

omit hζ in
theorem smul_algebraMap {K : Type} [Field K] [NumberField K] [Algebra F K]
    (w : HeightOneSpectrum (𝓞 K)) (σ : NumberField.PlaceDecomp.decomp F K w) (y : K) :
    σ • algebraMap K (w.adicCompletion K) y = algebraMap K (w.adicCompletion K) ((σ : K ≃ₐ[F] K) y) := by
  rw [NumberField.PlaceDecomp.smul_def]
  exact NumberField.PlaceDecomp.actRingEquiv_coe σ (WithVal.toVal _ y)

/-- **Steinberg**: `(a, -a)_v = 1`. -/
theorem sym_steinberg (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    sym F hζ v a (C0Y.emb F v (-a)) = 1 := by
  classical
  haveI := isMulCommutative_KF a hζ
  set K := KF F ℓ a
  obtain ⟨w, hw⟩ := exists_under F K v
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec F K
  have hr : artinMap F K (single F v (C0Y.emb F v (-a))) = 1 := by
    rw [idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq F K _ h𝔣 _ h1 h2 h3 h4 v _ _
      (single_mem F v _) (finPart_single F v _) w hw]
    set φ := HeightOneSpectrum.Extension.adicCompletionSemialgHom F K
      (⟨w, hw⟩ : v.Extension (𝓞 K))
    have hφ : φ ((C0Y.emb F v (-a) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        algebraMap K (w.adicCompletion K) (algebraMap F K (-(a : F))) := φ.commutes _
    rw [hφ]
    have hne : ∀ y : K, y ≠ 0 → algebraMap K (w.adicCompletion K) y ≠ 0 := fun y hy => by
      rwa [Ne, map_eq_zero]
    by_cases hD : NumberField.PlaceDecomp.decomp F K w = ⊥
    · refine ⟨Units.mk0 (algebraMap K (w.adicCompletion K) (algebraMap F K (-(a : F))))
        (hne _ (by simp)), ?_⟩
      rw [finprod_eq_single _ 1 (fun σ hσ => absurd (Subtype.ext (by
        have h2 : (σ : K ≃ₐ[F] K) ∈ (⊥ : Subgroup (K ≃ₐ[F] K)) := by rw [← hD]; exact σ.2
        exact Subgroup.mem_bot.mp h2)) hσ)]
      rw [one_smul, Units.val_mk0]
    · have hG := card_gal_dvd F hζ a
      have hDG : Nat.card (NumberField.PlaceDecomp.decomp F K w) ∣ Nat.card (K ≃ₐ[F] K) :=
        Subgroup.card_subgroup_dvd_card _
      have hD1 : Nat.card (NumberField.PlaceDecomp.decomp F K w) ≠ 1 := fun h =>
        hD (Subgroup.card_eq_one.mp h)
      have hDl : Nat.card (NumberField.PlaceDecomp.decomp F K w) = ℓ :=
        ((hℓ.eq_one_or_self_of_dvd _ (hDG.trans hG)).resolve_left hD1)
      have hGl : Nat.card (K ≃ₐ[F] K) = ℓ :=
        Nat.dvd_antisymm hG (by have h := hDG; rw [hDl] at h; exact h)
      have hDtop : NumberField.PlaceDecomp.decomp F K w = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (hDl.trans hGl.symm)
      have hα0 : -(rootKF (ℓ := ℓ) F a).β ≠ 0 := neg_ne_zero.mpr (rootKF F a).ne_zero
      refine ⟨Units.mk0 _ (hne _ hα0), ?_⟩
      rw [finprod_eq_prod_of_fintype, Units.coe_prod]
      simp only [NumberField.PlaceDecomp.coe_smul_units, Units.val_mk0, smul_algebraMap]
      rw [← map_prod, ← prod_neg_root F hζ a hGl]
      congr 1
      refine Fintype.prod_bijective Subtype.val ⟨Subtype.val_injective, fun σ =>
        ⟨⟨σ, by rw [hDtop]; trivial⟩, rfl⟩⟩ _ _ fun σ => rfl
  show kch hζ (rootKF F a) (artinMap F K (single F v (C0Y.emb F v (-a)))) = 1
  rw [hr, map_one]

end C0Z

end
end
end

section
section
/-! C0Z: Kummer extensions are unramified at `v ∤ ℓ a`; the unit–unit symbol. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

/-- `n`-th roots of unity congruent modulo `Q` with `n ∉ Q` are equal. -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {n : ℕ}
    (hn : (n : R) ∉ Q) {a b : R} (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : a - b ∈ Q) : a = b := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  set η := b * a ^ (n - 1) with hη
  have han : a ^ (n - 1) * a = 1 := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), ha]
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ (n - 1) * (a - b) := by
      rw [hη, mul_sub, han]; ring
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · calc a = a * 1 := (mul_one a).symm
      _ = a * η := by rw [hη1]
      _ = b * (a ^ (n - 1) * a) := by rw [hη]; ring
      _ = b := by rw [han, mul_one]
  · exfalso
    have hηn : η ^ n = 1 := by
      rw [hη, mul_pow, ← pow_mul, hb, one_mul, mul_comm, pow_mul, ha, one_pow]
    have hsum : ∑ i ∈ Finset.range n, η ^ i = 0 := by
      have h := geom_sum_mul η n
      rw [hηn, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hη1)
    apply hn
    have : (n : R) = ∑ i ∈ Finset.range n, (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
    rw [this]
    refine Q.sum_mem fun i _ => ?_
    rw [← geom_sum_mul_neg]
    exact Q.mul_mem_left _ h1

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- An integral Kummer generator `β = d α` at a place where `a` is a unit. -/
theorem exists_intGen (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    ∃ (d n : 𝓞 F) (β : 𝓞 (KF F ℓ a)), d ∉ v.asIdeal ∧ n ∉ v.asIdeal ∧
      (a : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n ∧
      (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β ∧
      β ^ ℓ = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (d ^ (ℓ - 1) * n) := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (a : F) ha.le
  have hd : (d : 𝓞 F) ∉ v.asIdeal := d.2
  have hn : n ∉ v.asIdeal := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, ha,
      (v.valuation_eq_one_iff_notMem (K := F)).mpr hd, one_mul]
  set K := KF F ℓ a
  set β : K := algebraMap F K (algebraMap (𝓞 F) F d) * (rootKF F a).β
  have hβpow : β ^ ℓ = algebraMap F K (algebraMap (𝓞 F) F ((d : 𝓞 F) ^ (ℓ - 1) * n)) := by
    have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm
    rw [mul_pow, rootKF_pow, ← map_pow, ← map_mul]
    congr 1
    rw [map_mul, map_pow, ← hnd]
    conv_lhs => rw [hℓ1, pow_succ]
    ring
  have hint : IsIntegral ℤ β := by
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow, ← IsScalarTower.algebraMap_apply]
    exact ((((d : 𝓞 F) ^ (ℓ - 1) * n).isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F K))
  refine ⟨d, n, ⟨β, hint⟩, hd, hn, hnd, rfl, ?_⟩
  apply RingOfIntegers.ext
  simp only [map_pow]
  show β ^ ℓ = _
  rw [hβpow, ← IsScalarTower.algebraMap_apply]
  rfl

/-- A root of unity of `F` as an algebraic integer. -/
def rootO (μ : rootsOfUnity ℓ F) : 𝓞 F :=
  ⟨((μ : Fˣ) : F), IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by
    have := μ.2; rw [mem_rootsOfUnity] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]; exact isIntegral_one)⟩

omit [NumberField F] in
theorem rootO_pow (μ : rootsOfUnity ℓ F) : rootO F μ ^ ℓ = 1 := by
  apply RingOfIntegers.ext
  show ((μ : Fˣ) : F) ^ ℓ = 1
  have := μ.2; rw [mem_rootsOfUnity] at this
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

include hζ in
/-- `σ β = μ_σ β` in `𝓞 K`. -/
theorem smul_intGen (a : Fˣ) (d : 𝓞 F) (β : 𝓞 (KF F ℓ a))
    (hβ : (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β)
    (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a) :
    σ • β = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ)) * β := by
  apply RingOfIntegers.ext
  have e : ∀ x : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x : 𝓞 (KF F ℓ a)) : KF F ℓ a) =
      algebraMap F (KF F ℓ a) (x : F) := fun x => rfl
  show σ (β : KF F ℓ a) = ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) _ : 𝓞 (KF F ℓ a)) : KF F ℓ a) *
    (β : KF F ℓ a)
  rw [e, hβ]
  show σ _ = algebraMap F (KF F ℓ a) ((kch hζ (rootKF F a) σ : Fˣ) : F) * _
  rw [algebraMap_kch, map_mul, AlgEquiv.commutes]
  field_simp [(rootKF (ℓ := ℓ) F a).ne_zero]

include hζ in
/-- **Kummer extensions are unramified** at `v ∤ ℓ` where `a` is a unit. -/
theorem inertia_eq_bot (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) (w : HeightOneSpectrum (𝓞 (KF F ℓ a)))
    (hw : w.under (𝓞 F) = v) :
    w.asIdeal.inertia (KF F ℓ a ≃ₐ[F] KF F ℓ a) = ⊥ := by
  obtain ⟨d, n, β, hd, hn, -, hβ, hβpow⟩ := exists_intGen (ℓ := ℓ) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ ℓ ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow] at this
    have h2 := hmem _ this
    rcases v.isPrime.mem_or_mem h2 with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have h1 := hσ β
  rw [smul_intGen F hζ a d β hβ σ] at h1
  have h2 : (algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ) - 1)) * β ∈
      w.asIdeal := by rw [map_sub, map_one, sub_mul, one_mul]; exact h1
  rcases w.isPrime.mem_or_mem h2 with h3 | h3
  · have h4 := hmem _ h3
    have h5 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F _) (one_pow ℓ) h4
    apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
    rw [map_one]
    apply Subtype.ext; apply Units.ext
    have := congrArg (fun z : 𝓞 F => (z : F)) h5
    exact this
  · exact absurd h3 hβw

include hζ in
/-- Symbols of two units at `v ∤ ℓ` are trivial. -/
theorem sym_unit_unit (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a b : Fˣ)
    (ha : v.valuation F (a : F) = 1) (hb : v.valuation F (b : F) = 1) :
    sym F hζ v a (C0Y.emb F v b) = 1 := by
  haveI := isMulCommutative_KF a hζ
  obtain ⟨w, hw⟩ := exists_under F (KF F ℓ a) v
  have hmem := single_unit_mem_inertia F (KF F ℓ a) v w hw (C0Y.emb F v b) (by
    show Valued.v ((b : F) : v.adicCompletion F) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hb])
  rw [inertia_eq_bot F hζ v hv a ha w hw, Subgroup.mem_bot] at hmem
  show kch hζ (rootKF F a) (artinMap F (KF F ℓ a) (single F v (C0Y.emb F v b))) = 1
  rw [hmem, map_one]

end C0Z

end
end
end

section
section
/-! C0Z: the tame formula `(a, π)_v ≡ a^{(Nv - 1)/ℓ} (mod v)` at `v ∤ ℓ`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- An algebraic integer from an element of `F` that is a root of unity. -/
def toO (x : F) (hx : x ^ ℓ = 1) : 𝓞 F :=
  ⟨x, IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by rw [hx]; exact isIntegral_one)⟩

omit [NumberField F] in
theorem toO_pow (x : F) (hx : x ^ ℓ = 1) : toO F x hx ^ ℓ = 1 := by
  apply RingOfIntegers.ext; show x ^ ℓ = 1; exact hx

include hζ in
/-- `ℓ ∣ N v - 1` when `v ∤ ℓ`. -/
theorem dvd_card_sub_one (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) :
    ℓ ∣ Nat.card (𝓞 F ⧸ v.asIdeal) - 1 := by
  classical
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  set z := toO F ζ hζ.pow_eq_one
  have hz : z ^ ℓ = 1 := toO_pow F ζ _
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal z) ℓ := by
    refine ⟨by rw [← map_pow, hz, map_one], fun l hl => ?_⟩
    have h1 : z ^ l - 1 ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hl, map_one, sub_self]
    have h2 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv
      (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (one_pow ℓ) h1
    apply hζ.dvd_of_pow_eq_one
    have := congrArg (fun x : 𝓞 F => (x : F)) h2
    simpa [z, toO] using this
  have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk v.asIdeal z)
    (hη.ne_zero (NeZero.ne ℓ))
  rw [Fintype.card_eq_nat_card] at this
  exact hη.dvd_of_pow_eq_one _ this

include hζ in
/-- The place over `v` used for the Frobenius. -/
theorem placeOrd_single (v : HeightOneSpectrum (𝓞 F)) (π : Fˣ)
    (hπ : v.valuation F (π : F) = WithZero.exp (-1 : ℤ)) :
    placeOrd F (projFin F (single F v (C0Y.emb F v π))) v = 1 := by
  classical
  unfold placeOrd
  have : ((projFin F (single F v (C0Y.emb F v π)) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v = ((π : F) : v.adicCompletion F) := by
    show (fsingle F v ((C0Y.emb F v π : (v.adicCompletion F)ˣ) : v.adicCompletion F)) v = _
    rw [fsingle_apply, Pi.mulSingle_eq_same]
    rfl
  rw [this, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, WithZero.log_exp]
  norm_num

include hζ in
/-- **Tame formula.** -/
theorem sym_tame (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a π : Fˣ) (ω : F)
    (ha : v.valuation F (a : F) = 1) (hπ : v.valuation F (π : F) = WithZero.exp (-1 : ℤ))
    (hω : ω ^ ℓ = 1)
    (hcong : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / ℓ) - ω) < 1) :
    ((sym F hζ v a (C0Y.emb F v π) : Fˣ) : F) = ω := by
  classical
  haveI := isMulCommutative_KF a hζ
  set K := KF F ℓ a
  set Q := primeAbove F K v
  let w : HeightOneSpectrum (𝓞 K) := ⟨Q, (primeAbove_isMaximal F K v).isPrime, primeAbove_ne_bot F K v⟩
  have hw : w.under (𝓞 F) = v := by ext1; exact under_primeAbove F K v
  have hQv : Q.under (𝓞 F) = v.asIdeal := under_primeAbove F K v
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec F K
  set φ := artinFrob F K v
  have hφ : IsArithFrobAt (𝓞 F) φ w.asIdeal := isArithFrobAt_artinFrob F K v
  have hin := idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt F K _ h𝔣 _ h1 h2 h3 h4
    v (C0Y.emb F v π) (single F v (C0Y.emb F v π)) (single_mem F v _) (finPart_single F v _) w hw φ hφ
  rw [placeOrd_single F hζ v π hπ, inertia_eq_bot F hζ v hv a ha w hw, Subgroup.mem_bot,
    zpow_one, mul_inv_eq_one] at hin
  show ((kch hζ (rootKF F a) (artinMap F K (single F v (C0Y.emb F v π))) : Fˣ) : F) = ω
  rw [hin]
  -- the Kummer value of the Frobenius
  set μ := kch hζ (rootKF F a) φ
  obtain ⟨d, n, β, hd, hn, hnd, hβ, hβpow⟩ := exists_intGen (ℓ := ℓ) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ ℓ ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow] at this
    rcases v.isPrime.mem_or_mem (hmem _ this) with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  set q := Nat.card (𝓞 F ⧸ v.asIdeal)
  have hq : q = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hFrob : ∀ x : 𝓞 K, φ • x - x ^ q ∈ w.asIdeal := by
    intro x
    have := hφ x
    rw [show w.asIdeal.under (𝓞 F) = v.asIdeal from hQv] at this
    exact this
  -- `ℓ ∣ q - 1`
  have hℓq : ℓ ∣ q - 1 := dvd_card_sub_one F hζ v hv
  obtain ⟨K', hK'⟩ := hℓq
  have hq1 : q = ℓ * K' + 1 := by
    have : 0 < q := by
      rw [hq]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    omega
  have hK'eq : (Ideal.absNorm v.asIdeal - 1) / ℓ = K' := by
    rw [← hq, hK', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  rw [hK'eq] at hcong
  set μO := rootO F μ
  have hsm := smul_intGen F hζ a d β hβ φ
  have hfb := hFrob β
  rw [hsm, hq1, pow_succ, pow_mul, hβpow] at hfb
  have hfb' : algebraMap (𝓞 F) (𝓞 K) (μO - ((d ^ (ℓ - 1) * n) ^ K')) * β ∈ w.asIdeal := by
    rw [map_sub, map_pow, sub_mul]; convert hfb using 1
  have hμA : μO - (d ^ (ℓ - 1) * n) ^ K' ∈ v.asIdeal := by
    rcases w.isPrime.mem_or_mem hfb' with h | h
    · exact hmem _ h
    · exact absurd h hβw
  -- valuations in `F`
  set D : F := algebraMap (𝓞 F) F d
  set A : F := algebraMap (𝓞 F) F ((d ^ (ℓ - 1) * n) ^ K')
  have hDv : v.valuation F D = 1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hA : A = D ^ (q - 1) * (a : F) ^ K' := by
    have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm
    simp only [A, map_pow, map_mul]
    rw [← hnd, hK']
    have e : D ^ (ℓ - 1) * ((a : F) * D) = (a : F) * D ^ ℓ := by
      conv_rhs => rw [hℓ1, pow_succ]
      ring
    rw [e, mul_pow, ← pow_mul, mul_comm]
  -- Fermat: `D^{q-1} ≡ 1`
  have hferm : v.valuation F (D ^ (q - 1) - 1) < 1 := by
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    have hmd : Ideal.Quotient.mk v.asIdeal d ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ hmd
    rw [Fintype.card_eq_nat_card, ← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal),
      Ideal.Quotient.eq] at this
    have e : D ^ (q - 1) - 1 = algebraMap (𝓞 F) F (d ^ (q - 1) - 1) := by
      simp [D]
    rw [e]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr this
  set ωO := toO F ω hω
  have hωF : algebraMap (𝓞 F) F ωO = ω := rfl
  have hωv : v.valuation F ω ≤ 1 := by rw [← hωF]; exact v.valuation_le_one (K := F) ωO
  have hAω : v.valuation F (A - ω) < 1 := by
    rw [hA]
    have e : D ^ (q - 1) * (a : F) ^ K' - ω =
        D ^ (q - 1) * ((a : F) ^ K' - ω) + (D ^ (q - 1) - 1) * ω := by ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow, hDv, one_pow, one_mul]; exact hcong
    · rw [map_mul]
      calc _ ≤ v.valuation F (D ^ (q - 1) - 1) * 1 := mul_le_mul_right hωv _
        _ < 1 := by rw [mul_one]; exact hferm
  have hμv : v.valuation F (algebraMap (𝓞 F) F μO - A) < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F) _).mpr hμA
    change v.valuation F (algebraMap (𝓞 F) F (μO - _)) < 1 at this
    rwa [map_sub] at this
  have hμω : μO - ωO ∈ v.asIdeal := by
    rw [← v.valuation_lt_one_iff_mem (K := F)]
    change v.valuation F (algebraMap (𝓞 F) F (μO - ωO)) < 1
    rw [map_sub, hωF]
    have e : algebraMap (𝓞 F) F μO - ω = (algebraMap (𝓞 F) F μO - A) + (A - ω) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hμv hAω)
  have heq := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F μ) (toO_pow F ω hω) hμω
  have := congrArg (fun x : 𝓞 F => (x : F)) heq
  simpa [μO, rootO, ωO, toO] using this

end C0Z

end
end
end

section
section
/-! C0Y, abstract algebra: character count and the Lagrangian counting lemma. -/

set_option autoImplicit false

namespace C0Y

open Cardinal in
/-- A finite group has finitely many, at most `|Q|`, homomorphisms into the units of a field
(Dedekind independence of characters). -/
theorem finite_and_natCard_monoidHom_units_le (Q K : Type*) [CommGroup Q] [Finite Q] [Field K] :
    Finite (Q →* Kˣ) ∧ Nat.card (Q →* Kˣ) ≤ Nat.card Q := by
  classical
  have hli := linearIndependent_monoidHom Q K
  haveI : Fintype Q := Fintype.ofFinite Q
  have h1 := hli.cardinalMk_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have hfin : Finite (Q →* K) :=
    Cardinal.lt_aleph0_iff_finite.mp (lt_of_le_of_lt h1 (Cardinal.nat_lt_aleph0 _))
  have h2 : Nat.card (Q →* K) ≤ Fintype.card Q := by
    have := Cardinal.toNat_le_toNat h1 (Cardinal.nat_lt_aleph0 _)
    simpa [Nat.card] using this
  let f : (Q →* Kˣ) → (Q →* K) := fun φ => (Units.coeHom K).comp φ
  have hf : Function.Injective f := fun φ ψ h => by
    ext q
    have := congrArg (fun χ : Q →* K => χ q) h
    simpa [f] using this
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc Nat.card (Q →* Kˣ) ≤ Nat.card (Q →* K) := Nat.card_le_card_of_injective f hf
    _ ≤ Fintype.card Q := h2
    _ = Nat.card Q := Nat.card_eq_fintype_card.symm

/-- Skew-symmetry of an alternating pairing. -/
theorem skew {G M : Type*} [CommGroup G] [CommGroup M] (H : G →* G →* M) (halt : ∀ x, H x x = 1)
    (x y : G) : H x y * H y x = 1 := by
  have h := halt (x * y)
  simp only [map_mul, MonoidHom.mul_apply, halt x, halt y, one_mul, mul_one] at h
  rw [mul_comm]; exact h

/-- **Lagrangian counting.** `H` alternating with `L` in the radical, radical inside `L`, `U`
isotropic and `[G : L] = [U : U ∩ L]²`: then anything orthogonal to `U` lies in `U ⊔ L`. -/
theorem mem_sup_of_forall_eq_one {G K : Type*} [CommGroup G] [Field K] (H : G →* G →* Kˣ)
    (L U : Subgroup G) [hfin : Finite (G ⧸ L)]
    (halt : ∀ x, H x x = 1)
    (hL : ∀ x y, y ∈ L → H x y = 1)
    (hnd : ∀ x, (∀ y, H x y = 1) → x ∈ L)
    (hiso : ∀ u ∈ U, ∀ u' ∈ U, H u u' = 1)
    (hcard : L.index = (L.relIndex U) ^ 2) :
    ∀ x, (∀ u ∈ U, H x u = 1) → x ∈ U ⊔ L := by
  classical
  let X : Subgroup G :=
    { carrier := {x | ∀ u ∈ U, H x u = 1}
      one_mem' := fun u _ => by simp
      mul_mem' := fun {a b} ha hb u hu => by simp [ha u hu, hb u hu]
      inv_mem' := fun {a} ha u hu => by simp [ha u hu] }
  let J : Subgroup G := U ⊔ L
  have hLJ : L ≤ J := le_sup_right
  have hJX : J ≤ X := by
    refine sup_le (fun u hu u' hu' => hiso u hu u' hu') (fun l hl u hu => ?_)
    have := skew H halt l u
    rw [hL u l hl, mul_one] at this
    exact this
  have hLfin : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  -- `H x` kills `J` for `x ∈ X`
  have hkill : ∀ x ∈ X, J ≤ (H x).ker := fun x hx =>
    sup_le (fun u hu => hx u hu) (fun l hl => hL x l hl)
  let Φ : X →* (G ⧸ J →* Kˣ) :=
    { toFun := fun x => QuotientGroup.lift J (H x) (hkill x x.2)
      map_one' := by ext q; simp
      map_mul' := fun x y => by
        ext q; simp }
  have hker : Φ.ker ≤ L.subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hnd
    intro y
    have := congrArg (fun χ : G ⧸ J →* Kˣ => χ (QuotientGroup.mk y)) (MonoidHom.mem_ker.mp hx)
    simpa [Φ] using this
  haveI : L.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : J.FiniteIndex := Subgroup.finiteIndex_of_le hLJ
  haveI : Finite (G ⧸ J) := Subgroup.finite_quotient_of_finiteIndex
  have hJidx : J.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  -- `[X : L] ≤ [G : J]`
  obtain ⟨hHf, hHc⟩ := finite_and_natCard_monoidHom_units_le (G ⧸ J) K
  have h1 : L.relIndex X ≤ J.index := by
    have hXL : L ≤ X := hLJ.trans hJX
    have hne : L.relIndex X ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_index hXL
      rw [h0, zero_mul] at this
      exact hLfin this.symm
    have hk : (L.subgroupOf X).index ≤ Φ.ker.index := by
      have hd := Subgroup.index_dvd_of_le hker
      have hpos : 0 < Φ.ker.index := by
        rw [Subgroup.index_ker]
        haveI : Finite Φ.range := Finite.of_injective _ Subtype.val_injective
        exact Nat.card_pos
      exact Nat.le_of_dvd hpos hd
    calc L.relIndex X = (L.subgroupOf X).index := rfl
      _ ≤ Φ.ker.index := hk
      _ = Nat.card Φ.range := Subgroup.index_ker Φ
      _ ≤ Nat.card (G ⧸ J →* Kˣ) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ ≤ Nat.card (G ⧸ J) := hHc
      _ = J.index := rfl
  have hLJidx : L.relIndex J * J.index = L.index := Subgroup.relIndex_mul_index hLJ
  have hLJU : L.relIndex J = L.relIndex U := Subgroup.relIndex_sup_right U L
  have he : L.relIndex U ≠ 0 := by
    intro h0; rw [h0] at hcard; simp at hcard; exact hLfin hcard
  have hJe : J.index = L.relIndex U := by
    rw [hLJU, hcard, sq] at hLJidx
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) hLJidx
  have hmul := Subgroup.relIndex_mul_relIndex L J X hLJ hJX
  rw [hLJU] at hmul
  have hJX1 : J.relIndex X = 1 := by
    have hle : L.relIndex U * J.relIndex X ≤ L.relIndex U * 1 := by
      rw [hmul, mul_one, ← hJe]; exact h1
    have h0 : J.relIndex X ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hmul
      have hXL : L ≤ X := hLJ.trans hJX
      have := Subgroup.relIndex_mul_index hXL
      rw [← hmul, zero_mul] at this
      exact hLfin this.symm
    have := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero he)
    omega
  intro x hx
  exact Subgroup.relIndex_eq_one.mp hJX1 hx

end C0Y

end
end

section
section
/-! C0Y: weak approximation modulo local `ℓ`-th powers. -/

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace C0Y

variable {F : Type} [Field F] [NumberField F]

/-- Weak approximation modulo `ℓ`-th powers: any family of local units at the places of `S` is
the image of a global unit up to local `ℓ`-th powers. -/
theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 F))) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (b : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) :
    ∃ y : Fˣ, ∀ v ∈ S, emb F v y * (b v)⁻¹ ∈
      (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
  classical
  let R : (v : HeightOneSpectrum (𝓞 F)) → Subgroup (v.adicCompletion F)ˣ := fun v =>
    (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range
  let V : (w : S) → Set (w.1.adicCompletion F) := fun w =>
    Units.val '' {u | u * (b w)⁻¹ ∈ R w}
  have hV : ∀ w, IsOpen (V w) := by
    intro w
    apply (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.1.adicCompletion F)).isOpenMap
    have hR : IsOpen (R w : Set (w.1.adicCompletion F)ˣ) :=
      NumberField.isOpen_range_powMonoidHom_units_adicCompletion w.1 hℓ
    exact hR.preimage (continuous_mul_right _)
  have hmem : ∀ w : S, ((b w : (w.1.adicCompletion F)ˣ) : w.1.adicCompletion F) ∈ V w := by
    intro w
    exact ⟨b w, by simpa [R] using ⟨1, one_pow ℓ⟩, rfl⟩
  have hO : IsOpen (Set.pi Set.univ V) := isOpen_set_pi Set.finite_univ (fun w _ => hV w)
  obtain ⟨x, hx⟩ := (NumberField.denseRange_algebraMap_pi_adicCompletion (K := F) S).exists_mem_open
    hO ⟨fun w => (b w : w.1.adicCompletion F), fun w _ => hmem w⟩
  by_cases hS : S = ∅
  · exact ⟨1, by simp [hS]⟩
  obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨u, -, hu⟩ := hx ⟨v₀, hv₀⟩ (Set.mem_univ _)
    simp only [map_zero] at hu
    exact u.ne_zero hu
  refine ⟨Units.mk0 x hx0, fun v hv => ?_⟩
  obtain ⟨u, hu, hux⟩ := hx ⟨v, hv⟩ (Set.mem_univ _)
  have : u = emb F v (Units.mk0 x hx0) := Units.ext hux
  rw [← this]
  exact hu

end C0Y

end
end
end

section
section
/-! C0Y: the counts `[Fˣ : L] = ℓ^{2(|S|+r)}` and `[U_S : U_S ∩ L] = ℓ^{|S|+r}`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain

noncomputable section

namespace C0Y

variable {F : Type} [Field F] [NumberField F]

theorem index_pi_dep {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (H : ∀ i, Subgroup (β i)) : (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

/-- `Fˣ → ∏_{v ∈ S} F_vˣ`. -/
def piEmb (S : Finset (HeightOneSpectrum (𝓞 F))) : Fˣ →* ((v : S) → (v.1.adicCompletion F)ˣ) :=
  Pi.monoidHom fun v => emb F v.1

/-- `∏_{v ∈ S} F_vˣ^ℓ`. -/
def Rpi (ℓ : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Subgroup ((v : S) → (v.1.adicCompletion F)ˣ) :=
  Subgroup.pi Set.univ fun v =>
    (powMonoidHom ℓ : (v.1.adicCompletion F)ˣ →* (v.1.adicCompletion F)ˣ).range

theorem locPow_eq_comap (ℓ : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    locPow ℓ S = (Rpi ℓ S).comap (piEmb S) := by
  ext x
  rw [mem_locPow, Subgroup.mem_comap, Rpi, Subgroup.mem_pi]
  constructor
  · intro h v _; exact h v.1 v.2
  · intro h v hv; exact h ⟨v, hv⟩ (Set.mem_univ _)

theorem range_sup_Rpi {ℓ : ℕ} (hℓ : 0 < ℓ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (piEmb S).range ⊔ Rpi ℓ S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro g _
  let b' : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ := fun v =>
    if h : v ∈ S then g ⟨v, h⟩ else 1
  obtain ⟨y, hy⟩ := exists_approx S hℓ b'
  have hr : (piEmb S y)⁻¹ * g ∈ Rpi ℓ S := by
    rw [Rpi, Subgroup.mem_pi]
    intro v _
    have := hy v.1 v.2
    simp only [b', dif_pos v.2] at this
    have h2 : ((piEmb S y)⁻¹ * g) v = (emb F v.1 y * (g v)⁻¹)⁻¹ := by
      simp only [Pi.mul_apply, Pi.inv_apply, piEmb]
      rw [mul_inv_rev, inv_inv, mul_comm]
      rfl
    rw [h2]
    exact Subgroup.inv_mem _ this
  have : g = piEmb S y * ((piEmb S y)⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ⟨y, rfl⟩ hr

theorem index_locPow {ℓ : ℕ} (hℓ : ℓ.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
    (hcx : ∀ w : InfinitePlace F, w.IsComplex) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v ∈ S) :
    (locPow (F := F) ℓ S).index = ℓ ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  classical
  rw [locPow_eq_comap, Subgroup.index_comap, ← Subgroup.relIndex_sup_right,
    range_sup_Rpi hℓ.pos, Subgroup.relIndex_top_right, Rpi, index_pi_dep]
  have hμ : (primitiveRoots ℓ F).Nonempty := ⟨ζ, (mem_primitiveRoots hℓ.pos).mpr hζ⟩
  have key := NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
    hℓ hμ S hSℓ
  have hinf : ∏ w : InfinitePlace F,
      Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom ℓ : (w.Completion)ˣ →* (w.Completion)ˣ).range) = 1 :=
    Finset.prod_eq_one fun w _ =>
      NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isComplex w
        (hcx w) hℓ.pos
  rw [hinf, mul_one] at key
  rw [← key]
  exact Finset.prod_coe_sort S (fun v => Nat.card ((v.adicCompletion F)ˣ ⧸
    (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range))

end C0Y

namespace C0Y

variable {F : Type} [Field F] [NumberField F]

theorem relIndex_locPow_unit {ℓ : ℕ} (hℓ : ℓ.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
    (hcx : ∀ w : InfinitePlace F, w.IsComplex) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (hcl : M4aHerbrand.principalIdeles (𝓞 F) F ⊔
      NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S : Set (HeightOneSpectrum (𝓞 F))) = ⊤) :
    (locPow (F := F) ℓ S).relIndex ((↑S : Set (HeightOneSpectrum (𝓞 F))).unit F) =
      ℓ ^ (S.card + Fintype.card (InfinitePlace F)) := by
  classical
  set U := (↑S : Set (HeightOneSpectrum (𝓞 F))).unit F
  have hμ : (primitiveRoots ℓ F).Nonempty := ⟨ζ, (mem_primitiveRoots hℓ.pos).mpr hζ⟩
  have hsub : (locPow (F := F) ℓ S).subgroupOf U = (powMonoidHom ℓ : U →* U).range := by
    ext u
    rw [Subgroup.mem_subgroupOf, mem_locPow, MonoidHom.mem_range]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom F hℓ hμ S ∅ hSℓ hcl
        (fun x _ => ⟨1, fun v _ => by simp, fun v hv => absurd hv (Finset.notMem_empty v)⟩)
        ((u : Fˣ) : F) (fun v hv _ => u.2 v hv)
        (fun v hv => by
          obtain ⟨d, hd⟩ := h v hv
          refine ⟨(d : v.adicCompletion F), ?_⟩
          have := congrArg Units.val hd
          simpa [emb] using this.symm)
        (fun w hw => absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr (hcx w)))
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_pow hℓ.ne_zero] at hc
        exact (u : Fˣ).ne_zero hc
      have hcU : Units.mk0 c hc0 ∈ U := by
        intro v hv
        have h1 : v.valuation F c ^ ℓ = 1 := by
          rw [← map_pow, ← hc]; exact u.2 v hv
        exact (pow_eq_one_iff_left hℓ.ne_zero).mp h1
      refine ⟨⟨Units.mk0 c hc0, hcU⟩, ?_⟩
      ext
      simp [hc]
    · rintro ⟨c, rfl⟩ v _
      exact ⟨emb F v c, by simp⟩
  rw [Subgroup.relIndex, hsub, Subgroup.index,
    NumberField.natCard_sUnit_quotient_range_powMonoidHom F _ hμ]
  congr 1
  have hcard : Nat.card (↑S : Set (HeightOneSpectrum (𝓞 F))) = S.card := Nat.card_eq_finsetCard S
  have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  rw [hcard, NumberField.Units.rank]
  omega

end C0Y

end
end
end

section
section
/-! C0Y: clauses 1–4 of C0-H from a local-symbol package. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain

noncomputable section

namespace C0Y

variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ}

/-- `H` composed into `Fˣ`. -/
def toUnitsPair (H : Fˣ →* Fˣ →* rootsOfUnity ℓ F) : Fˣ →* Fˣ →* Fˣ where
  toFun x := (rootsOfUnity ℓ F).subtype.comp (H x)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem toUnitsPair_apply (H : Fˣ →* Fˣ →* rootsOfUnity ℓ F) (x y : Fˣ) :
    toUnitsPair H x y = (H x y : Fˣ) := rfl

theorem toUnitsPair_eq_one (H : Fˣ →* Fˣ →* rootsOfUnity ℓ F) (x y : Fˣ) :
    toUnitsPair H x y = 1 ↔ H x y = 1 := by
  rw [toUnitsPair_apply]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

theorem SymbolPkg.HS_nondeg (P : SymbolPkg F ℓ) (hℓ : 0 < ℓ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : Fˣ) (hx : ∀ y, P.HS S x y = 1) : x ∈ locPow ℓ S := by
  classical
  rw [mem_locPow]
  intro v hv
  by_contra hnot
  have : ¬ ∀ b, P.h v x b = 1 := fun h => hnot (P.nondeg v x h)
  push_neg at this
  obtain ⟨b, hb⟩ := this
  let b' : (w : HeightOneSpectrum (𝓞 F)) → (w.adicCompletion F)ˣ := fun w =>
    if h : w = v then h ▸ b else 1
  obtain ⟨y, hy⟩ := exists_approx S hℓ b'
  have hyv : P.h v x (emb F v y) = P.h v x b := by
    have := hy v hv
    simp only [b', dif_pos rfl] at this
    have h2 : emb F v y = (emb F v y * b⁻¹) * b := by group
    rw [h2, map_mul, P.h_of_mem_range v x this, one_mul]
  have hother : ∀ w ∈ S, w ≠ v → P.hv w x y = 1 := by
    intro w hw hwv
    have := hy w hw
    simp only [b', dif_neg hwv, inv_one, mul_one] at this
    exact P.h_of_mem_range w x this
  have := hx y
  rw [P.HS_apply, Finset.prod_eq_single v hother (fun h => absurd hv h), SymbolPkg.hv_apply,
    hyv] at this
  exact hb this

/-- Clauses 1–4 of C0-H for the pairing `H_S`. -/
theorem SymbolPkg.clauses (P : SymbolPkg F ℓ) (hℓ : ℓ.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
    (hcx : ∀ w : InfinitePlace F, w.IsComplex) {c : Fˣ} (hc : c ^ ℓ = -1)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (hcl : M4aHerbrand.principalIdeles (𝓞 F) F ⊔
      NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S : Set (HeightOneSpectrum (𝓞 F))) = ⊤) :
    (∀ x, P.HS S x x = 1) ∧
    (∀ u ∈ (↑S : Set (HeightOneSpectrum (𝓞 F))).unit F,
      ∀ u' ∈ (↑S : Set (HeightOneSpectrum (𝓞 F))).unit F, P.HS S u u' = 1) ∧
    (∀ x, (∀ u ∈ (↑S : Set (HeightOneSpectrum (𝓞 F))).unit F, P.HS S x u = 1) →
      ∃ u ∈ (↑S : Set (HeightOneSpectrum (𝓞 F))).unit F, P.HS S (x * u⁻¹) = 1) ∧
    Finite (Fˣ ⧸ (P.HS S).ker) := by
  classical
  set U := (↑S : Set (HeightOneSpectrum (𝓞 F))).unit F
  have halt : ∀ x, P.HS S x x = 1 := P.HS_alt S hc
  have hiso : ∀ u ∈ U, ∀ u' ∈ U, P.HS S u u' = 1 := fun u hu u' hu' =>
    P.HS_unit S hSℓ u u' (fun v hv => hu v hv) (fun v hv => hu' v hv)
  have hidx := index_locPow hℓ hζ hcx S hSℓ
  have hrel := relIndex_locPow_unit hℓ hζ hcx S hSℓ hcl
  have hne : (locPow (F := F) ℓ S).index ≠ 0 := by
    rw [hidx]; exact pow_ne_zero _ hℓ.ne_zero
  haveI : (locPow (F := F) ℓ S).FiniteIndex := ⟨hne⟩
  haveI : Finite (Fˣ ⧸ locPow (F := F) ℓ S) := Subgroup.finite_quotient_of_finiteIndex
  have hle : locPow (F := F) ℓ S ≤ (P.HS S).ker := fun x hx => by
    rw [MonoidHom.mem_ker]; ext y; simp [P.HS_locPow_left S x y hx]
  refine ⟨halt, hiso, fun x hx => ?_, ?_⟩
  · have key := mem_sup_of_forall_eq_one (toUnitsPair (P.HS S)) (locPow ℓ S) U
      (fun x => (toUnitsPair_eq_one _ x x).mpr (halt x))
      (fun x y hy => (toUnitsPair_eq_one _ x y).mpr (P.HS_locPow_right S x y hy))
      (fun x hx => P.HS_nondeg hℓ.pos S x fun y => (toUnitsPair_eq_one _ x y).mp (hx y))
      (fun u hu u' hu' => (toUnitsPair_eq_one _ u u').mpr (hiso u hu u' hu'))
      (by rw [hidx, hrel, ← pow_mul, mul_comm])
      x (fun u hu => (toUnitsPair_eq_one _ x u).mpr (hx u hu))
    obtain ⟨u, hu, l, hl, rfl⟩ := Subgroup.mem_sup.mp key
    refine ⟨u, hu, ?_⟩
    have : u * l * u⁻¹ = l := by rw [mul_comm u l, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact hle hl
  · haveI : (P.HS S).ker.FiniteIndex := Subgroup.finiteIndex_of_le hle
    exact Subgroup.finite_quotient_of_finiteIndex

end C0Y

end
end
end

section
section
/-!
# Transport of `AllowedGen` along a field isomorphism

Used to move from `F : Type u` to the universe-0 copy `CyclotomicField n ℚ`.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

namespace C0R

/-! ### Generic facts on ideals along a ring equivalence -/

section Ideals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem mem_map_equiv (f : R ≃+* S) (I : Ideal R) (y : S) : y ∈ I.map f ↔ f.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, f.symm_apply_apply]; exact hx,
    fun h => ⟨_, h, f.apply_symm_apply y⟩⟩

theorem map_equiv_le_iff (f : R ≃+* S) {I J : Ideal R} : I.map f ≤ J.map f ↔ I ≤ J := by
  constructor
  · intro h x hx
    have : f x ∈ J.map f := h ((mem_map_equiv f I _).2 (by simpa using hx))
    simpa using (mem_map_equiv f J _).1 this
  · intro h y hy
    exact (mem_map_equiv f J y).2 (h ((mem_map_equiv f I y).1 hy))

theorem map_equiv_symm_map (f : R ≃+* S) (I : Ideal R) : (I.map f).map f.symm = I := by
  ext x
  rw [mem_map_equiv, RingEquiv.symm_symm, mem_map_equiv, RingEquiv.symm_apply_apply]

theorem map_equiv_coe (f : R ≃+* S) (I : Ideal R) : I.map (f : R →+* S) = I.map f := rfl

end Ideals

/-! ### The equivalences -/

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

omit [NumberField F] [NumberField F'] in
theorem mapRingEquiv_symm (e : F ≃+* F') :
    RingOfIntegers.mapRingEquiv e.symm = (RingOfIntegers.mapRingEquiv e).symm := by
  ext x; rfl

/-- `S`-integrality transports along `e`. -/
theorem mem_integer_map (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) :
    e x ∈ (placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e))).integer F' := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro v' hv'
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v'.asIdeal.comap (eO : 𝓞 F →+* 𝓞 F')
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        apply v'.ne_bot
        rw [← Ideal.map_comap_of_surjective (eO : 𝓞 F →+* 𝓞 F') eO.surjective v'.asIdeal, h,
          Ideal.map_bot] }
  have hv : v ∉ placesOf 𝔪 := by
    intro h
    apply hv'
    change 𝔪.map eO ≤ v'.asIdeal
    rw [← map_equiv_coe]
    exact Ideal.map_le_iff_le_comap.2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x (hx v hv)
  have hd : eO d ∉ v'.asIdeal := d.2
  have hnd' : e x * algebraMap (𝓞 F') F' (eO d) = algebraMap (𝓞 F') F' (eO n) := by
    have := congrArg e hnd
    rw [map_mul] at this
    exact this
  have h1 : v'.valuation F' (algebraMap (𝓞 F') F' (eO d)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h2 : v'.valuation F' (algebraMap (𝓞 F') F' (eO n)) ≤ 1 := v'.valuation_le_one _
  rw [← hnd', map_mul, h1, mul_one] at h2
  exact h2

/-- The ring `R = 𝓞_S` transports along `e`. -/
def sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) :
    SInt 𝔪 ≃+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)) where
  toFun x := ⟨e x, mem_integer_map e 𝔪 x x.2⟩
  invFun y := ⟨e.symm y, by
    have := mem_integer_map e.symm (𝔪.map (RingOfIntegers.mapRingEquiv e)) y y.2
    rwa [mapRingEquiv_symm, map_equiv_symm_map] at this⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

@[simp] theorem sIntEquiv_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ((sIntEquiv e 𝔪 x : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) : F') = e x := rfl

@[simp] theorem sIntEquiv_symm_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F))
    (y : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) :
    (((sIntEquiv e 𝔪).symm y : SInt 𝔪) : F) = e.symm y := rfl

theorem map_map_sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    (I.map (algebraMap (𝓞 F) (SInt 𝔪))).map (sIntEquiv e 𝔪) =
      (I.map (RingOfIntegers.mapRingEquiv e)).map
        (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)))) := by
  show Ideal.map ((sIntEquiv e 𝔪 : SInt 𝔪 →+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.map (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map ((RingOfIntegers.mapRingEquiv e : 𝓞 F →+* 𝓞 F')))
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

theorem absNorm_map_equiv (e : F ≃+* F') (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

theorem isExterior_map (e : F ≃+* F') {𝔪 I : Ideal (𝓞 F)} (h : IsExterior 𝔪 I) :
    IsExterior (𝔪.map (RingOfIntegers.mapRingEquiv e)) (I.map (RingOfIntegers.mapRingEquiv e)) := by
  refine ⟨fun h0 => h.1 ?_, ?_⟩
  · exact (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).1 h0
  · rw [← Ideal.map_sup, h.2, Ideal.map_top]

/-! ### Uniqueness of the sixth root of unity modulo `P` -/

theorem eq_of_pow_six {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) (h6 : (6 : R) ∉ Q)
    {a b : R} (ha : a ^ 6 = 1) (hb : b ^ 6 = 1) (hab : a - b ∈ Q) : a = b := by
  set η := b * a ^ 5 with hη
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ 5 * (a - b) := by rw [hη]; linear_combination (-1 : R) * ha
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · have : b = a := calc
        b = b * a ^ 6 := by rw [ha, mul_one]
        _ = (b * a ^ 5) * a := by ring
        _ = a := by rw [← hη, hη1, one_mul]
    exact this.symm
  · exfalso
    have hη6 : η ^ 6 = 1 := by
      rw [hη]
      calc (b * a ^ 5) ^ 6 = b ^ 6 * (a ^ 6) ^ 5 := by ring
        _ = 1 := by rw [ha, hb]; ring
    have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5 = 0 := by
      have : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) = 0 := by
        linear_combination hη6
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hη1
      · exact h
    apply h6
    have : (6 : R) = (1 - η) * (5 + 4 * η + 3 * η ^ 2 + 2 * η ^ 3 + η ^ 4) +
        (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) := by ring
    rw [this, hsum, add_zero]
    exact Q.mul_mem_right _ h1

/-! ### The residue symbol transports -/

theorem sexticResidueSymbol_transport (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F))
    (h6 : P ⊔ Ideal.span {6} = ⊤) (x : SInt 𝔪) :
    sexticResidueSymbol (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (P.map (RingOfIntegers.mapRingEquiv e)) (sIntEquiv e 𝔪 x) =
      sexticResidueSymbol ι 𝔪 P x := by
  classical
  set eO := RingOfIntegers.mapRingEquiv e
  set eS := sIntEquiv e 𝔪
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set f' := algebraMap (𝓞 F') (SInt (𝔪.map eO))
  set Q := P.map f
  have hQ' : (P.map eO).map f' = Q.map eS := (map_map_sIntEquiv e 𝔪 P).symm
  have hmem : ∀ y : SInt 𝔪, eS y ∈ (P.map eO).map f' ↔ y ∈ Q := fun y => by
    rw [hQ', mem_map_equiv, RingEquiv.symm_apply_apply]
  have hN : Ideal.absNorm (P.map eO) = Ideal.absNorm P := absNorm_map_equiv e P
  unfold sexticResidueSymbol
  simp only [Ideal.Quotient.eq_zero_iff_mem]
  by_cases hx : x ∈ Q
  · rw [if_pos hx, if_pos ((hmem x).2 hx)]
  rw [if_neg hx, if_neg (fun h => hx ((hmem x).1 h)), hN]
  set k := (Ideal.absNorm P - 1) / 6
  -- `6 ∉ Q`
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h6m
    apply hx
    have : Q = ⊤ := by
      rw [eq_top_iff, ← Ideal.map_top f, ← h6, Ideal.map_sup]
      refine sup_le le_rfl ?_
      rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.span_le,
        Set.singleton_subset_iff]
      exact h6m
    rw [this]; trivial
  have hC : ∀ ζ : 𝓞 F, (ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k) ↔
      ((eO ζ) ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' (eO ζ)) =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k) := by
    intro ζ
    apply and_congr
    · rw [← map_pow, ← map_one eO]
      exact eO.injective.eq_iff.symm
    · rw [← map_pow, ← map_pow, Ideal.Quotient.eq, Ideal.Quotient.eq, ← map_pow eS,
        show f' (eO ζ) = eS (f ζ) from rfl, ← map_sub, hmem]
  have huniq : ∀ ζ₁ ζ₂ : 𝓞 F, (ζ₁ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₁) = Ideal.Quotient.mk Q x ^ k) →
      (ζ₂ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₂) = Ideal.Quotient.mk Q x ^ k) → ζ₁ = ζ₂ := by
    intro ζ₁ ζ₂ h1 h2
    have hsub : f ζ₁ - f ζ₂ ∈ Q := by
      rw [← Ideal.Quotient.eq, h1.2, h2.2]
    have := eq_of_pow_six Q h6Q (by rw [← map_pow, h1.1, map_one])
      (by rw [← map_pow, h2.1, map_one]) hsub
    have h' : ((f ζ₁ : SInt 𝔪) : F) = ((f ζ₂ : SInt 𝔪) : F) := by rw [this]
    exact RingOfIntegers.ext h'
  by_cases h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k
  · have h' : ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k :=
      ⟨eO h.choose, (hC _).1 h.choose_spec⟩
    rw [dif_pos h, dif_pos h']
    have hspec : eO (eO.symm h'.choose) = h'.choose := eO.apply_symm_apply _
    have hC' := (hC (eO.symm h'.choose)).2 (by rw [hspec]; exact h'.choose_spec)
    have := huniq _ _ hC' h.choose_spec
    rw [← this]
    simp [eO]
  · have h' : ¬ ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k := by
      rintro ⟨ζ', hζ'⟩
      apply h
      refine ⟨eO.symm ζ', (hC _).2 ?_⟩
      rw [eO.apply_symm_apply]; exact hζ'
    rw [dif_neg h, dif_neg h']

/-! ### `AllowedGen` transports -/

/-- `SmallPrimesDvd` transports. -/
theorem smallPrimesDvd_map (e : F ≃+* F') {N₀ : ℕ} {𝔪 : Ideal (𝓞 F)} (h : SmallPrimesDvd N₀ 𝔪) :
    SmallPrimesDvd N₀ (𝔪.map (RingOfIntegers.mapRingEquiv e)) := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro P' hP' hP'0 hN
  set P := P'.map eO.symm
  have hPP : P.map eO = P' := by
    have := map_equiv_symm_map eO.symm P'
    rwa [RingEquiv.symm_symm] at this
  have hP : P.IsPrime := Ideal.map_isPrime_of_equiv eO.symm
  have hP0 : P ≠ ⊥ := fun h0 => hP'0 (by rw [← hPP, h0, Ideal.map_bot])
  have hNP : Ideal.absNorm P ≤ N₀ := by rw [← absNorm_map_equiv e P, hPP]; exact hN
  rw [← hPP]
  exact (map_equiv_le_iff eO).2 (h P hP hP0 hNP)

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-! C0Y: valuations of prime generators in `SInt 𝔪` and the sextic residue symbol. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace C0Y

variable {F : Type} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem sInt_val_le_one (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

theorem coe_algebraMap_sInt (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

/-- Elements of `P · SInt` have `v_P < 1`. -/
theorem val_lt_one_of_mem_map (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    {z : SInt 𝔪} (hz : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (z : F) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_algebraMap_sInt]
    exact (v.valuation_lt_one_iff_mem (K := F) a).mpr ha
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Subalgebra.coe_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul a x _ hx =>
    simp only [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * v.valuation F (x : F) :=
          mul_le_mul_left (sInt_val_le_one a v hv) _
      _ < 1 := by rw [one_mul]; exact hx

/-- Valuations of a generator of `P · SInt`. -/
theorem val_generator (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ w.asIdeal → w ≠ v → w.valuation F (p : F) = 1 := by
  have hpmem : p ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hp]; exact Ideal.subset_span rfl
  have hlt := val_lt_one_of_mem_map v hv hpmem
  -- every `a ∈ P` is a multiple of `p` in `SInt`
  have hdiv : ∀ a ∈ v.asIdeal, ∃ s : SInt 𝔪, algebraMap (𝓞 F) F a = (p : F) * (s : F) := by
    intro a ha
    have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ Ideal.span {p} := by
      rw [hp]; exact Ideal.mem_map_of_mem _ ha
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp this
    refine ⟨s, ?_⟩
    rw [← coe_algebraMap_sInt (𝔪 := 𝔪), ← hs, Subalgebra.coe_mul, mul_comm]
  refine ⟨?_, fun w hw hwv => ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer' F
    have hπmem : π ∈ v.asIdeal := by
      rw [← v.valuation_lt_one_iff_mem (K := F), hπ]; exact by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    obtain ⟨s, hs⟩ := hdiv π hπmem
    have h1 : v.valuation F (p : F) * v.valuation F (s : F) = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← hs, hπ]
    have hs1 := sInt_val_le_one s v hv
    have hp0 : v.valuation F (p : F) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact WithZero.exp_ne_zero h1.symm
    have hge : WithZero.exp (-1 : ℤ) ≤ v.valuation F (p : F) := by
      rw [← h1]; exact mul_le_of_le_one_right' hs1
    have hle : v.valuation F (p : F) ≤ WithZero.exp (-1 : ℤ) := by
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hp0
      rw [← hk] at hlt ⊢
      rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl] at hlt
      have : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [this, WithZero.exp_lt_exp] at hlt
      rw [this, WithZero.exp_le_exp]
      omega
    exact le_antisymm hle hge
  · -- `P ⊄ w`
    have hnle : ¬ v.asIdeal ≤ w.asIdeal := by
      intro hle
      have := v.isMaximal.eq_of_le w.isPrime.ne_top hle
      exact hwv (HeightOneSpectrum.ext this.symm)
    obtain ⟨a, ha, haw⟩ := Set.not_subset.mp hnle
    obtain ⟨s, hs⟩ := hdiv a ha
    have h1 : w.valuation F (p : F) * w.valuation F (s : F) = 1 := by
      rw [← map_mul, ← hs]; exact (w.valuation_eq_one_iff_notMem (K := F)).mpr haw
    have hp1 := sInt_val_le_one p w hw
    have hs1 := sInt_val_le_one s w hw
    by_contra hne
    have hlt : w.valuation F (p : F) < 1 := lt_of_le_of_ne hp1 hne
    have : w.valuation F (p : F) * w.valuation F (s : F) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt hs1) le_rfl
    rw [h1] at this
    exact lt_irrefl _ this

/-- Elements of `SInt` with `v_P < 1` lie in `P · SInt` (given a generator). -/
theorem mem_map_of_val_lt_one (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (z : SInt 𝔪)
    (hz : v.valuation F (z : F) < 1) : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨hpv, hpw⟩ := val_generator v hv p hp
  have hp0 : (p : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hpv; exact WithZero.exp_ne_zero hpv.symm
  have hq : (z : F) / (p : F) ∈ (placesOf 𝔪).integer F := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      rw [map_div₀, hpv]
      by_cases hz0 : w.valuation F (z : F) = 0
      · rw [hz0, zero_div]; exact zero_le
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hz0
      rw [← hk] at hz ⊢
      have e : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [e, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [e, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [map_div₀, hpw w hw hwv, div_one]
      exact sInt_val_le_one z w hw
  have : z = p * ⟨(z : F) / (p : F), hq⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    field_simp
  rw [← hp, this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- The sextic residue symbol at an exterior prime with generator: `6 ∣ N P − 1`, and
`χ_P(y) = ι ξ` for the sixth root of unity `ξ ≡ y^{(N P − 1)/6} (mod P)`. -/
theorem sextic_spec (ι : F →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    (p : SInt 𝔪) (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (y : SInt 𝔪)
    (hy : v.valuation F (y : F) = 1) :
    6 ∣ Ideal.absNorm v.asIdeal - 1 ∧ ∃ ξ : 𝓞 F, ξ ^ 6 = 1 ∧
      v.valuation F ((y : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - algebraMap (𝓞 F) F ξ) < 1 ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal y = ι (algebraMap (𝓞 F) F ξ) := by
  classical
  set P := v.asIdeal with hPdef
  letI : Field (𝓞 F ⧸ P) := Ideal.Quotient.field P
  haveI : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P v.ne_bot
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hinj : ∀ a b : 𝓞 F, a ^ 6 = 1 → b ^ 6 = 1 →
      Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → a = b := fun a b ha hb h =>
    C0R.eq_of_pow_six P h6 ha hb (Ideal.Quotient.eq.mp h)
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk P z6) 6 := by
    refine ⟨by rw [← map_pow, hz6.pow_eq_one, map_one], fun l hl => ?_⟩
    have : z6 ^ l = 1 := hinj _ _ (by rw [← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow])
      (one_pow 6) (by rw [map_pow, hl, map_one])
    exact hz6.dvd_of_pow_eq_one l this
  have h6N : 6 ∣ Ideal.absNorm P - 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk P z6) (hη.ne_zero (by norm_num))
    rw [hcard] at this
    exact hη.dvd_of_pow_eq_one _ this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (y : F) hy.le
  have hd : (d : 𝓞 F) ∉ P := d.2
  have hdv : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    intro h0; rw [h0, map_zero] at hdv; exact zero_ne_one hdv
  have hn : (n : 𝓞 F) ∉ P := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, hy, hdv, one_mul]
  set k := (Ideal.absNorm P - 1) / 6 with hk
  set u : 𝓞 F ⧸ P := Ideal.Quotient.mk P n * (Ideal.Quotient.mk P d)⁻¹ with hu
  have hmd : Ideal.Quotient.mk P (d : 𝓞 F) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmn : Ideal.Quotient.mk P n ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hu0 : u ≠ 0 := mul_ne_zero hmn (inv_ne_zero hmd)
  have hu6 : (u ^ k) ^ 6 = 1 := by
    rw [← pow_mul, hk, Nat.div_mul_cancel h6N, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one u hu0
  obtain ⟨i, -, hi⟩ := hη.eq_pow_of_pow_eq_one hu6
  set ξ := z6 ^ i with hξ
  have hξ6 : ξ ^ 6 = 1 := by rw [hξ, ← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow]
  have hcong : n ^ k - ξ * (d : 𝓞 F) ^ k ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, map_pow, map_pow, hi,
      hu, mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hmd), mul_one, sub_self]
  have hval : v.valuation F ((y : F) ^ k - algebraMap (𝓞 F) F ξ) < 1 := by
    have hyd : (y : F) = algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F d := by
      rw [← hnd, mul_div_cancel_right₀ _ hdF]
    have : (y : F) ^ k - algebraMap (𝓞 F) F ξ =
        algebraMap (𝓞 F) F (n ^ k - ξ * (d : 𝓞 F) ^ k) / (algebraMap (𝓞 F) F d) ^ k := by
      rw [hyd, eq_div_iff (pow_ne_zero _ hdF)]
      simp only [map_sub, map_mul, map_pow]
      rw [sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdF)]
    rw [this, map_div₀, map_pow, hdv, one_pow, div_one]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr hcong
  refine ⟨h6N, ξ, hξ6, hval, ?_⟩
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set Q := P.map f
  have hyQ : y ∉ Q := fun h => by
    have := val_lt_one_of_mem_map v hv h; rw [hy] at this; exact lt_irrefl _ this
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h
    have := val_lt_one_of_mem_map v hv h
    have e : ((6 : SInt 𝔪) : F) = algebraMap (𝓞 F) F 6 := by rw [map_ofNat]; rfl
    rw [e, (v.valuation_eq_one_iff_notMem (K := F)).mpr h6] at this
    exact lt_irrefl _ this
  have hex : f ξ - y ^ k ∈ Q := by
    apply mem_map_of_val_lt_one v hv p hp
    have e : ((f ξ - y ^ k : SInt 𝔪) : F) = -((y : F) ^ k - algebraMap (𝓞 F) F ξ) := by
      simp [f, coe_algebraMap_sInt]
    rw [e, Valuation.map_neg]; exact hval
  unfold sexticResidueSymbol
  rw [if_neg (by rwa [Ideal.Quotient.eq_zero_iff_mem])]
  have hE : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q y ^ k :=
    ⟨ξ, hξ6, by rw [← map_pow, Ideal.Quotient.eq]; exact hex⟩
  rw [dif_pos hE]
  have hch := hE.choose_spec
  have hsub : f hE.choose - f ξ ∈ Q := by
    rw [← Ideal.Quotient.eq, hch.2, ← map_pow, Ideal.Quotient.eq]
    have : y ^ k - f ξ = -(f ξ - y ^ k) := by ring
    rw [this]; exact Q.neg_mem hex
  have heq := C0R.eq_of_pow_six Q h6Q (by rw [← map_pow, hch.1, map_one])
    (by rw [← map_pow, hξ6, map_one]) hsub
  have : hE.choose = ξ := by
    have h' := congrArg (fun z : SInt 𝔪 => (z : F)) heq
    simp only [f, coe_algebraMap_sInt] at h'
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F h'
  rw [this]

end C0Y

end
end
end

section
section
/-!
# C0-P: the `S`-integers form a PID once `S` contains the small primes

Every ideal class contains a nonzero ideal of bounded norm; once `𝔪` is divisible by every prime of
norm at most that bound, every ideal of `R = 𝓞_S` is principal.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

/-- `𝔪 R = R` for `𝔪 ≠ 0`: a power `𝔪^h = (a)` is principal, and `a⁻¹ ∈ R`. -/
theorem map_self_eq_top (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
  classical
  have h𝔪' : 𝔪 ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔪
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hpow : 𝔪 ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem h𝔪' h
  have hprin : (𝔪 ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hpow]
    have : (⟨𝔪 ^ h, hpow⟩ : (Ideal (𝓞 F))⁰) = (⟨𝔪, h𝔪'⟩ : (Ideal (𝓞 F))⁰) ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := hprin.principal
  rw [Ideal.submodule_span_eq] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
    exact (pow_ne_zero h h𝔪) ha
  have hamem : a ∈ 𝔪 := by
    have : a ∈ 𝔪 ^ h := by rw [ha]; exact Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_self hpos.ne' this
  -- `a⁻¹` is an `S`-integer
  have hinv : ((a : F))⁻¹ ∈ (placesOf 𝔪).integer F := by
    intro v hv
    have hav : a ∉ v.asIdeal := by
      intro hav
      apply hv
      change 𝔪 ≤ v.asIdeal
      have : 𝔪 ^ h ≤ v.asIdeal := by
        rw [ha, Ideal.span_le, Set.singleton_subset_iff]; exact hav
      exact v.isPrime.le_of_pow_le this
    rw [map_inv₀]
    have : v.valuation F (a : F) = 1 := by
      rw [show (a : F) = algebraMap (𝓞 F) F a from rfl, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact hav
    rw [this, inv_one]
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : SInt 𝔪) = algebraMap (𝓞 F) (SInt 𝔪) a * ⟨_, hinv⟩ := by
    apply Subtype.ext
    change (1 : F) = (a : F) * (a : F)⁻¹
    rw [mul_inv_cancel₀]
    exact_mod_cast ha0
  rw [h1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hamem)

/-- An ideal all of whose prime divisors contain `𝔪` becomes the unit ideal in `R`. -/
theorem map_eq_top_of_primes (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (J : Ideal (𝓞 F))
    (hprimes : ∀ Q : Ideal (𝓞 F), Q.IsPrime → J ≤ Q → 𝔪 ≤ Q) :
    J.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hne
  have hQ : (M.comap (algebraMap (𝓞 F) (SInt 𝔪))).IsPrime := Ideal.comap_isPrime _ M
  have hJQ : J ≤ M.comap (algebraMap (𝓞 F) (SInt 𝔪)) := Ideal.map_le_iff_le_comap.1 hJM
  have h𝔪Q := hprimes _ hQ hJQ
  have : 𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ M :=
    Ideal.map_le_iff_le_comap.2 h𝔪Q
  rw [map_self_eq_top 𝔪 h𝔪, top_le_iff] at this
  exact hM.ne_top this

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-!
# C0-L: an isotropic complement of a Lagrangian, for an alternating form

Over a field `K`, let `B` be an alternating bilinear form on a finite-dimensional space `V`, and
`E` an isotropic subspace with `E^⊥ ≤ E ⊔ ker B`. Then some isotropic `W` has `E ⊔ W = ⊤`.
-/

namespace ArtinPrimitiveRoots

open Module LinearMap

namespace C0R

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-!
# From an alternating pairing on a group to an isotropic complement of `U`

Group-theoretic form of the linear algebra used for Lemma 3.2: `H : G →* G →* M` with
`M` of exponent `ℓ` (embedded in `ZMod ℓ`), alternating, `U` isotropic and `U^⊥ ⊆ U · rad H`,
and `G / rad H` finite. Then there is an isotropic "`B`" (`Good`) with `G = B · U`, stable under
`ℓ`-th powers.
-/

namespace ArtinPrimitiveRoots

set_option linter.style.haveILetI false

namespace C0R

variable {G : Type*} [CommGroup G] {M : Type*} [CommGroup M]

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-!
# Glue: allowed generators from the `S`-Hilbert pairings for `ℓ = 2, 3`

For a fixed field and modulus (any universe): if `R` is a PID and the sextic residue symbols are
controlled by alternating pairings `H₂, H₃` as in C0-H, then `AllowedGen ι 𝔪` is nonempty.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain UniqueFactorizationMonoid

set_option linter.style.haveILetI false

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-!
# C0: `exists_cutoff_nonempty_allowedGen` from C0-P, C0-L (proved) and C0-H (hypothesis)
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

set_option linter.style.haveILetI false

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

theorem smallPrimesDvd_mono {N N₁ : ℕ} {𝔪 : Ideal (𝓞 F)} (h : SmallPrimesDvd N₁ 𝔪)
    (hle : N ≤ N₁) : SmallPrimesDvd N 𝔪 :=
  fun P hP h0 hN => h P hP h0 (le_trans hN hle)

theorem sup_span_six_eq_top {N₀ : ℕ} {𝔪 P : Ideal (𝓞 F)}
    (hN : Ideal.absNorm (Ideal.span {(6 : 𝓞 F)}) ≤ N₀) (hs : SmallPrimesDvd N₀ 𝔪)
    (hP : P.IsPrime) (hE : IsExterior 𝔪 P) : P ⊔ Ideal.span {6} = ⊤ := by
  by_contra h
  have hmax : P.IsMaximal := hP.isMaximal hE.1
  have hle : Ideal.span {(6 : 𝓞 F)} ≤ P := by
    have := hmax.eq_of_le h le_sup_left
    rw [this]; exact le_sup_right
  have h60 : (6 : 𝓞 F) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap (𝓞 F) F) h0
    simp at this
  have hn0 : Ideal.absNorm (Ideal.span {(6 : 𝓞 F)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact h60
  have hNP : Ideal.absNorm P ≤ N₀ :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Ideal.absNorm_dvd_absNorm_of_le hle)) hN
  have h𝔪 := hs P hP hE.1 hNP
  apply hP.ne_top
  rw [← hE.2, sup_eq_left.2 h𝔪]

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-! C0Y: clause 5 (reciprocity) and the assembly of C0-H from local-symbol packages. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain ArtinPrimitiveRoots
open scoped nonZeroDivisors

noncomputable section

namespace C0Y

variable {F : Type} [Field F] [NumberField F]

theorem val_pow_sub_pow_lt_one (v : HeightOneSpectrum (𝓞 F)) {a b : F}
    (ha : v.valuation F a ≤ 1) (hb : v.valuation F b ≤ 1) (hab : v.valuation F (a - b) < 1)
    (m : ℕ) (hm : 0 < m) : v.valuation F (a ^ m - b ^ m) < 1 := by
  rw [← Commute.geom_sum₂_mul (Commute.all a b) m, map_mul]
  have hG : v.valuation F (∑ i ∈ Finset.range m, a ^ i * b ^ (m - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' ha _) (pow_le_one' hb _)
  calc _ ≤ 1 * v.valuation F (a - b) := mul_le_mul_left hG _
    _ < 1 := by rw [one_mul]; exact hab

end C0Y

namespace C0Y

/-- The packages that C0-H needs: local `ℓ`-th Hilbert symbols for totally complex number
fields containing `μ_ℓ`. -/
def PkgHyp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ), ℓ.Prime → (∃ ζ : F, IsPrimitiveRoot ζ ℓ) →
    (∀ w : InfinitePlace F, w.IsComplex) → Nonempty (SymbolPkg F ℓ)

end C0Y

end
end
end

section
section
/-! C0Z: the local-symbol package from the idelic Artin map, and C0-H. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace C0Z

/-- **The local Hilbert-symbol package exists** (from the library's idelic Artin map). -/
theorem pkgHyp : C0Y.PkgHyp := by
  intro F _ _ ℓ hℓ hζ' hcx
  obtain ⟨ζ, hζ⟩ := hζ'
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact ⟨{ h := symHom F hζ
           steinberg := fun v a => sym_steinberg F hζ hℓ v a
           prod_eq_one := fun a b T hT => prod_sym_eq_one F hζ hcx a b T hT
           nondeg := fun v a h => sym_nondeg F hζ v a h
           unit_unit := fun v hv a b ha hb => sym_unit_unit F hζ v hv a b ha hb
           tame := fun v hv a π ω ha hπ hω hc => sym_tame F hζ v hv a π ω ha hπ hω hc }⟩

end C0Z

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

end ArtinPrimitiveRoots

end
end
end

section
section
/-! L3B: the `S`-Hilbert pairings for `ℓ = 2, 3` with the properties used for SB (universe 0). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain ArtinPrimitiveRoots
open scoped nonZeroDivisors

noncomputable section

namespace L3B

open C0Y

variable {F : Type} [Field F] [NumberField F]

/-- The converse of clause 5: equal residue symbols give `H_S(p, p') = 1`. -/
theorem recip_conv {ℓ : ℕ} (P : SymbolPkg F ℓ) (hℓ : ℓ = 2 ∨ ℓ = 3) (ι : F →+* ℂ)
    {𝔪 : Ideal (𝓞 F)} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v, v ∈ S ↔ 𝔪 ≤ v.asIdeal)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (v v' : HeightOneSpectrum (𝓞 F)) (hvv : v ≠ v') (hv : ¬ 𝔪 ≤ v.asIdeal)
    (hv' : ¬ 𝔪 ≤ v'.asIdeal) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (h6' : (6 : 𝓞 F) ∉ v'.asIdeal)
    (p p' : SInt 𝔪) (x x' : Fˣ) (hx : (x : F) = p) (hx' : (x' : F) = p')
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hp' : Ideal.span {p'} = v'.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hχ : sexticResidueSymbol ι 𝔪 v.asIdeal p' = sexticResidueSymbol ι 𝔪 v'.asIdeal p) :
    P.HS S x x' = 1 := by
  classical
  have hm : ℓ * (6 / ℓ) = 6 := by rcases hℓ with rfl | rfl <;> norm_num
  have hmpos : 0 < 6 / ℓ := by rcases hℓ with rfl | rfl <;> norm_num
  have hℓv : ∀ w : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∉ w.asIdeal → (ℓ : 𝓞 F) ∉ w.asIdeal := by
    intro w h6w hℓw
    apply h6w
    have : (6 : 𝓞 F) = (ℓ : 𝓞 F) * ((6 / ℓ : ℕ) : 𝓞 F) := by
      rw [← Nat.cast_mul, hm]; norm_num
    rw [this]; exact w.asIdeal.mul_mem_right _ hℓw
  obtain ⟨hpv, hpw⟩ := val_generator v hv p hp
  obtain ⟨hpv', hpw'⟩ := val_generator v' hv' p' hp'
  have hp'v : v.valuation F (p' : F) = 1 := hpw' v hv hvv
  have hpv'' : v'.valuation F (p : F) = 1 := hpw v' hv' (Ne.symm hvv)
  obtain ⟨h6N, ξ, hξ6, hval, hsym⟩ := sextic_spec ι v hv p hp hz6 h6 p' hp'v
  obtain ⟨h6N', ξ', hξ6', hval', hsym'⟩ := sextic_spec ι v' hv' p' hp' hz6 h6' p hpv''
  have hint : ∀ (w : HeightOneSpectrum (𝓞 F)) (ξ : 𝓞 F), w.valuation F (algebraMap (𝓞 F) F ξ) ≤ 1 :=
    fun w ξ => w.valuation_le_one ξ
  have hexp : ∀ N : ℕ, 6 ∣ N - 1 → (N - 1) / ℓ = (N - 1) / 6 * (6 / ℓ) := by
    intro N hN
    obtain ⟨t, ht⟩ := hN
    rw [ht, Nat.mul_div_cancel_left _ (by norm_num : 0 < 6)]
    rcases hℓ with rfl | rfl <;> omega
  have t1 : ((P.h v x' (emb F v x) : Fˣ) : F) = algebraMap (𝓞 F) F ξ ^ (6 / ℓ) := by
    apply P.tame v (hℓv v h6) x' x _ (by rw [hx']; exact hp'v) (by rw [hx]; exact hpv)
    · rw [← map_pow, ← map_pow, ← pow_mul, mul_comm, hm, hξ6, map_one]
    · rw [hexp _ h6N, pow_mul, hx']
      exact val_pow_sub_pow_lt_one v (by rw [map_pow, hp'v, one_pow]) (hint v ξ) hval _ hmpos
  have t2 : ((P.h v' x (emb F v' x') : Fˣ) : F) = algebraMap (𝓞 F) F ξ' ^ (6 / ℓ) := by
    apply P.tame v' (hℓv v' h6') x x' _ (by rw [hx]; exact hpv'') (by rw [hx']; exact hpv')
    · rw [← map_pow, ← map_pow, ← pow_mul, mul_comm, hm, hξ6', map_one]
    · rw [hexp _ h6N', pow_mul, hx]
      exact val_pow_sub_pow_lt_one v' (by rw [map_pow, hpv'', one_pow]) (hint v' ξ') hval' _ hmpos
  have hξ : algebraMap (𝓞 F) F ξ = algebraMap (𝓞 F) F ξ' := by
    apply ι.injective
    rw [← hsym, ← hsym', hχ]
  have heq : P.h v' x (emb F v' x') = P.h v x' (emb F v x) := by
    apply Subtype.ext; apply Units.ext
    rw [t1, t2, hξ]
  have hvS : v ∉ S := fun h => hv ((hS v).mp h)
  have hv'S : v' ∉ S := fun h => hv' ((hS v').mp h)
  have hprod := P.prod_eq_one x x' (insert v (insert v' S)) (by
    intro w hw
    simp only [Finset.mem_insert, not_or] at hw
    obtain ⟨hwv, hwv', hwS⟩ := hw
    have hw𝔪 : ¬ 𝔪 ≤ w.asIdeal := fun h => hwS ((hS w).mpr h)
    exact P.unit_unit w (fun h => hwS (hSℓ w h)) x x' (by rw [hx]; exact hpw w hw𝔪 hwv)
      (by rw [hx']; exact hpw' w hw𝔪 hwv'))
  rw [Finset.prod_insert (by simp [hvv, hvS]), Finset.prod_insert hv'S] at hprod
  have hskew := P.skew v x x'
  simp only [SymbolPkg.hv_apply] at hskew
  rw [heq, ← mul_assoc, hskew, one_mul] at hprod
  rw [P.HS_apply]
  exact hprod

/-- The pairing package for SB. -/
theorem pair (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (ℓ : ℕ) (hℓ : ℓ = 2 ∨ ℓ = 3) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ H : Fˣ →* Fˣ →* rootsOfUnity ℓ F,
        (∀ x, H x x = 1) ∧
        (∀ u ∈ (placesOf 𝔪).unit F, ∀ u' ∈ (placesOf 𝔪).unit F, H u u' = 1) ∧
        (∀ x y : Fˣ, (∀ v ∈ placesOf 𝔪, emb F v x ∈
            (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range) →
          H x y = 1) ∧
        (∀ u ∈ (placesOf 𝔪).unit F, (∀ y, H u y = 1) → ∃ c ∈ (placesOf 𝔪).unit F, c ^ ℓ = u) ∧
        (∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P → IsExterior 𝔪 P' →
          P ≠ P' →
          ∀ (p p' : SInt 𝔪) (x x' : Fˣ), (x : F) = p → (x' : F) = p' →
            Ideal.span {p} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
            Ideal.span {p'} = P'.map (algebraMap (𝓞 F) (SInt 𝔪)) →
            sexticResidueSymbol ι 𝔪 P p' = sexticResidueSymbol ι 𝔪 P' p → H x x' = 1) := by
  classical
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζn := IsCyclotomicExtension.zeta_spec n ℚ F
  have hprim : ∀ d : ℕ, d ∣ n → ∃ z : F, IsPrimitiveRoot z d := by
    intro d hd
    obtain ⟨m, hm⟩ := hd
    exact ⟨_, hζn.pow hn0 (by rw [hm, mul_comm])⟩
  have hℓp : ℓ.Prime := by rcases hℓ with rfl | rfl <;> norm_num
  have hℓn : ℓ ∣ n := by
    rcases hℓ with rfl | rfl
    · exact dvd_trans (by norm_num) hn
    · exact dvd_trans (by norm_num) hn
  obtain ⟨ζ, hζ⟩ := hprim ℓ hℓn
  obtain ⟨z, hz⟩ := hprim 6 (dvd_trans (by norm_num) hn)
  let z6 : 𝓞 F := ⟨z, hz.isIntegral (by norm_num)⟩
  have hz6 : IsPrimitiveRoot z6 6 :=
    (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap (𝓞 F) F)
      (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mp hz
  have hcx : ∀ w : InfinitePlace F, w.IsComplex :=
    (IsCyclotomicExtension.Rat.isTotallyComplex (n := n) F
      (lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd hn0 hn))).isComplex
  obtain ⟨c, hc⟩ : ∃ c : Fˣ, c ^ ℓ = -1 := by
    rcases hℓ with rfl | rfl
    · obtain ⟨i, hi⟩ := hprim 4 (dvd_trans (by norm_num) hn)
      refine ⟨Units.mk0 i (hi.ne_zero (by norm_num)), Units.ext ?_⟩
      have h2 := hi.pow_of_dvd (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) ∣ 4)
      simpa using h2.eq_neg_one_of_two_right
    · exact ⟨-1, by norm_num⟩
  obtain ⟨P⟩ := C0Z.pkgHyp F ℓ hℓp ⟨ζ, hζ⟩ hcx
  let rep : ClassGroup (𝓞 F) → (Ideal (𝓞 F))⁰ :=
    fun C => Function.surjInv ClassGroup.mk0_surjective C
  have hrep : ∀ C, ClassGroup.mk0 (rep C) = C := fun C =>
    Function.surjInv_eq ClassGroup.mk0_surjective C
  set Nc := Finset.univ.sup fun C => Ideal.absNorm (rep C : Ideal (𝓞 F))
  set N6 := Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})
  refine ⟨max Nc N6, fun 𝔪 h𝔪 hsmall => ?_⟩
  have hfin := Ideal.finite_factors (I := 𝔪) h𝔪
  set S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ 𝔪 ≤ v.asIdeal := fun v => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]
  have hSet : (↑S : Set (HeightOneSpectrum (𝓞 F))) = placesOf 𝔪 := by
    ext v; rw [Finset.mem_coe, hS]; rfl
  have hle_norm : ∀ (v : HeightOneSpectrum (𝓞 F)) (J : Ideal (𝓞 F)), J ≠ ⊥ → J ≤ v.asIdeal →
      Ideal.absNorm J ≤ max Nc N6 → v ∈ S := by
    intro v J hJ hJv hN
    rw [hS]
    apply hsmall v.asIdeal v.isPrime v.ne_bot
    have hJn : Ideal.absNorm J ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hJ
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hJn) (Ideal.absNorm_dvd_absNorm_of_le hJv)) hN
  have h60 : Ideal.span {(6 : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h0
    have := congrArg (algebraMap (𝓞 F) F) h0
    simp at this
  have hSℓ : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply hle_norm v _ h60 _ (le_max_right _ _)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : (6 : 𝓞 F) = (ℓ : 𝓞 F) * ((6 / ℓ : ℕ) : 𝓞 F) := by
      rcases hℓ with rfl | rfl <;> norm_num
    rw [SetLike.mem_coe, this]; exact v.asIdeal.mul_mem_right _ hv
  have hcl : M4aHerbrand.principalIdeles (𝓞 F) F ⊔
      NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S : Set (HeightOneSpectrum (𝓞 F))) = ⊤ :=
    NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top (𝓞 F) F _ fun C =>
      ⟨rep C, hrep C, fun v hv => by
        have hJ0 : (rep C : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero _
        exact hle_norm v _ hJ0 (Ideal.le_of_dvd hv)
          (le_trans (Finset.le_sup (f := fun C => Ideal.absNorm (rep C : Ideal (𝓞 F)))
            (Finset.mem_univ C)) (le_max_left _ _))⟩
  obtain ⟨c1, c2, -, -⟩ := P.clauses hℓp hζ hcx hc S hSℓ hcl
  rw [hSet] at c2
  have hμ : (primitiveRoots ℓ F).Nonempty := ⟨ζ, (mem_primitiveRoots hℓp.pos).mpr hζ⟩
  refine ⟨P.HS S, c1, c2, ?_, ?_, ?_⟩
  · intro x y hx
    exact P.HS_locPow_left S x y (mem_locPow.mpr fun v hv => hx v ((hS v).mp hv))
  · intro u hu hrad
    have hloc := P.HS_nondeg hℓp.pos S u hrad
    obtain ⟨c, hc⟩ := NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom F hℓp hμ S ∅ hSℓ hcl
      (fun x _ => ⟨1, fun v _ => by simp, fun v hv => absurd hv (Finset.notMem_empty v)⟩)
      ((u : Fˣ) : F) (fun v hv _ => hu v (by rw [← hSet]; exact hv))
      (fun v hv => by
        obtain ⟨d, hd⟩ := mem_locPow.mp hloc v hv
        refine ⟨(d : v.adicCompletion F), ?_⟩
        have := congrArg Units.val hd
        simpa [emb] using this.symm)
      (fun w hw => absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr (hcx w)))
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hℓp.ne_zero] at hc
      exact (u : Fˣ).ne_zero hc
    refine ⟨Units.mk0 c hc0, ?_, Units.ext (by simp [hc])⟩
    intro v hv
    have h1 : v.valuation F c ^ ℓ = 1 := by
      rw [← map_pow, ← hc]; exact hu v hv
    exact (pow_eq_one_iff_left hℓp.ne_zero).mp h1
  · intro Pi Pi' hPi hPi' hE hE' hne p p' x x' hx hx' hp hp' hχ
    have hnot : ∀ Q : Ideal (𝓞 F), Q.IsPrime → IsExterior 𝔪 Q → ¬ 𝔪 ≤ Q := by
      intro Q hQ hEQ h
      apply hQ.ne_top
      rw [← hEQ.2, sup_eq_left.mpr h]
    have h6 : ∀ Q : Ideal (𝓞 F), Q.IsPrime → IsExterior 𝔪 Q → (6 : 𝓞 F) ∉ Q := by
      intro Q hQ hEQ h
      have := C0R.sup_span_six_eq_top (N₀ := max Nc N6) (le_max_right _ _) hsmall hQ hEQ
      apply hQ.ne_top
      rw [← this, sup_eq_left.mpr]
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact h
    let v : HeightOneSpectrum (𝓞 F) := ⟨Pi, hPi, hE.1⟩
    let v' : HeightOneSpectrum (𝓞 F) := ⟨Pi', hPi', hE'.1⟩
    have hvv : v ≠ v' := fun h => hne (congrArg HeightOneSpectrum.asIdeal h)
    exact recip_conv P hℓ ι S hS hSℓ hz6 v v' hvv (hnot Pi hPi hE) (hnot Pi' hPi' hE')
      (h6 Pi hPi hE) (h6 Pi' hPi' hE') p p' x x' hx hx' hp hp' hχ

end L3B

end
end
end

section
section
/-! L3B: the level subgroup against local powers (universe 0).

* `exists_level`: for `k` large, `SLevel 𝔪 k` consists of local `ℓ`-th powers at every `v ∈ S_f`
  (`ℓ`-th powers are open, 11fcc23a).
* `mem_level_sup`: a local sixth power at every `v ∈ S_f` lies in `SLevel 𝔪 k · Fˣ⁶`
  (weak approximation, 1bfe4906).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace L3B

open C0Y

variable {F : Type} [Field F] [NumberField F]

theorem adicAbv_eq_of_sub_lt {v : HeightOneSpectrum (𝓞 F)} {a b : F}
    (h : NumberField.HeightOneSpectrum.adicAbv F v (a - b) <
      NumberField.HeightOneSpectrum.adicAbv F v b) :
    NumberField.HeightOneSpectrum.adicAbv F v a = NumberField.HeightOneSpectrum.adicAbv F v b := by
  set A := NumberField.HeightOneSpectrum.adicAbv F v
  have h1 : A a ≤ max (A (a - b)) (A b) := by
    have := NumberField.HeightOneSpectrum.adicAbv_add_le_max F v (a - b) b
    rwa [sub_add_cancel] at this
  have h2 : A b ≤ max (A (b - a)) (A a) := by
    have := NumberField.HeightOneSpectrum.adicAbv_add_le_max F v (b - a) a
    rwa [sub_add_cancel] at this
  rw [AbsoluteValue.map_sub] at h2
  refine le_antisymm (h1.trans (max_le h.le le_rfl)) ?_
  rcases le_max_iff.1 h2 with h' | h'
  · exact absurd (h'.trans_lt h) (lt_irrefl _)
  · exact h'

theorem norm_coe (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖(algebraMap F (v.adicCompletion F) x)‖ = NumberField.HeightOneSpectrum.adicAbv F v x :=
  NumberField.FinitePlace.norm_embedding v x

theorem exists_level_at (v : HeightOneSpectrum (𝓞 F)) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ x : Fˣ,
      NumberField.HeightOneSpectrum.adicAbv F v ((x : F) - 1) ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1)) →
      emb F v x ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
  set R := (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range
  have hR : IsOpen (R : Set (v.adicCompletion F)ˣ) :=
    NumberField.isOpen_range_powMonoidHom_units_adicCompletion v hℓ
  have hV : IsOpen (Units.val '' (R : Set (v.adicCompletion F)ˣ)) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ hR
  have h1 : (1 : v.adicCompletion F) ∈ Units.val '' (R : Set (v.adicCompletion F)ˣ) :=
    ⟨1, R.one_mem, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 1 h1
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  refine ⟨m, fun k hk x hx => ?_⟩
  have hδ : (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1)) < ε := by
    have e1 : (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1)) =
        ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ (k + 1) := by
      rw [show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        inv_pow]
    rw [e1]
    refine lt_of_le_of_lt ?_ hm
    exact pow_le_pow_of_le_one (inv_nonneg.2 hq0.le) (inv_le_one_of_one_le₀ hq.le) (by omega)
  have hmem : (algebraMap F (v.adicCompletion F) (x : F)) ∈ Metric.ball (1 : v.adicCompletion F) ε := by
    rw [Metric.mem_ball, dist_eq_norm, ← map_one (algebraMap F (v.adicCompletion F)), ← map_sub,
      norm_coe]
    exact lt_of_le_of_lt hx hδ
  obtain ⟨r, hr, hrx⟩ := hball hmem
  have : emb F v x = r := Units.ext hrx.symm
  rw [this]; exact hr

theorem placesOf_finite {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  have hfin := Ideal.finite_factors (I := 𝔪) h𝔪
  refine hfin.subset fun v hv => ?_
  simp only [Set.mem_setOf_eq]
  exact Ideal.dvd_iff_le.2 hv

theorem exists_level (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ x ∈ SLevel 𝔪 k, ∀ v ∈ placesOf 𝔪,
      emb F v x ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
  classical
  have hfin := placesOf_finite h𝔪
  choose kf hkf using fun v : HeightOneSpectrum (𝓞 F) => exists_level_at v hℓ
  refine ⟨hfin.toFinset.sup kf, fun k hk x hx v hv => ?_⟩
  have hle : kf v ≤ k :=
    le_trans (Finset.le_sup (f := kf) ((Set.Finite.mem_toFinset hfin).2 hv)) hk
  exact hkf v k hle x (hx v hv)

theorem mem_level_sup (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (k : ℕ) (x : Fˣ)
    (hx : ∀ v ∈ placesOf 𝔪,
      emb F v x ∈ (powMonoidHom 6 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range) :
    x ∈ SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range := by
  classical
  have hfin := placesOf_finite h𝔪
  set S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ v ∈ placesOf 𝔪 := fun v => Set.Finite.mem_toFinset hfin
  by_cases hSe : S = ∅
  · refine Subgroup.mem_sup_left fun v hv => ?_
    exact absurd ((hS v).2 hv) (by rw [hSe]; exact Finset.notMem_empty v)
  obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
  have hc : ∀ w : S, ∃ c : (w.1.adicCompletion F)ˣ, c ^ 6 = emb F w.1 x := fun w => by
    obtain ⟨c, hc⟩ := hx w.1 ((hS w.1).1 w.2)
    exact ⟨c, hc⟩
  choose c hc using hc
  let δ : HeightOneSpectrum (𝓞 F) → ℝ := fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ (-((k : ℤ) + 1))
  have hδpos : ∀ w, 0 < δ w := fun w => by
    have hq : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm w
      exact_mod_cast (show 0 < Ideal.absNorm w.asIdeal by omega)
    exact zpow_pos hq _
  have hδ1 : ∀ w, δ w < 1 := fun w => absNorm_zpow_neg_lt_one w k
  let V : (w : S) → Set (w.1.adicCompletion F) := fun w =>
    {z | ‖z ^ 6 - algebraMap F (w.1.adicCompletion F) (x : F)‖ <
      ‖algebraMap F (w.1.adicCompletion F) (x : F)‖ * δ w.1}
  have hVo : ∀ w, IsOpen (V w) := fun w =>
    isOpen_lt (by fun_prop) continuous_const
  have hxpos : ∀ w : HeightOneSpectrum (𝓞 F), 0 < ‖algebraMap F (w.adicCompletion F) (x : F)‖ :=
    fun w => norm_pos_iff.2 ((map_ne_zero _).2 x.ne_zero)
  have hcV : ∀ w : S, ((c w : (w.1.adicCompletion F)ˣ) : w.1.adicCompletion F) ∈ V w := by
    intro w
    show ‖((c w : (w.1.adicCompletion F)ˣ) : w.1.adicCompletion F) ^ 6 -
      algebraMap F (w.1.adicCompletion F) (x : F)‖ < _
    have : ((c w : (w.1.adicCompletion F)ˣ) : w.1.adicCompletion F) ^ 6 =
        algebraMap F (w.1.adicCompletion F) (x : F) := by
      have := congrArg Units.val (hc w)
      simpa [emb] using this
    rw [this, sub_self, norm_zero]
    exact mul_pos (hxpos w.1) (hδpos w.1)
  have hO : IsOpen (Set.pi Set.univ V) := isOpen_set_pi Set.finite_univ (fun w _ => hVo w)
  obtain ⟨y, hy⟩ := (NumberField.denseRange_algebraMap_pi_adicCompletion (K := F) S).exists_mem_open
    hO ⟨fun w => ((c w : (w.1.adicCompletion F)ˣ) : w.1.adicCompletion F), fun w _ => hcV w⟩
  have hyv : ∀ w ∈ placesOf 𝔪,
      NumberField.HeightOneSpectrum.adicAbv F w (y ^ 6 - (x : F)) <
        NumberField.HeightOneSpectrum.adicAbv F w (x : F) * δ w := by
    intro w hw
    have := hy ⟨w, (hS w).2 hw⟩ (Set.mem_univ _)
    simp only [V, Set.mem_setOf_eq] at this
    rw [← map_pow, ← map_sub, norm_coe, norm_coe] at this
    exact this
  have hy0 : y ≠ 0 := by
    rintro rfl
    have := hyv v₀ ((hS v₀).1 hv₀)
    rw [zero_pow (by norm_num), zero_sub, AbsoluteValue.map_neg] at this
    have hpos : 0 < NumberField.HeightOneSpectrum.adicAbv F v₀ (x : F) :=
      (NumberField.HeightOneSpectrum.adicAbv F v₀).pos x.ne_zero
    nlinarith [hδ1 v₀]
  set Y : Fˣ := Units.mk0 y hy0
  have hdecomp : x = (x * (Y ^ 6)⁻¹) * Y ^ 6 := by group
  rw [hdecomp]
  refine Subgroup.mul_mem_sup (fun w hw => ?_) ⟨Y, rfl⟩
  have h1 := hyv w hw
  have hpos : 0 < NumberField.HeightOneSpectrum.adicAbv F w (x : F) :=
    (NumberField.HeightOneSpectrum.adicAbv F w).pos x.ne_zero
  have hlt : NumberField.HeightOneSpectrum.adicAbv F w (y ^ 6 - (x : F)) <
      NumberField.HeightOneSpectrum.adicAbv F w (x : F) := by
    nlinarith [hδ1 w]
  have heq := adicAbv_eq_of_sub_lt hlt
  have hy6 : y ^ 6 ≠ 0 := pow_ne_zero _ hy0
  have hval : (((x * (Y ^ 6)⁻¹ : Fˣ)) : F) - 1 = -(y ^ 6 - (x : F)) / y ^ 6 := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Y,
      Units.val_mk0]
    field_simp
    ring
  rw [hval, map_div₀, AbsoluteValue.map_neg, heq, div_le_iff₀ hpos]
  linarith

/-- Local squares and cubes are local sixth powers. -/
theorem mem_range_six {G : Type*} [CommGroup G] {x : G}
    (h2 : x ∈ (powMonoidHom 2 : G →* G).range) (h3 : x ∈ (powMonoidHom 3 : G →* G).range) :
    x ∈ (powMonoidHom 6 : G →* G).range := by
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := h3
  simp only [powMonoidHom_apply] at ha hb
  refine ⟨a * b⁻¹, ?_⟩
  simp only [powMonoidHom_apply]
  calc (a * b⁻¹) ^ 6 = (a ^ 2) ^ 3 * ((b ^ 3) ^ 2)⁻¹ := by
        rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul]
    _ = x ^ 3 * (x ^ 2)⁻¹ := by rw [ha, hb]
    _ = x := by group

end L3B

end
end
end

section
section
/-! L3B: SB in subgroup form, for `F : Type`.

`K = SLevel 𝔪 k · Fˣ⁶` has finite index, and `B = ⟨g 𝔄⟩ · K` satisfies
`ε · g 𝔄 ∈ B ↔ ε ∈ U_S⁶`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain ArtinPrimitiveRoots
open scoped nonZeroDivisors

noncomputable section

namespace L3B

open C0Y

variable {G M : Type*} [CommGroup G] [CommGroup M]

/-- The subgroup of elements orthogonal (on the left) to a set. -/
def orth (H : G →* G →* M) (T : Set G) : Subgroup G := ⨅ t : T, (H.flip t.1).ker

theorem mem_orth {H : G →* G →* M} {T : Set G} {a : G} : a ∈ orth H T ↔ ∀ t ∈ T, H a t = 1 := by
  simp [orth, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem isotropic_closure (H : G →* G →* M) (T : Set G) (hT : ∀ s ∈ T, ∀ t ∈ T, H s t = 1) :
    ∀ a ∈ Subgroup.closure T, ∀ b ∈ Subgroup.closure T, H a b = 1 := by
  have h1 : Subgroup.closure T ≤ orth H T :=
    (Subgroup.closure_le _).2 fun s hs => mem_orth.2 (hT s hs)
  intro a ha b hb
  have h2 : Subgroup.closure T ≤ (H a).ker :=
    (Subgroup.closure_le _).2 fun t ht => (MonoidHom.mem_ker).2 (mem_orth.1 (h1 ha) t ht)
  exact h2 hb

variable {F : Type} [Field F] [NumberField F]

theorem gen_ne_zero {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) : ((g.gen 𝔟 : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have hm0 : g.gen 𝔟 = 0 := Subtype.ext h0
  have hm := g.span_gen 𝔟 h𝔟
  rw [hm0, Ideal.span_singleton_eq_bot.2 rfl] at hm
  apply h𝔟.1
  rw [eq_bot_iff]
  intro b hb
  have : algebraMap (𝓞 F) (SInt 𝔪) b ∈ (⊥ : Ideal (SInt 𝔪)) := hm ▸ Ideal.mem_map_of_mem _ hb
  rw [Ideal.mem_bot] at this
  have h2 : algebraMap (𝓞 F) F b = 0 := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) this
    simpa using this
  rw [Ideal.mem_bot]
  exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h2

/-- The generator as a unit of `F`. -/
def genU {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) : Fˣ := Units.mk0 _ (gen_ne_zero g h𝔟)

@[simp] theorem coe_genU {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) : ((genU g h𝔟 : Fˣ) : F) = (g.gen 𝔟 : F) := rfl

/-- Prime generators and sixth powers. -/
def primeGens {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) : Set Fˣ :=
  {z | ∃ P : Ideal (𝓞 F), P.IsPrime ∧ IsExterior 𝔪 P ∧ (z : F) = (g.gen P : F)} ∪
    Set.range (fun c : Fˣ => c ^ 6)

theorem mem_closure_primeGens {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (𝔄 : Ideal (𝓞 F)) : IsExterior 𝔪 𝔄 → ∀ z : Fˣ, (z : F) = (g.gen 𝔄 : F) →
      z ∈ Subgroup.closure (primeGens g) := by
  induction 𝔄 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ x hx =>
    intro hE z hz
    rw [Ideal.isUnit_iff] at hx
    subst hx
    obtain ⟨ε, hε⟩ := g.gen_mul ⊤ ⊤ hE hE
    rw [Ideal.top_mul] at hε
    have h0 := gen_ne_zero g hE
    have h1 : (((ε : Fˣ) : F)) ^ 6 * (g.gen ⊤ : F) = 1 := by
      have : (g.gen ⊤ : F) * ((((ε : Fˣ) : F)) ^ 6 * (g.gen ⊤ : F) - 1) = 0 := by
        linear_combination -hε
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h h0
      · exact sub_eq_zero.1 h
    refine Subgroup.subset_closure (Or.inr ⟨(ε : Fˣ)⁻¹, Units.ext ?_⟩)
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow, hz]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  | h₃ a p ha hp ih =>
    intro hE z hz
    have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hp.ne_zero).1 hp
    have hEp : IsExterior 𝔪 p := ⟨hp.ne_zero, by
      rw [eq_top_iff, ← hE.2]; exact sup_le_sup_right Ideal.mul_le_left _⟩
    have hEa : IsExterior 𝔪 a := ⟨ha, by
      rw [eq_top_iff, ← hE.2]; exact sup_le_sup_right Ideal.mul_le_right _⟩
    obtain ⟨ε, hε⟩ := g.gen_mul p a hEp hEa
    have hzz : z = (ε : Fˣ) ^ 6 * genU g hEp * genU g hEa := by
      ext; rw [hz, hε]; simp
    rw [hzz]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (ih hEa _ rfl)
    · exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨p, hpP, hEp, rfl⟩)

/-- Every nonzero ideal becomes an exterior ideal in `R`. -/
theorem exists_exterior_map_eq (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (I : Ideal (𝓞 F)) :
    I ≠ ⊥ → ∃ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 ∧
      I.map (algebraMap (𝓞 F) (SInt 𝔪)) = 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff] at hx
    exact ⟨⊤, ⟨top_ne_bot, top_sup_eq _⟩, by rw [hx]⟩
  | h₃ a p ha hp ih =>
    intro _
    obtain ⟨𝔄, hE, hmap⟩ := ih ha
    have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hp.ne_zero).1 hp
    by_cases hcop : p ⊔ 𝔪 = ⊤
    · refine ⟨p * 𝔄, ⟨mul_ne_zero hp.ne_zero hE.1, ?_⟩, ?_⟩
      · rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rw [sup_comm]; exact hcop), sup_comm,
          hE.2]
      · rw [Ideal.map_mul, Ideal.map_mul, hmap]
    · have hmax : p.IsMaximal := hpP.isMaximal hp.ne_zero
      have h𝔪p : 𝔪 ≤ p := by
        have := hmax.eq_of_le hcop le_sup_left
        rw [this]; exact le_sup_right
      have htop : p.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
        apply C0R.map_eq_top_of_primes 𝔪 h𝔪 p
        intro Q hQ hpQ
        have : Q = p := (hmax.eq_of_le hQ.ne_top hpQ).symm
        rw [this]; exact h𝔪p
      exact ⟨𝔄, hE, by rw [Ideal.map_mul, htop, Ideal.top_mul, hmap]⟩

/-- `Fˣ` is generated by `U_S` and the generators. -/
theorem mem_closure_units_gens {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥)
    (g : AllowedGen ι 𝔪) (y : Fˣ) :
    y ∈ Subgroup.closure (((placesOf 𝔪).unit F : Set Fˣ) ∪
      {z | ∃ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 ∧ (z : F) = (g.gen 𝔄 : F)}) := by
  set C := Subgroup.closure (((placesOf 𝔪).unit F : Set Fˣ) ∪
      {z : Fˣ | ∃ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 ∧ (z : F) = (g.gen 𝔄 : F)})
  have hint : ∀ a : 𝓞 F, (ha : algebraMap (𝓞 F) F a ≠ 0) → Units.mk0 _ ha ∈ C := by
    intro a ha
    have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
    have hI : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨𝔄, hE, hmap⟩ := exists_exterior_map_eq 𝔪 h𝔪 _ hI
    rw [Ideal.map_span, Set.image_singleton, ← g.span_gen 𝔄 hE,
      Ideal.span_singleton_eq_span_singleton] at hmap
    obtain ⟨u, hu⟩ := hmap
    let uS : SUnit 𝔪 := (Set.unitEquivUnitsInteger (placesOf 𝔪) F).symm u
    have huS : (((uS : Fˣ)) : F) = ((u : SInt 𝔪) : F) := rfl
    have hdec : Units.mk0 _ ha = genU g hE * ((uS : Fˣ))⁻¹ := by
      ext
      simp only [Units.val_mk0, Units.val_mul, coe_genU, Units.val_inv_eq_inv_val, huS]
      have := congrArg (fun z : SInt 𝔪 => (z : F)) hu
      simp only [MulMemClass.coe_mul] at this
      rw [← this]
      have hu0 : ((u : SInt 𝔪) : F) ≠ 0 := by
        intro h0
        have : (u : SInt 𝔪) = 0 := Subtype.ext h0
        exact u.ne_zero this
      field_simp
      rfl
    rw [hdec]
    refine C.mul_mem (Subgroup.subset_closure (Or.inr ⟨𝔄, hE, rfl⟩)) (C.inv_mem ?_)
    exact Subgroup.subset_closure (Or.inl uS.2)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (y : F)
  have hb0 : algebraMap (𝓞 F) F b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hb)
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 := by
    intro h; rw [h, zero_div] at hab; exact y.ne_zero hab.symm
  have hy : y = Units.mk0 _ ha0 * (Units.mk0 _ hb0)⁻¹ := by
    ext; simp [← hab, div_eq_mul_inv]
  rw [hy]
  exact C.mul_mem (hint a ha0) (C.inv_mem (hint b hb0))

theorem pow_six_eq_one_of_mem {ℓ : ℕ} (hℓ : ℓ = 2 ∨ ℓ = 3) (z : rootsOfUnity ℓ F) : z ^ 6 = 1 := by
  have h := rootsOfUnity_pow_eq_one (ℓ := ℓ) z
  rcases hℓ with rfl | rfl
  · calc z ^ 6 = (z ^ 2) ^ 3 := by rw [← pow_mul]
      _ = 1 := by rw [h, one_pow]
  · calc z ^ 6 = (z ^ 3) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h, one_pow]

/-- **SB in subgroup form** (universe 0). -/
theorem core (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
        (SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range).FiniteIndex ∧
        ∃ B : Subgroup Fˣ, SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range ≤ B ∧
          ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪, ∀ z : Fˣ,
            (z : F) = ((ε : Fˣ) : F) * (g.gen 𝔄 : F) →
            (z ∈ B ↔ ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range) := by
  classical
  obtain ⟨N₂, hN₂⟩ := pair n hn0 hn F ι 2 (Or.inl rfl)
  obtain ⟨N₃, hN₃⟩ := pair n hn0 hn F ι 3 (Or.inr rfl)
  set N6 := Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})
  refine ⟨max (max N₂ N₃) N6, fun 𝔪 h𝔪 hsmall g => ?_⟩
  obtain ⟨H₂, a2, b2, c2, d2, e2⟩ := hN₂ 𝔪 h𝔪 (C0R.smallPrimesDvd_mono hsmall (by omega))
  obtain ⟨H₃, a3, b3, c3, d3, e3⟩ := hN₃ 𝔪 h𝔪 (C0R.smallPrimesDvd_mono hsmall (by omega))
  obtain ⟨k₂, hk₂⟩ := exists_level 𝔪 h𝔪 (ℓ := 2) (by norm_num)
  obtain ⟨k₃, hk₃⟩ := exists_level 𝔪 h𝔪 (ℓ := 3) (by norm_num)
  refine ⟨max k₂ k₃, fun k hk => ?_⟩
  set K := SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range
  -- the finite set `S`
  have hfin := placesOf_finite h𝔪
  set S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ v ∈ placesOf 𝔪 := fun v => Set.Finite.mem_toFinset hfin
  have hSℓ : ∀ ℓ : ℕ, ℓ ∣ 6 → ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v ∈ S := by
    intro ℓ hℓ v hv
    rw [hS]
    by_contra hnot
    have hE : IsExterior 𝔪 v.asIdeal := ⟨v.ne_bot, by
      by_contra hne
      have hmax := v.isPrime.isMaximal v.ne_bot
      have := hmax.eq_of_le hne le_sup_left
      exact hnot (by show 𝔪 ≤ v.asIdeal; rw [this]; exact le_sup_right)⟩
    have h6 := C0R.sup_span_six_eq_top (N₀ := max (max N₂ N₃) N6) (le_max_right _ _) hsmall
      v.isPrime hE
    apply v.isPrime.ne_top
    rw [← h6, sup_eq_left.mpr]
    rw [Ideal.span_le, Set.singleton_subset_iff]
    obtain ⟨m, hm⟩ := hℓ
    have : (6 : 𝓞 F) = (ℓ : 𝓞 F) * (m : 𝓞 F) := by
      rw [← Nat.cast_mul, ← hm]; norm_num
    rw [SetLike.mem_coe, this]; exact v.asIdeal.mul_mem_right _ hv
  -- finite index
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζn := IsCyclotomicExtension.zeta_spec n ℚ F
  have hprim : ∀ d : ℕ, d ∣ n → ∃ z : F, IsPrimitiveRoot z d := by
    intro d hd
    obtain ⟨m, hm⟩ := hd
    exact ⟨_, hζn.pow hn0 (by rw [hm, mul_comm])⟩
  have hcx : ∀ w : InfinitePlace F, w.IsComplex :=
    (IsCyclotomicExtension.Rat.isTotallyComplex (n := n) F
      (lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd hn0 hn))).isComplex
  have hfi : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 6 → (locPow (F := F) ℓ S).FiniteIndex := by
    intro ℓ hℓ hℓ6
    obtain ⟨ζ, hζ⟩ := hprim ℓ (dvd_trans hℓ6 (dvd_trans (by norm_num) hn))
    have hidx := index_locPow hℓ hζ hcx S (hSℓ ℓ hℓ6)
    exact ⟨by rw [hidx]; exact pow_ne_zero _ hℓ.ne_zero⟩
  haveI := hfi 2 Nat.prime_two (by norm_num)
  haveI := hfi 3 Nat.prime_three (by norm_num)
  have hle : locPow (F := F) 2 S ⊓ locPow 3 S ≤ K := by
    intro x hx
    rw [Subgroup.mem_inf, mem_locPow, mem_locPow] at hx
    exact mem_level_sup 𝔪 h𝔪 k x fun v hv =>
      mem_range_six (hx.1 v ((hS v).2 hv)) (hx.2 v ((hS v).2 hv))
  refine ⟨Subgroup.finiteIndex_of_le hle, ?_⟩
  -- the subgroup `B`
  set Gs : Set Fˣ := {z | ∃ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 ∧ (z : F) = (g.gen 𝔄 : F)}
  set B := Subgroup.closure Gs ⊔ K
  refine ⟨B, le_sup_right, fun 𝔄 hE ε z hz => ?_⟩
  have hw : genU g hE ∈ B := Subgroup.mem_sup_left (Subgroup.subset_closure ⟨𝔄, hE, rfl⟩)
  have hzε : z = (ε : Fˣ) * genU g hE := by ext; rw [hz]; rfl
  constructor
  · intro hzB
    have hεB : (ε : Fˣ) ∈ B := by
      have : (ε : Fˣ) = z * (genU g hE)⁻¹ := by rw [hzε]; group
      rw [this]; exact B.mul_mem hzB (B.inv_mem hw)
    -- for each `ℓ`, `ε` is in the radical, hence an `ℓ`-th power of an `S`-unit
    have key : ∀ (ℓ : ℕ) (hℓ : ℓ = 2 ∨ ℓ = 3) (H : Fˣ →* Fˣ →* rootsOfUnity ℓ F),
        (∀ x, H x x = 1) →
        (∀ u ∈ (placesOf 𝔪).unit F, ∀ u' ∈ (placesOf 𝔪).unit F, H u u' = 1) →
        (∀ x y : Fˣ, (∀ v ∈ placesOf 𝔪, emb F v x ∈
            (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range) →
          H x y = 1) →
        (∀ u ∈ (placesOf 𝔪).unit F, (∀ y, H u y = 1) → ∃ c ∈ (placesOf 𝔪).unit F, c ^ ℓ = u) →
        (∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P → IsExterior 𝔪 P' →
          P ≠ P' →
          ∀ (p p' : SInt 𝔪) (x x' : Fˣ), (x : F) = p → (x' : F) = p' →
            Ideal.span {p} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
            Ideal.span {p'} = P'.map (algebraMap (𝓞 F) (SInt 𝔪)) →
            sexticResidueSymbol ι 𝔪 P p' = sexticResidueSymbol ι 𝔪 P' p → H x x' = 1) →
        (∀ x ∈ SLevel 𝔪 k, ∀ v ∈ placesOf 𝔪, emb F v x ∈
            (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range) →
        ε ∈ (powMonoidHom ℓ : SUnit 𝔪 →* SUnit 𝔪).range := by
      intro ℓ hℓ H ha hb hc hd he hlev
      have hpow6 : ∀ c y : Fˣ, H (c ^ 6) y = 1 := fun c y => by
        rw [map_pow, MonoidHom.pow_apply]; exact pow_six_eq_one_of_mem hℓ _
      have hpow6' : ∀ c y : Fˣ, H y (c ^ 6) = 1 := fun c y => by
        rw [map_pow]; exact pow_six_eq_one_of_mem hℓ _
      -- the prime generators are isotropic
      have hiso : ∀ s ∈ primeGens g, ∀ t ∈ primeGens g, H s t = 1 := by
        rintro s (⟨P, hP, hEP, hs⟩ | ⟨c, rfl⟩) t (⟨P', hP', hEP', ht⟩ | ⟨c', rfl⟩)
        · by_cases hPP : P = P'
          · subst hPP
            have : s = t := Units.ext (by rw [hs, ht])
            rw [this]; exact ha t
          · exact he P P' hP hP' hEP hEP' hPP _ _ s t hs ht (g.span_gen P hEP)
              (g.span_gen P' hEP') (g.reciprocity P P' hP hP' hEP hEP' hPP)
        · exact hpow6' c' s
        · exact hpow6 c t
        · exact hpow6 c _
      have hGs : Gs ⊆ Subgroup.closure (primeGens g) := by
        rintro z ⟨𝔅, hE𝔅, hz𝔅⟩
        exact mem_closure_primeGens g 𝔅 hE𝔅 z hz𝔅
      -- `B` is orthogonal to the closure of the prime generators
      have hBo : B ≤ orth H (Subgroup.closure (primeGens g)) := by
        refine sup_le ?_ (sup_le ?_ ?_)
        · refine (Subgroup.closure_le _).2 fun s hs => mem_orth.2 fun t ht => ?_
          exact isotropic_closure H _ hiso s (hGs hs) t ht
        · intro x hx
          exact mem_orth.2 fun t _ => hc x t (hlev x hx)
        · rintro x ⟨c, rfl⟩
          exact mem_orth.2 fun t _ => hpow6 c t
      have hεo := mem_orth.1 (hBo hεB)
      have hall : ∀ y, H ε y = 1 := by
        intro y
        have hC : Subgroup.closure (((placesOf 𝔪).unit F : Set Fˣ) ∪ Gs) ≤ (H ε).ker := by
          refine (Subgroup.closure_le _).2 ?_
          rintro t (ht | ht)
          · exact (MonoidHom.mem_ker).2 (hb _ ε.2 t ht)
          · exact (MonoidHom.mem_ker).2 (hεo t (hGs ht))
        exact (MonoidHom.mem_ker).1 (hC (mem_closure_units_gens h𝔪 g y))
      obtain ⟨c, hcU, hcε⟩ := hd _ ε.2 hall
      exact ⟨⟨c, hcU⟩, Subtype.ext hcε⟩
    have h2 := key 2 (Or.inl rfl) H₂ a2 b2 c2 d2 e2 (hk₂ k (le_trans (le_max_left _ _) hk))
    have h3 := key 3 (Or.inr rfl) H₃ a3 b3 c3 d3 e3 (hk₃ k (le_trans (le_max_right _ _) hk))
    exact mem_range_six h2 h3
  · rintro ⟨c, rfl⟩
    rw [hzε]
    refine B.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_right ⟨(c : Fˣ), ?_⟩)) hw
    simp

end L3B

end
end
end

section
section
/-! L3B: transport of valuations, `SLevel`, `S`-units and `AllowedGen` along `e : F ≃+* F'`. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace L3B

open C0R

section

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

theorem withZero_eq_of_le_exp_iff {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) :
    a = b := by
  rw [← WithZero.exp_log ha, ← WithZero.exp_log hb] at h ⊢
  rw [← WithZero.exp_log ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha1
  rw [← WithZero.exp_log hb, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb1
  congr 1
  have h1 := h (-WithZero.log a).toNat
  have h2 := h (-WithZero.log b).toNat
  simp only [WithZero.exp_le_exp] at h1 h2
  omega

/-- The prime of `𝓞 F'` corresponding to `v`. -/
def vmap (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 F') where
  asIdeal := v.asIdeal.map (RingOfIntegers.mapRingEquiv e)
  isPrime := Ideal.map_isPrime_of_equiv _
  ne_bot := fun h => v.ne_bot
    ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).1 h)

theorem intValuation_vmap (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    (vmap e v).intValuation (RingOfIntegers.mapRingEquiv e r) = v.intValuation r := by
  by_cases hr : r = 0
  · subst hr; simp
  have hr' : RingOfIntegers.mapRingEquiv e r ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RingOfIntegers.mapRingEquiv e).injective]; exact hr
  refine withZero_eq_of_le_exp_iff ((vmap e v).intValuation_ne_zero _ hr')
    (v.intValuation_ne_zero _ hr) ((vmap e v).intValuation_le_one _) (v.intValuation_le_one _)
    fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  change _ ∈ (v.asIdeal.map (RingOfIntegers.mapRingEquiv e)) ^ n ↔ _
  rw [← Ideal.map_pow, mem_map_equiv, RingEquiv.symm_apply_apply]

theorem valuation_vmap (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    (vmap e v).valuation F' (e x) = v.valuation F x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have ha : e (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F') F' (RingOfIntegers.mapRingEquiv e a) := rfl
  have hb' : e (algebraMap (𝓞 F) F b) = algebraMap (𝓞 F') F' (RingOfIntegers.mapRingEquiv e b) :=
    rfl
  rw [map_div₀, ha, hb', map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_vmap, intValuation_vmap]

theorem absNorm_vmap (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm (vmap e v).asIdeal = Ideal.absNorm v.asIdeal := absNorm_map_equiv e v.asIdeal

theorem adicAbv_vmap (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    NumberField.HeightOneSpectrum.adicAbv F' (vmap e v) (e x) =
      NumberField.HeightOneSpectrum.adicAbv F v x := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, NumberField.HeightOneSpectrum.adicAbv_def,
    valuation_vmap]
  have key : ∀ (a b : NNReal) (ha : a ≠ 0) (hb : b ≠ 0), a = b → ∀ z : WithZero (Multiplicative ℤ),
      WithZeroMulInt.toNNReal ha z = WithZeroMulInt.toNNReal hb z := by
    rintro a b ha hb rfl z; rfl
  rw [key _ _ _ _ (by rw [absNorm_vmap]) (v.valuation F x)]

theorem vmap_symm_vmap (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F')) :
    vmap e (vmap e.symm v) = v := by
  ext1
  change (v.asIdeal.map (RingOfIntegers.mapRingEquiv e.symm)).map (RingOfIntegers.mapRingEquiv e) = _
  rw [mapRingEquiv_symm]
  have := map_equiv_symm_map (RingOfIntegers.mapRingEquiv e).symm v.asIdeal
  rwa [RingEquiv.symm_symm] at this

theorem mem_placesOf_vmap (e : F ≃+* F') {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} :
    vmap e v ∈ placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e)) ↔ v ∈ placesOf 𝔪 :=
  map_equiv_le_iff _

theorem map_symm_map (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) :
    (𝔪.map (RingOfIntegers.mapRingEquiv e)).map (RingOfIntegers.mapRingEquiv e.symm) = 𝔪 := by
  rw [mapRingEquiv_symm]; exact map_equiv_symm_map _ 𝔪

/-- The units map. -/
abbrev uMap (e : F ≃+* F') : Fˣ →* F'ˣ := Units.map (e : F →* F')

theorem mem_sLevel_map (e : F ≃+* F') {𝔪 : Ideal (𝓞 F)} {k : ℕ} {x : Fˣ} (hx : x ∈ SLevel 𝔪 k) :
    uMap e x ∈ SLevel (𝔪.map (RingOfIntegers.mapRingEquiv e)) k := by
  intro v' hv'
  rw [← vmap_symm_vmap e v'] at hv' ⊢
  have hv := (mem_placesOf_vmap e).1 hv'
  have h := hx _ hv
  have : (((uMap e x : F'ˣ)) : F') - 1 = e ((x : F) - 1) := by simp
  rw [this, adicAbv_vmap, absNorm_vmap]
  exact h

theorem mem_unit_map (e : F ≃+* F') {𝔪 : Ideal (𝓞 F)} {u : Fˣ} (hu : u ∈ (placesOf 𝔪).unit F) :
    uMap e u ∈ (placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e))).unit F' := by
  intro v' hv'
  rw [← vmap_symm_vmap e v'] at hv' ⊢
  have hv : vmap e.symm v' ∉ placesOf 𝔪 := fun h => hv' ((mem_placesOf_vmap e).2 h)
  have : (((uMap e u : F'ˣ)) : F') = e (u : F) := rfl
  rw [this, valuation_vmap]
  exact hu _ hv

theorem uMap_symm_uMap (e : F ≃+* F') (x : F'ˣ) : uMap e (uMap e.symm x) = x := by
  ext; simp

theorem uMap_uMap_symm (e : F ≃+* F') (x : Fˣ) : uMap e.symm (uMap e x) = x := by
  ext; simp

theorem mem_sLevel_map_iff (e : F ≃+* F') {𝔪 : Ideal (𝓞 F)} {k : ℕ} {x : Fˣ} :
    uMap e x ∈ SLevel (𝔪.map (RingOfIntegers.mapRingEquiv e)) k ↔ x ∈ SLevel 𝔪 k := by
  refine ⟨fun h => ?_, mem_sLevel_map e⟩
  have := mem_sLevel_map e.symm h
  rwa [map_symm_map, uMap_uMap_symm] at this

theorem mem_unit_map_iff (e : F ≃+* F') {𝔪 : Ideal (𝓞 F)} {u : Fˣ} :
    uMap e u ∈ (placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e))).unit F' ↔
      u ∈ (placesOf 𝔪).unit F := by
  refine ⟨fun h => ?_, mem_unit_map e⟩
  have := mem_unit_map e.symm h
  rwa [map_symm_map, uMap_uMap_symm] at this

theorem isExterior_symm_map (e : F ≃+* F') {𝔪 : Ideal (𝓞 F)} {I' : Ideal (𝓞 F')}
    (h : IsExterior (𝔪.map (RingOfIntegers.mapRingEquiv e)) I') :
    IsExterior 𝔪 (I'.map (RingOfIntegers.mapRingEquiv e.symm)) := by
  have := isExterior_map e.symm h
  rwa [map_symm_map] at this

theorem map_map_symm (e : F ≃+* F') (I' : Ideal (𝓞 F')) :
    (I'.map (RingOfIntegers.mapRingEquiv e.symm)).map (RingOfIntegers.mapRingEquiv e) = I' := by
  have := map_symm_map e.symm I'
  rwa [RingEquiv.symm_symm] at this

/-- `AllowedGen` transported along `e`. -/
def allowedGenMap (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤)
    (g : AllowedGen ι 𝔪) :
    AllowedGen (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e)) where
  gen I' := sIntEquiv e 𝔪 (g.gen (I'.map (RingOfIntegers.mapRingEquiv e.symm)))
  span_gen I' hI' := by
    have h := g.span_gen _ (isExterior_symm_map e hI')
    have h2 := congrArg (Ideal.map (sIntEquiv e 𝔪)) h
    rw [Ideal.map_span, Set.image_singleton, map_map_sIntEquiv, map_map_symm] at h2
    exact h2
  gen_mul I' J' hI' hJ' := by
    obtain ⟨ε, hε⟩ := g.gen_mul _ _ (isExterior_symm_map e hI') (isExterior_symm_map e hJ')
    refine ⟨⟨uMap e ε, mem_unit_map e ε.2⟩, ?_⟩
    change e (g.gen ((I' * J').map (RingOfIntegers.mapRingEquiv e.symm)) : F) =
      (e ((ε : Fˣ) : F)) ^ 6 * e (g.gen (I'.map (RingOfIntegers.mapRingEquiv e.symm)) : F) *
        e (g.gen (J'.map (RingOfIntegers.mapRingEquiv e.symm)) : F)
    rw [Ideal.map_mul, hε, map_mul, map_mul, map_pow]
  reciprocity P' Q' hP' hQ' hEP hEQ hne := by
    set eO := RingOfIntegers.mapRingEquiv e
    set P := P'.map (RingOfIntegers.mapRingEquiv e.symm)
    set Q := Q'.map (RingOfIntegers.mapRingEquiv e.symm)
    have hP : P.IsPrime := Ideal.map_isPrime_of_equiv _
    have hQ : Q.IsPrime := Ideal.map_isPrime_of_equiv _
    have hEP' := isExterior_symm_map e hEP
    have hEQ' := isExterior_symm_map e hEQ
    have hne' : P ≠ Q := by
      intro h
      apply hne
      rw [← map_map_symm e P', ← map_map_symm e Q']
      exact congrArg (Ideal.map eO) h
    have r := g.reciprocity P Q hP hQ hEP' hEQ' hne'
    have t1 := sexticResidueSymbol_transport e ι 𝔪 P (h6 P hP hEP') (g.gen Q)
    have t2 := sexticResidueSymbol_transport e ι 𝔪 Q (h6 Q hQ hEQ') (g.gen P)
    rw [map_map_symm] at t1 t2
    rw [t1, t2]
    exact r

@[simp] theorem allowedGenMap_gen (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (h6)
    (g : AllowedGen ι 𝔪) (I' : Ideal (𝓞 F')) :
    (((allowedGenMap e ι 𝔪 h6 g).gen I' : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) : F') =
      e (g.gen (I'.map (RingOfIntegers.mapRingEquiv e.symm)) : F) := rfl

end

end L3B

end
end
end

section
section
/-! L3B: SB `exists_cutoff_finite_sFinCls_and_exists_addSubgroup_mem_iff_mem_range_pow_six`
as `L3B_main`, for `F : Type*` (transport from `CyclotomicField n ℚ`). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace L3B

section

variable {F : Type*} [Field F] [NumberField F]

theorem gen_ne_zero' {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) : ((g.gen 𝔟 : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have hm0 : g.gen 𝔟 = 0 := Subtype.ext h0
  have hm := g.span_gen 𝔟 h𝔟
  rw [hm0, Ideal.span_singleton_eq_bot.2 rfl] at hm
  apply h𝔟.1
  rw [eq_bot_iff]
  intro b hb
  have : algebraMap (𝓞 F) (SInt 𝔪) b ∈ (⊥ : Ideal (SInt 𝔪)) := hm ▸ Ideal.mem_map_of_mem _ hb
  rw [Ideal.mem_bot] at this
  have h2 : algebraMap (𝓞 F) F b = 0 := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) this
    simpa using this
  rw [Ideal.mem_bot]
  exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h2

/-- `Fˣ → SFinCls 𝔪 k`. -/
def piS (𝔪 : Ideal (𝓞 F)) (k : ℕ) : Additive Fˣ →+ SFinCls 𝔪 k where
  toFun a := QuotientAddGroup.mk (SFin.mk 𝔪 k (Additive.toMul a))
  map_zero' := rfl
  map_add' a b := by
    rw [← QuotientAddGroup.mk_add]
    rfl

theorem piS_ofMul (𝔪 : Ideal (𝓞 F)) (k : ℕ) (x : Fˣ) :
    piS 𝔪 k (Additive.ofMul x) = QuotientAddGroup.mk (SFin.mk 𝔪 k x) := rfl

theorem sFin_mk_pow (𝔪 : Ideal (𝓞 F)) (k : ℕ) (x : Fˣ) (m : ℕ) :
    SFin.mk 𝔪 k (x ^ m) = m • SFin.mk 𝔪 k x := by
  induction m with
  | zero => simp only [pow_zero, zero_smul]; rfl
  | succ m ih =>
    rw [pow_succ, succ_nsmul, ← ih]
    rfl

theorem mem_of_piS_eq_zero (𝔪 : Ideal (𝓞 F)) (k : ℕ) (x : Fˣ)
    (h : piS 𝔪 k (Additive.ofMul x) = 0) :
    x ∈ SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range := by
  rw [piS_ofMul, QuotientAddGroup.eq_zero_iff] at h
  obtain ⟨s, hs⟩ := h
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul s)
  have hsy : s = SFin.mk 𝔪 k y := by rw [SFin.mk, hy]; rfl
  rw [nsmulAddMonoidHom_apply, hsy, ← sFin_mk_pow] at hs
  have hq : (QuotientGroup.mk (y ^ 6) : Fˣ ⧸ SLevel 𝔪 k) = QuotientGroup.mk x :=
    Additive.ofMul.injective hs
  rw [QuotientGroup.eq] at hq
  have : x = y ^ 6 * ((y ^ 6)⁻¹ * x) := by group
  rw [this, mul_comm]
  exact Subgroup.mul_mem_sup hq ⟨y, rfl⟩

theorem piS_eq_zero_of_mem (𝔪 : Ideal (𝓞 F)) (k : ℕ) (x : Fˣ)
    (hx : x ∈ SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range) :
    piS 𝔪 k (Additive.ofMul x) = 0 := by
  obtain ⟨a, ha, b, ⟨c, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
  rw [ofMul_mul, map_add]
  have h1 : piS 𝔪 k (Additive.ofMul a) = 0 := by
    rw [piS_ofMul, QuotientAddGroup.eq_zero_iff]
    have : SFin.mk 𝔪 k a = 0 := by
      show Additive.ofMul (QuotientGroup.mk a : Fˣ ⧸ SLevel 𝔪 k) = Additive.ofMul 1
      exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff a).2 ha)
    rw [this]; exact AddSubgroup.zero_mem _
  have h2 : piS 𝔪 k (Additive.ofMul ((powMonoidHom 6 : Fˣ →* Fˣ) c)) = 0 := by
    rw [piS_ofMul, QuotientAddGroup.eq_zero_iff, powMonoidHom_apply, sFin_mk_pow]
    exact ⟨SFin.mk 𝔪 k c, rfl⟩
  rw [h1, h2, add_zero]

/-- From the subgroup form to the stub's form. -/
theorem final {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (k : ℕ)
    (hfi : (SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range).FiniteIndex)
    (B : Subgroup Fˣ) (hKB : SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range ≤ B)
    (hB : ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪, ∀ z : Fˣ,
      (z : F) = ((ε : Fˣ) : F) * (g.gen 𝔄 : F) →
      (z ∈ B ↔ ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)) :
    Finite (SFinCls 𝔪 k) ∧
      ∃ B' : AddSubgroup (SFinCls 𝔪 k), ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪,
        ((QuotientAddGroup.mk (sEmb 𝔪 k ((ε : Fˣ) * (g.gen 𝔄 : F))).2.2 : SFinCls 𝔪 k) ∈ B' ↔
          ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range) := by
  classical
  set K := SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range
  haveI : Finite (Fˣ ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨?_, ?_⟩
  · let f : Fˣ ⧸ K → SFinCls 𝔪 k := fun q => Quotient.liftOn' q (fun x => piS 𝔪 k (Additive.ofMul x))
      (by
        intro x y hxy
        have hmem : x⁻¹ * y ∈ K := QuotientGroup.leftRel_apply.mp hxy
        have h0 := piS_eq_zero_of_mem 𝔪 k _ hmem
        have : y = x * (x⁻¹ * y) := by group
        show piS 𝔪 k (Additive.ofMul x) = piS 𝔪 k (Additive.ofMul y)
        rw [this, ofMul_mul, map_add, h0, add_zero])
    refine Finite.of_surjective f fun s => ?_
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective s
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul t)
    refine ⟨QuotientGroup.mk y, ?_⟩
    show piS 𝔪 k (Additive.ofMul y) = _
    rw [piS_ofMul]
    congr 1
  · refine ⟨(Subgroup.toAddSubgroup B).map (piS 𝔪 k), fun 𝔄 hE ε => ?_⟩
    have hne : ((ε : Fˣ) : F) * (g.gen 𝔄 : F) ≠ 0 :=
      mul_ne_zero (ε : Fˣ).ne_zero (gen_ne_zero' g hE)
    set z : Fˣ := Units.mk0 _ hne
    have hsE : (sEmb 𝔪 k (((ε : Fˣ) : F) * (g.gen 𝔄 : F))).2.2 = SFin.mk 𝔪 k z := by
      rw [sEmb, dif_neg hne]
    rw [hsE, ← piS_ofMul, ← hB 𝔄 hE ε z rfl]
    constructor
    · rintro ⟨a, ha, hpa⟩
      replace ha : Additive.toMul a ∈ B := ha
      have h0 : piS 𝔪 k (Additive.ofMul (z * (Additive.toMul a)⁻¹)) = 0 := by
        rw [ofMul_mul, map_add, ofMul_inv, map_neg, ← hpa]
        simp
      have hzK := hKB (mem_of_piS_eq_zero 𝔪 k _ h0)
      have : z = z * (Additive.toMul a)⁻¹ * Additive.toMul a := by group
      rw [this]
      exact B.mul_mem hzK ha
    · intro hz
      exact ⟨Additive.ofMul z, (Additive.mem_toAddSubgroup B _).2 hz, rfl⟩

end

end L3B

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem L3B_main (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      Finite (SFinCls 𝔪 k) ∧
      ∃ B : AddSubgroup (SFinCls 𝔪 k), ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪,
        ((QuotientAddGroup.mk (sEmb 𝔪 k ((ε : Fˣ) * (g.gen 𝔄 : F))).2.2 : SFinCls 𝔪 k) ∈ B ↔
          ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range) := by
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : NeZero ((n : ℚ)) := ⟨by exact_mod_cast hn0.ne'⟩
  haveI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let e : F ≃+* CyclotomicField n ℚ :=
    (IsCyclotomicExtension.algEquiv {n} ℚ F (CyclotomicField n ℚ)).toRingEquiv
  obtain ⟨N₁, hN₁⟩ := _root_.L3B.core n hn0 hn (CyclotomicField n ℚ)
    (ι.comp (e.symm : CyclotomicField n ℚ →+* F))
  refine ⟨max N₁ (Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})), fun 𝔪 h𝔪 hsmall g => ?_⟩
  set eO := RingOfIntegers.mapRingEquiv e
  set 𝔪₀ := 𝔪.map eO
  have h𝔪₀ : 𝔪₀ ≠ ⊥ := fun h0 =>
    h𝔪 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
  have hs₀ : SmallPrimesDvd N₁ 𝔪₀ :=
    C0R.smallPrimesDvd_map e (C0R.smallPrimesDvd_mono hsmall (le_max_left _ _))
  have h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤ :=
    fun P hP hE => C0R.sup_span_six_eq_top (le_max_right _ _) hsmall hP hE
  obtain ⟨k₀, hk₀⟩ := hN₁ 𝔪₀ h𝔪₀ hs₀ (_root_.L3B.allowedGenMap e ι 𝔪 h6 g)
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨hfi₀, B₀, hKB₀, hB₀⟩ := hk₀ k hk
  set φ := _root_.L3B.uMap e
  have hsurj : Function.Surjective φ := fun x => ⟨_root_.L3B.uMap e.symm x, L3B.uMap_symm_uMap e x⟩
  set K := SLevel 𝔪 k ⊔ (powMonoidHom 6 : Fˣ →* Fˣ).range
  set K₀ := SLevel 𝔪₀ k ⊔ (powMonoidHom 6 : (CyclotomicField n ℚ)ˣ →* (CyclotomicField n ℚ)ˣ).range
  have hcomap : K₀.comap φ ≤ K := by
    intro x hx
    obtain ⟨a, ha, b, ⟨c, rfl⟩, hab⟩ := Subgroup.mem_sup.1 (Subgroup.mem_comap.1 hx)
    have hx' : x = L3B.uMap e.symm a * (L3B.uMap e.symm c) ^ 6 := by
      have := congrArg (L3B.uMap e.symm) hab
      rw [L3B.uMap_uMap_symm] at this
      rw [← this, map_mul, powMonoidHom_apply, map_pow]
    rw [hx']
    refine Subgroup.mul_mem_sup ?_ ⟨_, rfl⟩
    rw [← L3B.mem_sLevel_map_iff e, L3B.uMap_symm_uMap]
    exact ha
  have hfi : K.FiniteIndex := by
    haveI : (K₀.comap φ).FiniteIndex :=
      ⟨by rw [Subgroup.index_comap_of_surjective _ hsurj]; exact hfi₀.1⟩
    exact Subgroup.finiteIndex_of_le hcomap
  have hKB : K ≤ B₀.comap φ := by
    refine sup_le (fun x hx => hKB₀ (Subgroup.mem_sup_left (L3B.mem_sLevel_map e hx))) ?_
    rintro x ⟨c, rfl⟩
    refine hKB₀ (Subgroup.mem_sup_right ⟨φ c, ?_⟩)
    simp [φ]
  refine L3B.final g k hfi (B₀.comap φ) hKB fun 𝔄 hE ε z hz => ?_
  have hE₀ : IsExterior 𝔪₀ (𝔄.map eO) := C0R.isExterior_map e hE
  let ε₀ : SUnit 𝔪₀ := ⟨φ ε, L3B.mem_unit_map e ε.2⟩
  have hz₀ : ((φ z : (CyclotomicField n ℚ)ˣ) : CyclotomicField n ℚ) = ((ε₀ : (CyclotomicField n ℚ)ˣ) :
      CyclotomicField n ℚ) * ((_root_.L3B.allowedGenMap e ι 𝔪 h6 g).gen (𝔄.map eO) :
        CyclotomicField n ℚ) := by
    rw [L3B.allowedGenMap_gen, L3B.map_symm_map]
    change e (z : F) = e ((ε : Fˣ) : F) * e (g.gen 𝔄 : F)
    rw [hz, map_mul]
  rw [Subgroup.mem_comap, hB₀ _ hE₀ ε₀ (φ z) hz₀]
  constructor
  · rintro ⟨c₀, hc₀⟩
    have hc : L3B.uMap e.symm (c₀ : (CyclotomicField n ℚ)ˣ) ∈ (placesOf 𝔪).unit F := by
      rw [← L3B.mem_unit_map_iff e, L3B.uMap_symm_uMap]; exact c₀.2
    refine ⟨⟨_, hc⟩, Subtype.ext ?_⟩
    have := congrArg (fun u : SUnit 𝔪₀ => L3B.uMap e.symm (u : (CyclotomicField n ℚ)ˣ)) hc₀
    simp only [powMonoidHom_apply, SubgroupClass.coe_pow, map_pow, ε₀, φ,
      L3B.uMap_uMap_symm] at this
    simpa using this
  · rintro ⟨c, rfl⟩
    refine ⟨⟨φ c, L3B.mem_unit_map e c.2⟩, Subtype.ext ?_⟩
    simp [ε₀, φ]

end ArtinPrimitiveRoots

end
end
end

section
section
/-! L3B: SB under the target's own name (does not import the target's stub). -/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem exists_cutoff_finite_sFinCls_and_exists_addSubgroup_mem_iff_mem_range_pow_six (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      Finite (SFinCls 𝔪 k) ∧
      ∃ B : AddSubgroup (SFinCls 𝔪 k), ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪,
        ((QuotientAddGroup.mk (sEmb 𝔪 k ((ε : Fˣ) * (g.gen 𝔄 : F))).2.2 : SFinCls 𝔪 k) ∈ B ↔
          ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)
  := L3B_main n hn0 hn F ι

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      Finite (SFinCls 𝔪 k) ∧
      ∃ B : AddSubgroup (SFinCls 𝔪 k), ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪,
        ((QuotientAddGroup.mk (sEmb 𝔪 k ((ε : Fˣ) * (g.gen 𝔄 : F))).2.2 : SFinCls 𝔪 k) ∈ B ↔
          ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)
  := by
  exact ArtinPrimitiveRoots.exists_cutoff_finite_sFinCls_and_exists_addSubgroup_mem_iff_mem_range_pow_six n hn0 hn F ι

end
