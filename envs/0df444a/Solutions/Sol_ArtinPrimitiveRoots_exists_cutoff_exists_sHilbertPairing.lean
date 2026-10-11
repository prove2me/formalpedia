-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_sHilbertPairing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T17:47:19.483331+00:00
-- url     : https://prove2.me/submissions/6285dddb-49f3-4ae2-8a06-4c1e9b4703e3

import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_M4aHerbrand_prod_idelicArtinMap_single_eq_one
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
import Theorems.Thm_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
import Mathlib
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

/-! ### `AllowedGen` transports -/

end C0R

end ArtinPrimitiveRoots
end

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

end C0R

end ArtinPrimitiveRoots
end

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

section
/-!
# C0: `exists_cutoff_nonempty_allowedGen` from C0-P, C0-L (proved) and C0-H (hypothesis)
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

/-- **C0-H** (the cut left open): for `F ⊇ μ₁₂` (universe 0) and `ℓ ∈ {2, 3}`, once `S` contains
the small primes there is an alternating pairing `H : Fˣ × Fˣ → μ_ℓ(F)` (classically the `S`-part
`H_S(x, y) = ∏_{v ∈ S} (x, y)_{ℓ, v}` of the `ℓ`-th Hilbert symbol) such that: the `S`-units are
isotropic; anything orthogonal to all `S`-units is an `S`-unit modulo the radical (`E^⊥ ⊆ E + rad`,
i.e. `U_S` is Lagrangian); the radical has finite index; and for prime generators `p, p'` of
distinct exterior primes with `H(p, p') = 1` the `ℓ`-th power residue symbols agree,
`χ_P(p')^{6/ℓ} = χ_{P'}(p)^{6/ℓ}` (Hilbert reciprocity + tame symbols). -/
def CutH : Prop :=
  ∀ (n : ℕ), 0 < n → 12 ∣ n → ∀ (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (ℓ : ℕ), (ℓ = 2 ∨ ℓ = 3) →
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ H : Fˣ →* Fˣ →* rootsOfUnity ℓ F,
        (∀ x, H x x = 1) ∧
        (∀ u ∈ (placesOf 𝔪).unit F, ∀ u' ∈ (placesOf 𝔪).unit F, H u u' = 1) ∧
        (∀ x, (∀ u ∈ (placesOf 𝔪).unit F, H x u = 1) →
          ∃ u ∈ (placesOf 𝔪).unit F, H (x * u⁻¹) = 1) ∧
        Finite (Fˣ ⧸ H.ker) ∧
        ∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P → IsExterior 𝔪 P' →
          P ≠ P' →
          ∀ (p p' : SInt 𝔪) (x x' : Fˣ), (x : F) = p → (x' : F) = p' →
            Ideal.span {p} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
            Ideal.span {p'} = P'.map (algebraMap (𝓞 F) (SInt 𝔪)) → H x x' = 1 →
              sexticResidueSymbol ι 𝔪 P p' ^ (6 / ℓ) = sexticResidueSymbol ι 𝔪 P' p ^ (6 / ℓ)

set_option linter.style.haveILetI false

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

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

/-- Clause 5 for two places given by generators. -/
theorem SymbolPkg.recip {ℓ : ℕ} (P : SymbolPkg F ℓ) (hℓ : ℓ = 2 ∨ ℓ = 3) (ι : F →+* ℂ)
    {𝔪 : Ideal (𝓞 F)} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v, v ∈ S ↔ 𝔪 ≤ v.asIdeal)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (v v' : HeightOneSpectrum (𝓞 F)) (hvv : v ≠ v') (hv : ¬ 𝔪 ≤ v.asIdeal)
    (hv' : ¬ 𝔪 ≤ v'.asIdeal) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (h6' : (6 : 𝓞 F) ∉ v'.asIdeal)
    (p p' : SInt 𝔪) (x x' : Fˣ) (hx : (x : F) = p) (hx' : (x' : F) = p')
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hp' : Ideal.span {p'} = v'.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hH : P.HS S x x' = 1) :
    sexticResidueSymbol ι 𝔪 v.asIdeal p' ^ (6 / ℓ) =
      sexticResidueSymbol ι 𝔪 v'.asIdeal p ^ (6 / ℓ) := by
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
  -- the tame symbols
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
  -- product formula over `S ∪ {v, v'}`
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
  have hHS : ∏ w ∈ S, P.h w x (emb F w x') = 1 := by
    rw [P.HS_apply] at hH; exact hH
  rw [hHS, mul_one] at hprod
  have hskew := P.skew v x x'
  simp only [SymbolPkg.hv_apply] at hskew
  have heq : P.h v' x (emb F v' x') = P.h v x' (emb F v x) := by
    have := hprod.trans hskew.symm
    exact mul_left_cancel this
  have hF : algebraMap (𝓞 F) F ξ' ^ (6 / ℓ) = algebraMap (𝓞 F) F ξ ^ (6 / ℓ) := by
    rw [← t1, ← t2, heq]
  rw [hsym, hsym', ← map_pow ι (algebraMap (𝓞 F) F ξ), ← map_pow ι (algebraMap (𝓞 F) F ξ'), hF]

end C0Y

namespace C0Y

/-- The packages that C0-H needs: local `ℓ`-th Hilbert symbols for totally complex number
fields containing `μ_ℓ`. -/
def PkgHyp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ), ℓ.Prime → (∃ ζ : F, IsPrimitiveRoot ζ ℓ) →
    (∀ w : InfinitePlace F, w.IsComplex) → Nonempty (SymbolPkg F ℓ)

/-- **C0-H from the local-symbol packages.** -/
theorem cutH_of_pkgHyp (hpkg : PkgHyp) : CutH := by
  intro n hn0 hn F _ _ _ ι ℓ hℓ
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
  obtain ⟨P⟩ := hpkg F ℓ hℓp ⟨ζ, hζ⟩ hcx
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
  obtain ⟨c1, c2, c3, c4⟩ := P.clauses hℓp hζ hcx hc S hSℓ hcl
  rw [hSet] at c2 c3
  refine ⟨P.HS S, c1, c2, c3, c4, ?_⟩
  intro Pi Pi' hPi hPi' hE hE' hne p p' x x' hx hx' hp hp' hH
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
  exact P.recip hℓ ι S hS hSℓ hz6 v v' hvv (hnot Pi hPi hE) (hnot Pi' hPi' hE')
    (h6 Pi hPi hE) (h6 Pi' hPi' hE') p p' x x' hx hx' hp hp' hH

end C0Y
end
end

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

section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open ArtinPrimitiveRoots
open NumberField IsDedekindDomain
theorem solution :
  ∀ (n : ℕ), 0 < n → 12 ∣ n → ∀ (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (ℓ : ℕ), (ℓ = 2 ∨ ℓ = 3) →
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ H : Fˣ →* Fˣ →* rootsOfUnity ℓ F,
        (∀ x, H x x = 1) ∧
        (∀ u ∈ (placesOf 𝔪).unit F, ∀ u' ∈ (placesOf 𝔪).unit F, H u u' = 1) ∧
        (∀ x, (∀ u ∈ (placesOf 𝔪).unit F, H x u = 1) →
          ∃ u ∈ (placesOf 𝔪).unit F, H (x * u⁻¹) = 1) ∧
        Finite (Fˣ ⧸ H.ker) ∧
        ∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P → IsExterior 𝔪 P' →
          P ≠ P' →
          ∀ (p p' : SInt 𝔪) (x x' : Fˣ), (x : F) = p → (x' : F) = p' →
            Ideal.span {p} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
            Ideal.span {p'} = P'.map (algebraMap (𝓞 F) (SInt 𝔪)) → H x x' = 1 →
              sexticResidueSymbol ι 𝔪 P p' ^ (6 / ℓ) = sexticResidueSymbol ι 𝔪 P' p ^ (6 / ℓ) :=
  C0Y.cutH_of_pkgHyp C0Z.pkgHyp
end
end
