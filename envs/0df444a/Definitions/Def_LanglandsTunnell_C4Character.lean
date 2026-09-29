-- Prove2me | Definitions.Def_LanglandsTunnell_C4Character
-- name    : LanglandsTunnell_C4Character
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/57a86277-8961-511d-93da-7f00041feaae
-- title:
--   The order-four cyclic subgroup and its Galois character
-- statement:
--   Throughout, $L$ is a number field equipped with a group isomorphism $e$ of $L \simeq_{\mathbb{Q}} L$ with $\mathrm{GL}_2(\mathbb{Z}/3)$, and $\gamma_T$ denotes the element $e^{-1}(\bar t)$, where $\bar t$ is the reduction modulo the prime above $3$ of the explicit matrix $\tilde T$ over $\mathbb{Z}[\sqrt{-2}]$; $\gamma_T$ has order $8$ and generates the subgroup `c8H e`. Three objects are introduced. First, `c4H e` is the subgroup of $L \simeq_{\mathbb{Q}} L$ of integer powers of $\gamma_T^2$; it is shown to have order $4$ (since $\gamma_T^2$ has order $4$) and to be contained in `c8H e`, together with the canonical monoid homomorphism `c4H_inclusion` between the two subgroups, which carries the distinguished element `gammaTSqMem` (namely $\gamma_T^2$ viewed inside `c4H e`) to the square of the corresponding generator of `c8H e`. Second, for $\zeta \in \mathbb{C}$ with $\zeta^4 = -1$, `chiGal4 e hζ` is the composite of that inclusion with the character `chiGal e hζ` of `c8H e`; it sends $\gamma_T^2$ to the square of the unit determined by $\zeta$, this square has order $4$, and the resulting character of `c4H e` is injective. Third, assuming in addition $L/\mathbb{Q}$ Galois, `artinValue4 e hζ v` is defined for a height-one prime $v$ of the ring of integers of the fixed field of `c4H e`: it is the value of `chiGal4 e hζ` at the element `seedFrob (c4H e) v`, the arithmetic Frobenius at a chosen prime of $\mathcal{O}_L$ over $v$ raised to the least positive exponent landing in `c4H e`.
--
--   Also established: $\gamma_T^2$ lies in `sylowH e` (witnessed by the square of $\tilde T$ in the explicit $16$-element list `P16`) and in `detKer e`, hence `c4H e` $\le$ `quatH e`; together with `c4H e` $\le$ `c8H e` this yields inclusions of fixed fields, with the attendant algebra and scalar-tower structures over $\mathbb{Q}$ and under $L$.
--
--   **Relation to Mathlib.** The subgroup is Mathlib's `Subgroup.zpowers` of an explicit Galois element, and the fixed fields are Mathlib's `FixedPoints.intermediateField`; the characters, the Frobenius datum and the Artin values are the project's own constructions.
--
--   **Where it is used.** These are the order-$4$ layer of the tower of subgroups of $\mathrm{GL}_2(\mathbb{F}_3)$ used in the Langlands–Tunnell step: the character `chiGal4` and the values `artinValue4` provide the Artin data over the fixed field of `c4H e` from which the relevant Hecke eigensystem over the quaternionic layer is obtained by descent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_C4Character.lean

import Definitions.Def_LanglandsTunnell_C8Character
import Definitions.Def_LanglandsTunnell_QuatH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain

section C4Sub

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

theorem gammaT_sq_mem_c8H : gammaT e ^ 2 ∈ c8H e :=
  Subgroup.pow_mem _ (gammaT_mem e) 2

def c4H : Subgroup (L ≃ₐ[ℚ] L) := Subgroup.zpowers (gammaT e ^ 2)

theorem mem_c4H_iff (γ : L ≃ₐ[ℚ] L) : γ ∈ c4H e ↔ ∃ k : ℤ, (gammaT e ^ 2) ^ k = γ :=
  Subgroup.mem_zpowers_iff

theorem c4H_le_c8H : c4H e ≤ c8H e :=
  (Subgroup.zpowers_le (G := L ≃ₐ[ℚ] L)).2 (gammaT_sq_mem_c8H e)

theorem orderOf_gammaT_sq : orderOf (gammaT e ^ 2) = 4 := by
  rw [orderOf_pow, orderOf_gammaT]
  decide

theorem card_c4H : Nat.card ↥(c4H e) = 4 := by
  rw [c4H, Nat.card_zpowers, orderOf_gammaT_sq]

def gammaTSqMem : ↥(c4H e) := ⟨gammaT e ^ 2, Subgroup.mem_zpowers _⟩

theorem orderOf_gammaTSqMem : orderOf (gammaTSqMem e) = 4 := by
  rw [← orderOf_injective (c4H e).subtype Subtype.coe_injective (gammaTSqMem e)]
  exact orderOf_gammaT_sq e

theorem mem_zpowers_gammaTSqMem (x : ↥(c4H e)) : x ∈ Subgroup.zpowers (gammaTSqMem e) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
  exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩

def c4H_inclusion : ↥(c4H e) →* ↥(c8H e) := Subgroup.inclusion (c4H_le_c8H e)

theorem c4H_inclusion_gammaTSqMem : c4H_inclusion e (gammaTSqMem e) = gammaTMem e ^ 2 :=
  Subtype.ext rfl

end C4Sub

section ChiGal4

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  {ζ : ℂ} (hζ : ζ ^ 4 = -1)

def chiGal4 : ↥(c4H e) →* ℂˣ := (chiGal e hζ).comp (c4H_inclusion e)

theorem chiGal4_apply (x : ↥(c4H e)) : chiGal4 e hζ x = chiGal e hζ (c4H_inclusion e x) := rfl

theorem chiGal4_gammaTSqMem : chiGal4 e hζ (gammaTSqMem e) = zetaUnit hζ ^ 2 := by
  rw [chiGal4_apply, c4H_inclusion_gammaTSqMem, map_pow, chiGal_gammaTMem]

include hζ in
theorem zetaUnit_sq_pow_two_ne_one : (zetaUnit hζ ^ 2) ^ 2 ≠ 1 := by
  rw [← pow_mul]
  exact zetaUnit_pow_four_ne_one hζ

theorem orderOf_zetaUnit_sq : orderOf (zetaUnit hζ ^ 2) = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := zetaUnit hζ ^ 2) (zetaUnit_sq_pow_two_ne_one hζ)
    (by rw [← pow_mul]; exact zetaUnit_pow_eight hζ)
  norm_num at h
  exact h

theorem chiGal4_injective : Function.Injective (chiGal4 e hζ) := by
  refine (injective_iff_map_eq_one (chiGal4 e hζ)).2 fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_gammaTSqMem e x)
  rw [map_zpow, chiGal4_gammaTSqMem] at hx
  have hdvd : (4 : ℤ) ∣ k := by
    rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_zetaUnit_sq] at hx
    exact_mod_cast hx
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_gammaTSqMem]
  exact_mod_cast hdvd

end ChiGal4

section Artin4

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

def artinValue4 (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) : ℂˣ :=
  chiGal4 e hζ ⟨seedFrob (c4H e) v, seedFrob_mem (c4H e) v⟩

theorem artinValue4_def (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) :
    artinValue4 e hζ v = chiGal4 e hζ ⟨seedFrob (c4H e) v, seedFrob_mem (c4H e) v⟩ := rfl

end Artin4

section QuatHContainment

open FLT.ExplicitLift LanglandsTunnell.Lift48 LanglandsTunnell

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

theorem pw_Tlift_two_mem_P16 : pw Tlift 2 ∈ P16 := by
  rw [pw_eq_pow, pow_two]
  exact P16_mul_closed Tlift one_mem_P16.2.1 Tlift one_mem_P16.2.1

theorem gammaT_sq_mem_sylowH : gammaT e ^ 2 ∈ sylowH e :=
  ⟨pw Tlift 2, pw_Tlift_two_mem_P16, by
    rw [map_pow, e_gammaT, val_tbarGL_pow, ← pw_eq_pow, RingHom.mapMatrix_apply]⟩

theorem gammaT_sq_mem_detKer : gammaT e ^ 2 ∈ detKer e := by
  rw [mem_detKer_iff, map_pow, e_gammaT, val_tbarGL_pow, ← pw_eq_pow]
  decide

theorem c4H_le_quatH : c4H e ≤ quatH e :=
  (Subgroup.zpowers_le (G := L ≃ₐ[ℚ] L)).2 ⟨gammaT_sq_mem_sylowH e, gammaT_sq_mem_detKer e⟩

end QuatHContainment

section TowerInstances

open LanglandsTunnell

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

theorem fixFld_c8H_le_fixFld_c4H : fixFld (c8H e) ≤ fixFld (c4H e) :=
  fixFld_le_fixFld_of_le (c4H_le_c8H e)

noncomputable instance algebra_fixFldC8H_fixFldC4H :
    Algebra ↥(fixFld (c8H e)) ↥(fixFld (c4H e)) :=
  (IntermediateField.inclusion (fixFld_c8H_le_fixFld_c4H e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldC8H_fixFldC4H :
    IsScalarTower ℚ ↥(fixFld (c8H e)) ↥(fixFld (c4H e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldC8H_fixFldC4H_L :
    IsScalarTower ↥(fixFld (c8H e)) ↥(fixFld (c4H e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_c8H_le_fixFld_c4H e) x).symm)

theorem fixFld_quatH_le_fixFld_c4H : fixFld (quatH e) ≤ fixFld (c4H e) :=
  fixFld_le_fixFld_of_le (c4H_le_quatH e)

noncomputable instance algebra_fixFldQuatH_fixFldC4H :
    Algebra ↥(fixFld (quatH e)) ↥(fixFld (c4H e)) :=
  (IntermediateField.inclusion (fixFld_quatH_le_fixFld_c4H e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldQuatH_fixFldC4H :
    IsScalarTower ℚ ↥(fixFld (quatH e)) ↥(fixFld (c4H e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldQuatH_fixFldC4H_L :
    IsScalarTower ↥(fixFld (quatH e)) ↥(fixFld (c4H e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_quatH_le_fixFld_c4H e) x).symm)

end TowerInstances

section SynthProbe

open LanglandsTunnell
variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
noncomputable example : Algebra (𝓞 ↥(fixFld (c8H e))) (𝓞 ↥(fixFld (c4H e))) := inferInstance
noncomputable example : Algebra.IsIntegral (𝓞 ↥(fixFld (c8H e))) (𝓞 ↥(fixFld (c4H e))) := inferInstance
noncomputable example : Algebra (𝓞 ↥(fixFld (quatH e))) (𝓞 ↥(fixFld (c4H e))) := inferInstance
noncomputable example : Algebra.IsIntegral (𝓞 ↥(fixFld (quatH e))) (𝓞 ↥(fixFld (c4H e))) := inferInstance
end SynthProbe

end LanglandsTunnell.P2

end


