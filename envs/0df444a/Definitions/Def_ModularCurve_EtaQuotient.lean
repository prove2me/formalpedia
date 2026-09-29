-- Prove2me | Definitions.Def_ModularCurve_EtaQuotient
-- name    : ModularCurve_EtaQuotient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/6ef8b177-6f2f-5472-9308-9574f24e9294
-- title:
--   Sharp eta quotient on X0​(ℓ): exponents, series, invariance
-- statement:
--   Fix a natural number $\ell$. The module introduces the integers $k(\ell)=\gcd(\ell-1,12)$ (`sharpIndex`, with truncated natural subtraction) and $e(\ell)=24/k(\ell)$ (`sharpExp`), together with the elementary arithmetic of these quantities: $k(\ell)$ divides $12$, $24$ and $\ell-1$, is positive, $e(\ell)k(\ell)=24$, $e(\ell)$ is even, and $k(\ell)\cdot n(\ell)=\ell-1$, $e(\ell)(\ell-1)=24\,n(\ell)$, where $n(\ell)=$ `eisensteinNumerator ℓ` $=(\ell-1)/\gcd(\ell-1,12)$. On the formal side, `etaProdPow ℓ` is the $e(\ell)$-th power of the integral product $\prod_{n\ge 1}(1-X^{n})$ pushed into $\mathbb{Q}[[X]]$, with constant term $1$; under `[NeZero ℓ]`, `sharpUnitSeries ℓ` is the Laurent series $q^{-n(\ell)}\cdot\prod_{n\ge1}(1-q^{n})^{e(\ell)}\cdot\bigl(\prod_{n\ge1}(1-q^{\ell n})^{e(\ell)}\bigr)^{-1}$ over $\mathbb{Q}$, the second factor being the image of `etaProdPow ℓ` under the substitution $q\mapsto q^{\ell}$ given by `qExpand`, inverted in the field of Laurent series. On the analytic side, `sharpUnitFun ℓ` is the function $\tau\mapsto\bigl(\eta(\tau)/\eta(\ell\tau)\bigr)^{e(\ell)}$ on the upper half-plane, where $\ell\tau$ is expressed as the action of [`ModularForm.heckeDiagMatrix ℓ`](../def/ModularForm_HeckeOperator.html#L21) on $\tau$.
--
--   Two propositions are named as inputs. `SharpUnitInvariant ℓ` asserts that `sharpUnitFun ℓ` is invariant under the action of every element of $\Gamma_0(\ell)$ on every point of the upper half-plane. `SharpUnitNecessary ℓ` is a divisibility statement about arbitrary functions: for every natural $m>0$ and every continuous $H:\mathfrak{H}\to\mathbb{C}$ which is $\Gamma_0(\ell)$-invariant and satisfies $H(\tau)^{\ell-1}=\bigl(\Delta(\tau)/\Delta(\ell\tau)\bigr)^{m}$ identically, one has $n(\ell)\mid m$. Thus $e(\ell)$ is recorded as sufficient, and $n(\ell)$ as the obstruction to smaller exponents.
--
--   **Relation to Mathlib.** The Dedekind eta function $\eta$, the discriminant modular form `ModularForm.discriminant` and the congruence subgroups `CongruenceSubgroup.Gamma0` are Mathlib's; the eta-quotient exponents, the formal $q$-expansion `sharpUnitSeries`, the function `sharpUnitFun` and the two invariance/necessity predicates are the project's own.
--
--   **Where it is used.** The function $(\eta(\tau)/\eta(\ell\tau))^{e(\ell)}$ is the $k(\ell)$-th root of Ogg's modular unit $\Delta(\tau)/\Delta(\ell\tau)$ on $X_0(\ell)$, and $n(\ell)$ is the numerator of $(\ell-1)/12$; the two named predicates isolate exactly the automorphy input needed for the modular-curve and cuspidal-divisor computations at prime level used on the modular side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_EtaQuotient.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped ModularForm MatrixGroups

namespace ModularCurve

def sharpIndex (ℓ : ℕ) : ℕ := Nat.gcd (ℓ - 1) 12

def sharpExp (ℓ : ℕ) : ℕ := 24 / sharpIndex ℓ

theorem sharpIndex_def (ℓ : ℕ) : sharpIndex ℓ = Nat.gcd (ℓ - 1) 12 := rfl

theorem sharpExp_def (ℓ : ℕ) : sharpExp ℓ = 24 / sharpIndex ℓ := rfl

theorem sharpIndex_dvd_twelve (ℓ : ℕ) : sharpIndex ℓ ∣ 12 := Nat.gcd_dvd_right _ _

theorem sharpIndex_dvd_sub_one (ℓ : ℕ) : sharpIndex ℓ ∣ ℓ - 1 := Nat.gcd_dvd_left _ _

theorem sharpIndex_pos (ℓ : ℕ) : 0 < sharpIndex ℓ :=
  Nat.pos_of_ne_zero fun h => by simpa [h] using sharpIndex_dvd_twelve ℓ

theorem sharpIndex_dvd_twentyfour (ℓ : ℕ) : sharpIndex ℓ ∣ 24 :=
  (sharpIndex_dvd_twelve ℓ).trans ⟨2, by norm_num⟩

theorem sharpExp_mul_sharpIndex (ℓ : ℕ) : sharpExp ℓ * sharpIndex ℓ = 24 :=
  Nat.div_mul_cancel (sharpIndex_dvd_twentyfour ℓ)

theorem sharpExp_pos (ℓ : ℕ) : 0 < sharpExp ℓ :=
  Nat.pos_of_ne_zero fun h => by simpa [h] using sharpExp_mul_sharpIndex ℓ

theorem two_dvd_sharpExp (ℓ : ℕ) : 2 ∣ sharpExp ℓ := by
  obtain ⟨c, hc⟩ := sharpIndex_dvd_twelve ℓ
  have hk : 0 < sharpIndex ℓ := sharpIndex_pos ℓ
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => by simp [h] at hc
  refine ⟨c, ?_⟩
  have h24 : 24 = sharpIndex ℓ * (2 * c) :=
    calc (24 : ℕ) = 2 * 12 := by norm_num
      _ = 2 * (sharpIndex ℓ * c) := by rw [← hc]
      _ = sharpIndex ℓ * (2 * c) := by ring
  rw [sharpExp, h24, Nat.mul_div_cancel_left _ hk]

theorem sharpExp_div_two_mul_two (ℓ : ℕ) : sharpExp ℓ / 2 * 2 = sharpExp ℓ :=
  Nat.div_mul_cancel (two_dvd_sharpExp ℓ)

theorem two_mul_sharpExp_div_two (ℓ : ℕ) : 2 * (sharpExp ℓ / 2) = sharpExp ℓ :=
  Nat.mul_div_cancel' (two_dvd_sharpExp ℓ)

theorem sharpIndex_mul_eisensteinNumerator (ℓ : ℕ) :
    sharpIndex ℓ * eisensteinNumerator ℓ = ℓ - 1 := by
  rw [eisensteinNumerator, ← sharpIndex_def, Nat.mul_div_cancel' (sharpIndex_dvd_sub_one ℓ)]

theorem sharpExp_mul_sub_one (ℓ : ℕ) : sharpExp ℓ * (ℓ - 1) = 24 * eisensteinNumerator ℓ := by
  rw [← sharpIndex_mul_eisensteinNumerator, ← mul_assoc, sharpExp_mul_sharpIndex]

def etaProdPow (ℓ : ℕ) : PowerSeries ℚ := (etaProd ^ sharpExp ℓ).map (Int.castRingHom ℚ)

theorem etaProdPow_def (ℓ : ℕ) :
    etaProdPow ℓ = (etaProd ^ sharpExp ℓ).map (Int.castRingHom ℚ) := rfl

theorem constantCoeff_etaProdPow (ℓ : ℕ) : PowerSeries.constantCoeff (etaProdPow ℓ) = 1 := by
  rw [etaProdPow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_etaProd, one_pow, map_one]

variable (ℓ : ℕ)

def sharpUnitFun (τ : UpperHalfPlane) : ℂ :=
  (η (τ : ℂ) / η ((ModularForm.heckeDiagMatrix ℓ • τ : UpperHalfPlane) : ℂ)) ^ sharpExp ℓ

theorem sharpUnitFun_apply (τ : UpperHalfPlane) :
    sharpUnitFun ℓ τ =
      (η (τ : ℂ) / η ((ModularForm.heckeDiagMatrix ℓ • τ : UpperHalfPlane) : ℂ)) ^ sharpExp ℓ :=
  rfl

section Series

variable [NeZero ℓ]

def sharpUnitSeries : LaurentSeries ℚ :=
  HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) *
    HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ) *
    (qExpand ℚ ℓ (HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ)))⁻¹

theorem sharpUnitSeries_def :
    sharpUnitSeries ℓ = HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) *
      HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ) *
      (qExpand ℚ ℓ (HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ)))⁻¹ := rfl

end Series

def SharpUnitInvariant : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, sharpUnitFun ℓ (γ • τ) = sharpUnitFun ℓ τ

def SharpUnitNecessary : Prop :=
  ∀ (m : ℕ) (H : UpperHalfPlane → ℂ), 0 < m → Continuous H →
    (∀ τ : UpperHalfPlane, H τ ^ (ℓ - 1) =
      (ModularForm.discriminant τ /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m) →
    (∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, H (γ • τ) = H τ) →
    eisensteinNumerator ℓ ∣ m

end ModularCurve

end


