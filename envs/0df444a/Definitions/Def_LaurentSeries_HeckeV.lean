-- Prove2me | Definitions.Def_LaurentSeries_HeckeV
-- name    : LaurentSeries_HeckeV
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/39218592-fa2f-50d4-b9c2-b6b2d9fb3922
-- title:
--   The formal operators Vℓ​ and Tℓ​ on Laurent series
-- statement:
--   Throughout, $R$ is a commutative ring and $\ell$ a natural number with $0 < \ell$; `LaurentSeries R` is Mathlib's type of Hahn series over $\mathbb{Z}$ with coefficients in $R$, i.e. formal series $\sum_n a_n q^n$ whose coefficient support is well-founded (in particular bounded below).
--
--   The helper lemma `bddBelow_support_coeff_div` states that for $f$ a Laurent series over a type with zero and $\ell > 0$, the function $n \mapsto a_{n/\ell}(f)$ if $\ell \mid n$ and $0$ otherwise has support bounded below; this is what allows the function to be packaged as a Laurent series. The operator `heckeV R ℓ hℓ` is the $R$-linear endomorphism of `LaurentSeries R` sending $f$ to the series whose $n$-th coefficient is $a_{n/\ell}(f)$ when $\ell \mid n$ and $0$ otherwise — that is, $\sum_n a_n q^n \mapsto \sum_n a_n q^{\ell n}$ — and `coeff_heckeV` records exactly this coefficient formula. Additivity and compatibility with scalars are part of the bundled linear-map data.
--
--   The operator `heckeT R ℓ hℓ k`, for a natural number $k$, is defined as $U_\ell + \ell^{k-1} \cdot V_\ell$, where $U_\ell$ is `heckeU R ℓ hℓ` from the imported module (the $R$-linear map with $a_n(U_\ell f) = a_{\ell n}(f)$), the scalar $\ell^{k-1}$ is the image of $\ell$ in $R$ raised to the truncated-subtraction exponent $k-1$ (so $k = 0$ and $k = 1$ both give the exponent $0$). The lemma `coeff_heckeT` gives the resulting coefficientwise description:
--   $$a_n(T_\ell f) = a_{\ell n}(f) + \ell^{k-1}\bigl(\text{$a_{n/\ell}(f)$ if $\ell \mid n$, else $0$}\bigr).$$
--   Only these coefficient formulas, together with linearity, are fixed here; no relation between the operators is asserted in this module.
--
--   **Relation to Mathlib.** `LaurentSeries R` and the constructor `HahnSeries.ofSuppBddBelow` are Mathlib's; the formal Hecke operators themselves are the project's own, and are the Laurent-series counterparts of the project's [`PowerSeries.heckeU`](../def/PowerSeries_FormalHeckeOperators.html#L11), [`PowerSeries.heckeV`](../def/PowerSeries_FormalHeckeOperators.html#L20) and [`PowerSeries.heckeT`](../def/PowerSeries_FormalHeckeOperators.html#L33) on $R⟦X⟧$.
--
--   **Where it is used.** These operators give the purely formal, coefficientwise description of $T_\ell$ acting on $q$-expansions, with weight $k = 2$ the case relevant to differentials on $X_0(N)$; the imported module also records that $U_\ell$ commutes with the coercion of power series into Laurent series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LaurentSeries_HeckeV.lean

import Mathlib
import Definitions.Def_LaurentSeries_HeckeU

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LaurentSeries

theorem bddBelow_support_coeff_div {R : Type*} [Zero R] (f : LaurentSeries R) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    BddBelow (Function.support fun n : ℤ => if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0) := by
  by_cases hS : (Function.support f.coeff).Nonempty
  · refine ⟨(ℓ : ℤ) * f.isWF_support.min hS, fun n hn => ?_⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    obtain ⟨⟨m, rfl⟩, hm⟩ := hn
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
    rw [Int.mul_ediv_cancel_left _ hℓ0] at hm
    have hmin : f.isWF_support.min hS ≤ m := f.isWF_support.min_le hS hm
    have hℓ1 : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
    nlinarith
  · refine ⟨0, fun n hn => ?_⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    exact absurd ⟨_, hn.2⟩ hS

noncomputable def heckeV (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    LaurentSeries R →ₗ[R] LaurentSeries R where
  toFun f := HahnSeries.ofSuppBddBelow (fun n : ℤ => if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0)
    (bddBelow_support_coeff_div f ℓ hℓ)
  map_add' f g := by
    ext n
    by_cases h : (ℓ : ℤ) ∣ n <;> simp [HahnSeries.ofSuppBddBelow_coeff, h]
  map_smul' c f := by
    ext n
    by_cases h : (ℓ : ℤ) ∣ n <;> simp [HahnSeries.ofSuppBddBelow_coeff, h]

@[simp]
theorem coeff_heckeV (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (f : LaurentSeries R) (n : ℤ) :
    (heckeV R ℓ hℓ f).coeff n = if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0 :=
  HahnSeries.ofSuppBddBelow_coeff _ (bddBelow_support_coeff_div f ℓ hℓ) n

noncomputable def heckeT (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ) :
    LaurentSeries R →ₗ[R] LaurentSeries R :=
  heckeU R ℓ hℓ + ((ℓ : R) ^ (k - 1)) • heckeV R ℓ hℓ

theorem coeff_heckeT (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ) (f : LaurentSeries R) (n : ℤ) :
    (heckeT R ℓ hℓ k f).coeff n =
      f.coeff (ℓ * n) + (ℓ : R) ^ (k - 1) * (if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0) := by
  simp [heckeT, coeff_heckeU, coeff_heckeV]

end LaurentSeries


