-- Prove2me | Definitions.Def_LaurentSeries_HeckeU
-- name    : LaurentSeries_HeckeU
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/3cc70365-ab54-58f5-b95c-1b91790e5e20
-- title:
--   The Uℓ​ decimation operator on Laurent series
-- statement:
--   Fix a commutative ring $R$ and a natural number $\ell$ with $0 < \ell$. The module defines [`LaurentSeries.heckeU R ℓ hℓ`](../def/LaurentSeries_HeckeU.html#L22) as an $R$-linear endomorphism of `LaurentSeries R`, the Laurent series over $R$ realised as Hahn series with value group $\mathbb{Z}$; on coefficients it is the decimation map $f \mapsto \bigl(n \mapsto a_{\ell n}\bigr)$, so that $\sum_{n \in \mathbb{Z}} a_n q^n \mapsto \sum_{n \in \mathbb{Z}} a_{\ell n} q^n$. This is recorded as the simp lemma [`LaurentSeries.coeff_heckeU`](../def/LaurentSeries_HeckeU.html#L33): the $n$-th coefficient of `heckeU R ℓ hℓ f` is the $(\ell n)$-th coefficient of $f$, with the same index convention as [`PowerSeries.coeff_heckeU`](../def/PowerSeries_FormalHeckeOperators.html#L16).
--
--   For this to define a Hahn series one needs the new coefficient function to have support bounded below, which is the content of the helper [`LaurentSeries.bddBelow_support_coeff_mul`](../def/LaurentSeries_HeckeU.html#L8): for $f$ a Laurent series over a type with a zero and $\ell > 0$, the set of $n \in \mathbb{Z}$ with $a_{\ell n} \neq 0$ is bounded below. If the support of $f$ is empty this is trivial; otherwise the minimum $m$ of the (well-founded) support of $f$ together with $\ell n \le n$ for $n < 0$ gives $\min(m,0)$ as a lower bound.
--
--   Finally, [`LaurentSeries.heckeU_ofPowerSeries`](../def/LaurentSeries_HeckeU.html#L37) states the compatibility with the power-series operator of the companion module: for $\varphi \in R[[q]]$, applying `heckeU R ℓ hℓ` to the image of $\varphi$ in `LaurentSeries R` gives the image of [`PowerSeries.heckeU ℓ φ`](../def/PowerSeries_FormalHeckeOperators.html#L11), where the latter is the $R$-linear map $\varphi \mapsto \bigl(n \mapsto \mathrm{coeff}_{\ell n}\,\varphi\bigr)$ on $R[[q]]$. Thus $U_\ell$ on Laurent series extends $U_\ell$ on power series along $R[[q]] \hookrightarrow R((q))$. Note that only the $U$-operator is transferred to Laurent series here; the operators `heckeV` and `heckeT` of the imported module remain on power series.
--
--   **Relation to Mathlib.** Mathlib supplies `LaurentSeries`, `HahnSeries.ofSuppBddBelow` and the coercion from `PowerSeries`, but no formal $U_\ell$ operator; `heckeU` on Laurent series is the project's own, the Laurent-series counterpart of the project's [`PowerSeries.heckeU`](../def/PowerSeries_FormalHeckeOperators.html#L11).
--
--   **Where it is used.** The $q$-expansions used in the project are Laurent-series valued with $\mathbb{Z}$-indexed coefficients, so the decimation operator is stated at that level; on $q$-expansions of weight-two forms of level prime to $\ell$ it computes $T_\ell$ modulo $\ell$, and it is the coefficientwise effect of the Cartier operator, both of which enter the study of mod-$\ell$ Galois representations attached to modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LaurentSeries_HeckeU.lean

import Mathlib
import Definitions.Def_PowerSeries_FormalHeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LaurentSeries

theorem bddBelow_support_coeff_mul {R : Type*} [Zero R] (f : LaurentSeries R) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    BddBelow (Function.support fun n : ℤ => f.coeff (ℓ * n)) := by
  by_cases hS : (Function.support f.coeff).Nonempty
  · refine ⟨min (f.isWF_support.min hS) 0, fun n hn => ?_⟩
    have hmem : (ℓ : ℤ) * n ∈ Function.support f.coeff := hn
    have hmin : f.isWF_support.min hS ≤ (ℓ : ℤ) * n := f.isWF_support.min_le hS hmem
    by_cases hn0 : 0 ≤ n
    · exact le_trans (min_le_right _ _) hn0
    · have hℓ1 : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
      have hle : (ℓ : ℤ) * n ≤ n := by nlinarith
      exact le_trans (min_le_left _ _) (hmin.trans hle)
  · refine ⟨0, fun n hn => ?_⟩
    exact absurd ⟨(ℓ : ℤ) * n, hn⟩ hS

noncomputable def heckeU (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    LaurentSeries R →ₗ[R] LaurentSeries R where
  toFun f := HahnSeries.ofSuppBddBelow (fun n : ℤ => f.coeff (ℓ * n)) (bddBelow_support_coeff_mul f ℓ hℓ)
  map_add' f g := by
    ext n
    simp [HahnSeries.ofSuppBddBelow_coeff]
  map_smul' c f := by
    ext n
    simp [HahnSeries.ofSuppBddBelow_coeff]

@[simp]
theorem coeff_heckeU (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (f : LaurentSeries R) (n : ℤ) :
    (heckeU R ℓ hℓ f).coeff n = f.coeff (ℓ * n) :=
  HahnSeries.ofSuppBddBelow_coeff _ (bddBelow_support_coeff_mul f ℓ hℓ) n

theorem heckeU_ofPowerSeries (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (φ : PowerSeries R) :
    heckeU R ℓ hℓ (φ : LaurentSeries R) = ((PowerSeries.heckeU ℓ φ : PowerSeries R) : LaurentSeries R) := by
  ext n
  rw [coeff_heckeU, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h1 : ¬ (ℓ : ℤ) * (m : ℤ) < 0 := not_lt.mpr (by positivity)
    have h2 : ¬ (m : ℤ) < 0 := not_lt.mpr hn
    rw [if_neg h1, if_neg h2, PowerSeries.coeff_heckeU]
    congr 1
  · have h1 : (ℓ : ℤ) * n < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hℓ) hn
    rw [if_pos h1, if_pos hn]

end LaurentSeries


