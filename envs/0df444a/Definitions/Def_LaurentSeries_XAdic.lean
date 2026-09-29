-- Prove2me | Definitions.Def_LaurentSeries_XAdic
-- name    : LaurentSeries_XAdic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/8e5fa3c6-33f8-5f7d-b9d2-b223208b11eb
-- title:
--   The X-adic normed field structure on Laurent series
-- statement:
--   For a field $F$, Mathlib equips the field $F((X))$ of formal Laurent series (Hahn series over $\mathbb{Z}$) with the $X$-adic valuation `Valued.v` taking values in $\mathbb{Z}^{m0} =$ `WithZero (Multiplicative ℤ)`. This module fixes the normalisation and packages the resulting analytic structure. The anchor `valued_single_one_one` records that the uniformiser $X =$ `HahnSeries.single 1 1` has valuation the image of `Multiplicative.ofAdd (-1)`, i.e. $v(X) = \exp(-1)$, so that $v(f)$ decreases as $\operatorname{ord}_X f$ increases; `single_one_one_ne_zero` deduces $X \neq 0$. Three scoped instances follow, in the namespace `LaurentSeries.XAdic`: `rankOne`, which exhibits `Valued.v` as nontrivial (witness $X$, whose valuation is neither $0$ nor $1$) and of rank at most one by composing the embedding of its value group with `WithZeroMulInt.toNNReal` at base $2$ — thus the associated absolute value is $\|f\| = 2^{-\operatorname{ord}_X f}$, $\|0\| = 0$; `nontriviallyNormedField`, obtained from the rank-one valuation by `Valued.toNontriviallyNormedField`, so that the norm topology and uniformity are the valued ones; and `isUltrametricDist`, from the non-archimedean inequality $\|f+g\| \le \max(\|f\|,\|g\|)$ for the valued norm. A low-priority classical `DecidableEq` instance is also provided. The remaining lemmas are the numerical facts needed to use $X^N$ as a Tate parameter: $\|X\| < 1$ and $\|X\|_+ < 1$ for the real and nonnegative-real norms, $\|X^N\|_+ < 1$ for every $N \neq 0$, and $X^N \neq 0$ for all $N$. Finally `charZero` shows that $F((X))$ has characteristic zero whenever $F$ does, via injectivity of the constant embedding `HahnSeries.C`.
--
--   **Relation to Mathlib.** No new object is introduced: the valuation `Valued.v` on `LaurentSeries F`, the passage `Valued.toNontriviallyNormedField` from a rank-one valuation to a nontrivially normed field, and the completeness of `LaurentSeries F` are all Mathlib's. The module only supplies the missing `Valuation.RankOne` instance (base $2$, nontriviality witness $X$) and the derived `NontriviallyNormedField`, `IsUltrametricDist` and `DecidableEq` instances as scoped instances, together with the normalisation lemma $v(X) = \exp(-1)$.
--
--   **Where it is used.** These instances let the project's ultrametric theory of the Tate curve over a complete non-archimedean field be instantiated at $K = F((t))$ with Tate parameter $q = t^N$, where $0 < \|q\| < 1$ is exactly the content of `nnnorm_X_pow_lt_one` and `X_pow_ne_zero`. That instantiation describes the behaviour of elliptic curves and their level structures at the cusps of the modular curves $X(N)$, $X_1(N)$, $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LaurentSeries_XAdic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped NNReal
open HahnSeries

namespace LaurentSeries.XAdic

variable (F : Type*) [Field F]

theorem valued_single_one_one :
    (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))
        (HahnSeries.single (1 : ℤ) (1 : F))
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  simpa [WithZero.exp] using LaurentSeries.valuation_single_zpow (K := F) 1

theorem single_one_one_ne_zero : (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ≠ 0 := by
  intro h
  have hv := valued_single_one_one F
  rw [h, map_zero] at hv
  exact WithZero.zero_ne_coe hv

scoped instance rankOne :
    (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).RankOne := by
  haveI hnt : (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨⟨HahnSeries.single (1 : ℤ) (1 : F),
      by rw [valued_single_one_one]; exact WithZero.coe_ne_zero,
      by
        rw [valued_single_one_one]
        intro h
        have h' := Multiplicative.ofAdd.injective (WithZero.coe_inj.mp (h.trans rfl : _ =
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))))
        norm_num at h'⟩⟩
  haveI hle : (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).RankLeOne :=
    Valuation.RankLeOne.mk
      ((WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding)
      (fun a b hab =>
        WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)
          (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hab))
  exact Valuation.RankOne.mk

scoped instance nontriviallyNormedField : NontriviallyNormedField (LaurentSeries F) :=
  Valued.toNontriviallyNormedField (LaurentSeries F) (WithZero (Multiplicative ℤ))

scoped instance isUltrametricDist : IsUltrametricDist (LaurentSeries F) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm (LaurentSeries F) (WithZero (Multiplicative ℤ)))

scoped instance (priority := low) decidableEq : DecidableEq (LaurentSeries F) := Classical.decEq _

theorem norm_X_lt_one : ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, valued_single_one_one]
  exact WithZero.coe_lt_coe.mpr (Multiplicative.ofAdd_lt.mpr (by norm_num))

theorem nnnorm_X_lt_one : ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F)‖₊ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
  exact norm_X_lt_one F

theorem nnnorm_X_pow_lt_one {N : ℕ} (hN : N ≠ 0) :
    ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N‖₊ < 1 := by
  rw [nnnorm_pow]
  exact pow_lt_one₀ zero_le (nnnorm_X_lt_one F) hN

theorem X_pow_ne_zero (N : ℕ) : (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N ≠ 0 :=
  pow_ne_zero N (single_one_one_ne_zero F)

theorem charZero [CharZero F] : CharZero (LaurentSeries F) :=
  charZero_of_injective_ringHom (f := (HahnSeries.C : F →+* LaurentSeries F)) HahnSeries.C_injective

end LaurentSeries.XAdic

end


