-- Prove2me | Definitions.Def_ModularCurve_QAdicPlaceModV2
-- name    : ModularCurve_QAdicPlaceModV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/19a6ef10-fd19-59bd-855e-dc5574dbc00c
-- title:
--   Coefficients of the integral j-expansion over a commutative ring
-- statement:
--   Throughout, $K$ is a commutative ring and the ambient object is the field-of-Laurent-series type $\mathrm{LaurentSeries}\,K$ of Hahn series over $\mathbb{Z}$ with coefficients in $K$. The series in play is `jqModC K`, defined as $q^{-1}$ (the Hahn series `single (-1) 1`) times the image in $K[[q]]$ of the integral power series `jNum` $= E_4^3\cdot(\eta\text{-product})^{-24}$ under the unique ring map $\mathbb{Z}\to K$; thus `jqModC K` is the $q$-expansion of the modular $j$-invariant, reduced into $K$, with leading term $q^{-1}$ and all coefficients integral.
--
--   The declarations collected here are the coefficient facts about powers of this series. First, for every $n$, the $n$-th power satisfies $(\mathtt{jqModC}\,K)^n = q^{-n}\cdot\bigl(\overline{\mathtt{jNum}}\bigr)^n$, where $\overline{\mathtt{jNum}}$ denotes the image of `jNum` in $K[[q]]$; second, that image has constant coefficient $1$, because `jNum` does and the constant coefficient commutes with coefficientwise base change. Consequently the coefficient of $q^{-n}$ in $(\mathtt{jqModC}\,K)^n$ equals $1$, and the coefficient at any exponent $m < -n$ vanishes, since a power series contributes nothing in negative degrees. The case $n = 1$ gives that the coefficient of `jqModC K` at $-1$ is $1$. The last two declarations restate the vanishing below $q^{-b}$ and the value $1$ at $q^{-1}$ at the top level of the `ModularCurve` namespace, in the form in which they are consumed. The module then opens the namespace with its standing context, a field $K$, an intermediate field $F$ of $K(\!(q)\!)/K$, and a nonzero level $N$, under which the $q$-adic place constructions of the imported modules are made.
--
--   **Relation to Mathlib.** The coefficient manipulations use Mathlib's `HahnSeries`/`LaurentSeries` and `PowerSeries` API (`single`, `ofPowerSeries`, `coeff_single_mul`, `constantCoeff`); the series `jqModC` itself, an integral $q$-expansion of $j$ specialised to an arbitrary commutative ring, is the project's own, as Mathlib has no such object.
--
--   **Where it is used.** These coefficient facts are exactly what is needed to show that `jqModC K` is nonzero of Hahn-series order $-1$, hence that inversion of it provides a uniformiser; on that rests the construction, in the imported modules, of the cusp at infinity as a degree-one $K$-rational place of the geometric modular function field $K(\bar j(q),\bar j(q^N))$, with $\operatorname{ord}_\infty \bar j(q) = -1$ and $\operatorname{ord}_\infty \bar j(q^N) = -N$. This place is the base point used when the modular curve of level $N$ is studied over coefficient fields of arbitrary characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_QAdicPlaceModV2.lean

import Mathlib
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QAdicPlaceMod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section InlinedTheorems

namespace ModularCurve
namespace CharLRows

open HahnSeries

variable (K : Type*) [CommRing K]

private theorem jqModC_pow (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

private theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

private theorem coeff_jqModC_pow_self (n : ℕ) : ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

private theorem coeff_jqModC_pow_of_lt_loc {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : ((jqModC K) ^ n).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

private theorem coeff_jqModC_neg_one_loc : (jqModC K).coeff (-1 : ℤ) = 1 := by
  simpa using coeff_jqModC_pow_self K 1

end CharLRows
end ModularCurve

open ModularCurve in

private theorem ModularCurve.coeff_jqModC_neg_one_loc (K : Type*) [CommRing K] :
    (jqModC K).coeff (-1 : ℤ) = 1 :=
  CharLRows.coeff_jqModC_neg_one_loc K

open ModularCurve in

private theorem ModularCurve.coeff_jqModC_pow_of_lt_loc (K : Type*) [CommRing K] {b : ℕ} {m : ℤ} (hm : m < -(b : ℤ)) :
    ((jqModC K) ^ b).coeff m = 0 :=
  CharLRows.coeff_jqModC_pow_of_lt_loc K hm

end InlinedTheorems

set_option autoImplicit false

noncomputable section

open HahnSeries AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000

namespace ModularCurve

variable (K : Type*) [Field K]

section OrderJqModC

end OrderJqModC

section QAdicPlaceMod

variable (F : IntermediateField K (LaurentSeries K))

end QAdicPlaceMod

section LevelN

variable (N : ℕ) [NeZero N]

end LevelN

section Gates

end Gates

end ModularCurve


