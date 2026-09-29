-- Prove2me | Definitions.Def_ModularCurve_TateOrigin
-- name    : ModularCurve_TateOrigin
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/6f73bd06-d80a-5f0c-8c9c-d6dc236e62bd
-- title:
--   Tate curve coordinates as Laurent series in a uniformiser
-- statement:
--   Fix a commutative ring $K$. The module defines two elements [`ModularCurve.tateOriginX`](../def/ModularCurve_TateOrigin.html#L10) and [`ModularCurve.tateOriginY`](../def/ModularCurve_TateOrigin.html#L17) of `LaurentSeries (PowerSeries K)`, that is, of $\mathrm{HahnSeries}\,\mathbb{Z}\,(K[[\mathfrak q]])$: series in an outer variable $T$ with integer exponents whose coefficients are power series in $\mathfrak q$. Explicitly,
--   $$x = T^{-2} + T^{-1} + \sum_{k\ge 0} T^{k}\sum_{M\ge 1}\mathfrak q^{M}\Bigl[\sum_{e\mid M} e\Bigl(\binom{e}{k} + (-1)^{k}\binom{e+k-1}{k}\Bigr) - \delta_{k,0}\,2\!\!\sum_{e\mid M} e\Bigr],$$
--   $$y = -T^{-3} - 2T^{-2} - T^{-1} + \sum_{k\ge 0} T^{k}\sum_{M\ge 1}\mathfrak q^{M}\Bigl[\sum_{e\mid M}\Bigl(\binom{e}{2}\binom{e}{k} - \binom{e+1}{2}(-1)^{k}\binom{e+k-1}{k}\Bigr) + \delta_{k,0}\!\!\sum_{e\mid M} e\Bigr],$$
--   all binomial coefficients and divisors being natural numbers cast into $K$, the divisor sums running over the divisors of $M$, and the $\mathfrak q$-coefficient at $M=0$ being set to $0$. Since $\binom{e}{k}$ and $(-1)^{k}\binom{e+k-1}{k}$ are the $T^{k}$-coefficients of $(1+T)^{e}$ and $(1+T)^{-e}$, these are the coordinates of the Tate parametrisation evaluated at $u = 1+T$ and re-expanded with $T$ as the outer variable, the divisor sums encoding $\sum_{e\mid M}e\bigl((1+T)^{e}+(1+T)^{-e}\bigr)-2\sigma_{1}(M)$ and $\sum_{e\mid M}\bigl(\binom{e}{2}(1+T)^{e}-\binom{e+1}{2}(1+T)^{-e}\bigr)+\sigma_{1}(M)$.
--
--   Four coefficient lemmas accompany the definitions: the $T^{-2}$-coefficient of $x$ is the power series $1$ and all coefficients in degrees $<-2$ vanish; the $T^{-3}$-coefficient of $y$ is $-1$ and all coefficients in degrees $<-3$ vanish. Thus $x$ has a double and $y$ a triple pole in $T$, with the normalisations expected at the origin of the Tate curve; no algebraic relation between $x$ and $y$ is asserted here.
--
--   **Relation to Mathlib.** The ambient types `HahnSeries`, `LaurentSeries` and `PowerSeries` are Mathlib's; Mathlib has no Tate curve or Tate parametrisation, so these $q$-expansions, like the Weierstrass coefficients `tateA4`, `tateA6` and the curve `tateLaurent` they accompany, are the project's own.
--
--   **Where it is used.** These series provide a candidate point on the Tate curve $y^{2}+xy = x^{3}+a_{4}(\mathfrak q)x+a_{6}(\mathfrak q)$ over $K[[\mathfrak q]]$, whose Weierstrass coefficients and ellipticity are set up in the companion module, written in a coordinate $T$ with $u = 1+T$ so that $T$ is a uniformiser at the origin. The pole orders recorded here are what makes $T$ a normalised uniformiser, which is the input to residue computations on the Tate curve used in the study of the mod $p$ geometry of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_TateOrigin.lean

import Mathlib
import Definitions.Def_ModularCurve_TateFormal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def tateOriginX (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-2 : ℤ) (1 : PowerSeries K) + HahnSeries.single (-1 : ℤ) (1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k => PowerSeries.mk fun M =>
      if M = 0 then 0 else
        (∑ e ∈ M.divisors, (e : K) * ((e.choose k : K) + (-1) ^ k * ((e + k - 1).choose k : K)))
          - (if k = 0 then 2 * ∑ e ∈ M.divisors, (e : K) else 0))

def tateOriginY (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-3 : ℤ) (-1 : PowerSeries K) + HahnSeries.single (-2 : ℤ) (-2 : PowerSeries K) +
    HahnSeries.single (-1 : ℤ) (-1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k => PowerSeries.mk fun M =>
      if M = 0 then 0 else
        (∑ e ∈ M.divisors, ((e.choose 2 : K) * (e.choose k : K)
            - ((e + 1).choose 2 : K) * ((-1) ^ k * ((e + k - 1).choose k : K))))
          + (if k = 0 then ∑ e ∈ M.divisors, (e : K) else 0))

theorem coeff_tateOriginX_neg_two (K : Type*) [CommRing K] : (tateOriginX K).coeff (-2) = 1 := by
  rw [tateOriginX, HahnSeries.coeff_add, HahnSeries.coeff_add, ofPowerSeries_coeff_of_neg _ (by norm_num),
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_pos rfl, if_neg (by norm_num), add_zero, add_zero]

theorem coeff_tateOriginX_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -2) :
    (tateOriginX K).coeff n = 0 := by
  have h1 : n ≠ -2 := by omega
  have h2 : n ≠ -1 := by omega
  rw [tateOriginX, HahnSeries.coeff_add, HahnSeries.coeff_add, ofPowerSeries_coeff_of_neg _ (by omega),
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_neg h1, if_neg h2, add_zero, add_zero]

theorem coeff_tateOriginY_neg_three (K : Type*) [CommRing K] : (tateOriginY K).coeff (-3) = -1 := by
  rw [tateOriginY, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    ofPowerSeries_coeff_of_neg _ (by norm_num), HahnSeries.coeff_single, HahnSeries.coeff_single,
    HahnSeries.coeff_single, if_pos rfl, if_neg (by norm_num), if_neg (by norm_num), add_zero, add_zero, add_zero]

theorem coeff_tateOriginY_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -3) :
    (tateOriginY K).coeff n = 0 := by
  have h1 : n ≠ -3 := by omega
  have h2 : n ≠ -2 := by omega
  have h3 : n ≠ -1 := by omega
  rw [tateOriginY, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    ofPowerSeries_coeff_of_neg _ (by omega), HahnSeries.coeff_single, HahnSeries.coeff_single,
    HahnSeries.coeff_single, if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero, add_zero]

end ModularCurve

end


