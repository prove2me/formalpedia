-- Prove2me | Definitions.Def_WeierstrassCurve_FormalGroup
-- name    : WeierstrassCurve_FormalGroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/8f1af757-23ff-5317-a8cd-dab543b82e05
-- title:
--   Weierstrass formal group via generic points on the curve
-- statement:
--   Throughout, $R$ is a commutative integral domain and $W$ a Weierstrass curve over $R$; $W$.`formalW` denotes the unique $w \in R[[X]]$ with zero constant term satisfying $w = X^3 + a_1Xw + a_2X^2w + a_3w^2 + a_4Xw^2 + a_6w^3$. For a multivariate power series $t$ over $R$ in variables indexed by $\sigma$, `fgGenW` is the substitution $w(t)$ of $t$ into `formalW`. `GenK σ R` abbreviates the fraction field of `MvPowerSeries σ R` and `genι` the canonical map into it; `xGen t` and `yGen t` are $t/w(t)$ and $-1/w(t)$ in that field, the usual $(z/w, -1/w)$ coordinates, and `genW σ` is $W$ base-changed along $R \to$ `GenK σ R`. The statements `equation_genericPoint` and `nonsingular_genericPoint` show that this pair satisfies the affine Weierstrass equation, and is nonsingular when $W$ is elliptic, whenever $t$ is substitutable and $w(t)$ is nonzero; `genericPoint` packages the resulting element of the affine point group, and `genericPoint_injective` records that $t$ is recovered from it. `NoVar j x` asserts that every coefficient of $x$ at a multidegree with nonzero exponent in the variable $j$ vanishes.
--
--   The bulk of the module transports the chord–tangent law to the power-series side: `eq_subst_formalW` is the uniqueness characterisation of $w$, `kwB_Ra`, `kwB_Rb`, `kwB_Rc` express that the three parameters $a$, $b$ and the substituted `fgZ3Fixed` lie on the line with slope datum `fgSlope`, `fgNu`, and `obl1`, `obl_collin`, `obl2`, `genericPoint_sum`, `obl0` and `genericPoint_hom` identify substitution into `formalGroupLawFixed` with addition of generic points. From this follow associativity of `formalGroupLawFixed`, its packaging as a term of Mathlib's `FormalGroup R` under the name `formalGroup`, its commutativity, and the corresponding `IsComm` instance. A general substitution identity for a pair of variables, [`MvPowerSeries.subst_X_pair_eq_self`](../def/WeierstrassCurve_FormalGroup.html#L16), is proved as support.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve`, its affine points and addition, multivariate power-series substitution, and the `FormalGroup` structure; the series `formalW`, `fgZ3Fixed`, `fgInv` and `formalGroupLawFixed` and the generic-point apparatus (`fgGenW`, `GenK`, `xGen`, `yGen`, `genericPoint`, `NoVar`) are the project's own, and `formalGroup` instantiates Mathlib's `FormalGroup R` with the formal group law constructed here.
--
--   **Where it is used.** The formal group of a Weierstrass curve is the tool for local analysis of points of an elliptic curve near the identity, the kernel of reduction over a local field being the group of points of this formal group; it is used widely downstream in the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_FormalGroup.lean

import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Evaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

theorem subst_X_pair_eq_self (h : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.subst
      ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] h = h := by
  have hXX : MvPowerSeries.HasSubst
      (![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by fin_cases i <;> exact MvPowerSeries.constantCoeff_X _)
  ext d
  rw [MvPowerSeries.coeff_subst hXX]

  have hXeq : (![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R),
      MvPowerSeries.X 1]) = MvPowerSeries.X := by
    funext i; fin_cases i <;> rfl
  simp only [hXeq]
  have hprod : ∀ e : Fin 2 →₀ ℕ,
      (e.prod fun i k => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ k) =
      MvPowerSeries.monomial e (1 : R) := fun e => by
    have hde : e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hde]
    rw [Finsupp.prod_add_index (by intro i _; exact pow_zero _)
        (by intro i _ a b; exact pow_add _ a b)]
    rw [show (Finsupp.single (0 : Fin 2) (e 0)).prod
          (fun i k => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ k)
        = (MvPowerSeries.X 0) ^ (e 0) from Finsupp.prod_single_index (pow_zero _),
      show (Finsupp.single (1 : Fin 2) (e 1)).prod
          (fun i k => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ k)
        = (MvPowerSeries.X 1) ^ (e 1) from Finsupp.prod_single_index (pow_zero _),
      MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, one_mul, ← hde]
  rw [finsum_eq_single _ d]
  · rw [hprod, MvPowerSeries.coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro e he
    rw [hprod, MvPowerSeries.coeff_monomial, if_neg (Ne.symm he), smul_zero]

end MvPowerSeries

noncomputable section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
variable {σ : Type*}

noncomputable def fgGenW (t : MvPowerSeries σ R) : MvPowerSeries σ R :=
  PowerSeries.subst t W.formalW

abbrev GenK (σ : Type*) (R : Type*) [CommRing R] [IsDomain R] : Type _ :=
  FractionRing (MvPowerSeries σ R)

noncomputable abbrev genι : MvPowerSeries σ R →+* GenK σ R :=
  algebraMap (MvPowerSeries σ R) (FractionRing (MvPowerSeries σ R))

noncomputable def xGen (t : MvPowerSeries σ R) : GenK σ R :=
  genι t / genι (W.fgGenW t)

noncomputable def yGen (t : MvPowerSeries σ R) : GenK σ R :=
  -1 / genι (W.fgGenW t)

noncomputable def genW (σ : Type*) : WeierstrassCurve (GenK σ R) :=
  W.map (algebraMap R (GenK σ R))

theorem equation_genericPoint {t : MvPowerSeries σ R}
    (ht : PowerSeries.HasSubst t)
    (hw : genι (W.fgGenW t) ≠ 0) :
    (W.genW σ).toAffine.Equation (W.xGen t) (W.yGen t) := by

  have h := congrArg (PowerSeries.substAlgHom ht) W.formalW_eq
  simp only [map_add, map_mul, map_pow, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom] at h
  replace h := congrArg genι h
  simp only [map_add, map_mul, map_pow, PowerSeries.subst_C] at h

  have hC : ∀ a : R, genι (MvPowerSeries.C a) = algebraMap R (GenK σ R) a := by
    intro a
    rw [IsScalarTower.algebraMap_apply R (MvPowerSeries σ R) (GenK σ R) a]
    rfl
  simp only [hC] at h
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [genW, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  unfold xGen yGen
  field_simp [hw]

  rw [show PowerSeries.subst t W.formalW = W.fgGenW t from rfl] at h
  linear_combination h

theorem nonsingular_genericPoint [W.IsElliptic] {t : MvPowerSeries σ R}
    (ht : PowerSeries.HasSubst t) (hw : genι (W.fgGenW t) ≠ 0) :
    (W.genW σ).toAffine.Nonsingular (W.xGen t) (W.yGen t) := by
  haveI : (W.genW σ).IsElliptic := by
    unfold genW
    infer_instance
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mp (W.equation_genericPoint ht hw)

noncomputable def genericPoint [W.IsElliptic] {t : MvPowerSeries σ R}
    (ht : PowerSeries.HasSubst t) (hw : genι (W.fgGenW t) ≠ 0) :
    (W.genW σ).toAffine.Point :=
  .some (W.xGen t) (W.yGen t) (W.nonsingular_genericPoint ht hw)

theorem fgGenW_ne_zero [NoZeroDivisors (MvPowerSeries σ R)] {t : MvPowerSeries σ R}
    (ht : PowerSeries.HasSubst t) (htc : MvPowerSeries.constantCoeff t = 0) (ht_ne : t ≠ 0) :
    W.fgGenW t ≠ 0 := by
  obtain ⟨v, hv⟩ := W.X_pow_three_dvd_formalW
  have hfac : W.fgGenW t = t ^ 3 * PowerSeries.subst t v := by
    have e := congrArg (PowerSeries.substAlgHom ht) hv
    simpa [fgGenW, map_mul, map_pow, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom] using e
  have hv_const : MvPowerSeries.constantCoeff (PowerSeries.subst t v) = (1 : R) := by
    rw [PowerSeries.constantCoeff_subst ht,
      finsum_eq_single _ 0 (fun d hd => by rw [map_pow, htc, zero_pow hd, smul_zero])]
    rw [pow_zero, map_one, smul_eq_mul, mul_one]
    have h3 := W.coeff_formalW_three
    rw [hv] at h3
    have hcm : PowerSeries.coeff 3 (PowerSeries.X ^ 3 * v) = PowerSeries.coeff 0 v := by
      simpa using PowerSeries.coeff_X_pow_mul v 3 0
    rwa [hcm] at h3
  have hv_ne : PowerSeries.subst t v ≠ 0 := by
    intro hz; rw [hz, map_zero] at hv_const; exact one_ne_zero hv_const.symm
  rw [hfac]
  exact mul_ne_zero (pow_ne_zero 3 ht_ne) hv_ne

theorem genericPoint_injective [W.IsElliptic] {a b : MvPowerSeries σ R}
    (hta : PowerSeries.HasSubst a) (htb : PowerSeries.HasSubst b)
    (hwa : genι (W.fgGenW a) ≠ 0) (hwb : genι (W.fgGenW b) ≠ 0)
    (hab : W.genericPoint hta hwa = W.genericPoint htb hwb) : a = b := by
  have chart : ∀ {s : MvPowerSeries σ R}, genι (W.fgGenW s) ≠ 0 → genι s = - W.xGen s / W.yGen s := by
    intro s hs
    rw [xGen, yGen]
    field_simp
  unfold genericPoint at hab
  rw [WeierstrassCurve.Affine.Point.some.injEq] at hab
  have hgi : genι a = genι b := by rw [chart hwa, chart hwb, hab.1, hab.2]
  exact IsFractionRing.injective (MvPowerSeries σ R) (GenK σ R) hgi

end WeierstrassCurve

end

set_option maxHeartbeats 1000000

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

theorem eq_subst_formalW {σ : Type*} {c : MvPowerSeries σ R}
    (hc : MvPowerSeries.constantCoeff c = 0)
    {u : MvPowerSeries σ R} (hu : MvPowerSeries.constantCoeff u = 0)
    (heq : u = c ^ 3 + MvPowerSeries.C W.a₁ * c * u + MvPowerSeries.C W.a₂ * c ^ 2 * u
      + MvPowerSeries.C W.a₃ * u ^ 2 + MvPowerSeries.C W.a₄ * c * u ^ 2
      + MvPowerSeries.C W.a₆ * u ^ 3) :
    u = PowerSeries.subst c W.formalW := by
  have hcs : PowerSeries.HasSubst c := PowerSeries.HasSubst.of_constantCoeff_zero hc
  set v : MvPowerSeries σ R := PowerSeries.subst c W.formalW with hv

  have hveq : v = c ^ 3 + MvPowerSeries.C W.a₁ * c * v + MvPowerSeries.C W.a₂ * c ^ 2 * v
      + MvPowerSeries.C W.a₃ * v ^ 2 + MvPowerSeries.C W.a₄ * c * v ^ 2
      + MvPowerSeries.C W.a₆ * v ^ 3 := by
    have h := congrArg (PowerSeries.substAlgHom (R := R) hcs) W.formalW_eq
    simp only [map_add, map_mul, map_pow, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
    rw [hv]
    convert h using 2

  have hvc : MvPowerSeries.constantCoeff v = 0 := by
    rw [hv, PowerSeries.constantCoeff_subst hcs,
      finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hc, zero_pow hd, smul_zero])]
    rw [pow_zero, map_one, smul_eq_mul, mul_one, PowerSeries.coeff_zero_eq_constantCoeff,
      W.constantCoeff_formalW]

  set M : MvPowerSeries σ R :=
    MvPowerSeries.C W.a₁ * c + MvPowerSeries.C W.a₂ * c ^ 2 + MvPowerSeries.C W.a₃ * (u + v)
      + MvPowerSeries.C W.a₄ * c * (u + v) + MvPowerSeries.C W.a₆ * (u ^ 2 + u * v + v ^ 2)
    with hM
  have hMδ : (1 - M) * (u - v) = 0 := by rw [hM]; linear_combination heq - hveq
  have hMconst : MvPowerSeries.constantCoeff (1 - M) = 1 := by
    rw [hM]
    simp [map_sub, map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, hc, hu, hvc]
  have hunit : IsUnit (1 - M) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, hMconst]
    exact isUnit_one
  have hδ : u - v = 0 := (IsUnit.mul_right_eq_zero hunit).mp hMδ
  exact sub_eq_zero.mp hδ

theorem subst_pair_bridge {σ : Type*} {a b : MvPowerSeries σ R}
    (hab : MvPowerSeries.HasSubst ![a, b]) {g : MvPowerSeries (Fin 2) R}
    (hg : PowerSeries.HasSubst g) (h : PowerSeries R) :
    MvPowerSeries.subst ![a, b] (PowerSeries.subst g h)
      = PowerSeries.subst (MvPowerSeries.subst ![a, b] g) h := by
  show MvPowerSeries.subst ![a, b] (MvPowerSeries.subst (Function.const Unit g) h)
      = MvPowerSeries.subst (Function.const Unit (MvPowerSeries.subst ![a, b] g)) h
  exact congrFun (MvPowerSeries.subst_comp_subst (PowerSeries.hasSubst_iff.mp hg) hab) h

theorem kwB_hasSubst_pair {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  · simpa using ha
  · simpa using hb

theorem kwB_Ra {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    W.fgGenW a
      = MvPowerSeries.subst ![a, b] W.fgSlope * a + MvPowerSeries.subst ![a, b] W.fgNu := by
  have hab : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ R) := kwB_hasSubst_pair ha hb
  have hX0 : MvPowerSeries.subst ![a, b]
      (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) = a := by
    rw [MvPowerSeries.subst_X hab]; rfl
  have hfgW1 : MvPowerSeries.subst ![a, b] W.fgW₁ = W.fgGenW a := by
    simp only [fgW₁, fgGenW]
    rw [subst_pair_bridge hab
        (PowerSeries.HasSubst.of_constantCoeff_zero (by rw [MvPowerSeries.constantCoeff_X])), hX0]
  have hNu : MvPowerSeries.subst ![a, b] W.fgNu
      = W.fgGenW a - MvPowerSeries.subst ![a, b] W.fgSlope * a := by
    simp only [fgNu]
    rw [← MvPowerSeries.coe_substAlgHom hab, map_sub, map_mul,
        MvPowerSeries.coe_substAlgHom hab, hfgW1, hX0]
  rw [hNu]; ring

theorem coeff_subst_X_formalW (i : Fin 2) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) W.formalW)
      = if d = Finsupp.single i (d i) then PowerSeries.coeff (d i) W.formalW else 0 := by
  classical
  rw [PowerSeries.coeff_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (by rw [MvPowerSeries.constantCoeff_X]))]
  rw [finsum_eq_single _ (d i) (fun n hn => by
    rw [MvPowerSeries.coeff_X_pow, if_neg (fun h => hn ?_), smul_zero]
    have hdi := congrFun (congrArg DFunLike.coe h) i
    simpa [Finsupp.single_eq_same] using hdi.symm)]
  rw [MvPowerSeries.coeff_X_pow]
  by_cases h : d = Finsupp.single i (d i)
  · rw [if_pos h, if_pos h, smul_eq_mul, mul_one]
  · rw [if_neg h, if_neg h, smul_zero]

theorem formalW_divided_difference :
    W.fgSlope * (MvPowerSeries.X (1 : Fin 2) - MvPowerSeries.X (0 : Fin 2))
      = PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) W.formalW
        - W.fgW₁ := by
  classical
  ext d
  have hLHSi : ∀ i : Fin 2, MvPowerSeries.coeff d (W.fgSlope * MvPowerSeries.X i)
      = if (Finsupp.single i 1 : Fin 2 →₀ ℕ) ≤ d
        then PowerSeries.coeff (d 0 + d 1) W.formalW else 0 := by
    intro i
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial]
    by_cases hle : (Finsupp.single i 1 : Fin 2 →₀ ℕ) ≤ d
    · rw [if_pos hle, if_pos hle, W.coeff_fgSlope, mul_one]
      have hidx : (d - Finsupp.single i 1 : Fin 2 →₀ ℕ) 0
          + (d - Finsupp.single i 1 : Fin 2 →₀ ℕ) 1 + 1 = d 0 + d 1 := by
        rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
        have h0 : (Finsupp.single i 1) 0 ≤ d 0 := Finsupp.le_def.mp hle 0
        have h1 : (Finsupp.single i 1) 1 ≤ d 1 := Finsupp.le_def.mp hle 1
        have hs : (Finsupp.single i 1) 0 + (Finsupp.single i 1) 1 = 1 := by
          fin_cases i <;> simp
        omega
      rw [hidx]
    · rw [if_neg hle, if_neg hle]
  rw [mul_sub, map_sub, hLHSi 1, hLHSi 0, map_sub, fgW₁,
    W.coeff_subst_X_formalW 1, W.coeff_subst_X_formalW 0]
  have hs1 : ((Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≤ d) ↔ 1 ≤ d 1 := by
    rw [Finsupp.single_le_iff]
  have hs0 : ((Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≤ d) ↔ 1 ≤ d 0 := by
    rw [Finsupp.single_le_iff]
  have hd1 : (d = Finsupp.single 1 (d 1)) ↔ d 0 = 0 := by
    constructor
    · intro h; have := congrFun (congrArg DFunLike.coe h) 0
      simpa [Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] using this
    · intro h; ext j; fin_cases j <;>
        simp [h, Finsupp.single_eq_same]
  have hd0 : (d = Finsupp.single 0 (d 0)) ↔ d 1 = 0 := by
    constructor
    · intro h; have := congrFun (congrArg DFunLike.coe h) 1
      simpa [Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] using this
    · intro h; ext j; fin_cases j <;>
        simp [h, Finsupp.single_eq_same]
  rcases Nat.eq_zero_or_pos (d 0) with h0 | h0 <;> rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
  · rw [if_neg (by rw [hs1]; omega), if_neg (by rw [hs0]; omega),
      if_pos (hd1.mpr h0), if_pos (hd0.mpr h1), h0, h1]
    simp
  · rw [if_pos (by rw [hs1]; omega), if_neg (by rw [hs0]; omega),
      if_pos (hd1.mpr h0), if_neg (by rw [hd0]; omega), h0, zero_add, sub_zero]
  · rw [if_neg (by rw [hs1]; omega), if_pos (by rw [hs0]; omega),
      if_neg (by rw [hd1]; omega), if_pos (hd0.mpr h1), h1, add_zero, zero_sub]
  · rw [if_pos (by rw [hs1]; omega), if_pos (by rw [hs0]; omega),
      if_neg (by rw [hd1]; omega), if_neg (by rw [hd0]; omega), sub_self, sub_zero]

theorem kwB_Rb {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    W.fgGenW b
      = MvPowerSeries.subst ![a, b] W.fgSlope * b + MvPowerSeries.subst ![a, b] W.fgNu := by
  have hab : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ R) := kwB_hasSubst_pair ha hb
  have hX0 : MvPowerSeries.subst ![a, b]
      (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) = a := by
    rw [MvPowerSeries.subst_X hab]; rfl
  have hX1 : MvPowerSeries.subst ![a, b]
      (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) = b := by
    rw [MvPowerSeries.subst_X hab]; rfl
  have hsX0 : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [MvPowerSeries.constantCoeff_X])
  have hsX1 : PowerSeries.HasSubst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [MvPowerSeries.constantCoeff_X])
  have hGb : MvPowerSeries.subst ![a, b]
      (PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) W.formalW)
      = W.fgGenW b := by
    simp only [fgGenW]; rw [subst_pair_bridge hab hsX1, hX1]
  have hGa : MvPowerSeries.subst ![a, b] W.fgW₁ = W.fgGenW a := by
    simp only [fgW₁, fgGenW]; rw [subst_pair_bridge hab hsX0, hX0]
  have hdd := congrArg (MvPowerSeries.subst ![a, b]) W.formalW_divided_difference
  rw [← MvPowerSeries.coe_substAlgHom hab, map_mul, map_sub, map_sub,
      MvPowerSeries.coe_substAlgHom hab, hX1, hX0, hGb, hGa] at hdd
  have hRa := W.kwB_Ra ha hb
  linear_combination hRa - hdd

theorem kwB_constantCoeff_subst_pair {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0)
    {g : MvPowerSeries (Fin 2) R} (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![a, b] g) = 0 := by
  have hab : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ R) := kwB_hasSubst_pair ha hb
  have hv0 : ∀ s : Fin 2, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → MvPowerSeries σ R) s) = 0 := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, ha, hb]
  rw [MvPowerSeries.constantCoeff_subst hab]
  have hterm : ∀ d : Fin 2 →₀ ℕ,
      (MvPowerSeries.coeff d) g • MvPowerSeries.constantCoeff (d.prod fun s e => (![a, b] : Fin 2 → MvPowerSeries σ R) s ^ e) = 0 := by
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [Finsupp.prod_zero_index, map_one, smul_eq_mul, mul_one,
        MvPowerSeries.coeff_zero_eq_constantCoeff, hg]
    · have hprod : MvPowerSeries.constantCoeff (d.prod fun s e => (![a, b] : Fin 2 → MvPowerSeries σ R) s ^ e) = 0 := by
        rw [Finsupp.prod, map_prod]
        obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
        apply Finset.prod_eq_zero hs
        rw [map_pow, hv0 s, zero_pow (Finsupp.mem_support_iff.mp hs)]
      rw [hprod, smul_zero]
  rw [finsum_congr hterm, finsum_zero]

theorem kwB_Rc {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0)
    (hne : a ≠ b) :
    W.fgGenW (MvPowerSeries.subst ![a, b] W.fgZ3Fixed)
      = MvPowerSeries.subst ![a, b] W.fgSlope * MvPowerSeries.subst ![a, b] W.fgZ3Fixed
        + MvPowerSeries.subst ![a, b] W.fgNu := by
  have hab : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ R) := kwB_hasSubst_pair ha hb
  have hsa : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hsb : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero hb
  have hs1 : MvPowerSeries.subst ![a, b] (1 : MvPowerSeries (Fin 2) R) = 1 := by
    rw [← MvPowerSeries.coe_substAlgHom hab, map_one]
  have hs2 : MvPowerSeries.subst ![a, b] (2 : MvPowerSeries (Fin 2) R) = 2 := by
    rw [← MvPowerSeries.coe_substAlgHom hab, map_ofNat]
  have hs3 : MvPowerSeries.subst ![a, b] (3 : MvPowerSeries (Fin 2) R) = 3 := by
    rw [← MvPowerSeries.coe_substAlgHom hab, map_ofNat]
  have hsneg : ∀ x : MvPowerSeries (Fin 2) R,
      MvPowerSeries.subst ![a, b] (-x) = -(MvPowerSeries.subst ![a, b] x) := fun x => by
    rw [← MvPowerSeries.coe_substAlgHom hab, map_neg, MvPowerSeries.coe_substAlgHom]

  have heqa : W.fgGenW a = a ^ 3 + MvPowerSeries.C W.a₁ * a * W.fgGenW a
      + MvPowerSeries.C W.a₂ * a ^ 2 * W.fgGenW a + MvPowerSeries.C W.a₃ * W.fgGenW a ^ 2
      + MvPowerSeries.C W.a₄ * a * W.fgGenW a ^ 2 + MvPowerSeries.C W.a₆ * W.fgGenW a ^ 3 := by
    have h := congrArg (PowerSeries.substAlgHom (R := R) hsa) W.formalW_eq
    simp only [map_add, map_mul, map_pow, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
    simp only [fgGenW]; convert h using 2
  have heqb : W.fgGenW b = b ^ 3 + MvPowerSeries.C W.a₁ * b * W.fgGenW b
      + MvPowerSeries.C W.a₂ * b ^ 2 * W.fgGenW b + MvPowerSeries.C W.a₃ * W.fgGenW b ^ 2
      + MvPowerSeries.C W.a₄ * b * W.fgGenW b ^ 2 + MvPowerSeries.C W.a₆ * W.fgGenW b ^ 3 := by
    have h := congrArg (PowerSeries.substAlgHom (R := R) hsb) W.formalW_eq
    simp only [map_add, map_mul, map_pow, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
    simp only [fgGenW]; convert h using 2
  rw [W.kwB_Ra ha hb] at heqa
  rw [W.kwB_Rb ha hb] at heqb
  have hcc : MvPowerSeries.constantCoeff (MvPowerSeries.subst ![a, b] W.fgZ3Fixed) = 0 :=
    kwB_constantCoeff_subst_pair ha hb W.constantCoeff_fgZ3Fixed
  have hSc : MvPowerSeries.constantCoeff (MvPowerSeries.subst ![a, b] W.fgSlope) = 0 :=
    kwB_constantCoeff_subst_pair ha hb W.constantCoeff_fgSlope
  have hNuc : MvPowerSeries.constantCoeff (MvPowerSeries.subst ![a, b] W.fgNu) = 0 :=
    kwB_constantCoeff_subst_pair ha hb W.constantCoeff_fgNu

  have hD1 : MvPowerSeries.constantCoeff (σ := Fin 2) W.fgZ3Denom = 1 := by
    simp only [fgZ3Denom, map_add, map_one, map_mul, map_pow, MvPowerSeries.constantCoeff_C,
      W.constantCoeff_fgSlope]; ring
  have hDiD : MvPowerSeries.subst ![a, b] W.fgZ3Denom
      * MvPowerSeries.subst ![a, b] (MvPowerSeries.invOfUnit W.fgZ3Denom 1) = 1 := by
    rw [← MvPowerSeries.coe_substAlgHom hab, ← map_mul,
      MvPowerSeries.mul_invOfUnit W.fgZ3Denom 1 (by rw [hD1]; rfl), map_one]
  have hcexp : MvPowerSeries.subst ![a, b] W.fgZ3Fixed
      = -a - b + MvPowerSeries.subst ![a, b] W.fgZ3NumFixed
          * MvPowerSeries.subst ![a, b] (MvPowerSeries.invOfUnit W.fgZ3Denom 1) := by
    rw [fgZ3Fixed, ← MvPowerSeries.coe_substAlgHom hab]
    simp only [map_add, map_sub, map_neg, map_mul, MvPowerSeries.coe_substAlgHom,
      MvPowerSeries.subst_X hab, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hc : MvPowerSeries.subst ![a, b] W.fgZ3Denom
      * (MvPowerSeries.subst ![a, b] W.fgZ3Fixed + a + b)
      = MvPowerSeries.subst ![a, b] W.fgZ3NumFixed := by
    rw [hcexp]; linear_combination (MvPowerSeries.subst ![a, b] W.fgZ3NumFixed) * hDiD
  set c := MvPowerSeries.subst ![a, b] W.fgZ3Fixed with hcdef
  set S := MvPowerSeries.subst ![a, b] W.fgSlope with hSdef
  set Nu := MvPowerSeries.subst ![a, b] W.fgNu with hNudef

  have hDexp : MvPowerSeries.subst ![a, b] W.fgZ3Denom
      = 1 + MvPowerSeries.C W.a₂ * S + MvPowerSeries.C W.a₄ * S ^ 2
        + MvPowerSeries.C W.a₆ * S ^ 3 := by
    rw [hSdef, fgZ3Denom]
    simp only [MvPowerSeries.subst_add hab, MvPowerSeries.subst_mul hab,
      MvPowerSeries.subst_pow hab, MvPowerSeries.subst_C, hs1]
  have hNexp : MvPowerSeries.subst ![a, b] W.fgZ3NumFixed
      = -(MvPowerSeries.C W.a₁ * S + MvPowerSeries.C W.a₃ * S ^ 2 + MvPowerSeries.C W.a₂ * Nu
        + 2 * MvPowerSeries.C W.a₄ * (S * Nu) + 3 * MvPowerSeries.C W.a₆ * (S ^ 2 * Nu)) := by
    rw [hSdef, hNudef, fgZ3NumFixed]
    simp only [hsneg, MvPowerSeries.subst_add hab, MvPowerSeries.subst_mul hab,
      MvPowerSeries.subst_pow hab, MvPowerSeries.subst_C, hs2, hs3, map_mul, map_ofNat]
  rw [hDexp, hNexp] at hc

  have hQ : (1 + MvPowerSeries.C W.a₂ * S + MvPowerSeries.C W.a₄ * S ^ 2
          + MvPowerSeries.C W.a₆ * S ^ 3) * (a ^ 2 + a * b + b ^ 2)
        + (MvPowerSeries.C W.a₁ * S + MvPowerSeries.C W.a₂ * Nu + MvPowerSeries.C W.a₃ * S ^ 2
          + 2 * MvPowerSeries.C W.a₄ * (S * Nu) + 3 * MvPowerSeries.C W.a₆ * (S ^ 2 * Nu)) * (a + b)
        + (MvPowerSeries.C W.a₁ * Nu + 2 * MvPowerSeries.C W.a₃ * (S * Nu)
          + MvPowerSeries.C W.a₄ * Nu ^ 2 + 3 * MvPowerSeries.C W.a₆ * (Nu ^ 2 * S) - S) = 0 := by
    have hd : (a - b) * ((1 + MvPowerSeries.C W.a₂ * S + MvPowerSeries.C W.a₄ * S ^ 2
          + MvPowerSeries.C W.a₆ * S ^ 3) * (a ^ 2 + a * b + b ^ 2)
        + (MvPowerSeries.C W.a₁ * S + MvPowerSeries.C W.a₂ * Nu + MvPowerSeries.C W.a₃ * S ^ 2
          + 2 * MvPowerSeries.C W.a₄ * (S * Nu) + 3 * MvPowerSeries.C W.a₆ * (S ^ 2 * Nu)) * (a + b)
        + (MvPowerSeries.C W.a₁ * Nu + 2 * MvPowerSeries.C W.a₃ * (S * Nu)
          + MvPowerSeries.C W.a₄ * Nu ^ 2 + 3 * MvPowerSeries.C W.a₆ * (Nu ^ 2 * S) - S)) = 0 := by
      linear_combination heqb - heqa
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hu : MvPowerSeries.constantCoeff (S * c + Nu) = 0 := by
    rw [map_add, map_mul, hSc, hcc, hNuc]; ring
  have hP : S * c + Nu = c ^ 3 + MvPowerSeries.C W.a₁ * c * (S * c + Nu)
      + MvPowerSeries.C W.a₂ * c ^ 2 * (S * c + Nu) + MvPowerSeries.C W.a₃ * (S * c + Nu) ^ 2
      + MvPowerSeries.C W.a₄ * c * (S * c + Nu) ^ 2 + MvPowerSeries.C W.a₆ * (S * c + Nu) ^ 3 := by
    linear_combination heqa - (c - a) * hQ - (c - a) * (c - b) * hc
  have hfix := W.eq_subst_formalW hcc hu hP
  simp only [fgGenW]
  exact hfix.symm

set_option maxRecDepth 100000 in
open Classical in

theorem obl1 {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (hne : a ≠ b)
    (hwa : genι (W.fgGenW a) ≠ 0) (hwb : genι (W.fgGenW b) ≠ 0)
    (hwc : genι (W.fgGenW (MvPowerSeries.subst ![a, b] W.fgZ3Fixed)) ≠ 0)
    (hx : W.xGen a ≠ W.xGen b) :
    W.xGen (MvPowerSeries.subst ![a, b] W.fgZ3Fixed)
      = (W.genW σ).toAffine.addX (W.xGen a) (W.xGen b)
          ((W.genW σ).toAffine.slope (W.xGen a) (W.xGen b) (W.yGen a) (W.yGen b)) := by
  classical
  have hWa := congrArg genι (W.kwB_Ra ha hb)
  have hWb := congrArg genι (W.kwB_Rb ha hb)
  have hWc := congrArg genι (W.kwB_Rc ha hb hne)
  simp only [map_add, map_mul] at hWa hWb hWc
  have hAB : genι a ≠ genι b := fun h => hx (by simp only [xGen, hWa, hWb, h])
  set ℓ := (W.genW σ).toAffine.slope (W.xGen a) (W.xGen b) (W.yGen a) (W.yGen b) with hℓdef

  have hLNu : ℓ * genι (MvPowerSeries.subst ![a, b] W.fgNu)
      = genι (MvPowerSeries.subst ![a, b] W.fgSlope) := by
    have h : ℓ = (W.yGen a - W.yGen b) / (W.xGen a - W.xGen b) := by
      rw [hℓdef]; exact WeierstrassCurve.Affine.slope_of_X_ne hx
    rw [eq_div_iff (sub_ne_zero.mpr hx)] at h
    simp only [xGen, yGen] at h
    field_simp [hwa, hwb] at h
    simp only [hWa, hWb] at h
    apply mul_right_cancel₀ (sub_ne_zero.mpr hAB)
    linear_combination h

  have hPa := W.equation_genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero ha) hwa
  have hPb := W.equation_genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero hb) hwb
  have hPc := W.equation_genericPoint
    (PowerSeries.HasSubst.of_constantCoeff_zero
      (kwB_constantCoeff_subst_pair ha hb W.constantCoeff_fgZ3Fixed)) hwc
  rw [WeierstrassCurve.Affine.equation_iff] at hPa hPb hPc
  simp only [genW, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, xGen, yGen] at hPa hPb hPc
  field_simp [hwa] at hPa
  field_simp [hwb] at hPb
  field_simp [hwc] at hPc
  simp only [hWa] at hPa
  simp only [hWb] at hPb
  simp only [hWc] at hPc
  rw [← hLNu] at hPa hPb hPc

  have hab : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ R) := kwB_hasSubst_pair ha hb
  have hs1 : MvPowerSeries.subst ![a, b] (1 : MvPowerSeries (Fin 2) R) = 1 := by
    rw [← MvPowerSeries.coe_substAlgHom hab, map_one]
  have hs2 : MvPowerSeries.subst ![a, b] (2 : MvPowerSeries (Fin 2) R) = 2 := by
    rw [← MvPowerSeries.coe_substAlgHom hab, map_ofNat]
  have hs3 : MvPowerSeries.subst ![a, b] (3 : MvPowerSeries (Fin 2) R) = 3 := by
    rw [← MvPowerSeries.coe_substAlgHom hab, map_ofNat]
  have hsneg : ∀ x : MvPowerSeries (Fin 2) R,
      MvPowerSeries.subst ![a, b] (-x) = -(MvPowerSeries.subst ![a, b] x) := fun x => by
    rw [← MvPowerSeries.coe_substAlgHom hab, map_neg, MvPowerSeries.coe_substAlgHom]
  have hCalg : ∀ r : R, genι (MvPowerSeries.C r : MvPowerSeries σ R)
      = algebraMap R (GenK σ R) r := fun r => by
    rw [IsScalarTower.algebraMap_apply R (MvPowerSeries σ R) (GenK σ R) r]; rfl
  have hD1 : MvPowerSeries.constantCoeff (σ := Fin 2) W.fgZ3Denom = 1 := by
    simp only [fgZ3Denom, map_add, map_one, map_mul, map_pow, MvPowerSeries.constantCoeff_C,
      W.constantCoeff_fgSlope]; ring

  set nu := genι (MvPowerSeries.subst ![a, b] W.fgNu) with hnudef
  set Aa := genι a with hAadef
  set Bb := genι b with hBbdef
  set Cc := genι (MvPowerSeries.subst ![a, b] W.fgZ3Fixed) with hCcdef
  set Dx := 1 + algebraMap R (GenK σ R) W.a₂ * ℓ * nu
      + algebraMap R (GenK σ R) W.a₄ * ℓ ^ 2 * nu ^ 2
      + algebraMap R (GenK σ R) W.a₆ * ℓ ^ 3 * nu ^ 3 with hDxdef
  set Nx := -(algebraMap R (GenK σ R) W.a₂ * nu + algebraMap R (GenK σ R) W.a₁ * ℓ * nu
      + algebraMap R (GenK σ R) W.a₃ * ℓ ^ 2 * nu ^ 2 + 2 * algebraMap R (GenK σ R) W.a₄ * ℓ * nu ^ 2
      + 3 * algebraMap R (GenK σ R) W.a₆ * ℓ ^ 2 * nu ^ 3) with hNxdef
  set C1x := algebraMap R (GenK σ R) W.a₁ * nu + algebraMap R (GenK σ R) W.a₄ * nu ^ 2
      + 2 * algebraMap R (GenK σ R) W.a₃ * ℓ * nu ^ 2 + 3 * algebraMap R (GenK σ R) W.a₆ * ℓ * nu ^ 3
      - ℓ * nu with hC1xdef
  set C0x := algebraMap R (GenK σ R) W.a₃ * nu ^ 2 + algebraMap R (GenK σ R) W.a₆ * nu ^ 3 - nu
    with hC0xdef

  have hDx : genι (MvPowerSeries.subst ![a, b] W.fgZ3Denom) = Dx := by
    have e : MvPowerSeries.subst ![a, b] W.fgZ3Denom
        = 1 + MvPowerSeries.C W.a₂ * MvPowerSeries.subst ![a, b] W.fgSlope
          + MvPowerSeries.C W.a₄ * (MvPowerSeries.subst ![a, b] W.fgSlope) ^ 2
          + MvPowerSeries.C W.a₆ * (MvPowerSeries.subst ![a, b] W.fgSlope) ^ 3 := by
      rw [fgZ3Denom]
      simp only [MvPowerSeries.subst_add hab, MvPowerSeries.subst_mul hab,
        MvPowerSeries.subst_pow hab, MvPowerSeries.subst_C, hs1]
    rw [e, hDxdef]
    simp only [map_add, map_one, map_mul, map_pow, hCalg]
    rw [← hLNu]; ring
  have hNx : genι (MvPowerSeries.subst ![a, b] W.fgZ3NumFixed) = Nx := by
    have e : MvPowerSeries.subst ![a, b] W.fgZ3NumFixed
        = -(MvPowerSeries.C W.a₁ * MvPowerSeries.subst ![a, b] W.fgSlope
          + MvPowerSeries.C W.a₃ * (MvPowerSeries.subst ![a, b] W.fgSlope) ^ 2
          + MvPowerSeries.C W.a₂ * MvPowerSeries.subst ![a, b] W.fgNu
          + 2 * MvPowerSeries.C W.a₄ * (MvPowerSeries.subst ![a, b] W.fgSlope
              * MvPowerSeries.subst ![a, b] W.fgNu)
          + 3 * MvPowerSeries.C W.a₆ * ((MvPowerSeries.subst ![a, b] W.fgSlope) ^ 2
              * MvPowerSeries.subst ![a, b] W.fgNu)) := by
      rw [fgZ3NumFixed]
      simp only [hsneg, MvPowerSeries.subst_add hab, MvPowerSeries.subst_mul hab,
        MvPowerSeries.subst_pow hab, MvPowerSeries.subst_C, hs2, hs3, map_mul, map_ofNat]
    rw [e, hNxdef]
    simp only [map_neg, map_add, map_mul, map_pow, hCalg, map_ofNat]
    rw [← hLNu]; ring

  have hDiD : MvPowerSeries.subst ![a, b] W.fgZ3Denom
      * MvPowerSeries.subst ![a, b] (MvPowerSeries.invOfUnit W.fgZ3Denom 1) = 1 := by
    rw [← MvPowerSeries.coe_substAlgHom hab, ← map_mul,
      MvPowerSeries.mul_invOfUnit W.fgZ3Denom 1 (by rw [hD1]; rfl), map_one]
  have hcexp : MvPowerSeries.subst ![a, b] W.fgZ3Fixed
      = -a - b + MvPowerSeries.subst ![a, b] W.fgZ3NumFixed
          * MvPowerSeries.subst ![a, b] (MvPowerSeries.invOfUnit W.fgZ3Denom 1) := by
    rw [fgZ3Fixed, ← MvPowerSeries.coe_substAlgHom hab]
    simp only [map_add, map_sub, map_neg, map_mul, MvPowerSeries.coe_substAlgHom,
      MvPowerSeries.subst_X hab, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hc_mv : MvPowerSeries.subst ![a, b] W.fgZ3Denom
      * (MvPowerSeries.subst ![a, b] W.fgZ3Fixed + a + b)
      = MvPowerSeries.subst ![a, b] W.fgZ3NumFixed := by
    rw [hcexp]; linear_combination (MvPowerSeries.subst ![a, b] W.fgZ3NumFixed) * hDiD
  have hc : Dx * (Aa + Bb + Cc) = Nx := by
    have hcg := congrArg genι hc_mv
    simp only [map_mul, map_add, hDx, hNx] at hcg
    linear_combination hcg

  have hQ : Dx * (Aa ^ 2 + Aa * Bb + Bb ^ 2) + (-Nx) * (Aa + Bb) + C1x = 0 := by
    have hd : (Aa - Bb) * (Dx * (Aa ^ 2 + Aa * Bb + Bb ^ 2) + (-Nx) * (Aa + Bb) + C1x) = 0 := by
      linear_combination hPb - hPa
    exact (mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hAB)
  have hDne : MvPowerSeries.subst ![a, b] W.fgZ3Denom ≠ 0 := fun h => by
    rw [h, zero_mul] at hDiD; exact zero_ne_one hDiD
  have hD : Dx ≠ 0 := by
    rw [← hDx]
    exact fun h => hDne ((map_eq_zero_iff genι
      (IsFractionRing.injective (MvPowerSeries σ R) (GenK σ R))).mp h)
  rw [hDxdef, hNxdef] at hc
  rw [hDxdef, hNxdef, hC1xdef] at hQ
  rw [hDxdef] at hD

  have hE2 : (1 + algebraMap R (GenK σ R) W.a₂ * ℓ * nu
        + algebraMap R (GenK σ R) W.a₄ * ℓ ^ 2 * nu ^ 2
        + algebraMap R (GenK σ R) W.a₆ * ℓ ^ 3 * nu ^ 3) * (Aa * Bb + Bb * Cc + Cc * Aa)
      = algebraMap R (GenK σ R) W.a₁ * nu + algebraMap R (GenK σ R) W.a₄ * nu ^ 2
        + 2 * algebraMap R (GenK σ R) W.a₃ * ℓ * nu ^ 2
        + 3 * algebraMap R (GenK σ R) W.a₆ * ℓ * nu ^ 3 - ℓ * nu := by
    linear_combination (Aa + Bb) * hc - hQ

  have hcubC : (1 + algebraMap R (GenK σ R) W.a₂ * ℓ * nu
        + algebraMap R (GenK σ R) W.a₄ * ℓ ^ 2 * nu ^ 2
        + algebraMap R (GenK σ R) W.a₆ * ℓ ^ 3 * nu ^ 3) * Cc ^ 3
      - (-(algebraMap R (GenK σ R) W.a₂ * nu + algebraMap R (GenK σ R) W.a₁ * ℓ * nu
        + algebraMap R (GenK σ R) W.a₃ * ℓ ^ 2 * nu ^ 2
        + 2 * algebraMap R (GenK σ R) W.a₄ * ℓ * nu ^ 2
        + 3 * algebraMap R (GenK σ R) W.a₆ * ℓ ^ 2 * nu ^ 3)) * Cc ^ 2
      + (algebraMap R (GenK σ R) W.a₁ * nu + algebraMap R (GenK σ R) W.a₄ * nu ^ 2
        + 2 * algebraMap R (GenK σ R) W.a₃ * ℓ * nu ^ 2
        + 3 * algebraMap R (GenK σ R) W.a₆ * ℓ * nu ^ 3 - ℓ * nu) * Cc
      + (algebraMap R (GenK σ R) W.a₃ * nu ^ 2 + algebraMap R (GenK σ R) W.a₆ * nu ^ 3 - nu) = 0 := by
    linear_combination -hPc
  have hE3 : (1 + algebraMap R (GenK σ R) W.a₂ * ℓ * nu
        + algebraMap R (GenK σ R) W.a₄ * ℓ ^ 2 * nu ^ 2
        + algebraMap R (GenK σ R) W.a₆ * ℓ ^ 3 * nu ^ 3) * (Aa * Bb * Cc)
      = -(algebraMap R (GenK σ R) W.a₃ * nu ^ 2 + algebraMap R (GenK σ R) W.a₆ * nu ^ 3 - nu) := by
    linear_combination hcubC - Cc ^ 2 * hc + Cc * hE2

  rw [WeierstrassCurve.Affine.addX]
  simp only [genW, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, xGen]
  field_simp [hwa, hwb, hwc]
  simp only [hWa, hWb, hWc]
  rw [← hLNu]
  apply mul_left_cancel₀ hD
  linear_combination
      (nu ^ 2 - ℓ * (ℓ ^ 2 + algebraMap R (GenK σ R) W.a₁ * ℓ - algebraMap R (GenK σ R) W.a₂) * nu ^ 3) * hc
    + (2 * ℓ * nu ^ 2 - ℓ ^ 2 * (ℓ ^ 2 + algebraMap R (GenK σ R) W.a₁ * ℓ - algebraMap R (GenK σ R) W.a₂) * nu ^ 3) * hE2
    + (3 * ℓ ^ 2 * nu ^ 2 - ℓ ^ 3 * (ℓ ^ 2 + algebraMap R (GenK σ R) W.a₁ * ℓ - algebraMap R (GenK σ R) W.a₂) * nu ^ 3) * hE3

open Classical in

theorem obl_collin {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (hne : a ≠ b)
    (hwa : genι (W.fgGenW a) ≠ 0) (hwb : genι (W.fgGenW b) ≠ 0)
    (hwc : genι (W.fgGenW (MvPowerSeries.subst ![a, b] W.fgZ3Fixed)) ≠ 0)
    (hx : W.xGen a ≠ W.xGen b) :
    W.yGen (MvPowerSeries.subst ![a, b] W.fgZ3Fixed) - W.yGen a
      = (W.genW σ).toAffine.slope (W.xGen a) (W.xGen b) (W.yGen a) (W.yGen b)
          * (W.xGen (MvPowerSeries.subst ![a, b] W.fgZ3Fixed) - W.xGen a) := by
  classical
  have hWa := congrArg genι (W.kwB_Ra ha hb)
  have hWb := congrArg genι (W.kwB_Rb ha hb)
  have hWc := congrArg genι (W.kwB_Rc ha hb hne)
  simp only [map_add, map_mul] at hWa hWb hWc
  have hAB : genι a ≠ genι b := fun h => hx (by simp only [xGen, hWa, hWb, h])
  set ℓ := (W.genW σ).toAffine.slope (W.xGen a) (W.xGen b) (W.yGen a) (W.yGen b) with hℓdef
  have hLNu : ℓ * genι (MvPowerSeries.subst ![a, b] W.fgNu)
      = genι (MvPowerSeries.subst ![a, b] W.fgSlope) := by
    have h : ℓ = (W.yGen a - W.yGen b) / (W.xGen a - W.xGen b) := by
      rw [hℓdef]; exact WeierstrassCurve.Affine.slope_of_X_ne hx
    rw [eq_div_iff (sub_ne_zero.mpr hx)] at h
    simp only [xGen, yGen] at h
    field_simp [hwa, hwb] at h
    simp only [hWa, hWb] at h
    apply mul_right_cancel₀ (sub_ne_zero.mpr hAB)
    linear_combination h
  simp only [xGen, yGen]
  field_simp [hwa, hwc]
  simp only [hWa, hWc]
  rw [← hLNu]
  ring

open Classical in

theorem obl2 {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (hne : a ≠ b)
    (hwa : genι (W.fgGenW a) ≠ 0) (hwb : genι (W.fgGenW b) ≠ 0)
    (hwc : genι (W.fgGenW (MvPowerSeries.subst ![a, b] W.fgZ3Fixed)) ≠ 0)
    (hx : W.xGen a ≠ W.xGen b) :
    (W.genW σ).toAffine.negY (W.xGen (MvPowerSeries.subst ![a, b] W.fgZ3Fixed))
        (W.yGen (MvPowerSeries.subst ![a, b] W.fgZ3Fixed))
      = (W.genW σ).toAffine.addY (W.xGen a) (W.xGen b) (W.yGen a)
          ((W.genW σ).toAffine.slope (W.xGen a) (W.xGen b) (W.yGen a) (W.yGen b)) := by
  have h1 := W.obl1 ha hb hne hwa hwb hwc hx
  have h2 := W.obl_collin ha hb hne hwa hwb hwc hx
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]
  rw [← h1]
  linear_combination -h2

open Classical in

theorem genericPoint_sum [W.IsElliptic] {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (hne : a ≠ b)
    (hwa : genι (W.fgGenW a) ≠ 0) (hwb : genι (W.fgGenW b) ≠ 0)
    (hwc : genι (W.fgGenW (MvPowerSeries.subst ![a, b] W.fgZ3Fixed)) ≠ 0)
    (hx : W.xGen a ≠ W.xGen b) :
    W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero ha) hwa
        + W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero hb) hwb
      = - W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero
          (kwB_constantCoeff_subst_pair ha hb W.constantCoeff_fgZ3Fixed)) hwc := by
  have hxy : ¬(W.xGen a = W.xGen b ∧
      W.yGen a = (W.genW σ).toAffine.negY (W.xGen b) (W.yGen b)) := fun h => hx h.1
  simp only [genericPoint]
  rw [WeierstrassCurve.Affine.Point.add_some hxy, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨(W.obl1 ha hb hne hwa hwb hwc hx).symm, (W.obl2 ha hb hne hwa hwb hwc hx).symm⟩

theorem subst_formalGroupLawFixed_eq {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst ![a, b] W.formalGroupLawFixed
      = PowerSeries.subst (MvPowerSeries.subst ![a, b] W.fgZ3Fixed) W.fgInv := by
  unfold WeierstrassCurve.formalGroupLawFixed
  exact subst_pair_bridge (kwB_hasSubst_pair ha hb) W.hasSubst_fgZ3Fixed W.fgInv

theorem fgInv_mul_fgInvDenom : W.fgInv * W.fgInvDenom = - PowerSeries.X := by
  have hcc : PowerSeries.constantCoeff W.fgInvDenom = 1 := by
    simp only [fgInvDenom, map_sub, map_mul, map_one, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, W.constantCoeff_formalW, mul_zero, sub_zero]
  have hu : W.fgInvDenom * PowerSeries.invOfUnit W.fgInvDenom 1 = 1 :=
    PowerSeries.mul_invOfUnit W.fgInvDenom 1 (by rw [hcc]; simp)
  rw [show W.fgInv = -PowerSeries.X * PowerSeries.invOfUnit W.fgInvDenom 1 from rfl,
    mul_assoc, mul_comm (PowerSeries.invOfUnit W.fgInvDenom 1) W.fgInvDenom, hu, mul_one]

theorem constantCoeff_subst_fgInv {σ : Type*} {c' : MvPowerSeries σ R}
    (hc' : MvPowerSeries.constantCoeff c' = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst c' W.fgInv) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hc'),
    finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hc', zero_pow hd, smul_zero])]
  rw [pow_zero, map_one, smul_eq_mul, mul_one, PowerSeries.coeff_zero_eq_constantCoeff,
    W.constantCoeff_fgInv]

theorem genericPoint_congr [W.IsElliptic] {σ : Type*} {s t : MvPowerSeries σ R}
    (hs : PowerSeries.HasSubst s) (hws : genι (W.fgGenW s) ≠ 0)
    (ht : PowerSeries.HasSubst t) (hwt : genι (W.fgGenW t) ≠ 0)
    (hst : s = t) :
    W.genericPoint hs hws = W.genericPoint ht hwt := by
  subst hst; rfl

open Classical in

theorem obl0 [W.IsElliptic] {σ : Type*} {c' : MvPowerSeries σ R}
    (hc' : MvPowerSeries.constantCoeff c' = 0)
    (hwc' : genι (W.fgGenW c') ≠ 0)
    (hwic' : genι (W.fgGenW (PowerSeries.subst c' W.fgInv)) ≠ 0) :
    W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero (W.constantCoeff_subst_fgInv hc'))
        hwic'
      = - W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero hc') hwc' := by
  classical
  have hc's : PowerSeries.HasSubst c' := PowerSeries.HasSubst.of_constantCoeff_zero hc'
  have hCalg : ∀ r : R, genι (MvPowerSeries.C r : MvPowerSeries σ R)
      = algebraMap R (GenK σ R) r := fun r => by
    rw [IsScalarTower.algebraMap_apply R (MvPowerSeries σ R) (GenK σ R) r]; rfl
  set ic' := PowerSeries.subst c' W.fgInv with hicdef
  set w := W.fgGenW c' with hwdef
  have hccw : MvPowerSeries.constantCoeff w = 0 := by
    rw [hwdef, fgGenW, PowerSeries.constantCoeff_subst hc's,
      finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hc', zero_pow hd, smul_zero])]
    rw [pow_zero, map_one, smul_eq_mul, mul_one, PowerSeries.coeff_zero_eq_constantCoeff,
      W.constantCoeff_formalW]
  have hccic : MvPowerSeries.constantCoeff ic' = 0 := W.constantCoeff_subst_fgInv hc'

  have heq_c : w = c' ^ 3 + MvPowerSeries.C W.a₁ * c' * w + MvPowerSeries.C W.a₂ * c' ^ 2 * w
      + MvPowerSeries.C W.a₃ * w ^ 2 + MvPowerSeries.C W.a₄ * c' * w ^ 2
      + MvPowerSeries.C W.a₆ * w ^ 3 := by
    have h := congrArg (PowerSeries.substAlgHom (R := R) hc's) W.formalW_eq
    simp only [map_add, map_mul, map_pow, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
    rw [show PowerSeries.subst c' W.formalW = W.fgGenW c' from rfl, ← hwdef] at h
    linear_combination h

  set Dc' := PowerSeries.subst c' W.fgInvDenom with hDcdef
  have hDcexp : Dc' = 1 - MvPowerSeries.C W.a₁ * c' - MvPowerSeries.C W.a₃ * w := by
    have h := congrArg (PowerSeries.substAlgHom (R := R) hc's)
      (show W.fgInvDenom
        = 1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * W.formalW from rfl)
    simp only [map_sub, map_mul, map_one, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
    rw [← hDcdef, show PowerSeries.subst c' W.formalW = W.fgGenW c' from rfl, ← hwdef] at h
    exact h
  have hccDc' : MvPowerSeries.constantCoeff Dc' = 1 := by
    rw [hDcexp]
    simp only [map_sub, map_mul, map_one, MvPowerSeries.constantCoeff_C, hc', hccw,
      mul_zero, sub_zero]
  set iD := MvPowerSeries.invOfUnit Dc' 1 with hiDdef
  have hinv_raw : Dc' * iD = 1 := MvPowerSeries.mul_invOfUnit Dc' 1 (by rw [hccDc']; simp)
  have hinv_c : (1 - MvPowerSeries.C W.a₁ * c' - MvPowerSeries.C W.a₃ * w) * iD = 1 := by
    rw [← hDcexp]; exact hinv_raw

  have hIrel_c : ic' * Dc' = -c' := by
    have h := congrArg (PowerSeries.substAlgHom (R := R) hc's) W.fgInv_mul_fgInvDenom
    simp only [map_mul, map_neg, PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom] at h
    rw [hicdef, hDcdef]; exact h
  have hic : ic' = -c' * iD := by
    rw [← mul_one ic', ← hinv_raw, ← mul_assoc, hIrel_c, neg_mul]

  have hccU : MvPowerSeries.constantCoeff (-w * iD) = 0 := by
    simp only [map_mul, map_neg, hccw, neg_zero, zero_mul]
  have hUeq : (-w * iD) = ic' ^ 3 + MvPowerSeries.C W.a₁ * ic' * (-w * iD)
      + MvPowerSeries.C W.a₂ * ic' ^ 2 * (-w * iD) + MvPowerSeries.C W.a₃ * (-w * iD) ^ 2
      + MvPowerSeries.C W.a₄ * ic' * (-w * iD) ^ 2 + MvPowerSeries.C W.a₆ * (-w * iD) ^ 3 := by
    rw [hic]
    linear_combination (iD * w * (iD + 1)) * hinv_c + (-(iD) ^ 3) * heq_c

  have hWic : W.fgGenW ic' = -w * iD := by
    have huniq := W.eq_subst_formalW hccic hccU hUeq
    rw [fgGenW]; exact huniq.symm

  have h0y : W.fgGenW ic' * (1 - MvPowerSeries.C W.a₁ * c' - MvPowerSeries.C W.a₃ * w) = -w := by
    rw [hWic]; linear_combination (-w) * hinv_c
  have h0x : ic' * w = c' * W.fgGenW ic' := by
    rw [hWic, hic]; ring

  simp only [genericPoint]
  rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · rw [xGen, xGen, div_eq_div_iff hwic' hwc', ← map_mul, ← map_mul]
    exact congrArg genι h0x
  · rw [yGen, yGen, xGen, WeierstrassCurve.Affine.negY]
    simp only [genW, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    have h0yK := congrArg genι h0y
    simp only [map_mul, map_sub, map_one, map_neg, hCalg] at h0yK
    rw [hicdef, hwdef] at h0yK
    field_simp
    linear_combination -h0yK

open Classical in

theorem genericPoint_hom [W.IsElliptic] {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (hne : a ≠ b)
    (hwa : genι (W.fgGenW a) ≠ 0) (hwb : genι (W.fgGenW b) ≠ 0)
    (hwc : genι (W.fgGenW (MvPowerSeries.subst ![a, b] W.fgZ3Fixed)) ≠ 0)
    (hwF : genι (W.fgGenW (MvPowerSeries.subst ![a, b] W.formalGroupLawFixed)) ≠ 0)
    (hx : W.xGen a ≠ W.xGen b) :
    W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero
          (kwB_constantCoeff_subst_pair ha hb W.constantCoeff_formalGroupLawFixed)) hwF
      = W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero ha) hwa
        + W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero hb) hwb := by
  have hFic := W.subst_formalGroupLawFixed_eq ha hb
  have hwic : genι (W.fgGenW
      (PowerSeries.subst (MvPowerSeries.subst ![a, b] W.fgZ3Fixed) W.fgInv)) ≠ 0 := by
    rw [← hFic]; exact hwF
  have hFgp := W.genericPoint_congr
    (PowerSeries.HasSubst.of_constantCoeff_zero
      (kwB_constantCoeff_subst_pair ha hb W.constantCoeff_formalGroupLawFixed)) hwF
    (PowerSeries.HasSubst.of_constantCoeff_zero
      (W.constantCoeff_subst_fgInv (kwB_constantCoeff_subst_pair ha hb W.constantCoeff_fgZ3Fixed))) hwic
    hFic
  rw [hFgp, W.obl0 (kwB_constantCoeff_subst_pair ha hb W.constantCoeff_fgZ3Fixed) hwc hwic]
  exact (W.genericPoint_sum ha hb hne hwa hwb hwc hx).symm

theorem genι_fgGenW_ne_zero {σ : Type*} [NoZeroDivisors (MvPowerSeries σ R)]
    {t : MvPowerSeries σ R} (ht : PowerSeries.HasSubst t)
    (htc : MvPowerSeries.constantCoeff t = 0) (ht_ne : t ≠ 0) :
    genι (W.fgGenW t) ≠ 0 := fun h =>
  W.fgGenW_ne_zero ht htc ht_ne
    ((map_eq_zero_iff genι (IsFractionRing.injective (MvPowerSeries σ R) (GenK σ R))).mp h)

theorem xGen_ne {σ : Type*} {a b : MvPowerSeries σ R}
    (hwa : genι (W.fgGenW a) ≠ 0) (hwb : genι (W.fgGenW b) ≠ 0)
    (hN : a * W.fgGenW b - b * W.fgGenW a ≠ 0) : W.xGen a ≠ W.xGen b := by
  intro h
  apply hN
  rw [xGen, xGen, div_eq_div_iff hwa hwb, ← map_mul, ← map_mul] at h
  rw [sub_eq_zero]
  exact (IsFractionRing.injective (MvPowerSeries σ R) (GenK σ R)) h

abbrev NoVar {σ : Type*} (j : σ) (x : MvPowerSeries σ R) : Prop :=
  ∀ d : σ →₀ ℕ, d j ≠ 0 → MvPowerSeries.coeff d x = 0

lemma noVar_one {σ : Type*} {j : σ} : NoVar j (1 : MvPowerSeries σ R) := by
  intro d hd
  classical
  rw [MvPowerSeries.coeff_one]
  split_ifs with he
  · exact absurd (by rw [he]; rfl : d j = 0) hd
  · rfl

lemma noVar_X {σ : Type*} {i j : σ} (hij : i ≠ j) :
    NoVar j (MvPowerSeries.X i : MvPowerSeries σ R) := by
  intro d hd
  classical
  rw [MvPowerSeries.coeff_X]
  split_ifs with he
  · rw [he] at hd; exact absurd (by simp [hij] : (Finsupp.single i 1) j = 0) hd
  · rfl

lemma kwB_noVar_mul {σ : Type*} {j : σ} {x y : MvPowerSeries σ R}
    (hx : NoVar j x) (hy : NoVar j y) : NoVar j (x * y) := by
  intro d hd
  classical
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rcases (by
    by_contra h; push Not at h
    exact hd (by have := congrArg (fun e => e j) hp
                 simpa [Finsupp.add_apply, h.1, h.2] using this.symm)
    : p.1 j ≠ 0 ∨ p.2 j ≠ 0) with h1 | h2
  · rw [hx p.1 h1, zero_mul]
  · rw [hy p.2 h2, mul_zero]

lemma kwB_noVar_pow {σ : Type*} {j : σ} {x : MvPowerSeries σ R} (hx : NoVar j x) :
    ∀ n, NoVar j (x ^ n)
  | 0 => by simpa using (noVar_one : NoVar j (1 : MvPowerSeries σ R))
  | (n+1) => by rw [pow_succ]; exact kwB_noVar_mul (kwB_noVar_pow hx n) hx

lemma noVar_fgGenW {σ : Type*} {j : σ} {a : MvPowerSeries σ R} (ha : NoVar j a)
    (hcc : MvPowerSeries.constantCoeff a = 0) : NoVar j (W.fgGenW a) := by
  intro d hd
  rw [fgGenW, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hcc)]
  have hterm : ∀ n, (PowerSeries.coeff n W.formalW) • MvPowerSeries.coeff d (a ^ n) = 0 := by
    intro n; rw [(kwB_noVar_pow ha n) d hd, smul_zero]
  rw [finsum_congr hterm, finsum_zero]

lemma noVar_subst_pair {σ : Type*} {j : σ} {a0 a1 : MvPowerSeries σ R}
    (h0 : NoVar j a0) (h1 : NoVar j a1)
    (hc0 : MvPowerSeries.constantCoeff a0 = 0) (hc1 : MvPowerSeries.constantCoeff a1 = 0)
    {g : MvPowerSeries (Fin 2) R} : NoVar j (MvPowerSeries.subst ![a0, a1] g) := by
  intro d hd
  rw [MvPowerSeries.coeff_subst (kwB_hasSubst_pair hc0 hc1)]
  have hterm : ∀ e : Fin 2 →₀ ℕ,
      (MvPowerSeries.coeff e g) •
        (MvPowerSeries.coeff d (e.prod fun s n => (![a0, a1] s) ^ n)) = 0 := by
    intro e
    have hnv : NoVar j (e.prod fun s n => (![a0, a1] s) ^ n) := by
      rw [Finsupp.prod]
      refine Finset.prod_induction _ (NoVar j) (fun _ _ hx hy => kwB_noVar_mul hx hy) noVar_one ?_
      intro s _
      fin_cases s
      · simpa using kwB_noVar_pow h0 (e 0)
      · simpa using kwB_noVar_pow h1 (e 1)
    rw [hnv d hd, smul_zero]
  rw [finsum_congr hterm, finsum_zero]

lemma coeff_fgGenW_X {σ : Type*} (j : σ) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single j k) (W.fgGenW (MvPowerSeries.X j))
      = PowerSeries.coeff k W.formalW := by
  classical
  rw [fgGenW, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  rw [finsum_eq_single _ k ?vanish]
  · rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  case vanish =>
    intro n hn
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
    exact fun he => hn (by have h2 := congrArg (fun f => f j) he; simp only [Finsupp.single_eq_same] at h2; omega)

lemma coeff_mul_noVar_X {σ : Type*} [DecidableEq σ] {j : σ} {a g : MvPowerSeries σ R}
    (ha : NoVar j a) (hg : ∀ k, k ≠ j → NoVar k g) {i : σ} (hij : i ≠ j) (t : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j t) (a * g)
      = MvPowerSeries.coeff (Finsupp.single i 1) a * MvPowerSeries.coeff (Finsupp.single j t) g := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single_of_mem
        (Finsupp.single i 1, Finsupp.single j t) (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)]
  intro p hp hpne
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_contra hprod
  obtain ⟨ha1, hg2⟩ := mul_ne_zero_iff.mp hprod
  have hp1j : p.1 j = 0 := by by_contra h; exact ha1 (ha p.1 h)
  have hp2nj : ∀ k, k ≠ j → p.2 k = 0 := fun k hk => by by_contra h; exact hg2 (hg k hk p.2 h)
  have hp2 : p.2 = Finsupp.single j t := by
    ext k
    rcases eq_or_ne k j with rfl | hk
    · have h := DFunLike.congr_fun hp k
      have hA : (Finsupp.single i (1 : ℕ)) k = 0 := Finsupp.single_eq_of_ne (Ne.symm hij)
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, hA, hp1j, zero_add] at h
      rw [h, Finsupp.single_eq_same]
    · rw [hp2nj k hk, Finsupp.single_eq_of_ne hk]
  exact hpne (Prod.ext (by rw [hp2] at hp; exact add_right_cancel hp) hp2)

lemma hN_aXj {σ : Type*} [DecidableEq σ] {a : MvPowerSeries σ R} {i j : σ} (hij : i ≠ j)
    (ha : NoVar j a) (hacc : MvPowerSeries.constantCoeff a = 0)
    (hai : MvPowerSeries.coeff (Finsupp.single i 1) a = 1) :
    a * W.fgGenW (MvPowerSeries.X j) - (MvPowerSeries.X j) * W.fgGenW a ≠ 0 := by
  classical
  intro h
  have key : MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j 3)
      (a * W.fgGenW (MvPowerSeries.X j) - (MvPowerSeries.X j) * W.fgGenW a) = 1 := by
    rw [map_sub]
    rw [coeff_mul_noVar_X ha
          (fun k hk => W.noVar_fgGenW (noVar_X (Ne.symm hk)) (by rw [MvPowerSeries.constantCoeff_X])) hij 3,
        hai, W.coeff_fgGenW_X, W.coeff_formalW_three, mul_one]
    have hterm2 : MvPowerSeries.coeff (Finsupp.single i 1 + Finsupp.single j 3)
        ((MvPowerSeries.X j) * W.fgGenW a) = 0 := by
      rw [MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases hp1 : p.1 = Finsupp.single j 1
      · have hp2j : p.2 j ≠ 0 := by
          have h := hp; rw [hp1] at h
          have h2 := DFunLike.congr_fun h j
          have hA : (Finsupp.single i (1 : ℕ)) j = 0 := Finsupp.single_eq_of_ne (Ne.symm hij)
          simp only [Finsupp.add_apply, Finsupp.single_eq_same, hA] at h2
          omega
        rw [W.noVar_fgGenW ha hacc p.2 hp2j, mul_zero]
      · rw [MvPowerSeries.coeff_X, if_neg hp1, zero_mul]
    rw [hterm2, sub_zero]
  rw [h, map_zero] at key; exact one_ne_zero key.symm

lemma hlin_Fab : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
    (MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] W.formalGroupLawFixed) = (1 : R) := by
  rw [MvPowerSeries.coeff_subst
        (kwB_hasSubst_pair (by simp [MvPowerSeries.constantCoeff_X]) (by simp [MvPowerSeries.constantCoeff_X]))]
  rw [finsum_eq_single _ (Finsupp.single 0 1) ?van]
  · simp [Finsupp.prod_single_index, Matrix.cons_val_zero, MvPowerSeries.coeff_X,
      W.coeff_single_formalGroupLawFixed 0]
  case van =>
    intro e he
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial]
    rw [if_neg, smul_zero]
    intro hmu
    apply he
    have h0 := DFunLike.congr_fun hmu 0
    have h1 := DFunLike.congr_fun hmu 1
    simp [Finsupp.add_apply] at h0 h1
    ext k
    fin_cases k <;> simp  <;> omega

lemma hlin_Fbc : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 1)
    (MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] W.formalGroupLawFixed) = (1 : R) := by
  rw [MvPowerSeries.coeff_subst
        (kwB_hasSubst_pair (by simp [MvPowerSeries.constantCoeff_X]) (by simp [MvPowerSeries.constantCoeff_X]))]
  rw [finsum_eq_single _ (Finsupp.single 0 1) ?van]
  · simp [Finsupp.prod_single_index, Matrix.cons_val_zero, MvPowerSeries.coeff_X,
      W.coeff_single_formalGroupLawFixed 0]
  case van =>
    intro e he
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial]
    rw [if_neg, smul_zero]
    intro hmu
    apply he
    have h0 := DFunLike.congr_fun hmu 1
    have h1 := DFunLike.congr_fun hmu 2
    simp [Finsupp.add_apply] at h0 h1
    ext k
    fin_cases k <;> simp  <;> omega

lemma coeffZ_X0X1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
    (MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] W.fgZ3Fixed) = (-1 : R) := by
  rw [MvPowerSeries.coeff_subst
        (kwB_hasSubst_pair (by simp [MvPowerSeries.constantCoeff_X]) (by simp [MvPowerSeries.constantCoeff_X]))]
  rw [finsum_eq_single _ (Finsupp.single 0 1) ?van]
  · simp [Finsupp.prod_single_index, Matrix.cons_val_zero, MvPowerSeries.coeff_X,
      W.coeff_single_fgZ3Fixed 0]
  case van =>
    intro e he
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial]
    rw [if_neg, smul_zero]
    intro hmu
    apply he
    have h0 := DFunLike.congr_fun hmu 0
    have h1 := DFunLike.congr_fun hmu 1
    simp [Finsupp.add_apply] at h0 h1
    ext k
    fin_cases k <;> simp  <;> omega

lemma coeffZ_X1X2 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 1)
    (MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] W.fgZ3Fixed) = (-1 : R) := by
  rw [MvPowerSeries.coeff_subst
        (kwB_hasSubst_pair (by simp [MvPowerSeries.constantCoeff_X]) (by simp [MvPowerSeries.constantCoeff_X]))]
  rw [finsum_eq_single _ (Finsupp.single 0 1) ?van]
  · simp [Finsupp.prod_single_index, Matrix.cons_val_zero, MvPowerSeries.coeff_X,
      W.coeff_single_fgZ3Fixed 0]
  case van =>
    intro e he
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial]
    rw [if_neg, smul_zero]
    intro hmu
    apply he
    have h0 := DFunLike.congr_fun hmu 1
    have h1 := DFunLike.congr_fun hmu 2
    simp [Finsupp.add_apply] at h0 h1
    ext k
    fin_cases k <;> simp  <;> omega

lemma coeff_single_one_mul_cc {σ : Type*} {a c : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hc : MvPowerSeries.constantCoeff c = 0) (k : σ) :
    MvPowerSeries.coeff (Finsupp.single k 1) (a * c) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  have h1a : (1 : ℕ∞) ≤ a.order := by
    simpa using MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero 1 ha
  have h1c : (1 : ℕ∞) ≤ c.order := by
    simpa using MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero 1 hc
  calc ((Finsupp.degree (Finsupp.single k 1) : ℕ) : ℕ∞)
        = 1 := by simp [Finsupp.degree_single]
    _ < 1 + 1 := by norm_num
    _ ≤ a.order + c.order := add_le_add h1a h1c
    _ ≤ (a * c).order := MvPowerSeries.le_order_mul

lemma coeffZ_FabX2 :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
      (MvPowerSeries.subst
        ![MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)] W.formalGroupLawFixed,
          MvPowerSeries.X (2 : Fin 3)]
        W.fgZ3Fixed) = (-1 : R) := by

  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cFab := kwB_constantCoeff_subst_pair cX0 cX1 W.constantCoeff_formalGroupLawFixed
  have hlinF := W.hlin_Fab
  set Fab : MvPowerSeries (Fin 3) R := MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)] W.formalGroupLawFixed
    with hFabdef
  have hsub : MvPowerSeries.HasSubst
      (![Fab, MvPowerSeries.X (2 : Fin 3)] : Fin 2 → MvPowerSeries (Fin 3) R) := kwB_hasSubst_pair cFab cX2
  rw [MvPowerSeries.coeff_subst (f := W.fgZ3Fixed) hsub]
  rw [finsum_eq_single _ (Finsupp.single 0 1) ?van]
  · simp [Finsupp.prod_single_index, Matrix.cons_val_zero, hlinF, W.coeff_single_fgZ3Fixed 0]
  case van =>
    intro e he
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    suffices h : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
        (Fab ^ (e 0) * (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) ^ (e 1)) = 0 by
      rw [h, smul_zero]
    rcases Nat.lt_or_ge (e 0 + e 1) 2 with hlt | hge
    · have he2 : e = 0 ∨ e = Finsupp.single (1 : Fin 2) 1 := by
        rcases Nat.eq_zero_or_pos (e 0) with h0 | h0
        · rcases Nat.eq_zero_or_pos (e 1) with h1 | h1
          · exact Or.inl (by ext k; fin_cases k <;> simp_all)
          · refine Or.inr ?_; ext k; fin_cases k <;>
              simp_all; omega
        · exact absurd (show e = Finsupp.single (0 : Fin 2) 1 by
            ext k; fin_cases k <;> simp_all  <;> omega) he
      rcases he2 with rfl | rfl
      · simp [MvPowerSeries.coeff_one]
      · rw [show ((Finsupp.single (1 : Fin 2) 1) 0) = 0 from by simp,
          show ((Finsupp.single (1 : Fin 2) 1) 1) = 1 from by simp,
          pow_zero, one_mul, pow_one, MvPowerSeries.coeff_X,
          if_neg (by intro h; simpa using DFunLike.congr_fun h (0 : Fin 3))]
    · apply MvPowerSeries.coeff_of_lt_order
      calc ((Finsupp.degree (Finsupp.single (0 : Fin 3) 1) : ℕ) : ℕ∞)
            = 1 := by simp [Finsupp.degree_single]
        _ < 2 := by norm_num
        _ ≤ (e 0 : ℕ∞) + (e 1 : ℕ∞) := by exact_mod_cast hge
        _ ≤ (Fab ^ (e 0)).order + ((MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) ^ (e 1)).order :=
            add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (e 0) cFab)
              (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (e 1) cX2)
        _ ≤ _ := MvPowerSeries.le_order_mul

lemma coeffZ_X0Fbc :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
      (MvPowerSeries.subst
        ![MvPowerSeries.X (0 : Fin 3),
          MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X (2 : Fin 3)] W.formalGroupLawFixed]
        W.fgZ3Fixed) = (-1 : R) := by
  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX2 : MvPowerSeries.constantCoeff (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cFbc := kwB_constantCoeff_subst_pair cX1 cX2 W.constantCoeff_formalGroupLawFixed
  set Fbc : MvPowerSeries (Fin 3) R := MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X (2 : Fin 3)] W.formalGroupLawFixed
    with hFbcdef
  have hNoVarFbc : NoVar (0 : Fin 3) Fbc := by
    rw [hFbcdef]
    exact noVar_subst_pair (noVar_X (by decide)) (noVar_X (by decide)) cX1 cX2
  have hsub : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (0 : Fin 3), Fbc] : Fin 2 → MvPowerSeries (Fin 3) R) := kwB_hasSubst_pair cX0 cFbc
  rw [MvPowerSeries.coeff_subst (f := W.fgZ3Fixed) hsub]
  rw [finsum_eq_single _ (Finsupp.single 0 1) ?van]
  · simp [Finsupp.prod_single_index, Matrix.cons_val_zero, MvPowerSeries.coeff_X,
      W.coeff_single_fgZ3Fixed 0]
  case van =>
    intro e he
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    suffices h : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
        ((MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) ^ (e 0) * Fbc ^ (e 1)) = 0 by
      rw [h, smul_zero]
    rcases Nat.lt_or_ge (e 0 + e 1) 2 with hlt | hge
    · have he2 : e = 0 ∨ e = Finsupp.single (1 : Fin 2) 1 := by
        rcases Nat.eq_zero_or_pos (e 0) with h0 | h0
        · rcases Nat.eq_zero_or_pos (e 1) with h1 | h1
          · exact Or.inl (by ext k; fin_cases k <;> simp_all)
          · refine Or.inr ?_; ext k; fin_cases k <;>
              simp_all; omega
        · exact absurd (show e = Finsupp.single (0 : Fin 2) 1 by
            ext k; fin_cases k <;> simp_all  <;> omega) he
      rcases he2 with rfl | rfl
      · simp [MvPowerSeries.coeff_one]
      · rw [show ((Finsupp.single (1 : Fin 2) 1) 0) = 0 from by simp,
          show ((Finsupp.single (1 : Fin 2) 1) 1) = 1 from by simp,
          pow_zero, one_mul, pow_one]
        exact hNoVarFbc (Finsupp.single 0 1) (by simp)
    · apply MvPowerSeries.coeff_of_lt_order
      calc ((Finsupp.degree (Finsupp.single (0 : Fin 3) 1) : ℕ) : ℕ∞)
            = 1 := by simp [Finsupp.degree_single]
        _ < 2 := by norm_num
        _ ≤ (e 0 : ℕ∞) + (e 1 : ℕ∞) := by exact_mod_cast hge
        _ ≤ ((MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) ^ (e 0)).order + (Fbc ^ (e 1)).order :=
            add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (e 0) cX0)
              (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (e 1) cFbc)
        _ ≤ _ := MvPowerSeries.le_order_mul

lemma hlin_FabX2 :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
      (MvPowerSeries.subst
        ![MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)] W.formalGroupLawFixed,
          MvPowerSeries.X (2 : Fin 3)]
        W.formalGroupLawFixed) = (1 : R) := by

  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cFab := kwB_constantCoeff_subst_pair cX0 cX1 W.constantCoeff_formalGroupLawFixed
  have hlinF := W.hlin_Fab
  set Fab : MvPowerSeries (Fin 3) R := MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)] W.formalGroupLawFixed
    with hFabdef
  have hsub : MvPowerSeries.HasSubst
      (![Fab, MvPowerSeries.X (2 : Fin 3)] : Fin 2 → MvPowerSeries (Fin 3) R) := kwB_hasSubst_pair cFab cX2
  rw [MvPowerSeries.coeff_subst (f := W.formalGroupLawFixed) hsub]
  rw [finsum_eq_single _ (Finsupp.single 0 1) ?van]
  · simp [Finsupp.prod_single_index, Matrix.cons_val_zero, hlinF, W.coeff_single_formalGroupLawFixed 0]
  case van =>
    intro e he
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    suffices h : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
        (Fab ^ (e 0) * (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) ^ (e 1)) = 0 by
      rw [h, smul_zero]
    rcases Nat.lt_or_ge (e 0 + e 1) 2 with hlt | hge
    · have he2 : e = 0 ∨ e = Finsupp.single (1 : Fin 2) 1 := by
        rcases Nat.eq_zero_or_pos (e 0) with h0 | h0
        · rcases Nat.eq_zero_or_pos (e 1) with h1 | h1
          · exact Or.inl (by ext k; fin_cases k <;> simp_all)
          · refine Or.inr ?_; ext k; fin_cases k <;>
              simp_all; omega
        · exact absurd (show e = Finsupp.single (0 : Fin 2) 1 by
            ext k; fin_cases k <;> simp_all  <;> omega) he
      rcases he2 with rfl | rfl
      · simp [MvPowerSeries.coeff_one]
      · rw [show ((Finsupp.single (1 : Fin 2) 1) 0) = 0 from by simp,
          show ((Finsupp.single (1 : Fin 2) 1) 1) = 1 from by simp,
          pow_zero, one_mul, pow_one, MvPowerSeries.coeff_X,
          if_neg (by intro h; simpa using DFunLike.congr_fun h (0 : Fin 3))]
    · apply MvPowerSeries.coeff_of_lt_order
      calc ((Finsupp.degree (Finsupp.single (0 : Fin 3) 1) : ℕ) : ℕ∞)
            = 1 := by simp [Finsupp.degree_single]
        _ < 2 := by norm_num
        _ ≤ (e 0 : ℕ∞) + (e 1 : ℕ∞) := by exact_mod_cast hge
        _ ≤ (Fab ^ (e 0)).order + ((MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) ^ (e 1)).order :=
            add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (e 0) cFab)
              (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (e 1) cX2)
        _ ≤ _ := MvPowerSeries.le_order_mul

lemma hlin_X0Fbc :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
      (MvPowerSeries.subst
        ![MvPowerSeries.X (0 : Fin 3),
          MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X (2 : Fin 3)] W.formalGroupLawFixed]
        W.formalGroupLawFixed) = (1 : R) := by
  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX2 : MvPowerSeries.constantCoeff (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cFbc := kwB_constantCoeff_subst_pair cX1 cX2 W.constantCoeff_formalGroupLawFixed
  set Fbc : MvPowerSeries (Fin 3) R := MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X (2 : Fin 3)] W.formalGroupLawFixed
    with hFbcdef
  have hNoVarFbc : NoVar (0 : Fin 3) Fbc := by
    rw [hFbcdef]
    exact noVar_subst_pair (noVar_X (by decide)) (noVar_X (by decide)) cX1 cX2
  have hsub : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (0 : Fin 3), Fbc] : Fin 2 → MvPowerSeries (Fin 3) R) := kwB_hasSubst_pair cX0 cFbc
  rw [MvPowerSeries.coeff_subst (f := W.formalGroupLawFixed) hsub]
  rw [finsum_eq_single _ (Finsupp.single 0 1) ?van]
  · simp [Finsupp.prod_single_index, Matrix.cons_val_zero, MvPowerSeries.coeff_X,
      W.coeff_single_formalGroupLawFixed 0]
  case van =>
    intro e he
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    suffices h : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)
        ((MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) ^ (e 0) * Fbc ^ (e 1)) = 0 by
      rw [h, smul_zero]
    rcases Nat.lt_or_ge (e 0 + e 1) 2 with hlt | hge
    · have he2 : e = 0 ∨ e = Finsupp.single (1 : Fin 2) 1 := by
        rcases Nat.eq_zero_or_pos (e 0) with h0 | h0
        · rcases Nat.eq_zero_or_pos (e 1) with h1 | h1
          · exact Or.inl (by ext k; fin_cases k <;> simp_all)
          · refine Or.inr ?_; ext k; fin_cases k <;>
              simp_all; omega
        · exact absurd (show e = Finsupp.single (0 : Fin 2) 1 by
            ext k; fin_cases k <;> simp_all  <;> omega) he
      rcases he2 with rfl | rfl
      · simp [MvPowerSeries.coeff_one]
      · rw [show ((Finsupp.single (1 : Fin 2) 1) 0) = 0 from by simp,
          show ((Finsupp.single (1 : Fin 2) 1) 1) = 1 from by simp,
          pow_zero, one_mul, pow_one]
        exact hNoVarFbc (Finsupp.single 0 1) (by simp)
    · apply MvPowerSeries.coeff_of_lt_order
      calc ((Finsupp.degree (Finsupp.single (0 : Fin 3) 1) : ℕ) : ℕ∞)
            = 1 := by simp [Finsupp.degree_single]
        _ < 2 := by norm_num
        _ ≤ (e 0 : ℕ∞) + (e 1 : ℕ∞) := by exact_mod_cast hge
        _ ≤ ((MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) ^ (e 0)).order + (Fbc ^ (e 1)).order :=
            add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (e 0) cX0)
              (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (e 1) cFbc)
        _ ≤ _ := MvPowerSeries.le_order_mul

theorem formalGroupLawFixed_assoc [W.IsElliptic] :
    MvPowerSeries.subst
        ![MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)]
            W.formalGroupLawFixed,
          (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R)] W.formalGroupLawFixed
      = MvPowerSeries.subst
        ![(MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R),
          MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X (2 : Fin 3)]
            W.formalGroupLawFixed] W.formalGroupLawFixed := by
  classical

  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]
  have cX2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) = 0 := by
    simp [MvPowerSeries.constantCoeff_X]

  have cFab := kwB_constantCoeff_subst_pair cX0 cX1 W.constantCoeff_formalGroupLawFixed
  have cFbc := kwB_constantCoeff_subst_pair cX1 cX2 W.constantCoeff_formalGroupLawFixed
  have cFabX2 := kwB_constantCoeff_subst_pair cFab cX2 W.constantCoeff_formalGroupLawFixed
  have cX0Fbc := kwB_constantCoeff_subst_pair cX0 cFbc W.constantCoeff_formalGroupLawFixed
  have cZab := kwB_constantCoeff_subst_pair cX0 cX1 W.constantCoeff_fgZ3Fixed
  have cZbc := kwB_constantCoeff_subst_pair cX1 cX2 W.constantCoeff_fgZ3Fixed
  have cZFabX2 := kwB_constantCoeff_subst_pair cFab cX2 W.constantCoeff_fgZ3Fixed
  have cZX0Fbc := kwB_constantCoeff_subst_pair cX0 cFbc W.constantCoeff_fgZ3Fixed

  have nX0 : (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
  have nX1 : (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 1)) h
  have nX2 : (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) 1)) h
  have nFab : (MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)]
      W.formalGroupLawFixed : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [W.hlin_Fab] using congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
  have nFbc : (MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X (2 : Fin 3)]
      W.formalGroupLawFixed : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [W.hlin_Fbc] using congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 1)) h
  have nFabX2 : (MvPowerSeries.subst
      ![MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)]
          W.formalGroupLawFixed, MvPowerSeries.X (2 : Fin 3)] W.formalGroupLawFixed
      : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [W.hlin_FabX2] using congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
  have nX0Fbc : (MvPowerSeries.subst
      ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3),
          MvPowerSeries.X (2 : Fin 3)] W.formalGroupLawFixed] W.formalGroupLawFixed
      : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [W.hlin_X0Fbc] using congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
  have nZab : (MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)]
      W.fgZ3Fixed : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [W.coeffZ_X0X1] using congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
  have nZbc : (MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X (2 : Fin 3)]
      W.fgZ3Fixed : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [W.coeffZ_X1X2] using congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 1)) h
  have nZFabX2 : (MvPowerSeries.subst
      ![MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)]
          W.formalGroupLawFixed, MvPowerSeries.X (2 : Fin 3)] W.fgZ3Fixed
      : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [W.coeffZ_FabX2] using congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
  have nZX0Fbc : (MvPowerSeries.subst
      ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3),
          MvPowerSeries.X (2 : Fin 3)] W.formalGroupLawFixed] W.fgZ3Fixed
      : MvPowerSeries (Fin 3) R) ≠ 0 := fun h => by
    simpa [W.coeffZ_X0Fbc] using congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h

  have gwX0 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cX0) cX0 nX0
  have gwX1 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cX1) cX1 nX1
  have gwX2 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cX2) cX2 nX2
  have gwFab := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cFab) cFab nFab
  have gwFbc := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cFbc) cFbc nFbc
  have gwLHS := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cFabX2) cFabX2 nFabX2
  have gwRHS := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cX0Fbc) cX0Fbc nX0Fbc
  have gwcAb := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cZab) cZab nZab
  have gwcBc := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cZbc) cZbc nZbc
  have gwcFabX2 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cZFabX2) cZFabX2 nZFabX2
  have gwcX0Fbc := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cZX0Fbc) cZX0Fbc nZX0Fbc

  have hN1 : (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) * W.fgGenW (MvPowerSeries.X 1)
      - (MvPowerSeries.X 1) * W.fgGenW (MvPowerSeries.X 0) ≠ 0 :=
    W.hN_aXj (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) (noVar_X (by decide)) cX0
      (by simp [MvPowerSeries.coeff_X])
  have hN2 : (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) R) * W.fgGenW (MvPowerSeries.X 2)
      - (MvPowerSeries.X 2) * W.fgGenW (MvPowerSeries.X 1) ≠ 0 :=
    W.hN_aXj (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) (noVar_X (by decide)) cX1
      (by simp [MvPowerSeries.coeff_X])
  have hN3 : MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] W.formalGroupLawFixed
        * W.fgGenW (MvPowerSeries.X 2)
      - (MvPowerSeries.X 2) * W.fgGenW (MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3),
          MvPowerSeries.X 1] W.formalGroupLawFixed) ≠ 0 :=
    W.hN_aXj (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
      (noVar_subst_pair (noVar_X (by decide)) (noVar_X (by decide)) cX0 cX1) cFab W.hlin_Fab
  have hN4 : MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] W.formalGroupLawFixed
        * W.fgGenW (MvPowerSeries.X 0)
      - (MvPowerSeries.X 0) * W.fgGenW (MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3),
          MvPowerSeries.X 2] W.formalGroupLawFixed) ≠ 0 :=
    W.hN_aXj (i := (1 : Fin 3)) (j := (0 : Fin 3)) (by decide)
      (noVar_subst_pair (noVar_X (by decide)) (noVar_X (by decide)) cX1 cX2) cFbc W.hlin_Fbc

  have hne1 : MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] W.formalGroupLawFixed
      ≠ MvPowerSeries.X 2 := fun h => hN3 (by rw [h]; ring)
  have hne2 : (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) ≠ MvPowerSeries.X 1 :=
    fun h => hN1 (by rw [h]; ring)
  have hne3 : (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) R) ≠ MvPowerSeries.X 2 :=
    fun h => hN2 (by rw [h]; ring)
  have hne4 : (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R)
      ≠ MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] W.formalGroupLawFixed :=
    fun h => hN4 (by rw [h]; ring)

  have hx1 := W.xGen_ne gwFab gwX2 hN3
  have hx2 := W.xGen_ne gwX0 gwX1 hN1
  have hx3 := W.xGen_ne gwX1 gwX2 hN2
  have hx4 := (W.xGen_ne gwFbc gwX0 hN4).symm

  apply W.genericPoint_injective _ _ gwLHS gwRHS
  calc W.genericPoint _ gwLHS
      = W.genericPoint _ gwFab + W.genericPoint _ gwX2 :=
          W.genericPoint_hom cFab cX2 hne1 gwFab gwX2 gwcFabX2 gwLHS hx1
    _ = (W.genericPoint _ gwX0 + W.genericPoint _ gwX1) + W.genericPoint _ gwX2 := by
          rw [W.genericPoint_hom cX0 cX1 hne2 gwX0 gwX1 gwcAb gwFab hx2]
    _ = W.genericPoint _ gwX0 + (W.genericPoint _ gwX1 + W.genericPoint _ gwX2) := add_assoc _ _ _
    _ = W.genericPoint _ gwX0 + W.genericPoint _ gwFbc := by
          rw [← W.genericPoint_hom cX1 cX2 hne3 gwX1 gwX2 gwcBc gwFbc hx3]
    _ = W.genericPoint _ gwRHS :=
          (W.genericPoint_hom cX0 cFbc hne4 gwX0 gwFbc gwcX0Fbc gwRHS hx4).symm

def formalGroup [W.IsElliptic] : FormalGroup R where
  toPowerSeries := W.formalGroupLawFixed
  zero_constantCoeff := W.constantCoeff_formalGroupLawFixed
  lin_coeff_X := W.coeff_zero_formalGroupLawFixed
  lin_coeff_Y := W.coeff_one_formalGroupLawFixed
  assoc := W.formalGroupLawFixed_assoc

end

end WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

open MvPowerSeries in

theorem formalGroupLawFixed_comm [W.IsElliptic] :
    MvPowerSeries.subst
        ![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]
        W.formalGroupLawFixed
      = W.formalGroupLawFixed := by
  classical

  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have cX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) = 0 :=
    MvPowerSeries.constantCoeff_X _

  have cF01 := kwB_constantCoeff_subst_pair cX0 cX1 W.constantCoeff_formalGroupLawFixed
  have cF10 := kwB_constantCoeff_subst_pair cX1 cX0 W.constantCoeff_formalGroupLawFixed
  have cZ01 := kwB_constantCoeff_subst_pair cX0 cX1 W.constantCoeff_fgZ3Fixed
  have cZ10 := kwB_constantCoeff_subst_pair cX1 cX0 W.constantCoeff_fgZ3Fixed

  have nX0 : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ≠ 0 := fun h => by
    simpa [MvPowerSeries.coeff_X] using
      congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
  have nX1 : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ≠ 0 := fun h => by
    simpa [MvPowerSeries.coeff_X] using
      congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) h

  have hF01 : MvPowerSeries.subst
      ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1]
      W.formalGroupLawFixed = W.formalGroupLawFixed :=
    MvPowerSeries.subst_X_pair_eq_self W.formalGroupLawFixed
  have hZ01 : MvPowerSeries.subst
      ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1]
      W.fgZ3Fixed = W.fgZ3Fixed :=
    MvPowerSeries.subst_X_pair_eq_self W.fgZ3Fixed
  have nF : W.formalGroupLawFixed ≠ 0 := fun h => by
    simpa [W.coeff_zero_formalGroupLawFixed] using
      congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
  have nZ : W.fgZ3Fixed ≠ 0 := fun h => by
    simpa [W.coeff_single_fgZ3Fixed 0] using
      congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
  have nF01 : (MvPowerSeries.subst
      ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1]
      W.formalGroupLawFixed : MvPowerSeries (Fin 2) R) ≠ 0 := by rw [hF01]; exact nF
  have nZ01 : (MvPowerSeries.subst
      ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1]
      W.fgZ3Fixed : MvPowerSeries (Fin 2) R) ≠ 0 := by rw [hZ01]; exact nZ

  have hSwapSub : MvPowerSeries.HasSubst
      (![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by fin_cases i <;> exact MvPowerSeries.constantCoeff_X _)
  have hSwapInj : Function.Injective
      (MvPowerSeries.subst (R := R)
        ![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) := by
    intro f g hfg
    have hid : ∀ h : MvPowerSeries (Fin 2) R,
        MvPowerSeries.subst
          ![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]
          (MvPowerSeries.subst
            ![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] h)
          = h := fun h => by
      rw [MvPowerSeries.subst_comp_subst_apply hSwapSub hSwapSub]
      have heq : (fun s => MvPowerSeries.subst
          ![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]
          ((![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) s))
          = ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] := by
        funext s; fin_cases s <;> simp [MvPowerSeries.subst_X hSwapSub]
      rw [heq]
      exact MvPowerSeries.subst_X_pair_eq_self h
    calc f = MvPowerSeries.subst _ (MvPowerSeries.subst _ f) := (hid f).symm
      _ = MvPowerSeries.subst _ (MvPowerSeries.subst _ g) := by rw [hfg]
      _ = g := hid g
  have nF10 : (MvPowerSeries.subst
      ![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]
      W.formalGroupLawFixed : MvPowerSeries (Fin 2) R) ≠ 0 := fun h => nF (hSwapInj (by
        rw [h, ← MvPowerSeries.coe_substAlgHom hSwapSub, map_zero]))
  have nZ10 : (MvPowerSeries.subst
      ![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]
      W.fgZ3Fixed : MvPowerSeries (Fin 2) R) ≠ 0 := fun h => nZ (hSwapInj (by
        rw [h, ← MvPowerSeries.coe_substAlgHom hSwapSub, map_zero]))

  have gwX0 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cX0) cX0 nX0
  have gwX1 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cX1) cX1 nX1
  have gwF01 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cF01) cF01 nF01
  have gwF10 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cF10) cF10 nF10
  have gwZ01 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cZ01) cZ01 nZ01
  have gwZ10 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cZ10) cZ10 nZ10

  have hN01 : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) * W.fgGenW (MvPowerSeries.X 1)
      - (MvPowerSeries.X 1) * W.fgGenW (MvPowerSeries.X 0) ≠ 0 :=
    W.hN_aXj (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) (noVar_X (by decide)) cX0
      (by simp [MvPowerSeries.coeff_X])
  have hN10 : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) * W.fgGenW (MvPowerSeries.X 0)
      - (MvPowerSeries.X 0) * W.fgGenW (MvPowerSeries.X 1) ≠ 0 :=
    W.hN_aXj (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide) (noVar_X (by decide)) cX1
      (by simp [MvPowerSeries.coeff_X])

  have hne01 : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ≠ MvPowerSeries.X 1 :=
    fun h => hN01 (by rw [h]; ring)
  have hne10 : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ≠ MvPowerSeries.X 0 :=
    fun h => hN10 (by rw [h]; ring)

  have hx01 := W.xGen_ne gwX0 gwX1 hN01
  have hx10 := W.xGen_ne gwX1 gwX0 hN10

  conv_rhs => rw [← hF01]
  apply W.genericPoint_injective _ _ gwF10 gwF01
  calc W.genericPoint _ gwF10
      = W.genericPoint _ gwX1 + W.genericPoint _ gwX0 :=
          W.genericPoint_hom cX1 cX0 hne10 gwX1 gwX0 gwZ10 gwF10 hx10
    _ = W.genericPoint _ gwX0 + W.genericPoint _ gwX1 := add_comm _ _
    _ = W.genericPoint _ gwF01 :=
          (W.genericPoint_hom cX0 cX1 hne01 gwX0 gwX1 gwZ01 gwF01 hx01).symm

instance instIsCommFormalGroup [W.IsElliptic] : W.formalGroup.IsComm where
  comm := by
    show W.formalGroup.toPowerSeries
      = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] W.formalGroup.toPowerSeries
    exact (W.formalGroupLawFixed_comm).symm

end WeierstrassCurve


