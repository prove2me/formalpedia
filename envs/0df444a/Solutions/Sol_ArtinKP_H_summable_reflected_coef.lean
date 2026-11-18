-- Prove2me | solution 1 for ArtinKP.H.summable_reflected_coef
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:13.301923+00:00
-- url     : https://prove2.me/submissions/6006a3a5-382f-4246-88ab-b6cfa81fbf35

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB017

section
-- module Solutions.Artin.T12.L3X_Meas
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The finite norm -/

theorem SFin.norm_mk (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm = ∏ᶠ v ∈ placesOf 𝔪, NumberField.HeightOneSpectrum.adicAbv F v (x : F) :=
  rfl

theorem SFin.mk_mul (x y : Fˣ) : SFin.mk 𝔪 k (x * y) = SFin.mk 𝔪 k x + SFin.mk 𝔪 k y := rfl

theorem SFin.mk_surjective : Function.Surjective (SFin.mk 𝔪 k) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
  exact ⟨x, by simp only [SFin.mk, hx]; rfl⟩


theorem SFin.norm_mk_eq_prod (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm =
      ∏ v ∈ (finite_placesOf h𝔪).toFinset, NumberField.HeightOneSpectrum.adicAbv F v (x : F) := by
  rw [SFin.norm_mk, finprod_mem_eq_finite_toFinset_prod _ (finite_placesOf h𝔪)]

theorem SFin.norm_mk_pos (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) : 0 < (SFin.mk 𝔪 k x).norm := by
  rw [SFin.norm_mk_eq_prod h𝔪]
  exact Finset.prod_pos fun v _ => (AbsoluteValue.pos_iff _).2 x.ne_zero

theorem SFin.norm_pos (h𝔪 : 𝔪 ≠ ⊥) (y : SFin 𝔪 k) : 0 < y.norm := by
  obtain ⟨x, rfl⟩ := SFin.mk_surjective y
  exact SFin.norm_mk_pos h𝔪 x

theorem SFin.norm_add (h𝔪 : 𝔪 ≠ ⊥) (y z : SFin 𝔪 k) : (y + z).norm = y.norm * z.norm := by
  obtain ⟨x, rfl⟩ := SFin.mk_surjective y
  obtain ⟨x', rfl⟩ := SFin.mk_surjective z
  rw [← SFin.mk_mul, SFin.norm_mk_eq_prod h𝔪, SFin.norm_mk_eq_prod h𝔪, SFin.norm_mk_eq_prod h𝔪,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Units.val_mul, map_mul]

/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3P_Val
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L3P_Val: valuations as counts of principal fractional ideals

For `x ≠ 0` in a number field, `v.valuation x = exp (−count_v (x))`, where
`count_v (x) = FractionalIdeal.count F v (spanSingleton x)`. Membership in a nonzero fractional
ideal is a comparison of counts.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

/-! ### The places of `S` -/

variable {𝔪 : Ideal (𝓞 F)}

variable [Fintype (SP 𝔪)]

omit [Fintype (SP 𝔪)] in
theorem one_lt_qS (v : SP 𝔪) : 1 < qS v := by
  rw [qS]
  have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
  have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := by
    rw [ne_eq, Ideal.absNorm_eq_one_iff]; exact v.1.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.1.asIdeal := by omega
  exact_mod_cast this

theorem NN_eq_prod {S : Type*} [Fintype S] (q : S → ℝ) (hq : ∀ v, 0 < q v) (k : S → ℤ) :
    NN q k = ∏ v, q v ^ k v := by
  rw [NN, Real.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [lq, mul_comm, ← Real.rpow_intCast, Real.rpow_def_of_pos (hq v)]

theorem absNorm_Pk (k : SP 𝔪 → ℤ) :
    ((FractionalIdeal.absNorm ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) = NN (qS (𝔪 := 𝔪)) k := by
  rw [coe_Pk, map_prod, NN_eq_prod qS (fun v => (one_lt_qS v).trans' one_pos)]
  push_cast
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow₀, coeIdeal_absNorm]
  push_cast; rfl

/-- `|N m| = N 𝔟 · N(P^{val_S m})`. -/
theorem abs_norm_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔟 : ℝ) * NN (qS (𝔪 := 𝔪)) (valS (m : F)) := by
  rw [← absNorm_span_singleton (R := 𝓞 F), spanSingleton_eq_mul_Pk h𝔟 hm, map_mul,
    coeIdeal_absNorm, Rat.cast_mul, absNorm_Pk]
  push_cast; rfl

/-! ### Units, the different, and the trace dual -/

end ArtinPrimitiveRoots.L3P
end

section
-- module Solutions.Artin.T12.L3X_Emb
/-! # L3X_Emb: the embedding `F^× → SModel 𝔪 k`

* `sEmb` is a homomorphism on `F^×`.
* The `v`-adic absolute value is `q_v^{-ord_v}`; the finite norm of `[x]` is `∏_{v∈S_f} q_v^{-ord_v x}`.
* The product formula: `lnorm (sEmb m) = log N 𝔟` for an `S`-integer `m` generating the exterior
  ideal `𝔟 R`; in particular `lnorm (sEmb ε) = 0` for `S`-units.
* Valuations at `S_f` descend to `SFin`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem sEmb_of_ne {x : F} (hx : x ≠ 0) :
    sEmb 𝔪 k x = (fun w => (w.mult : ℝ) * Real.log (w x),
      fun w => ((Complex.arg (w.embedding x) : ℝ) : AddCircle (2 * Real.pi)),
      SFin.mk 𝔪 k (Units.mk0 x hx)) := by
  rw [sEmb, dif_neg hx]

theorem sEmb_fin {x : F} (hx : x ≠ 0) : (sEmb 𝔪 k x).2.2 = SFin.mk 𝔪 k (Units.mk0 x hx) := by
  rw [sEmb_of_ne hx]

theorem sEmb_fst {x : F} (hx : x ≠ 0) (w : InfinitePlace F) :
    (sEmb 𝔪 k x).1 w = (w.mult : ℝ) * Real.log (w x) := by
  rw [sEmb_of_ne hx]

/-! ### Absolute values and valuations -/

theorem adicAbv_eq (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv F v x =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-L3P.ordv v x) := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, L3P.valuation_eq_exp_neg_ordv v hx,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
    WithZero.log_exp]
  simp [zpow_neg]

theorem log_SFin_norm_mk (h𝔪 : 𝔪 ≠ ⊥) {x : F} (hx : x ≠ 0) :
    letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
    Real.log (SFin.mk 𝔪 k (Units.mk0 x hx)).norm =
      -∑ v : L3P.SP 𝔪, (L3P.ordv v.1 x : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  rw [SFin.norm_mk_eq_prod h𝔪]
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < (Ideal.absNorm v.asIdeal : ℝ) := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)
  rw [Real.log_prod (fun v _ => by
    rw [Units.val_mk0, adicAbv_eq v hx]; exact (zpow_pos (hq v) _).ne')]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_subtype (finite_placesOf h𝔪).toFinset (p := fun v => v ∈ placesOf 𝔪)
    (by simp)]
  convert Finset.sum_congr rfl fun (v : L3P.SP 𝔪) _ => (show
    Real.log ((NumberField.HeightOneSpectrum.adicAbv F v.1) ((Units.mk0 x hx : Fˣ) : F)) =
      -((L3P.ordv v.1 x : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ)) by
    rw [Units.val_mk0, adicAbv_eq v.1 hx, Real.log_zpow]; push_cast; ring)

/-- The product formula on the model. -/
theorem lnorm_sEmb_gen (h𝔪 : 𝔪 ≠ ⊥) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    lnorm (sEmb 𝔪 k (m : F)) = Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  have hm0 : (m : F) ≠ 0 := L3P.ne_zero_of_span_eq h𝔟 hm
  have hN := L3P.abs_norm_eq (𝔪 := 𝔪) h𝔟 hm
  have hinf : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w (m : F)) =
      Real.log (((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ)) := by
    rw [← InfinitePlace.prod_eq_abs_norm, Real.log_prod (fun w _ =>
      pow_ne_zero _ ((map_ne_zero w).2 hm0))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
  have h𝔟0 : (0 : ℝ) < Ideal.absNorm 𝔟 := by
    have : Ideal.absNorm 𝔟 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact h𝔟.1
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [lnorm, sEmb_of_ne hm0]
  simp only
  rw [hinf, log_SFin_norm_mk h𝔪 hm0, hN, L3P.NN, Real.log_mul h𝔟0.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  simp only [L3P.lq, L3P.qS, L3P.valS]
  ring

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Phi
/-! # L3X_Phi: the weight `Φ = ρ · 1_B([y]) · L(y)⁻¹` and the `S`-functions

* `Lmod` is a unitary character of `SModel`, radially trivial, rotating by `ω_{m_w}`.
* `psi y = 1_B([y]) L(y)⁻¹` is `Γ`-invariant; `Phi = ρ · psi`.
* `fpF` facts: its norm, and `L(y)⁻¹ fpF(y) = ∏_w κ(|y_w|)` on `y_f = 0`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Angular characters -/

theorem norm_toCircle (a : AddCircle (2 * Real.pi)) :
    ‖((AddCircle.toCircle a : Circle) : ℂ)‖ = 1 := Circle.norm_coe _

/-! ### The weight -/

/-! ### The forward `S`-function -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Row
/-! # WP-H0, file 3: the coordinate dictionary, part 1 — rows and frequencies

`(z, γ) ↦ γ · rowElt g z` is a bijection `RowClass 𝔪 × U_S⁶ ≃ R ∖ {0}` (`rowEquiv`), so each of the
two `∑'` of the frozen goal is a sum over `ν ∈ R ∖ 0` (`tsum_forward`, `tsum_reflected`, with the
exact summands of the goal). `rowOf ν` is the row class of `ν`: its ideal is the unique exterior
ideal `𝔷` with `𝔷R = νR` (`span_eq_map_rowOf`, `rowOf_ideal_unique`), its multiplicities are the
valuations of `ν` (`count_rowOf`), and it only depends on `ν` modulo `U_S⁶` (`rowOf_gam_mul`). -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

section

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)
include h𝔪

/-- The ideal of `rowOf ν` generates `νR`. -/
theorem span_eq_map_rowOf (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    Ideal.span {(ν : SInt 𝔪)} = (rowOf h𝔪 g ν).1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  have h : (ν : SInt 𝔪) = rowSInt g ((rowEquiv h𝔪 g).symm ν) :=
    (congrArg Subtype.val ((rowEquiv h𝔪 g).apply_symm_apply ν)).symm
  rw [h, rowSInt_eq_par]
  exact L3P.span_unit_mul_gen g _ _

/-! ### Reindexing the two sums of the frozen goal -/

end

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H0_Coord
/-! # WP-H0, file 4: the coordinate dictionary, part 2 — `SFin`, `sEmb`, `fp`, `Fm`

* `SFin`: `SFin.mk x = 0 ↔ x ∈ SLevel` (`= F^× ∩ U_k`), equality of classes, and weak approximation
  in the form needed: every class of `SFin 𝔪 k` is the class of a nonzero `S`-integer
  (`exists_sInt_rep`); `mem_SLevel_of_sub_one_mem`: `d ≡ 1 mod 𝔪^{k+1}` lies in `SLevel 𝔪 k`.
* `fpF_sEmb_add`: `fp (sEmb ν + y)` is the indicator of `[ν] + y_f = 0` (i.e. `ν·y_f ∈ U_k`)
  times `∏_w ω_{m_w}(ν_w) ω_{m_w}(y_w) κ(|ν|_w · e^{x_w})`.
* `FmOf_sEmb_sub`: the product-form `Fm` at `sEmb ν − y`.
* rotation covariance: `fpF_add_rot`, `FmOf_sub_rot`. -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots FractionalIdeal

set_option linter.unusedSectionVars false

open scoped Classical nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### `SFin` -/

theorem SFin_mk_eq_mk_iff (x y : Fˣ) :
    SFin.mk 𝔪 k x = SFin.mk 𝔪 k y ↔ x⁻¹ * y ∈ SLevel 𝔪 k :=
  Additive.ofMul.injective.eq_iff.trans QuotientGroup.eq

/-! ### `SFinCls` -/

/-! ### Angular characters and rotations -/

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ)

/-! ### The two functions at `sEmb ν ± y` -/

theorem exp_sEmb_fst_add {ν : F} (hν : ν ≠ 0) (w : InfinitePlace F) (t : ℝ) :
    Real.exp ((sEmb 𝔪 k ν).1 w + t) = w ν ^ w.mult * Real.exp t := by
  rw [L3X.sEmb_fst hν, Real.exp_add, Real.exp_nat_mul, Real.exp_log (w.pos_iff.2 hν)]

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H_Grid
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-HA, file 1: a grid bound for sums over separated point sets (pure analysis)

`grid_sum`: let `e : T → (W → ℂ)` (`W` finite) be such that two distinct points never lie in a
common cell of mesh `h` (in every real and imaginary coordinate). Then

  `∑_{t ∈ T} ∏_w (1 + ‖e t w‖)⁻⁴ ≤ (2 (1 + ζ₂ / h²))^{2 #W}`,

with absolute convergence. No measure theory: the points are injected into the grid
`(W × Bool → Bool × ℕ)` (sign and `⌊|x| / h⌋`), and the sum over the grid is a product of
one-dimensional sums (`pi_prod_summable`). -/

namespace ArtinKP.H

open Finset

/-- A sum of products over a finite index set is bounded by the product of the sums. -/
theorem pi_prod_summable {I : Type*} [Fintype I] [DecidableEq I] {β : Type*} (f : I → β → ℝ)
    (hf0 : ∀ i b, 0 ≤ f i b) (hf : ∀ i, Summable (f i)) :
    Summable (fun a : I → β => ∏ i, f i (a i)) ∧
      ∑' a : I → β, ∏ i, f i (a i) ≤ ∏ i, ∑' b, f i b := by
  classical
  have key : ∀ s : Finset (I → β), ∑ a ∈ s, ∏ i, f i (a i) ≤ ∏ i, ∑' b, f i b := by
    intro s
    set t : I → Finset β := fun i => s.image (fun a => a i)
    have hsub : s ⊆ Fintype.piFinset t := by
      intro a ha
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem (fun a => a i) ha
    calc ∑ a ∈ s, ∏ i, f i (a i) ≤ ∑ a ∈ Fintype.piFinset t, ∏ i, f i (a i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun a _ _ => Finset.prod_nonneg fun i _ => hf0 i _)
      _ = ∏ i, ∑ b ∈ t i, f i b := (Finset.prod_univ_sum t f).symm
      _ ≤ ∏ i, ∑' b, f i b := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun b _ => hf0 i b)
          (fun i _ => (hf i).sum_le_tsum _ (fun b _ => hf0 i b))
  have hs : Summable (fun a : I → β => ∏ i, f i (a i)) :=
    summable_of_sum_le (fun a => Finset.prod_nonneg fun i _ => hf0 i (a i)) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

theorem summable_zeta2 : Summable (fun j : ℕ => (((j : ℝ) + 1) ^ 2)⁻¹) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine h.congr fun j => ?_
  push_cast
  rw [one_div]

theorem zeta2_nonneg : 0 ≤ zeta2 := tsum_nonneg fun j => by positivity

/-- The one-dimensional cell sum. -/
theorem summable_cell {h : ℝ} (hh : 0 < h) :
    Summable (fun j : ℕ => ((1 + h * (j : ℝ)) ^ 2)⁻¹) ∧
      ∑' j : ℕ, ((1 + h * (j : ℝ)) ^ 2)⁻¹ ≤ 1 + zeta2 / h ^ 2 := by
  have hle : ∀ j : ℕ, ((1 + h * ((j + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ≤ (h ^ 2)⁻¹ * (((j : ℝ) + 1) ^ 2)⁻¹ := by
    intro j
    rw [← mul_inv, ← mul_pow]
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h1 : 0 < h * ((j : ℝ) + 1) := mul_pos hh hj
    apply inv_anti₀ (by positivity)
    push_cast
    nlinarith
  have hsh : Summable (fun j : ℕ => ((1 + h * ((j + 1 : ℕ) : ℝ)) ^ 2)⁻¹) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle (summable_zeta2.mul_left _)
  have hs : Summable (fun j : ℕ => ((1 + h * (j : ℝ)) ^ 2)⁻¹) := (summable_nat_add_iff 1).1 hsh
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_zero_add]
  have h0 : ((1 + h * ((0 : ℕ) : ℝ)) ^ 2)⁻¹ = 1 := by simp
  rw [h0]
  have h2 : ∑' j : ℕ, ((1 + h * ((j + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ≤ (h ^ 2)⁻¹ * zeta2 := by
    rw [zeta2, ← tsum_mul_left]
    exact hsh.tsum_le_tsum hle (summable_zeta2.mul_left _)
  rw [div_eq_inv_mul]
  linarith

theorem cell_bound {h : ℝ} (hh : 0 < h) {x r : ℝ} (hx : |x| ≤ r) :
    ((1 + r) ^ 2)⁻¹ ≤ ((1 + h * ((cellOf h x).2 : ℝ)) ^ 2)⁻¹ := by
  have h1 : ((cellOf h x).2 : ℝ) ≤ |x| / h := Nat.floor_le (div_nonneg (abs_nonneg x) hh.le)
  have h2 : h * ((cellOf h x).2 : ℝ) ≤ |x| := by
    rw [le_div_iff₀ hh] at h1; linarith
  have h3 : (0 : ℝ) ≤ h * ((cellOf h x).2 : ℝ) := by positivity
  apply inv_anti₀ (by positivity)
  have : 1 + h * ((cellOf h x).2 : ℝ) ≤ 1 + r := by linarith
  exact pow_le_pow_left₀ (by linarith) this 2

theorem cell_sep {h : ℝ} (hh : 0 < h) {x x' : ℝ} (hc : cellOf h x = cellOf h x') :
    |x - x'| < h := by
  have hs : decide (x < 0) = decide (x' < 0) := congrArg Prod.fst hc
  have hf : ⌊|x| / h⌋₊ = ⌊|x'| / h⌋₊ := congrArg Prod.snd hc
  have a1 : (⌊|x| / h⌋₊ : ℝ) ≤ |x| / h := Nat.floor_le (div_nonneg (abs_nonneg x) hh.le)
  have a2 : |x| / h < ⌊|x| / h⌋₊ + 1 := Nat.lt_floor_add_one _
  have b1 : (⌊|x'| / h⌋₊ : ℝ) ≤ |x'| / h := Nat.floor_le (div_nonneg (abs_nonneg x') hh.le)
  have b2 : |x'| / h < ⌊|x'| / h⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [hf] at a1 a2
  rw [le_div_iff₀ hh] at a1 b1
  rw [div_lt_iff₀ hh] at a2 b2
  have key : |(|x| - |x'|)| < h := by
    rw [abs_lt]; constructor <;> nlinarith
  by_cases hx : x < 0
  · have hx' : x' < 0 := by simpa [hx] using hs.symm
    rw [abs_of_neg hx, abs_of_neg hx'] at key
    rw [abs_lt] at key ⊢
    constructor <;> linarith [key.1, key.2]
  · have hx' : ¬ x' < 0 := by
      intro h'
      have : decide (x < 0) = true := by rw [hs]; simpa using h'
      exact hx (by simpa using this)
    rw [abs_of_nonneg (not_lt.1 hx), abs_of_nonneg (not_lt.1 hx')] at key
    exact key

/-- **The grid bound.** -/
theorem grid_sum {W : Type*} [Fintype W] [DecidableEq W] {T : Type*} (e : T → W → ℂ) {h : ℝ}
    (hh : 0 < h)
    (hsep : ∀ t t' : T,
      (∀ w, |(e t w).re - (e t' w).re| < h ∧ |(e t w).im - (e t' w).im| < h) → t = t') :
    Summable (fun t : T => ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹) ∧
      ∑' t : T, ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹ ≤
        (2 * (1 + zeta2 / h ^ 2)) ^ (Fintype.card W * 2) := by
  obtain ⟨hcs, hct⟩ := summable_cell hh
  set u : Bool × ℕ → ℝ := fun p => ((1 + h * (p.2 : ℝ)) ^ 2)⁻¹ with hu
  have hu0 : ∀ p, 0 ≤ u p := fun p => by positivity
  have hus : Summable u :=
    (summable_prod_of_nonneg hu0).2 ⟨fun _ => hcs, Summable.of_finite⟩
  have hut : ∑' p, u p ≤ 2 * (1 + zeta2 / h ^ 2) := by
    rw [hus.tsum_prod, tsum_fintype, Fintype.sum_bool]
    simp only [hu]
    linarith
  obtain ⟨hGs, hGt⟩ := pi_prod_summable (fun _ : W × Bool => u) (fun _ p => hu0 p) (fun _ => hus)
  set c : T → (W × Bool → Bool × ℕ) := fun t i =>
    cellOf h (if i.2 then (e t i.1).im else (e t i.1).re) with hc
  have hinj : Function.Injective c := by
    intro t t' htt
    refine hsep t t' fun w => ⟨?_, ?_⟩
    · have := congrFun htt (w, false)
      simp only [hc, Bool.false_eq_true, if_false] at this
      exact cell_sep hh this
    · have := congrFun htt (w, true)
      simp only [hc, if_true] at this
      exact cell_sep hh this
  have hle : ∀ t : T, ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹ ≤ ∏ i : W × Bool, u (c t i) := by
    intro t
    rw [Fintype.prod_prod_type]
    refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
    rw [Fintype.prod_bool]
    have h1 : ((1 + ‖e t w‖) ^ 2)⁻¹ ≤ u (c t (w, true)) := by
      simp only [hu, hc, if_true]
      exact cell_bound hh (Complex.abs_im_le_norm _)
    have h2 : ((1 + ‖e t w‖) ^ 2)⁻¹ ≤ u (c t (w, false)) := by
      simp only [hu, hc, Bool.false_eq_true, if_false]
      exact cell_bound hh (Complex.abs_re_le_norm _)
    calc ((1 + ‖e t w‖) ^ 4)⁻¹ = ((1 + ‖e t w‖) ^ 2)⁻¹ * ((1 + ‖e t w‖) ^ 2)⁻¹ := by
          rw [← mul_inv, ← pow_add]
      _ ≤ u (c t (w, true)) * u (c t (w, false)) :=
          mul_le_mul h1 h2 (by positivity) (hu0 _)
  have hcomp : Summable (fun t : T => ∏ i : W × Bool, u (c t i)) := hGs.comp_injective hinj
  have hs : Summable (fun t : T => ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹) :=
    Summable.of_nonneg_of_le (fun t => Finset.prod_nonneg fun w _ => by positivity) hle hcomp
  refine ⟨hs, ?_⟩
  calc ∑' t : T, ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹ ≤ ∑' t : T, ∏ i : W × Bool, u (c t i) :=
        hs.tsum_le_tsum hle hcomp
    _ ≤ ∑' a : W × Bool → Bool × ℕ, ∏ i, u (a i) :=
        tsum_comp_le_tsum_of_inj hGs (fun a => Finset.prod_nonneg fun i _ => hu0 _) hinj
    _ ≤ ∏ _i : W × Bool, ∑' p, u p := hGt
    _ = (∑' p, u p) ^ (Fintype.card W * 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    _ ≤ (2 * (1 + zeta2 / h ^ 2)) ^ (Fintype.card W * 2) :=
        pow_le_pow_left₀ (tsum_nonneg hu0) hut _

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.H_Sum
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty
/-! # WP-HA, file 2: sums over the nonzero `S`-integers, grouped by their class in `SFin`

* `one_le_prod_mul_norm`: the product formula for `d ∈ R ∖ 0`:
  `∏_w |d|_w · |d|_{S_f} = N(dR) ≥ 1`.
* `sep_class`: two distinct `ν, ν' ∈ R ∖ 0` of the same class `s ∈ SFin` satisfy
  `∏_w |ν − ν'|_w ≥ |s|_{S_f}⁻¹`.
* `fiber_sum`: `∑_{ν ∈ R∖0, [ν] = s} ∏_w (1 + w ν)⁻⁴ ≤ K (1 + |s|_{S_f}^{4r})`, `r = #places`,
  with `K` independent of `s`.
* `summable_class_weight`: `∑_{ν ∈ R∖0} B([ν]) ∏_w (1 + w ν)⁻⁴ < ∞` when `B ≥ 0`,
  `∑_s B(s) < ∞` and `∑_s B(s) |s|^{4r} < ∞`.

No hypothesis on the signature of `F` is used (the count is crude). -/

namespace ArtinKP.H

open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The product formula on `R ∖ 0`, as an inequality. -/
theorem one_le_prod_mul_norm (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (d : {ν : SInt 𝔪 // ν ≠ 0}) :
    1 ≤ (∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult) *
      (SFin.mk 𝔪 k (Units.mk0 ((d : SInt 𝔪) : F) (H0.coe_ne_zero d))).norm := by
  have hd := H0.coe_ne_zero d
  have h1 := L3X.lnorm_sEmb_gen (k := k) h𝔪 (H0.rowOf h𝔪 g d).1.2 (H0.span_eq_map_rowOf h𝔪 g d)
  have hN : (1 : ℝ) ≤ Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 := by
    have : Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact (H0.rowOf h𝔪 g d).1.2.1
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hP : 0 < ∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (w.pos_iff.2 hd) _
  have hn := L3X.SFin.norm_mk_pos (k := k) h𝔪 (Units.mk0 _ hd)
  rw [← Real.log_nonneg_iff (mul_pos hP hn), Real.log_mul hP.ne' hn.ne',
    Real.log_prod (fun w _ => (pow_pos (w.pos_iff.2 hd) _).ne')]
  have h2 : L3X.lnorm (sEmb 𝔪 k ((d : SInt 𝔪) : F)) =
      ∑ w : InfinitePlace F, Real.log (w ((d : SInt 𝔪) : F) ^ w.mult) +
        Real.log (SFin.mk 𝔪 k (Units.mk0 ((d : SInt 𝔪) : F) hd)).norm := by
    rw [L3X.lnorm, L3X.sEmb_fin hd]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [L3X.sEmb_fst hd, Real.log_pow]
  rw [← h2, h1]
  exact Real.log_nonneg hN

/-- Two elements of one class of `SFin`: the difference is no larger at `S_f`. -/
theorem norm_mk_sub_le (h𝔪 : 𝔪 ≠ ⊥) {x y : Fˣ} (hxy : SFin.mk 𝔪 k x = SFin.mk 𝔪 k y)
    (hne : (x : F) - (y : F) ≠ 0) :
    (SFin.mk 𝔪 k (Units.mk0 ((x : F) - (y : F)) hne)).norm ≤ (SFin.mk 𝔪 k x).norm := by
  rw [L3X.SFin.norm_mk_eq_prod h𝔪, L3X.SFin.norm_mk_eq_prod h𝔪]
  refine Finset.prod_le_prod (fun v _ => AbsoluteValue.nonneg _ _) fun v hv => ?_
  have hv' : v ∈ placesOf 𝔪 := (L3X.finite_placesOf h𝔪).mem_toFinset.1 hv
  have hmem := (H0.SFin_mk_eq_mk_iff x y).1 hxy v hv'
  have hlt := absNorm_zpow_neg_lt_one v k
  have hx0 : (x : F) ≠ 0 := x.ne_zero
  have e1 : ((x⁻¹ * y : Fˣ) : F) - 1 = (x : F)⁻¹ * (y : F) - 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  have e2 : (x : F) - (y : F) = -((x : F) * ((x : F)⁻¹ * (y : F) - 1)) := by
    field_simp; ring
  rw [e1] at hmem
  rw [Units.val_mk0, e2, AbsoluteValue.map_neg, map_mul]
  calc NumberField.HeightOneSpectrum.adicAbv F v (x : F) *
        NumberField.HeightOneSpectrum.adicAbv F v ((x : F)⁻¹ * (y : F) - 1)
      ≤ NumberField.HeightOneSpectrum.adicAbv F v (x : F) * 1 :=
        mul_le_mul_of_nonneg_left (hmem.trans hlt.le) (AbsoluteValue.nonneg _ _)
    _ = _ := mul_one _

/-- **Separation inside a class of `SFin`.** -/
theorem sep_class (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {ν ν' : {ν : SInt 𝔪 // ν ≠ 0}}
    (hs : (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2 = (sEmb 𝔪 k ((ν' : SInt 𝔪) : F)).2.2)
    (hne : ν ≠ ν') :
    ((sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2).norm⁻¹ ≤
      ∏ w : InfinitePlace F, w (((ν : SInt 𝔪) : F) - ((ν' : SInt 𝔪) : F)) ^ w.mult := by
  have hν := H0.coe_ne_zero ν
  have hν' := H0.coe_ne_zero ν'
  have hd0 : (ν : SInt 𝔪) - (ν' : SInt 𝔪) ≠ 0 := sub_ne_zero.2 fun h => hne (Subtype.ext h)
  set d : {ν : SInt 𝔪 // ν ≠ 0} := ⟨(ν : SInt 𝔪) - (ν' : SInt 𝔪), hd0⟩ with hd
  have hdF : ((d : SInt 𝔪) : F) = ((ν : SInt 𝔪) : F) - ((ν' : SInt 𝔪) : F) := rfl
  have h1 := one_le_prod_mul_norm (k := k) h𝔪 g d
  rw [L3X.sEmb_fin hν, L3X.sEmb_fin hν'] at hs
  have hne' : ((Units.mk0 _ hν : Fˣ) : F) - ((Units.mk0 _ hν' : Fˣ) : F) ≠ 0 := by
    rw [Units.val_mk0, Units.val_mk0, ← hdF]; exact H0.coe_ne_zero d
  have h2 := norm_mk_sub_le h𝔪 hs hne'
  have hn := L3X.SFin.norm_mk_pos (k := k) h𝔪 (Units.mk0 _ hν)
  have hP : 0 ≤ ∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult :=
    Finset.prod_nonneg fun w _ => pow_nonneg (apply_nonneg _ _) _
  rw [L3X.sEmb_fin hν, inv_le_iff_one_le_mul₀ hn, ← hdF]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hP)
  exact h2

theorem one_add_pow_le {u : ℝ} (hu : 0 ≤ u) (M : ℕ) : (1 + u) ^ M ≤ 2 ^ M * (1 + u ^ M) := by
  have hM : (0 : ℝ) ≤ u ^ M := pow_nonneg hu M
  have h2 : (0 : ℝ) ≤ 2 ^ M := by positivity
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ ≤ 2 ^ M * (1 + u ^ M) := le_mul_of_one_le_right h2 (by linarith)
  · calc (1 + u) ^ M ≤ (2 * u) ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ = 2 ^ M * u ^ M := mul_pow _ _ _
      _ ≤ 2 ^ M * (1 + u ^ M) := mul_le_mul_of_nonneg_left (by linarith) h2

/-- **The fibre bound**: the sum over one class of `SFin`, uniformly in the class. -/
theorem fiber_sum (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : SFin 𝔪 k,
      Summable (fun ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} //
          (sEmb 𝔪 k (((ν : SInt 𝔪)) : F)).2.2 = s} =>
        ∏ w : InfinitePlace F, ((1 + w (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) ^ 4)⁻¹) ∧
      ∑' ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // (sEmb 𝔪 k (((ν : SInt 𝔪)) : F)).2.2 = s},
        ∏ w : InfinitePlace F, ((1 + w (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) ^ 4)⁻¹ ≤
          K * (1 + s.norm ^ expo F) := by
  set r := Fintype.card (InfinitePlace F) with hr
  have hz := zeta2_nonneg
  refine ⟨(2 * (1 + 4 * zeta2)) ^ (r * 2) * 2 ^ (r * 4), by positivity, fun s => ?_⟩
  have hn : 0 < s.norm := L3X.SFin.norm_pos h𝔪 s
  set n := s.norm with hndef
  set h : ℝ := min 1 n⁻¹ / 2 with hh
  have hμ : 0 < min 1 n⁻¹ := lt_min one_pos (inv_pos.2 hn)
  have hh0 : 0 < h := by positivity
  have hsep : ∀ ν ν' : {ν : {ν : SInt 𝔪 // ν ≠ 0} // (sEmb 𝔪 k (((ν : SInt 𝔪)) : F)).2.2 = s},
      (∀ w : InfinitePlace F,
        |(w.embedding (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)).re -
            (w.embedding (((ν' : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)).re| < h ∧
          |(w.embedding (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)).im -
            (w.embedding (((ν' : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)).im| < h) → ν = ν' := by
    intro ν ν' hcell
    by_contra hne
    have hne' : (ν : {ν : SInt 𝔪 // ν ≠ 0}) ≠ ν' := fun h' => hne (Subtype.ext h')
    have hsp := sep_class h𝔪 g (ν.2.trans ν'.2.symm) hne'
    rw [ν.2] at hsp
    set dF : F := (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F) -
      (((ν' : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F) with hdF
    have hw : ∀ w : InfinitePlace F, w dF < min 1 n⁻¹ := by
      intro w
      obtain ⟨c1, c2⟩ := hcell w
      rw [← InfinitePlace.norm_embedding_eq, hdF, map_sub]
      have := Complex.norm_le_abs_re_add_abs_im
        (w.embedding (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F) -
          w.embedding (((ν' : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F))
      rw [Complex.sub_re, Complex.sub_im] at this
      have h2 : h + h = min 1 n⁻¹ := by rw [hh]; ring
      linarith
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have hle : ∏ w : InfinitePlace F, w dF ^ w.mult ≤ w₀ dF := by
      calc ∏ w : InfinitePlace F, w dF ^ w.mult
          ≤ ∏ w : InfinitePlace F, (if w = w₀ then w₀ dF else 1) := by
            refine Finset.prod_le_prod (fun w _ => pow_nonneg (apply_nonneg _ _) _) fun w _ => ?_
            have hw1 : w dF ≤ 1 := ((hw w).trans_le (min_le_left _ _)).le
            split_ifs with hw0
            · subst hw0
              exact pow_le_of_le_one (apply_nonneg _ _) hw1 InfinitePlace.mult_pos.ne'
            · exact pow_le_one₀ (apply_nonneg _ _) hw1
        _ = w₀ dF := by simp
    have := (hsp.trans hle).trans_lt ((hw w₀).trans_le (min_le_right _ _))
    exact lt_irrefl _ this
  obtain ⟨hs1, hs2⟩ := grid_sum
    (fun (ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // (sEmb 𝔪 k (((ν : SInt 𝔪)) : F)).2.2 = s})
      (w : InfinitePlace F) => w.embedding (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) hh0 hsep
  simp only [InfinitePlace.norm_embedding_eq] at hs1 hs2
  refine ⟨hs1, hs2.trans ?_⟩
  -- the constant
  have hn1 : (0 : ℝ) < 1 + n := by linarith
  have hμ' : (1 + n)⁻¹ ≤ min 1 n⁻¹ :=
    le_min (inv_le_one_of_one_le₀ (by linarith)) (inv_anti₀ hn (by linarith))
  have hh1 : 1 ≤ 2 * (1 + n) * h := by
    have : (1 + n) * (1 + n)⁻¹ = 1 := mul_inv_cancel₀ hn1.ne'
    have h3 : (1 + n) * (1 + n)⁻¹ ≤ (1 + n) * min 1 n⁻¹ := mul_le_mul_of_nonneg_left hμ' hn1.le
    rw [hh]; nlinarith
  have hq : zeta2 / h ^ 2 ≤ zeta2 * (4 * (1 + n) ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ (2 * (1 + n) * h) ^ 2 := one_le_pow₀ hh1
    nlinarith
  have hA : 2 * (1 + zeta2 / h ^ 2) ≤ 2 * (1 + 4 * zeta2) * (1 + n) ^ 2 := by
    have : (1 : ℝ) ≤ (1 + n) ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  have hq0 : 0 ≤ zeta2 / h ^ 2 := by positivity
  calc (2 * (1 + zeta2 / h ^ 2)) ^ (r * 2)
      ≤ (2 * (1 + 4 * zeta2) * (1 + n) ^ 2) ^ (r * 2) :=
        pow_le_pow_left₀ (by positivity) hA _
    _ = (2 * (1 + 4 * zeta2)) ^ (r * 2) * (1 + n) ^ (r * 4) := by
        rw [mul_pow, ← pow_mul]; congr 2; ring
    _ ≤ (2 * (1 + 4 * zeta2)) ^ (r * 2) * (2 ^ (r * 4) * (1 + n ^ (r * 4))) :=
        mul_le_mul_of_nonneg_left (one_add_pow_le hn.le _) (by positivity)
    _ = (2 * (1 + 4 * zeta2)) ^ (r * 2) * 2 ^ (r * 4) * (1 + n ^ expo F) := by
        rw [expo]; ring

/-- **Class-weighted sums over `R ∖ 0`.** -/
theorem summable_class_weight (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (B : SFin 𝔪 k → ℝ)
    (hB0 : ∀ s, 0 ≤ B s) (hB : Summable B) (hB' : Summable fun s => B s * s.norm ^ expo F) :
    Summable (fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      B (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2 *
        ∏ w : InfinitePlace F, ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹) := by
  obtain ⟨K, hK0, hK⟩ := fiber_sum (k := k) h𝔪 g
  set c : {ν : SInt 𝔪 // ν ≠ 0} → SFin 𝔪 k := fun ν => (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2 with hc
  set f : {ν : SInt 𝔪 // ν ≠ 0} → ℝ := fun ν =>
    B (c ν) * ∏ w : InfinitePlace F, ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹ with hf
  have hf0 : ∀ ν, 0 ≤ f ν := fun ν =>
    mul_nonneg (hB0 _) (Finset.prod_nonneg fun w _ => by positivity)
  change Summable f
  rw [← (Equiv.sigmaFiberEquiv c).summable_iff]
  refine (summable_sigma_of_nonneg fun x => hf0 _).2 ⟨fun s => ?_, ?_⟩
  · have := (hK s).1.mul_left (B s)
    refine this.congr fun ν => ?_
    simp only [Equiv.sigmaFiberEquiv_apply, hf]
    rw [show c (ν : {ν : SInt 𝔪 // ν ≠ 0}) = s from ν.2]
  · have hfib : ∀ s : SFin 𝔪 k,
        ∑' ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // c ν = s}, (f ∘ Equiv.sigmaFiberEquiv c) ⟨s, ν⟩ =
          B s * ∑' ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // c ν = s},
            ∏ w : InfinitePlace F,
              ((1 + w (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) ^ 4)⁻¹ := by
      intro s
      rw [← tsum_mul_left]
      refine tsum_congr fun ν => ?_
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, hf]
      rw [show c (ν : {ν : SInt 𝔪 // ν ≠ 0}) = s from ν.2]
    refine Summable.of_nonneg_of_le (fun s => tsum_nonneg fun ν => hf0 _) (fun s => ?_)
      ((hB.mul_left K).add (hB'.mul_left K))
    refine (hfib s).le.trans ?_
    calc B s * ∑' ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // c ν = s},
          ∏ w : InfinitePlace F, ((1 + w (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) ^ 4)⁻¹
        ≤ B s * (K * (1 + s.norm ^ expo F)) := mul_le_mul_of_nonneg_left (hK s).2 (hB0 s)
      _ = K * B s + K * (B s * s.norm ^ expo F) := by ring

end

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.H_SumMain
/-! # WP-HA, file 3: pointwise summability of the two sums of `H0.KPCutNu`

For every `y : SModel 𝔪 k`:

* `summable_forward_coef`: `∑_{ν ∈ R∖0} coef(ν) · fp(sEmb ν + y)` converges absolutely for any
  bounded coefficient function (the support condition `[ν] + y_f = 0` confines `ν` to one class of
  `SFin`, a separated set in the Minkowski space; `κ(t) ≤ C min(t^α, t^{-4})`).
* `summable_reflected_coef`: `∑_{ν ∈ R∖0} coef(ν) · Fm(cl ν, sEmb ν − y)` converges absolutely for
  any bounded coefficient function and any class function `cl`, under the cut's hypotheses on
  `J`, `bf` (used at `σ = 0` and `σ = 4·#places`).
* `summable_forward`, `summable_reflected`: the two families of `KPCutNu` verbatim;
  `summable_forward_kappaB`, `summable_reflected_kappaB`: with `κ = K.kappaB c` and the cut's
  hypotheses exactly. -/

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The decay of `κ` in the form used on the grid. -/
theorem kappa_grid {κ : ℝ → ℝ} {α : ℝ} (hα : 0 ≤ α)
    (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N)))
    {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : ℝ) (n : ℕ), 0 < x → 0 < n → κ (x ^ n * c) ≤ K * ((1 + x) ^ 4)⁻¹ := by
  obtain ⟨C, hC⟩ := hκb 4 (by norm_num)
  set C₀ := max C 0 with hC₀
  have hC0 : 0 ≤ C₀ := le_max_right _ _
  have hM1 : (1 : ℝ) ≤ max 1 (c ^ 4)⁻¹ := le_max_left _ _
  refine ⟨16 * C₀ * max 1 (c ^ 4)⁻¹, by positivity, fun x n hx hn => ?_⟩
  have ht : 0 < x ^ n * c := by positivity
  have hmin0 : 0 ≤ min ((x ^ n * c) ^ α) ((x ^ n * c) ^ (-(4 : ℝ))) :=
    le_min (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)
  have h2 : κ (x ^ n * c) ≤ C₀ * min ((x ^ n * c) ^ α) ((x ^ n * c) ^ (-(4 : ℝ))) :=
    (hC _ ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hmin0)
  have hx4 : 0 < (1 + x) ^ 4 := by positivity
  have hinv : 0 ≤ ((1 + x) ^ 4)⁻¹ := by positivity
  rcases le_total x 1 with hx1 | hx1
  · have hmin1 : min ((x ^ n * c) ^ α) ((x ^ n * c) ^ (-(4 : ℝ))) ≤ 1 := by
      rcases le_total (x ^ n * c) 1 with ht1 | ht1
      · exact (min_le_left _ _).trans (Real.rpow_le_one ht.le ht1 hα)
      · exact (min_le_right _ _).trans
          (Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num))
    have h16 : (1 : ℝ) ≤ 16 * ((1 + x) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hx4]
      have : (1 + x) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      linarith
    calc κ (x ^ n * c) ≤ C₀ * 1 := h2.trans (mul_le_mul_of_nonneg_left hmin1 hC0)
      _ ≤ C₀ * (16 * ((1 + x) ^ 4)⁻¹) := mul_le_mul_of_nonneg_left h16 hC0
      _ ≤ C₀ * (16 * ((1 + x) ^ 4)⁻¹) * max 1 (c ^ 4)⁻¹ :=
          le_mul_of_one_le_right (by positivity) hM1
      _ = 16 * C₀ * max 1 (c ^ 4)⁻¹ * ((1 + x) ^ 4)⁻¹ := by ring
  · have hxn : x ≤ x ^ n := le_self_pow₀ hx1 hn.ne'
    have h4 : (1 + x) ^ 4 / 16 * c ^ 4 ≤ (x ^ n * c) ^ 4 := by
      have ha : (1 + x) ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      have hb : x ^ 4 ≤ (x ^ n) ^ 4 := pow_le_pow_left₀ (by linarith) hxn 4
      have hc4 : 0 < c ^ 4 := by positivity
      rw [mul_pow]
      have : (1 + x) ^ 4 / 16 ≤ (x ^ n) ^ 4 := by
        rw [div_le_iff₀ (by norm_num)]
        calc (1 + x) ^ 4 ≤ (2 * x) ^ 4 := ha
          _ = x ^ 4 * 16 := by ring
          _ ≤ (x ^ n) ^ 4 * 16 := by linarith
      exact mul_le_mul_of_nonneg_right this hc4.le
    have hmin4 : min ((x ^ n * c) ^ α) ((x ^ n * c) ^ (-(4 : ℝ))) ≤
        16 * (c ^ 4)⁻¹ * ((1 + x) ^ 4)⁻¹ := by
      refine (min_le_right _ _).trans ?_
      rw [Real.rpow_neg ht.le, Real.rpow_ofNat]
      have hpos : 0 < (1 + x) ^ 4 / 16 * c ^ 4 := by positivity
      calc ((x ^ n * c) ^ 4)⁻¹ ≤ ((1 + x) ^ 4 / 16 * c ^ 4)⁻¹ := inv_anti₀ hpos h4
        _ = 16 * (c ^ 4)⁻¹ * ((1 + x) ^ 4)⁻¹ := by
            rw [mul_inv, div_eq_mul_inv, mul_inv, inv_inv]; ring
    calc κ (x ^ n * c) ≤ C₀ * (16 * (c ^ 4)⁻¹ * ((1 + x) ^ 4)⁻¹) :=
          h2.trans (mul_le_mul_of_nonneg_left hmin4 hC0)
      _ = 16 * C₀ * ((1 + x) ^ 4)⁻¹ * (c ^ 4)⁻¹ := by ring
      _ ≤ 16 * C₀ * ((1 + x) ^ 4)⁻¹ * max 1 (c ^ 4)⁻¹ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ = 16 * C₀ * max 1 (c ^ 4)⁻¹ * ((1 + x) ^ 4)⁻¹ := by ring

theorem norm_FmOf {κ : ℝ → ℝ} (hκ0 : ∀ t, 0 ≤ κ t) (m : InfinitePlace F → ℤ)
    (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (cl : SFinCls 𝔪 k) (z : SModel 𝔪 k) :
    ‖H0.FmOf κ m J cl z‖ = ‖J cl z.2.2‖ * ∏ w, κ (Real.exp (z.1 w)) := by
  unfold H0.FmOf
  rw [norm_mul, norm_prod]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [norm_mul, L3X.norm_toCircle, one_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 _)]

section general

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {κ : ℝ → ℝ} (hκ0 : ∀ t, 0 ≤ κ t) {α : ℝ}
  (hα : 0 ≤ α)
  (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N)))
  (m : InfinitePlace F → ℤ)

include h𝔪 g hκ0 hα hκb

/-- **Reflected sums converge absolutely** (any bounded coefficients, any class function), under
the cut's hypotheses on `J` and `bf`. -/
theorem summable_reflected_coef_oai (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) {bf : SFin 𝔪 k → ℝ}
    (hJ : ∀ cl y, ‖J cl y‖ ≤ bf y)
    (hbf : ∀ σ : ℝ, 0 ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ))
    (coef : {ν : SInt 𝔪 // ν ≠ 0} → ℂ) {C : ℝ} (hcoef : ∀ ν, ‖coef ν‖ ≤ C)
    (cl : {ν : SInt 𝔪 // ν ≠ 0} → SFinCls 𝔪 k) (y : SModel 𝔪 k) :
    Summable (fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      coef ν * H0.FmOf κ m J (cl ν) (sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y)) := by
  choose Kw hKw0 hKw using fun w : InfinitePlace F => kappa_grid hα hκb (Real.exp_pos (-(y.1 w)))
  have hbf0 : ∀ s, 0 ≤ bf s := fun s => (norm_nonneg (J 0 s)).trans (hJ 0 s)
  set B : SFin 𝔪 k → ℝ := fun s => bf (s - y.2.2) with hB
  have hB0 : ∀ s, 0 ≤ B s := fun s => hbf0 _
  have hs0 : Summable bf := by
    have := hbf 0 le_rfl
    simpa using this
  have hB1 : Summable B := (Equiv.subRight y.2.2).summable_iff.2 hs0
  have hsM : Summable (fun s : SFin 𝔪 k => bf s * s.norm ^ expo F) := by
    have := hbf (expo F : ℝ) (Nat.cast_nonneg _)
    simpa [Real.rpow_natCast] using this
  have hB2 : Summable (fun s => B s * s.norm ^ expo F) := by
    have h1 := ((Equiv.subRight y.2.2).summable_iff.2 hsM).mul_right (y.2.2.norm ^ expo F)
    refine h1.congr fun s => ?_
    simp only [Function.comp_apply, Equiv.subRight_apply, hB]
    have : s.norm = (s - y.2.2).norm * y.2.2.norm := by
      rw [← L3X.SFin.norm_add h𝔪, sub_add_cancel]
    rw [this, mul_pow, mul_assoc]
  have hsum := summable_class_weight h𝔪 g B hB0 hB1 hB2
  refine Summable.of_norm_bounded ((hsum.mul_left (∏ w, Kw w)).mul_left C) fun ν => ?_
  have hν := H0.coe_ne_zero ν
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hcoef ν)
  rw [norm_mul, norm_FmOf hκ0]
  have hP0 : 0 ≤ ∏ w, κ (Real.exp ((sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y).1 w)) :=
    Finset.prod_nonneg fun w _ => hκ0 _
  refine mul_le_mul (hcoef ν) ?_ (mul_nonneg (norm_nonneg _) hP0) hC0
  have hP : ∏ w, κ (Real.exp ((sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y).1 w)) ≤
      (∏ w, Kw w) * ∏ w : InfinitePlace F, ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => hκ0 _) fun w _ => ?_
    have : (sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y).1 w =
        (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).1 w + -(y.1 w) := sub_eq_add_neg _ _
    rw [this, H0.exp_sEmb_fst_add hν]
    exact hKw w _ _ (w.pos_iff.2 hν) InfinitePlace.mult_pos
  have hJ' : ‖J (cl ν) (sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y).2.2‖ ≤
      B (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2 := hJ _ _
  calc ‖J (cl ν) (sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y).2.2‖ *
        ∏ w, κ (Real.exp ((sEmb 𝔪 k ((ν : SInt 𝔪) : F) - y).1 w))
      ≤ B (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2 *
          ((∏ w, Kw w) * ∏ w : InfinitePlace F, ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹) :=
        mul_le_mul hJ' hP hP0 (hB0 _)
    _ = _ := by ring

end general

end

end ArtinKP.H
end

theorem solution.{u_1} : type_of% @ArtinKP.H.summable_reflected_coef_oai.{u_1} := @ArtinKP.H.summable_reflected_coef_oai.{u_1}
