-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:09.655207+00:00
-- url     : https://prove2.me/submissions/b0b91d71-2071-4d26-9082-c340f490eebc

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_GR_secCut_of_isCyclotomicExtension
import Theorems.Thm_ArtinKP_H0_goal_of_KPCut
import Theorems.Thm_ArtinKP_HB_autCut2_of_secCut
import Theorems.Thm_ArtinKP_HB_kpCutNu_of_autCut2

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

theorem SFin.mk_mul (x y : Fˣ) : SFin.mk 𝔪 k (x * y) = SFin.mk 𝔪 k x + SFin.mk 𝔪 k y := rfl

theorem SFin.mk_one : SFin.mk 𝔪 k 1 = 0 := rfl

/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Cut
/-! # WP-H0, file 1: the intermediate cut `KPCut` ("one unknown function `J`")

`KPCut n F ι` is the frozen goal 8b3180bd with
* `κ := K.kappaB c` (`t ↦ t·K_{1/3}(c√t)`), for some `c > 0`;
* `Fm cl y' := J cl y'_f · ∏_w e^{−i m_w θ'_w} κ(e^{x'_w})`, for some `J : SFinCls → SFin → ℂ`
  (it may depend on `m`; signs and constants are absorbed in it);
* a majorant `bf ≥ |J|` with the frozen summability clause, for some `0 < α ≤ 5/6`.

All `let`s of the frozen statement (`lsym … Eloc`, `fp`, `coef`, `Ez`, `D`) are copied verbatim
(generated from the `Theorems/` file by `proofs/kp/scratch/h0/gen_cut.py`).
`KPCutEq` is the variant "the two `tsum`s are equal" (`D ≡ 0`); `KPCutEq → KPCut`. -/

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

theorem KPCut_of_KPCutEq (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (h : KPCutEq n F ι) : KPCut n F ι := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs g => ?_⟩
  obtain ⟨k₀, hk⟩ := hN 𝔪 h𝔪 hs g
  refine ⟨k₀, fun k hk' => ?_⟩
  obtain ⟨c, α, hc, hα, hα', hm⟩ := hk k hk'
  refine ⟨c, α, hc, hα, hα', fun m hm' => ?_⟩
  obtain ⟨J, bf, hJ, hbf, hD⟩ := hm m hm'
  refine ⟨J, bf, hJ, hbf, fun 𝔟 h𝔟 => ?_⟩
  intro κ Fm fp coef Ez D w φ y
  have h0 : ∀ y, D y = 0 := fun y => sub_eq_zero.2 (hD 𝔟 h𝔟 y)
  rw [h0, h0]

end ArtinKP.H0
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

theorem sEmb_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    sEmb 𝔪 k (x * y) = sEmb 𝔪 k x + sEmb 𝔪 k y := by
  rw [sEmb_of_ne (mul_ne_zero hx hy), sEmb_of_ne hx, sEmb_of_ne hy]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext w
    simp only [Prod.fst_add, Pi.add_apply, map_mul]
    rw [Real.log_mul ((map_ne_zero w).2 hx) ((map_ne_zero w).2 hy)]
    ring
  · funext w
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, map_mul]
    exact Complex.arg_mul_coe_angle ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)
  · show SFin.mk 𝔪 k (Units.mk0 (x * y) _) = SFin.mk 𝔪 k _ + SFin.mk 𝔪 k _
    rw [← SFin.mk_mul]
    congr 1
    ext; simp

theorem sEmb_one : sEmb 𝔪 k (1 : F) = 0 := by
  rw [sEmb_of_ne one_ne_zero]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext w; simp
  · funext w; simp
  · show SFin.mk 𝔪 k (Units.mk0 1 _) = 0
    rw [← SFin.mk_one (𝔪 := 𝔪) (k := k)]
    congr 1
    ext; simp

theorem sEmb_pow {x : F} (hx : x ≠ 0) (n : ℕ) : sEmb 𝔪 k (x ^ n) = n • sEmb 𝔪 k x := by
  induction n with
  | zero => simp [sEmb_one]
  | succ n ih => rw [pow_succ, sEmb_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

/-! ### Absolute values and valuations -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Rho
/-! # L3X_Rho: a partition of unity for `Γ = U_S⁶` acting on `SModel 𝔪 k`

* `valF : SFin 𝔪 k → (S_f → ℤ)`, the valuations at `S_f` (they descend from `F^×`).
* `rho0 y = Ω(−log y, val y)` with L3P's fundamental-domain weight; every `U_S`-orbit meets it with
  total weight `|μ_F|`.
* `rho y = |μ_F|⁻¹ Σ_{s ∈ U_S/U_S⁶} rho0 (u_s y)`; then `Σ_{γ ∈ Γ} rho (γ y) = 1`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain NumberField.Units

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem sUnit_ne_zero (ε : SUnit 𝔪) : ((ε : Fˣ) : F) ≠ 0 := (ε : Fˣ).ne_zero

/-! ### The weights -/

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

theorem toCircle_zsmul_add (n : ℤ) (a b : AddCircle (2 * Real.pi)) :
    ((AddCircle.toCircle (n • (a + b)) : Circle) : ℂ) =
      ((AddCircle.toCircle (n • a) : Circle) : ℂ) * ((AddCircle.toCircle (n • b) : Circle) : ℂ) := by
  rw [smul_add, AddCircle.toCircle_add]; rfl

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

theorem coe_eq_gamOf_mul (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ((ν : SInt 𝔪) : F) =
      (((gamOf h𝔪 g ν : SUnit 𝔪) : Fˣ) : F) * (rowElt g (rowOf h𝔪 g ν) : F) := by
  have h := congrArg (fun x : {ν : SInt 𝔪 // ν ≠ 0} => ((x : SInt 𝔪) : F))
    ((rowEquiv h𝔪 g).apply_symm_apply ν)
  exact h.symm

/-! ### Reindexing the two sums of the frozen goal -/

theorem tsum_row_eq {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : RowClass 𝔪 × L3X.Gam 𝔪 → E) :
    ∑' p, f p = ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, f ((rowEquiv h𝔪 g).symm ν) :=
  ((rowEquiv h𝔪 g).symm.tsum_eq f).symm

omit h𝔪 in
/-- Multiplying by `γ ∈ U_S⁶` does not change the class in `SFinCls`. -/
theorem cls_gam_mul (γ : L3X.Gam 𝔪) {x : F} (hx : x ≠ 0) :
    (QuotientAddGroup.mk (sEmb 𝔪 k ((((γ : SUnit 𝔪) : Fˣ) : F) * x)).2.2 : SFinCls 𝔪 k) =
      QuotientAddGroup.mk (sEmb 𝔪 k x).2.2 := by
  obtain ⟨δ, hδ⟩ := γ.2
  have hγ : (((γ : SUnit 𝔪) : Fˣ) : F) = (((δ : Fˣ) : F)) ^ 6 := by
    rw [← hδ]; simp
  rw [L3X.sEmb_mul (L3X.sUnit_ne_zero _) hx, hγ, L3X.sEmb_pow (L3X.sUnit_ne_zero δ)]
  simp only [Prod.snd_add, Prod.smul_snd, QuotientAddGroup.mk_add]
  rw [add_eq_right, QuotientAddGroup.eq_zero_iff]
  exact ⟨_, rfl⟩

/-- **The forward sum of the frozen goal as a sum over `ν ∈ R ∖ 0`** (summands verbatim). -/
theorem tsum_forward (coef : RowClass 𝔪 → ℂ) (fp : SModel 𝔪 k → ℂ) (y : SModel 𝔪 k) :
    ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
        coef p.1 * fp (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y) =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        coef (rowOf h𝔪 g ν) * fp (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y) := by
  rw [tsum_row_eq h𝔪 g]
  refine tsum_congr fun ν => ?_
  rw [coe_eq_gamOf_mul h𝔪 g ν]
  rfl

/-- **The reflected sum of the frozen goal as a sum over `ν ∈ R ∖ 0`** (summands verbatim, with
`b` for `g.gen 𝔟`): the frequency is `ν / b²`. -/
theorem tsum_reflected (Ez : RowClass 𝔪 → ℂ) (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) {b : F}
    (hb : b ≠ 0) (y : SModel 𝔪 k) :
    ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
        Ez p.1 * Fm (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / b ^ 2)).2.2)
          (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * ((rowElt g p.1 : F) / b ^ 2)) - y) =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        Ez (rowOf h𝔪 g ν) * Fm (QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / b ^ 2)).2.2)
          (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / b ^ 2) - y) := by
  rw [tsum_row_eq h𝔪 g]
  refine tsum_congr fun ν => ?_
  have hr : (rowElt g (rowOf h𝔪 g ν) : F) ≠ 0 := by
    intro h0
    exact coe_ne_zero ν (by rw [coe_eq_gamOf_mul h𝔪 g ν, h0, mul_zero])
  have hx : (rowElt g (rowOf h𝔪 g ν) : F) / b ^ 2 ≠ 0 := div_ne_zero hr (pow_ne_zero _ hb)
  rw [coe_eq_gamOf_mul h𝔪 g ν, mul_div_assoc, cls_gam_mul (gamOf h𝔪 g ν) hx]
  rfl

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

/-! ### `SFinCls` -/

/-! ### Angular characters and rotations -/

theorem prod_toCircle_rot (m : InfinitePlace F → ℤ) (θ : InfinitePlace F → AddCircle (2 * Real.pi))
    (r : InfinitePlace F → ℂ) (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) :
    ∏ x, ((AddCircle.toCircle (m x • (θ x +
        (Pi.single w φ : InfinitePlace F → AddCircle (2 * Real.pi)) x)) : Circle) : ℂ) * r x =
      ((AddCircle.toCircle (m w • φ) : Circle) : ℂ) *
        ∏ x, ((AddCircle.toCircle (m x • θ x) : Circle) : ℂ) * r x := by
  have h1 : ∏ x, ((AddCircle.toCircle (m x •
      (Pi.single w φ : InfinitePlace F → AddCircle (2 * Real.pi)) x) : Circle) : ℂ) =
      ((AddCircle.toCircle (m w • φ) : Circle) : ℂ) := by
    rw [Finset.prod_eq_single w]
    · rw [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ w) h
  rw [Finset.prod_congr rfl (fun x _ => by rw [L3X.toCircle_zsmul_add]),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, h1, Finset.prod_mul_distrib]
  ring

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ)

/-- The forward function is of pure angular type `m`. -/
theorem fpF_add_rot (y : SModel 𝔪 k) (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) :
    L3X.fpF κ m (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)) =
      ((AddCircle.toCircle (m w • φ) : Circle) : ℂ) * L3X.fpF κ m y := by
  unfold L3X.fpF
  have h2 : (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)).2.2 = y.2.2 := by simp
  have h1 : ∀ x, (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)).1 x = y.1 x := fun x => by simp
  have h3 : ∀ x, (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)).2.1 x =
      y.2.1 x + (Pi.single w φ : InfinitePlace F → AddCircle (2 * Real.pi)) x := fun x => rfl
  simp only [h1, h2, h3]
  split_ifs
  · exact prod_toCircle_rot m _ _ w φ
  · rw [mul_zero]

/-- The product-form reflected function is of pure angular type `−m`. -/
theorem FmOf_sub_rot (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (cl : SFinCls 𝔪 k) (y : SModel 𝔪 k)
    (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) :
    FmOf κ m J cl (y - ((0, Pi.single w φ, 0) : SModel 𝔪 k)) =
      ((AddCircle.toCircle (m w • φ) : Circle) : ℂ) * FmOf κ m J cl y := by
  have hy : y - ((0, Pi.single w φ, 0) : SModel 𝔪 k) =
      y + ((0, Pi.single w (-φ), 0) : SModel 𝔪 k) := by
    rw [sub_eq_add_neg]
    congr 1
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    simp [Pi.single_neg]
  rw [hy]
  unfold FmOf
  have h2 : (y + ((0, Pi.single w (-φ), 0) : SModel 𝔪 k)).2.2 = y.2.2 := by simp
  have h1 : ∀ x, (y + ((0, Pi.single w (-φ), 0) : SModel 𝔪 k)).1 x = y.1 x := fun x => by simp
  have h3 : ∀ x, (y + ((0, Pi.single w (-φ), 0) : SModel 𝔪 k)).2.1 x =
      y.2.1 x + (Pi.single w (-φ) : InfinitePlace F → AddCircle (2 * Real.pi)) x := fun x => rfl
  simp only [h1, h2, h3]
  rw [prod_toCircle_rot (fun x => -m x) _ _ w (-φ), neg_smul_neg]
  ring

/-! ### The two functions at `sEmb ν ± y` -/

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.T12.L3X_Rot
/-! # L3X_Rot: the angular cancellation of the constant terms (`eq:reflection-angular-cancellation`)

If `D` is radial at the place `w₀` and the angular type of `L` at `w₀` is `±1`, then
`∫ Φ D dμ_a = 0`: rotating `y` by `π` at `w₀` preserves `μ_a`, `ρ`, `1_B([y])` and `D`, and
multiplies `L(y)⁻¹` by `−1`. No integrability is needed.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem toCircle_pi_zsmul {n : ℤ} (hn : n = 1 ∨ n = -1) :
    ((AddCircle.toCircle (n • ((Real.pi : ℝ) : AddCircle (2 * Real.pi))) : Circle) : ℂ) = -1 := by
  rw [← AddCircle.coe_zsmul, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  have h2 : 2 * Real.pi / (2 * Real.pi) = 1 := div_self (by positivity)
  rw [h2, one_mul]
  rcases hn with rfl | rfl
  · simp [Complex.exp_pi_mul_I]
  · simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_one, neg_mul, one_mul, Complex.ofReal_neg]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Rot
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty
/-! # WP-H0, file 5: for the product form, "radial difference" is the same as "equal sums"

For the product-form `Fm` both sums of the frozen goal are of pure angular type `m` in `y`
(`Dcut_add_rot`), so their difference is rotation invariant only if it vanishes:
`KPCut ↔ KPCutEq`. The automorphic packages therefore have to prove the exact identity of the two
`tsum`s; there is no slack in the "radial constant term" variant. -/

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- Both sums are of pure angular type `m`. -/
theorem Dcut_add_rot (g : AllowedGen ι 𝔪) (coef Ez : RowClass 𝔪 → ℂ) (κ : ℝ → ℝ)
    (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (b : F) (y : SModel 𝔪 k)
    (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) :
    Dcut g coef Ez (L3X.fpF κ m) (FmOf κ m J) b (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)) =
      ((AddCircle.toCircle (m w • φ) : Circle) : ℂ) *
        Dcut g coef Ez (L3X.fpF κ m) (FmOf κ m J) b y := by
  unfold Dcut
  rw [mul_sub, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  · refine tsum_congr fun p => ?_
    rw [← add_assoc, fpF_add_rot]
    ring
  · refine tsum_congr fun p => ?_
    rw [← sub_sub, FmOf_sub_rot]
    ring

/-- A rotation-invariant difference vanishes. -/
theorem Dcut_eq_zero (g : AllowedGen ι 𝔪) (coef Ez : RowClass 𝔪 → ℂ) (κ : ℝ → ℝ)
    (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (b : F) (y : SModel 𝔪 k)
    (w : InfinitePlace F) (hm : m w = 1 ∨ m w = -1)
    (h : Dcut g coef Ez (L3X.fpF κ m) (FmOf κ m J) b
        (y + ((0, Pi.single w ((Real.pi : ℝ) : AddCircle (2 * Real.pi)), 0) : SModel 𝔪 k)) =
      Dcut g coef Ez (L3X.fpF κ m) (FmOf κ m J) b y) :
    Dcut g coef Ez (L3X.fpF κ m) (FmOf κ m J) b y = 0 := by
  rw [Dcut_add_rot, L3X.toCircle_pi_zsmul hm] at h
  have : (2 : ℂ) * Dcut g coef Ez (L3X.fpF κ m) (FmOf κ m J) b y = 0 := by
    linear_combination -h
  simpa using this

theorem KPCutEq_of_KPCut (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (h : KPCut n F ι) : KPCutEq n F ι := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs g => ?_⟩
  obtain ⟨k₀, hk⟩ := hN 𝔪 h𝔪 hs g
  refine ⟨k₀, fun k hk' => ?_⟩
  obtain ⟨c, α, hc, hα, hα', hm⟩ := hk k hk'
  refine ⟨c, α, hc, hα, hα', fun m hm' => ?_⟩
  obtain ⟨J, bf, hJ, hbf, hD⟩ := hm m hm'
  refine ⟨J, bf, hJ, hbf, fun 𝔟 h𝔟 => ?_⟩
  intro κ Fm fp coef Ez y
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h3 : Dcut g coef Ez (L3X.fpF (K.kappaB c) m) (FmOf (K.kappaB c) m J) (g.gen 𝔟 : F)
      (y + ((0, Pi.single w₀ ((Real.pi : ℝ) : AddCircle (2 * Real.pi)), 0) : SModel 𝔪 k)) =
      Dcut g coef Ez (L3X.fpF (K.kappaB c) m) (FmOf (K.kappaB c) m J) (g.gen 𝔟 : F) y :=
    hD 𝔟 h𝔟 w₀ _ y
  have h4 := Dcut_eq_zero g coef Ez _ m J _ y w₀ (hm' w₀) h3
  rw [Dcut] at h4
  exact sub_eq_zero.1 h4

theorem KPCut_iff_KPCutEq (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    KPCut n F ι ↔ KPCutEq n F ι :=
  ⟨KPCutEq_of_KPCut n F ι, KPCut_of_KPCutEq n F ι⟩

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H0_Nu
/-! # WP-H0, file 6: the cut as an identity of sums over `ν ∈ R ∖ 0`, with named local data

`KPCutNu` is the form of the cut the automorphic packages should prove: with the top-level
definitions `L3X.coefF'`, `L3V.Eprod` (definitionally the frozen `coef`, `Ez`), `L3X.fpF`, `FmOf`,
and the two sums indexed by nonzero `S`-integers:

  `∑_{ν ∈ R∖0} c⁺_𝔟(ν) f⁺(ν y) = ∑_{ν ∈ R∖0} c⁻_𝔟(ν) Fm([ν/b²], (ν/b²)/y)`,  `b = gen 𝔟`.

`KPCutNu ↔ KPCutEq ↔ KPCut`, and `goal_of_KPCutNu` is the frozen goal from it. -/

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem cut_sums_iff (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (h𝔟 : IsExterior 𝔪 𝔟)
    (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (y : SModel 𝔪 k) :
    (∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
        L3X.coefF' g 𝔟 p.1 *
          L3X.fpF κ m (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y) =
      ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
        L3V.Eprod g (⟨𝔟, h𝔟⟩, 1) p.1 *
          FmOf κ m J (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) *
              ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)) - y)) ↔
    (∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        L3X.coefF' g 𝔟 (rowOf h𝔪 g ν) * L3X.fpF κ m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y) =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        L3V.Eprod g (⟨𝔟, h𝔟⟩, 1) (rowOf h𝔪 g ν) *
          FmOf κ m J
            (QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) - y)) := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  have hb : (g.gen 𝔟 : F) ≠ 0 := L3P.gen_ne_zero g ⟨𝔟, h𝔟⟩
  rw [tsum_forward h𝔪 g, tsum_reflected h𝔪 g _ _ hb]

theorem KPCutEq_iff_KPCutNu (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    KPCutEq n F ι ↔ KPCutNu n F ι := by
  constructor
  · rintro ⟨N₀, hN⟩
    refine ⟨N₀, fun 𝔪 h𝔪 hs g => ?_⟩
    obtain ⟨k₀, hk⟩ := hN 𝔪 h𝔪 hs g
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, α, hc, hα, hα', hm⟩ := hk k hk'
    refine ⟨c, α, hc, hα, hα', fun m hm' => ?_⟩
    obtain ⟨J, bf, hJ, hbf, hD⟩ := hm m hm'
    exact ⟨J, bf, hJ, hbf, fun 𝔟 h𝔟 y =>
      (cut_sums_iff h𝔪 g 𝔟 h𝔟 (K.kappaB c) m J y).1 (hD 𝔟 h𝔟 y)⟩
  · rintro ⟨N₀, hN⟩
    refine ⟨N₀, fun 𝔪 h𝔪 hs g => ?_⟩
    obtain ⟨k₀, hk⟩ := hN 𝔪 h𝔪 hs g
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, α, hc, hα, hα', hm⟩ := hk k hk'
    refine ⟨c, α, hc, hα, hα', fun m hm' => ?_⟩
    obtain ⟨J, bf, hJ, hbf, hD⟩ := hm m hm'
    exact ⟨J, bf, hJ, hbf, fun 𝔟 h𝔟 y =>
      (cut_sums_iff h𝔪 g 𝔟 h𝔟 (K.kappaB c) m J y).2 (hD 𝔟 h𝔟 y)⟩

theorem KPCut_iff_KPCutNu (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    KPCut n F ι ↔ KPCutNu n F ι :=
  (KPCut_iff_KPCutEq n F ι).trans (KPCutEq_iff_KPCutNu n F ι)

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.GR_Main
/-! # WP-GR, file 4: the final assembly

* `weylFlip`: the named hypothesis `GR.WeylFlip` discharged by `GW.weyl_flip_thetaT`.
* **`secCut : HB.SecCut n F ι`** — `c = 4π`, `α = 1/4`, `J = GK.Jdef hG hz6 Φ₀`,
  `bf = GK.bfdef hG hz6 Φ₀ k`, `Θ = GR.ThetaG hG hz6 m Φ₀`, `k₀` a deep level of the symbol package.
* `autCut2`, `kpCutNu`, and **`goal`**: the frozen statement 8b3180bd, written out (checked against the stub in `GR_Check`).
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.G2a

noncomputable section

/-- `HB.AutCut2` (the repaired automorphic contract). -/
theorem autCut2 (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    HB.AutCut2 n F ι :=
  HB.autCut2_of_secCut n hn0 hn F ι (secCut_of_isCyclotomicExtension n hn0 hn F ι)

/-- The intermediate cut `H0.KPCutNu`. -/
theorem kpCutNu (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    H0.KPCutNu n F ι :=
  HB.kpCutNu_of_autCut2 n hn0 hn F ι (autCut2 n hn0 hn F ι)

end

end ArtinKP.GR

namespace ArtinKP.GR

open UniqueFactorizationMonoid

open Classical in
/-- **The frozen goal 8b3180bd** (the Kazhdan–Patterson cubic theta leaf), with the statement of the
published `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`
written out; `GR_Check` checks the two statements agree (`type_of%`). -/
theorem goal (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    let lsym : Ideal (𝓞 F) → F → ℂ := fun P t =>
      if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yz.2 : F) * t = (yz.1 : F) then
        sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
      else 0
    let ladd : Ideal (𝓞 F) → F → ℂ := fun P w =>
      if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
        sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
      else 0
    let Wv : Ideal (𝓞 F) → ℕ → ℂ := fun P e =>
      if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
      else if e % 3 = 1 then
        (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
      else 0
    let Wsph : Ideal (𝓞 F) → ℤ → F → ℂ := fun P e₀ t =>
      if e₀ < 0 then 0 else lsym P t ^ (2 * e₀.toNat) * Wv P e₀.toNat
    let tau : Ideal (𝓞 F) → ℕ → ℂ := fun P j =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
          sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))
    let mask : (P : Ideal (𝓞 F)) → ℕ → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P j v =>
        if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
        else (tau P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j
    let Wweyl : (P : Ideal (𝓞 F)) → ℤ → F → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P e₀ t v =>
        if e₀ + 2 < 0 then 0 else
          Wv P (e₀ + 2).toNat * lsym P t ^ (4 + 2 * (e₀ + 2).toNat) *
            sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
            ladd P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    let Eloc : Ideal (𝓞 F) → ℕ → ℤ → F → ℂ := fun P k e₀ t =>
      if k = 0 then Wsph P e₀ t else
        ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
          mask P (k % 6) v * (if v = 0 then Wsph P e₀ t else Wweyl P e₀ t v)
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (κ : ℝ → ℝ) (cκ Aκ α : ℝ), Measurable κ ∧ 0 < cκ ∧ 0 < Aκ ∧ 0 < α ∧ (∀ t, 0 ≤ κ t) ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (κ t : ℂ)) s ∧
        mellin (fun t => (κ t : ℂ)) s =
          (cκ : ℂ) * (Aκ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ c, Measurable (Fm c)) ∧ (∀ y, 0 ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
      (∀ w c y, ContDiff ℝ 2 (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ w c y, ∀ j : ℕ, j ≤ 2 →
        ‖iteratedDeriv j (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k))) 0‖ ≤
          C * (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) * bf y.2.2) ∧
    ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 →
    let fp : SModel 𝔪 k → ℂ := fun y =>
      if y.2.2 = 0 then
        ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
      else 0
    let coef : RowClass 𝔪 → ℂ := fun z =>
      residueSymbol ι 𝔪 𝔟 (rowElt g z) *
        ∏ P ∈ (normalizedFactors z.1.1).toFinset,
          Wsph P ((normalizedFactors z.1.1).count P : ℤ)
            ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))
    let Ez : RowClass 𝔪 → ℂ := fun z =>
      (∏ P ∈ (normalizedFactors (z.1.1 * 𝔟)).toFinset,
        Eloc P ((normalizedFactors 𝔟).count P)
          (((normalizedFactors z.1.1).count P : ℤ) -
            2 * ((normalizedFactors 𝔟).count P : ℤ))
          ((rowElt g z : F) / (g.gen 𝔟 : F) ^ 2 *
            (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
              2 * ((normalizedFactors 𝔟).count P : ℤ)))))
    let D : SModel 𝔪 k → ℂ := fun y =>
      (∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          coef p.1 * fp (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y)) -
        ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          Ez p.1 * Fm (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)) - y)
    ∀ (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) (y : SModel 𝔪 k),
      D (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)) = D y :=
  H0.goal_of_KPCut n hn0 hn F ι ((H0.KPCut_iff_KPCutNu n F ι).2 (kpCutNu n hn0 hn F ι))

end ArtinKP.GR
end

theorem solution.{u_1} : type_of% @ArtinKP.GR.goal.{u_1} := @ArtinKP.GR.goal.{u_1}
