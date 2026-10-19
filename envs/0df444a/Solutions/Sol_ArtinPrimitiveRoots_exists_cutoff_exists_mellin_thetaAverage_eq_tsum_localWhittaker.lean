-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T12:16:31.208956+00:00
-- url     : https://prove2.me/submissions/ecf657f3-0116-4294-8cf7-5dc9ec1a3cb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_digitSum_eq_mul_localSymbol_pow
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_finite_sFinCls_and_exists_addSubgroup_mem_iff_mem_range_pow_six
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_sChar_sEmb_gen_eq_thetaChar_mul_residueSymbol
import Mathlib

section
section
/-! # L3X_Cut: the two candidate cuts under 93d56f1c

* `L3X_CutKP`: Prop 5.1 (Kazhdan–Patterson cubic theta) evaluated on the torus–digit family
  `g(y, v)` and its Weyl translate, digit-masked, on the model `SModel 𝔪 k` of `F_S^× / U`:
  the difference of the forward and the reflected nonconstant Fourier expansions is the
  difference of the two constant terms, hence radial at every complex place.
* `L3X_CutSB`: the `S`-classes of §3 at level `k`: finiteness of `F_S^×/F_S^{×6}` and the subgroup
  `B` (the classes of allowed generators, a complement of `E = [U_S]`, with `U_S/U_S⁶ ↪ E`).
* `L3X_CutSL`: the characters `L_υ = L_S λ_ε` with `L_υ(gen 𝔄) = ϑ(𝔄) χ_𝔄(ε)` (Lemma 3.4,
  (3.13), (3.4)).
-/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-- The `S`-classes of §3 at level `k`: `F_S^×/F_S^{×6}` is finite, and it has a subgroup `B` (the
complement `B′` of `E = [U_S]` containing the classes of the allowed generators, L3V.md) with
`[ε gen 𝔄] ∈ B ⟺ ε ∈ U_S⁶` (this uses `U_S/U_S⁶ ↪ E`). -/
def L3X_CutSB (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      Finite (SFinCls 𝔪 k) ∧
      ∃ B : AddSubgroup (SFinCls 𝔪 k), ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪,
        ((QuotientAddGroup.mk (sEmb 𝔪 k ((ε : Fˣ) * (g.gen 𝔄 : F))).2.2 : SFinCls 𝔪 k) ∈ B ↔
          ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)

/-- The `S`-characters `L_υ = L_S λ_ε` of (3.13) and (6.2) at level `k`: unitary characters of the model,
radially trivial, of angular type `±1` at each complex place, trivial on `U_S`, with
`L_υ(gen 𝔄) = ϑ(𝔄) χ_𝔄(ε)` (Lemma 3.4, (3.13), (3.4)). -/
def L3X_CutSL (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ υ : SClass 𝔪, ∃ (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ),
        (∀ w, m w = 1 ∨ m w = -1) ∧ (∀ a b, Lf (a + b) = Lf a * Lf b) ∧ (∀ a, ‖Lf a‖ = 1) ∧
        let L : SModel 𝔪 k → ℂ := fun y =>
          Lf y.2.2 * ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ)
        (∀ ε : SUnit 𝔪, L (sEmb 𝔪 k ((ε : Fˣ) : F)) = 1) ∧
        ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 →
          L (sEmb 𝔪 k (g.gen 𝔄 : F)) = χ.thetaChar g 𝔄 * residueSymbol ι 𝔪 𝔄 υ.rep

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3J_Cut: the corrected KP cut

`L3J_CutKP` is `L3X_CutKP` (= the published 95871697) with `0 < N →` added to the two decay
clauses (κ and the derivatives of `Fm`), as in every other stub of the Lemma 6.3 chain. The
published form is false (`L3J_False`). -/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
def L3J_CutKP (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
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
      D (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)) = D y

end ArtinPrimitiveRoots

end
end

section
section
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

instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

instance instDiscrSFin : DiscreteMeasurableSpace (SFin 𝔪 k) := ⟨fun _ => trivial⟩

theorem countable_field (F : Type*) [Field F] [NumberField F] : Countable F := by
  have b := Module.finBasis ℚ F
  exact b.equivFun.injective.countable

instance instCountableSFin : Countable (SFin 𝔪 k) := by
  have := countable_field F
  have : Countable Fˣ := Function.Injective.countable (f := fun u : Fˣ => (u : F))
    Units.val_injective
  have : Countable (Fˣ ⧸ SLevel 𝔪 k) := (QuotientGroup.mk_surjective).countable
  exact Countable.of_equiv (Fˣ ⧸ SLevel 𝔪 k) Additive.ofMul

/-! ### The finite norm -/

theorem SFin.norm_mk (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm = ∏ᶠ v ∈ placesOf 𝔪, NumberField.HeightOneSpectrum.adicAbv F v (x : F) :=
  rfl

theorem SFin.mk_mul (x y : Fˣ) : SFin.mk 𝔪 k (x * y) = SFin.mk 𝔪 k x + SFin.mk 𝔪 k y := rfl

theorem SFin.mk_one : SFin.mk 𝔪 k 1 = 0 := rfl

theorem SFin.mk_surjective : Function.Surjective (SFin.mk 𝔪 k) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
  exact ⟨x, by simp only [SFin.mk, hx]; rfl⟩

theorem finite_placesOf (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  have := (Ideal.finite_factors h𝔪)
  refine this.subset fun v hv => ?_
  simp only [placesOf, Set.mem_ofPred_eq] at hv
  simpa [Set.mem_ofPred_eq] using Ideal.dvd_iff_le.mpr hv


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

theorem SFin.norm_zero (h𝔪 : 𝔪 ≠ ⊥) : (0 : SFin 𝔪 k).norm = 1 := by
  rw [← SFin.mk_one, SFin.norm_mk_eq_prod h𝔪]
  simp

theorem SFin.norm_neg (h𝔪 : 𝔪 ≠ ⊥) (y : SFin 𝔪 k) : (-y).norm = y.norm⁻¹ := by
  have h := SFin.norm_add h𝔪 y (-y)
  rw [add_neg_cancel, SFin.norm_zero h𝔪] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-! ### `lnorm` -/

/-- `log |y|_S`. -/
noncomputable def lnorm (y : SModel 𝔪 k) : ℝ := ∑ w, y.1 w + Real.log y.2.2.norm

theorem lnorm_add (h𝔪 : 𝔪 ≠ ⊥) (y z : SModel 𝔪 k) : lnorm (y + z) = lnorm y + lnorm z := by
  simp only [lnorm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib,
    SFin.norm_add h𝔪, Real.log_mul (SFin.norm_pos h𝔪 _).ne' (SFin.norm_pos h𝔪 _).ne']
  ring

theorem lnorm_zero (h𝔪 : 𝔪 ≠ ⊥) : lnorm (0 : SModel 𝔪 k) = 0 := by
  simp [lnorm, SFin.norm_zero h𝔪]

theorem lnorm_neg (h𝔪 : 𝔪 ≠ ⊥) (y : SModel 𝔪 k) : lnorm (-y) = -lnorm y := by
  have := lnorm_add h𝔪 y (-y)
  rw [add_neg_cancel, lnorm_zero h𝔪] at this
  linarith

theorem lnorm_sub (h𝔪 : 𝔪 ≠ ⊥) (y z : SModel 𝔪 k) : lnorm (y - z) = lnorm y - lnorm z := by
  rw [sub_eq_add_neg, lnorm_add h𝔪, lnorm_neg h𝔪]; ring

/-! ### Slices -/

variable (w₀ : InfinitePlace F)

/-- The other infinite places. -/
abbrev Wo : Type _ := {w : InfinitePlace F // w ≠ w₀}

/-- The vector with `w₀`-coordinate `t` and the other coordinates `x'`. -/
def ext (x' : Wo w₀ → ℝ) (t : ℝ) : InfinitePlace F → ℝ :=
  fun w => if h : w = w₀ then t else x' ⟨w, h⟩

theorem ext_self (x' : Wo w₀ → ℝ) (t : ℝ) : ext w₀ x' t w₀ = t := by simp [ext]

theorem ext_of_ne (x' : Wo w₀ → ℝ) (t : ℝ) {w : InfinitePlace F} (h : w ≠ w₀) :
    ext w₀ x' t w = x' ⟨w, h⟩ := by simp [ext, h]

theorem sum_eq_add_sum_Wo (x : InfinitePlace F → ℝ) :
    ∑ w, x w = x w₀ + ∑ w : Wo w₀, x w := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)]
  congr 1
  rw [Finset.sum_subtype (Finset.univ.erase w₀) (p := fun w => w ≠ w₀) (by simp)]

theorem measurable_ext : Measurable fun p : (Wo w₀ → ℝ) × ℝ => ext w₀ p.1 p.2 := by
  refine measurable_pi_lambda _ fun w => ?_
  by_cases h : w = w₀
  · simp only [ext, h, dite_true]; exact measurable_snd
  · simp only [ext, h, dite_false]
    exact (measurable_pi_apply _).comp measurable_fst

/-- The base space of a sheet. -/
abbrev Base (𝔪 : Ideal (𝓞 F)) (k : ℕ) : Type _ :=
  SFin 𝔪 k × ((Wo w₀ → ℝ) × (InfinitePlace F → AddCircle (2 * Real.pi)))

/-- Counting ⊗ Lebesgue ⊗ Haar. -/
noncomputable def baseMeasure (𝔪 : Ideal (𝓞 F)) (k : ℕ) : Measure (Base w₀ 𝔪 k) :=
  Measure.count.prod volume

/-- The slice map onto the sheet `lnorm = a`. -/
noncomputable def slice (a : ℝ) (p : Base w₀ 𝔪 k) : SModel 𝔪 k :=
  (ext w₀ p.2.1 (a - Real.log p.1.norm - ∑ w, p.2.1 w), p.2.2, p.1)

/-- The sheet measure on `X_{e^a}`. -/
noncomputable def shMeasure (𝔪 : Ideal (𝓞 F)) (k : ℕ) (a : ℝ) : Measure (SModel 𝔪 k) :=
  (baseMeasure w₀ 𝔪 k).map (slice w₀ a)

theorem measurable_slice (a : ℝ) : Measurable (slice (𝔪 := 𝔪) (k := k) w₀ a) := by
  have h1 : Measurable fun p : Base w₀ 𝔪 k => Real.log p.1.norm :=
    (measurable_of_countable (fun y : SFin 𝔪 k => Real.log y.norm)).comp measurable_fst
  refine Measurable.prodMk ?_ (Measurable.prodMk (measurable_snd.comp measurable_snd)
    measurable_fst)
  refine (measurable_ext w₀).comp (Measurable.prodMk (measurable_fst.comp measurable_snd) ?_)
  refine (measurable_const.sub h1).sub ?_
  exact Finset.measurable_sum _ fun w _ =>
    (measurable_pi_apply w).comp (measurable_fst.comp measurable_snd)

theorem slice_add_single (a t : ℝ) (p : Base w₀ 𝔪 k) :
    slice w₀ (a + t) p = slice w₀ a p + ((Pi.single w₀ t, 0, 0) : SModel 𝔪 k) := by
  simp only [slice, Prod.mk_add_mk, add_zero]
  congr 1
  funext w
  by_cases h : w = w₀
  · subst h; simp [ext_self]; ring
  · simp [ext_of_ne w₀ _ _ h, h]


/-! ### Measure preservation -/

instance : MeasurableAdd (SFin 𝔪 k) :=
  ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩

instance : MeasurableNeg (SFin 𝔪 k) := ⟨measurable_of_countable _⟩

instance : MeasurableAdd₂ (SFin 𝔪 k) := ⟨measurable_of_countable _⟩

instance instMeasurableAddSModel : MeasurableAdd (SModel 𝔪 k) := by
  constructor
  · intro c
    exact (measurable_fst.const_add c.1).prodMk
      (((measurable_fst.comp measurable_snd).const_add c.2.1).prodMk
        ((measurable_snd.comp measurable_snd).const_add c.2.2))
  · intro c
    exact (measurable_fst.add_const c.1).prodMk
      (((measurable_fst.comp measurable_snd).add_const c.2.1).prodMk
        ((measurable_snd.comp measurable_snd).add_const c.2.2))

instance instMeasurableNegSModel : MeasurableNeg (SModel 𝔪 k) := by
  constructor
  exact measurable_fst.neg.prodMk ((measurable_fst.comp measurable_snd).neg.prodMk
    (measurable_snd.comp measurable_snd).neg)

/-- Translation of the base by `d`. -/
def shiftB (d : SModel 𝔪 k) (p : Base w₀ 𝔪 k) : Base w₀ 𝔪 k :=
  (p.1 + d.2.2, (p.2.1 + fun w : Wo w₀ => d.1 w, p.2.2 + d.2.1))

theorem mp_shiftB (d : SModel 𝔪 k) :
    MeasurePreserving (shiftB (𝔪 := 𝔪) (k := k) w₀ d) (baseMeasure w₀ 𝔪 k)
      (baseMeasure w₀ 𝔪 k) := by
  have h1 : MeasurePreserving (fun y : SFin 𝔪 k => y + d.2.2) Measure.count Measure.count :=
    measurePreserving_add_right _ _
  have h2 : MeasurePreserving (fun x : Wo w₀ → ℝ => x + fun w : Wo w₀ => d.1 w) volume volume :=
    measurePreserving_add_right _ _
  have h3 : MeasurePreserving (fun θ : InfinitePlace F → AddCircle (2 * Real.pi) => θ + d.2.1)
      volume volume :=
    measurePreserving_add_right _ _
  exact h1.prod (h2.prod h3)

/-- Negation of the base. -/
def negB (p : Base w₀ 𝔪 k) : Base w₀ 𝔪 k := (-p.1, (-p.2.1, -p.2.2))

theorem mp_negB :
    MeasurePreserving (negB (𝔪 := 𝔪) (k := k) w₀) (baseMeasure w₀ 𝔪 k) (baseMeasure w₀ 𝔪 k) := by
  have h1 : MeasurePreserving (fun y : SFin 𝔪 k => -y) Measure.count Measure.count :=
    Measure.measurePreserving_neg _
  have h2 : MeasurePreserving (fun x : Wo w₀ → ℝ => -x) volume volume :=
    Measure.measurePreserving_neg _
  have : (volume : Measure (InfinitePlace F → AddCircle (2 * Real.pi))).IsNegInvariant := by
    rw [volume_pi]; exact Measure.pi.isNegInvariant _
  have h3 : MeasurePreserving (fun θ : InfinitePlace F → AddCircle (2 * Real.pi) => -θ)
      volume volume :=
    Measure.measurePreserving_neg _
  exact h1.prod (h2.prod h3)

theorem slice_add (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (d : SModel 𝔪 k) (p : Base w₀ 𝔪 k) :
    slice w₀ a p + d = slice w₀ (a + lnorm d) (shiftB w₀ d p) := by
  refine Prod.ext ?_ rfl
  funext w
  simp only [slice, shiftB, Prod.fst_add, Pi.add_apply]
  rw [SFin.norm_add h𝔪, Real.log_mul (SFin.norm_pos h𝔪 _).ne' (SFin.norm_pos h𝔪 _).ne']
  by_cases h : w = w₀
  · subst h
    simp only [ext_self, lnorm, Finset.sum_add_distrib, Pi.add_apply]
    rw [sum_eq_add_sum_Wo w d.1]
    ring
  · simp only [ext_of_ne w₀ _ _ h, Pi.add_apply]

theorem slice_neg (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (p : Base w₀ 𝔪 k) :
    -slice w₀ a p = slice w₀ (-a) (negB w₀ p) := by
  refine Prod.ext ?_ rfl
  funext w
  simp only [slice, negB, Prod.fst_neg, Pi.neg_apply]
  rw [SFin.norm_neg h𝔪, Real.log_inv]
  by_cases h : w = w₀
  · subst h
    simp only [ext_self, Pi.neg_apply, Finset.sum_neg_distrib]
    ring
  · simp only [ext_of_ne w₀ _ _ h, Pi.neg_apply]

theorem map_shMeasure_add (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (d : SModel 𝔪 k) :
    (shMeasure w₀ 𝔪 k a).map (· + d) = shMeasure w₀ 𝔪 k (a + lnorm d) := by
  rw [shMeasure, Measure.map_map (measurable_add_const d) (measurable_slice w₀ a)]
  have : (fun y => y + d) ∘ slice w₀ a = slice w₀ (a + lnorm d) ∘ shiftB w₀ d := by
    funext p; exact slice_add w₀ h𝔪 a d p
  rw [this, ← Measure.map_map (measurable_slice w₀ _) (mp_shiftB w₀ d).measurable,
    (mp_shiftB w₀ d).map_eq, shMeasure]

theorem map_shMeasure_neg (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) :
    (shMeasure w₀ 𝔪 k a).map Neg.neg = shMeasure w₀ 𝔪 k (-a) := by
  rw [shMeasure, Measure.map_map measurable_neg (measurable_slice w₀ a)]
  have : Neg.neg ∘ slice (𝔪 := 𝔪) (k := k) w₀ a = slice w₀ (-a) ∘ negB w₀ := by
    funext p; exact slice_neg w₀ h𝔪 a p
  rw [this, ← Measure.map_map (measurable_slice w₀ _) (mp_negB w₀).measurable,
    (mp_negB w₀).map_eq, shMeasure]

theorem mp_add (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (d : SModel 𝔪 k) :
    MeasurePreserving (· + d) (shMeasure w₀ 𝔪 k a) (shMeasure w₀ 𝔪 k (a + lnorm d)) :=
  ⟨measurable_add_const d, map_shMeasure_add w₀ h𝔪 a d⟩

theorem mp_neg (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) :
    MeasurePreserving (Neg.neg : SModel 𝔪 k → SModel 𝔪 k) (shMeasure w₀ 𝔪 k a)
      (shMeasure w₀ 𝔪 k (-a)) :=
  ⟨measurable_neg, map_shMeasure_neg w₀ h𝔪 a⟩

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-!
# L3P_Sfin: the finite places of `S`, combinatorially

`S` a finite type with `q v > 1`. For `j : S → ℤ`, `NN j = ∏ q_v^{j_v}`. The weight
`Om j = Σ_{e ⊆ S} (−1)^{|e|} 1[j + 1_e ≥ 0] / NN (j + 1_e)` is the profile of the Fourier transform
of `∏_v 1_{𝒪_v^×}` (self-dual normalisation), and
`Σ_j Om j · NN j^{1−z} = ∏_v (1 − q_v^{z−1}) / (1 − q_v^{−z})` for `Re z > 0`.
-/

namespace ArtinPrimitiveRoots.L3P

open scoped BigOperators Classical

set_option linter.unusedSectionVars false

/-! ### Products of geometric series over `S → ℕ` -/

/-! ### The weight `Om` -/

section Om

variable {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ)

/-- `log q_v`. -/
noncomputable def lq (v : S) : ℝ := Real.log (q v)

/-- `NN j = ∏ q_v^{j_v} = exp (Σ j_v log q_v)`. -/
noncomputable def NN (j : S → ℤ) : ℝ := Real.exp (∑ v, (j v : ℝ) * lq q v)

variable (hq : ∀ v, 1 < q v)
include hq

end Om

end ArtinPrimitiveRoots.L3P

end
end

section
section
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

/-- `count_v (x)`. -/
noncomputable def ordv (v : HeightOneSpectrum (𝓞 F)) (x : F) : ℤ :=
  FractionalIdeal.count F v (spanSingleton (𝓞 F)⁰ x)

theorem spanSingleton_ne_zero {x : F} (hx : x ≠ 0) : spanSingleton (𝓞 F)⁰ x ≠ 0 :=
  (spanSingleton_eq_zero_iff).not.2 hx

theorem ordv_algebraMap (v : HeightOneSpectrum (𝓞 F)) {r : 𝓞 F} (hr : r ≠ 0) :
    ordv v (algebraMap (𝓞 F) F r) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors : ℤ) := by
  rw [ordv, ← coeIdeal_span_singleton, count_coe F v]
  rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]

theorem ordv_mul (v : HeightOneSpectrum (𝓞 F)) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordv v (x * y) = ordv v x + ordv v y := by
  rw [ordv, ← spanSingleton_mul_spanSingleton, count_mul F v (spanSingleton_ne_zero hx)
    (spanSingleton_ne_zero hy)]
  rfl

theorem ordv_inv (v : HeightOneSpectrum (𝓞 F)) (x : F) : ordv v x⁻¹ = -ordv v x := by
  rw [ordv, ← spanSingleton_inv, count_inv]; rfl

theorem ordv_one (v : HeightOneSpectrum (𝓞 F)) : ordv v (1 : F) = 0 := by
  rw [ordv, spanSingleton_one, count_one]

theorem valuation_eq_exp_neg_ordv (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F x = WithZero.exp (-ordv v x) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl; simp at hx
  have hrK : algebraMap (𝓞 F) F r ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  have hsK : algebraMap (𝓞 F) F s ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  rw [div_eq_mul_inv, map_mul, map_inv₀, valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_if_neg _ hr0, intValuation_if_neg _ hs0, ordv_mul v hrK (inv_ne_zero hsK),
    ordv_inv, ordv_algebraMap v hr0, ordv_algebraMap v hs0, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr 1; ring

theorem valuation_le_one_iff (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F x ≤ 1 ↔ 0 ≤ ordv v x := by
  rw [valuation_eq_exp_neg_ordv v hx, ← WithZero.exp_zero, WithZero.exp_le_exp, neg_nonpos]

/-- For nonzero fractional ideals, `I ≤ J ↔ ∀ v, count_v J ≤ count_v I`. -/
theorem le_iff_count {I J : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum (𝓞 F), count F v J ≤ count F v I := by
  constructor
  · intro h v; exact count_mono F v hI h
  · intro h
    set K := I * J⁻¹
    have hK : K ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
    have hcount : ∀ v, 0 ≤ count F v K := fun v => by
      rw [count_mul F v hI (inv_ne_zero hJ), count_inv]; linarith [h v]
    have hpow : ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v K =
        coeIdealHom (𝓞 F)⁰ F (v.asIdeal ^ (count F v K).toNat) := fun v => by
      rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hcount v)]; rfl
    have hKle : K ≤ 1 := by
      rw [← finprod_heightOneSpectrum_factorization' F hK]
      simp_rw [hpow]
      have e := MonoidHom.map_finprod_of_injective (coeIdealHom (𝓞 F)⁰ F).toMonoidHom
        coeIdeal_injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ (count F v K).toNat)
      calc _ = (coeIdealHom (𝓞 F)⁰ F) (∏ᶠ v : HeightOneSpectrum (𝓞 F),
            v.asIdeal ^ (count F v K).toNat) := e.symm
        _ ≤ 1 := coeIdeal_le_one
    have : I = K * J := by
      simp only [K]; rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    rw [this]
    calc K * J ≤ 1 * J := mul_le_mul_left hKle J
      _ = J := one_mul J

theorem eq_of_count_eq {I J : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), count F v I = count F v J) : I = J :=
  le_antisymm ((le_iff_count hI hJ).2 fun v => (h v).ge) ((le_iff_count hJ hI).2 fun v => (h v).le)

theorem mem_iff_count {x : F} (hx : x ≠ 0) {J : FractionalIdeal (𝓞 F)⁰ F} (hJ : J ≠ 0) :
    x ∈ J ↔ ∀ v : HeightOneSpectrum (𝓞 F), count F v J ≤ ordv v x := by
  rw [← spanSingleton_le_iff_mem, le_iff_count (spanSingleton_ne_zero hx) hJ]; rfl

theorem ordv_add_ge (v : HeightOneSpectrum (𝓞 F)) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (ordv v x) (ordv v y) ≤ ordv v (x + y) := by
  have h := Valuation.map_add (v.valuation F) x y
  rw [valuation_eq_exp_neg_ordv v hx, valuation_eq_exp_neg_ordv v hy,
    valuation_eq_exp_neg_ordv v hxy] at h
  rcases le_total (ordv v x) (ordv v y) with hle | hle
  · rw [min_eq_left hle]
    rw [max_eq_left (WithZero.exp_le_exp.2 (neg_le_neg hle))] at h
    have := WithZero.exp_le_exp.1 h; linarith
  · rw [min_eq_right hle]
    rw [max_eq_right (WithZero.exp_le_exp.2 (neg_le_neg hle))] at h
    have := WithZero.exp_le_exp.1 h; linarith

/-- In a nonzero fractional ideal, the count is attained. -/
theorem exists_mem_ordv_eq {J : FractionalIdeal (𝓞 F)⁰ F} (hJ : J ≠ 0)
    (w : HeightOneSpectrum (𝓞 F)) : ∃ x ∈ J, x ≠ 0 ∧ ordv w x = count F w J := by
  have hw0 : (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 w.ne_bot
  have hJw : J * w.asIdeal ≠ 0 := mul_ne_zero hJ hw0
  have hne : ¬ J ≤ J * w.asIdeal := by
    intro h
    have := count_mono F w hJ h
    rw [count_mul F w hJ hw0, count_self] at this
    linarith
  rw [SetLike.not_le_iff_exists] at hne
  obtain ⟨x, hxJ, hxJw⟩ := hne
  have hx0 : x ≠ 0 := by rintro rfl; exact hxJw (zero_mem _)
  refine ⟨x, hxJ, hx0, le_antisymm ?_ (((mem_iff_count hx0 hJ).1 hxJ) w)⟩
  by_contra hlt
  push Not at hlt
  apply hxJw
  rw [mem_iff_count hx0 hJw]
  intro v
  rw [count_mul F v hJ hw0, count_maximal]
  split_ifs with hvw
  · subst hvw; linarith
  · rw [add_zero]; exact (mem_iff_count hx0 hJ).1 hxJ v

/-! ### The places of `S` -/

variable {𝔪 : Ideal (𝓞 F)}

/-- The finite places of `S`, as a type. -/
abbrev SP (𝔪 : Ideal (𝓞 F)) : Type _ := ↥(placesOf 𝔪)

theorem mem_SInt_iff {x : F} (hx : x ≠ 0) :
    x ∈ (placesOf 𝔪).integer F ↔ ∀ v ∉ placesOf 𝔪, 0 ≤ ordv v x := by
  change (∀ v ∉ placesOf 𝔪, v.valuation F x ≤ 1) ↔ _
  simp only [valuation_le_one_iff _ hx]

/-- The prime `v` as a unit fractional ideal. -/
noncomputable def primeU (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) (coeIdeal_ne_zero.2 v.ne_bot)

/-- The valuation vector at `S`. -/
noncomputable def valS (x : F) : SP 𝔪 → ℤ := fun v => ordv v.1 x

variable [Fintype (SP 𝔪)]

/-- `P^k = ∏_{v ∈ S} 𝔭_v^{k_v}`. -/
noncomputable def Pk (k : SP 𝔪 → ℤ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := ∏ v : SP 𝔪, primeU v.1 ^ k v

theorem coe_Pk (k : SP 𝔪 → ℤ) :
    ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      ∏ v : SP 𝔪, (v.1.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ k v := by
  rw [Pk, Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val]
  rfl

theorem Pk_ne_zero (k : SP 𝔪 → ℤ) :
    ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := (Pk k).ne_zero

theorem count_Pk (k : SP 𝔪 → ℤ) (w : HeightOneSpectrum (𝓞 F)) :
    count F w ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      if h : w ∈ placesOf 𝔪 then k ⟨w, h⟩ else 0 := by
  rw [coe_Pk, count_prod F w _ _ fun v _ => zpow_ne_zero _ (coeIdeal_ne_zero.2 v.1.ne_bot)]
  simp_rw [count_zpow, count_maximal]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨w, h⟩]
    · simp
    · intro v _ hv
      have : v.1 ≠ w := fun e => hv (Subtype.ext e)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun v _ => ?_
    have : v.1 ≠ w := fun e => h (e ▸ v.2)
    simp [this]

omit [Fintype (SP 𝔪)] in
/-- Elements of `𝔟 R` have `w`-adic order at least `count_w 𝔟` outside `S`. -/
theorem ordv_ge_of_mem_map (𝔟 : Ideal (𝓞 F)) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ placesOf 𝔪)
    {y : SInt 𝔪} (hy : y ∈ 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) (hy0 : (y : F) ≠ 0) :
    count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ ordv w (y : F) := by
  suffices h : ∀ y ∈ 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪)), (y : F) = 0 ∨
      count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ ordv w (y : F) from (h y hy).resolve_left hy0
  intro y hy
  rw [Ideal.map, Ideal.span] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    by_cases hb0 : b = 0
    · left; simp [hb0]
    · right
      have hbK : algebraMap (𝓞 F) F b ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      have h1 : spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F b) ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [spanSingleton_le_iff_mem]; exact mem_coeIdeal_of_mem _ hb
      have h2 := count_mono F w (spanSingleton_ne_zero hbK) h1
      exact h2
  | zero => left; rfl
  | add x y _ _ hx hy =>
    by_cases hx0 : (x : F) = 0
    · have : ((x + y : SInt 𝔪) : F) = (y : F) := by simp [hx0]
      rw [this]; exact hy
    by_cases hy0 : (y : F) = 0
    · have : ((x + y : SInt 𝔪) : F) = (x : F) := by simp [hy0]
      rw [this]; exact hx
    by_cases hxy : ((x + y : SInt 𝔪) : F) = 0
    · left; exact hxy
    right
    have h1 := hx.resolve_left hx0
    have h2 := hy.resolve_left hy0
    have hxy' : (x : F) + (y : F) ≠ 0 := by simpa using hxy
    have := ordv_add_ge w hx0 hy0 hxy'
    simp only [Subalgebra.coe_add]
    exact (le_min h1 h2).trans this
  | smul r x _ hx =>
    by_cases h0 : ((r • x : SInt 𝔪) : F) = 0
    · left; exact h0
    right
    have hrx : ((r • x : SInt 𝔪) : F) = (r : F) * (x : F) := rfl
    rw [hrx] at h0 ⊢
    have hr0 : (r : F) ≠ 0 := left_ne_zero_of_mul h0
    have hx0 : (x : F) ≠ 0 := right_ne_zero_of_mul h0
    rw [ordv_mul w hr0 hx0]
    have hr : 0 ≤ ordv w (r : F) := (mem_SInt_iff hr0).1 r.2 w hw
    linarith [hx.resolve_left hx0]

omit [Fintype (SP 𝔪)] in
theorem count_eq_zero_of_exterior {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ placesOf 𝔪) : count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
  rw [count_coe F w h𝔟.1, Nat.cast_eq_zero]
  by_contra hc
  have hdvd := (Associates.count_ne_zero_iff_dvd h𝔟.1 w.irreducible).1 hc
  have h1 : 𝔟 ≤ w.asIdeal := Ideal.le_of_dvd hdvd
  have h2 : 𝔟 ⊔ 𝔪 ≤ w.asIdeal := sup_le h1 hw
  rw [h𝔟.2, top_le_iff] at h2
  exact w.isPrime.ne_top h2

omit [Fintype (SP 𝔪)] in
theorem ne_zero_of_span_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) : (m : F) ≠ 0 := by
  intro h0
  have hm0 : m = 0 := Subtype.ext h0
  rw [hm0, Ideal.span_singleton_eq_bot.2 rfl] at hm
  apply h𝔟.1
  rw [eq_bot_iff]
  intro b hb
  have : algebraMap (𝓞 F) (SInt 𝔪) b ∈ (⊥ : Ideal (SInt 𝔪)) := hm ▸ Ideal.mem_map_of_mem _ hb
  rw [Ideal.mem_bot] at this
  have h2 : algebraMap (𝓞 F) F b = 0 := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) this
    simpa using this
  rw [Ideal.mem_bot]
  exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h2

/-- `m R = 𝔟 R` with `𝔟` exterior gives `(m) = 𝔟 · P^{val_S m}` as fractional ideals of `𝓞`. -/
theorem spanSingleton_eq_mul_Pk {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    spanSingleton (𝓞 F)⁰ (m : F) =
      (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * ((Pk (valS (𝔪 := 𝔪) (m : F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
  have hm0 := ne_zero_of_span_eq h𝔟 hm
  have h𝔟0 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 h𝔟.1
  refine eq_of_count_eq (spanSingleton_ne_zero hm0) (mul_ne_zero h𝔟0 (Pk_ne_zero _)) fun w => ?_
  rw [count_mul F w h𝔟0 (Pk_ne_zero _), count_Pk]
  change ordv w (m : F) = _
  split_ifs with hw
  · rw [count_eq_zero_of_exterior h𝔟 hw, zero_add]; rfl
  · rw [add_zero]
    refine le_antisymm ?_ (ordv_ge_of_mem_map 𝔟 hw (hm ▸ Ideal.mem_span_singleton_self m) hm0)
    obtain ⟨x, hx, hx0, hxo⟩ := exists_mem_ordv_eq h𝔟0 w
    obtain ⟨b, hb, rfl⟩ := (mem_coeIdeal _).1 hx
    have hbm : algebraMap (𝓞 F) (SInt 𝔪) b ∈ Ideal.span {m} := hm ▸ Ideal.mem_map_of_mem _ hb
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hbm
    have hrF : (r : F) * (m : F) = algebraMap (𝓞 F) F b := by
      have := congrArg (fun z : SInt 𝔪 => (z : F)) hr
      simpa using this
    have hr0 : (r : F) ≠ 0 := by
      intro h; rw [h, zero_mul] at hrF; exact hx0 hrF.symm
    rw [← hxo, ← hrF, ordv_mul w hr0 hm0]
    have := (mem_SInt_iff hr0).1 r.2 w hw
    linarith

/-- `q_v = N 𝔭_v`. -/
noncomputable def qS (v : SP 𝔪) : ℝ := (Ideal.absNorm v.1.asIdeal : ℝ)

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

theorem valS_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    valS (𝔪 := 𝔪) (x * y) = valS x + valS y := funext fun v => ordv_mul v.1 hx hy

theorem isExterior_top : IsExterior 𝔪 (⊤ : Ideal (𝓞 F)) := ⟨top_ne_bot, top_sup_eq _⟩

theorem unit_ne_zero (ε : (SInt 𝔪)ˣ) : ((ε : SInt 𝔪) : F) ≠ 0 := by
  intro h; exact ε.ne_zero (Subtype.ext h)

end ArtinPrimitiveRoots.L3P

end
end

section
section
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

theorem sEmb_inv {x : F} (hx : x ≠ 0) : sEmb 𝔪 k x⁻¹ = -sEmb 𝔪 k x := by
  have h := sEmb_mul (𝔪 := 𝔪) (k := k) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, sEmb_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem sEmb_div {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    sEmb 𝔪 k (x / y) = sEmb 𝔪 k x - sEmb 𝔪 k y := by
  rw [div_eq_mul_inv, sEmb_mul hx (inv_ne_zero hy), sEmb_inv hy, sub_eq_add_neg]

theorem sEmb_pow {x : F} (hx : x ≠ 0) (n : ℕ) : sEmb 𝔪 k (x ^ n) = n • sEmb 𝔪 k x := by
  induction n with
  | zero => simp [sEmb_one]
  | succ n ih => rw [pow_succ, sEmb_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

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

/-- `S`-units have norm one. -/
theorem lnorm_sEmb_unit (h𝔪 : 𝔪 ≠ ⊥) (ε : SUnit 𝔪) : lnorm (sEmb 𝔪 k ((ε : Fˣ) : F)) = 0 := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  set u : (SInt 𝔪)ˣ := Set.unitEquivUnitsInteger (placesOf 𝔪) F ε
  have hu : (((u : SInt 𝔪)) : F) = ((ε : Fˣ) : F) := rfl
  have hspan : Ideal.span {(u : SInt 𝔪)} = (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_top, Ideal.span_singleton_eq_top]; exact u.isUnit
  rw [← hu, lnorm_sEmb_gen h𝔪 L3P.isExterior_top hspan, Ideal.absNorm_top]
  simp

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

lemma sAddChar_congr {𝔪 : Ideal (𝓞 F)} (x x' : F)
    (H : ∀ y : F, (x - y ∈ (placesOf 𝔪).integer F) ↔ (x' - y ∈ (placesOf 𝔪).integer F)) :
    sAddChar 𝔪 x = sAddChar 𝔪 x' := by
  classical
  let G : (F → Prop) → ℂ := fun p => if h : ∃ y, p y then
    Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F h.choose : ℚ) : ℂ)) else 0
  have e1 : sAddChar 𝔪 x = G (fun y => x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  have e2 : sAddChar 𝔪 x' = G (fun y => x' - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  rw [e1, e2]
  congr 1
  funext y
  exact propext (and_congr_left' (H y))

/-- `e` is invariant under translation by `R`. -/
lemma sAddChar_add_mem {𝔪 : Ideal (𝓞 F)} (x r : F) (hr : r ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 (x + r) = sAddChar 𝔪 x := by
  have key : ∀ y : F, (x + r - y ∈ (placesOf 𝔪).integer F) ↔ (x - y ∈ (placesOf 𝔪).integer F) := by
    intro y
    constructor
    · intro h
      have := sub_mem h hr
      rwa [show x + r - y - r = x - y by ring] at this
    · intro h
      have := add_mem h hr
      rwa [show x - y + r = x + r - y by ring] at this
  exact sAddChar_congr _ _ key

/-- `e` is trivial on `R`. -/
lemma sAddChar_of_mem {𝔪 : Ideal (𝓞 F)} (x : F) (hx : x ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 x = 1 := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 :=
    ⟨0, by simpa using hx, fun v _ => by simp⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set y := hex.choose
  have hy : y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem hx h1
    rwa [sub_sub_cancel] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact h2 v hv
    · exact hy v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F y hall
  have htr : Algebra.trace ℚ F y = ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [← hz, Algebra.coe_trace_int]
  rw [htr]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [← this]
  congr 1
  push_cast
  ring

/-- The generator of the unit ideal is a unit of `R`. -/
lemma isUnit_gen_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    IsUnit (g.gen ⊤) := by
  have h := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.map_top] at h
  exact Ideal.span_singleton_eq_top.mp h

lemma div_gen_top_mem {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) : x / (g.gen ⊤ : F) ∈ (placesOf 𝔪).integer F := by
  obtain ⟨u, hu⟩ := isUnit_gen_top g
  have hinv : ((↑(u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = ((g.gen ⊤ : SInt 𝔪) : F)⁻¹ := by
    rw [← hu]
    have h1 : ((↑u : SInt 𝔪) : F) * ((↑(u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
    exact (eq_inv_of_mul_eq_one_right h1)
  rw [div_eq_mul_inv, ← hinv]
  exact mul_mem hx (SetLike.coe_mem _)

lemma subsingleton_quot_top {𝔪 : Ideal (𝓞 F)} :
    Subsingleton (SInt 𝔪 ⧸ (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [Ideal.map_top]
  infer_instance

lemma finsum_quot_top {𝔪 : Ideal (𝓞 F)}
    (f : SInt 𝔪 ⧸ (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) → ℂ) :
    ∑ᶠ x, f x = f 0 := by
  have := subsingleton_quot_top (𝔪 := 𝔪)
  exact finsum_eq_single f 0 (fun x hx => absurd (Subsingleton.elim x 0) hx)

lemma normalizedFactors_top : normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
  rw [← Ideal.one_eq_top, normalizedFactors_one]

lemma residueSymbol_top (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 ⊤ x = 1 := by
  simp [residueSymbol, normalizedFactors_top]

lemma gaussPhase_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (j : ℕ) :
    gaussPhase g j ⊤ = 1 := by
  rw [gaussPhase, finsum_quot_top, residueSymbol_top, one_pow, one_mul,
    sAddChar_of_mem _ (div_gen_top_mem g _ (SetLike.coe_mem _))]
  simp [Ideal.absNorm_top]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

lemma sexticResidueSymbol_eq_of_mk_eq (ι : F →+* ℂ) (P : Ideal (𝓞 F)) (x y : SInt 𝔪)
    (h : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x =
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :
    sexticResidueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P y := by
  unfold sexticResidueSymbol
  rw [h]

lemma residueSymbol_congr (ι : F →+* ℂ) (𝔞 : Ideal (𝓞 F)) (x y : SInt 𝔪)
    (h : x - y ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    residueSymbol ι 𝔪 𝔞 x = residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  apply sexticResidueSymbol_eq_of_mk_eq
  rw [Ideal.Quotient.eq]
  exact Ideal.map_mono (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)) h

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma gen_ne_zero (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    ((g.gen I : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have h0' : g.gen I = 0 := Subtype.ext h0
  have hs := g.span_gen I hI
  rw [h0', Ideal.span_singleton_eq_bot.mpr rfl] at hs
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
  have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ ha
  rw [← hs, Ideal.mem_bot] at this
  apply ha0
  have := congrArg (fun z : SInt 𝔪 => (z : F)) this
  simp only [coe_algebraMap_SInt, ZeroMemClass.coe_zero] at this
  exact_mod_cast this

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

lemma val_alg (a : 𝓞 F) : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a :=
  v.valuation_of_algebraMap a

lemma le_of_mul_le_mul_ne {a b c : ℤᵐ⁰} (h : a * c ≤ b * c) (hc : c ≠ 0) : a ≤ b := by
  have := mul_le_mul_right h c⁻¹
  rwa [mul_comm c⁻¹, mul_comm c⁻¹, mul_inv_cancel_right₀ hc, mul_inv_cancel_right₀ hc] at this

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact ⟨top_ne_bot, top_sup_eq _⟩
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `x` has a witness in the definition of `sAddChar`. -/
def HasWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧ ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1

/-- The value of `e` through any witness. -/
lemma sAddChar_eq_of_wit {x y : F} (h1 : x - y ∈ (placesOf 𝔪).integer F)
    (h2 : ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) :
    sAddChar 𝔪 x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F y : ℚ) : ℂ)) := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 := ⟨y, h1, h2⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨k1, k2⟩ := hex.choose_spec
  set y' := hex.choose
  have hd : y' - y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem h1 k1
    rwa [show x - y - (x - y') = y' - y by ring] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y' - y) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact (Valuation.map_sub _ _ _).trans (max_le (k2 v hv) (h2 v hv))
    · exact hd v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hall
  have htr : Algebra.trace ℚ F y' = Algebra.trace ℚ F y + ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [Algebra.coe_trace_int, show ((z : 𝓞 F) : F) = algebraMap (𝓞 F) F z from rfl, hz, map_sub]
    ring
  rw [htr]
  push_cast
  rw [mul_add, Complex.exp_add]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℂ) =
      ((-(Algebra.trace ℤ (𝓞 F) z) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring, this,
    mul_one]

/-- `e` is additive on elements with witnesses. -/
lemma sAddChar_add {x x' : F} (h : HasWit 𝔪 x) (h' : HasWit 𝔪 x') :
    sAddChar 𝔪 (x + x') = sAddChar 𝔪 x * sAddChar 𝔪 x' := by
  obtain ⟨y, hy1, hy2⟩ := h
  obtain ⟨y', hy1', hy2'⟩ := h'
  have hs1 : x + x' - (y + y') ∈ (placesOf 𝔪).integer F := by
    rw [show x + x' - (y + y') = (x - y) + (x' - y') by ring]; exact add_mem hy1 hy1'
  have hs2 : ∀ v ∈ placesOf 𝔪, v.valuation F (y + y') ≤ 1 :=
    fun v hv => (Valuation.map_add _ _ _).trans (max_le (hy2 v hv) (hy2' v hv))
  rw [sAddChar_eq_of_wit hs1 hs2, sAddChar_eq_of_wit hy1 hy2, sAddChar_eq_of_wit hy1' hy2',
    ← Complex.exp_add, map_add]
  push_cast
  ring_nf

/-- A witness exists when `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
lemma hasWit_of_mul_mem (x : F) (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤)
    (hx : ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F) : HasWit 𝔪 x := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨i, hi, w, hw, hiw⟩ := hcop.exists
  refine ⟨x * algebraMap (𝓞 F) F w, ?_, fun v hv => ?_⟩
  · have hw' : algebraMap (𝓞 F) F w = 1 - algebraMap (𝓞 F) F i := by
      rw [← map_one (algebraMap (𝓞 F) F), ← hiw, map_add]; ring
    have : x - x * algebraMap (𝓞 F) F w = x * algebraMap (𝓞 F) F i := by
      rw [hw']; ring
    rw [this]; exact hx i hi
  · have hvm : 𝔪 ≤ v.asIdeal := hv
    -- `d ∉ v^N`
    have hdN : d ∉ v.asIdeal ^ N := by
      intro hmem
      have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
      have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [map_pow] at hdvd
      have hN0 : N ≠ 0 := by
        rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
      have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
        have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
        have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
        omega
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
      have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
      have h4 : N < 2 ^ N := Nat.lt_two_pow_self
      omega
    have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
    have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
      rw [val_alg, v.intValuation_le_pow_iff_mem]
      exact Ideal.pow_right_mono hvm N hw
    have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
    have hxd : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
      rw [← hbd, div_mul_cancel₀]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
    have key : v.valuation F (x * algebraMap (𝓞 F) F w) * v.valuation F (algebraMap (𝓞 F) F d) ≤
        1 * v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [← map_mul, show x * algebraMap (𝓞 F) F w * algebraMap (𝓞 F) F d =
        algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [← hxd]; ring, map_mul]
      calc v.valuation F (algebraMap (𝓞 F) F b) * v.valuation F (algebraMap (𝓞 F) F w)
          ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) :=
            mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
        _ = _ := rfl
    exact le_of_mul_le_mul_ne key hdpos

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L3P_Char: the archimedean phase is the `S`-character

For `z` in the trace dual of an exterior ideal `𝔫` (and `S ⊇` the primes of the different),
`exp(2πi Tr z) = e(−z)` with `e = sAddChar 𝔪`: write `z = y + r` with `y ∈ 𝔫⁻¹` integral at `S` and
`r ∈ 𝔇⁻¹`, so `Tr r ∈ ℤ` and `r ∈ R`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical Real

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Dil: positive dilations of the mixed space

For `x : realSpace K`, `dilV x = mixedSpaceOfRealSpace (expMap x)` has coordinates
`exp(x_w / mult w) > 0`. Multiplication by it is a linear automorphism of determinant
`exp (∑ w, x w)` (for `K` totally complex), and it rescales the Fourier transform.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

/-- The positive point `(exp(x_w / mult w))_w` of the mixed space. -/
noncomputable def dilV (x : realSpace K) : mixedSpace K := mixedSpaceOfRealSpace (expMap x)

theorem dilV_fst (x : realSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (dilV x).1 w = Real.exp ((w.1.mult : ℝ)⁻¹ * x w) := by
  simp [dilV, mixedSpaceOfRealSpace_apply, expMap_apply]

theorem dilV_snd (x : realSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    (dilV x).2 w = (Real.exp ((w.1.mult : ℝ)⁻¹ * x w) : ℂ) := by
  simp [dilV, mixedSpaceOfRealSpace_apply, expMap_apply]

theorem dilV_add (x x' : realSpace K) : dilV (x + x') = dilV x * dilV x' := by
  ext w
  · simp only [dilV_fst, Prod.fst_mul, Pi.mul_apply, Pi.add_apply, mul_add, Real.exp_add]
  · simp only [dilV_snd, Prod.snd_mul, Pi.mul_apply, Pi.add_apply, mul_add, Real.exp_add,
      Complex.ofReal_mul]

theorem dilV_zero : dilV (0 : realSpace K) = 1 := by
  ext w
  · simp [dilV_fst]
  · simp [dilV_snd]

theorem dilV_mul_neg (x : realSpace K) : dilV x * dilV (-x) = 1 := by
  rw [← dilV_add, add_neg_cancel, dilV_zero]

/-- Multiplication by `a`, as a linear map. -/
noncomputable def mulL (a : mixedSpace K) : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  LinearMap.mulLeft ℝ a

@[simp] theorem mulL_apply (a z : mixedSpace K) : mulL a z = a * z := rfl

/-- Multiplication by an invertible `a`, as a continuous linear equivalence. -/
noncomputable def mulE (a b : mixedSpace K) (hab : a * b = 1) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  LinearEquiv.toContinuousLinearEquiv
    { mulL a with
      invFun := fun z => b * z
      left_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc,
          mul_comm b a, hab, one_mul]
      right_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc, hab,
          one_mul] }

@[simp] theorem mulE_apply (a b : mixedSpace K) (hab : a * b = 1) (z : mixedSpace K) :
    mulE a b hab z = a * z := rfl

/-- Multiplication by `dilV x`, as a continuous linear equivalence. -/
noncomputable def dilE (x : realSpace K) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  mulE (dilV x) (dilV (-x)) (dilV_mul_neg x)

@[simp] theorem dilE_apply (x : realSpace K) (z : mixedSpace K) : dilE x z = dilV x * z := rfl

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Pois: Poisson summation over a fractional ideal, dilated and translated

From the library's lattice Poisson formula (4bf11d4c) and the trace dual of an ideal lattice
(9fd5cbc5): for a fractional ideal `I`, a Schwartz function `φ` on the mixed space, a positive
dilation `x` and a translation `t ∈ K`,
`∑_{a ∈ I} φ(y_x (t + a)) = (covol I · e^{Σx})⁻¹ ∑_{η ∈ I^∨} φ̂(y_x⁻¹ η) e(Tr(t η))`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L2B_Quot: exterior ideals of `𝓞 F` and of `R` (copied from L2A_FSQuot, prover A, to decouple)

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,

-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

end ArtinPrimitiveRoots.L2B

end
end

section
section
/-!
# L3P_Lat: the lattices `P^k`, their cosets mod `𝔫`, and summability

* `summable_schwartz_lattice`: a Schwartz function is summable over a translated ideal lattice.
* `exists_rep`: every class of `R / 𝔫R` has a representative in `P^k`.
* `sub_mem_mul_Pk`, `mem_map_of_mem_mul_Pk`: `P^k ∩ 𝔫R = 𝔫 P^k`.
* `tsum_Pk_eq_sum_cosets`: a lattice sum over `P^k` splits over the classes of `R / 𝔫R`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  FractionalIdeal
open scoped nonZeroDivisors Classical Real SchwartzMap

set_option linter.unusedSectionVars false

/-! ### Summability over ideal lattices -/

section summ

variable {K : Type*} [Field K] [NumberField K]

end summ

/-! ### Coset representatives -/

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Test: radial test functions on the mixed space

A smooth compactly supported `Φ` on `realSpace K` (log coordinates `mult w · log ‖z_w‖`) gives the
radial test function `phiF Φ` on the mixed space: smooth, compactly supported, vanishing near the
coordinate hyperplanes. Its Fourier transform is radial as well, `fourierM (phiF Φ) z = PhiHat Φ
(logM z)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

/-- Log coordinates of a point of the mixed space. -/
noncomputable def logM (z : mixedSpace K) : realSpace K :=
  fun w => (w.mult : ℝ) * Real.log (normAtPlace w z)

/-- Log coordinates of an element of `K`. -/
noncomputable def logK (m : K) : realSpace K := logM (mixedEmbedding K m)

theorem logK_apply (m : K) (w : InfinitePlace K) : logK m w = (w.mult : ℝ) * Real.log (w m) := by
  simp [logK, logM, normAtPlace_apply]

/-- The radial test function attached to `Φ`. -/
noncomputable def phiF (Φ : realSpace K → ℝ) (z : mixedSpace K) : ℂ :=
  if ∀ w, normAtPlace w z ≠ 0 then (Φ (logM z) : ℂ) else 0

theorem phiF_of_ne {Φ : realSpace K → ℝ} {z : mixedSpace K} (hz : ∀ w, normAtPlace w z ≠ 0) :
    phiF Φ z = Φ (logM z) := if_pos hz

section smooth

variable [IsTotallyComplex K]

theorem normAtPlace_eq_norm_snd (w : InfinitePlace K) (z : mixedSpace K) :
    normAtPlace w z = ‖z.2 ⟨w, IsTotallyComplex.isComplex w⟩‖ :=
  normAtPlace_apply_of_isComplex (IsTotallyComplex.isComplex w) z

theorem contDiffAt_logM {z : mixedSpace K} (hz : ∀ w, normAtPlace w z ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (logM (K := K)) z := by
  refine contDiffAt_pi.2 fun w => ?_
  have hw := hz w
  rw [normAtPlace_eq_norm_snd] at hw
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : mixedSpace K => ‖z.2 ⟨w, IsTotallyComplex.isComplex w⟩‖)
      z := by
    have hn := contDiffAt_norm ℝ (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (norm_ne_zero_iff.1 hw)
    have hp : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : mixedSpace K => z.2 ⟨w, IsTotallyComplex.isComplex w⟩) :=
      (contDiff_apply ℝ ℂ _).comp contDiff_snd
    exact hn.comp z hp.contDiffAt
  have h2 := (Real.contDiffAt_log.2 hw).comp z h1
  have h3 := contDiffAt_const (c := (w.mult : ℝ)).mul h2
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)
  simp only [logM, normAtPlace_eq_norm_snd, Function.comp_apply]

variable {Φ : realSpace K → ℝ}

theorem exists_bound_of_hasCompactSupport (hΦ : HasCompactSupport Φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ b, R < ‖b‖ → Φ b = 0 := by
  obtain ⟨R, hR⟩ := hΦ.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun b hb => ?_⟩
  by_contra h
  have := hR (subset_tsupport _ h)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R 1]

theorem phiF_eventually_zero (hΦ : HasCompactSupport Φ) {z : mixedSpace K}
    (hz : ¬ ∀ w, normAtPlace w z ≠ 0) : phiF Φ =ᶠ[nhds z] 0 := by
  push Not at hz
  obtain ⟨w, hw⟩ := hz
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hΦ
  have hm : (1 : ℝ) ≤ w.mult := by exact_mod_cast w.mult_pos
  set ε := Real.exp (-(R + 1))
  have hε : 0 < ε := Real.exp_pos _
  have hcont : Continuous (normAtPlace w : mixedSpace K → ℝ) := continuous_normAtPlace w
  have hU : ∀ᶠ z' in nhds z, normAtPlace w z' < ε :=
    hcont.continuousAt.eventually (gt_mem_nhds (by rw [hw]; exact hε))
  filter_upwards [hU] with z' hz'
  simp only [Pi.zero_apply, phiF]
  split_ifs with h
  · have hpos : 0 < normAtPlace w z' := lt_of_le_of_ne (normAtPlace_nonneg w z') (Ne.symm (h w))
    have hlog : Real.log (normAtPlace w z') < -(R + 1) := by
      rw [Real.log_lt_iff_lt_exp hpos]; exact hz'
    have hb : R < ‖logM z'‖ := by
      have h1 : |logM z' w| ≤ ‖logM z'‖ := by
        have := norm_le_pi_norm (logM z') w
        rwa [Real.norm_eq_abs] at this
      have h2 : R < |logM z' w| := by
        rw [abs_of_neg]
        · simp only [logM]; nlinarith
        · simp only [logM]; nlinarith
      linarith
    rw [hR _ hb]; simp
  · rfl

theorem contDiff_phiF (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (phiF (K := K) Φ) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : ∀ w, normAtPlace w z ≠ 0
  · have hU : ∀ᶠ z' in nhds z, ∀ w, normAtPlace w z' ≠ 0 := by
      refine Filter.eventually_all.2 fun w => ?_
      exact (continuous_normAtPlace w).continuousAt.eventually_ne (hz w)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' => ((Φ (logM z') : ℝ) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z (hΦs.contDiffAt.comp z (contDiffAt_logM hz))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU] with z' hz'
    exact phiF_of_ne hz'
  · exact contDiffAt_const.congr_of_eventuallyEq (phiF_eventually_zero hΦ hz)

theorem hasCompactSupport_phiF (hΦ : HasCompactSupport Φ) :
    HasCompactSupport (phiF (K := K) Φ) := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hΦ
  have hm : ∀ w : InfinitePlace K, (1 : ℝ) ≤ w.mult := fun w => by exact_mod_cast w.mult_pos
  refine HasCompactSupport.intro (isCompact_closedBall (0 : mixedSpace K) (Real.exp R))
    fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  simp only [phiF]
  split_ifs with h
  · rw [norm_eq_sup'_normAtPlace] at hz
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun w => normAtPlace w z)
    rw [hw] at hz
    have hpos : 0 < normAtPlace w z := lt_of_le_of_ne (normAtPlace_nonneg w z) (Ne.symm (h w))
    have hlog : R < Real.log (normAtPlace w z) := by
      rw [Real.lt_log_iff_exp_lt hpos]; exact hz
    have hb : R < ‖logM z‖ := by
      have h1 : |logM z w| ≤ ‖logM z‖ := by
        have := norm_le_pi_norm (logM z) w
        rwa [Real.norm_eq_abs] at this
      have h2 : R < |logM z w| := by
        rw [abs_of_pos]
        · simp only [logM]; nlinarith [hm w]
        · simp only [logM]; nlinarith [hm w]
      linarith
    rw [hR _ hb]; simp
  · rfl

/-- The radial test function as a Schwartz function. -/
noncomputable def phiS (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ) :
    𝓢(mixedSpace K, ℂ) :=
  (hasCompactSupport_phiF hΦ).toSchwartzMap (contDiff_phiF hΦs hΦ)

@[simp] theorem phiS_apply (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ)
    (z : mixedSpace K) : phiS hΦs hΦ z = phiF Φ z := rfl

end smooth

/-! ### The Fourier transform is radial -/

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Radial: integrals of radial functions in log coordinates

For `K` totally complex and `f z = F (logM z)` off the coordinate hyperplanes,
`∫ f = π^{r₂} ∫ e^{Σ b} F(b) db` (polar coordinates, then `r_w = exp (b_w / 2)`).
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Zeta: log-profiles of Schwartz functions and their zeta integrals

For `h` Schwartz on the mixed space, `prof h b = h (dilV b)` decays like `∏_w (1 + e^{b_w/2})^{-N}`
for every `N`, so `Zm h s = ∫ prof h b · e^{s Σ b} db` converges and is holomorphic on `Re s > 0`,
bounded on vertical strips.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

variable [IsTotallyComplex K]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Exch: the exchange identity and `Z(φ̂, 1/6) ≠ 0`

For the radial test function `φ = phiF Φ`, Fubini and Fourier inversion (a79f4737) give
`∫ φ̂(y_b v) φ̂(v) dv = c ∫ φ(u) φ(y_b u) du` with `c > 0`; integrating against `e^{s Σ b}` in log
coordinates gives `Z(φ̂, s) Z(φ̂, 1 − s) = c Z(φ, s) Z(φ, 1 − s)` for `0 < s < 1`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

section exchange

variable {Φ : realSpace K → ℝ} (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ)

end exchange

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Main: (7.16)–(7.17) at `u = 1` from four arithmetic cuts

With `b(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)` (the coefficient at `u = 1`, without the
`S`-unit `u`), the target `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul` follows from

* `CutMul`: cross-prime multiplicativity `b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀},P^l,P^k,P^m) b(𝔠,𝔫,𝔰,𝔯)`
  ((7.14), (7.16): Chinese remainders + reciprocity (3.3));
* `CutF`: the local Poisson factor `F(P^k, P^{e₀}(P^l)³, gen(P^m)⁶)` ((7.15), (7.17));
* `CutHD`: `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1` (Davenport–Hasse, (3.9)–(3.11));
* `CutG6`: `Ḡ(P)⁶ = 1`.

Proved here: `a(1,1,1,1) = 1` (`C3B_Norm`), the `U_S⁶`-invariance replacing `u` by `1`
(`C3B_Unit`, `C3B_Good`), `ϑ` on prime powers, `Λ⁶ = jacobiPhaseSix`, and the table algebra. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary lemmas -/

lemma isExterior_top (𝔪 : Ideal (𝓞 F)) : IsExterior 𝔪 ⊤ := ⟨top_ne_bot, top_sup_eq _⟩

lemma isExterior_mul {𝔪 I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {𝔪 I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact isExterior_top 𝔪
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

lemma normalizedFactors_prime_pow {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (t : ℕ) :
    normalizedFactors (P ^ t) = Multiset.replicate t P := by
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [normalizedFactors_pow, normalizedFactors_irreducible hirr, normalize_eq,
    Multiset.nsmul_singleton]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
def ExtWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ I : Ideal (𝓞 F), I ⊔ 𝔪 = ⊤ ∧
    ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F

/-- `e` is additive on elements with `ExtWit` (proved below from section A's `C3I_Add`). -/
def HypAdd (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ x y : F, ExtWit 𝔪 x → ExtWit 𝔪 y → sAddChar 𝔪 (x + y) = sAddChar 𝔪 x * sAddChar 𝔪 y

theorem hypAdd (𝔪 : Ideal (𝓞 F)) : HypAdd 𝔪 := by
  rintro x y ⟨I, hI, hx⟩ ⟨J, hJ, hy⟩
  exact C3I.sAddChar_add (C3I.hasWit_of_mul_mem x I hI hx) (C3I.hasWit_of_mul_mem y J hJ hy)

lemma extWit_div_add {𝔪 I : Ideal (𝓞 F)} (hI : I ⊔ 𝔪 = ⊤) {q : SInt 𝔪}
    (hq : Ideal.span {q} = I.map (algebraMap (𝓞 F) (SInt 𝔪))) (hq0 : (q : F) ≠ 0)
    (z r : SInt 𝔪) : ExtWit 𝔪 ((z : F) / (q : F) + (r : F)) := by
  refine ⟨I, hI, fun i hi => ?_⟩
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ Ideal.span {q} := hq ▸ Ideal.mem_map_of_mem _ hi
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  have hiF : algebraMap (𝓞 F) F i = (t : F) * (q : F) := by
    have := congrArg (fun x : SInt 𝔪 => (x : F)) ht
    simp only [Subalgebra.coe_mul] at this
    rw [this]; rfl
  rw [hiF, show ((z : F) / (q : F) + (r : F)) * ((t : F) * (q : F)) =
    (z : F) * (t : F) + (r : F) * (t : F) * (q : F) by field_simp]
  exact add_mem (mul_mem z.2 t.2) (mul_mem (mul_mem r.2 t.2) q.2)

/-- Hypothesis (section A): at an exterior prime, the sextic symbol is multiplicative on `R`, with
sixth power `1` off `PR`. -/
def HypChi (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
    (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
      sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
    (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1)

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

lemma exterior_of_mem_factors {𝔞 Q : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (hQ : Q ∈ normalizedFactors 𝔞) : Q.IsPrime ∧ IsExterior 𝔪 Q := by
  have hpr : Prime Q := prime_of_normalized_factor Q hQ
  refine ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero, ?_⟩
  have hle : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  exact eq_top_iff.mpr (h𝔞.2 ▸ sup_le_sup_right hle 𝔪)

lemma isExterior_of_mul_left {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) : IsExterior 𝔪 I := by
  refine ⟨fun h0 => h.1 (by rw [h0, Ideal.bot_mul]), ?_⟩
  exact eq_top_iff.mpr (h.2 ▸ sup_le_sup_right (Ideal.mul_le_inf.trans inf_le_left) 𝔪)

lemma isExterior_of_mul_right {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) :
    IsExterior 𝔪 J := by
  rw [mul_comm] at h; exact isExterior_of_mul_left h

/-- An exterior prime does not become the unit ideal in `R`. -/
lemma map_ne_top {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q) :
    Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≠ ⊤ := by
  intro htop
  let v : HeightOneSpectrum (𝓞 F) := ⟨Q, hQ, hQe.1⟩
  have hvS : v ∉ placesOf 𝔪 := by
    intro hv
    have : (⊤ : Ideal (𝓞 F)) ≤ Q := hQe.2 ▸ sup_le le_rfl hv
    exact hQ.ne_top (eq_top_iff.mpr this)
  let J : Ideal (SInt 𝔪) :=
    { carrier := {x | v.valuation F (x : F) < 1}
      add_mem' := fun {a b} ha hb => by
        show v.valuation F ((a + b : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_add]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by
        show v.valuation F ((0 : SInt 𝔪) : F) < 1
        simp
      smul_mem' := fun c x hx => by
        show v.valuation F ((c * x : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (c.2 v hvS)) hx }
  have hle : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show v.valuation F ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) < 1
    rw [C3B.coe_algebraMap_SInt]
    exact (v.valuation_lt_one_iff_mem a).mpr ha
  have h1 : (1 : SInt 𝔪) ∈ J := hle (htop ▸ Submodule.mem_top)
  have : v.valuation F ((1 : SInt 𝔪) : F) < 1 := h1
  simp at this

/-- `𝓞 → R/𝔞R` is onto for exterior `𝔞`. -/
lemma exists_sub_mem_map {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  let O' : Submodule (𝓞 F) (SInt 𝔪) := LinearMap.range (Algebra.linearMap (𝓞 F) (SInt 𝔪))
  let J : Ideal (𝓞 F) := O'.colon {r}
  have hJ : J ⊔ 𝔞 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hne
    have h𝔞M : 𝔞 ≤ M := le_trans le_sup_right hJM
    have hM0 : M ≠ ⊥ := fun h => h𝔞.1 (eq_bot_iff.mpr (h ▸ h𝔞M))
    let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hM0⟩
    have hvS : v ∉ placesOf 𝔪 := by
      intro hv
      have : (⊤ : Ideal (𝓞 F)) ≤ M := h𝔞.2 ▸ sup_le h𝔞M hv
      exact hM.ne_top (eq_top_iff.mpr this)
    obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hvS)
    have hdJ : d ∈ J := by
      rw [Submodule.mem_colon_singleton]
      refine ⟨n, ?_⟩
      apply Subtype.ext
      show ((algebraMap (𝓞 F) (SInt 𝔪) n : SInt 𝔪) : F) = ((d • r : SInt 𝔪) : F)
      rw [C3B.coe_algebraMap_SInt, Algebra.smul_def, Subalgebra.coe_mul, C3B.coe_algebraMap_SInt]
      have h2 : ((n : 𝓞 F) : F) = (d : F) * (r : F) := by rw [mul_comm]; exact hnd.symm
      exact h2
    exact hd (le_trans le_sup_left hJM hdJ)
  obtain ⟨j, hj, a, ha, hja⟩ := Submodule.mem_sup.mp (hJ ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ J ⊔ 𝔞)
  rw [Submodule.mem_colon_singleton] at hj
  obtain ⟨b, hb⟩ := hj
  refine ⟨b, ?_⟩
  have hb' : algebraMap (𝓞 F) (SInt 𝔪) b = algebraMap (𝓞 F) (SInt 𝔪) j * r := by
    rw [← Algebra.smul_def]; exact hb
  have : r - algebraMap (𝓞 F) (SInt 𝔪) b = algebraMap (𝓞 F) (SInt 𝔪) a * r := by
    rw [hb']
    have h1 : (1 : SInt 𝔪) = algebraMap (𝓞 F) (SInt 𝔪) j + algebraMap (𝓞 F) (SInt 𝔪) a := by
      rw [← map_add, hja, map_one]
    linear_combination r * h1
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

lemma finite_quot {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Finite (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ 𝔞) := Ring.HasFiniteQuotients.finiteQuotient h𝔞.1
  let f := Ideal.quotientMap (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪))
    Ideal.le_comap_map
  refine Finite.of_surjective f ?_
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := exists_sub_mem_map h𝔞 r
  refine ⟨Ideal.Quotient.mk 𝔞 a, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  rw [← neg_mem_iff, neg_sub]; exact ha

lemma isCoprime_map {I J : Ideal (𝓞 F)} (h : IsCoprime I J) :
    IsCoprime (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (J.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  rw [← Ideal.map_sup, h, Ideal.map_top]

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

lemma residueSymbol_mul_ideal (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma residueSymbol_prime {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  have h := C3B.normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h
  simp [residueSymbol, h]

lemma residueSymbol_mul (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (x y : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 (x * y) = residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  rw [← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun Q hQ => ?_
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  exact (hχ Q hQp hQe).1 x y

lemma not_mem_of_isCoprime {I : Ideal (SInt 𝔪)} (hI : I ≠ ⊤) {x : SInt 𝔪}
    (h : IsCoprime (Ideal.span {x}) I) : x ∉ I := by
  intro hx
  apply hI
  rw [Ideal.isCoprime_iff_sup_eq] at h
  rw [eq_top_iff, ← h]
  exact sup_le ((Ideal.span_singleton_le_iff_mem I).mpr hx) le_rfl

lemma residueSymbol_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ^ 6 = 1 := by
  unfold residueSymbol
  rw [← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  apply (hχ Q hQp hQe).2
  apply not_mem_of_isCoprime (map_ne_top hQp hQe)
  have hle : 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.map_mono (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ))
  rw [Ideal.isCoprime_iff_sup_eq] at hx ⊢
  exact eq_top_iff.mpr (hx ▸ sup_le_sup_left hle _)

lemma residueSymbol_ne_zero (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ≠ 0 := by
  intro h0
  have := residueSymbol_pow_six hχ h𝔞 hx
  rw [h0] at this; norm_num at this

lemma isCoprime_one (I : Ideal (SInt 𝔪)) : IsCoprime (Ideal.span {(1 : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_one]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_one (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    residueSymbol ι 𝔪 𝔞 1 = 1 := by
  have h := residueSymbol_mul hχ h𝔞 (1 : SInt 𝔪) 1
  rw [one_mul] at h
  have h0 := residueSymbol_ne_zero hχ h𝔞 (isCoprime_one _)
  have : residueSymbol ι 𝔪 𝔞 1 * (residueSymbol ι 𝔪 𝔞 1 - 1) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 h0
  · exact sub_eq_zero.mp h1

lemma isCoprime_unit (u : (SInt 𝔪)ˣ) (I : Ideal (SInt 𝔪)) :
    IsCoprime (Ideal.span {(u : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_unit_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (u : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ 6 * x) = residueSymbol ι 𝔪 𝔞 x := by
  have hp : ∀ n : ℕ, residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ n) = residueSymbol ι 𝔪 𝔞 u ^ n := by
    intro n
    induction n with
    | zero => simp [residueSymbol_one hχ h𝔞]
    | succ n ih => rw [pow_succ, residueSymbol_mul hχ h𝔞, ih, pow_succ]
  rw [residueSymbol_mul hχ h𝔞, hp, residueSymbol_pow_six hχ h𝔞 (isCoprime_unit u _), one_mul]

/-! ### Generators -/

/-- `gen(I J) = ε⁶ gen(I) gen(J)` with `ε` a unit of `R`. -/
lemma gen_mul' (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) :
    ∃ ε : (SInt 𝔪)ˣ, g.gen (I * J) = (ε : SInt 𝔪) ^ 6 * g.gen I * g.gen J := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, ?_⟩
  apply Subtype.ext
  rw [hε]
  simp

lemma gen_top (g : AllowedGen ι 𝔪) : ∃ ε : (SInt 𝔪)ˣ, g.gen ⊤ = (ε : SInt 𝔪) ^ 6 := by
  obtain ⟨ε, hε⟩ := gen_mul' g ⟨top_ne_bot, top_sup_eq _⟩ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.top_mul] at hε
  obtain ⟨u, hu⟩ := C3B.isUnit_gen_top g
  refine ⟨ε⁻¹, ?_⟩
  have h1 : (u : SInt 𝔪) * 1 = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) := by
    rw [← hu] at hε
    rw [mul_one]
    calc (u : SInt 𝔪) = (ε : SInt 𝔪) ^ 6 * u * u := hε
      _ = _ := by ring
  have h2 := u.isUnit.mul_left_cancel h1
  rw [← hu]
  have h3 : ((ε : SInt 𝔪) ^ 6) * ((↑(ε⁻¹) : SInt 𝔪) ^ 6) = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  calc (u : SInt 𝔪) = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (↑(ε⁻¹) : SInt 𝔪) ^ 6) := by
        rw [h3, mul_one]
    _ = ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) * (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by ring
    _ = (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by rw [← h2, one_mul]

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L2B_Bound: crude norm bounds for the arithmetic factors

`|e| ≤ 1`, `|χ_𝔞| ≤ 1`, `|g_𝔞(k)| ≤ q_𝔞`, `|γ_j(𝔠)| ≤ q_𝔠^{1/2}`, `|F(𝔰,𝔄,h)| ≤ q_𝔰 q_𝔄`,
`|Λ(𝔞)|, |G(𝔞)| ≤ q_𝔞^{1/2}`, `|ϑ(𝔞)| ≤ q_𝔞`.
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F]

/-! ### Generic lemmas -/

theorem norm_prod_map_le {α : Type*} (s : Multiset α) (f : α → ℂ) (b : α → ℝ)
    (hb : ∀ a ∈ s, 0 ≤ b a) (h : ∀ a ∈ s, ‖f a‖ ≤ b a) :
    ‖(s.map f).prod‖ ≤ (s.map b).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have hs : ∀ a ∈ s, 0 ≤ b a := fun x hx => hb x (Multiset.mem_cons_of_mem hx)
    exact mul_le_mul (h a (Multiset.mem_cons_self _ _))
      (ih hs fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _)
      (hb a (Multiset.mem_cons_self _ _))

theorem norm_finsum_le {α : Type*} [Finite α] (f : α → ℂ) (B : ℝ) (h : ∀ a, ‖f a‖ ≤ B) :
    ‖∑ᶠ a, f a‖ ≤ Nat.card α * B := by
  have := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a, ‖f a‖ ≤ ∑ _a : α, B := Finset.sum_le_sum fun a _ => h a
    _ = Fintype.card α * B := by simp

/-! ### Characters -/

theorem norm_sAddChar_le (𝔪 : Ideal (𝓞 F)) (x : F) : ‖sAddChar 𝔪 x‖ ≤ 1 := by
  unfold sAddChar
  split_ifs
  · rw [Complex.norm_exp]
    simp
  · simp

theorem norm_sexticResidueSymbol_le (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h0 h
  · simp
  · have h6 : (ι ((h.choose : 𝓞 F) : F)) ^ 6 = 1 := by
      have h' : ((h.choose : 𝓞 F) : F) ^ 6 = 1 := by
        have := congrArg (algebraMap (𝓞 F) F) h.choose_spec.1
        simpa using this
      rw [← map_pow, h', map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)).le
  · simp

theorem norm_residueSymbol_le (ι : F →+* ℂ) (𝔪 𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  refine (norm_prod_map_le _ _ (fun _ => 1) (fun _ _ => zero_le_one)
    fun P _ => norm_sexticResidueSymbol_le ι 𝔪 P x).trans ?_
  simp

/-! ### Quotients -/

variable {𝔪 : Ideal (𝓞 F)}

theorem card_quot_le {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Nat.card (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) ≤ Ideal.absNorm 𝔞 := by
  have : Finite (𝓞 F ⧸ 𝔞) := Ring.HasFiniteQuotients.finiteQuotient h𝔞.1
  let f := Ideal.quotientMap (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪))
    Ideal.le_comap_map
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := C3M.exists_sub_mem_map h𝔞 r
    refine ⟨Ideal.Quotient.mk 𝔞 a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]; exact ha
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_le_card_of_surjective f hf

variable {ι : F →+* ℂ}

theorem norm_gaussPhase_le (g : AllowedGen ι 𝔪) (j : ℕ) {𝔠 : Ideal (𝓞 F)}
    (h𝔠 : IsExterior 𝔪 𝔠) : ‖gaussPhase g j 𝔠‖ ≤ Real.sqrt (Ideal.absNorm 𝔠) := by
  have := C3M.finite_quot h𝔠
  unfold gaussPhase
  have hN : (0 : ℝ) < Ideal.absNorm 𝔠 := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => h𝔠.1 (Ideal.absNorm_eq_zero_iff.1 h))
  have hs : 0 < Real.sqrt (Ideal.absNorm 𝔠) := Real.sqrt_pos.2 hN
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hsum : ‖∑ᶠ x : SInt 𝔪 ⧸ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪)),
      residueSymbol ι 𝔪 𝔠 (quotLift x) ^ j * sAddChar 𝔪 ((quotLift x : F) / (g.gen 𝔠 : F))‖ ≤
      Ideal.absNorm 𝔠 := by
    refine (norm_finsum_le _ 1 fun v => ?_).trans ?_
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_residueSymbol_le ι 𝔪 𝔠 _))
        (norm_nonneg _) (norm_sAddChar_le _ _)
    · rw [mul_one]; exact_mod_cast card_quot_le h𝔠
  rw [inv_mul_le_iff₀ hs]
  calc _ ≤ (Ideal.absNorm 𝔠 : ℝ) := hsum
    _ = Real.sqrt (Ideal.absNorm 𝔠) * Real.sqrt (Ideal.absNorm 𝔠) :=
      (Real.mul_self_sqrt hN.le).symm

end ArtinPrimitiveRoots.L2B

end
end

section
section
/-!
# L3P_Theta: Poisson summation over `P^k` with a periodic coefficient

For `c` periodic modulo `𝔫R`,
`Σ_{m ∈ P^j} c(m) φ(y_x m) = (covol(𝔫 P^j) e^{Σx})⁻¹ Σ_{h ∈ P^{val ν − j − δ}} ĉ⁻(h) φ̂(y_x⁻¹ h/ν)`
with `ĉ⁻(h) = Σ_{x mod 𝔫R} c(x) e(−h x / ν)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  FractionalIdeal
open scoped nonZeroDivisors Classical Real SchwartzMap

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

variable [IsTotallyComplex F]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Phi: the concrete test function

`Φ(b) = χ(Σ_w b_w) · ∏_{w ≠ w₀} β(b_w)` with `β` a bump at `0` and `χ(t) = β(t) − e^{−1} β(t − 1)`.
Then `∫ Φ(b) G(Σ b) db = c_β ∫ χ(t) G(t) dt`, so `Z(φ, s) = c_β (1 − e^{s−1}) ∫ β(t) e^{st} dt`:
it vanishes at `s = 1` (`∫ φ = 0`, hence `φ̂(0) = 0`) and not at `s = 1/6, 5/6`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

section split

variable {K : Type*} [Field K] [NumberField K]

variable [IsTotallyComplex K]

end split

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_ThetaS: the theta identity with exact valuations at `S`

For `x : realSpace F` and `k : S → ℤ`,
`Σ_{m ≠ 0, val m = k} c(m) Φ(x + ℓ(m)) =
  Σ_{e ⊆ S} (−1)^{|e|} (covol(𝔫 P^{k+e}) e^{Σx})⁻¹ Σ_{h ≠ 0, h ∈ P^{val ν − k − e − δ}} ĉ⁻(h) Φ̂(ℓ(h) − ℓ(ν) − x)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical Real SchwartzMap

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]

/-! ### Inclusion–exclusion at `S` -/

/-! ### The theta identity -/

variable {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Dom: a fundamental domain for the units acting on log coordinates

`D₀ = {x : realSpace | coordinates of x along the fundamental units lie in [0, 1)}`. For every
`x`, exactly `|μ_F|` units `η ∈ 𝓞ˣ` have `x − ℓ(η) ∈ D₀` (Dirichlet: `η = ζ ∏ f_i^{n_i}`,
`ℓ(η) = Σ n_i ℓ(f_i)`, and `n` is the floor of the coordinates of `x`).
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open scoped Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

theorem logK_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : logK (a * b) = logK a + logK b := by
  funext w
  simp only [logK_apply, Pi.add_apply, map_mul]
  rw [Real.log_mul ((map_ne_zero w).2 ha) ((map_ne_zero w).2 hb)]
  ring

theorem logK_one : logK (1 : F) = 0 := by
  funext w; simp [logK_apply]

theorem logK_eq_expMap_symm (x : F) :
    logK x = expMap.symm (normAtAllPlaces (mixedEmbedding F x)) := by
  funext w; simp [logK_apply, normAtAllPlaces_apply, normAtPlace_apply]

/-- `ℓ` on the units of `𝓞`. -/
noncomputable def logU (η : (𝓞 F)ˣ) : realSpace F := logK ((η : 𝓞 F) : F)

theorem unit_coe_ne_zero (η : (𝓞 F)ˣ) : ((η : 𝓞 F) : F) ≠ 0 := by
  simp

theorem logU_mul (η η' : (𝓞 F)ˣ) : logU (η * η') = logU η + logU η' := by
  rw [logU, logU, logU, Units.val_mul]
  push_cast
  exact logK_mul (unit_coe_ne_zero η) (unit_coe_ne_zero η')

theorem logU_one : logU (1 : (𝓞 F)ˣ) = 0 := by
  simp [logU, logK_one]

/-- `ℓ` as an additive homomorphism. -/
noncomputable def logUHom : Additive (𝓞 F)ˣ →+ realSpace F where
  toFun η := logU (Additive.toMul η)
  map_zero' := logU_one
  map_add' _ _ := logU_mul _ _

theorem logU_zpow (η : (𝓞 F)ˣ) (n : ℤ) : logU (η ^ n) = n • logU η := by
  change logUHom (Additive.ofMul (η ^ n)) = _
  rw [ofMul_zpow, map_zsmul]
  rfl

theorem logU_prod {ι : Type*} (s : Finset ι) (f : ι → (𝓞 F)ˣ) :
    logU (∏ i ∈ s, f i) = ∑ i ∈ s, logU (f i) := by
  change logUHom (Additive.ofMul (∏ i ∈ s, f i)) = _
  rw [ofMul_prod, map_sum]
  rfl

theorem logU_torsion {ζ : (𝓞 F)ˣ} (hζ : ζ ∈ torsion F) : logU ζ = 0 := by
  funext w
  rw [logU, logK_apply, (mem_torsion F).1 hζ w, Real.log_one, mul_zero]
  rfl

/-- The decomposition `η = ζ ∏ f_i^{e_i}` of Dirichlet's unit theorem. -/
noncomputable def decomp (η : (𝓞 F)ˣ) : torsion F × (Fin (rank F) → ℤ) :=
  (exist_unique_eq_mul_prod F η).exists.choose

/-- The exponents of a unit along the fundamental system. -/
noncomputable def expo (η : (𝓞 F)ˣ) : Fin (rank F) → ℤ := (decomp η).2

theorem decomp_spec (η : (𝓞 F)ˣ) :
    η = ((decomp η).1 : (𝓞 F)ˣ) * ∏ i, (fundSystem F i) ^ (expo η i) :=
  (exist_unique_eq_mul_prod F η).exists.choose_spec

theorem expo_eq {η ζ : (𝓞 F)ˣ} (hζ : ζ ∈ torsion F) {e : Fin (rank F) → ℤ}
    (h : η = ζ * ∏ i, (fundSystem F i) ^ (e i)) : e = expo η := by
  have := (exist_unique_eq_mul_prod F η).unique (y₁ := (⟨ζ, hζ⟩, e)) (y₂ := decomp η) h
    (decomp_spec η)
  exact congrArg Prod.snd this

theorem logU_fundSystem (i : Fin (rank F)) :
    logU (fundSystem F i) = completeBasis F (equivFinRank i) := by
  rw [completeBasis_apply_of_ne, Equiv.symm_apply_apply, logU, logK_eq_expMap_symm]

theorem logU_eq_sum (η : (𝓞 F)ˣ) :
    logU η = ∑ i, (expo η i : ℝ) •
      completeBasis F (equivFinRank i) := by
  conv_lhs => rw [decomp_spec η]
  rw [logU_mul, logU_torsion (decomp η).1.2, zero_add, logU_prod]
  simp_rw [logU_zpow, logU_fundSystem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]

/-- The fundamental domain for `𝓞ˣ` acting on `realSpace` by translation by `ℓ`. -/
def D0 (F : Type*) [Field F] [NumberField F] : Set (realSpace F) :=
  {x | ∀ i : Fin (rank F), (completeBasis F).repr x (equivFinRank i) ∈ Set.Ico (0 : ℝ) 1}

theorem repr_sub_logU (x : realSpace F) (η : (𝓞 F)ˣ) (i : Fin (rank F)) :
    (completeBasis F).repr (x - logU η) (equivFinRank i) =
      (completeBasis F).repr x (equivFinRank i) - (expo η i) := by
  rw [map_sub, logU_eq_sum, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg (fun h => hj (equivFinRank.injective (Subtype.ext h))), mul_zero]
  · simp

/-- Exactly `|μ|` units translate `x` into `D₀`. -/
theorem hasSum_D0 (x : realSpace F) :
    HasSum (fun η : (𝓞 F)ˣ => (D0 F).indicator (fun _ => (1 : ℝ)) (x - logU η))
      (torsionOrder F : ℝ) := by
  have : Fintype (torsion F) := Fintype.ofFinite _
  set n : Fin (rank F) → ℤ := fun i => ⌊(completeBasis F).repr x (equivFinRank i)⌋
  set g : torsion F → (𝓞 F)ˣ := fun ζ => ζ * ∏ i, (fundSystem F i) ^ (n i)
  have hrepr : ∀ ζ : torsion F, expo (g ζ) = n := fun ζ => (expo_eq ζ.2 rfl).symm
  have hg : Function.Injective g := by
    intro a b hab
    have := mul_right_cancel hab
    exact Subtype.ext this
  have hmem : ∀ η : (𝓞 F)ˣ, x - logU η ∈ D0 F ↔ expo η = n := by
    intro η
    simp only [D0, Set.mem_ofPred_eq, repr_sub_logU, Set.mem_Ico]
    constructor
    · intro h; ext i
      have := h i
      refine (Int.floor_eq_iff.2 ⟨by linarith [this.1], by linarith [this.2]⟩).symm
    · intro h i
      rw [h]
      exact ⟨by linarith [Int.floor_le ((completeBasis F).repr x (equivFinRank i))],
        by linarith [Int.lt_floor_add_one ((completeBasis F).repr x (equivFinRank i))]⟩
  have hzero : ∀ η ∉ Set.range g, (D0 F).indicator (fun _ => (1 : ℝ)) (x - logU η) = 0 := by
    intro η hη
    rw [Set.indicator_of_notMem]
    intro hD
    apply hη
    have he := (hmem η).1 hD
    refine ⟨(decomp η).1, ?_⟩
    have := decomp_spec η
    rw [show expo η = n from he] at this
    exact this.symm
  rw [← hg.hasSum_iff hzero]
  have h1 : ∀ ζ : torsion F, (D0 F).indicator (fun _ => (1 : ℝ)) (x - logU (g ζ)) = 1 := fun ζ => by
    rw [Set.indicator_of_mem ((hmem _).2 (hrepr ζ))]
  have := hasSum_fintype (fun ζ : torsion F => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
  rw [torsionOrder, Nat.card_eq_fintype_card]
  exact this.congr_fun fun ζ => by simp only [Function.comp_apply, h1]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_DomS: a fundamental domain for the `S`-units acting on `realSpace × ℤ^S`

The `S`-unit `ε` acts by `(x, k) ↦ (x + ℓ(ε), k − val_S ε)`. With `B` a set of representatives of
`ℤ^S / val_S(U_S)`, the set `Ω = D₀ × B` meets every orbit in exactly `|μ_F|` points.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-- `ℓ` of an `S`-unit. -/
noncomputable def LxU (ε : (SInt 𝔪)ˣ) : realSpace F := logK ((ε : SInt 𝔪) : F)

/-- `val_S` of an `S`-unit. -/
noncomputable def LkU (ε : (SInt 𝔪)ˣ) : SP 𝔪 → ℤ := valS ((ε : SInt 𝔪) : F)

theorem LxU_mul (ε ε' : (SInt 𝔪)ˣ) : LxU (ε * ε') = LxU ε + LxU ε' := by
  rw [LxU, LxU, LxU, Units.val_mul, Subalgebra.coe_mul, logK_mul (unit_ne_zero ε) (unit_ne_zero ε')]

theorem LkU_mul (ε ε' : (SInt 𝔪)ˣ) : LkU (ε * ε') = LkU ε + LkU ε' := by
  rw [LkU, LkU, LkU, Units.val_mul, Subalgebra.coe_mul, valS_mul (unit_ne_zero ε) (unit_ne_zero ε')]

/-- `val_S` as an additive homomorphism. -/
noncomputable def LkHom (𝔪 : Ideal (𝓞 F)) [Fintype (SP 𝔪)] : Additive (SInt 𝔪)ˣ →+ (SP 𝔪 → ℤ) where
  toFun ε := LkU (Additive.toMul ε)
  map_zero' := by
    funext v
    simp [LkU, valS, ordv_one]
  map_add' _ _ := LkU_mul _ _

/-- The units of `𝓞` as `S`-units. -/
noncomputable def iotaU (η : (𝓞 F)ˣ) : (SInt 𝔪)ˣ := Units.map (algebraMap (𝓞 F) (SInt 𝔪)) η

theorem coe_iotaU (η : (𝓞 F)ˣ) : (((iotaU (𝔪 := 𝔪) η : (SInt 𝔪)ˣ) : SInt 𝔪) : F) =
    ((η : 𝓞 F) : F) := rfl

theorem LxU_iotaU (η : (𝓞 F)ˣ) : LxU (iotaU (𝔪 := 𝔪) η) = logU η := rfl

theorem ordv_unit_O (v : HeightOneSpectrum (𝓞 F)) (η : (𝓞 F)ˣ) : ordv v ((η : 𝓞 F) : F) = 0 := by
  have h1 : 0 ≤ ordv v ((η : 𝓞 F) : F) := (valuation_le_one_iff v (unit_coe_ne_zero η)).1
    (v.valuation_le_one _)
  have h2 : 0 ≤ ordv v (((η⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) := (valuation_le_one_iff v
    (unit_coe_ne_zero _)).1 (v.valuation_le_one _)
  have h3 : (((η⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = ((η : 𝓞 F) : F)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have := congrArg (fun z : 𝓞 F => (z : F)) (η.inv_mul)
    simpa using this
  rw [h3, ordv_inv] at h2
  omega

theorem LkU_iotaU (η : (𝓞 F)ˣ) : LkU (iotaU (𝔪 := 𝔪) η) = 0 := by
  funext v; exact ordv_unit_O v.1 η

theorem exists_iotaU_of_LkU_eq_zero {ε : (SInt 𝔪)ˣ} (h : LkU ε = 0) :
    ∃ η : (𝓞 F)ˣ, iotaU η = ε := by
  have hε0 := unit_ne_zero ε
  have hord : ∀ v : HeightOneSpectrum (𝓞 F), ordv v ((ε : SInt 𝔪) : F) = 0 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact congrFun h ⟨v, hv⟩
    · have h1 : 0 ≤ ordv v ((ε : SInt 𝔪) : F) := (mem_SInt_iff hε0).1 (ε : SInt 𝔪).2 v hv
      have hinv : (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        exact congrArg (fun z : SInt 𝔪 => (z : F)) (ε.inv_mul)
      have h2 : 0 ≤ ordv v (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) :=
        (mem_SInt_iff (unit_ne_zero _)).1 (ε⁻¹ : (SInt 𝔪)ˣ).1.2 v hv
      rw [hinv, ordv_inv] at h2
      omega
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((ε : SInt 𝔪) : F) ≤ 1 := fun v =>
    (valuation_le_one_iff v hε0).2 (hord v).ge
  have hval' : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((ε : SInt 𝔪) : F)⁻¹ ≤ 1 := fun v =>
    (valuation_le_one_iff v (inv_ne_zero hε0)).2 (by rw [ordv_inv, hord v, neg_zero])
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hval
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hval'
  have hab : a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ hε0]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ?_⟩
  ext
  simp only [coe_iotaU]
  exact ha

/-- The image `Λ = val_S(U_S)`. -/
noncomputable def LamS (𝔪 : Ideal (𝓞 F)) [Fintype (SP 𝔪)] : AddSubgroup (SP 𝔪 → ℤ) :=
  (LkHom 𝔪).range

/-- Representatives of `ℤ^S / Λ`. -/
def Bset (𝔪 : Ideal (𝓞 F)) [Fintype (SP 𝔪)] : Set (SP 𝔪 → ℤ) :=
  Set.range (Quotient.out : (SP 𝔪 → ℤ) ⧸ LamS 𝔪 → SP 𝔪 → ℤ)

/-- The fundamental domain `Ω = D₀ × B`, as a weight. -/
noncomputable def Omg (x : realSpace F) (k : SP 𝔪 → ℤ) : ℝ :=
  (D0 F).indicator (fun _ => (1 : ℝ)) x * (Bset 𝔪).indicator (fun _ => (1 : ℝ)) k

/-- Exactly `|μ|` points of every orbit lie in `Ω`. -/
theorem hasSum_Omg (y : realSpace F) (k : SP 𝔪 → ℤ) :
    HasSum (fun ε : (SInt 𝔪)ˣ => Omg (y - LxU ε) (k + LkU ε)) (torsionOrder F : ℝ) := by
  set q : (SP 𝔪 → ℤ) ⧸ LamS 𝔪 := QuotientAddGroup.mk k
  set lam0 := Quotient.out q - k
  have hlam0 : lam0 ∈ LamS 𝔪 := by
    have : (QuotientAddGroup.mk (Quotient.out q) : (SP 𝔪 → ℤ) ⧸ LamS 𝔪) = QuotientAddGroup.mk k :=
      Quotient.out_eq q
    rw [QuotientAddGroup.eq] at this
    rw [show lam0 = -(-Quotient.out q + k) by simp only [lam0]; abel]
    exact neg_mem (by simpa [add_comm] using this)
  obtain ⟨ε₁, hε₁⟩ := hlam0
  set ε₁' : (SInt 𝔪)ˣ := Additive.toMul ε₁
  have hε₁' : LkU ε₁' = lam0 := hε₁
  set g : (𝓞 F)ˣ → (SInt 𝔪)ˣ := fun η => ε₁' * iotaU η
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : iotaU (𝔪 := 𝔪) a = iotaU b := mul_left_cancel hab
    have h2 := congrArg (fun z : (SInt 𝔪)ˣ => ((z : SInt 𝔪) : F)) h1
    simp only [coe_iotaU] at h2
    exact Units.ext (by exact_mod_cast h2)
  have hB : ∀ ε : (SInt 𝔪)ˣ, k + LkU ε ∈ Bset 𝔪 → LkU ε = lam0 := by
    rintro ε ⟨q', hq'⟩
    have hmem : LkU ε ∈ LamS 𝔪 := ⟨Additive.ofMul ε, rfl⟩
    have h1 : (QuotientAddGroup.mk (k + LkU ε) : (SP 𝔪 → ℤ) ⧸ LamS 𝔪) = q := by
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).2 hmem, add_zero]
    have h2 : q' = q := by
      rw [← h1, ← hq']; exact (Quotient.out_eq q').symm
    simp only [lam0]
    rw [← h2, hq']; ring
  have hzero : ∀ ε ∉ Set.range g, Omg (y - LxU ε) (k + LkU ε) = 0 := by
    intro ε hε
    rw [Omg]
    by_cases hk : k + LkU ε ∈ Bset 𝔪
    · exfalso; apply hε
      have h1 : LkU (ε₁'⁻¹ * ε) = 0 := by
        rw [LkU_mul, hB ε hk, ← hε₁', ← LkU_mul, inv_mul_cancel]; exact (LkHom 𝔪).map_zero
      obtain ⟨η, hη⟩ := exists_iotaU_of_LkU_eq_zero h1
      exact ⟨η, by simp only [g, hη, mul_inv_cancel_left]⟩
    · rw [Set.indicator_of_notMem hk, mul_zero]
  rw [← hg.hasSum_iff hzero]
  have hcomp : ∀ η : (𝓞 F)ˣ, Omg (y - LxU (g η)) (k + LkU (g η)) =
      (D0 F).indicator (fun _ => (1 : ℝ)) ((y - LxU ε₁') - logU η) := by
    intro η
    have hk : k + LkU (g η) ∈ Bset 𝔪 := by
      rw [LkU_mul, LkU_iotaU, add_zero, hε₁']
      exact ⟨q, by simp [lam0]⟩
    rw [Omg, Set.indicator_of_mem hk, mul_one, LxU_mul, LxU_iotaU, sub_add_eq_sub_sub]
  have := hasSum_D0 (y - LxU ε₁')
  exact this.congr_fun fun η => by simp only [Function.comp_apply, hcomp]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Unf: unfolding over the `S`-units

For `G : realSpace × ℤ^S → ℂ` with `Σ_k ∫ ‖G(·, k)‖ < ∞`,
`Σ_{ε ∈ U_S} Σ_k ∫ Ω(x, k) G(x + ℓ(ε), k − val ε) dx = |μ| Σ_k ∫ G(x, k) dx`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open MeasureTheory
open scoped Classical ENNReal

set_option linter.unusedSectionVars false

theorem countable_numberField (F : Type*) [Field F] [NumberField F] : Countable F := by
  have b := Module.finBasis ℚ F
  exact b.equivFun.injective.countable

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

instance countable_SUnits : Countable (SInt 𝔪)ˣ := by
  have := countable_numberField F
  have h : Function.Injective (fun ε : (SInt 𝔪)ˣ => ((ε : SInt 𝔪) : F)) := fun a b h =>
    Units.ext (Subtype.ext h)
  exact h.countable

theorem measurableSet_D0 : MeasurableSet (D0 F) := by
  have hc : ∀ i : Fin (rank F), Continuous fun x : realSpace F =>
      (completeBasis F).repr x (equivFinRank i) := fun i => by
    have := ((completeBasis F).equivFunL).continuous
    exact (continuous_apply _).comp this
  have : D0 F = ⋂ i : Fin (rank F), (fun x : realSpace F =>
      (completeBasis F).repr x (equivFinRank i)) ⁻¹' Set.Ico 0 1 := by
    ext x; simp [D0]
  rw [this]
  exact MeasurableSet.iInter fun i => (hc i).measurable measurableSet_Ico

theorem Omg_nonneg (x : realSpace F) (k : SP 𝔪 → ℤ) : 0 ≤ Omg (𝔪 := 𝔪) x k := by
  unfold Omg; exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

end ArtinPrimitiveRoots.L3P

end
end

section
section
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

/-- Elements of the level subgroup are units at `S_f`. -/
theorem ordv_eq_zero_of_mem {x : Fˣ} (hx : x ∈ SLevel 𝔪 k) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∈ placesOf 𝔪) : L3P.ordv v (x : F) = 0 := by
  have h1 := adicAbv_eq_one_of_sub_lt ((hx v hv).trans_lt (absNorm_zpow_neg_lt_one v k))
  rw [adicAbv_eq v x.ne_zero] at h1
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have := (zpow_eq_one_iff_right₀ (by linarith) hq.ne').1 h1
  omega

/-- The valuations at `S_f` on `SFin`. -/
def valF (y : SFin 𝔪 k) : L3P.SP 𝔪 → ℤ :=
  Quotient.liftOn' (Additive.toMul y) (fun x : Fˣ => L3P.valS (𝔪 := 𝔪) (x : F)) (by
    intro x y hxy
    have hmem : x⁻¹ * y ∈ SLevel 𝔪 k := QuotientGroup.leftRel_apply.mp hxy
    funext v
    have h0 := ordv_eq_zero_of_mem hmem v.2
    have hy : (y : F) = (x : F) * ((x⁻¹ * y : Fˣ) : F) := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    simp only [L3P.valS]
    rw [hy, L3P.ordv_mul v.1 x.ne_zero (Units.ne_zero _), h0, add_zero])

theorem valF_mk (x : Fˣ) : valF (SFin.mk 𝔪 k x) = L3P.valS (𝔪 := 𝔪) (x : F) := rfl

theorem valF_sEmb {x : F} (hx : x ≠ 0) : valF (sEmb 𝔪 k x).2.2 = L3P.valS (𝔪 := 𝔪) x := by
  rw [sEmb_fin hx, valF_mk, Units.val_mk0]

theorem valF_add [Fintype (L3P.SP 𝔪)] (y z : SFin 𝔪 k) : valF (y + z) = valF y + valF z := by
  obtain ⟨x, rfl⟩ := SFin.mk_surjective y
  obtain ⟨x', rfl⟩ := SFin.mk_surjective z
  rw [← SFin.mk_mul, valF_mk, valF_mk, valF_mk, Units.val_mul]
  exact L3P.valS_mul x.ne_zero x'.ne_zero

theorem sEmb_fst_eq_logK {x : F} (hx : x ≠ 0) : (sEmb 𝔪 k x).1 = L3P.logK x := by
  funext w; rw [sEmb_fst hx, L3P.logK_apply]

instance instCountableSUnit : Countable (SUnit 𝔪) := by
  have := countable_field F
  exact Function.Injective.countable (f := fun u : SUnit 𝔪 => ((u : Fˣ) : F))
    (fun a b h => Subtype.ext (Units.ext h))

instance instCountableSClass : Countable (SClass 𝔪) := QuotientGroup.mk_surjective.countable

/-- The `S`-unit coset representative of a class. -/
def uRep (s : SClass 𝔪) : SUnit 𝔪 := Function.surjInv QuotientGroup.mk_surjective s

theorem mk_uRep (s : SClass 𝔪) : (QuotientGroup.mk (uRep s) : SClass 𝔪) = s :=
  Function.surjInv_eq _ s

theorem sUnit_ne_zero (ε : SUnit 𝔪) : ((ε : Fˣ) : F) ≠ 0 := (ε : Fˣ).ne_zero

/-- `Γ = U_S⁶`. -/
abbrev Gam (𝔪 : Ideal (𝓞 F)) : Subgroup (SUnit 𝔪) := (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range

/-- `U_S/U_S⁶ × Γ ≃ U_S`, `(s, γ) ↦ u_s γ`. -/
def unitEquiv : SClass 𝔪 × Gam 𝔪 ≃ SUnit 𝔪 where
  toFun p := uRep p.1 * (p.2 : SUnit 𝔪)
  invFun u := ((QuotientGroup.mk u : SClass 𝔪), ⟨(uRep (QuotientGroup.mk u : SClass 𝔪))⁻¹ * u, by
    rw [← QuotientGroup.leftRel_apply, ← Quotient.eq'']
    exact (mk_uRep _)⟩)
  left_inv p := by
    obtain ⟨s, γ⟩ := p
    have h1 : (QuotientGroup.mk (uRep s * (γ : SUnit 𝔪)) : SClass 𝔪) = s := by
      refine (QuotientGroup.eq.2 ?_).trans (mk_uRep s)
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem γ.2
    refine Prod.ext h1 (Subtype.ext ?_)
    simp only
    rw [h1, inv_mul_cancel_left]
  right_inv u := by
    simp only [mul_inv_cancel_left]

/-! ### The weights -/

section Weights

variable [Fintype (L3P.SP 𝔪)]

/-- `Ω(−log y, val y)`. -/
def rho0 (y : SModel 𝔪 k) : ℝ := L3P.Omg (𝔪 := 𝔪) (-y.1) (valF y.2.2)

theorem rho0_nonneg (y : SModel 𝔪 k) : 0 ≤ rho0 y := L3P.Omg_nonneg _ _

theorem measurable_rho0 : Measurable (rho0 (𝔪 := 𝔪) (k := k)) := by
  have : rho0 (𝔪 := 𝔪) (k := k) = fun y => (L3P.D0 F).indicator (fun _ => (1 : ℝ)) (-y.1) *
      (L3P.Bset 𝔪).indicator (fun _ => (1 : ℝ)) (valF y.2.2) := rfl
  rw [this]
  refine Measurable.mul ?_ ?_
  · exact (measurable_const.indicator L3P.measurableSet_D0).comp measurable_fst.neg
  · exact (measurable_of_countable (fun y : SFin 𝔪 k =>
      (L3P.Bset 𝔪).indicator (fun _ => (1 : ℝ)) (valF y))).comp (measurable_snd.comp measurable_snd)

theorem hasSum_rho0 (y : SModel 𝔪 k) :
    HasSum (fun ε : SUnit 𝔪 => rho0 (sEmb 𝔪 k ((ε : Fˣ) : F) + y)) (torsionOrder F : ℝ) := by
  have h := L3P.hasSum_Omg (𝔪 := 𝔪) (-y.1) (valF y.2.2)
  have h' := (Set.unitEquivUnitsInteger (placesOf 𝔪) F).toEquiv.hasSum_iff.mpr h
  refine h'.congr_fun fun ε => ?_
  simp only [Function.comp_apply, rho0, Prod.fst_add, Prod.snd_add, valF_add,
    valF_sEmb (sUnit_ne_zero ε), sEmb_fst_eq_logK (sUnit_ne_zero ε), L3P.LxU, L3P.LkU]
  congr 1
  · rw [neg_add, sub_eq_add_neg, add_comm]; rfl
  · rw [add_comm]; rfl

/-- The `Γ`-partition of unity. -/
def rho (y : SModel 𝔪 k) : ℝ :=
  (torsionOrder F : ℝ)⁻¹ * ∑' s : SClass 𝔪, rho0 (sEmb 𝔪 k ((uRep s : Fˣ) : F) + y)

theorem rho_nonneg (y : SModel 𝔪 k) : 0 ≤ rho y :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (tsum_nonneg fun _ => rho0_nonneg _)

theorem hasSum_rho (y : SModel 𝔪 k) :
    HasSum (fun γ : Gam 𝔪 => rho (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y)) 1 := by
  have h := (unitEquiv (𝔪 := 𝔪)).hasSum_iff.mpr (hasSum_rho0 (𝔪 := 𝔪) (k := k) y)
  have h2 : HasSum (fun p : Gam 𝔪 × SClass 𝔪 =>
      rho0 (sEmb 𝔪 k ((uRep p.2 : Fˣ) : F) + (sEmb 𝔪 k (((p.1 : SUnit 𝔪) : Fˣ) : F) + y)))
      (torsionOrder F : ℝ) := by
    have := (Equiv.prodComm (Gam 𝔪) (SClass 𝔪)).hasSum_iff.mpr h
    refine this.congr_fun fun p => ?_
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
      unitEquiv, Equiv.coe_fn_mk, Subgroup.coe_mul, Units.val_mul]
    rw [sEmb_mul (sUnit_ne_zero _) (sUnit_ne_zero _), add_assoc]
  have h3 := h2.prod_fiberwise fun γ => (h2.summable.prod_factor γ).hasSum
  have hμ : (torsionOrder F : ℝ) ≠ 0 := by
    exact_mod_cast torsionOrder_ne_zero F
  have h4 := h3.mul_left (torsionOrder F : ℝ)⁻¹
  rw [inv_mul_cancel₀ hμ] at h4
  exact h4

theorem rho_add_rot (y : SModel 𝔪 k) (φ : InfinitePlace F → AddCircle (2 * Real.pi)) :
    rho (y + ((0, φ, 0) : SModel 𝔪 k)) = rho y := by
  simp only [rho, rho0]
  congr 2
  funext s
  congr 1 <;> simp

theorem measurable_rho : Measurable (rho (𝔪 := 𝔪) (k := k)) := by
  refine measurable_const.mul ?_
  exact Measurable.tsum fun s => (measurable_rho0).comp (measurable_const_add _)

end Weights

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3V_Cut: the candidate cut `L3V_CutKP` (the integrated cubic-theta functional equation)

For a row `r = (𝔟, υ)` and `l > 0`, the forward theta average `T_m(l)` (Lemma 6.1, first formula,
`eq:reflection-unreflected`; Cut63V's left side verbatim) equals the reflected expansion of
`eq:reflection-theta-average` *before* any digit sum is evaluated: the sum over the nonconstant
rational frequencies `ν ∈ F^× / U_S^6` of
* the exterior local Whittaker product `∏_P E_P(ν)`, with
  - `E_P(ν) = W_P(a(ν))` (5.4) for `P ∤ 𝔟`;
  - `E_P(ν) = ∑_{v mod P} α_{P,j}(v) W_P(a(ν) w n(v/p))` for `P ∣ 𝔟`, `j = v_P(𝔟) mod 6`, with the
    masks (6.4) and, for `v ≠ 0`, `W_P(a(p^{e−2}t) w n(v/p)) = W_e χ(t)^{4+2e} χ(v)^4 ψ_P(p^{e−1}t/v)`
    (the per-digit value in the proof of Lemma 6.2), `W_P(a(ν))` for `v = 0`;
* the separated `S`-character `L_υ(ν)^{-1}` and the sheet profile `H_{υ,[ν]}(|ν|_S / l)` of
  `eq:reflection-S-unfolding`/`eq:reflection-profiles`.
Here `lsym P t = χ_P(t)` for a `P`-unit `t ∈ F` (`0` otherwise) and `ladd P w = ψ_P(w/p)` for
`P`-integral `w` (`ψ_P(y/p) = e(−y/p)` for `y ∈ R`), both through a chosen representation by
elements of `R`. Every such `ν` with a nonzero exterior product has `ν b² ∈ R` (`b = gen 𝔟`), so the frequencies are
written `ν = x / b²` with `x` running over `RowClass 𝔪 ≅ (R ∖ 0)/U_S^6`; and `E_P = 1` off the primes
of `x b`. This packages Prop 5.1 (Kazhdan–Patterson), Lemmas 5.3–5.4, the local Weyl lift identity of
Lemma 6.2 and the two orbit unfoldings. -/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Defs: local symbols at an exterior prime, on elements of `F`

Internal definitions; the cut `L3V_CutKP` inlines them as `let`s (no new bundle):
* `localSymbol ι 𝔪 P t`: `χ_P(t)` for a `P`-unit `t ∈ F` (as `χ_P(y) conj χ_P(z)` for any
  `t = y / z` with `y, z ∈ R` prime to `P`), and `0` if `t` is not a `P`-unit;
* `localAddChar g P w`: `ψ_P(w / p)` for a `P`-integral `w ∈ F`, `p = gen P`, i.e. `e(−y / p)` for
  any `y ∈ R` with `y ≡ w (mod P)`.
-/

namespace ArtinPrimitiveRoots

namespace L3V

open NumberField

variable {F : Type*} [Field F] [NumberField F]

open Classical in
/-- The sextic residue symbol `χ_P(t)` of a `P`-unit `t ∈ F`: `χ_P(y) · conj χ_P(z)` for a
representation `z t = y` with `y, z ∈ R` and `z ∉ P R` (a choice; the value does not depend on it);
`0` if there is none, and `0` (through `χ_P(y) = 0`) when `t ∈ P`. -/
noncomputable def localSymbol (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (t : F) : ℂ :=
  if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      (yz.2 : F) * t = (yz.1 : F) then
    sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
  else 0

open Classical in
/-- The local additive character `ψ_P(w / p)` of the standard character at the exterior prime `P`,
for `P`-integral `w ∈ F`, with `p` the allowed generator of `P`: `e(−y / p)` for some `y ∈ R` with
`z (w − y) ∈ P R` for some `z ∈ R ∖ P R` (a choice; `0` if there is none). By the product formula
`ψ_P(y / p) = conj e(y / p) = e(−y / p)` for `y ∈ R`. -/
noncomputable def localAddChar {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (P : Ideal (𝓞 F)) (w : F) : ℂ :=
  if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
    sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
  else 0

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Base: the local data of `L3V_CutKP` as top-level definitions, and the cut's data

* `Wv`, `Wsph`, `tau`, `mask`, `Wweyl`, `Eloc`: the `let`s of `L3V_CutKP`; `Rsum`: the nonzero-digit
  part of `Eloc`.
* `Data χ g`: the objects the cut provides for one `(𝔪, χ, g)`; `data_of_cut`.
-/

namespace ArtinPrimitiveRoots

namespace L3V

open NumberField UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- `W_P(a(p^e))` of (5.4). -/
noncomputable def Wv (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
  else if e % 3 = 1 then
    (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
  else 0

/-- `W_P(a(p^{e₀} t))`. -/
noncomputable def Wsph (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e₀ : ℤ) (t : F) : ℂ :=
  if e₀ < 0 then 0 else localSymbol ι 𝔪 P t ^ (2 * e₀.toNat) * Wv g P e₀.toNat

/-- `τ_{P,j}`. -/
noncomputable def tau (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ) : ℂ :=
  ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
    starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
      sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))

open Classical in
/-- The mask `α_{P,j}` of (6.4). -/
noncomputable def mask (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ)
    (v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ :=
  if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
  else (tau g P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j

/-- The per-digit Weyl value `W_P(a(p^{e−2} t) w n(v/p))`, `e = e₀ + 2`. -/
noncomputable def Wweyl (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e₀ : ℤ) (t : F)
    (v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ :=
  if e₀ + 2 < 0 then 0 else
    Wv g P (e₀ + 2).toNat * localSymbol ι 𝔪 P t ^ (4 + 2 * (e₀ + 2).toNat) *
      sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
      localAddChar g P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))

open Classical in
/-- The exterior local factor `E_P`. -/
noncomputable def Eloc (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (k : ℕ) (e₀ : ℤ) (t : F) : ℂ :=
  if k = 0 then Wsph g P e₀ t else
    ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
      mask g P (k % 6) v * (if v = 0 then Wsph g P e₀ t else Wweyl g P e₀ t v)

open Classical in
/-- The nonzero-digit part of `E_P`. -/
noncomputable def Rsum (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ) (e₀ : ℤ) (t : F) : ℂ :=
  ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
    mask g P j v * (if v = 0 then 0 else Wweyl g P e₀ t v)

/-- The monomial exponent `b(j, e)` of (6.15). -/
def bexp (j e : ℕ) : ℕ := if e = 0 then 8 + 5 * j else 4 + 2 * e

/-- `ν = x / b²` for the frequency class `z` and row `r`. -/
noncomputable def nu (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) : F :=
  (rowElt g z : F) / (g.gen r.1.1 : F) ^ 2

/-- `v_P(ν)`. -/
noncomputable def e0 (r z : RowClass 𝔪) (P : Ideal (𝓞 F)) : ℤ :=
  ((normalizedFactors z.1.1).count P : ℤ) - 2 * ((normalizedFactors r.1.1).count P : ℤ)

/-- The exterior product `∏_P E_P(ν)`. -/
noncomputable def Eprod (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) : ℂ :=
  ∏ P ∈ (normalizedFactors (z.1.1 * r.1.1)).toFinset,
    Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P)
      (nu g r z * (g.gen P : F) ^ (-(e0 r z P)))

/-- The forward theta average (Cut63V's left side). -/
noncomputable def fwd (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) (V : ℝ → ℝ) (r : RowClass 𝔪)
    (l : ℝ) : ℂ :=
  ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
      {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
    gaussPhase g 2 p.1.1 /
        ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
      χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
      residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
      ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ)

/-- The data provided by the cut for one `(𝔪, χ, g)`. -/
structure Data (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) where
  V : ℝ → ℝ
  𝒱 : Type
  grp : CommGroup 𝒱
  fin : Fintype 𝒱
  cls : F → 𝒱
  L : SClass 𝔪 → F → ℂ
  H : SClass 𝔪 → 𝒱 → ℝ → ℂ
  α : ℝ
  hα : 0 < α
  hcls : ∀ a b : F, a ≠ 0 → b ≠ 0 → cls (a * b) = cls a * cls b
  hcls6 : ∀ ε : SUnit 𝔪, cls (((ε : Fˣ) : F) ^ 6) = 1
  hL : ∀ υ (a b : F), a ≠ 0 → b ≠ 0 → L υ (a * b) = L υ a * L υ b
  hLn : ∀ υ (a : F), a ≠ 0 → ‖L υ a‖ = 1
  hLu : ∀ υ (ε : SUnit 𝔪), L υ ((ε : Fˣ) : F) = 1
  hH : ∀ υ κ, ContDiff ℝ 2 (fun t => H υ κ (Real.exp t))
  hHb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ κ, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
    ‖iteratedDeriv j (fun t => H υ κ (Real.exp t)) t‖ ≤
      C * min (Real.exp (α * t)) (Real.exp (-(N * t)))
  hid : ∀ (r : RowClass 𝔪) (l : ℝ), 0 < l →
    fwd g χ V r l = ∑' z : RowClass 𝔪, Eprod g r z * (L r.2 (nu g r z))⁻¹ *
      H r.2 (cls (nu g r z)) ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l))

attribute [instance] Data.grp Data.fin

/-- The `V`-clause of the cut (shared with Cut63V). -/
def VClause (V : ℝ → ℝ) : Prop :=
  ∃ (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
    (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
      MellinConvergent (fun t => (V t : ℂ)) s ∧
      mellin (fun t => (V t : ℂ)) s =
        (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr)

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3X_Pack: the two cuts with top-level definitions

* `fpF κ m`: the forward `S`-Whittaker function `1_{y_f = 0} ∏_w ω_{m_w}(y_w) κ(|y_w|_w)`.
* `coefF'` (the cut's forward coefficient), `Fw`, `Rf`: the forward and the reflected
  nonconstant Fourier expansions.
* `KPk g k`, `SBk g k`, `SLk χ g k`: the conclusions of the three cuts at level `k`;
  `kp_unpack`, `sb_unpack`, `sl_unpack`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The rotation by `φ` at the place `w`. -/
def rot (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) : SModel 𝔪 k := (0, Pi.single w φ, 0)

/-- The forward `S`-Whittaker function. -/
def fpF (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (y : SModel 𝔪 k) : ℂ :=
  if y.2.2 = 0 then
    ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
  else 0

/-- `γ ∈ Γ` as an element of `F`. -/
def gamF (γ : Gam 𝔪) : F := (((γ : SUnit 𝔪) : Fˣ) : F)

/-- The class of `x` in `F_S^× / F_S^{×6}`. -/
def clsF (x : F) : SFinCls 𝔪 k := QuotientAddGroup.mk (sEmb 𝔪 k x).2.2

/-- The cut's forward coefficient (the same as `L3X.coefF`, written with `L3V.Wsph`). -/
def coefF' (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (z : RowClass 𝔪) : ℂ :=
  residueSymbol ι 𝔪 𝔟 (rowElt g z) *
    ∏ P ∈ (normalizedFactors z.1.1).toFinset,
      L3V.Wsph g P ((normalizedFactors z.1.1).count P : ℤ)
        ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))

/-- The forward nonconstant Fourier expansion at `y`. -/
def Fw (g : AllowedGen ι 𝔪) (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (𝔟 : Ideal (𝓞 F))
    (y : SModel 𝔪 k) : ℂ :=
  ∑' p : RowClass 𝔪 × Gam 𝔪,
    coefF' g 𝔟 p.1 * fpF κ m (sEmb 𝔪 k (gamF p.2 * (rowElt g p.1 : F)) + y)

/-- The reflected nonconstant Fourier expansion at `y`. -/
def Rf (g : AllowedGen ι 𝔪) (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (r : RowClass 𝔪)
    (y : SModel 𝔪 k) : ℂ :=
  ∑' p : RowClass 𝔪 × Gam 𝔪,
    L3V.Eprod g r p.1 * Fm (clsF (L3V.nu g r p.1)) (sEmb 𝔪 k (gamF p.2 * L3V.nu g r p.1) - y)

/-- The conclusion of `L3X_CutKP` at level `k`. -/
def KPk (g : AllowedGen ι 𝔪) (k : ℕ) : Prop :=
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
      ∀ (r : RowClass 𝔪) (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) (y : SModel 𝔪 k),
        Fw g κ m r.1.1 (y + rot w φ) - Rf g Fm r (y + rot w φ) = Fw g κ m r.1.1 y - Rf g Fm r y

theorem kp_unpack (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) (h : L3J_CutKP n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ g : AllowedGen ι 𝔪, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → KPk g k := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs g => ?_⟩
  obtain ⟨k₀, hk⟩ := hN 𝔪 h𝔪 hs g
  refine ⟨k₀, fun k hk' => ?_⟩
  obtain ⟨κ, cκ, Aκ, α, h1, h2, h3, h4, h5, h6, h7, hrest⟩ := hk k hk'
  refine ⟨κ, cκ, Aκ, α, h1, h2, h3, h4, h5, h6, h7, fun m hm => ?_⟩
  obtain ⟨Fm, bf, g1, g2, g3, g4, g5, hD⟩ := hrest m hm
  exact ⟨Fm, bf, g1, g2, g3, g4, g5, fun r w φ y => hD r.1.1 r.1.2 w φ y⟩

/-- The `S`-character `L(y) = L_f(y_f) ∏_w ω_{m_w}(y_w)`. -/
def Lmod (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ) (y : SModel 𝔪 k) : ℂ :=
  Lf y.2.2 * ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ)

/-- The conclusion of `L3X_CutSB` at level `k`. -/
def SBk (g : AllowedGen ι 𝔪) (k : ℕ) : Prop :=
  Finite (SFinCls 𝔪 k) ∧
    ∃ B : AddSubgroup (SFinCls 𝔪 k), ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪,
      ((QuotientAddGroup.mk (sEmb 𝔪 k ((ε : Fˣ) * (g.gen 𝔄 : F))).2.2 : SFinCls 𝔪 k) ∈ B ↔
        ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)

/-- The conclusion of `L3X_CutSL` at level `k`. -/
def SLk (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (k : ℕ) : Prop :=
  ∀ υ : SClass 𝔪, ∃ (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ),
    (∀ w, m w = 1 ∨ m w = -1) ∧ (∀ a b, Lf (a + b) = Lf a * Lf b) ∧ (∀ a, ‖Lf a‖ = 1) ∧
    (∀ ε : SUnit 𝔪, Lmod Lf m (sEmb 𝔪 k ((ε : Fˣ) : F)) = 1) ∧
    ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 →
      Lmod Lf m (sEmb 𝔪 k (g.gen 𝔄 : F)) = χ.thetaChar g 𝔄 * residueSymbol ι 𝔪 𝔄 υ.rep

theorem sb_unpack (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) (h : L3X_CutSB n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ g : AllowedGen ι 𝔪, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → SBk g k := h

theorem sl_unpack (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) (h : L3X_CutSL n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → SLk χ g k := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs χ g => ?_⟩
  obtain ⟨k₀, hk⟩ := hN 𝔪 h𝔪 hs χ g
  refine ⟨k₀, fun k hk' υ => ?_⟩
  obtain ⟨Lf, m, j1, j2, j3, j4, j5⟩ := hk k hk' υ
  exact ⟨Lf, m, j1, j2, j3, j4, j5⟩

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3X_Unf: changes of variables and the `Γ`-unfolding on sheets

* `integral_add_sEmb`: `∫ H(x y) dμ_a = ∫ H dμ_{a + log|x|}` for `x ∈ F^×`.
* `integral_sEmb_sub`: `∫ H(x / y) dμ_a = ∫ H dμ_{log|x| − a}`.
* `integral_add_rot`: rotations preserve every sheet measure.
* `lintegral_unfold`, `integral_unfold`: `Σ_{γ ∈ Γ} ∫ ρ(y) H(γ y) dμ_a = ∫ H dμ_a`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain NumberField.Units

set_option linter.unusedSectionVars false

open scoped Classical ENNReal

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

variable (w₀ : InfinitePlace F)

theorem measurableEmbedding_add (d : SModel 𝔪 k) :
    MeasurableEmbedding (· + d : SModel 𝔪 k → SModel 𝔪 k) :=
  (MeasurableEquiv.addRight d).measurableEmbedding

theorem measurableEmbedding_neg :
    MeasurableEmbedding (Neg.neg : SModel 𝔪 k → SModel 𝔪 k) :=
  (MeasurableEquiv.neg (SModel 𝔪 k)).measurableEmbedding

theorem integral_add (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (d : SModel 𝔪 k) (H : SModel 𝔪 k → ℂ) :
    ∫ y, H (y + d) ∂(shMeasure w₀ 𝔪 k a) = ∫ y, H y ∂(shMeasure w₀ 𝔪 k (a + lnorm d)) :=
  (mp_add w₀ h𝔪 a d).integral_comp (measurableEmbedding_add d) H

theorem lintegral_add (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (d : SModel 𝔪 k) (H : SModel 𝔪 k → ℝ≥0∞) :
    ∫⁻ y, H (y + d) ∂(shMeasure w₀ 𝔪 k a) = ∫⁻ y, H y ∂(shMeasure w₀ 𝔪 k (a + lnorm d)) :=
  (mp_add w₀ h𝔪 a d).lintegral_comp_emb (measurableEmbedding_add d) H

theorem integral_neg (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (H : SModel 𝔪 k → ℂ) :
    ∫ y, H (-y) ∂(shMeasure w₀ 𝔪 k a) = ∫ y, H y ∂(shMeasure w₀ 𝔪 k (-a)) :=
  (mp_neg w₀ h𝔪 a).integral_comp measurableEmbedding_neg H

theorem lintegral_neg (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (H : SModel 𝔪 k → ℝ≥0∞) :
    ∫⁻ y, H (-y) ∂(shMeasure w₀ 𝔪 k a) = ∫⁻ y, H y ∂(shMeasure w₀ 𝔪 k (-a)) :=
  (mp_neg w₀ h𝔪 a).lintegral_comp_emb measurableEmbedding_neg H

/-- `y ↦ d − y` sends `μ_a` to `μ_{lnorm d − a}`. -/
theorem integral_sub_left (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (d : SModel 𝔪 k) (H : SModel 𝔪 k → ℂ) :
    ∫ y, H (d - y) ∂(shMeasure w₀ 𝔪 k a) = ∫ y, H y ∂(shMeasure w₀ 𝔪 k (lnorm d - a)) := by
  have : (fun y => H (d - y)) = fun y => (fun z => H (z + d)) (-y) := by
    funext y; congr 1; abel
  rw [this, integral_neg w₀ h𝔪 a (fun z => H (z + d)), integral_add w₀ h𝔪 (-a) d H]
  congr 2; ring

theorem lintegral_sub_left (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (d : SModel 𝔪 k) (H : SModel 𝔪 k → ℝ≥0∞) :
    ∫⁻ y, H (d - y) ∂(shMeasure w₀ 𝔪 k a) = ∫⁻ y, H y ∂(shMeasure w₀ 𝔪 k (lnorm d - a)) := by
  have : (fun y => H (d - y)) = fun y => (fun z => H (z + d)) (-y) := by
    funext y; congr 1; abel
  rw [this, lintegral_neg w₀ h𝔪 a (fun z => H (z + d)), lintegral_add w₀ h𝔪 (-a) d H]
  congr 2; ring

theorem lnorm_rot (h𝔪 : 𝔪 ≠ ⊥) (φ : InfinitePlace F → AddCircle (2 * Real.pi)) :
    lnorm ((0, φ, 0) : SModel 𝔪 k) = 0 := by
  simp [lnorm, SFin.norm_zero h𝔪]

theorem integral_add_rot (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (φ : InfinitePlace F → AddCircle (2 * Real.pi))
    (H : SModel 𝔪 k → ℂ) :
    ∫ y, H (y + ((0, φ, 0) : SModel 𝔪 k)) ∂(shMeasure w₀ 𝔪 k a) = ∫ y, H y ∂(shMeasure w₀ 𝔪 k a) := by
  rw [integral_add w₀ h𝔪, lnorm_rot h𝔪, add_zero]

/-! ### `Γ`-unfolding -/

section Unfold

variable [Fintype (L3P.SP 𝔪)]

theorem sEmb_gam_inv (γ : Gam 𝔪) :
    sEmb 𝔪 k ((((γ⁻¹ : Gam 𝔪) : SUnit 𝔪) : Fˣ) : F) = -sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) := by
  rw [show ((((γ⁻¹ : Gam 𝔪) : SUnit 𝔪) : Fˣ) : F) = ((((γ : SUnit 𝔪) : Fˣ) : F))⁻¹ by
    simp [Units.val_inv_eq_inv_val]]
  exact sEmb_inv (sUnit_ne_zero _)

theorem hasSum_rho_sub (y : SModel 𝔪 k) :
    HasSum (fun γ : Gam 𝔪 => rho (y - sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F))) 1 := by
  have h := (Equiv.inv (Gam 𝔪)).hasSum_iff.mpr (hasSum_rho (𝔪 := 𝔪) (k := k) y)
  refine h.congr_fun fun γ => ?_
  simp only [Function.comp_apply, Equiv.inv_apply, sEmb_gam_inv]
  congr 1; abel

theorem lintegral_unfold (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (H : SModel 𝔪 k → ℝ≥0∞) (hH : Measurable H) :
    ∑' γ : Gam 𝔪, ∫⁻ y, ENNReal.ofReal (rho y) *
        H (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y) ∂(shMeasure w₀ 𝔪 k a) =
      ∫⁻ y, H y ∂(shMeasure w₀ 𝔪 k a) := by
  have h1 : ∀ γ : Gam 𝔪, ∫⁻ y, ENNReal.ofReal (rho y) *
        H (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y) ∂(shMeasure w₀ 𝔪 k a) =
      ∫⁻ y, ENNReal.ofReal (rho (y - sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F))) * H y
        ∂(shMeasure w₀ 𝔪 k a) := by
    intro γ
    set d := sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F)
    have hd : lnorm d = 0 := lnorm_sEmb_unit h𝔪 _
    have := lintegral_add w₀ h𝔪 a d
      (fun y => ENNReal.ofReal (rho (y - d)) * H y)
    simp only [add_sub_cancel_right, hd, add_zero] at this
    rw [← this]
    congr 1; funext y; rw [add_comm d y]
  simp_rw [h1]
  rw [← lintegral_tsum (f := fun (γ : Gam 𝔪) (y : SModel 𝔪 k) =>
    ENNReal.ofReal (rho (y - sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F))) * H y) fun γ =>
      ((ENNReal.measurable_ofReal.comp (measurable_rho.comp (measurable_sub_const _))).mul
        hH).aemeasurable]
  congr 1; funext y
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => rho_nonneg _)
    (hasSum_rho_sub y).summable, (hasSum_rho_sub y).tsum_eq, ENNReal.ofReal_one, one_mul]

theorem integral_unfold (h𝔪 : 𝔪 ≠ ⊥) (a : ℝ) (H : SModel 𝔪 k → ℂ) (hH : Measurable H)
    (hfin : ∫⁻ y, ‖H y‖ₑ ∂(shMeasure w₀ 𝔪 k a) ≠ ∞) :
    ∑' γ : Gam 𝔪, ∫ y, (rho y : ℂ) *
        H (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y) ∂(shMeasure w₀ 𝔪 k a) =
      ∫ y, H y ∂(shMeasure w₀ 𝔪 k a) := by
  have h1 : ∀ γ : Gam 𝔪, ∫ y, (rho y : ℂ) *
        H (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y) ∂(shMeasure w₀ 𝔪 k a) =
      ∫ y, (rho (y - sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F)) : ℂ) * H y
        ∂(shMeasure w₀ 𝔪 k a) := by
    intro γ
    set d := sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F)
    have hd : lnorm d = 0 := lnorm_sEmb_unit h𝔪 _
    have := integral_add w₀ h𝔪 a d (fun y => (rho (y - d) : ℂ) * H y)
    simp only [add_sub_cancel_right, hd, add_zero] at this
    rw [← this]
    congr 1; funext y; rw [add_comm d y]
  simp_rw [h1]
  have hmeas : ∀ γ : Gam 𝔪, AEStronglyMeasurable (fun y => (rho (y -
      sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F)) : ℂ) * H y) (shMeasure w₀ 𝔪 k a) := fun γ =>
    ((Complex.measurable_ofReal.comp (measurable_rho.comp (measurable_sub_const _))).mul
      hH).aestronglyMeasurable
  rw [← integral_tsum hmeas]
  · congr 1; funext y
    rw [tsum_mul_right, ← Complex.ofReal_tsum, (hasSum_rho_sub y).tsum_eq, Complex.ofReal_one,
      one_mul]
  · have : ∀ γ : Gam 𝔪, ∫⁻ y, ‖(rho (y - sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F)) : ℂ) * H y‖ₑ
          ∂(shMeasure w₀ 𝔪 k a) =
        ∫⁻ y, ENNReal.ofReal (rho (y - sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F))) * ‖H y‖ₑ
          ∂(shMeasure w₀ 𝔪 k a) := by
      intro γ; congr 1; funext y
      rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (rho_nonneg _)]
    simp_rw [this]
    rw [← lintegral_tsum (f := fun (γ : Gam 𝔪) (y : SModel 𝔪 k) =>
      ENNReal.ofReal (rho (y - sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F))) * ‖H y‖ₑ) fun γ =>
        ((ENNReal.measurable_ofReal.comp (measurable_rho.comp (measurable_sub_const _))).mul
          hH.enorm).aemeasurable]
    convert hfin using 2
    funext y
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => rho_nonneg _)
      (hasSum_rho_sub y).summable, (hasSum_rho_sub y).tsum_eq, ENNReal.ofReal_one, one_mul]

end Unfold

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
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

theorem norm_toCircle (a : AddCircle (2 * Real.pi)) :
    ‖((AddCircle.toCircle a : Circle) : ℂ)‖ = 1 := Circle.norm_coe _

section Lmod

variable (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ)
  (hLf : ∀ a b, Lf (a + b) = Lf a * Lf b) (hLfn : ∀ a, ‖Lf a‖ = 1)

include hLf hLfn in
theorem Lf_zero : Lf 0 = 1 := by
  have h := hLf 0 0
  rw [add_zero] at h
  have h0 : Lf 0 ≠ 0 := by
    intro h0; have := hLfn 0; rw [h0, norm_zero] at this; exact zero_ne_one this
  have : Lf 0 * Lf 0 = Lf 0 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ h0 this

include hLf in
theorem Lmod_add (y z : SModel 𝔪 k) : Lmod Lf m (y + z) = Lmod Lf m y * Lmod Lf m z := by
  simp only [Lmod, Prod.snd_add, Prod.fst_add, Pi.add_apply, hLf]
  rw [Finset.prod_congr rfl (fun w _ => toCircle_zsmul_add (m w) _ _), Finset.prod_mul_distrib]
  ring

include hLfn in
theorem norm_Lmod (y : SModel 𝔪 k) : ‖Lmod Lf m y‖ = 1 := by
  simp only [Lmod, norm_mul, norm_prod, norm_toCircle, hLfn, Finset.prod_const_one, mul_one]

include hLf hLfn in
theorem Lmod_neg (y : SModel 𝔪 k) : Lmod Lf m (-y) = (Lmod Lf m y)⁻¹ := by
  have h := Lmod_add Lf m hLf y (-y)
  rw [add_neg_cancel] at h
  have h0 : Lmod Lf m (0 : SModel 𝔪 k) = 1 := by
    simp [Lmod, Lf_zero Lf hLf hLfn]
  rw [h0] at h
  exact eq_inv_of_mul_eq_one_right h.symm

include hLf hLfn in
theorem Lmod_sub (y z : SModel 𝔪 k) :
    Lmod Lf m (y - z) = Lmod Lf m y * (Lmod Lf m z)⁻¹ := by
  rw [sub_eq_add_neg, Lmod_add Lf m hLf, Lmod_neg Lf m hLf hLfn]

theorem Lmod_rot (y : SModel 𝔪 k) (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) :
    Lmod Lf m (y + rot w φ) =
      Lmod Lf m y * ((AddCircle.toCircle (m w • φ) : Circle) : ℂ) := by
  simp only [Lmod, rot, Prod.snd_add, Prod.fst_add, Pi.add_apply, add_zero]
  rw [Finset.prod_congr rfl (fun x _ => toCircle_zsmul_add (m x) _ _), Finset.prod_mul_distrib,
    mul_assoc]
  congr 2
  rw [Finset.prod_eq_single w]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem Lmod_rsh (y : SModel 𝔪 k) (w : InfinitePlace F) (s : ℝ) :
    Lmod Lf m (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)) = Lmod Lf m y := by
  simp [Lmod]

theorem continuous_toCircle_zsmul (n : ℤ) :
    Continuous fun θ : AddCircle (2 * Real.pi) => ((AddCircle.toCircle (n • θ) : Circle) : ℂ) :=
  continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp (continuous_zsmul n))

theorem measurable_Lmod : Measurable (Lmod (𝔪 := 𝔪) (k := k) Lf m) := by
  refine ((measurable_of_countable Lf).comp (measurable_snd.comp measurable_snd)).mul ?_
  refine Finset.measurable_prod _ fun w _ => ?_
  exact (continuous_toCircle_zsmul (m w)).measurable.comp ((measurable_pi_apply w).comp
      (measurable_fst.comp measurable_snd))

end Lmod

/-! ### The weight -/

section Weight

variable (B : AddSubgroup (SFinCls 𝔪 k)) (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ)

/-- `1_B`. -/
def Bind (c : SFinCls 𝔪 k) : ℂ := if c ∈ B then 1 else 0

theorem norm_Bind_le (c : SFinCls 𝔪 k) : ‖Bind B c‖ ≤ 1 := by
  unfold Bind; split_ifs <;> simp

theorem Bind_neg (c : SFinCls 𝔪 k) : Bind B (-c) = Bind B c := by
  simp [Bind, neg_mem_iff]

/-- `1_B([y]) L(y)⁻¹`. -/
def psi (y : SModel 𝔪 k) : ℂ :=
  Bind B (QuotientAddGroup.mk y.2.2) * (Lmod Lf m y)⁻¹

/-- `Φ = ρ · 1_B([y]) L(y)⁻¹`. -/
def Phi [Fintype (L3P.SP 𝔪)] (y : SModel 𝔪 k) : ℂ := (rho y : ℂ) * psi B Lf m y

theorem fin_sEmb_gam (γ : Gam 𝔪) :
    (QuotientAddGroup.mk (sEmb 𝔪 k (gamF γ)).2.2 : SFinCls 𝔪 k) = 0 := by
  obtain ⟨ε, hε⟩ := γ.2
  have hγ : gamF γ = (((ε : SUnit 𝔪) : Fˣ) : F) ^ 6 := by
    simp only [gamF, ← hε, powMonoidHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
  rw [hγ, sEmb_pow (sUnit_ne_zero ε)]
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨(sEmb 𝔪 k (((ε : SUnit 𝔪) : Fˣ) : F)).2.2, by simp [nsmulAddMonoidHom]⟩

variable (hLf : ∀ a b, Lf (a + b) = Lf a * Lf b) (hLfn : ∀ a, ‖Lf a‖ = 1)
  (hLu : ∀ ε : SUnit 𝔪, Lmod Lf m (sEmb 𝔪 k ((ε : Fˣ) : F)) = 1)

include hLf hLu in
theorem psi_gam_add (γ : Gam 𝔪) (y : SModel 𝔪 k) :
    psi B Lf m (sEmb 𝔪 k (gamF γ) + y) = psi B Lf m y := by
  have h2 : (QuotientAddGroup.mk (sEmb 𝔪 k (gamF γ) + y).2.2 : SFinCls 𝔪 k) =
      QuotientAddGroup.mk y.2.2 := by
    rw [Prod.snd_add, Prod.snd_add, QuotientAddGroup.mk_add, fin_sEmb_gam, zero_add]
  rw [psi, psi, h2, Lmod_add Lf m hLf]
  simp only [gamF, hLu, one_mul]

include hLfn in
theorem norm_psi_le (y : SModel 𝔪 k) : ‖psi B Lf m y‖ ≤ 1 := by
  rw [psi, norm_mul, norm_inv, norm_Lmod Lf m hLfn, inv_one, mul_one]
  exact norm_Bind_le B _

theorem psi_rot (y : SModel 𝔪 k) (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) :
    psi B Lf m (y + rot w φ) =
      psi B Lf m y * (((AddCircle.toCircle (m w • φ) : Circle) : ℂ))⁻¹ := by
  have h2 : (y + rot w φ).2.2 = y.2.2 := by simp [rot]
  rw [psi, psi, h2, Lmod_rot, mul_inv]
  ring

theorem measurable_psi : Measurable (psi (𝔪 := 𝔪) (k := k) B Lf m) := by
  refine ((measurable_of_countable (fun y : SFin 𝔪 k =>
    Bind B (QuotientAddGroup.mk y))).comp (measurable_snd.comp measurable_snd)).mul ?_
  exact (measurable_Lmod Lf m).inv

theorem measurable_Phi [Fintype (L3P.SP 𝔪)] : Measurable (Phi (𝔪 := 𝔪) (k := k) B Lf m) :=
  (Complex.measurable_ofReal.comp measurable_rho).mul (measurable_psi B Lf m)

include hLfn in
theorem norm_Phi_le [Fintype (L3P.SP 𝔪)] (y : SModel 𝔪 k) : ‖Phi B Lf m y‖ ≤ rho y := by
  rw [Phi, norm_mul, Complex.norm_real, Real.norm_of_nonneg (rho_nonneg y)]
  exact mul_le_of_le_one_right (rho_nonneg y) (norm_psi_le B Lf m hLfn y)

end Weight

/-! ### The forward `S`-function -/

section Fp

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ)

/-- `|fpF|` as a real function. -/
def fpAbs (y : SModel 𝔪 k) : ℝ := if y.2.2 = 0 then ∏ w, κ (Real.exp (y.1 w)) else 0

theorem norm_fpF (hκ0 : ∀ t, 0 ≤ κ t) (y : SModel 𝔪 k) : ‖fpF κ m y‖ = fpAbs κ y := by
  unfold fpF fpAbs
  split_ifs
  · rw [norm_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [norm_mul, norm_toCircle, one_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 _)]
  · simp

theorem fpAbs_nonneg (hκ0 : ∀ t, 0 ≤ κ t) (y : SModel 𝔪 k) : 0 ≤ fpAbs κ y := by
  unfold fpAbs; split_ifs
  · exact Finset.prod_nonneg fun _ _ => hκ0 _
  · exact le_rfl

theorem Lmod_inv_mul_fpF (Lf : SFin 𝔪 k → ℂ) (hLf : ∀ a b, Lf (a + b) = Lf a * Lf b)
    (hLfn : ∀ a, ‖Lf a‖ = 1) (y : SModel 𝔪 k) :
    (Lmod Lf m y)⁻¹ * fpF κ m y = (fpAbs κ y : ℂ) := by
  unfold fpF fpAbs Lmod
  split_ifs with h
  · rw [h, Lf_zero Lf hLf hLfn, one_mul, Finset.prod_mul_distrib, ← mul_assoc,
      inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun w _ => Circle.coe_ne_zero _), one_mul]
    push_cast; rfl
  · simp

theorem measurable_fpF (hκm : Measurable κ) : Measurable (fpF (𝔪 := 𝔪) (k := k) κ m) := by
  unfold fpF
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_singleton (0 : SFin 𝔪 k)).preimage (measurable_snd.comp measurable_snd)
  · refine Finset.measurable_prod _ fun w _ => ?_
    refine ((continuous_toCircle_zsmul (m w)).measurable.comp ((measurable_pi_apply w).comp
      (measurable_fst.comp measurable_snd))).mul ?_
    exact Complex.measurable_ofReal.comp (hκm.comp (Real.measurable_exp.comp
      ((measurable_pi_apply w).comp measurable_fst)))

theorem measurable_fpAbs (hκm : Measurable κ) : Measurable (fpAbs (𝔪 := 𝔪) (k := k) κ) := by
  unfold fpAbs
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_singleton (0 : SFin 𝔪 k)).preimage (measurable_snd.comp measurable_snd)
  · exact Finset.measurable_prod _ fun w _ => hκm.comp (Real.measurable_exp.comp
      ((measurable_pi_apply w).comp measurable_fst))

end Fp

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3X_Tsum: integrals of absolutely convergent series of measurable functions -/

namespace ArtinPrimitiveRoots.L3X

open MeasureTheory

open scoped ENNReal

theorem tsum_integral_of_lintegral {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    {f : ι → α → ℂ} (hf : ∀ i, Measurable (f i)) (h : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ∞) :
    Integrable (fun a => ∑' i, f i a) μ ∧ ∫ a, ∑' i, f i a ∂μ = ∑' i, ∫ a, f i a ∂μ ∧
      Summable (fun i => ∫ a, f i a ∂μ) := by
  have hmeas : Measurable fun a => ∑' i, f i a := Measurable.tsum hf
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, integral_tsum (fun i => (hf i).aestronglyMeasurable) h,
    ?_⟩
  · refine lt_of_le_of_lt (lintegral_mono fun a => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun i => (hf i).enorm.aemeasurable]
    exact h.lt_top
  · have hfin : ∀ i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ∞ := fun i =>
      ne_top_of_le_ne_top h (ENNReal.le_tsum i)
    have hs : Summable fun i => (∫⁻ a, ‖f i a‖ₑ ∂μ).toReal := ENNReal.summable_toReal h
    refine Summable.of_norm_bounded hs fun i => ?_
    refine (norm_integral_le_lintegral_norm _).trans ?_
    refine ENNReal.toReal_mono (hfin i) (le_of_eq ?_)
    congr 1; funext a; exact ofReal_norm (f i a)

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3X_Bd: sheet integrals of product majorants

`bmaj α N x = min(e^{αx}, e^{-Nx})`. For `−α < σ < N`, the sheet integral at `lnorm = a` of
`∏_w bmaj(log|y_w|) · bf(y_f)` is `≤ C e^{−σ a}` whenever `Σ bf(y_f) |y_f|^σ < ∞`
(the weighted-sup argument of Lemma 5.4: bound the `w₀` factor by `e^{−σ x₀}` and integrate the
others).
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The archimedean majorant `min(e^{αx}, e^{-Nx})`. -/
def bmaj (α N x : ℝ) : ℝ := min (Real.exp (α * x)) (Real.exp (-(N * x)))

theorem bmaj_nonneg (α N x : ℝ) : 0 ≤ bmaj α N x :=
  le_min (Real.exp_pos _).le (Real.exp_pos _).le

theorem continuous_bmaj (α N : ℝ) : Continuous (bmaj α N) := by
  unfold bmaj; fun_prop

theorem bmaj_le_exp {α N σ : ℝ} (h1 : -α ≤ σ) (h2 : σ ≤ N) (x : ℝ) :
    bmaj α N x ≤ Real.exp (-(σ * x)) := by
  rcases le_or_gt 0 x with hx | hx
  · refine (min_le_right _ _).trans (Real.exp_le_exp.2 ?_)
    nlinarith
  · refine (min_le_left _ _).trans (Real.exp_le_exp.2 ?_)
    nlinarith

theorem bmaj_add_le {α N : ℝ} (hα : 0 ≤ α) (hN : 0 ≤ N) (x δ : ℝ) :
    bmaj α N (x + δ) ≤ Real.exp ((α + N) * |δ|) * bmaj α N x := by
  unfold bmaj
  rw [mul_min_of_nonneg _ _ (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_add]
  refine min_le_min (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 ?_)
  · nlinarith [le_abs_self δ, neg_abs_le δ, abs_nonneg δ]
  · nlinarith [le_abs_self δ, neg_abs_le δ, abs_nonneg δ]

theorem integrable_bmaj_mul_exp {α N σ : ℝ} (h1 : -α < σ) (h2 : σ < N) :
    Integrable (fun x : ℝ => bmaj α N x * Real.exp (σ * x)) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => bmaj α N x * Real.exp (σ * x)) volume :=
    ((continuous_bmaj α N).mul (by fun_prop)).aestronglyMeasurable
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (integrableOn_exp_mul_Iic (a := α + σ) (by linarith) 0) hm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (bmaj_nonneg _ _ _) (Real.exp_pos _).le)]
    calc bmaj α N x * Real.exp (σ * x) ≤ Real.exp (α * x) * Real.exp (σ * x) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le
      _ = Real.exp ((α + σ) * x) := by rw [← Real.exp_add]; ring_nf
  · refine Integrable.mono' (integrableOn_exp_mul_Ioi (a := σ - N) (by linarith) 0) hm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (bmaj_nonneg _ _ _) (Real.exp_pos _).le)]
    calc bmaj α N x * Real.exp (σ * x) ≤ Real.exp (-(N * x)) * Real.exp (σ * x) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
      _ = Real.exp ((σ - N) * x) := by rw [← Real.exp_add]; ring_nf

variable (w₀ : InfinitePlace F)

theorem prod_eq_mul_prod_Wo (x : InfinitePlace F → ℝ) (f : ℝ → ℝ) :
    ∏ w, f (x w) = f (x w₀) * ∏ w : Wo w₀, f (x w) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀)]
  congr 1
  rw [Finset.prod_subtype (Finset.univ.erase w₀) (p := fun w => w ≠ w₀) (by simp)]

theorem prod_ext_eq (f : ℝ → ℝ) (x' : Wo w₀ → ℝ) (t : ℝ) :
    ∏ w, f (ext w₀ x' t w) = f t * ∏ w : Wo w₀, f (x' w) := by
  rw [prod_eq_mul_prod_Wo w₀ (ext w₀ x' t) f, ext_self]
  congr 1
  exact Finset.prod_congr rfl fun w _ => by rw [ext_of_ne w₀ x' t w.2]

theorem measurable_majorant (α N : ℝ) (bf : SFin 𝔪 k → ℝ) :
    Measurable fun y : SModel 𝔪 k => (∏ w, bmaj α N (y.1 w)) * bf y.2.2 := by
  refine Measurable.mul ?_ ((measurable_of_countable bf).comp (measurable_snd.comp measurable_snd))
  exact Finset.measurable_prod _ fun w _ =>
    (continuous_bmaj α N).measurable.comp ((measurable_pi_apply w).comp measurable_fst)

/-- The base form of the majorant bound. -/
theorem lintegral_majorant_base_le (h𝔪 : 𝔪 ≠ ⊥) {α N σ : ℝ}
    (hσ1 : -α < σ) (hσ2 : σ < N) (bf : SFin 𝔪 k → ℝ) (hbf0 : ∀ y, 0 ≤ bf y)
    (hbf : Summable (fun y => bf y * (SFin.norm y) ^ σ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ,
      ∫⁻ p, ENNReal.ofReal ((∏ w, bmaj α N ((slice w₀ a p).1 w)) * bf (slice w₀ a p).2.2)
          ∂(baseMeasure w₀ 𝔪 k) ≤
        ENNReal.ofReal (C * Real.exp (-(σ * a))) := by
  set φ : ℝ → ℝ := fun x => bmaj α N x * Real.exp (σ * x)
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => mul_nonneg (bmaj_nonneg _ _ _) (Real.exp_pos _).le
  have hφi : Integrable φ := integrable_bmaj_mul_exp hσ1 hσ2
  set Pp : (Wo w₀ → ℝ) → ℝ := fun x' => ∏ w : Wo w₀, φ (x' w)
  have hPpi : Integrable Pp := by
    have := Integrable.fintype_prod (ι := Wo w₀) (μ := fun _ => (volume : Measure ℝ))
      (f := fun _ => φ) (fun _ => hφi)
    simpa [Pp, volume_pi] using this
  have hPp0 : ∀ x', 0 ≤ Pp x' := fun x' => Finset.prod_nonneg fun w _ => hφ0 _
  set I : ℝ := ∫ x', Pp x'
  have hI0 : 0 ≤ I := integral_nonneg hPp0
  set S : ℝ := ∑' y, bf y * (SFin.norm y) ^ σ
  have hS0 : 0 ≤ S := tsum_nonneg fun y =>
    mul_nonneg (hbf0 y) (Real.rpow_nonneg (SFin.norm_pos h𝔪 y).le _)
  set A : ℝ := (volume (Set.univ : Set (InfinitePlace F → AddCircle (2 * Real.pi)))).toReal
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  refine ⟨S * I * A, by positivity, fun a => ?_⟩
  -- pointwise bound
  have hpt : ∀ p : Base w₀ 𝔪 k,
      ENNReal.ofReal ((∏ w, bmaj α N ((slice w₀ a p).1 w)) * bf (slice w₀ a p).2.2) ≤
        ENNReal.ofReal (Real.exp (-(σ * a)) * (bf p.1 * (SFin.norm p.1) ^ σ)) *
          ENNReal.ofReal (Pp p.2.1) := by
    intro p
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (hbf0 _) (Real.rpow_nonneg (SFin.norm_pos h𝔪 _).le _)))]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [slice]
    rw [prod_ext_eq w₀ (bmaj α N)]
    set t := a - Real.log p.1.norm - ∑ w, p.2.1 w
    have h1 : bmaj α N t ≤ Real.exp (-(σ * t)) := bmaj_le_exp hσ1.le hσ2.le t
    have h2 : Real.exp (-(σ * t)) =
        Real.exp (-(σ * a)) * (SFin.norm p.1) ^ σ * ∏ w : Wo w₀, Real.exp (σ * p.2.1 w) := by
      rw [Real.rpow_def_of_pos (SFin.norm_pos h𝔪 _), ← Real.exp_sum, ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      simp only [t]
      rw [← Finset.mul_sum]
      ring
    have hP : Pp p.2.1 = (∏ w : Wo w₀, bmaj α N (p.2.1 w)) * ∏ w : Wo w₀, Real.exp (σ * p.2.1 w) := by
      simp only [Pp, φ, Finset.prod_mul_distrib]
    rw [hP]
    have hb0 : 0 ≤ ∏ w : Wo w₀, bmaj α N (p.2.1 w) := Finset.prod_nonneg fun _ _ => bmaj_nonneg _ _ _
    calc bmaj α N t * (∏ w : Wo w₀, bmaj α N (p.2.1 w)) * bf p.1
        ≤ Real.exp (-(σ * t)) * (∏ w : Wo w₀, bmaj α N (p.2.1 w)) * bf p.1 := by
          gcongr
          exact hbf0 _
      _ = _ := by rw [h2]; ring
  refine (lintegral_mono hpt).trans ?_
  -- product integral
  have hmeas1 : AEMeasurable (fun y : SFin 𝔪 k =>
      ENNReal.ofReal (Real.exp (-(σ * a)) * (bf y * (SFin.norm y) ^ σ))) Measure.count :=
    (measurable_of_countable _).aemeasurable
  have hmeasPp : Measurable fun x' : Wo w₀ → ℝ => ENNReal.ofReal (Pp x') := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact Finset.measurable_prod _ fun w _ =>
      ((continuous_bmaj α N).measurable.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).comp
        (measurable_pi_apply w)
  have hmeas2 : AEMeasurable (fun q : (Wo w₀ → ℝ) × (InfinitePlace F → AddCircle (2 * Real.pi)) =>
      ENNReal.ofReal (Pp q.1)) volume := (hmeasPp.comp measurable_fst).aemeasurable
  have hsplit := lintegral_prod_mul (μ := (Measure.count : Measure (SFin 𝔪 k)))
    (ν := (volume : Measure ((Wo w₀ → ℝ) × (InfinitePlace F → AddCircle (2 * Real.pi)))))
    hmeas1 hmeas2
  simp only [baseMeasure]
  rw [hsplit]
  -- count part
  have hc : ∫⁻ y, ENNReal.ofReal (Real.exp (-(σ * a)) * (bf y * (SFin.norm y) ^ σ)) ∂Measure.count
      = ENNReal.ofReal (Real.exp (-(σ * a)) * S) := by
    rw [lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg (fun y => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (hbf0 y) (Real.rpow_nonneg (SFin.norm_pos h𝔪 y).le _))) (hbf.mul_left _),
      tsum_mul_left]
  -- volume part
  have hv : ∫⁻ q : (Wo w₀ → ℝ) × (InfinitePlace F → AddCircle (2 * Real.pi)),
      ENNReal.ofReal (Pp q.1) = ENNReal.ofReal I * ENNReal.ofReal A := by
    have := lintegral_prod_mul (μ := (volume : Measure (Wo w₀ → ℝ)))
      (ν := (volume : Measure (InfinitePlace F → AddCircle (2 * Real.pi))))
      (f := fun x' => ENNReal.ofReal (Pp x')) (g := fun _ => 1) hmeasPp.aemeasurable
      aemeasurable_const
    simp only [mul_one] at this
    rw [Measure.volume_eq_prod, this, lintegral_const, one_mul,
      ← ofReal_integral_eq_lintegral_ofReal hPpi (Filter.Eventually.of_forall hPp0),
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hc, hv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

theorem lintegral_majorant_le (h𝔪 : 𝔪 ≠ ⊥) {α N σ : ℝ}
    (hσ1 : -α < σ) (hσ2 : σ < N) (bf : SFin 𝔪 k → ℝ) (hbf0 : ∀ y, 0 ≤ bf y)
    (hbf : Summable (fun y => bf y * (SFin.norm y) ^ σ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ,
      ∫⁻ y, ENNReal.ofReal ((∏ w, bmaj α N (y.1 w)) * bf y.2.2) ∂(shMeasure w₀ 𝔪 k a) ≤
        ENNReal.ofReal (C * Real.exp (-(σ * a))) := by
  obtain ⟨C, hC0, hC⟩ := lintegral_majorant_base_le w₀ h𝔪 hσ1 hσ2 bf hbf0 hbf
  refine ⟨C, hC0, fun a => ?_⟩
  rw [shMeasure]
  have := lintegral_map (μ := baseMeasure w₀ 𝔪 k)
    (ENNReal.measurable_ofReal.comp (measurable_majorant (𝔪 := 𝔪) (k := k) α N bf))
    (measurable_slice w₀ a)
  simp only [Function.comp_def] at this
  rw [this]
  exact hC a

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3V_LocStmt: the local statement `L3V_LocPkg` (Lemma 6.2 and the local symbols at one prime)

At an exterior prime `P` (for `𝔪` divisible by the small primes): the sextic symbol is
multiplicative with sixth power `1` on units; `R ∖ P R` is the valuation-`1` part of `R`;
`v_P(gen I) = v_P(I)`; `χ_P` on `P`-units of `F` is multiplicative, of order dividing `6`, and extends
`χ_P` on `R`; and Lemma 6.2: the masked digit sum splits off the zero digit, `α_{P,j}(0) = 0` for
`j ≠ 0`, the nonzero digits give `R(t) = R(1) χ_P(t)^{b(j,e)}` ((6.15), `b(j,0) = 8 + 5j ≡ 8 − j`,
`b(j,e) = 4 + 2e`), `R = 0` for `j = 1`, `e > 0` ((6.14)), `|R(1)| ≤ β_P(e)` ((6.20)), `|α(0)| ≤ 1`
and `|γ₂(P)| ≤ 1`. -/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
/-- The local statement (see the module doc). -/
def L3V_LocPkg (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
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
    let Rsum : (P : Ideal (𝓞 F)) → ℕ → ℤ → F → ℂ := fun P j e₀ t =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        mask P j v * (if v = 0 then 0 else Wweyl P e₀ t v)
    let βp : ℝ → ℕ → ℝ := fun q e =>
      if e = 0 then 1
      else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
      else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
      else 0
    ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hPe : IsExterior 𝔪 P),
      let val := (⟨P, hP, hPe.1⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 F)).valuation F
      (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
        sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
      (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1) ∧
      (∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ val (y : F) = 1) ∧
      (∀ I : Ideal (𝓞 F), IsExterior 𝔪 I →
        val (g.gen I : F) = WithZero.exp (-(((normalizedFactors I).count P : ℕ) : ℤ))) ∧
      (∀ t t' : F, val t = 1 → val t' = 1 → lsym P (t * t') = lsym P t * lsym P t') ∧
      (∀ t : F, val t = 1 → lsym P t ^ 6 = 1) ∧
      (∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
        lsym P (y : F) = sexticResidueSymbol ι 𝔪 P y) ∧
      (∀ k : ℕ, k ≠ 0 → ∀ (e₀ : ℤ) (t : F),
        Eloc P k e₀ t = mask P (k % 6) 0 * Wsph P e₀ t + Rsum P (k % 6) e₀ t) ∧
      (∀ j : ℕ, j ≠ 0 → mask P j 0 = 0) ∧
      (∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 → ∀ t : F, val t = 1 →
        Rsum P j e₀ t = Rsum P j e₀ 1 *
          lsym P t ^ (if (e₀ + 2).toNat = 0 then 8 + 5 * j else 4 + 2 * (e₀ + 2).toNat)) ∧
      (∀ e₀ : ℤ, 0 < e₀ + 2 → ∀ t : F, val t ≤ 1 → Rsum P 1 e₀ t = 0) ∧
      (∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 →
        ‖Rsum P j e₀ 1‖ ≤ βp (Ideal.absNorm P) (e₀ + 2).toNat) ∧
      (∀ j : ℕ, ‖mask P j 0‖ ≤ 1) ∧
      ‖gaussPhase g 2 P‖ ≤ 1

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_VP: the `P`-adic valuation `vP` and the unit-part symbol `uSym` (definitions and the
valuation algebra) -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

open Classical in
/-- The `P`-adic valuation `v_P(x) ∈ ℤ` (`0` if `P` is not a nonzero prime). -/
noncomputable def vP (P : Ideal (𝓞 F)) (x : F) : ℤ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then
    -log ((⟨P, h.1, h.2⟩ : HeightOneSpectrum (𝓞 F)).valuation F x)
  else 0

/-- The symbol `χ_P(x p^{−v_P(x)})` of the unit part of `x` at `P` (`p = gen P`). -/
noncomputable def uSym (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (x : F) : ℂ :=
  localSymbol ι 𝔪 P (x * (g.gen P : F) ^ (-(vP P x)))

lemma vP_v (x : F) : vP v.asIdeal x = -log (v.valuation F x) := by
  unfold vP
  rw [dif_pos ⟨v.isPrime, v.ne_bot⟩]

lemma val_eq_exp_vP {x : F} (hx : x ≠ 0) : v.valuation F x = exp (-(vP v.asIdeal x)) := by
  rw [vP_v, neg_neg, exp_log]
  exact (Valuation.ne_zero_iff _).2 hx

lemma vP_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    vP v.asIdeal (x * y) = vP v.asIdeal x + vP v.asIdeal y := by
  rw [vP_v, vP_v, vP_v, map_mul, log_mul ((Valuation.ne_zero_iff _).2 hx)
    ((Valuation.ne_zero_iff _).2 hy)]
  ring

end L3V

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField Filter Topology

/-! L2D: ideal counting in a number field. -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_finite_le (t : ℝ) : {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ t}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le ⌊t⌋₊).subset fun I hI => Nat.le_floor hI

/-- The finite set of ideals of norm `≤ t` (including `⊥`). -/
noncomputable def L2D_le (F : Type*) [Field F] [NumberField F] (t : ℝ) : Finset (Ideal (𝓞 F)) :=
  (L2D_finite_le (F := F) t).toFinset

@[simp] lemma L2D_mem_le {t : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ L2D_le F t ↔ (Ideal.absNorm I : ℝ) ≤ t := by
  simp [L2D_le]

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: candidate cuts beneath C1b (Proposition 4.1 (4.5)).

* `L2D_Cut64`: Lemma 6.4 (p. 38), the quadratic large sieve for `χ_𝔡(c)^3`
  (Goldmakher–Louvel, Thm 1.1).
* `L2D_Cut63`: Lemma 6.3 (p. 34) with (6.22) (p. 33), the reflected expansion of `B_m(Z)`, with
  the coefficients, row/column functions and profiles existentially quantified and only their
  stated bounds retained. -/

/-- `β_p(e)` of (6.20) (p. 33), at a prime of norm `q`. -/
noncomputable def L2D_betaP (q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
  else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
  else 0

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: factorization combinatorics for the proof of (4.5). -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_prime_of_mem {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) : Prime P :=
  prime_of_normalized_factor P hP

lemma L2D_eq_of_nf_eq {a b : Ideal (𝓞 F)} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (h : normalizedFactors a = normalizedFactors b) : a = b := by
  have h1 := prod_normalizedFactors ha
  have h2 := prod_normalizedFactors hb
  rw [associated_iff_eq] at h1 h2
  rw [← h1, ← h2, h]

lemma L2D_mem_nf_of_dvd {f Q : Ideal (𝓞 F)} (hf : f ≠ ⊥) (hQ : Prime Q) (hQf : Q ∣ f) :
    Q ∈ normalizedFactors f := by
  obtain ⟨Q', hQ', hassoc⟩ := exists_mem_normalizedFactors_of_dvd hf hQ.irreducible hQf
  rw [associated_iff_eq] at hassoc
  rwa [hassoc]

/-! ### `β_p` and the sum of `β_𝔣` -/


end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Sum: the Poisson sum and the Gauss sum with free generators; CRT and twists

* `PS 𝔰 𝔄 s A Af c h = ∑_{d mod 𝔰} ∑_{v mod 𝔄} [h ≡ Af d (𝔰)] χ_𝔰(d) χ_𝔄(v) e((h − Af d) v c/(sA))`;
  `poissonFactor g 𝔰 𝔄 h = PS 𝔰 𝔄 (gen 𝔰) (gen 𝔄) (gen 𝔄) 1 h`.
* `GS 𝔠 c c' j = ∑_{x mod 𝔠} χ_𝔠(x)^j e(x c'/c)`; `gaussPhase g j 𝔠 = q^{-1/2} GS 𝔠 (gen 𝔠) 1 j`.
* `PS_crt`, `GS_crt`: Chinese remainders with idempotents `β s₂A₂`, `α s₁A₁`.
* `PS_twist`, `GS_twist`: unit substitutions.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

section defs

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))

/-- The Gauss sum summand with free generator `c` and twist `c'`. -/
noncomputable def V (𝔠 : Ideal (𝓞 F)) (c c' : SInt 𝔪) (j : ℕ) (x : SInt 𝔪) : ℂ :=
  residueSymbol ι 𝔪 𝔠 x ^ j * sAddChar 𝔪 ((x : F) * (c' : F) / (c : F))

/-- The Gauss sum with free generator. -/
noncomputable def GS (𝔠 : Ideal (𝓞 F)) (c c' : SInt 𝔪) (j : ℕ) : ℂ :=
  ∑ᶠ x : SInt 𝔪 ⧸ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪)), V ι 𝔪 𝔠 c c' j (quotLift x)

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

lemma quotLift_mul_sub (I : Ideal (SInt 𝔪)) (u : SInt 𝔪) (x : SInt 𝔪 ⧸ I) :
    quotLift (Ideal.Quotient.mk I u * x) - u * quotLift x ∈ I := by
  rw [← Ideal.Quotient.eq, map_mul]
  rw [show Ideal.Quotient.mk I (quotLift (Ideal.Quotient.mk I u * x)) =
    Ideal.Quotient.mk I u * x from Function.surjInv_eq Ideal.Quotient.mk_surjective _]
  rw [show Ideal.Quotient.mk I (quotLift x) = x from Function.surjInv_eq Ideal.Quotient.mk_surjective _]

lemma periodic_eq {I : Ideal (SInt 𝔪)} {f : SInt 𝔪 → ℂ}
    (hf : ∀ x w, w ∈ I → f (x + w) = f x) {x y : SInt 𝔪} (h : x - y ∈ I) : f x = f y := by
  have := hf y (x - y) h
  rwa [add_sub_cancel] at this

lemma exists_eq_mul_of_mem {s : SInt 𝔪} {x : SInt 𝔪} (hx : x ∈ Ideal.span {s}) :
    ∃ y : SInt 𝔪, x = y * s := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
  exact ⟨a, ha.symm⟩

/-- Chinese remainders for a periodic function. -/
lemma finsum_crt {I J K : Ideal (SInt 𝔪)} [Finite (SInt 𝔪 ⧸ I)] [Finite (SInt 𝔪 ⧸ J)]
    {e₁ e₂ : SInt 𝔪} (he₁ : e₁ ∈ J) (he₂ : e₂ ∈ I) (h1 : e₁ + e₂ = 1) (hK : K = I * J)
    (f : SInt 𝔪 → ℂ) (hf : ∀ x w, w ∈ K → f (x + w) = f x) :
    ∑ᶠ x : SInt 𝔪 ⧸ K, f (quotLift x) =
      ∑ᶠ x₁ : SInt 𝔪 ⧸ I, ∑ᶠ x₂ : SInt 𝔪 ⧸ J, f (quotLift x₁ * e₁ + quotLift x₂ * e₂) := by
  subst hK
  have cop : IsCoprime I J :=
    Ideal.isCoprime_iff_exists.mpr ⟨e₂, he₂, e₁, he₁, by rw [add_comm]; exact h1⟩
  let φ := Ideal.quotientMulEquivQuotientProd I J cop
  rw [← finsum_comp_equiv φ.symm.toEquiv]
  rw [finsum_curry _ (Set.toFinite _)]
  refine finsum_congr fun x₁ => finsum_congr fun x₂ => ?_
  apply periodic_eq hf
  rw [← Ideal.Quotient.eq]
  rw [show Ideal.Quotient.mk (I * J) (quotLift (φ.symm.toEquiv (x₁, x₂))) = φ.symm (x₁, x₂) from
    Function.surjInv_eq Ideal.Quotient.mk_surjective _]
  apply φ.injective
  rw [RingEquiv.apply_symm_apply]
  have hl : ∀ (L : Ideal (SInt 𝔪)) (y : SInt 𝔪 ⧸ L), Ideal.Quotient.mk L (quotLift y) = y :=
    fun L y => Function.surjInv_eq Ideal.Quotient.mk_surjective _
  ext
  · rw [Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
    rw [← hl I x₁, Ideal.Quotient.eq, hl I x₁]
    have : quotLift x₁ - (quotLift x₁ * e₁ + quotLift x₂ * e₂) = (quotLift x₁ - quotLift x₂) * e₂ := by
      linear_combination (-quotLift x₁) * h1
    rw [this]; exact Ideal.mul_mem_left _ _ he₂
  · rw [Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
    rw [← hl J x₂, Ideal.Quotient.eq, hl J x₂]
    have : quotLift x₂ - (quotLift x₁ * e₁ + quotLift x₂ * e₂) = (quotLift x₂ - quotLift x₁) * e₁ := by
      linear_combination (-quotLift x₂) * h1
    rw [this]; exact Ideal.mul_mem_left _ _ he₁

/-- Substitution by a unit of `R/I`. -/
lemma finsum_unit_subst {I : Ideal (SInt 𝔪)} {u u' : SInt 𝔪} (hu : u * u' - 1 ∈ I)
    (f : SInt 𝔪 → ℂ) (hf : ∀ x w, w ∈ I → f (x + w) = f x) :
    ∑ᶠ x : SInt 𝔪 ⧸ I, f (quotLift x) = ∑ᶠ x : SInt 𝔪 ⧸ I, f (u * quotLift x) := by
  have h1 : Ideal.Quotient.mk I u * Ideal.Quotient.mk I u' = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hu
  let w : (SInt 𝔪 ⧸ I)ˣ := Units.mkOfMulEqOne _ _ h1
  rw [← finsum_comp_equiv (Units.mulLeft w)]
  refine finsum_congr fun x => ?_
  exact periodic_eq hf (quotLift_mul_sub I u x)

/-! ### Coercions -/

lemma coe_sub' (x y : SInt 𝔪) : ((x - y : SInt 𝔪) : F) = (x : F) - (y : F) := rfl
lemma coe_mul' (x y : SInt 𝔪) : ((x * y : SInt 𝔪) : F) = (x : F) * (y : F) := rfl
lemma coe_add' (x y : SInt 𝔪) : ((x + y : SInt 𝔪) : F) = (x : F) + (y : F) := rfl
lemma coe_one' : ((1 : SInt 𝔪) : F) = 1 := rfl

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

end U

/-! ### Field identities -/

lemma alg_gs_crt (x₁ x₂ c' α β c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hαβ : α * c₁ + β * c₂ = 1) :
    (x₁ * (β * c₂) + x₂ * (α * c₁)) * c' / (c₁ * c₂) =
      (x₁ * (c' * β) / c₁ + c' * β * α * (x₂ - x₁)) +
        (x₂ * (c' * α) / c₂ + c' * α * β * (x₁ - x₂)) := by
  have hα : α = (1 - β * c₂) / c₁ := by
    field_simp; linear_combination hαβ
  subst hα
  field_simp
  ring

lemma alg_gs_twist (x C c'' c w : F) (hc : c ≠ 0) (h : C * c'' - 1 = w * c) :
    (C * x) * c'' / c = x * 1 / c + x * w := by
  have h' : C * c'' = 1 + w * c := by linear_combination h
  have e : (C * x) * c'' / c = x * (C * c'') / c := by ring
  rw [e, h']
  field_simp

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

lemma castF {x y : SInt 𝔪} (h : x = y) : (x : F) = (y : F) := congrArg _ h

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

lemma V_add (hc : Ideal.span {c} = 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) (hc0 : (c : F) ≠ 0)
    (x w : SInt 𝔪) (hw : w ∈ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    V ι 𝔪 𝔠 c c' j (x + w) = V ι 𝔪 𝔠 c c' j x := by
  have hw' := hw
  rw [← hc] at hw'
  obtain ⟨w', rfl⟩ := exists_eq_mul_of_mem hw'
  unfold V
  rw [C3B.residueSymbol_congr ι 𝔠 (x + w' * c) x (by rw [add_sub_cancel_left]; exact hw)]
  have harg : ((x + w' * c : SInt 𝔪) : F) * (c' : F) / (c : F) =
      (x : F) * (c' : F) / (c : F) + ((w' * c' : SInt 𝔪) : F) := by
    simp only [coe_mul', coe_add']
    field_simp
  rw [harg, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]

lemma GS_crt (hadd : HypAdd 𝔪) {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} {c₁ c₂ α β : SInt 𝔪}
    (h𝔠₁ : IsExterior 𝔪 𝔠₁) (h𝔠₂ : IsExterior 𝔪 𝔠₂)
    (hc₁ : Ideal.span {c₁} = 𝔠₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc₂ : Ideal.span {c₂} = 𝔠₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc₁0 : (c₁ : F) ≠ 0) (hc₂0 : (c₂ : F) ≠ 0) (hαβ : α * c₁ + β * c₂ = 1) :
    GS ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j = GS ι 𝔪 𝔠₁ c₁ (c' * β) j * GS ι 𝔪 𝔠₂ c₂ (c' * α) j := by
  have := finite_quot h𝔠₁; have := finite_quot h𝔠₂
  have hc : Ideal.span {c₁ * c₂} = (𝔠₁ * 𝔠₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, ← hc₁, ← hc₂, Ideal.span_singleton_mul_span_singleton]
  have hc0 : ((c₁ * c₂ : SInt 𝔪) : F) ≠ 0 := by rw [coe_mul']; exact mul_ne_zero hc₁0 hc₂0
  have he₁ : β * c₂ ∈ 𝔠₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hc₂]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have he₂ : α * c₁ ∈ 𝔠₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hc₁]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h1 : β * c₂ + α * c₁ = 1 := by rw [add_comm]; exact hαβ
  unfold GS
  refine (finsum_crt he₁ he₂ h1 (Ideal.map_mul _ _ _) (V ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j)
    (fun x w hw => V_add hc hc0 x w hw)).trans ?_
  have hpt : ∀ x₁ x₂ : SInt 𝔪, V ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j (x₁ * (β * c₂) + x₂ * (α * c₁)) =
      V ι 𝔪 𝔠₁ c₁ (c' * β) j x₁ * V ι 𝔪 𝔠₂ c₂ (c' * α) j x₂ := by
    intro x₁ x₂
    have hx1 : x₁ * (β * c₂) + x₂ * (α * c₁) - x₁ = (x₂ - x₁) * (α * c₁) := by
      linear_combination x₁ * hαβ
    have hx2 : x₁ * (β * c₂) + x₂ * (α * c₁) - x₂ = (x₁ - x₂) * (β * c₂) := by
      linear_combination x₂ * hαβ
    unfold V
    rw [residueSymbol_mul_ideal _ _ h𝔠₁.1 h𝔠₂.1,
      C3B.residueSymbol_congr ι 𝔠₁ _ x₁ (by rw [hx1]; exact Ideal.mul_mem_left _ _ he₂),
      C3B.residueSymbol_congr ι 𝔠₂ _ x₂ (by rw [hx2]; exact Ideal.mul_mem_left _ _ he₁)]
    have hαβF := castF (F := F) hαβ
    simp only [coe_add', coe_mul', coe_one'] at hαβF
    have harg : ((x₁ * (β * c₂) + x₂ * (α * c₁) : SInt 𝔪) : F) * (c' : F) /
          ((c₁ * c₂ : SInt 𝔪) : F) =
        ((x₁ : F) * ((c' * β : SInt 𝔪) : F) / (c₁ : F) + ((c' * β * α * (x₂ - x₁) : SInt 𝔪) : F)) +
          ((x₂ : F) * ((c' * α : SInt 𝔪) : F) / (c₂ : F) +
            ((c' * α * β * (x₁ - x₂) : SInt 𝔪) : F)) := by
      simp only [coe_sub', coe_mul', coe_add']
      exact alg_gs_crt _ _ _ _ _ _ _ hc₁0 hc₂0 hαβF
    rw [harg, hadd, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _),
      C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
    · ring
    · exact extWit_div_add h𝔠₁.2 hc₁ hc₁0 (x₁ * (c' * β)) _
    · exact extWit_div_add h𝔠₂.2 hc₂ hc₂0 (x₂ * (c' * α)) _
  simp only [hpt]
  rw [finsum_mul]
  refine finsum_congr fun x₁ => ?_
  rw [mul_finsum]

lemma GS_twist (hχ : HypChi ι 𝔪) (h𝔠 : IsExterior 𝔪 𝔠)
    (hc : Ideal.span {c} = 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) (hc0 : (c : F) ≠ 0)
    {c'' C : SInt 𝔪} (hC : C * c'' - 1 ∈ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    GS ι 𝔪 𝔠 c c'' j = residueSymbol ι 𝔪 𝔠 C ^ j * GS ι 𝔪 𝔠 c 1 j := by
  unfold GS
  refine (finsum_unit_subst hC (V ι 𝔪 𝔠 c c'' j) (fun x w hw => V_add hc hc0 x w hw)).trans ?_
  rw [mul_finsum]
  refine finsum_congr fun x => ?_
  have hC' := hC
  rw [← hc] at hC'
  obtain ⟨w, hw⟩ := exists_eq_mul_of_mem hC'
  have hwF := castF (F := F) hw
  simp only [coe_sub', coe_mul', coe_one'] at hwF
  unfold V
  rw [residueSymbol_mul hχ h𝔠, mul_pow]
  have harg : ((C * quotLift x : SInt 𝔪) : F) * (c'' : F) / (c : F) =
      ((quotLift x : SInt 𝔪) : F) * ((1 : SInt 𝔪) : F) / (c : F) +
        ((quotLift x * w : SInt 𝔪) : F) := by
    simp only [coe_mul', coe_one']
    exact alg_gs_twist _ _ _ _ _ hc0 hwF
  rw [harg, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
  ring

end gs

lemma gaussPhase_eq_GS (g : AllowedGen ι 𝔪) (j : ℕ) (𝔠 : Ideal (𝓞 F)) :
    gaussPhase g j 𝔠 =
      ((Real.sqrt (Ideal.absNorm 𝔠) : ℝ) : ℂ)⁻¹ * GS ι 𝔪 𝔠 (g.gen 𝔠) 1 j := by
  unfold gaussPhase GS V
  congr 1
  refine finsum_congr fun x => ?_
  rw [coe_one', mul_one]

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Mul: twisted multiplicativity of `γ_j`, of `F(𝔰, 𝔄, gen(𝔯)⁶)`, of `ϑ`, and reciprocity

* `gaussPhase_mul` (3.10): `γ_j(𝔠₁𝔠₂) = χ_{𝔠₁}(c₂)^j χ_{𝔠₂}(c₁)^j γ_j(𝔠₁) γ_j(𝔠₂)`.
* `poissonFactor_mul`: for `𝔰₁𝔄₁` coprime to `𝔰₂𝔄₂`, `𝔯ᵢ` coprime to the other side,
  `χ_{𝔰₁}(A₂) χ_{𝔰₂}(A₁) F(𝔰₁𝔰₂, 𝔄₁𝔄₂, gen(𝔯₁𝔯₂)⁶)
     = χ_{𝔄₁}(s₂A₂) χ_{𝔄₂}(s₁A₁) F(𝔰₁, 𝔄₁, gen(𝔯₁)⁶) F(𝔰₂, 𝔄₂, gen(𝔯₂)⁶)`.
* `residueSymbol_gen_prime`: `χ_𝔟(gen P) = χ_P(gen 𝔟)` (from (3.3)).
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Coprimality in `R` -/

lemma exists_ab {x y : SInt 𝔪} (h : IsCoprime (Ideal.span {x}) (Ideal.span {y})) :
    ∃ α β : SInt 𝔪, α * x + β * y = 1 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  exact ⟨α, β, hij⟩

lemma unit_pow_mul_inv (ε : (SInt 𝔪)ˣ) :
    (ε : SInt 𝔪) ^ 6 * ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 = 1 := by
  rw [← mul_pow, Units.mul_inv, one_pow]

/-! ### Change of generators -/

lemma unit_coe_ne_zero (u : (SInt 𝔪)ˣ) : ((u : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have : ((u : SInt 𝔪) : F) * (((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← coe_mul', Units.mul_inv]; rfl
  rw [h0, zero_mul] at this; exact zero_ne_one this

lemma GS_gen_change {𝔠 : Ideal (𝓞 F)} {c₀ c c' : SInt 𝔪} {j : ℕ} (hc₀ : (c₀ : F) ≠ 0)
    (hc' : (c' : F) ≠ 0)
    (hc : (c : F) = (c' : F) * (c₀ : F)) : GS ι 𝔪 𝔠 c₀ 1 j = GS ι 𝔪 𝔠 c c' j := by
  unfold GS V
  refine finsum_congr fun x => ?_
  congr 2
  rw [hc, coe_one']
  field_simp

/-! ### Generators and residue symbols -/

lemma residueSymbol_gen_mul (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 I J : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    residueSymbol ι 𝔪 𝔞 (g.gen (I * J)) =
      residueSymbol ι 𝔪 𝔞 (g.gen I) * residueSymbol ι 𝔪 𝔞 (g.gen J) := by
  obtain ⟨ε, hε⟩ := gen_mul' g hI hJ
  rw [hε, mul_assoc, residueSymbol_unit_pow_six hχ h𝔞, residueSymbol_mul hχ h𝔞]

lemma residueSymbol_gen_top (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) : residueSymbol ι 𝔪 𝔞 (g.gen ⊤) = 1 := by
  obtain ⟨ε, hε⟩ := gen_top g
  rw [hε, ← mul_one ((ε : SInt 𝔪) ^ 6), residueSymbol_unit_pow_six hχ h𝔞,
    residueSymbol_one hχ h𝔞]

/-- Extended reciprocity: `χ_𝔟(gen P) = χ_P(gen 𝔟)` for an exterior `𝔟` prime to `P`. -/
lemma residueSymbol_gen_prime (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) (𝔟 : Ideal (𝓞 F)) :
    IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 𝔟 (g.gen P) = residueSymbol ι 𝔪 P (g.gen 𝔟) := by
  induction 𝔟 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro hue _
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    rw [C3B.residueSymbol_top, residueSymbol_gen_top hχ g hPe]
  | h₃ 𝔞 Q _ hQ ih =>
    intro hQa hle
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 𝔞 := isExterior_of_mul_right hQa
    have hQP : ¬ Q ≤ P := fun h => hle (le_trans Ideal.mul_le_left h)
    have haP : ¬ 𝔞 ≤ P := fun h => hle (le_trans Ideal.mul_le_right h)
    have hne : P ≠ Q := fun h => hQP (h ▸ le_rfl)
    rw [residueSymbol_mul_ideal _ _ hQe.1 hae.1, ih hae haP,
      residueSymbol_gen_mul hχ g hPe hQe hae, residueSymbol_prime hQp hQe.1,
      residueSymbol_prime hP hPe.1, residueSymbol_prime hP hPe.1,
      ← g.reciprocity P Q hP hQp hPe hQe hne]

/-! ### `ϑ` and norms -/

lemma sqrt_norm_mul_inv (I J : Ideal (𝓞 F)) :
    ((Real.sqrt (Ideal.absNorm (I * J)) : ℝ) : ℂ)⁻¹ =
      ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Ideal.absNorm J) : ℝ) : ℂ)⁻¹ := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, mul_inv]

/-! ### (3.10) -/

theorem gaussPhase_mul (hadd : HypAdd 𝔪) (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪)
    {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} (h₁ : IsExterior 𝔪 𝔠₁) (h₂ : IsExterior 𝔪 𝔠₂)
    (hcop : IsCoprime 𝔠₁ 𝔠₂) (j : ℕ) :
    gaussPhase g j (𝔠₁ * 𝔠₂) =
      residueSymbol ι 𝔪 𝔠₁ (g.gen 𝔠₂) ^ j * residueSymbol ι 𝔪 𝔠₂ (g.gen 𝔠₁) ^ j *
        (gaussPhase g j 𝔠₁ * gaussPhase g j 𝔠₂) := by
  obtain ⟨ε, hε⟩ := gen_mul' g h₁ h₂
  set c₁ := g.gen 𝔠₁
  set c₂ := g.gen 𝔠₂
  have hc₁ := g.span_gen 𝔠₁ h₁
  have hc₂ := g.span_gen 𝔠₂ h₂
  have hc₁0 := C3B.gen_ne_zero g 𝔠₁ h₁
  have hc₂0 := C3B.gen_ne_zero g 𝔠₂ h₂
  have h12 := C3B.gen_ne_zero g (𝔠₁ * 𝔠₂) (C3B.isExterior_mul h₁ h₂)
  obtain ⟨α, β, hαβ⟩ := exists_ab (x := c₁) (y := c₂) (by rw [hc₁, hc₂]; exact isCoprime_map hcop)
  set c' : SInt 𝔪 := ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6
  have hεc : (ε : SInt 𝔪) ^ 6 * c' = 1 := unit_pow_mul_inv ε
  rw [gaussPhase_eq_GS, gaussPhase_eq_GS, gaussPhase_eq_GS, sqrt_norm_mul_inv]
  rw [GS_gen_change (c := c₁ * c₂) (c' := c') h12
    (by rw [Subalgebra.coe_pow]; exact pow_ne_zero _ (unit_coe_ne_zero _)) (by
    rw [hε]; have := castF (F := F) hεc; simp only [coe_mul', coe_one'] at this ⊢
    simp only [Subalgebra.coe_pow] at this ⊢
    linear_combination (-((c₁ : F) * (c₂ : F))) * this)]
  rw [GS_crt hadd h₁ h₂ hc₁ hc₂ hc₁0 hc₂0 hαβ]
  rw [GS_twist (C := (ε : SInt 𝔪) ^ 6 * c₂) hχ h₁ hc₁ hc₁0 (by
      rw [show (ε : SInt 𝔪) ^ 6 * c₂ * (c' * β) - 1 = -(α * c₁) by
        linear_combination c₂ * β * hεc + hαβ, ← hc₁]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))),
    GS_twist (C := (ε : SInt 𝔪) ^ 6 * c₁) hχ h₂ hc₂ hc₂0 (by
      rw [show (ε : SInt 𝔪) ^ 6 * c₁ * (c' * α) - 1 = -(β * c₂) by
        linear_combination c₁ * α * hεc + hαβ, ← hc₂]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))]
  rw [residueSymbol_unit_pow_six hχ h₁, residueSymbol_unit_pow_six hχ h₂]
  ring

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_Ideal: prime-exponent bookkeeping for ideals of `𝓞 F`

`cnt P I = v_P(I)` (count in `normalizedFactors`), `prim I` its prime support; products, powers,
prime-power products over a finset, ideal equality from exponents, squarefreeness and coprimality
in exponent form, norms; `residueSymbol` over a squarefree ideal, and reciprocity
`χ_𝔠(gen 𝔡) = χ_𝔡(gen 𝔠)` for coprime exterior `𝔠, 𝔡`. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F]

/-- `v_P(I)`. -/
noncomputable abbrev cnt (P I : Ideal (𝓞 F)) : ℕ := (normalizedFactors I).count P

/-- The prime support of `I`. -/
noncomputable abbrev prim (I : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := (normalizedFactors I).toFinset

lemma cnt_mul {P I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    cnt P (I * J) = cnt P I + cnt P J := by
  unfold cnt; rw [normalizedFactors_mul hI hJ, Multiset.count_add]

lemma cnt_pow (P I : Ideal (𝓞 F)) (n : ℕ) : cnt P (I ^ n) = n * cnt P I := by
  unfold cnt; rw [normalizedFactors_pow, Multiset.count_nsmul]

lemma nf_prime' {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) : normalizedFactors Q = {Q} := by
  rw [normalizedFactors_irreducible ((Ideal.prime_of_isPrime hQ0 hQ).irreducible), normalize_eq]

lemma cnt_prime {P Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    cnt P Q = if P = Q then 1 else 0 := by
  unfold cnt; rw [nf_prime' hQ hQ0, Multiset.count_singleton]

lemma cnt_top (P : Ideal (𝓞 F)) : cnt P ⊤ = 0 := by
  unfold cnt; rw [C3B.normalizedFactors_top]; simp

lemma prime_of_mem_prim {P I : Ideal (𝓞 F)} (hP : P ∈ prim I) : P.IsPrime ∧ P ≠ ⊥ := by
  have hp := L2D_prime_of_mem (Multiset.mem_toFinset.1 hP)
  exact ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩

lemma prod_pow_ne_bot (s : Finset (Ideal (𝓞 F))) (hs : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥)
    (n : Ideal (𝓞 F) → ℕ) : ∏ Q ∈ s, Q ^ n Q ≠ ⊥ := by
  exact Finset.prod_ne_zero_iff.2 fun Q hQ => pow_ne_zero _ (hs Q hQ).2

lemma cnt_prod_pow (P : Ideal (𝓞 F)) (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥) (n : Ideal (𝓞 F) → ℕ) :
    cnt P (∏ Q ∈ s, Q ^ n Q) = if P ∈ s then n P else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cnt_top]
  | insert Q s hQs ih =>
    have hs' : ∀ R ∈ s, R.IsPrime ∧ R ≠ ⊥ := fun R hR => hs R (Finset.mem_insert_of_mem hR)
    have hQ := hs Q (Finset.mem_insert_self Q s)
    rw [Finset.prod_insert hQs, cnt_mul (pow_ne_zero _ hQ.2) (prod_pow_ne_bot s hs' n), cnt_pow,
      cnt_prime hQ.1 hQ.2, ih hs']
    by_cases hPQ : P = Q
    · subst hPQ; simp [hQs]
    · simp [hPQ, Finset.mem_insert]

lemma not_prime_count_zero {P I : Ideal (𝓞 F)} (hP : ¬ (P.IsPrime ∧ P ≠ ⊥)) : cnt P I = 0 := by
  unfold cnt
  rw [Multiset.count_eq_zero]
  intro hm
  exact hP (prime_of_mem_prim (Multiset.mem_toFinset.2 hm))

lemma eq_of_cnt {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ P : Ideal (𝓞 F), P.IsPrime → P ≠ ⊥ → cnt P I = cnt P J) : I = J := by
  apply L2D_eq_of_nf_eq hI hJ
  ext P
  by_cases hP : P.IsPrime ∧ P ≠ ⊥
  · exact h P hP.1 hP.2
  · change cnt P I = cnt P J
    rw [not_prime_count_zero hP, not_prime_count_zero hP]

lemma mem_prim_iff {P I : Ideal (𝓞 F)} : P ∈ prim I ↔ 0 < cnt P I := by
  unfold prim cnt; rw [Multiset.mem_toFinset, Multiset.count_pos]

lemma dvd_iff_cnt_pos {P I : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hI : I ≠ ⊥) :
    P ∣ I ↔ 0 < cnt P I := by
  rw [← mem_prim_iff, Multiset.mem_toFinset]
  constructor
  · exact L2D_mem_nf_of_dvd hI (Ideal.prime_of_isPrime hP0 hP)
  · exact dvd_of_mem_normalizedFactors

lemma squarefree_iff_cnt {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Squarefree I ↔ ∀ P, cnt P I ≤ 1 := by
  rw [squarefree_iff_nodup_normalizedFactors hI, Multiset.nodup_iff_count_le_one]

lemma sup_eq_top_iff_cnt {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ⊔ J = ⊤ ↔ ∀ P, cnt P I = 0 ∨ cnt P J = 0 := by
  constructor
  · intro h P
    by_contra hc
    push Not at hc
    have hP : P.IsPrime ∧ P ≠ ⊥ := by
      by_contra hn; exact hc.1 (not_prime_count_zero hn)
    have h1 := (dvd_iff_cnt_pos hP.1 hP.2 hI).2 (Nat.pos_of_ne_zero hc.1)
    have h2 := (dvd_iff_cnt_pos hP.1 hP.2 hJ).2 (Nat.pos_of_ne_zero hc.2)
    rw [Ideal.dvd_iff_le] at h1 h2
    exact hP.1.ne_top (eq_top_iff.2 (h ▸ sup_le h1 h2))
  · intro h
    by_contra hne
    obtain ⟨M, hM, hIJ⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := by
      intro h0; rw [h0] at hIJ; exact hI (eq_bot_iff.2 (le_trans le_sup_left hIJ))
    have h1 := (dvd_iff_cnt_pos hM.isPrime hM0 hI).1 (Ideal.dvd_iff_le.2 (le_trans le_sup_left hIJ))
    have h2 := (dvd_iff_cnt_pos hM.isPrime hM0 hJ).1 (Ideal.dvd_iff_le.2 (le_trans le_sup_right hIJ))
    rcases h M with h3 | h3 <;> omega

lemma exterior_of_prim {𝔪 I P : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hP : P ∈ prim I) :
    IsExterior 𝔪 P :=
  (C3M.exterior_of_mem_factors hI (Multiset.mem_toFinset.1 hP)).2

lemma exterior_prod_pow {𝔪 : Ideal (𝓞 F)} (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ Q ∈ s, IsExterior 𝔪 Q) (n : Ideal (𝓞 F) → ℕ) : IsExterior 𝔪 (∏ Q ∈ s, Q ^ n Q) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top]; exact ⟨top_ne_bot, top_sup_eq _⟩
  | insert Q s hQs ih =>
    rw [Finset.prod_insert hQs]
    exact C3I.isExterior_mul (C3I.isExterior_pow (hs Q (Finset.mem_insert_self Q s)) _)
      (ih fun R hR => hs R (Finset.mem_insert_of_mem hR))

lemma prod_prim (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : ∏ P ∈ prim I, P ^ cnt P I = I := by
  have h := prod_normalizedFactors hI
  rw [associated_iff_eq] at h
  conv_rhs => rw [← h]
  rw [Finset.prod_multiset_count]

lemma absNorm_eq_prod (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (Ideal.absNorm I : ℝ) = ∏ P ∈ prim I, (Ideal.absNorm P : ℝ) ^ cnt P I := by
  conv_lhs => rw [← prod_prim I hI]
  rw [map_prod]; push_cast
  simp [map_pow]

lemma residueSymbol_sqfree (ι : F →+* ℂ) (𝔪 𝔡 : Ideal (𝓞 F)) (h𝔡 : 𝔡 ≠ ⊥) (hs : Squarefree 𝔡)
    (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔡 x = ∏ P ∈ prim 𝔡, sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol prim
  have hnd := (squarefree_iff_nodup_normalizedFactors h𝔡).1 hs
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnd.dedup]

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- Reciprocity for coprime exterior ideals: `χ_𝔠(gen 𝔡) = χ_𝔡(gen 𝔠)`. -/
lemma residueSymbol_recip (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔡 : Ideal (𝓞 F)}
    (h𝔡 : IsExterior 𝔪 𝔡) (𝔠 : Ideal (𝓞 F)) :
    IsExterior 𝔪 𝔠 → 𝔠 ⊔ 𝔡 = ⊤ →
      residueSymbol ι 𝔪 𝔠 (g.gen 𝔡) = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) := by
  induction 𝔠 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro _ _
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    rw [C3B.residueSymbol_top, C3M.residueSymbol_gen_top hχ g h𝔡]
  | h₃ 𝔞 Q _ hQ ih =>
    intro hQa hcop
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := C3M.isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 𝔞 := C3M.isExterior_of_mul_right hQa
    have hQd : ¬ 𝔡 ≤ Q := by
      intro hle
      apply hQp.ne_top
      rw [eq_top_iff, ← hcop]
      exact sup_le Ideal.mul_le_left hle
    have hcop' : 𝔞 ⊔ 𝔡 = ⊤ := by
      rw [eq_top_iff, ← hcop]; exact sup_le_sup_right Ideal.mul_le_right _
    rw [C3M.residueSymbol_mul_ideal _ _ hQe.1 hae.1, ih hae hcop',
      C3M.residueSymbol_gen_mul hχ g h𝔡 hQe hae,
      C3M.residueSymbol_gen_prime hχ g hQp hQe 𝔡 h𝔡 hQd]

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3V_ValB: the local package `Env` (from `L3V_LocPkg`) and the unit-part symbol calculus

`Env ι 𝔪` records, at every exterior prime, the facts of the local statement `L3V_LocPkg`; from it:
valuations of generators and units, the unit part `x p^{−v_P(x)}`, and `uSym` multiplicative, of
order dividing `6`, equal to `χ_P` on `R ∖ P R`. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The local facts at one exterior prime. -/
structure LocAt (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) :
    Prop where
  sext_mul : ∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
    sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y
  sext_six : ∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
    sexticResidueSymbol ι 𝔪 P x ^ 6 = 1
  mem_iff : ∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (y : F) = 1
  val_gen : ∀ I : Ideal (𝓞 F), IsExterior 𝔪 I →
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (g.gen I : F) =
      exp (-(((normalizedFactors I).count P : ℕ) : ℤ))
  lsym_mul : ∀ t t' : F, (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t = 1 →
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t' = 1 →
    localSymbol ι 𝔪 P (t * t') = localSymbol ι 𝔪 P t * localSymbol ι 𝔪 P t'
  lsym_six : ∀ t : F, (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t = 1 →
    localSymbol ι 𝔪 P t ^ 6 = 1
  lsym_SInt : ∀ y : SInt 𝔪, y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
    localSymbol ι 𝔪 P (y : F) = sexticResidueSymbol ι 𝔪 P y
  Eloc_split : ∀ k : ℕ, k ≠ 0 → ∀ (e₀ : ℤ) (t : F),
    Eloc g P k e₀ t = mask g P (k % 6) 0 * Wsph g P e₀ t + Rsum g P (k % 6) e₀ t
  mask_zero : ∀ j : ℕ, j ≠ 0 → mask g P j 0 = 0
  Rsum_mono : ∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 → ∀ t : F,
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t = 1 →
    Rsum g P j e₀ t = Rsum g P j e₀ 1 * localSymbol ι 𝔪 P t ^ bexp j (e₀ + 2).toNat
  Rsum_one : ∀ e₀ : ℤ, 0 < e₀ + 2 → ∀ t : F,
    (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F t ≤ 1 → Rsum g P 1 e₀ t = 0
  Rsum_le : ∀ j : ℕ, j < 6 → ∀ e₀ : ℤ, 0 ≤ e₀ + 2 →
    ‖Rsum g P j e₀ 1‖ ≤ L2D_betaP (Ideal.absNorm P) (e₀ + 2).toNat
  mask_le : ∀ j : ℕ, ‖mask g P j 0‖ ≤ 1
  gp_le : ‖gaussPhase g 2 P‖ ≤ 1

/-- The standing hypotheses at the modulus `𝔪`. -/
structure Env (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) : Prop where
  loc : ∀ (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hPe : IsExterior 𝔪 P),
    LocAt g P hP hPe

lemma Env.hχ {E : Env ι 𝔪} (g : AllowedGen ι 𝔪) : C3M.HypChi ι 𝔪 := fun P hP hPe =>
  ⟨(E.loc g P hP hPe).sext_mul, (E.loc g P hP hPe).sext_six⟩

theorem env_of_locPkg (n : ℕ) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (h : L3V_LocPkg n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → Env ι 𝔪 := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs => ⟨fun g P hP hPe => ?_⟩⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hN 𝔪 h𝔪 hs g P hP hPe
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩


section ucalc

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime)
  (he : IsExterior 𝔪 P)
include E hP he

omit E in
lemma notS_of_ext : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)) ∉ placesOf 𝔪 := fun hv =>
  hP.ne_top (eq_top_iff.2 (he.2 ▸ sup_le le_rfl hv))

omit E in
lemma val_le_oneE (r : SInt 𝔪) : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (r : F) ≤ 1 :=
  r.2 _ (notS_of_ext hP he)

omit E in
lemma val_unitE (μ : (SInt 𝔪)ˣ) :
    (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F ((μ : SInt 𝔪) : F) = 1 := by
  have h1 := val_le_oneE hP he (μ : SInt 𝔪)
  have h2 := val_le_oneE hP he ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)
  have h3 : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F ((μ : SInt 𝔪) : F) *
      (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F
        (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

lemma val_piE : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (g.gen P : F) = exp (-1 : ℤ) := by
  rw [(E.loc g P hP he).val_gen P he]
  have : (normalizedFactors P).count P = 1 := by
    have := cnt_prime (P := P) hP he.1; simpa using this
  rw [this]; simp

lemma vP_genE (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    vP P (g.gen I : F) = ((normalizedFactors I).count P : ℤ) := by
  have := vP_v (v := ⟨P, hP, he.1⟩) (g.gen I : F)
  change vP P _ = _ at this
  rw [this, (E.loc g P hP he).val_gen I hI, log_exp, neg_neg]

omit E g in
lemma vP_unitE (μ : (SInt 𝔪)ˣ) : vP P ((μ : SInt 𝔪) : F) = 0 := by
  have := vP_v (v := ⟨P, hP, he.1⟩) ((μ : SInt 𝔪) : F)
  change vP P _ = _ at this
  rw [this, val_unitE hP he]; simp

lemma val_unitPartE {x : F} (hx : x ≠ 0) :
    (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (x * (g.gen P : F) ^ (-(vP P x))) = 1 := by
  have h := val_eq_exp_vP (v := ⟨P, hP, he.1⟩) hx
  change _ = exp (-(vP P x)) at h
  rw [map_mul, map_zpow₀, val_piE E g hP he, h, ← exp_zsmul, ← exp_add]
  simp

lemma p_ne_zeroE : (g.gen P : F) ≠ 0 := C3B.gen_ne_zero g P he

lemma uSym_mulE {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    uSym g P (x * y) = uSym g P x * uSym g P y := by
  unfold uSym
  rw [← (E.loc g P hP he).lsym_mul _ _ (val_unitPartE E g hP he hx) (val_unitPartE E g hP he hy)]
  have h := vP_mul (v := ⟨P, hP, he.1⟩) hx hy
  change vP P (x * y) = vP P x + vP P y at h
  rw [h, neg_add, zpow_add₀ (p_ne_zeroE E g hP he)]
  ring_nf

lemma uSym_pow_sixE {x : F} (hx : x ≠ 0) : uSym g P x ^ 6 = 1 :=
  (E.loc g P hP he).lsym_six _ (val_unitPartE E g hP he hx)

lemma uSym_oneE : uSym g P (1 : F) = 1 := by
  have hv1 : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (1 : F) = 1 := map_one _
  have h1 := (E.loc g P hP he).lsym_mul 1 1 hv1 hv1
  have h6 := (E.loc g P hP he).lsym_six 1 hv1
  rw [mul_one] at h1
  have h0 : localSymbol ι 𝔪 P 1 ≠ 0 := by intro h0; rw [h0] at h6; norm_num at h6
  have hl : localSymbol ι 𝔪 P 1 = 1 := by
    have := mul_left_cancel₀ h0 (h1.symm.trans (mul_one _).symm); exact this
  have hvp : vP P (1 : F) = 0 := by
    have := vP_v (v := ⟨P, hP, he.1⟩) (1 : F)
    change vP P _ = _ at this
    rw [this, hv1]; simp
  unfold uSym; rw [hvp, neg_zero, zpow_zero, mul_one, hl]

lemma uSym_powE {x : F} (hx : x ≠ 0) (n : ℕ) : uSym g P (x ^ n) = uSym g P x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, uSym_oneE E g hP he]
  | succ n ih => rw [pow_succ, uSym_mulE E g hP he (pow_ne_zero _ hx) hx, ih, pow_succ]

lemma uSym_SIntE {y : SInt 𝔪} (hy : y ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    uSym g P (y : F) = sexticResidueSymbol ι 𝔪 P y := by
  have hv := ((E.loc g P hP he).mem_iff y).1 hy
  have hvp : vP P (y : F) = 0 := by
    have := vP_v (v := ⟨P, hP, he.1⟩) (y : F)
    change vP P _ = _ at this
    rw [this, hv]; simp
  unfold uSym; rw [hvp, neg_zero, zpow_zero, mul_one, (E.loc g P hP he).lsym_SInt y hy]

lemma uSym_pow_six_unitE (μ : (SInt 𝔪)ˣ) : uSym g P (((μ : SInt 𝔪) : F) ^ 6) = 1 := by
  have hμ : ((μ : SInt 𝔪) : F) ≠ 0 := by
    intro h0; have := val_unitE hP he μ; rw [h0, map_zero] at this; exact zero_ne_one this
  rw [uSym_powE E g hP he hμ, uSym_pow_sixE E g hP he hμ]

end ucalc

end L3V

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3X_Coef: the forward Fourier coefficient and Cor 5.2

* `coefF g 𝔟 z`: the forward coefficient of `L3X_CutKP` at the frequency class `z` (row ideal `𝔟`):
  `χ_𝔟(x) ∏_{P ∣ 𝔷} W_P(a(x))`, `x = rowElt g z`, with `W_P` the spherical values (5.4).
* `gaussPhase_eq_prod_uSym` (from (3.10)): `γ₂(𝔠) = ∏_{P ∣ 𝔠} γ₂(P) χ_P(c/p)²` for squarefree `𝔠`.
* `prodW_cube` (Cor 5.2): `∏_{P ∣ 𝔠𝔫³} χ_P(A/p^e)^{2e} W_P(p^e) = γ₂(𝔠) / (q_𝔠^{1/2} q_𝔫)`,
  `A = gen(𝔠𝔫³)`, and the product vanishes when some exponent is `≡ 2 (mod 3)`.
* `tsum_coefF_eq_fwd`: the forward unfolded sum is Cut63V's left side `L3V.fwd`.
* `norm_coefF_le`: `‖coefF‖ ≤ 1`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots.L3X

open L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The forward Fourier coefficient of `L3X_CutKP` at the frequency class `z`, for the row ideal `𝔟`. -/
noncomputable def coefF (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (z : RowClass 𝔪) : ℂ :=
  residueSymbol ι 𝔪 𝔟 (rowElt g z) *
    ∏ P ∈ (normalizedFactors z.1.1).toFinset,
      L3V.Wsph g P ((normalizedFactors z.1.1).count P : ℤ)
        ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))

/-! ### Norm bounds -/

lemma norm_sext_le (P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have hζ := h2.choose_spec.1
    have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow]
      have : ((h2.choose : 𝓞 F) : F) ^ 6 = 1 := by
        exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) hζ
      rw [this, map_one]
    have hn : ‖ι (h2.choose : F)‖ ^ 6 = 1 := by rw [← norm_pow, h6, norm_one]
    have := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (6 : ℕ) ≠ 0)).1 hn
    rw [this]
  · simp

lemma norm_residueSymbol_le' (𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact (mul_le_mul (norm_sext_le P x) ih (norm_nonneg _) zero_le_one).trans (by norm_num)

lemma norm_localSymbol_le (P : Ideal (𝓞 F)) (t : F) : ‖localSymbol ι 𝔪 P t‖ ≤ 1 := by
  unfold localSymbol
  split_ifs with h
  · rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (norm_sext_le P _) (norm_sext_le P _) (norm_nonneg _) zero_le_one).trans
      (by norm_num)
  · simp

lemma norm_Wv_le_of (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (hP1 : (1 : ℝ) ≤ Ideal.absNorm P)
    (hgp : ‖gaussPhase g 2 P‖ ≤ 1) (e : ℕ) : ‖Wv g P e‖ ≤ 1 := by
  unfold Wv
  have hq0 : (0 : ℝ) < Ideal.absNorm P := lt_of_lt_of_le zero_lt_one hP1
  split_ifs with h0 h1
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    have : (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hP1 (by have := (e / 3 : ℕ).cast_nonneg (α := ℝ); linarith)
    exact (mul_le_mul this hgp (norm_nonneg _) zero_le_one).trans (by norm_num)
  · simp

lemma norm_Wsph_le_of (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (hP1 : (1 : ℝ) ≤ Ideal.absNorm P)
    (hgp : ‖gaussPhase g 2 P‖ ≤ 1) (e₀ : ℤ) (t : F) : ‖Wsph g P e₀ t‖ ≤ 1 := by
  unfold Wsph
  split_ifs
  · simp
  · rw [norm_mul, norm_pow]
    exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (norm_localSymbol_le P t))
      (norm_Wv_le_of g P hP1 hgp _) (norm_nonneg _) zero_le_one).trans (by norm_num)

lemma one_le_absNorm_of_prime {P : Ideal (𝓞 F)} (_hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (1 : ℝ) ≤ Ideal.absNorm P := by
  have : Ideal.absNorm P ≠ 0 := fun h => hP0 (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

theorem norm_coefF_le (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (z : RowClass 𝔪) :
    ‖coefF g 𝔟 z‖ ≤ 1 := by
  unfold coefF
  rw [norm_mul, norm_prod]
  refine (mul_le_mul (norm_residueSymbol_le' _ _) (Finset.prod_le_one (fun _ _ => norm_nonneg _)
    fun P hP => ?_) (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one).trans (by norm_num)
  obtain ⟨hPp, hPe⟩ := C3M.exterior_of_mem_factors z.1.2 (Multiset.mem_toFinset.1 hP)
  exact norm_Wsph_le_of g P (one_le_absNorm_of_prime hPp hPe.1) (E.loc g P hPp hPe).gp_le _ _


/-! ### Unit-part symbols of generators -/

section ucalc

variable (E : Env ι 𝔪) (g : AllowedGen ι 𝔪)

lemma unitF_ne (μ : (SInt 𝔪)ˣ) : ((μ : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have : (μ : SInt 𝔪) = 0 := Subtype.ext h0
  exact μ.ne_zero this

lemma rep_one_pow : ∃ μ : (SInt 𝔪)ˣ, (SClass.rep (1 : SClass 𝔪) : SInt 𝔪) = (μ : SInt 𝔪) ^ 6 := by
  set w := Function.surjInv (QuotientGroup.mk_surjective
    (s := (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)) (1 : SClass 𝔪)
  have hw : (w : SClass 𝔪) = 1 := Function.surjInv_eq _ _
  rw [QuotientGroup.eq_one_iff] at hw
  obtain ⟨ν, hν⟩ := hw
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ν, ?_⟩
  change ((Set.unitEquivUnitsInteger (placesOf 𝔪) F w : (SInt 𝔪)ˣ) : SInt 𝔪) = _
  rw [← hν, powMonoidHom_apply, map_pow, Units.val_pow_eq_pow_val]

variable {P : Ideal (𝓞 F)} (hP : P.IsPrime) (he : IsExterior 𝔪 P)
include E g hP he

lemma localSymbol_one : localSymbol ι 𝔪 P 1 = 1 := by
  have h := uSym_oneE E g hP he
  have hvp : vP P (1 : F) = 0 := by
    have := vP_v (v := ⟨P, hP, he.1⟩) (1 : F)
    change vP P _ = _ at this
    rw [this, map_one]; simp
  unfold uSym at h
  rwa [hvp, neg_zero, zpow_zero, mul_one] at h

lemma uSym_gen_self : uSym g P (g.gen P : F) = 1 := by
  unfold uSym
  rw [vP_genE E g hP he P he]
  have hc : (normalizedFactors P).count P = 1 := by
    have := cnt_prime (P := P) hP he.1; simpa using this
  rw [hc, Nat.cast_one, zpow_neg, zpow_one, mul_inv_cancel₀ (C3B.gen_ne_zero g P he)]
  exact localSymbol_one E g hP he

lemma uSym_gen_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    uSym g P (g.gen (I * J) : F) = uSym g P (g.gen I : F) * uSym g P (g.gen J : F) := by
  obtain ⟨ε, hε⟩ := C3M.gen_mul' g hI hJ
  have hεF : ((g.gen (I * J) : SInt 𝔪) : F) =
      ((ε : SInt 𝔪) : F) ^ 6 * ((g.gen I : SInt 𝔪) : F) * ((g.gen J : SInt 𝔪) : F) := by
    rw [hε]; simp
  have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := unitF_ne ε
  rw [hεF, uSym_mulE E g hP he (mul_ne_zero (pow_ne_zero _ hε0) (C3B.gen_ne_zero g I hI))
    (C3B.gen_ne_zero g J hJ), uSym_mulE E g hP he (pow_ne_zero _ hε0) (C3B.gen_ne_zero g I hI),
    uSym_pow_six_unitE E g hP he, one_mul]

lemma uSym_gen_top : uSym g P (g.gen ⊤ : F) = 1 := by
  obtain ⟨ε, hε⟩ := C3M.gen_top g
  have : ((g.gen ⊤ : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) ^ 6 := by rw [hε]; simp
  rw [this, uSym_pow_six_unitE E g hP he]

lemma uSym_gen_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    uSym g P (g.gen (I ^ n) : F) = uSym g P (g.gen I : F) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, uSym_gen_top E g hP he]
  | succ n ih =>
    rw [pow_succ, uSym_gen_mul E g hP he (C3B.isExterior_pow hI n) hI, ih, pow_succ]

lemma uSym_gen_of_count_zero {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (h0 : (normalizedFactors I).count P = 0) :
    uSym g P (g.gen I : F) = sexticResidueSymbol ι 𝔪 P (g.gen I) := by
  have hv : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)).valuation F (g.gen I : F) = 1 := by
    rw [(E.loc g P hP he).val_gen I hI, h0]; simp
  exact uSym_SIntE E g hP he (((E.loc g P hP he).mem_iff _).2 hv)

lemma uSym_rowElt_one {𝔷 : Ideal (𝓞 F)} (h𝔷 : IsExterior 𝔪 𝔷) :
    uSym g P (rowElt g (⟨𝔷, h𝔷⟩, 1) : F) = uSym g P (g.gen 𝔷 : F) := by
  obtain ⟨μ, hμ⟩ := rep_one_pow (𝔪 := 𝔪)
  have : (rowElt g (⟨𝔷, h𝔷⟩, 1) : F) = ((μ : SInt 𝔪) : F) ^ 6 * (g.gen 𝔷 : F) := by
    unfold rowElt; simp [hμ]
  rw [this, uSym_mulE E g hP he (pow_ne_zero _ (unitF_ne μ)) (C3B.gen_ne_zero g 𝔷 h𝔷),
    uSym_pow_six_unitE E g hP he, one_mul]

/-- The Wsph factor of `coefF` at a prime of `𝔷`. -/
lemma Wsph_rowElt_one {𝔷 : Ideal (𝓞 F)} (h𝔷 : IsExterior 𝔪 𝔷) :
    Wsph g P ((normalizedFactors 𝔷).count P : ℤ)
        ((rowElt g (⟨𝔷, h𝔷⟩, 1) : F) * (g.gen P : F) ^ (-((normalizedFactors 𝔷).count P : ℤ))) =
      uSym g P (g.gen 𝔷 : F) ^ (2 * (normalizedFactors 𝔷).count P) *
        Wv g P ((normalizedFactors 𝔷).count P) := by
  obtain ⟨μ, hμ⟩ := rep_one_pow (𝔪 := 𝔪)
  have hx : (rowElt g (⟨𝔷, h𝔷⟩, 1) : F) = ((μ : SInt 𝔪) : F) ^ 6 * (g.gen 𝔷 : F) := by
    unfold rowElt; simp [hμ]
  have hx0 : (rowElt g (⟨𝔷, h𝔷⟩, 1) : F) ≠ 0 := by
    rw [hx]; exact mul_ne_zero (pow_ne_zero _ (unitF_ne μ)) (C3B.gen_ne_zero g 𝔷 h𝔷)
  have hvp : vP P (rowElt g (⟨𝔷, h𝔷⟩, 1) : F) = ((normalizedFactors 𝔷).count P : ℤ) := by
    rw [hx, vP_mul (v := ⟨P, hP, he.1⟩) (pow_ne_zero _ (unitF_ne μ))
      (C3B.gen_ne_zero g 𝔷 h𝔷)]
    change vP P _ + vP P _ = _
    have h6 : ((μ : SInt 𝔪) : F) ^ 6 = (((μ ^ 6 : (SInt 𝔪)ˣ) : SInt 𝔪) : F) := by simp
    rw [vP_genE E g hP he 𝔷 h𝔷, h6, vP_unitE hP he, zero_add]
  have hls : localSymbol ι 𝔪 P ((rowElt g (⟨𝔷, h𝔷⟩, 1) : F) *
      (g.gen P : F) ^ (-((normalizedFactors 𝔷).count P : ℤ))) = uSym g P (g.gen 𝔷 : F) := by
    rw [← uSym_rowElt_one E g hP he h𝔷]
    unfold uSym; rw [hvp]
  unfold Wsph
  rw [if_neg (by omega), hls]
  simp

end ucalc


/-! ### (3.10) in unit-part form, and Cor 5.2 -/

lemma prim_mul_prime {Q 𝔞 : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) (ha : 𝔞 ≠ ⊥) :
    prim (Q * 𝔞) = insert Q (prim 𝔞) := by
  unfold prim
  rw [normalizedFactors_mul hQ0 ha, nf_prime' hQ hQ0, Multiset.toFinset_add,
    Multiset.toFinset_singleton, Finset.insert_eq]

theorem gaussPhase_eq_prod_uSym (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) (𝔠 : Ideal (𝓞 F)) :
    IsExterior 𝔪 𝔠 → Squarefree 𝔠 →
      gaussPhase g 2 𝔠 = ∏ P ∈ prim 𝔠, gaussPhase g 2 P * uSym g P (g.gen 𝔠 : F) ^ 2 := by
  induction 𝔠 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro _ _
    have : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst this
    rw [C3B.gaussPhase_top]
    simp [prim, C3B.normalizedFactors_top]
  | h₃ 𝔞 Q ha hQ ih =>
    intro hQa hsq
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := C3M.isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 𝔞 := C3M.isExterior_of_mul_right hQa
    have hsqa : Squarefree 𝔞 := hsq.of_mul_right
    have hQn : cnt Q 𝔞 = 0 := by
      have h1 := (squarefree_iff_cnt hQa.1).1 hsq Q
      rw [cnt_mul hQe.1 hae.1, cnt_prime hQp hQe.1, if_pos rfl] at h1
      omega
    have hcop : IsCoprime Q 𝔞 := by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine (sup_eq_top_iff_cnt hQe.1 hae.1).2 fun P => ?_
      rw [cnt_prime hQp hQe.1]
      by_cases hPQ : P = Q
      · subst hPQ; right; exact hQn
      · left; simp [hPQ]
    have hQnot : Q ∉ prim 𝔞 := fun h => by rw [mem_prim_iff] at h; omega
    rw [C3M.gaussPhase_mul (C3M.hypAdd 𝔪) (E.hχ g) g hQe hae hcop 2, ih hae hsqa,
      prim_mul_prime hQp hQe.1 hae.1, Finset.prod_insert hQnot]
    -- the new prime
    have hQQ : uSym g Q (g.gen (Q * 𝔞) : F) = sexticResidueSymbol ι 𝔪 Q (g.gen 𝔞) := by
      rw [uSym_gen_mul E g hQp hQe hQe hae, uSym_gen_self E g hQp hQe, one_mul,
        uSym_gen_of_count_zero E g hQp hQe hae hQn]
    -- the old primes
    have hold : ∀ P ∈ prim 𝔞, gaussPhase g 2 P * uSym g P (g.gen (Q * 𝔞) : F) ^ 2 =
        (gaussPhase g 2 P * uSym g P (g.gen 𝔞 : F) ^ 2) * sexticResidueSymbol ι 𝔪 P (g.gen Q) ^ 2 := by
      intro P hP
      obtain ⟨hPp, hP0⟩ := prime_of_mem_prim hP
      have hPe : IsExterior 𝔪 P := exterior_of_prim hae hP
      have hPQ : P ≠ Q := fun h => hQnot (h ▸ hP)
      have hc : (normalizedFactors Q).count P = 0 := by
        have := cnt_prime (P := P) hQp hQe.1; simpa [hPQ] using this
      rw [uSym_gen_mul E g hPp hPe hQe hae, uSym_gen_of_count_zero E g hPp hPe hQe hc]
      ring
    rw [Finset.prod_congr rfl hold, Finset.prod_mul_distrib, C3M.residueSymbol_prime hQp hQe.1,
      residueSymbol_sqfree ι 𝔪 𝔞 hae.1 hsqa, ← Finset.prod_pow, hQQ]
    simp only [Finset.prod_mul_distrib]
    ring

/-- Cor 5.2: the exterior spherical product at `𝔷 = 𝔠𝔫³`. -/
theorem prodW_cube (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {𝔠 𝔫 : Ideal (𝓞 F)}
    (h𝔠 : IsExterior 𝔪 𝔠) (hsq : Squarefree 𝔠) (h𝔫 : IsExterior 𝔪 𝔫) :
    ∏ P ∈ prim (𝔠 * 𝔫 ^ 3), uSym g P (g.gen (𝔠 * 𝔫 ^ 3) : F) ^ (2 * cnt P (𝔠 * 𝔫 ^ 3)) *
        Wv g P (cnt P (𝔠 * 𝔫 ^ 3)) =
      gaussPhase g 2 𝔠 / ((Real.sqrt (Ideal.absNorm 𝔠) * Ideal.absNorm 𝔫 : ℝ) : ℂ) := by
  have h𝔫3 : IsExterior 𝔪 (𝔫 ^ 3) := C3B.isExterior_pow h𝔫 3
  have h𝔷 : IsExterior 𝔪 (𝔠 * 𝔫 ^ 3) := C3B.isExterior_mul h𝔠 h𝔫3
  have hcnt : ∀ P, cnt P (𝔠 * 𝔫 ^ 3) = cnt P 𝔠 + 3 * cnt P 𝔫 := fun P => by
    rw [cnt_mul h𝔠.1 h𝔫3.1, cnt_pow]
  have hc1 : ∀ P, cnt P 𝔠 ≤ 1 := (squarefree_iff_cnt h𝔠.1).1 hsq
  set A : Ideal (𝓞 F) → ℂ := fun P => (((Ideal.absNorm P : ℝ) ^ (-(cnt P 𝔫 : ℝ)) : ℝ) : ℂ)
  set B : Ideal (𝓞 F) → ℂ := fun P => if cnt P 𝔠 = 1 then
    (((Ideal.absNorm P : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (gaussPhase g 2 P * uSym g P (g.gen 𝔠 : F) ^ 2) else 1
  have hterm : ∀ P ∈ prim (𝔠 * 𝔫 ^ 3),
      uSym g P (g.gen (𝔠 * 𝔫 ^ 3) : F) ^ (2 * cnt P (𝔠 * 𝔫 ^ 3)) * Wv g P (cnt P (𝔠 * 𝔫 ^ 3)) =
        A P * B P := by
    intro P hP
    obtain ⟨hPp, hP0⟩ := prime_of_mem_prim hP
    have hPe : IsExterior 𝔪 P := exterior_of_prim h𝔷 hP
    have hq0 : (0 : ℝ) < Ideal.absNorm P :=
      lt_of_lt_of_le zero_lt_one (one_le_absNorm_of_prime hPp hP0)
    rw [uSym_gen_mul E g hPp hPe h𝔠 h𝔫3, uSym_gen_pow E g hPp hPe h𝔫]
    have ha6 := uSym_pow_sixE E g hPp hPe (C3B.gen_ne_zero g 𝔠 h𝔠)
    have hb6 := uSym_pow_sixE E g hPp hPe (C3B.gen_ne_zero g 𝔫 h𝔫)
    set a := uSym g P (g.gen 𝔠 : F)
    set b := uSym g P (g.gen 𝔫 : F)
    rw [hcnt P]
    set n := cnt P 𝔫
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hc1 P) with h0 | h1
    · rw [h0, zero_add]
      have hB : B P = 1 := by simp only [B, h0]; simp
      rw [hB, mul_one]
      have hpow : (a * b ^ 3) ^ (2 * (3 * n)) = 1 := by
        rw [mul_pow, ← pow_mul, show 2 * (3 * n) = 6 * n by ring,
          show 3 * (6 * n) = 6 * (3 * n) by ring, pow_mul, pow_mul, ha6, hb6, one_pow, one_pow,
          one_mul]
      rw [hpow, one_mul]
      unfold Wv
      rw [if_pos (by omega), show 3 * n / 3 = n by omega]
    · rw [h1]
      have hB : B P = (((Ideal.absNorm P : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (gaussPhase g 2 P * a ^ 2) := by simp only [B, h1, if_true, a]
      rw [hB]
      have hpow : (a * b ^ 3) ^ (2 * (1 + 3 * n)) = a ^ 2 := by
        rw [mul_pow, ← pow_mul, show 2 * (1 + 3 * n) = 2 + 6 * n by ring,
          show 3 * (2 + 6 * n) = 6 * (1 + 3 * n) by ring, pow_add, pow_mul, pow_mul, ha6, hb6,
          one_pow, one_pow, mul_one, mul_one]
      rw [hpow]
      unfold Wv
      rw [if_neg (by omega), if_pos (by omega), show (1 + 3 * n) / 3 = n by omega]
      simp only [A]
      rw [show -((n : ℕ) : ℝ) - 1 / 2 = -(n : ℝ) + -(1 / 2) by ring, Real.rpow_add hq0]
      push_cast
      ring
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  -- the `A` product
  have hsubN : prim 𝔫 ⊆ prim (𝔠 * 𝔫 ^ 3) := fun P hP => by
    rw [mem_prim_iff] at hP ⊢; rw [hcnt]; omega
  have hA : ∏ P ∈ prim (𝔠 * 𝔫 ^ 3), A P = (((Ideal.absNorm 𝔫 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Finset.prod_subset hsubN (fun P _ hP => by
      have : cnt P 𝔫 = 0 := by rw [mem_prim_iff] at hP; omega
      simp [A, this])]
    simp only [A]
    rw [← Complex.ofReal_prod, absNorm_eq_prod 𝔫 h𝔫.1, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    obtain ⟨hPp, hP0⟩ := prime_of_mem_prim hP
    have hq0 : (0 : ℝ) ≤ Ideal.absNorm P := Nat.cast_nonneg _
    rw [Real.rpow_neg hq0, Real.rpow_natCast]
  -- the `B` product
  have hsubC : prim 𝔠 ⊆ prim (𝔠 * 𝔫 ^ 3) := fun P hP => by
    rw [mem_prim_iff] at hP ⊢; rw [hcnt]; omega
  have hB : ∏ P ∈ prim (𝔠 * 𝔫 ^ 3), B P =
      (((Real.sqrt (Ideal.absNorm 𝔠))⁻¹ : ℝ) : ℂ) * gaussPhase g 2 𝔠 := by
    rw [← Finset.prod_subset hsubC (fun P _ hP => by
      have : cnt P 𝔠 ≠ 1 := by rw [mem_prim_iff] at hP; omega
      simp [B, this])]
    have hB' : ∀ P ∈ prim 𝔠, B P = (((Ideal.absNorm P : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (gaussPhase g 2 P * uSym g P (g.gen 𝔠 : F) ^ 2) := by
      intro P hP
      have : cnt P 𝔠 = 1 := by have := hc1 P; rw [mem_prim_iff] at hP; omega
      simp only [B, this, if_true]
    rw [Finset.prod_congr rfl hB', Finset.prod_mul_distrib,
      ← gaussPhase_eq_prod_uSym E g 𝔠 h𝔠 hsq, ← Complex.ofReal_prod]
    congr 2
    rw [Real.finsetProd_rpow _ _ (fun P _ => Nat.cast_nonneg _),
      Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _)]
    congr 1
    rw [absNorm_eq_prod 𝔠 h𝔠.1]
    refine Finset.prod_congr rfl fun P hP => ?_
    have : cnt P 𝔠 = 1 := by have := hc1 P; rw [mem_prim_iff] at hP; omega
    rw [this, pow_one]
  rw [hA, hB]
  push_cast
  rw [div_eq_mul_inv, mul_inv]
  ring


/-! ### The forward sum -/

lemma residueSymbol_gen_eq_zero {𝔞 I P : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (hP : P ∈ normalizedFactors 𝔞) (hI : IsExterior 𝔪 I) (hIP : I ≤ P) :
    residueSymbol ι 𝔪 𝔞 (g.gen I) = 0 := by
  unfold residueSymbol
  refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨P, hP, ?_⟩)
  unfold sexticResidueSymbol
  rw [if_pos]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have : g.gen I ∈ Ideal.span {g.gen I} := Ideal.mem_span_singleton_self _
  rw [g.span_gen I hI] at this
  exact Ideal.map_mono hIP this

lemma recip_gen (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {𝔟 𝔷 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (h𝔷 : IsExterior 𝔪 𝔷) : residueSymbol ι 𝔪 𝔟 (g.gen 𝔷) = residueSymbol ι 𝔪 𝔷 (g.gen 𝔟) := by
  by_cases hc : 𝔷 ⊔ 𝔟 = ⊤
  · exact (L3V.residueSymbol_recip (E.hχ g) g h𝔟 𝔷 h𝔷 hc).symm
  · rw [sup_eq_top_iff_cnt h𝔷.1 h𝔟.1] at hc
    push Not at hc
    obtain ⟨P, h1, h2⟩ := hc
    have hP1 : P ∈ normalizedFactors 𝔷 := Multiset.count_pos.1 (Nat.pos_of_ne_zero h1)
    have hP2 : P ∈ normalizedFactors 𝔟 := Multiset.count_pos.1 (Nat.pos_of_ne_zero h2)
    rw [residueSymbol_gen_eq_zero g hP2 h𝔷 (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP1)),
      residueSymbol_gen_eq_zero g hP1 h𝔟 (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP2))]

lemma coefF_one (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (𝔷 : {𝔷 : Ideal (𝓞 F) // IsExterior 𝔪 𝔷}) :
    coefF g 𝔟 (𝔷, 1) = residueSymbol ι 𝔪 𝔟 (g.gen 𝔷.1) *
      ∏ P ∈ prim 𝔷.1, uSym g P (g.gen 𝔷.1 : F) ^ (2 * cnt P 𝔷.1) * Wv g P (cnt P 𝔷.1) := by
  unfold coefF
  obtain ⟨μ, hμ⟩ := rep_one_pow (𝔪 := 𝔪)
  have hx : rowElt g (𝔷, 1) = (μ : SInt 𝔪) ^ 6 * g.gen 𝔷.1 := by unfold rowElt; rw [hμ]
  congr 1
  · rw [hx, C3M.residueSymbol_unit_pow_six (E.hχ g) h𝔟]
  · refine Finset.prod_congr rfl fun P hP => ?_
    obtain ⟨hPp, hPe⟩ := C3M.exterior_of_mem_factors 𝔷.2 (Multiset.mem_toFinset.1 hP)
    exact Wsph_rowElt_one E g hPp hPe 𝔷.2

theorem tsum_coefF_eq_fwd (E : Env ι 𝔪) (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    (r : RowClass 𝔪) (V : ℝ → ℝ) (l : ℝ) (L : F → ℂ)
    (hL : ∀ z : RowClass 𝔪, z.2 = 1 →
      L (rowElt g z) = χ.thetaChar g z.1.1 * residueSymbol ι 𝔪 z.1.1 r.2.rep) :
    ∑' 𝔷 : {𝔷 : Ideal (𝓞 F) // IsExterior 𝔪 𝔷},
        coefF g r.1.1 (𝔷, 1) * L (rowElt g (𝔷, 1)) * ((V (Ideal.absNorm 𝔷.1 * l) : ℝ) : ℂ) =
      L3V.fwd g χ V r l := by
  set f : {𝔷 : Ideal (𝓞 F) // IsExterior 𝔪 𝔷} → ℂ := fun 𝔷 =>
    coefF g r.1.1 (𝔷, 1) * L (rowElt g (𝔷, 1)) * ((V (Ideal.absNorm 𝔷.1 * l) : ℝ) : ℂ)
  let φ : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
      {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} → {𝔷 : Ideal (𝓞 F) // IsExterior 𝔪 𝔷} :=
    fun p => ⟨p.1.1 * p.2.1 ^ 3, C3B.isExterior_mul p.1.2.1 (C3B.isExterior_pow p.2.2 3)⟩
  have hcnt : ∀ (𝔠 𝔫 : Ideal (𝓞 F)), 𝔠 ≠ ⊥ → 𝔫 ≠ ⊥ → ∀ P,
      cnt P (𝔠 * 𝔫 ^ 3) = cnt P 𝔠 + 3 * cnt P 𝔫 := fun 𝔠 𝔫 h1 h2 P => by
    rw [cnt_mul h1 (pow_ne_zero _ h2), cnt_pow]
  have hinj : Function.Injective φ := by
    rintro ⟨⟨𝔠, h𝔠, hs⟩, ⟨𝔫, h𝔫⟩⟩ ⟨⟨𝔠', h𝔠', hs'⟩, ⟨𝔫', h𝔫'⟩⟩ h
    have h' : 𝔠 * 𝔫 ^ 3 = 𝔠' * 𝔫' ^ 3 := congrArg Subtype.val h
    have hc1 := (squarefree_iff_cnt h𝔠.1).1 hs
    have hc1' := (squarefree_iff_cnt h𝔠'.1).1 hs'
    have key : ∀ P, cnt P 𝔠 = cnt P 𝔠' ∧ cnt P 𝔫 = cnt P 𝔫' := fun P => by
      have := congrArg (cnt P) h'
      rw [hcnt _ _ h𝔠.1 h𝔫.1, hcnt _ _ h𝔠'.1 h𝔫'.1] at this
      have := hc1 P; have := hc1' P
      omega
    have e1 : 𝔠 = 𝔠' := eq_of_cnt h𝔠.1 h𝔠'.1 fun P _ _ => (key P).1
    have e2 : 𝔫 = 𝔫' := eq_of_cnt h𝔫.1 h𝔫'.1 fun P _ _ => (key P).2
    subst e1; subst e2; rfl
  have hsupp : Function.support f ⊆ Set.range φ := by
    intro 𝔷 h𝔷f
    have hne : coefF g r.1.1 (𝔷, 1) ≠ 0 := fun h0 => h𝔷f (by simp only [f, h0, zero_mul])
    rw [coefF_one E g r.1.2] at hne
    have hprod := right_ne_zero_of_mul hne
    have hmod : ∀ P ∈ prim 𝔷.1, cnt P 𝔷.1 % 3 ≠ 2 := by
      intro P hP h2
      apply hprod
      refine Finset.prod_eq_zero hP ?_
      unfold Wv
      rw [if_neg (by omega), if_neg (by omega), mul_zero]
    set s := (prim 𝔷.1).filter (fun P => cnt P 𝔷.1 % 3 = 1)
    have hsP : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥ := fun Q hQ =>
      prime_of_mem_prim (Finset.mem_filter.1 hQ).1
    have hzP : ∀ Q ∈ prim 𝔷.1, Q.IsPrime ∧ Q ≠ ⊥ := fun Q hQ => prime_of_mem_prim hQ
    set 𝔠 := ∏ Q ∈ s, Q ^ (fun _ => 1) Q
    set 𝔫 := ∏ Q ∈ prim 𝔷.1, Q ^ (fun Q => cnt Q 𝔷.1 / 3) Q
    have h𝔠e : IsExterior 𝔪 𝔠 := exterior_prod_pow s
      (fun Q hQ => exterior_of_prim 𝔷.2 (Finset.mem_filter.1 hQ).1) _
    have h𝔫e : IsExterior 𝔪 𝔫 := exterior_prod_pow _ (fun Q hQ => exterior_of_prim 𝔷.2 hQ) _
    have hc𝔠 : ∀ P, cnt P 𝔠 = if P ∈ s then 1 else 0 := fun P => cnt_prod_pow P s hsP _
    have hc𝔫 : ∀ P, cnt P 𝔫 = if P ∈ prim 𝔷.1 then cnt P 𝔷.1 / 3 else 0 := fun P =>
      cnt_prod_pow P _ hzP _
    have hsq : Squarefree 𝔠 := (squarefree_iff_cnt h𝔠e.1).2 fun P => by
      rw [hc𝔠]; split_ifs <;> omega
    refine ⟨(⟨𝔠, h𝔠e, hsq⟩, ⟨𝔫, h𝔫e⟩), Subtype.ext ?_⟩
    refine eq_of_cnt (C3B.isExterior_mul h𝔠e (C3B.isExterior_pow h𝔫e 3)).1 𝔷.2.1 fun P _ _ => ?_
    change cnt P (𝔠 * 𝔫 ^ 3) = cnt P 𝔷.1
    rw [hcnt _ _ h𝔠e.1 h𝔫e.1, hc𝔠, hc𝔫]
    by_cases hP : P ∈ prim 𝔷.1
    · have := hmod P hP
      have hs' : P ∈ s ↔ cnt P 𝔷.1 % 3 = 1 := by
        rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩
      by_cases h1 : cnt P 𝔷.1 % 3 = 1
      · rw [if_pos (hs'.2 h1), if_pos hP]; omega
      · rw [if_neg (fun h => h1 (hs'.1 h)), if_pos hP]; omega
    · have hs' : P ∉ s := fun h => hP (Finset.mem_filter.1 h).1
      rw [if_neg hs', if_neg hP]
      rw [mem_prim_iff] at hP; omega
  rw [← hinj.tsum_eq hsupp]
  unfold L3V.fwd
  refine tsum_congr fun p => ?_
  obtain ⟨⟨𝔠, h𝔠, hs⟩, ⟨𝔫, h𝔫⟩⟩ := p
  simp only [f, φ]
  set 𝔷 : {𝔷 : Ideal (𝓞 F) // IsExterior 𝔪 𝔷} :=
    ⟨𝔠 * 𝔫 ^ 3, C3B.isExterior_mul h𝔠 (C3B.isExterior_pow h𝔫 3)⟩ with h𝔷def
  rw [coefF_one E g r.1.2 𝔷, hL (𝔷, 1) rfl]
  have hW := prodW_cube E g h𝔠 hs h𝔫
  simp only [𝔷] at hW ⊢
  rw [hW]
  have hrow : rowElt g r = r.2.rep * g.gen r.1.1 := rfl
  rw [hrow, C3M.residueSymbol_mul (E.hχ g) (C3B.isExterior_mul h𝔠 (C3B.isExterior_pow h𝔫 3)),
    recip_gen E g r.1.2 (C3B.isExterior_mul h𝔠 (C3B.isExterior_pow h𝔫 3))]
  ring


/-! ### Bounds on the exterior local factors (no `HypChi`) -/

section bounds

variable (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P)
include hP hPe

theorem norm_Wv_le (e : ℕ) : ‖L3V.Wv g P e‖ ≤ 1 := by
  have hP1 := one_le_absNorm_of_prime hP hPe.1
  have hq0 : (0 : ℝ) < Ideal.absNorm P := lt_of_lt_of_le zero_lt_one hP1
  have hgp := L2B.norm_gaussPhase_le g 2 hPe
  unfold Wv
  split_ifs with h0 h1
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    calc (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) * ‖gaussPhase g 2 P‖
        ≤ (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) * Real.sqrt (Ideal.absNorm P) :=
          mul_le_mul_of_nonneg_left hgp (Real.rpow_nonneg hq0.le _)
      _ = (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq0]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp)
  · simp

theorem norm_Wsph_le (e₀ : ℤ) (t : F) : ‖L3V.Wsph g P e₀ t‖ ≤ 1 := by
  unfold Wsph
  split_ifs
  · simp
  · rw [norm_mul, norm_pow]
    exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (norm_localSymbol_le P t))
      (norm_Wv_le g hP hPe _) (norm_nonneg _) zero_le_one).trans (by norm_num)

omit hP hPe in
lemma norm_localAddChar_le (w : F) : ‖localAddChar g P w‖ ≤ 1 := by
  unfold localAddChar
  split_ifs
  · exact L2B.norm_sAddChar_le _ _
  · simp

theorem norm_Wweyl_le (e₀ : ℤ) (t : F) (v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ‖L3V.Wweyl g P e₀ t v‖ ≤ 1 := by
  unfold Wweyl
  split_ifs
  · simp
  · rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    have h1 := norm_Wv_le g hP hPe (e₀ + 2).toNat
    have h2 := pow_le_one₀ (n := 4 + 2 * (e₀ + 2).toNat) (norm_nonneg _) (norm_localSymbol_le (ι := ι) (𝔪 := 𝔪) P t)
    have h3 := pow_le_one₀ (n := 4) (norm_nonneg _) (norm_sext_le (ι := ι) P (quotLift v))
    have h4 := norm_localAddChar_le (P := P) g ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    calc _ ≤ (1 : ℝ) * 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num

end bounds

open Classical in
/-- A bound for `‖E_P‖` depending only on `g, P, k`. -/
noncomputable def ElocBd (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (k : ℕ) : ℝ :=
  if k = 0 then 1 else max 1 (∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
    ‖L3V.mask g P (k % 6) v‖)

lemma one_le_ElocBd (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (k : ℕ) : 1 ≤ ElocBd g P k := by
  unfold ElocBd; split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem norm_Eloc_le (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime)
    (hPe : IsExterior 𝔪 P) (k : ℕ) (e₀ : ℤ) (t : F) :
    ‖L3V.Eloc g P k e₀ t‖ ≤ ElocBd g P k := by
  classical
  unfold Eloc ElocBd
  split_ifs with hk
  · exact norm_Wsph_le g hP hPe e₀ t
  · refine le_trans ?_ (le_max_right _ _)
    have := C3M.finite_quot hPe
    have := Fintype.ofFinite (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)))
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    rw [norm_mul]
    have hX : ‖(if v = 0 then Wsph g P e₀ t else Wweyl g P e₀ t v)‖ ≤ 1 := by
      split_ifs
      · exact norm_Wsph_le g hP hPe e₀ t
      · exact norm_Wweyl_le g hP hPe e₀ t v
    calc _ ≤ ‖mask g P (k % 6) v‖ * 1 := mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      _ = _ := mul_one _

theorem exists_norm_Eprod_le (g : AllowedGen ι 𝔪) (r : RowClass 𝔪) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : RowClass 𝔪, ‖L3V.Eprod g r z‖ ≤ C := by
  refine ⟨∏ P ∈ prim r.1.1, ElocBd g P (cnt P r.1.1),
    Finset.prod_nonneg fun P _ => le_trans zero_le_one (one_le_ElocBd g P _), fun z => ?_⟩
  have hzr : IsExterior 𝔪 (z.1.1 * r.1.1) := C3B.isExterior_mul z.1.2 r.1.2
  unfold Eprod
  rw [norm_prod]
  calc ∏ P ∈ prim (z.1.1 * r.1.1), ‖Eloc g P (cnt P r.1.1) (e0 r z P)
          (nu g r z * (g.gen P : F) ^ (-(e0 r z P)))‖
      ≤ ∏ P ∈ prim (z.1.1 * r.1.1), ElocBd g P (cnt P r.1.1) := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_
        obtain ⟨hPp, _⟩ := prime_of_mem_prim hP
        exact norm_Eloc_le g hPp (exterior_of_prim hzr hP) _ _ _
    _ = ∏ P ∈ prim r.1.1, ElocBd g P (cnt P r.1.1) := by
        symm
        refine Finset.prod_subset (fun P hP => ?_) (fun P _ hP => ?_)
        · rw [mem_prim_iff] at hP ⊢; rw [cnt_mul z.1.2.1 r.1.2.1]; omega
        · have : cnt P r.1.1 = 0 := by rw [mem_prim_iff] at hP; omega
          simp [ElocBd, this]

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-!
# L3P_Gen: `R ∖ 0 = U_S · {gen 𝔟}`

With a system of allowed generators, every nonzero `m ∈ R` is uniquely `ε · gen 𝔟` with `𝔟`
exterior and `ε ∈ R^×`. Sums over `R` (with vanishing term at `0`) are sums over these pairs.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-- Exterior ideals. -/
abbrev Ext (𝔪 : Ideal (𝓞 F)) : Type _ := {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟}

variable {ι : F →+* ℂ}

theorem span_unit_mul_gen (g : AllowedGen ι 𝔪) (𝔟 : Ext 𝔪) (ε : (SInt 𝔪)ˣ) :
    Ideal.span {(ε : SInt 𝔪) * g.gen 𝔟.1} = 𝔟.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← g.span_gen 𝔟.1 𝔟.2, Ideal.span_singleton_mul_left_unit ε.isUnit]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-! # L3X_Fwd: the forward orbit unfolding

`∫_{X_l} Φ(y) Σ_{z, γ} coef(z) f⁺(γ m_z y) = Σ_z coef(z) 1_B([m_z]) L(m_z) V(q_{m_z} l)`
(the paper's (6.1)/`eq:reflection-forward-unfolding`), with absolute convergence.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical ENNReal

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

instance L3X_countable_ideal : Countable (Ideal (𝓞 F)) := by
  have : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
    ext I; simp
  have hc : (Set.univ : Set (Ideal (𝓞 F))).Countable := by
    rw [this]
    exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
  exact Set.countable_univ_iff.1 hc

theorem span_rowElt [Fintype (L3P.SP 𝔪)] (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    Ideal.span {rowElt g z} = z.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  L3P.span_unit_mul_gen g z.1 _

theorem rowElt_ne_zero [Fintype (L3P.SP 𝔪)] (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    (rowElt g z : F) ≠ 0 :=
  L3P.ne_zero_of_span_eq z.1.2 (span_rowElt g z)

theorem lnorm_rowElt [Fintype (L3P.SP 𝔪)] (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    lnorm (sEmb 𝔪 k (rowElt g z : F)) = Real.log (Ideal.absNorm z.1.1 : ℝ) :=
  lnorm_sEmb_gen h𝔪 z.1.2 (span_rowElt g z)

theorem absNorm_pos_of_ext {𝔷 : Ideal (𝓞 F)} (h : IsExterior 𝔪 𝔷) : (0 : ℝ) < Ideal.absNorm 𝔷 := by
  have : Ideal.absNorm 𝔷 ≠ 0 := by rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact h.1
  exact_mod_cast Nat.pos_of_ne_zero this

theorem summable_rowClass_rpow [Finite (SClass 𝔪)] :
    Summable (fun z : RowClass 𝔪 => (Ideal.absNorm z.1.1 : ℝ) ^ (-(2 : ℝ))) := by
  have : Fintype (SClass 𝔪) := Fintype.ofFinite _
  have h1 : Summable (fun 𝔷 : {𝔷 : Ideal (𝓞 F) // IsExterior 𝔪 𝔷} =>
      ((Ideal.absNorm 𝔷.1 : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
    (T12B.summable_absNorm_rpow (F := F) (by norm_num : (1 : ℝ) < 2)).comp_injective
      Subtype.val_injective
  have h0 : ∀ z : RowClass 𝔪, 0 ≤ (Ideal.absNorm z.1.1 : ℝ) ^ (-(2 : ℝ)) := fun z =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine (summable_prod_of_nonneg h0).2 ⟨fun x => Summable.of_finite, ?_⟩
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact h1.mul_left _

/-- `κ(e^x) ≤ C bmaj α 3 x`, with `C ≥ 0`. -/
theorem kappa_bmaj (κ : ℝ → ℝ) (_hκ0 : ∀ t, 0 ≤ κ t) {α : ℝ}
    (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, κ (Real.exp x) ≤ C * bmaj α 3 x := by
  obtain ⟨C, hC⟩ := hκb 3 (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have h := hC (Real.exp x) (Real.exp_pos x)
  have he : min (Real.exp x ^ α) (Real.exp x ^ (-(3 : ℝ))) = bmaj α 3 x := by
    rw [bmaj, ← Real.exp_mul, ← Real.exp_mul]; congr 2 <;> ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (bmaj_nonneg _ _ _))

section Main

variable [Fintype (L3P.SP 𝔪)] (h𝔪 : 𝔪 ≠ ⊥) (w₀ : InfinitePlace F)

include h𝔪 in
/-- The absolute sheet integral of `f⁺` decays like `|X|^{-2}`. -/
theorem lintegral_fpAbs_le (κ : ℝ → ℝ) (hκ0 : ∀ t, 0 ≤ κ t) {α : ℝ} (hα : 0 < α)
    (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ,
      ∫⁻ y, ENNReal.ofReal (fpAbs κ y) ∂(shMeasure w₀ 𝔪 k b) ≤
        ENNReal.ofReal (C * Real.exp (-(2 * b))) := by
  obtain ⟨Cκ, hCκ0, hCκ⟩ := kappa_bmaj κ hκ0 hκb
  set bf : SFin 𝔪 k → ℝ := fun y => if y = 0 then Cκ ^ Fintype.card (InfinitePlace F) else 0
  have hbf0 : ∀ y, 0 ≤ bf y := fun y => by
    simp only [bf]; split_ifs
    · exact pow_nonneg hCκ0 _
    · exact le_rfl
  have hbfs : Summable (fun y => bf y * (SFin.norm y) ^ (2 : ℝ)) := by
    refine summable_of_ne_finset_zero (s := {0}) fun y hy => ?_
    simp only [Finset.mem_singleton] at hy
    simp [bf, hy]
  obtain ⟨C, hC0, hC⟩ := lintegral_majorant_le w₀ h𝔪 (α := α) (N := 3) (σ := 2)
    (by linarith) (by norm_num) bf hbf0 hbfs
  refine ⟨C, hC0, fun b => ?_⟩
  refine le_trans (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_) (hC b)
  unfold fpAbs
  split_ifs with h
  · simp only [bf, h, if_true]
    calc ∏ w, κ (Real.exp (y.1 w)) ≤ ∏ w, (Cκ * bmaj α 3 (y.1 w)) :=
          Finset.prod_le_prod (fun w _ => hκ0 _) fun w _ => hCκ (y.1 w)
      _ = (∏ w, bmaj α 3 (y.1 w)) * Cκ ^ Fintype.card (InfinitePlace F) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]; ring
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => bmaj_nonneg _ _ _) (hbf0 _)

variable (E : L3V.Env ι 𝔪) (g : AllowedGen ι 𝔪)
  (B : AddSubgroup (SFinCls 𝔪 k)) (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ)
  (hLf : ∀ a b, Lf (a + b) = Lf a * Lf b) (hLfn : ∀ a, ‖Lf a‖ = 1)
  (hLu : ∀ ε : SUnit 𝔪, Lmod Lf m (sEmb 𝔪 k ((ε : Fˣ) : F)) = 1)
  (κ : ℝ → ℝ) (hκm : Measurable κ) (hκ0 : ∀ t, 0 ≤ κ t)

/-- The summand of `Φ · Fw`. -/
def fwdTerm (𝔟 : Ideal (𝓞 F)) (p : RowClass 𝔪 × Gam 𝔪) (y : SModel 𝔪 k) : ℂ :=
  Phi B Lf m y * (coefF' g 𝔟 p.1 * fpF κ m (sEmb 𝔪 k (gamF p.2 * (rowElt g p.1 : F)) + y))

theorem sEmb_gam_mul (γ : Gam 𝔪) (z : RowClass 𝔪) :
    sEmb 𝔪 k (gamF γ * (rowElt g z : F)) = sEmb 𝔪 k (gamF γ) + sEmb 𝔪 k (rowElt g z : F) :=
  sEmb_mul (sUnit_ne_zero _) (rowElt_ne_zero g z)

include hLfn hκ0 E in
theorem norm_fwdTerm_le (𝔟 : Ideal (𝓞 F)) (p : RowClass 𝔪 × Gam 𝔪) (y : SModel 𝔪 k) :
    ‖fwdTerm g B Lf m κ 𝔟 p y‖ ≤ rho y *
      fpAbs κ (sEmb 𝔪 k (gamF p.2) + (sEmb 𝔪 k (rowElt g p.1 : F) + y)) := by
  rw [fwdTerm, norm_mul, norm_mul, norm_fpF κ m hκ0, sEmb_gam_mul, add_assoc]
  have h1 : ‖coefF' g 𝔟 p.1‖ ≤ 1 := norm_coefF_le E g 𝔟 p.1
  refine mul_le_mul (norm_Phi_le B Lf m hLfn y) ?_ (mul_nonneg (norm_nonneg _)
    (fpAbs_nonneg κ hκ0 _)) (rho_nonneg y)
  exact (mul_le_mul_of_nonneg_right h1 (fpAbs_nonneg κ hκ0 _)).trans_eq (one_mul _)

include hκm in
theorem measurable_fwdTerm (𝔟 : Ideal (𝓞 F)) (p : RowClass 𝔪 × Gam 𝔪) :
    Measurable (fwdTerm g B Lf m κ 𝔟 p) :=
  (measurable_Phi B Lf m).mul (measurable_const.mul
    ((measurable_fpF κ m hκm).comp (measurable_const_add _)))

include h𝔪 hLfn hκm hκ0 E in
/-- `Σ_{z,γ} ∫ ‖Φ · term‖` is finite. -/
theorem tsum_lintegral_fwdTerm_ne_top [Finite (SClass 𝔪)] {α : ℝ} (hα : 0 < α)
    (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N)))
    (𝔟 : Ideal (𝓞 F)) (a : ℝ) :
    ∑' p : RowClass 𝔪 × Gam 𝔪, ∫⁻ y, ‖fwdTerm g B Lf m κ 𝔟 p y‖ₑ ∂(shMeasure w₀ 𝔪 k a) ≠ ∞ := by
  obtain ⟨C, hC0, hC⟩ := lintegral_fpAbs_le h𝔪 w₀ (k := k) κ hκ0 hα hκb
  have hfp : Measurable (fpAbs (𝔪 := 𝔪) (k := k) κ) := measurable_fpAbs κ hκm
  have hz : ∀ z : RowClass 𝔪, ∑' γ : Gam 𝔪, ∫⁻ y, ‖fwdTerm g B Lf m κ 𝔟 (z, γ) y‖ₑ
      ∂(shMeasure w₀ 𝔪 k a) ≤
      ENNReal.ofReal (C * Real.exp (-(2 * a)) * (Ideal.absNorm z.1.1 : ℝ) ^ (-(2 : ℝ))) := by
    intro z
    set X := sEmb 𝔪 k (rowElt g z : F)
    have h1 : ∀ γ : Gam 𝔪, ∫⁻ y, ‖fwdTerm g B Lf m κ 𝔟 (z, γ) y‖ₑ ∂(shMeasure w₀ 𝔪 k a) ≤
        ∫⁻ y, ENNReal.ofReal (rho y) * ENNReal.ofReal (fpAbs κ (X + (sEmb 𝔪 k
          (((γ : SUnit 𝔪) : Fˣ) : F) + y))) ∂(shMeasure w₀ 𝔪 k a) := by
      intro γ
      refine lintegral_mono fun y => ?_
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (rho_nonneg y),
        show X + (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y) =
          sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + (X + y) by abel]
      exact ENNReal.ofReal_le_ofReal (norm_fwdTerm_le E g B Lf m hLfn κ hκ0 𝔟 (z, γ) y)
    refine (ENNReal.tsum_le_tsum h1).trans ?_
    rw [lintegral_unfold w₀ h𝔪 a (fun y => ENNReal.ofReal (fpAbs κ (X + y)))
      (ENNReal.measurable_ofReal.comp (hfp.comp (measurable_const_add X)))]
    have h2 := lintegral_add w₀ h𝔪 a X (fun y => ENNReal.ofReal (fpAbs κ y))
    rw [show (fun y => ENNReal.ofReal (fpAbs κ (X + y))) =
      fun y => ENNReal.ofReal (fpAbs κ (y + X)) by funext y; rw [add_comm], h2]
    refine (hC _).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [lnorm_rowElt h𝔪 g z, mul_add, neg_add, Real.exp_add, Real.rpow_def_of_pos
      (absNorm_pos_of_ext z.1.2)]
    have : -(2 * Real.log (Ideal.absNorm z.1.1 : ℝ)) = Real.log (Ideal.absNorm z.1.1 : ℝ) *
      (-(2 : ℝ)) := by ring
    rw [this]; ring
  rw [ENNReal.tsum_prod (f := fun (z : RowClass 𝔪) (γ : Gam 𝔪) =>
    ∫⁻ y, ‖fwdTerm g B Lf m κ 𝔟 (z, γ) y‖ₑ ∂(shMeasure w₀ 𝔪 k a))]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hz)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (summable_rowClass_rpow.mul_left _)]
  exact ENNReal.ofReal_ne_top

include h𝔪 hLf hLfn hLu hκm hκ0 E in
theorem fwd_integral [Finite (SClass 𝔪)] {α : ℝ} (hα : 0 < α)
    (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N)))
    (𝔟 : Ideal (𝓞 F)) (a : ℝ) :
    Integrable (fun y => Phi B Lf m y * Fw g κ m 𝔟 y) (shMeasure w₀ 𝔪 k a) ∧
    ∫ y, Phi B Lf m y * Fw g κ m 𝔟 y ∂(shMeasure w₀ 𝔪 k a) =
      ∑' z : RowClass 𝔪, coefF' g 𝔟 z * Bind B (clsF (rowElt g z : F)) *
        Lmod Lf m (sEmb 𝔪 k (rowElt g z : F)) *
        ((∫ y, fpAbs κ y ∂(shMeasure w₀ 𝔪 k (a + lnorm (sEmb 𝔪 k (rowElt g z : F)))) : ℝ) : ℂ) := by
  have hfin := tsum_lintegral_fwdTerm_ne_top h𝔪 w₀ E g B Lf m hLfn κ hκm hκ0 hα hκb 𝔟 a
  obtain ⟨hint, heq, hsum⟩ := tsum_integral_of_lintegral
    (fun p => measurable_fwdTerm g B Lf m κ hκm 𝔟 p) hfin
  have hfun : (fun y => Phi B Lf m y * Fw g κ m 𝔟 y) =
      fun y => ∑' p, fwdTerm g B Lf m κ 𝔟 p y := by
    funext y; rw [Fw, ← tsum_mul_left]; rfl
  rw [hfun]
  refine ⟨hint, ?_⟩
  rw [heq, hsum.tsum_prod' fun z => hsum.prod_factor z]
  congr 1; funext z
  set X := sEmb 𝔪 k (rowElt g z : F)
  have hfp : Measurable (fpF (𝔪 := 𝔪) (k := k) κ m) := measurable_fpF κ m hκm
  set H : SModel 𝔪 k → ℂ := fun y => psi B Lf m y * fpF κ m (X + y)
  have hH : Measurable H := (measurable_psi B Lf m).mul (hfp.comp (measurable_const_add X))
  have hterm : ∀ γ : Gam 𝔪, ∫ y, fwdTerm g B Lf m κ 𝔟 (z, γ) y ∂(shMeasure w₀ 𝔪 k a) =
      coefF' g 𝔟 z * ∫ y, (rho y : ℂ) * H (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y)
        ∂(shMeasure w₀ 𝔪 k a) := by
    intro γ
    rw [← integral_const_mul]
    congr 1; funext y
    simp only [fwdTerm, H, Phi]
    rw [sEmb_gam_mul, show (((γ : SUnit 𝔪) : Fˣ) : F) = gamF γ from rfl,
      psi_gam_add B Lf m hLf hLu γ y]
    rw [show sEmb 𝔪 k (gamF γ) + X + y = X + (sEmb 𝔪 k (gamF γ) + y) by abel]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hHfin : ∫⁻ y, ‖H y‖ₑ ∂(shMeasure w₀ 𝔪 k a) ≠ ∞ := by
    obtain ⟨C, _, hC⟩ := lintegral_fpAbs_le h𝔪 w₀ (k := k) κ hκ0 hα hκb
    have hle : ∫⁻ y, ‖H y‖ₑ ∂(shMeasure w₀ 𝔪 k a) ≤
        ∫⁻ y, ENNReal.ofReal (fpAbs κ (y + X)) ∂(shMeasure w₀ 𝔪 k a) := by
      refine lintegral_mono fun y => ?_
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [H]
      rw [norm_mul, norm_fpF κ m hκ0, add_comm X y]
      exact (mul_le_of_le_one_left (fpAbs_nonneg κ hκ0 _) (norm_psi_le B Lf m hLfn y))
    have h2 := lintegral_add w₀ h𝔪 a X (fun y => ENNReal.ofReal (fpAbs κ y))
    rw [h2] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle.trans (hC _))
  rw [integral_unfold w₀ h𝔪 a H hH hHfin]
  -- the change of variables `y ↦ y − X`
  have h3 := integral_add w₀ h𝔪 a X (fun y => psi B Lf m (y - X) * fpF κ m y)
  simp only [add_sub_cancel_right] at h3
  have h4 : ∫ y, H y ∂(shMeasure w₀ 𝔪 k a) =
      ∫ y, psi B Lf m (y - X) * fpF κ m y ∂(shMeasure w₀ 𝔪 k (a + lnorm X)) := by
    rw [← h3]; congr 1; funext y; simp only [H]; rw [add_comm X y]
  have h5 : ∀ y : SModel 𝔪 k, psi B Lf m (y - X) * fpF κ m y =
      Bind B (clsF (rowElt g z : F)) * Lmod Lf m X * (fpAbs κ y : ℂ) := by
    intro y
    by_cases hy : y.2.2 = 0
    · have hcl : (QuotientAddGroup.mk (y - X).2.2 : SFinCls 𝔪 k) = -clsF (rowElt g z : F) := by
        rw [Prod.snd_sub, Prod.snd_sub, hy, zero_sub, QuotientAddGroup.mk_neg]; rfl
      rw [psi, hcl, Bind_neg, Lmod_sub Lf m hLf hLfn, mul_inv, inv_inv,
        ← Lmod_inv_mul_fpF κ m Lf hLf hLfn y]
      ring
    · have h0 : fpF κ m y = 0 := by simp [fpF, hy]
      have h0' : fpAbs κ y = 0 := by simp [fpAbs, hy]
      rw [h0, h0']; simp
  rw [h4, funext h5, integral_const_mul, integral_complex_ofReal]
  ring

end Main

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3X_Rev: the reflected orbit unfolding

`∫_{X_l} Φ(y) · (reflected expansion)(y) = Σ_z E_z L(ν_z)⁻¹ H_{[ν_z]}(|ν_z|_S / l)`: the sum over
`γ ∈ Γ` is collapsed by the partition of unity `ρ`, then `y ↦ ν/y` maps the sheet `X_l` to
`X_{|ν|/l}`. Absolute convergence comes from the product majorant of the reflected `S`-function
and `Σ N𝔷^{-2} < ∞`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical ENNReal

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

instance instCountableIdealRev : Countable (Ideal (𝓞 F)) :=
  (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).symm.injective.countable

/-- The sheet profile `H_{υ,c}(u)`. -/
noncomputable def Hprof (w₀ : InfinitePlace F) (B : AddSubgroup (SFinCls 𝔪 k)) (Lf : SFin 𝔪 k → ℂ)
    (m : InfinitePlace F → ℤ) (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (c : SFinCls 𝔪 k) (u : ℝ) : ℂ :=
  ∫ y, Bind B (c - QuotientAddGroup.mk y.2.2) * Lmod Lf m y * Fm c y ∂(shMeasure w₀ 𝔪 k (Real.log u))

theorem span_rowElt_R (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    Ideal.span {rowElt g z} = z.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [rowElt, ← g.span_gen _ z.1.2]
  exact Ideal.span_singleton_mul_left_unit (Units.isUnit _) _

theorem measurable_sub_left' (d : SModel 𝔪 k) : Measurable fun y : SModel 𝔪 k => d - y := by
  simp_rw [sub_eq_add_neg]
  exact (measurable_const_add d).comp measurable_neg

section Main

variable [Fintype (L3P.SP 𝔪)]

theorem rowElt_ne_zero_R (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) : (rowElt g z : F) ≠ 0 :=
  L3P.ne_zero_of_span_eq z.1.2 (span_rowElt_R g z)

theorem gen_ne_zero' (g : AllowedGen ι 𝔪) (r : RowClass 𝔪) : (g.gen r.1.1 : F) ≠ 0 :=
  L3P.ne_zero_of_span_eq r.1.2 (g.span_gen _ r.1.2)

theorem nu_ne_zero (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) : L3V.nu g r z ≠ 0 :=
  div_ne_zero (rowElt_ne_zero_R g z) (pow_ne_zero 2 (gen_ne_zero' g r))

theorem lnorm_nu (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) :
    lnorm (sEmb 𝔪 k (L3V.nu g r z)) =
      Real.log (Ideal.absNorm z.1.1 : ℝ) - 2 * Real.log (Ideal.absNorm r.1.1 : ℝ) := by
  rw [L3V.nu, sEmb_div (rowElt_ne_zero_R g z) (pow_ne_zero 2 (gen_ne_zero' g r)),
    sEmb_pow (gen_ne_zero' g r), lnorm_sub h𝔪, two_nsmul, lnorm_add h𝔪,
    lnorm_sEmb_gen h𝔪 z.1.2 (span_rowElt_R g z), lnorm_sEmb_gen h𝔪 r.1.2 (g.span_gen _ r.1.2)]
  ring

theorem absNorm_pos' {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) : (0 : ℝ) < Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact hI.1
  exact_mod_cast Nat.pos_of_ne_zero this

theorem summable_rowClass_rpow_R [Finite (SClass 𝔪)] :
    Summable fun z : RowClass 𝔪 => ((Ideal.absNorm z.1.1 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hs := (T12B.summable_absNorm_rpow (F := F) (σ := 2) (by norm_num)).comp_injective
    (Subtype.val_injective (p := fun I : Ideal (𝓞 F) => IsExterior 𝔪 I))
  have : Fintype (SClass 𝔪) := Fintype.ofFinite _
  refine (summable_prod_of_nonneg (fun z => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact hs.mul_left _

theorem rev_integral [Finite (SClass 𝔪)] (h𝔪 : 𝔪 ≠ ⊥) (w₀ : InfinitePlace F)
    (g : AllowedGen ι 𝔪)
    (B : AddSubgroup (SFinCls 𝔪 k)) (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ)
    (hLf : ∀ a b, Lf (a + b) = Lf a * Lf b) (hLfn : ∀ a, ‖Lf a‖ = 1)
    (hLu : ∀ ε : SUnit 𝔪, Lmod Lf m (sEmb 𝔪 k ((ε : Fˣ) : F)) = 1)
    (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (hFm : ∀ c, Measurable (Fm c)) {α : ℝ} (hα : 0 < α)
    (bf : SFin 𝔪 k → ℝ) (hbf0 : ∀ y, 0 ≤ bf y)
    (hbf : ∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ))
    (hFb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ c y, ‖Fm c y‖ ≤ C * (∏ w, bmaj α N (y.1 w)) * bf y.2.2)
    (r : RowClass 𝔪) (a : ℝ) :
    Integrable (fun y => Phi B Lf m y * Rf g Fm r y) (shMeasure w₀ 𝔪 k a) ∧
    ∫ y, Phi B Lf m y * Rf g Fm r y ∂(shMeasure w₀ 𝔪 k a) =
      ∑' z : RowClass 𝔪, L3V.Eprod g r z * (Lmod Lf m (sEmb 𝔪 k (L3V.nu g r z)))⁻¹ *
        Hprof w₀ B Lf m Fm (clsF (L3V.nu g r z)) (Real.exp (lnorm (sEmb 𝔪 k (L3V.nu g r z)) - a)) := by
  set X : RowClass 𝔪 → SModel 𝔪 k := fun z => sEmb 𝔪 k (L3V.nu g r z) with hXdef
  set c : RowClass 𝔪 → SFinCls 𝔪 k := fun z => clsF (L3V.nu g r z) with hcdef
  set E : RowClass 𝔪 → ℂ := fun z => L3V.Eprod g r z with hEdef
  set μ := shMeasure w₀ 𝔪 k a
  set A : RowClass 𝔪 × Gam 𝔪 → SModel 𝔪 k → ℂ := fun p y =>
    Phi B Lf m y * (E p.1 * Fm (c p.1) (sEmb 𝔪 k (gamF p.2 * L3V.nu g r p.1) - y)) with hAdef
  have hA : ∀ y, Phi B Lf m y * Rf g Fm r y = ∑' p, A p y := by
    intro y; rw [Rf, ← tsum_mul_left]
  have hsplit : ∀ (γ : Gam 𝔪) (z : RowClass 𝔪),
      sEmb 𝔪 k (gamF γ * L3V.nu g r z) = sEmb 𝔪 k (gamF γ) + X z := fun γ z =>
    sEmb_mul (sUnit_ne_zero _) (nu_ne_zero g r z)
  have hAm : ∀ p, Measurable (A p) := fun p =>
    (measurable_Phi B Lf m).mul (measurable_const.mul ((hFm _).comp (measurable_sub_left' _)))
  -- the constants
  obtain ⟨CE, hCE0, hCE⟩ := exists_norm_Eprod_le g r
  obtain ⟨C3, hC3⟩ := hFb 3 (by norm_num)
  set D := max C3 0
  obtain ⟨C', hC'0, hC'⟩ := lintegral_majorant_le w₀ h𝔪 (α := α) (N := 3) (σ := 2)
    (by linarith) (by norm_num) bf hbf0 (hbf 2 (by linarith))
  -- the pointwise bound on the reflected function
  have hFm_le : ∀ c' y, ‖Fm c' y‖ₑ ≤
      ENNReal.ofReal D * ENNReal.ofReal ((∏ w, bmaj α 3 (y.1 w)) * bf y.2.2) := by
    intro c' y
    rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hC3 c' y).trans ?_)
    have h0 : 0 ≤ (∏ w, bmaj α 3 (y.1 w)) * bf y.2.2 :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => bmaj_nonneg _ _ _) (hbf0 _)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) h0
  have hFm_int : ∀ (z : RowClass 𝔪) (b : ℝ), ∫⁻ y, ‖E z‖ₑ * ‖Fm (c z) y‖ₑ ∂(shMeasure w₀ 𝔪 k b) ≤
      ENNReal.ofReal (CE * D) * ENNReal.ofReal (C' * Real.exp (-(2 * b))) := by
    intro z b
    calc ∫⁻ y, ‖E z‖ₑ * ‖Fm (c z) y‖ₑ ∂(shMeasure w₀ 𝔪 k b)
        ≤ ∫⁻ y, ENNReal.ofReal (CE * D) *
            ENNReal.ofReal ((∏ w, bmaj α 3 (y.1 w)) * bf y.2.2) ∂(shMeasure w₀ 𝔪 k b) := by
          refine lintegral_mono fun y => ?_
          rw [ENNReal.ofReal_mul hCE0, mul_assoc]
          refine mul_le_mul' ?_ (hFm_le _ y)
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hCE z)
      _ = ENNReal.ofReal (CE * D) * ∫⁻ y, ENNReal.ofReal ((∏ w, bmaj α 3 (y.1 w)) * bf y.2.2)
            ∂(shMeasure w₀ 𝔪 k b) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact hC' b
  -- the fibre over `z`
  have hfib : ∀ z : RowClass 𝔪, ∑' γ : Gam 𝔪, ∫⁻ y, ‖A (z, γ) y‖ₑ ∂μ ≤
      ∫⁻ y, ‖E z‖ₑ * ‖Fm (c z) y‖ₑ ∂(shMeasure w₀ 𝔪 k (lnorm (X z) - a)) := by
    intro z
    rw [← (Equiv.inv (Gam 𝔪)).tsum_eq]
    set H : SModel 𝔪 k → ℝ≥0∞ := fun y => ‖E z‖ₑ * ‖Fm (c z) (X z - y)‖ₑ
    have hH : Measurable H := measurable_const.mul ((hFm _).comp (measurable_sub_left' _)).enorm
    calc ∑' γ : Gam 𝔪, ∫⁻ y, ‖A (z, (Equiv.inv (Gam 𝔪)) γ) y‖ₑ ∂μ
        ≤ ∑' γ : Gam 𝔪, ∫⁻ y, ENNReal.ofReal (rho y) *
            H (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y) ∂μ := by
          refine ENNReal.tsum_le_tsum fun γ => lintegral_mono fun y => ?_
          simp only [hAdef, Equiv.inv_apply, H]
          rw [hsplit, show gamF γ⁻¹ = (((γ⁻¹ : Gam 𝔪) : SUnit 𝔪) : Fˣ) from rfl,
            sEmb_gam_inv, enorm_mul, enorm_mul]
          rw [show -sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + X z - y =
            X z - (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y) by abel]
          refine mul_le_mul' ?_ le_rfl
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_Phi_le B Lf m hLfn y)
      _ = ∫⁻ y, H y ∂μ := lintegral_unfold w₀ h𝔪 a H hH
      _ = _ := lintegral_sub_left w₀ h𝔪 a (X z) (fun y => ‖E z‖ₑ * ‖Fm (c z) y‖ₑ)
  -- the total
  set f : RowClass 𝔪 → ℝ := fun z => CE * D * (C' * Real.exp (-(2 * (lnorm (X z) - a))))
  have hf_eq : ∀ z, f z = CE * D * C' * Real.exp (2 * a) * (Ideal.absNorm r.1.1 : ℝ) ^ (4 : ℕ) *
      ((Ideal.absNorm z.1.1 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro z
    simp only [f, hXdef]
    rw [lnorm_nu h𝔪 g r z, Real.rpow_def_of_pos (absNorm_pos' z.1.2)]
    have hr := absNorm_pos' r.1.2
    rw [show (Ideal.absNorm r.1.1 : ℝ) ^ (4 : ℕ) = Real.exp (4 * Real.log (Ideal.absNorm r.1.1 : ℝ))
      by rw [← Real.exp_log (pow_pos hr 4), Real.log_pow]; push_cast; ring_nf]
    rw [mul_assoc (CE * D * C'), mul_assoc (CE * D * C'), ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hf_sum : Summable f := by
    have := (summable_rowClass_rpow_R (𝔪 := 𝔪)).mul_left
      (CE * D * C' * Real.exp (2 * a) * (Ideal.absNorm r.1.1 : ℝ) ^ (4 : ℕ))
    exact this.congr fun z => (hf_eq z).symm
  have hf0 : ∀ z, 0 ≤ f z := fun z =>
    mul_nonneg (mul_nonneg hCE0 (le_max_right _ _)) (mul_nonneg hC'0 (Real.exp_pos _).le)
  have htot : ∑' p, ∫⁻ y, ‖A p y‖ₑ ∂μ ≠ ∞ := by
    rw [ENNReal.tsum_prod']
    refine ne_top_of_le_ne_top (b := ∑' z, ENNReal.ofReal (f z)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hf_sum]; exact ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun z => (hfib z).trans ((hFm_int z _).trans ?_)
      rw [← ENNReal.ofReal_mul (mul_nonneg hCE0 (le_max_right _ _))]
  obtain ⟨hInt, hEq, hSum⟩ := tsum_integral_of_lintegral hAm htot
  have hfun : (fun y => Phi B Lf m y * Rf g Fm r y) = fun y => ∑' p, A p y := funext hA
  refine ⟨hfun ▸ hInt, ?_⟩
  rw [hfun, hEq, hSum.tsum_prod]
  refine tsum_congr fun z => ?_
  rw [← (Equiv.inv (Gam 𝔪)).tsum_eq]
  set H : SModel 𝔪 k → ℂ := fun y => psi B Lf m y * (E z * Fm (c z) (X z - y))
  have hHm : Measurable H := (measurable_psi B Lf m).mul
    (measurable_const.mul ((hFm _).comp (measurable_sub_left' _)))
  have hHfin : ∫⁻ y, ‖H y‖ₑ ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ y, ‖E z‖ₑ * ‖Fm (c z) (X z - y)‖ₑ ∂μ) ?_ ?_
    · rw [lintegral_sub_left w₀ h𝔪 a (X z) (fun y => ‖E z‖ₑ * ‖Fm (c z) y‖ₑ)]
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (hFm_int z _)
    · refine lintegral_mono fun y => ?_
      simp only [H, enorm_mul]
      rw [← mul_assoc]
      refine mul_le_mul' ?_ le_rfl
      calc ‖psi B Lf m y‖ₑ * ‖E z‖ₑ ≤ 1 * ‖E z‖ₑ := by
            refine mul_le_mul' ?_ le_rfl
            rw [← ofReal_norm, ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (norm_psi_le B Lf m hLfn y)
        _ = ‖E z‖ₑ := one_mul _
  have h1 : ∀ γ : Gam 𝔪, ∫ y, A (z, (Equiv.inv (Gam 𝔪)) γ) y ∂μ =
      ∫ y, (rho y : ℂ) * H (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F) + y) ∂μ := by
    intro γ
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hAdef, Equiv.inv_apply, H, Phi]
    rw [hsplit, show gamF γ⁻¹ = (((γ⁻¹ : Gam 𝔪) : SUnit 𝔪) : Fˣ) from rfl, sEmb_gam_inv,
      show (sEmb 𝔪 k (((γ : SUnit 𝔪) : Fˣ) : F)) = sEmb 𝔪 k (gamF γ) from rfl,
      psi_gam_add B Lf m hLf hLu γ y,
      show -sEmb 𝔪 k (gamF γ) + X z - y = X z - (sEmb 𝔪 k (gamF γ) + y) by abel]
    ring
  simp_rw [h1]
  rw [integral_unfold w₀ h𝔪 a H hHm hHfin]
  set G : SModel 𝔪 k → ℂ := fun y' => psi B Lf m (X z - y') * (E z * Fm (c z) y')
  have hHG : H = fun y => G (X z - y) := by
    funext y; simp only [H, G, sub_sub_cancel]
  rw [hHG, integral_sub_left w₀ h𝔪 a (X z) G]
  have hG : G = fun y' => E z * (Lmod Lf m (X z))⁻¹ *
      (Bind B (c z - QuotientAddGroup.mk y'.2.2) * Lmod Lf m y' * Fm (c z) y') := by
    funext y'
    simp only [G, psi, Lmod_sub Lf m hLf hLfn, mul_inv, inv_inv, Prod.snd_sub,
      QuotientAddGroup.mk_sub]
    simp only [hcdef, clsF, hXdef]
    ring
  rw [hG, integral_const_mul, Hprof, Real.log_exp]

end Main

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3X_H: the sheet profiles are `C²` with two-ended bounds (Lemma 5.4)

For a family `G i` on `SModel 𝔪 k` that is `C²` in the `w₀`-radial direction with derivatives
dominated by `C ∏_w min(e^{α x_w}, e^{-N x_w}) · bf(y_f)` (for every `N`, with `C` uniform in `i`),
the sheet profile `t ↦ ∫ G i dμ_t` is `C²` and its derivatives of order `≤ 2` are
`≤ C min(e^{(α/2) t}, e^{-N t})`, uniformly in `i`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory Filter Topology

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

variable (w₀ : InfinitePlace F)

/-- The radial shift at `w₀`. -/
abbrev rsh (𝔪 : Ideal (𝓞 F)) (k : ℕ) (s : ℝ) : SModel 𝔪 k := ((Pi.single w₀ s, 0, 0) : SModel 𝔪 k)

theorem rsh_add (s t : ℝ) : rsh w₀ 𝔪 k (s + t) = rsh w₀ 𝔪 k t + rsh w₀ 𝔪 k s := by
  simp only [rsh, Prod.mk_add_mk, add_zero, Pi.single_add]
  exact Prod.ext (add_comm _ _) rfl

theorem slice_eq_add (t : ℝ) (p : Base w₀ 𝔪 k) :
    slice w₀ t p = slice w₀ 0 p + rsh w₀ 𝔪 k t := by
  simpa using slice_add_single w₀ 0 t p

/-- The majorant on `SModel`. -/
def majM (α N : ℝ) (y : SModel 𝔪 k) : ℝ := ∏ w, bmaj α N (y.1 w)

theorem majM_nonneg (α N : ℝ) (y : SModel 𝔪 k) : 0 ≤ majM α N y :=
  Finset.prod_nonneg fun _ _ => bmaj_nonneg _ _ _

theorem majM_add_rsh {α N : ℝ} (hα : 0 ≤ α) (hN : 0 ≤ N) (y : SModel 𝔪 k) (δ : ℝ) :
    majM α N (y + rsh w₀ 𝔪 k δ) ≤ Real.exp ((α + N) * |δ|) * majM α N y := by
  unfold majM
  rw [prod_eq_mul_prod_Wo w₀ (fun w => (y + rsh w₀ 𝔪 k δ).1 w) (bmaj α N),
    prod_eq_mul_prod_Wo w₀ (fun w => y.1 w) (bmaj α N)]
  have h1 : (y + rsh w₀ 𝔪 k δ).1 w₀ = y.1 w₀ + δ := by simp [rsh]
  have h2 : ∀ w : Wo w₀, (y + rsh w₀ 𝔪 k δ).1 w = y.1 w := fun w => by
    simp [rsh, w.2]
  simp only [h1, h2]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (bmaj_add_le hα hN _ _)
    (Finset.prod_nonneg fun _ _ => bmaj_nonneg _ _ _)

theorem integrable_majM (h𝔪 : 𝔪 ≠ ⊥) {α N σ : ℝ} (hσ1 : -α < σ) (hσ2 : σ < N)
    (bf : SFin 𝔪 k → ℝ) (hbf0 : ∀ y, 0 ≤ bf y)
    (hbf : Summable (fun y => bf y * (SFin.norm y) ^ σ)) (a : ℝ) :
    Integrable (fun p => majM α N (slice w₀ a p) * bf p.1) (baseMeasure w₀ 𝔪 k) := by
  obtain ⟨C, _, hC⟩ := lintegral_majorant_base_le w₀ h𝔪 hσ1 hσ2 bf hbf0 hbf
  have hm : Measurable fun p : Base w₀ 𝔪 k => majM α N (slice w₀ a p) * bf p.1 :=
    (measurable_majorant (𝔪 := 𝔪) (k := k) α N bf).comp (measurable_slice w₀ a)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ p : Base w₀ 𝔪 k, ‖majM α N (slice w₀ a p) * bf p.1‖ₑ =
      ENNReal.ofReal ((∏ w, bmaj α N ((slice w₀ a p).1 w)) * bf (slice w₀ a p).2.2) := by
    intro p
    rw [Real.enorm_eq_ofReal (mul_nonneg (majM_nonneg _ _ _) (hbf0 _))]
    rfl
  simp_rw [this]
  exact (hC a).trans_lt ENNReal.ofReal_lt_top

theorem integral_majM_le (h𝔪 : 𝔪 ≠ ⊥) {α N σ : ℝ} (hσ1 : -α < σ) (hσ2 : σ < N)
    (bf : SFin 𝔪 k → ℝ) (hbf0 : ∀ y, 0 ≤ bf y)
    (hbf : Summable (fun y => bf y * (SFin.norm y) ^ σ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ,
      ∫ p, majM α N (slice w₀ a p) * bf p.1 ∂(baseMeasure w₀ 𝔪 k) ≤
        C * Real.exp (-(σ * a)) := by
  obtain ⟨C, hC0, hC⟩ := lintegral_majorant_base_le w₀ h𝔪 hσ1 hσ2 bf hbf0 hbf
  refine ⟨C, hC0, fun a => ?_⟩
  have hm : Measurable fun p : Base w₀ 𝔪 k => majM α N (slice w₀ a p) * bf p.1 :=
    (measurable_majorant (𝔪 := 𝔪) (k := k) α N bf).comp (measurable_slice w₀ a)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun p => mul_nonneg (majM_nonneg _ _ _) (hbf0 _))
    hm.aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC a)
  rw [ENNReal.toReal_ofReal (mul_nonneg hC0 (Real.exp_pos _).le)] at h
  exact h

/-- Measurability of a derivative in a parameter, via difference quotients. -/
theorem measurable_deriv_param {α : Type*} [MeasurableSpace α] {f : α → ℝ → ℂ} (t : ℝ)
    (hf : ∀ s, Measurable fun p => f p s) (hd : ∀ p, DifferentiableAt ℝ (f p) t) :
    Measurable fun p => deriv (f p) t := by
  set u : ℕ → ℝ := fun n => t + 1 / ((n : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝[≠] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [u] using (tendsto_const_nhds (x := t)).add this
    · simp only [u, Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
      positivity
  refine measurable_of_tendsto_metrizable (f := fun n p => slope (f p) t (u n)) (fun n => ?_) ?_
  · simp only [slope_def_module]
    exact ((hf _).sub (hf _)).const_smul _
  · refine tendsto_pi_nhds.2 fun p => ?_
    exact ((hasDerivAt_iff_tendsto_slope.1 (hd p).hasDerivAt).comp hu)

theorem sheet_profile (h𝔪 : 𝔪 ≠ ⊥) {ι : Type*} (G : ι → SModel 𝔪 k → ℂ) {α : ℝ} (hα : 0 < α)
    (bf : SFin 𝔪 k → ℝ) (hbf0 : ∀ y, 0 ≤ bf y)
    (hbf : ∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ))
    (hGm : ∀ i, Measurable (G i))
    (hG2 : ∀ i y, ContDiff ℝ 2 (fun s : ℝ => G i (y + ((Pi.single w₀ s, 0, 0) : SModel 𝔪 k))))
    (hGb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ i y, ∀ j : ℕ, j ≤ 2 →
      ‖iteratedDeriv j (fun s : ℝ => G i (y + ((Pi.single w₀ s, 0, 0) : SModel 𝔪 k))) 0‖ ≤
        C * (∏ w, min (Real.exp (α * y.1 w)) (Real.exp (-(N * y.1 w)))) * bf y.2.2) :
    (∀ i, ContDiff ℝ 2 (fun t => ∫ y, G i y ∂(shMeasure w₀ 𝔪 k t))) ∧
    ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ i, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
      ‖iteratedDeriv j (fun t => ∫ y, G i y ∂(shMeasure w₀ 𝔪 k t)) t‖ ≤
        C * min (Real.exp (α / 2 * t)) (Real.exp (-(N * t))) := by
  set μ := baseMeasure w₀ 𝔪 k
  -- the pointwise functions
  set g : ι → Base w₀ 𝔪 k → ℝ → ℂ := fun i p t => G i (slice w₀ 0 p + rsh w₀ 𝔪 k t)
  have hgC : ∀ i p, ContDiff ℝ 2 (g i p) := fun i p => hG2 i _
  have hg1 : ∀ i p, Differentiable ℝ (g i p) := fun i p =>
    (hgC i p).differentiable (by norm_num)
  have hgd : ∀ i p, ContDiff ℝ 1 (deriv (g i p)) := fun i p => by
    have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) (g i p) := by
      rw [show (1 + 1 : WithTop ℕ∞) = 2 by norm_num]; exact hgC i p
    exact (contDiff_succ_iff_deriv.1 h2).2.2
  have hg2 : ∀ i p, Differentiable ℝ (deriv (g i p)) := fun i p =>
    (contDiff_one_iff_deriv.1 (hgd i p)).1
  have hg2c : ∀ i p, Continuous (deriv (deriv (g i p))) := fun i p =>
    (contDiff_one_iff_deriv.1 (hgd i p)).2
  have hgm : ∀ i s, Measurable fun p => g i p s := fun i s =>
    (hGm i).comp ((measurable_slice w₀ 0).add_const _)
  have hd1m : ∀ i s, Measurable fun p => deriv (g i p) s := fun i s =>
    measurable_deriv_param s (hgm i) fun p => (hg1 i p) s
  have hd2m : ∀ i s, Measurable fun p => deriv (deriv (g i p)) s := fun i s =>
    measurable_deriv_param s (hd1m i) fun p => (hg2 i p) s
  -- iterated derivatives of `g` and the pointwise bound
  have hit : ∀ i p (j : ℕ) (t : ℝ), iteratedDeriv j (g i p) t =
      iteratedDeriv j (fun s : ℝ => G i (slice w₀ t p + ((Pi.single w₀ s, 0, 0) : SModel 𝔪 k))) 0 := by
    intro i p j t
    have h := congrFun (iteratedDeriv_comp_add_const j (g i p) t) 0
    rw [zero_add] at h
    rw [← h]
    congr 1
    funext s
    simp only [g, rsh_add, slice_eq_add w₀ t, add_assoc]
  have hbd : ∀ N : ℝ, 0 < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ i p (j : ℕ), j ≤ 2 → ∀ t,
      ‖iteratedDeriv j (g i p) t‖ ≤ C * (majM α N (slice w₀ t p) * bf p.1) := by
    intro N hN
    obtain ⟨C, hC⟩ := hGb N hN
    refine ⟨max C 0, le_max_right _ _, fun i p j hj t => ?_⟩
    rw [hit]
    refine (hC i _ j hj).trans ?_
    have : (slice w₀ t p).2.2 = p.1 := rfl
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (majM_nonneg _ _ _) (hbf0 _))
  have hit0 : ∀ (f : ℝ → ℂ), iteratedDeriv 0 f = f := fun f => iteratedDeriv_zero
  have hit1 : ∀ (f : ℝ → ℂ), iteratedDeriv 1 f = deriv f := fun f => iteratedDeriv_one
  have hit2 : ∀ (f : ℝ → ℂ), iteratedDeriv 2 f = deriv (deriv f) := fun f => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- domination near `t₀` (with `N = 1`, `σ = 0`)
  obtain ⟨C₁, hC₁0, hC₁⟩ := hbd 1 one_pos
  have hint₁ : ∀ a, Integrable (fun p => majM α 1 (slice w₀ a p) * bf p.1) μ := fun a =>
    integrable_majM w₀ h𝔪 (α := α) (σ := 0) (by linarith) (by norm_num) bf hbf0 (hbf 0 (by linarith)) a
  set B : ℝ → Base w₀ 𝔪 k → ℝ := fun t₀ p =>
    C₁ * Real.exp (α + 1) * (majM α 1 (slice w₀ t₀ p) * bf p.1)
  have hBi : ∀ t₀, Integrable (B t₀) μ := fun t₀ =>
    (hint₁ t₀).const_mul (C₁ * Real.exp (α + 1))
  have hloc : ∀ i p (j : ℕ), j ≤ 2 → ∀ t₀ t, t ∈ Metric.ball t₀ 1 →
      ‖iteratedDeriv j (g i p) t‖ ≤ B t₀ p := by
    intro i p j hj t₀ t ht
    refine (hC₁ i p j hj t).trans ?_
    have hδ : |t - t₀| < 1 := by rw [Metric.mem_ball, Real.dist_eq] at ht; exact ht
    have hs : slice w₀ t p = slice w₀ t₀ p + rsh w₀ 𝔪 k (t - t₀) := by
      have := slice_add_single w₀ t₀ (t - t₀) p
      rw [add_sub_cancel] at this
      exact this
    have hm := majM_add_rsh w₀ hα.le zero_le_one (slice w₀ t₀ p) (t - t₀)
    rw [← hs] at hm
    have he : Real.exp ((α + 1) * |t - t₀|) ≤ Real.exp (α + 1) :=
      Real.exp_le_exp.2 (by nlinarith [abs_nonneg (t - t₀)])
    simp only [B]
    have hmm : majM α 1 (slice w₀ t p) ≤ Real.exp (α + 1) * majM α 1 (slice w₀ t₀ p) :=
      hm.trans (mul_le_mul_of_nonneg_right he (majM_nonneg _ _ _))
    calc C₁ * (majM α 1 (slice w₀ t p) * bf p.1)
        ≤ C₁ * ((Real.exp (α + 1) * majM α 1 (slice w₀ t₀ p)) * bf p.1) := by
          gcongr
          exact hbf0 _
      _ = _ := by ring
  -- the integral functions
  set Φ0 : ι → ℝ → ℂ := fun i t => ∫ p, g i p t ∂μ
  set Φ1 : ι → ℝ → ℂ := fun i t => ∫ p, deriv (g i p) t ∂μ
  set Φ2 : ι → ℝ → ℂ := fun i t => ∫ p, deriv (deriv (g i p)) t ∂μ
  have hΦeq : ∀ i, (fun t => ∫ y, G i y ∂(shMeasure w₀ 𝔪 k t)) = Φ0 i := by
    intro i; funext t
    rw [shMeasure, integral_map (measurable_slice w₀ t).aemeasurable
      (hGm i).aestronglyMeasurable]
    simp only [Φ0, g]
    exact integral_congr_ae (Eventually.of_forall fun p => congrArg (G i) (slice_eq_add w₀ t p))
  have hint0 : ∀ i t, Integrable (fun p => g i p t) μ := fun i t =>
    Integrable.mono' (hBi t) (hgm i t).aestronglyMeasurable (Eventually.of_forall fun p => by
      have := hloc i p 0 (by norm_num) t t (Metric.mem_ball_self one_pos)
      rwa [hit0] at this)
  have hint1 : ∀ i t, Integrable (fun p => deriv (g i p) t) μ := fun i t =>
    Integrable.mono' (hBi t) (hd1m i t).aestronglyMeasurable (Eventually.of_forall fun p => by
      have := hloc i p 1 (by norm_num) t t (Metric.mem_ball_self one_pos)
      rwa [hit1] at this)
  have hD0 : ∀ i t₀, HasDerivAt (Φ0 i) (Φ1 i t₀) t₀ := by
    intro i t₀
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ one_pos)
      (Eventually.of_forall fun t => (hgm i t).aestronglyMeasurable) (hint0 i t₀)
      (hd1m i t₀).aestronglyMeasurable
      (Eventually.of_forall fun p t ht => by
        have := hloc i p 1 (by norm_num) t₀ t ht; rwa [hit1] at this)
      (hBi t₀) (Eventually.of_forall fun p t _ => ((hg1 i p) t).hasDerivAt)).2
  have hD1 : ∀ i t₀, HasDerivAt (Φ1 i) (Φ2 i t₀) t₀ := by
    intro i t₀
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ one_pos)
      (Eventually.of_forall fun t => (hd1m i t).aestronglyMeasurable) (hint1 i t₀)
      (hd2m i t₀).aestronglyMeasurable
      (Eventually.of_forall fun p t ht => by
        have := hloc i p 2 (by norm_num) t₀ t ht; rwa [hit2] at this)
      (hBi t₀) (Eventually.of_forall fun p t _ => ((hg2 i p) t).hasDerivAt)).2
  have hC2 : ∀ i, Continuous (Φ2 i) := by
    intro i
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    refine continuousAt_of_dominated (bound := B t₀)
      (Eventually.of_forall fun t => (hd2m i t).aestronglyMeasurable) ?_ (hBi t₀)
      (Eventually.of_forall fun p => (hg2c i p).continuousAt)
    filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with t ht
    exact Eventually.of_forall fun p => by
      have := hloc i p 2 (by norm_num) t₀ t ht; rwa [hit2] at this
  have hdΦ0 : ∀ i, deriv (Φ0 i) = Φ1 i := fun i => funext fun t => (hD0 i t).deriv
  have hdΦ1 : ∀ i, deriv (Φ1 i) = Φ2 i := fun i => funext fun t => (hD1 i t).deriv
  -- iterated derivatives of `Φ0`
  have hΦj : ∀ i (j : ℕ), j ≤ 2 → ∀ t,
      iteratedDeriv j (Φ0 i) t = ∫ p, iteratedDeriv j (g i p) t ∂μ := by
    intro i j hj t
    interval_cases j
    · simp only [hit0, Φ0]
    · simp only [hit1, hdΦ0, Φ1]
    · simp only [hit2, hdΦ0, hdΦ1, Φ2]
  refine ⟨fun i => ?_, fun N hN => ?_⟩
  · rw [hΦeq i]
    refine (contDiff_succ_iff_deriv (n := 1)).2 ⟨fun t => (hD0 i t).differentiableAt,
      by simp, ?_⟩
    rw [hdΦ0 i]
    refine contDiff_one_iff_deriv.2 ⟨fun t => (hD1 i t).differentiableAt, ?_⟩
    rw [hdΦ1 i]
    exact hC2 i
  · obtain ⟨C, hC0, hC⟩ := hbd (N + 1) (by linarith)
    obtain ⟨Ca, hCa0, hCa⟩ := integral_majM_le w₀ h𝔪 (α := α) (σ := -(α / 2)) (N := N + 1)
      (by linarith) (by linarith) bf hbf0 (hbf _ (by linarith))
    obtain ⟨Cb, hCb0, hCb⟩ := integral_majM_le w₀ h𝔪 (α := α) (σ := N) (N := N + 1)
      (by linarith) (by linarith) bf hbf0 (hbf _ (by linarith))
    refine ⟨C * max Ca Cb, fun i j hj t => ?_⟩
    rw [hΦeq i, hΦj i j hj t]
    have hintN : Integrable (fun p => majM α (N + 1) (slice w₀ t p) * bf p.1) μ :=
      integrable_majM w₀ h𝔪 (α := α) (σ := N) (by linarith) (by linarith) bf hbf0 (hbf _ (by linarith)) t
    have h1 : ‖∫ p, iteratedDeriv j (g i p) t ∂μ‖ ≤
        C * ∫ p, majM α (N + 1) (slice w₀ t p) * bf p.1 ∂μ := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hintN.const_mul C) (Eventually.of_forall fun p => ?_)
      exact hC i p j hj t
    have hKa : ∫ p, majM α (N + 1) (slice w₀ t p) * bf p.1 ∂μ ≤
        max Ca Cb * Real.exp (α / 2 * t) := by
      refine (hCa t).trans ?_
      rw [show -(-(α / 2) * t) = α / 2 * t by ring]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have hKb : ∫ p, majM α (N + 1) (slice w₀ t p) * bf p.1 ∂μ ≤
        max Ca Cb * Real.exp (-(N * t)) :=
      (hCb t).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    rcases min_choice (Real.exp (α / 2 * t)) (Real.exp (-(N * t))) with hm | hm
    · rw [hm]; exact hKa
    · rw [hm]; exact hKb

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3X_V: the radial profile `V` of (5.21) and its Mellin transform

* `Vprof w₀ 𝔪 k κ u`: the sheet integral over `X_u` of `1_{y_f = 0} ∏_w κ(|y_w|_w)`.
* `Vprof_eq`: `V(u) = (2π)^{|W|} ∫_{x' ∈ ℝ^{W∖w₀}} κ(e^{log u − Σx'}) ∏_{w'} κ(e^{x'_{w'}})`.
* `Vprof_mellin`: measurability and `V̂(s) = (2π)^{|W|} cκ^{|W|} (Aκ^{|W|})^s (Γ(s+5/6)Γ(s+7/6))^{|W|}`
  for `Re s > −5/6`, from `κ̂(s) = cκ Aκ^s Γ(s+5/6)Γ(s+7/6)` (Fubini; `κ ≥ 0`).
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The radial profile `V(u)` of (5.21): the sheet integral of `1_{y_f = 0} ∏_w κ(|y_w|_w)`. -/
noncomputable def Vprof (w₀ : InfinitePlace F) (𝔪 : Ideal (𝓞 F)) (k : ℕ) (κ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ y, (if y.2.2 = 0 then ∏ w, κ (Real.exp (y.1 w)) else 0) ∂(shMeasure w₀ 𝔪 k (Real.log u))

theorem prod_eq_mul_prod_Wo_V (w₀ : InfinitePlace F) {M : Type*} [CommMonoid M]
    (f : InfinitePlace F → M) : ∏ w, f w = f w₀ * ∏ w : Wo w₀, f w := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀)]
  congr 1
  rw [Finset.prod_subtype (Finset.univ.erase w₀) (p := fun w => w ≠ w₀) (by simp)]

/-- `Φ(a) = ∫_{x'} κ(e^{a − Σx'}) ∏_{w'} κ(e^{x'_{w'}})`. -/
noncomputable def Vcore (w₀ : InfinitePlace F) (κ : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x' : Wo w₀ → ℝ, κ (Real.exp (a - ∑ w, x' w)) * ∏ w, κ (Real.exp (x' w))

theorem volume_torus_real :
    (volume : Measure (InfinitePlace F → AddCircle (2 * Real.pi))).real Set.univ =
      (2 * Real.pi) ^ Fintype.card (InfinitePlace F) := by
  rw [Measure.real, volume_pi, Measure.pi_univ]
  simp only [AddCircle.measure_univ, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal Real.two_pi_pos.le]

theorem Vprof_eq (h𝔪 : 𝔪 ≠ ⊥) (w₀ : InfinitePlace F) (κ : ℝ → ℝ) (hκm : Measurable κ) (u : ℝ) :
    Vprof w₀ 𝔪 k κ u =
      (2 * Real.pi) ^ Fintype.card (InfinitePlace F) * Vcore w₀ κ (Real.log u) := by
  set a := Real.log u
  have hS : MeasurableSet {y : SModel 𝔪 k | y.2.2 = 0} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton (0 : SFin 𝔪 k))
  have hG : Measurable (fun y : SModel 𝔪 k =>
      if y.2.2 = 0 then ∏ w, κ (Real.exp (y.1 w)) else 0) := by
    refine Measurable.ite hS ?_ measurable_const
    exact Finset.measurable_prod _ fun w _ =>
      hκm.comp (Real.measurable_exp.comp ((measurable_pi_apply w).comp measurable_fst))
  rw [Vprof, shMeasure, integral_map (measurable_slice w₀ a).aemeasurable hG.aestronglyMeasurable]
  have hfun : (fun p : Base w₀ 𝔪 k => (fun y : SModel 𝔪 k =>
      if y.2.2 = 0 then ∏ w, κ (Real.exp (y.1 w)) else 0) (slice w₀ a p)) =
      ({0} ×ˢ Set.univ : Set (Base w₀ 𝔪 k)).indicator
        (fun p => κ (Real.exp (a - ∑ w, p.2.1 w)) * ∏ w, κ (Real.exp (p.2.1 w))) := by
    funext p
    by_cases h : p.1 = 0
    · rw [Set.indicator_of_mem (show p ∈ ({0} ×ˢ Set.univ : Set (Base w₀ 𝔪 k)) by simp [h])]
      dsimp only
      rw [if_pos (show (slice w₀ a p).2.2 = 0 from h)]
      simp only [slice]
      rw [h, SFin.norm_zero h𝔪, Real.log_one, sub_zero, prod_eq_mul_prod_Wo_V w₀,
        ext_self]
      congr 1
      exact Finset.prod_congr rfl fun w _ => by rw [ext_of_ne w₀ _ _ w.2]
    · rw [Set.indicator_of_notMem (show p ∉ ({0} ×ˢ Set.univ : Set (Base w₀ 𝔪 k)) by simp [h])]
      dsimp only
      rw [if_neg (show ¬ (slice w₀ a p).2.2 = 0 from h)]
  rw [hfun, integral_indicator ((measurableSet_singleton _).prod MeasurableSet.univ), baseMeasure,
    ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_singleton,
    Measure.count_singleton, one_smul]
  have h1 := integral_fun_snd (μ := Measure.dirac (0 : SFin 𝔪 k))
    (ν := (volume : Measure ((Wo w₀ → ℝ) × (InfinitePlace F → AddCircle (2 * Real.pi)))))
    (fun q => κ (Real.exp (a - ∑ w, q.1 w)) * ∏ w, κ (Real.exp (q.1 w)))
  have h2 := integral_fun_fst (μ := (volume : Measure (Wo w₀ → ℝ)))
    (ν := (volume : Measure (InfinitePlace F → AddCircle (2 * Real.pi))))
    (fun x' => κ (Real.exp (a - ∑ w, x' w)) * ∏ w, κ (Real.exp (x' w)))
  rw [h1, Measure.real, Measure.dirac_apply_of_mem (Set.mem_univ _), ENNReal.toReal_one, one_smul,
    Measure.volume_eq_prod, h2, volume_torus_real, smul_eq_mul, Vcore]

/-! ### The exponential substitution in the Mellin transform -/

theorem cpow_exp_eq (a : ℝ) (s : ℂ) :
    ((Real.exp a : ℝ) : ℂ) * ((Real.exp a : ℝ) : ℂ) ^ (s - 1) = Complex.exp (s * a) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos a).ne'),
    ← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; ring

theorem mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ a : ℝ, Complex.exp (s * a) * f (Real.exp a) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [mellin, h]
  congr 1; funext a
  rw [abs_of_pos (Real.exp_pos a), smul_eq_mul, Complex.real_smul, ← mul_assoc, cpow_exp_eq]

theorem mellinConvergent_iff_exp (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun a : ℝ => Complex.exp (s * a) * f (Real.exp a)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  rw [Set.image_univ, Real.range_exp, integrableOn_univ] at h
  rw [MellinConvergent, h]
  refine integrable_congr (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [abs_of_pos (Real.exp_pos a), smul_eq_mul, Complex.real_smul, ← mul_assoc, cpow_exp_eq]

/-! ### The Mellin transform of `V` -/

theorem norm_cexp_mul (s : ℂ) (a : ℝ) : ‖Complex.exp (s * a)‖ = Real.exp (s.re * a) := by
  rw [Complex.norm_exp]; simp [Complex.mul_re]

theorem Vprof_mellin (h𝔪 : 𝔪 ≠ ⊥) (w₀ : InfinitePlace F) (κ : ℝ → ℝ) (cκ Aκ : ℝ)
    (hκm : Measurable κ) (hκ0 : ∀ t, 0 ≤ κ t) (hcκ : 0 < cκ) (hAκ : 0 < Aκ)
    (hκM : ∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
      MellinConvergent (fun t => (κ t : ℂ)) s ∧
      mellin (fun t => (κ t : ℂ)) s =
        (cκ : ℂ) * (Aκ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) :
    Measurable (Vprof w₀ 𝔪 k κ) ∧
      ∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (Vprof w₀ 𝔪 k κ t : ℂ)) s ∧
        mellin (fun t => (Vprof w₀ 𝔪 k κ t : ℂ)) s =
          (((2 * Real.pi) ^ Fintype.card (InfinitePlace F) *
              cκ ^ Fintype.card (InfinitePlace F) : ℝ) : ℂ) *
            ((Aκ ^ Fintype.card (InfinitePlace F) : ℝ) : ℂ) ^ s *
            (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^
              Fintype.card (InfinitePlace F) := by
  set r := Fintype.card (InfinitePlace F)
  have hVeq : Vprof w₀ 𝔪 k κ = fun u => (2 * Real.pi) ^ r * Vcore w₀ κ (Real.log u) :=
    funext (Vprof_eq h𝔪 w₀ κ hκm)
  -- measurability of the integrand of `Vcore`
  have hfm : Measurable (fun q : ℝ × (Wo w₀ → ℝ) =>
      κ (Real.exp (q.1 - ∑ w, q.2 w)) * ∏ w, κ (Real.exp (q.2 w))) := by
    refine Measurable.mul (hκm.comp (Real.measurable_exp.comp (measurable_fst.sub ?_))) ?_
    · exact Finset.measurable_sum _ fun w _ => (measurable_pi_apply w).comp measurable_snd
    · exact Finset.measurable_prod _ fun w _ =>
        hκm.comp (Real.measurable_exp.comp ((measurable_pi_apply w).comp measurable_snd))
  refine ⟨?_, fun s hs => ?_⟩
  · rw [hVeq]
    have : Measurable (Vcore w₀ κ) :=
      (hfm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Wo w₀ → ℝ)))).measurable
    exact measurable_const.mul (this.comp Real.measurable_log)
  -- the one-variable integrand
  set g : ℝ → ℂ := fun b => Complex.exp (s * b) * (κ (Real.exp b) : ℂ) with hg_def
  have hg : Integrable g := (mellinConvergent_iff_exp _ s).1 (hκM s hs).1
  set M : ℂ := ∫ b, g b with hM_def
  have hMeq : M = (cκ : ℂ) * (Aκ : ℂ) ^ s *
      (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
    rw [hM_def, ← (hκM s hs).2, mellin_eq_integral_exp]
  have hgn : ∀ b, ‖g b‖ = Real.exp (s.re * b) * κ (Real.exp b) := by
    intro b
    rw [hg_def, norm_mul, norm_cexp_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 _)]
  -- the two-variable integrand
  set f₂ : ℝ × (Wo w₀ → ℝ) → ℂ := fun q =>
    Complex.exp (s * q.1) * (κ (Real.exp (q.1 - ∑ w, q.2 w)) : ℂ) *
      ∏ w, (κ (Real.exp (q.2 w)) : ℂ) with hf₂_def
  have hf₂_shift : ∀ (a : ℝ) (x' : Wo w₀ → ℝ), f₂ (a, x') =
      (Complex.exp (s * ∑ w, x' w) * ∏ w, (κ (Real.exp (x' w)) : ℂ)) * g (a - ∑ w, x' w) := by
    intro a x'
    simp only [hf₂_def, hg_def]
    rw [show Complex.exp (s * (a : ℂ)) = Complex.exp (s * ((∑ w, x' w : ℝ) : ℂ)) *
        Complex.exp (s * ((a - ∑ w, x' w : ℝ) : ℂ)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  have hprod_eq : ∀ x' : Wo w₀ → ℝ,
      Complex.exp (s * ∑ w, x' w) * ∏ w, (κ (Real.exp (x' w)) : ℂ) = ∏ w, g (x' w) := by
    intro x'
    simp only [hg_def, Finset.prod_mul_distrib]
    congr 1
    rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  have hf₂m : AEStronglyMeasurable f₂ (volume.prod volume) := by
    refine (Measurable.mul (Measurable.mul ?_ ?_) ?_).aestronglyMeasurable
    · exact Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp measurable_fst))
    · exact Complex.measurable_ofReal.comp
        (hκm.comp (Real.measurable_exp.comp (measurable_fst.sub
          (Finset.measurable_sum _ fun w _ => (measurable_pi_apply w).comp measurable_snd))))
    · exact Finset.measurable_prod _ fun w _ => Complex.measurable_ofReal.comp
        (hκm.comp (Real.measurable_exp.comp ((measurable_pi_apply w).comp measurable_snd)))
  have hpin : Integrable (fun x' : Wo w₀ → ℝ => ∏ w, ‖g (x' w)‖) := by
    have := Integrable.fintype_prod (ι := Wo w₀) (f := fun _ b => ‖g b‖)
      (μ := fun _ => (volume : Measure ℝ)) fun _ => hg.norm
    simpa only [← volume_pi] using this
  have hf₂i : Integrable f₂ (volume.prod volume) := by
    rw [integrable_prod_iff' hf₂m]
    refine ⟨Filter.Eventually.of_forall fun x' => ?_, ?_⟩
    · simp only [hf₂_shift]
      exact (hg.comp_sub_right _).const_mul _
    · have : (fun x' : Wo w₀ → ℝ => ∫ a, ‖f₂ (a, x')‖) =
          fun x' => (∫ b, ‖g b‖) * ∏ w, ‖g (x' w)‖ := by
        funext x'
        simp only [hf₂_shift, norm_mul]
        rw [integral_const_mul, integral_sub_right_eq_self (fun b => ‖g b‖), mul_comm,
          ← norm_mul, hprod_eq, norm_prod]
      rw [this]
      exact hpin.const_mul _
  -- `cexp(s a) V(e^a) = (2π)^r ∫ f₂(a, ·)`
  have hpt : ∀ a : ℝ, Complex.exp (s * a) * ((Vprof w₀ 𝔪 k κ (Real.exp a) : ℝ) : ℂ) =
      ((2 * Real.pi) ^ r : ℝ) * ∫ x', f₂ (a, x') := by
    intro a
    rw [hVeq]
    simp only [Real.log_exp, Vcore]
    rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_const_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
    simp only [hf₂_def, Complex.ofReal_mul, Complex.ofReal_prod]
    ring
  have hinner : ∀ x' : Wo w₀ → ℝ, ∫ a, f₂ (a, x') = M * ∏ w, g (x' w) := by
    intro x'
    simp only [hf₂_shift]
    rw [integral_const_mul, integral_sub_right_eq_self g, hprod_eq, mul_comm]
  refine ⟨?_, ?_⟩
  · rw [mellinConvergent_iff_exp]
    simp only [hpt]
    exact (hf₂i.integral_prod_left).const_mul _
  · rw [mellin_eq_integral_exp]
    simp only [hpt]
    rw [integral_const_mul,
      integral_integral_swap (f := fun a x' => f₂ (a, x'))
        (by have : Function.uncurry (fun a x' => f₂ (a, x')) = f₂ := by funext q; rfl
            rw [this]; exact hf₂i)]
    simp only [hinner]
    rw [integral_const_mul]
    have hpp : ∫ x' : Wo w₀ → ℝ, ∏ w, g (x' w) = ∏ _w : Wo w₀, M := by
      rw [volume_pi, integral_fintype_prod_eq_prod]
    rw [hpp]
    have hMr : M * ∏ _w : Wo w₀, M = M ^ r := by
      rw [← prod_eq_mul_prod_Wo_V w₀ (fun _ => M), Finset.prod_const, Finset.card_univ]
    rw [hMr, hMeq, mul_pow, mul_pow]
    have hA : ((Aκ ^ r : ℝ) : ℂ) ^ s = ((Aκ : ℂ) ^ s) ^ r := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hAκ r).ne'),
        Complex.cpow_def_of_ne_zero (by exact_mod_cast hAκ.ne'),
        ← Complex.ofReal_log (pow_pos hAκ r).le, ← Complex.ofReal_log hAκ.le, Real.log_pow,
        ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    rw [hA]
    push_cast
    ring

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
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

theorem integral_Phi_mul_eq_zero [Fintype (L3P.SP 𝔪)] (h𝔪 : 𝔪 ≠ ⊥) (w₀ : InfinitePlace F)
    (B : AddSubgroup (SFinCls 𝔪 k)) (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ)
    (hm : m w₀ = 1 ∨ m w₀ = -1) (D : SModel 𝔪 k → ℂ)
    (hD : ∀ (φ : AddCircle (2 * Real.pi)) (y : SModel 𝔪 k), D (y + rot w₀ φ) = D y) (a : ℝ) :
    ∫ y, Phi B Lf m y * D y ∂(shMeasure w₀ 𝔪 k a) = 0 := by
  set φ : AddCircle (2 * Real.pi) := ((Real.pi : ℝ) : AddCircle (2 * Real.pi))
  have hrot := integral_add_rot w₀ h𝔪 a (Pi.single w₀ φ) (fun y => Phi B Lf m y * D y)
  have hpt : ∀ y, Phi B Lf m (y + ((0, Pi.single w₀ φ, 0) : SModel 𝔪 k)) *
      D (y + ((0, Pi.single w₀ φ, 0) : SModel 𝔪 k)) = -(Phi B Lf m y * D y) := by
    intro y
    have h1 : (y + ((0, Pi.single w₀ φ, 0) : SModel 𝔪 k)) = y + rot w₀ φ := rfl
    have h2 : rho (y + rot w₀ φ) = rho y := rho_add_rot y (Pi.single w₀ φ)
    rw [h1, hD, Phi, Phi, psi_rot, h2, toCircle_pi_zsmul hm]
    ring
  rw [show (fun y => Phi B Lf m (y + ((0, Pi.single w₀ φ, 0) : SModel 𝔪 k)) *
      D (y + ((0, Pi.single w₀ φ, 0) : SModel 𝔪 k))) = fun y => -(Phi B Lf m y * D y) from
    funext hpt, MeasureTheory.integral_neg] at hrot
  have : (2 : ℂ) * ∫ y, Phi B Lf m y * D y ∂(shMeasure w₀ 𝔪 k a) = 0 := by
    linear_combination -hrot
  simpa using this

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField

/-! L2D: `U_S / U_S^6` is finite (library 4956b3f7, the S-unit count). -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_placesOf_finite (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  apply (Ideal.finite_factors h𝔪).subset
  intro v hv
  exact Ideal.dvd_iff_le.2 hv

lemma L2D_SClass_finite (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : Finite (SClass 𝔪) := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  have hμ : (primitiveRoots 6 F).Nonempty :=
    ⟨_, (mem_primitiveRoots (by norm_num)).2 hζ6⟩
  have : Finite (placesOf 𝔪) := (L2D_placesOf_finite 𝔪 h𝔪).to_subtype
  have hc := NumberField.natCard_sUnit_quotient_range_powMonoidHom F (placesOf 𝔪) hμ
  apply Nat.finite_of_card_ne_zero
  change Nat.card (↥((placesOf 𝔪).unit F) ⧸
    (powMonoidHom 6 : ↥((placesOf 𝔪).unit F) →* ↥((placesOf 𝔪).unit F)).range) ≠ 0
  rw [hc]
  positivity

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3X_Main: the data of `93d56f1c` from the two cuts

`data_of_cuts`: from `L3X_CutKP` (Prop 5.1 in coordinates) and `L3X_CutS` (the `S`-setting of §3)
one gets, for every admissible `(𝔪, χ, g)`, an `L3V.Data χ g` with `L3V.VClause`, i.e. the
conclusion of the integrated theta identity 93d56f1c:
* `V = Vprof` (the radial Bessel profile, Mellin transform (5.21));
* `𝒱 = F_S^×/F_S^{×6}` (as `Fin N`), `cls = [·]`, `L υ = L_υ`, `H υ c = Hprof` (Lemma 5.4);
* the identity: integrate `Fw − Rf` (radial by the cut) against `Φ = ρ 1_B L⁻¹` over the sheet
  `X_l`; the integral vanishes (`L3X_Rot`), the forward part is Cut63V's left side
  (`L3X_Fwd`, `L3X_Coef`) and the reflected part is the reflected expansion (`L3X_Rev`).
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem smallPrimesDvd_mono {N N' : ℕ} (h : N' ≤ N) (hs : SmallPrimesDvd N 𝔪) :
    SmallPrimesDvd N' 𝔪 :=
  fun P hP hP0 hle => hs P hP hP0 (hle.trans h)

theorem rowElt_eq (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    (rowElt g z : F) = (((uRep z.2 : SUnit 𝔪) : Fˣ) : F) * (g.gen z.1.1 : F) := by
  simp only [rowElt, Subalgebra.coe_mul]
  rfl

theorem lnorm_rowElt' (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    lnorm (sEmb 𝔪 k (rowElt g z : F)) = Real.log (Ideal.absNorm z.1.1 : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  have := L3P.span_unit_mul_gen g z.1
    (Set.unitEquivUnitsInteger (placesOf 𝔪) F (Function.surjInv QuotientGroup.mk_surjective z.2))
  exact lnorm_sEmb_gen h𝔪 z.1.2 this

theorem clsF_mul (h𝔪 : 𝔪 ≠ ⊥) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    clsF (𝔪 := 𝔪) (k := k) (a * b) = clsF a + clsF b := by
  simp only [clsF, sEmb_mul ha hb, Prod.snd_add, QuotientAddGroup.mk_add]

theorem clsF_pow_six (ε : SUnit 𝔪) :
    clsF (𝔪 := 𝔪) (k := k) ((((ε : SUnit 𝔪) : Fˣ) : F) ^ 6) = 0 := by
  simp only [clsF]
  rw [sEmb_pow (sUnit_ne_zero ε), QuotientAddGroup.eq_zero_iff]
  exact ⟨(sEmb 𝔪 k (((ε : SUnit 𝔪) : Fˣ) : F)).2.2, by simp [nsmulAddMonoidHom]⟩

theorem uRep_mem_iff (s : SClass 𝔪) :
    uRep s ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range ↔ s = 1 := by
  rw [← mk_uRep s, QuotientGroup.eq_one_iff, mk_uRep]

/-- The main identity for one row. -/
theorem hid_row [Fintype (L3P.SP 𝔪)] [Finite (SClass 𝔪)] (h𝔪 : 𝔪 ≠ ⊥) (E : L3V.Env ι 𝔪)
    (w₀ : InfinitePlace F) (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    (B : AddSubgroup (SFinCls 𝔪 k))
    (hB : ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 → ∀ ε : SUnit 𝔪,
      ((QuotientAddGroup.mk (sEmb 𝔪 k ((ε : Fˣ) * (g.gen 𝔄 : F))).2.2 : SFinCls 𝔪 k) ∈ B ↔
        ε ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range))
    (r : RowClass 𝔪) (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1)
    (hLf : ∀ a b, Lf (a + b) = Lf a * Lf b) (hLfn : ∀ a, ‖Lf a‖ = 1)
    (hLu : ∀ ε : SUnit 𝔪, Lmod Lf m (sEmb 𝔪 k ((ε : Fˣ) : F)) = 1)
    (hLg : ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 →
      Lmod Lf m (sEmb 𝔪 k (g.gen 𝔄 : F)) = χ.thetaChar g 𝔄 * residueSymbol ι 𝔪 𝔄 r.2.rep)
    (κ : ℝ → ℝ) (hκm : Measurable κ) (hκ0 : ∀ t, 0 ≤ κ t) {α : ℝ} (hα : 0 < α)
    (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N)))
    (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (hFm : ∀ c, Measurable (Fm c))
    (bf : SFin 𝔪 k → ℝ) (hbf0 : ∀ y, 0 ≤ bf y)
    (hbf : ∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ))
    (hFb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ c y, ‖Fm c y‖ ≤ C * (∏ w, bmaj α N (y.1 w)) * bf y.2.2)
    (hD : ∀ (φ : AddCircle (2 * Real.pi)) (y : SModel 𝔪 k),
      Fw g κ m r.1.1 (y + rot w₀ φ) - Rf g Fm r (y + rot w₀ φ) = Fw g κ m r.1.1 y - Rf g Fm r y)
    (l : ℝ) (hl : 0 < l) :
    L3V.fwd g χ (Vprof w₀ 𝔪 k κ) r l =
      ∑' z : RowClass 𝔪, L3V.Eprod g r z * (Lmod Lf m (sEmb 𝔪 k (L3V.nu g r z)))⁻¹ *
        Hprof w₀ B Lf m Fm (clsF (L3V.nu g r z))
          ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) := by
  set a := Real.log l
  obtain ⟨hFi, hFeq⟩ := fwd_integral h𝔪 w₀ E g B Lf m hLf hLfn hLu κ hκm hκ0 hα hκb r.1.1 a
  obtain ⟨hRi, hReq⟩ := rev_integral h𝔪 w₀ g B Lf m hLf hLfn hLu Fm hFm hα bf hbf0 hbf hFb r a
  have hzero := integral_Phi_mul_eq_zero h𝔪 w₀ B Lf m (hm w₀)
    (fun y => Fw g κ m r.1.1 y - Rf g Fm r y) hD a
  have hsplit : ∫ y, Phi B Lf m y * (Fw g κ m r.1.1 y - Rf g Fm r y) ∂(shMeasure w₀ 𝔪 k a) =
      ∫ y, Phi B Lf m y * Fw g κ m r.1.1 y ∂(shMeasure w₀ 𝔪 k a) -
        ∫ y, Phi B Lf m y * Rf g Fm r y ∂(shMeasure w₀ 𝔪 k a) := by
    simp_rw [mul_sub]
    exact integral_sub hFi hRi
  have heq : ∫ y, Phi B Lf m y * Fw g κ m r.1.1 y ∂(shMeasure w₀ 𝔪 k a) =
      ∫ y, Phi B Lf m y * Rf g Fm r y ∂(shMeasure w₀ 𝔪 k a) := by
    rw [hzero] at hsplit; exact sub_eq_zero.mp hsplit.symm
  -- the forward side
  have hfwd : L3V.fwd g χ (Vprof w₀ 𝔪 k κ) r l =
      ∫ y, Phi B Lf m y * Fw g κ m r.1.1 y ∂(shMeasure w₀ 𝔪 k a) := by
    rw [hFeq, ← tsum_coefF_eq_fwd E g χ r (Vprof w₀ 𝔪 k κ) l
      (fun x => Lmod Lf m (sEmb 𝔪 k x)) ?hL]
    case hL =>
      intro z hz
      rw [rowElt_eq, sEmb_mul (sUnit_ne_zero _) (C3B.gen_ne_zero g z.1.1 z.1.2),
        Lmod_add Lf m hLf, hLu, one_mul, hLg z.1.1 z.1.2]
    have hinj : Function.Injective (fun 𝔷 : {𝔷 : Ideal (𝓞 F) // IsExterior 𝔪 𝔷} =>
        ((𝔷, 1) : RowClass 𝔪)) := fun a b h => (Prod.ext_iff.1 h).1
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun 𝔷 => ?_
      have hsel : Bind B (clsF (rowElt g ((𝔷, 1) : RowClass 𝔪) : F)) = 1 := by
        have := (hB 𝔷.1 𝔷.2 (uRep 1)).2 ((uRep_mem_iff 1).2 rfl)
        rw [Bind, clsF, rowElt_eq, if_pos this]
      rw [hsel, mul_one]
      have hN0 : (0 : ℝ) < Ideal.absNorm 𝔷.1 := by
        have : Ideal.absNorm 𝔷.1 ≠ 0 := by
          rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact 𝔷.2.1
        exact_mod_cast Nat.pos_of_ne_zero this
      have hV : Vprof w₀ 𝔪 k κ (Ideal.absNorm 𝔷.1 * l) = ∫ y, fpAbs κ y ∂(shMeasure w₀ 𝔪 k
          (a + lnorm (sEmb 𝔪 k (rowElt g ((𝔷, 1) : RowClass 𝔪) : F)))) := by
        rw [Vprof, lnorm_rowElt' h𝔪 g, Real.log_mul hN0.ne' hl.ne', add_comm]
        rfl
      rw [hV]
      rfl
    · intro z hz
      by_cases h1 : z.2 = 1
      · exact ⟨z.1, Prod.ext rfl h1.symm⟩
      · exfalso; apply hz
        have hsel : Bind B (clsF (rowElt g z : F)) = 0 := by
          have := (hB z.1.1 z.1.2 (uRep z.2)).not.2 (by rw [uRep_mem_iff]; exact h1)
          rw [Bind, clsF, rowElt_eq, if_neg this]
        simp [hsel]
  -- the reflected side
  rw [hfwd, heq, hReq]
  refine tsum_congr fun z => ?_
  congr 2
  have hb0 : (g.gen r.1.1 : F) ≠ 0 := C3B.gen_ne_zero g r.1.1 r.1.2
  have hz0 : (rowElt g z : F) ≠ 0 := by
    rw [rowElt_eq]; exact mul_ne_zero (sUnit_ne_zero _) (C3B.gen_ne_zero g z.1.1 z.1.2)
  have hN : ∀ I : {I : Ideal (𝓞 F) // IsExterior 𝔪 I}, (0 : ℝ) < Ideal.absNorm I.1 := fun I => by
    have : Ideal.absNorm I.1 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact I.2.1
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [L3V.nu, sEmb_div hz0 (pow_ne_zero 2 hb0), sEmb_pow hb0, lnorm_sub h𝔪, lnorm_rowElt' h𝔪 g,
    show ((2 : ℕ) • sEmb 𝔪 k (g.gen r.1.1 : F)) = sEmb 𝔪 k (g.gen r.1.1 : F) +
      sEmb 𝔪 k (g.gen r.1.1 : F) by rw [two_nsmul], lnorm_add h𝔪,
    lnorm_sEmb_gen h𝔪 r.1.2 (g.span_gen r.1.1 r.1.2)]
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log (hN z.1), Real.exp_log (hN r.1),
    Real.exp_log hl]
  ring

/-- `𝒱`: `F_S^×/F_S^{×6}` as `Fin N`, multiplicatively. -/
def eV (𝔪 : Ideal (𝓞 F)) (k : ℕ) [Finite (SFinCls 𝔪 k)] :
    Fin (Nat.card (SFinCls 𝔪 k)) ≃ Multiplicative (SFinCls 𝔪 k) :=
  (Finite.equivFin (SFinCls 𝔪 k)).symm.trans Multiplicative.ofAdd

theorem data_of_cuts (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hLoc : L3V_LocPkg n F ι)
    (hKP : L3J_CutKP n F ι) (hSB : L3X_CutSB n F ι) (hSL : L3X_CutSL n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ D : L3V.Data χ g, L3V.VClause D.V := by
  obtain ⟨N₁, hN₁⟩ := kp_unpack n F ι hKP
  obtain ⟨N₂, hN₂⟩ := sb_unpack n F ι hSB
  obtain ⟨N₄, hN₄⟩ := sl_unpack n F ι hSL
  obtain ⟨N₃, hN₃⟩ := L3V.env_of_locPkg n F ι hLoc
  refine ⟨max (max N₁ N₄) (max N₂ N₃), fun 𝔪 h𝔪 hs χ g => ?_⟩
  have hs₁ := smallPrimesDvd_mono ((le_max_left _ _).trans (le_max_left _ _)) hs
  have hs₄ := smallPrimesDvd_mono ((le_max_right _ _).trans (le_max_left _ _)) hs
  have hs₂ := smallPrimesDvd_mono ((le_max_left _ _).trans (le_max_right _ _)) hs
  have hs₃ := smallPrimesDvd_mono ((le_max_right _ _).trans (le_max_right _ _)) hs
  have E := hN₃ 𝔪 h𝔪 hs₃
  obtain ⟨k₁, hk₁⟩ := hN₁ 𝔪 h𝔪 hs₁ g
  obtain ⟨k₂, hk₂⟩ := hN₂ 𝔪 h𝔪 hs₂ g
  obtain ⟨k₄, hk₄⟩ := hN₄ 𝔪 h𝔪 hs₄ χ g
  set k := max k₁ (max k₂ k₄)
  obtain ⟨κ, cκ, Aκ, α, hκm, hcκ, hAκ, hα, hκ0, hκM, hκb, hKm⟩ := hk₁ k (le_max_left _ _)
  obtain ⟨hfin, B, hB⟩ := hk₂ k ((le_max_left _ _).trans (le_max_right _ _))
  have hL := hk₄ k ((le_max_right _ _).trans (le_max_right _ _))
  choose Lf mυ hm hLf hLfn hLu hLg using hL
  choose! Fm bf hFm hbf0 hbf hFC hFb hD using hKm
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  haveI : Finite (SClass 𝔪) := L2D_SClass_finite n hn0 hn 𝔪 h𝔪
  haveI := hfin
  letI : Fintype (SClass 𝔪) := Fintype.ofFinite _
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set e := eV 𝔪 k
  letI grp : CommGroup (Fin (Nat.card (SFinCls 𝔪 k))) := e.commGroup
  -- the bound in Lemma 5.4 form
  have hFb0 : ∀ υ : SClass 𝔪, ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ c y,
      ‖Fm (mυ υ) c y‖ ≤ C * (∏ w, bmaj α N (y.1 w)) * bf (mυ υ) y.2.2 := by
    intro υ N hN
    obtain ⟨C, hC⟩ := hFb (mυ υ) (hm υ) N hN
    refine ⟨C, fun c y => ?_⟩
    have := hC w₀ c y 0 (by norm_num)
    have h0 : (y + ((Pi.single w₀ (0 : ℝ), 0, 0) : SModel 𝔪 k)) = y := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rw [iteratedDeriv_zero, h0] at this
    simpa [bmaj] using this
  -- the sheet profiles, family over `c`, for each `υ`
  have hprof : ∀ υ : SClass 𝔪,
      (∀ c, ContDiff ℝ 2 (fun t => Hprof w₀ B (Lf υ) (mυ υ) (Fm (mυ υ)) c (Real.exp t))) ∧
      ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ c, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => Hprof w₀ B (Lf υ) (mυ υ) (Fm (mυ υ)) c (Real.exp t)) t‖ ≤
          C * min (Real.exp (α / 2 * t)) (Real.exp (-(N * t))) := by
    intro υ
    set G : SFinCls 𝔪 k → SModel 𝔪 k → ℂ := fun c y =>
      Bind B (c - QuotientAddGroup.mk y.2.2) * Lmod (Lf υ) (mυ υ) y * Fm (mυ υ) c y
    have hHG : ∀ c, (fun t => Hprof w₀ B (Lf υ) (mυ υ) (Fm (mυ υ)) c (Real.exp t)) =
        fun t => ∫ y, G c y ∂(shMeasure w₀ 𝔪 k t) := by
      intro c; funext t; simp only [Hprof, Real.log_exp, G]
    have hshift : ∀ c y (s : ℝ), G c (y + ((Pi.single w₀ s, 0, 0) : SModel 𝔪 k)) =
        (Bind B (c - QuotientAddGroup.mk y.2.2) * Lmod (Lf υ) (mυ υ) y) *
          Fm (mυ υ) c (y + ((Pi.single w₀ s, 0, 0) : SModel 𝔪 k)) := by
      intro c y s
      simp only [G, Lmod_rsh, Prod.snd_add, add_zero]
    have hsp := sheet_profile w₀ h𝔪 G hα (bf (mυ υ)) (hbf0 (mυ υ) (hm υ)) (hbf (mυ υ) (hm υ))
      (fun c => ((measurable_of_countable (fun y : SFin 𝔪 k =>
          Bind B (c - QuotientAddGroup.mk y))).comp (measurable_snd.comp measurable_snd)).mul
        (measurable_Lmod (Lf υ) (mυ υ)) |>.mul (hFm (mυ υ) (hm υ) c))
      (fun c y => by
        simp_rw [hshift]
        exact contDiff_const.mul (hFC (mυ υ) (hm υ) w₀ c y))
      (fun N hN => by
        obtain ⟨C, hC⟩ := hFb (mυ υ) (hm υ) N hN
        refine ⟨C, fun c y j hj => ?_⟩
        simp_rw [hshift]
        rw [iteratedDeriv_const_mul_field, norm_mul]
        have h1 : ‖Bind B (c - QuotientAddGroup.mk y.2.2) * Lmod (Lf υ) (mυ υ) y‖ ≤ 1 := by
          rw [norm_mul, norm_Lmod (Lf υ) (mυ υ) (hLfn υ), mul_one]; exact norm_Bind_le B _
        have h2 := hC w₀ c y j hj
        have h3 : 0 ≤ C * (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) *
            bf (mυ υ) y.2.2 := (norm_nonneg _).trans h2
        calc _ ≤ 1 * ‖iteratedDeriv j (fun s : ℝ => Fm (mυ υ) c
              (y + ((Pi.single w₀ s, 0, 0) : SModel 𝔪 k))) 0‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact h2)
    refine ⟨fun c => (hHG c) ▸ hsp.1 c, fun N hN => ?_⟩
    obtain ⟨C, hC⟩ := hsp.2 N hN
    exact ⟨C, fun c j hj t => (hHG c) ▸ hC c j hj t⟩
  choose hHC hHB using hprof
  refine ⟨⟨Vprof w₀ 𝔪 k κ, Fin (Nat.card (SFinCls 𝔪 k)), grp, inferInstance,
    fun x => e.symm (Multiplicative.ofAdd (clsF x)),
    fun υ x => Lmod (Lf υ) (mυ υ) (sEmb 𝔪 k x),
    fun υ c u => Hprof w₀ B (Lf υ) (mυ υ) (Fm (mυ υ)) (Multiplicative.toAdd (e c)) u,
    α / 2, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- hcls
    intro a b ha hb
    rw [clsF_mul h𝔪 ha hb, Equiv.mul_def]
    simp
  · -- hcls6
    intro ε
    rw [clsF_pow_six, Equiv.one_def]
    rfl
  · intro υ a b ha hb
    rw [sEmb_mul ha hb, Lmod_add (Lf υ) (mυ υ) (hLf υ)]
  · intro υ a _; exact norm_Lmod (Lf υ) (mυ υ) (hLfn υ) _
  · intro υ ε; exact hLu υ ε
  · intro υ c; exact hHC υ _
  · intro N hN
    choose C hC using fun υ => hHB υ N hN
    refine ⟨∑ υ, |C υ|, fun υ c j hj t => ?_⟩
    refine (hC υ _ j hj t).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (le_min (Real.exp_pos _).le (Real.exp_pos _).le)
    exact (le_abs_self _).trans (Finset.single_le_sum (fun υ _ => abs_nonneg (C υ))
      (Finset.mem_univ υ))
  · intro r l hl
    have h := hid_row h𝔪 E w₀ g χ B hB r (Lf r.2) (mυ r.2) (hm r.2) (hLf r.2) (hLfn r.2)
      (hLu r.2) (hLg r.2) κ hκm hκ0 hα hκb (Fm (mυ r.2)) (hFm _ (hm r.2)) (bf (mυ r.2))
      (hbf0 _ (hm r.2)) (hbf _ (hm r.2)) (hFb0 r.2) (fun φ y => hD _ (hm r.2) r w₀ φ y) l hl
    rw [h]
    refine tsum_congr fun z => ?_
    simp
  · obtain ⟨hVm, hVM⟩ := Vprof_mellin (k := k) h𝔪 w₀ κ cκ Aκ hκm hκ0 hcκ hAκ hκM
    exact ⟨Fintype.card (InfinitePlace F), (2 * Real.pi) ^ Fintype.card (InfinitePlace F) *
      cκ ^ Fintype.card (InfinitePlace F), Aκ ^ Fintype.card (InfinitePlace F), hVm,
      by positivity, by positivity, hVM⟩

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3X_Final: 93d56f1c from the two cuts (statement verbatim from the stub) -/

namespace ArtinPrimitiveRoots.L3X

open NumberField UniqueFactorizationMonoid

open Classical in
theorem target_of_cuts (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hLoc : L3V_LocPkg n F ι) (hKP : L3J_CutKP n F ι) (hSB : L3X_CutSB n F ι)
    (hSL : L3X_CutSL n F ι) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
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
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (𝒱 : Type) (_ : CommGroup 𝒱) (_ : Fintype 𝒱) (cls : F → 𝒱) (L : SClass 𝔪 → F → ℂ)
      (H : SClass 𝔪 → 𝒱 → ℝ → ℂ) (α : ℝ), 0 < α ∧
      (∀ a b : F, a ≠ 0 → b ≠ 0 → cls (a * b) = cls a * cls b) ∧
      (∀ ε : SUnit 𝔪, cls (((ε : Fˣ) : F) ^ 6) = 1) ∧
      (∀ υ (a b : F), a ≠ 0 → b ≠ 0 → L υ (a * b) = L υ a * L υ b) ∧
      (∀ υ (a : F), a ≠ 0 → ‖L υ a‖ = 1) ∧
      (∀ υ (ε : SUnit 𝔪), L υ ((ε : Fˣ) : F) = 1) ∧
      (∀ υ κ, ContDiff ℝ 2 (fun t => H υ κ (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ κ, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ κ (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      ∀ (r : RowClass 𝔪) (l : ℝ), 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' z : RowClass 𝔪,
            (∏ P ∈ (normalizedFactors (z.1.1 * r.1.1)).toFinset,
              Eloc P ((normalizedFactors r.1.1).count P)
                (((normalizedFactors z.1.1).count P : ℤ) -
                  2 * ((normalizedFactors r.1.1).count P : ℤ))
                ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2 *
                  (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
                    2 * ((normalizedFactors r.1.1).count P : ℤ))))) *
            (L r.2 ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))⁻¹ *
            H r.2 (cls ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))
              ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) := by
  obtain ⟨N₀, hN⟩ := data_of_cuts n hn0 hn F ι hLoc hKP hSB hSL
  refine ⟨N₀, fun 𝔪 h𝔪 hs χ g => ?_⟩
  obtain ⟨D, rr, C₀, A₀, hV, hC₀, hA₀, hM⟩ := hN 𝔪 h𝔪 hs χ g
  exact ⟨D.V, rr, C₀, A₀, hV, hC₀, hA₀, hM, D.𝒱, D.grp, D.fin, D.cls, D.L, D.H, D.α, D.hα, D.hcls,
    D.hcls6, D.hL, D.hLn, D.hLu, D.hH, D.hHb, D.hid⟩

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! L3V_EnvP: the local package `L3V_LocPkg` (Lemma 6.2 at one prime) from the published seam
`exists_cutoff_digitSum_eq_mul_localSymbol_pow`, so that `L3V.Env` does not need `L3V_LocPf`. -/

namespace ArtinPrimitiveRoots

theorem L3V_locPkg_of_stub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L3V_LocPkg n F ι :=
  exists_cutoff_digitSum_eq_mul_localSymbol_pow n hn0 hn F ι

end ArtinPrimitiveRoots

end
end

section
section
/-! L3J: 93d56f1c (`exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker`) from the two
candidate cuts: Prop 5.1 in coordinates (the corrected KP cut, `…_rotInvariant`) and the `S`-setting of §3. Does not import the target stub. -/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

theorem L3J_cutKP_of_stub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L3J_CutKP n F ι :=
  exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant n hn0 hn F ι

theorem L3J_cutSB_of_stub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L3X_CutSB n F ι :=
  exists_cutoff_finite_sFinCls_and_exists_addSubgroup_mem_iff_mem_range_pow_six n hn0 hn F ι

theorem L3J_cutSL_of_stub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L3X_CutSL n F ι :=
  exists_cutoff_exists_sChar_sEmb_gen_eq_thetaChar_mul_residueSymbol n hn0 hn F ι

open Classical in
theorem exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
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
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (𝒱 : Type) (_ : CommGroup 𝒱) (_ : Fintype 𝒱) (cls : F → 𝒱) (L : SClass 𝔪 → F → ℂ)
      (H : SClass 𝔪 → 𝒱 → ℝ → ℂ) (α : ℝ), 0 < α ∧
      (∀ a b : F, a ≠ 0 → b ≠ 0 → cls (a * b) = cls a * cls b) ∧
      (∀ ε : SUnit 𝔪, cls (((ε : Fˣ) : F) ^ 6) = 1) ∧
      (∀ υ (a b : F), a ≠ 0 → b ≠ 0 → L υ (a * b) = L υ a * L υ b) ∧
      (∀ υ (a : F), a ≠ 0 → ‖L υ a‖ = 1) ∧
      (∀ υ (ε : SUnit 𝔪), L υ ((ε : Fˣ) : F) = 1) ∧
      (∀ υ κ, ContDiff ℝ 2 (fun t => H υ κ (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ κ, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ κ (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      ∀ (r : RowClass 𝔪) (l : ℝ), 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' z : RowClass 𝔪,
            (∏ P ∈ (normalizedFactors (z.1.1 * r.1.1)).toFinset,
              Eloc P ((normalizedFactors r.1.1).count P)
                (((normalizedFactors z.1.1).count P : ℤ) -
                  2 * ((normalizedFactors r.1.1).count P : ℤ))
                ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2 *
                  (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
                    2 * ((normalizedFactors r.1.1).count P : ℤ))))) *
            (L r.2 ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))⁻¹ *
            H r.2 (cls ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))
              ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) := by
  exact L3X.target_of_cuts n hn0 hn F ι (L3V_locPkg_of_stub n hn0 hn F ι) (L3J_cutKP_of_stub n hn0 hn F ι)
    (L3J_cutSB_of_stub n hn0 hn F ι) (L3J_cutSL_of_stub n hn0 hn F ι)

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
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
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (𝒱 : Type) (_ : CommGroup 𝒱) (_ : Fintype 𝒱) (cls : F → 𝒱) (L : SClass 𝔪 → F → ℂ)
      (H : SClass 𝔪 → 𝒱 → ℝ → ℂ) (α : ℝ), 0 < α ∧
      (∀ a b : F, a ≠ 0 → b ≠ 0 → cls (a * b) = cls a * cls b) ∧
      (∀ ε : SUnit 𝔪, cls (((ε : Fˣ) : F) ^ 6) = 1) ∧
      (∀ υ (a b : F), a ≠ 0 → b ≠ 0 → L υ (a * b) = L υ a * L υ b) ∧
      (∀ υ (a : F), a ≠ 0 → ‖L υ a‖ = 1) ∧
      (∀ υ (ε : SUnit 𝔪), L υ ((ε : Fˣ) : F) = 1) ∧
      (∀ υ κ, ContDiff ℝ 2 (fun t => H υ κ (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ κ, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ κ (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      ∀ (r : RowClass 𝔪) (l : ℝ), 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' z : RowClass 𝔪,
            (∏ P ∈ (normalizedFactors (z.1.1 * r.1.1)).toFinset,
              Eloc P ((normalizedFactors r.1.1).count P)
                (((normalizedFactors z.1.1).count P : ℤ) -
                  2 * ((normalizedFactors r.1.1).count P : ℤ))
                ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2 *
                  (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
                    2 * ((normalizedFactors r.1.1).count P : ℤ))))) *
            (L r.2 ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))⁻¹ *
            H r.2 (cls ((rowElt g z : F) / (g.gen r.1.1 : F) ^ 2))
              ((Ideal.absNorm z.1.1 : ℝ) / ((Ideal.absNorm r.1.1 : ℝ) ^ 2 * l)) := by
  exact ArtinPrimitiveRoots.exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker n hn0 hn F ι

end
