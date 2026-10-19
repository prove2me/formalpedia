-- Prove2me | solution 1 for ArtinPrimitiveRoots.not_exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_radial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T12:13:31.017979+00:00
-- url     : https://prove2.me/submissions/49ee3f40-35ad-4bd4-9d77-69c7c04c114f

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeSModel
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_nonempty_allowedGen
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

open Classical in
/-- Prop 5.1 in coordinates (see the module doc). -/
def L3X_CutKP (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
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
      (∀ N : ℝ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ c, Measurable (Fm c)) ∧ (∀ y, 0 ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
      (∀ w c y, ContDiff ℝ 2 (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
      (∀ N : ℝ, ∃ C : ℝ, ∀ w c y, ∀ j : ℕ, j ≤ 2 →
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
/-! # L3J_Kfalse: no profile κ has both the Mellin transform (5.20) and two-sided super-decay

If `κ ≥ 0`, `mellin κ s = cκ Aκ^s Γ(s+5/6) Γ(s+7/6)` for `Re s > −5/6`, and
`κ t ≤ C_N min(t^α, t^{-N})` for every real `N` (including negative `N`), then `False`:
`N = −1` gives `κ t ≤ C₁ t`, `N = 1` gives `κ t ≤ C₂ t⁻¹`, so `|mellin κ (−5/6 + ε)|` stays
bounded while the right side is `≥ c/ε`. -/

namespace ArtinPrimitiveRoots.L3J

open MeasureTheory Set

theorem gamma_lower : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc (1 / 3 : ℝ) 2, m ≤ Real.Gamma x := by
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 3 : ℝ) 2) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
    refine (Real.differentiableAt_Gamma fun m => ?_).continuousAt.continuousWithinAt
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 (by norm_num : (1 / 3 : ℝ) ≤ 2)) hcont
  refine ⟨Real.Gamma x₀, Real.Gamma_pos_of_pos (lt_of_lt_of_le (by norm_num) hx₀.1), ?_⟩
  intro x hx
  exact hmin hx

theorem rpow_lower {A : ℝ} (hA : 0 < A) {σ : ℝ} (h1 : -(5 / 6 : ℝ) ≤ σ) (h2 : σ ≤ 0) :
    min (A ^ (-(5 / 6 : ℝ))) 1 ≤ A ^ σ := by
  rcases le_or_gt 1 A with h | h
  · exact (min_le_left _ _).trans (Real.rpow_le_rpow_of_exponent_le h h1)
  · refine (min_le_right _ _).trans ?_
    calc (1 : ℝ) = A ^ (0 : ℝ) := (Real.rpow_zero A).symm
      _ ≤ A ^ σ := Real.rpow_le_rpow_of_exponent_ge hA h.le h2

/-- The majorant `C₁ t^{-5/6}` on `(0,1]`, `C₂ t^{-2}` on `(1,∞)`. -/
noncomputable def maj (C₁ C₂ : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun t => C₁ * t ^ (-(5 / 6 : ℝ))) t +
    (Ioi (1 : ℝ)).indicator (fun t => C₂ * t ^ (-(2 : ℝ))) t

theorem integrableOn_maj (C₁ C₂ : ℝ) : IntegrableOn (maj C₁ C₂) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => C₁ * t ^ (-(5 / 6 : ℝ))) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -(5 / 6))).const_mul C₁
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 this
  have h2 : IntegrableOn (fun t : ℝ => C₂ * t ^ (-(2 : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul C₂
  refine Integrable.add ?_ ?_
  · exact (h1.integrable_indicator measurableSet_Ioc).integrableOn
  · exact (h2.integrable_indicator measurableSet_Ioi).integrableOn

theorem integral_maj (C₁ C₂ : ℝ) : ∫ t in Ioi (0 : ℝ), maj C₁ C₂ t = 6 * C₁ + C₂ := by
  have h1 : IntegrableOn (fun t : ℝ => C₁ * t ^ (-(5 / 6 : ℝ))) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -(5 / 6))).const_mul C₁
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 this
  have h2 : IntegrableOn (fun t : ℝ => C₂ * t ^ (-(2 : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul C₂
  unfold maj
  rw [integral_add (h1.integrable_indicator measurableSet_Ioc).integrableOn
    (h2.integrable_indicator measurableSet_Ioi).integrableOn]
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi]
  have e1 : Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 := inter_eq_right.2 Ioc_subset_Ioi_self
  have e2 : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 := inter_eq_right.2 (Ioi_subset_Ioi zero_le_one)
  rw [e1, e2]
  have i1 : ∫ t in Ioc (0 : ℝ) 1, C₁ * t ^ (-(5 / 6 : ℝ)) = 6 * C₁ := by
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num))]
    rw [Real.one_rpow, Real.zero_rpow (by norm_num)]
    norm_num
    ring
  have i2 : ∫ t in Ioi (1 : ℝ), C₂ * t ^ (-(2 : ℝ)) = C₂ := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos, Real.one_rpow]
    norm_num
  rw [i1, i2]

theorem kappa_contra (κ : ℝ → ℝ) (cκ Aκ α : ℝ) (hcκ : 0 < cκ) (hAκ : 0 < Aκ)
    (hκ0 : ∀ t, 0 ≤ κ t)
    (hM : ∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (κ t : ℂ)) s ∧
        mellin (fun t => (κ t : ℂ)) s =
          (cκ : ℂ) * (Aκ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)))
    (hb : ∀ N : ℝ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) : False := by
  obtain ⟨C₁, hC₁⟩ := hb (-1)
  obtain ⟨C₂, hC₂⟩ := hb 1
  set D₁ := max C₁ 0
  set D₂ := max C₂ 0
  have hb1 : ∀ t : ℝ, 0 < t → κ t ≤ D₁ * t := by
    intro t ht
    have h := hC₁ t ht
    rw [neg_neg, Real.rpow_one] at h
    have hm0 : 0 ≤ min (t ^ α) t := le_min (Real.rpow_nonneg ht.le _) ht.le
    calc κ t ≤ C₁ * min (t ^ α) t := h
      _ ≤ D₁ * min (t ^ α) t := mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ ≤ D₁ * t := mul_le_mul_of_nonneg_left (min_le_right _ _) (le_max_right _ _)
  have hb2 : ∀ t : ℝ, 0 < t → κ t ≤ D₂ * t ^ (-(1 : ℝ)) := by
    intro t ht
    have h := hC₂ t ht
    have hm0 : 0 ≤ min (t ^ α) (t ^ (-(1 : ℝ))) :=
      le_min (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)
    calc κ t ≤ C₂ * min (t ^ α) (t ^ (-(1 : ℝ))) := h
      _ ≤ D₂ * min (t ^ α) (t ^ (-(1 : ℝ))) := mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ ≤ D₂ * t ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (le_max_right _ _)
  -- the uniform bound on the Mellin transform
  have hLHS : ∀ σ : ℝ, -(5 / 6 : ℝ) < σ → σ ≤ 0 →
      ‖mellin (fun t => (κ t : ℂ)) (σ : ℂ)‖ ≤ 6 * D₁ + D₂ := by
    intro σ hσ1 hσ2
    have hconv := (hM σ (by simpa using hσ1)).1
    unfold mellin
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_maj D₁ D₂]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
      (integrableOn_maj D₁ D₂) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_)
    have hn : ‖(t : ℂ) ^ ((σ : ℂ) - 1) • ((κ t : ℝ) : ℂ)‖ = t ^ (σ - 1) * κ t := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
        Real.norm_of_nonneg (hκ0 t)]
      simp
    show ‖(t : ℂ) ^ ((σ : ℂ) - 1) • ((κ t : ℝ) : ℂ)‖ ≤ maj D₁ D₂ t
    rw [hn]
    have hpos : 0 ≤ t ^ (σ - 1) := Real.rpow_nonneg ht.le _
    unfold maj
    rcases le_or_gt t 1 with h1 | h1
    · have hmem : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
      have hnm : t ∉ Ioi (1 : ℝ) := fun h => (not_lt.2 h1) h
      rw [indicator_of_mem hmem, indicator_of_notMem hnm, add_zero]
      calc t ^ (σ - 1) * κ t ≤ t ^ (σ - 1) * (D₁ * t) :=
            mul_le_mul_of_nonneg_left (hb1 t ht) hpos
        _ = D₁ * t ^ σ := by
            rw [show t ^ (σ - 1) * (D₁ * t) = D₁ * (t ^ (σ - 1) * t ^ (1 : ℝ)) by
              rw [Real.rpow_one]; ring, ← Real.rpow_add ht]
            ring_nf
        _ ≤ D₁ * t ^ (-(5 / 6 : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht h1 hσ1.le)
              (le_max_right _ _)
    · have hmem : t ∈ Ioi (1 : ℝ) := h1
      have hnm : t ∉ Ioc (0 : ℝ) 1 := fun h => (not_le.2 h1) h.2
      rw [indicator_of_mem hmem, indicator_of_notMem hnm, zero_add]
      calc t ^ (σ - 1) * κ t ≤ t ^ (σ - 1) * (D₂ * t ^ (-(1 : ℝ))) :=
            mul_le_mul_of_nonneg_left (hb2 t ht) hpos
        _ = D₂ * t ^ (σ - 2) := by
            rw [show t ^ (σ - 1) * (D₂ * t ^ (-(1 : ℝ))) = D₂ * (t ^ (σ - 1) * t ^ (-(1 : ℝ))) by
              ring, ← Real.rpow_add ht]
            ring_nf
        _ ≤ D₂ * t ^ (-(2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1.le (by linarith))
              (le_max_right _ _)
  -- the lower bound on the right side
  obtain ⟨m, hm0, hm⟩ := gamma_lower
  set a := min (Aκ ^ (-(5 / 6 : ℝ))) 1
  have ha0 : 0 < a := lt_min (Real.rpow_pos_of_pos hAκ _) one_pos
  set B := 6 * D₁ + D₂
  have hB0 : 0 ≤ B := by positivity
  set ε := min (1 / 12 : ℝ) (cκ * a * m * m / (2 * (B + 1)))
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 12 := min_le_left _ _
  have hε2 : ε ≤ cκ * a * m * m / (2 * (B + 1)) := min_le_right _ _
  set σ : ℝ := -(5 / 6) + ε
  have hσ1 : -(5 / 6 : ℝ) < σ := by simp only [σ]; linarith
  have hσ2 : σ ≤ 0 := by simp only [σ]; linarith
  have hval := (hM σ (by simpa using hσ1)).2
  have hL := hLHS σ hσ1 hσ2
  rw [hval] at hL
  have e1 : ((σ : ℝ) : ℂ) + 5 / 6 = ((ε : ℝ) : ℂ) := by
    simp only [σ]; push_cast; ring
  have e2 : ((σ : ℝ) : ℂ) + 7 / 6 = (((1 / 3 + ε : ℝ)) : ℂ) := by
    simp only [σ]; push_cast; ring
  rw [e1, e2, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_cpow hAκ.le] at hL
  rw [show ((cκ : ℂ) * ((Aκ ^ σ : ℝ) : ℂ) *
      (((Real.Gamma ε : ℝ) : ℂ) * ((Real.Gamma (1 / 3 + ε) : ℝ) : ℂ))) =
      (((cκ * Aκ ^ σ * (Real.Gamma ε * Real.Gamma (1 / 3 + ε))) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real] at hL
  have hG1 : Real.Gamma ε = Real.Gamma (ε + 1) / ε := by
    rw [Real.Gamma_add_one hε0.ne']; field_simp
  have hGa : m ≤ Real.Gamma (ε + 1) := hm _ ⟨by linarith, by linarith⟩
  have hGb : m ≤ Real.Gamma (1 / 3 + ε) := hm _ ⟨by linarith, by linarith⟩
  have hAσ : a ≤ Aκ ^ σ := rpow_lower hAκ hσ1.le hσ2
  have hpos : 0 < cκ * Aκ ^ σ * (Real.Gamma ε * Real.Gamma (1 / 3 + ε)) := by
    have := Real.Gamma_pos_of_pos hε0
    have := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < 1 / 3 + ε)
    have := Real.rpow_pos_of_pos hAκ σ
    positivity
  rw [Real.norm_of_nonneg hpos.le] at hL
  -- `cκ a m² / ε ≤ cκ Aκ^σ Γ(ε) Γ(1/3+ε) ≤ B`, while `cκ a m² / ε ≥ 2 (B + 1)`.
  have hlow : cκ * a * m * m / ε ≤ cκ * Aκ ^ σ * (Real.Gamma ε * Real.Gamma (1 / 3 + ε)) := by
    rw [hG1]
    have h1 : cκ * a * m * m / ε = cκ * a * (m / ε) * m := by ring
    have h2 : cκ * Aκ ^ σ * (Real.Gamma (ε + 1) / ε * Real.Gamma (1 / 3 + ε)) =
        cκ * Aκ ^ σ * (Real.Gamma (ε + 1) / ε) * Real.Gamma (1 / 3 + ε) := by ring
    rw [h1, h2]
    have hd : m / ε ≤ Real.Gamma (ε + 1) / ε := div_le_div_of_nonneg_right hGa hε0.le
    gcongr
  have hbig : 2 * (B + 1) ≤ cκ * a * m * m / ε := by
    rw [le_div_iff₀ hε0]
    have := mul_le_mul_of_nonneg_left hε2 (by positivity : (0 : ℝ) ≤ 2 * (B + 1))
    rw [mul_div_cancel₀ _ (by positivity : (2 * (B + 1) : ℝ) ≠ 0)] at this
    linarith
  linarith

end ArtinPrimitiveRoots.L3J

end
end

section
section
/-! # L3J_False: the published KP statement (95871697) is false

`L3X_CutKP n F ι` is the statement of 95871697 verbatim (checked in `L3J_Chk`). Its κ-clause
quantifies over every real `N` (no `0 < N`), which `L3J.kappa_contra` refutes. The only other input
is an `𝔪` with a system of allowed generators, which C0 (1c4e753c) supplies for every `𝔪` divisible
by the small primes; `𝔪 = (N!)` is divisible by every prime of norm `≤ N`. -/

namespace ArtinPrimitiveRoots.L3J

open NumberField

theorem smallPrimesDvd_factorial (F : Type*) [Field F] [NumberField F] {M N : ℕ} (hMN : M ≤ N) :
    SmallPrimesDvd M (Ideal.span {((N.factorial : ℕ) : 𝓞 F)}) := by
  intro P _ hP0 hPM
  rw [Ideal.span_le, Set.singleton_subset_iff]
  have hmem : ((Ideal.absNorm P : ℕ) : 𝓞 F) ∈ P := Ideal.absNorm_mem P
  have hpos : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero (by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact hP0)
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hpos (hPM.trans hMN)
  rw [SetLike.mem_coe, hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hmem

theorem span_factorial_ne_bot (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Ideal.span {((N.factorial : ℕ) : 𝓞 F)} ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast Nat.factorial_ne_zero N

theorem not_cutKP (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ)
    (hC0 : ∃ N₁ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₁ 𝔪 →
      Nonempty (AllowedGen ι 𝔪)) :
    ¬ L3X_CutKP n F ι := by
  rintro ⟨N₀, hN₀⟩
  obtain ⟨N₁, hN₁⟩ := hC0
  set N := max N₀ N₁
  obtain ⟨g⟩ := hN₁ _ (span_factorial_ne_bot F N)
    (smallPrimesDvd_factorial F (le_max_right N₀ N₁))
  obtain ⟨k₀, hk⟩ := hN₀ _ (span_factorial_ne_bot F N)
    (smallPrimesDvd_factorial F (le_max_left N₀ N₁)) g
  obtain ⟨κ, cκ, Aκ, α, _, hcκ, hAκ, _, hκ0, hM, hb, -⟩ := hk k₀ le_rfl
  exact kappa_contra κ cκ Aκ α hcκ hAκ hκ0 hM hb

end ArtinPrimitiveRoots.L3J

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem not_exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_radial (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ¬ ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
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
      (∀ N : ℝ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ c, Measurable (Fm c)) ∧ (∀ y, 0 ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
      (∀ w c y, ContDiff ℝ 2 (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
      (∀ N : ℝ, ∃ C : ℝ, ∀ w c y, ∀ j : ℕ, j ≤ 2 →
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
  := by
  exact L3J.not_cutKP n F ι (exists_cutoff_nonempty_allowedGen n hn0 hn F ι)

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ¬ ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
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
      (∀ N : ℝ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ c, Measurable (Fm c)) ∧ (∀ y, 0 ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
      (∀ w c y, ContDiff ℝ 2 (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
      (∀ N : ℝ, ∃ C : ℝ, ∀ w c y, ∀ j : ℕ, j ≤ 2 →
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
  := by
  exact ArtinPrimitiveRoots.not_exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_radial n hn0 hn F ι

end
