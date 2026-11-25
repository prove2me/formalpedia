-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
-- name    : GroundTheory_PAdicHodge_UntiltDegree
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:14:04.851614+00:00
-- url     : https://prove2.me/theorems/61583d1c-4355-41e4-b69d-bc19e5e91f36
-- title:
--   Untilt Degree
-- statement:
--   Definitions and structural lemmas for Untilt Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_untilt_add_p_mul
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_mem_Ioc
import Theorems.Thm_GroundTheory_PAdicHodge_exists_tiltSharp_family
import Theorems.Thm_GroundTheory_PAdicHodge_exists_untilt_sum_eq
import Theorems.Thm_GroundTheory_PAdicHodge_linearIndependent_tiltSharp
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_untilt_mem_untiltInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
theorem exists_mul_eq_add_p_mul (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    {ι : Type*} [Fintype ι] {w : ι → C♭} (hwN : ∀ i, w i ∈ N) (hw1 : ∀ i, ‖w i‖ ≤ 1)
    (hspan : ∀ x ∈ N, ∃ b : ι → K♭, x = ∑ i, b i • w i) {t r : ℝ} (ht : 0 < t)
    (hwr : ∀ i, r < ‖w i‖)
    (horth : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    {γ : 𝒪K♭} (hγ : ‖γ‖ ≤ t * r)
    {y : normInteger C} (hy : y ∈ untiltInteger K C p N) :
    ∃ v ∈ Submodule.span K (Set.range fun i => tiltSharp C p (w i)),
      ∃ y' ∈ untiltInteger K C p N,
        algebraMap K C ((PreTilt.untilt γ : normInteger K) : K) * (y : C) = v + (p : C) * y' := by
  classical
  set V := Submodule.span K (Set.range fun i => tiltSharp C p (w i))
  obtain ⟨a, ha, z', hz', rfl⟩ := exists_eq_untilt_add_p_mul hy
  set x : C♭ := algebraMap 𝒪C♭ C♭ a with hx
  have hxN : x ∈ N := (mem_integerTilt N).1 ha
  have hx1 : ‖x‖ ≤ 1 := by
    rw [hx, norm_algebraMap_preTilt]; exact preTilt_norm_le_one a
  obtain ⟨b, hb⟩ := hspan x hxN

  set g : K♭ := algebraMap 𝒪K♭ K♭ γ with hg
  have hgn : ‖g‖ = ‖γ‖ := norm_algebraMap_preTilt γ
  have hcb : ∀ i, ‖g * b i‖ ≤ 1 := by
    intro i
    have h1 : t * ‖b i • w i‖ ≤ ‖x‖ := by rw [hb]; exact horth b i
    rw [norm_smul] at h1
    have h2 : t * (‖b i‖ * r) ≤ 1 := by
      calc t * (‖b i‖ * r) ≤ t * (‖b i‖ * ‖w i‖) := by
            gcongr; exact (hwr i).le
        _ ≤ ‖x‖ := h1
        _ ≤ 1 := hx1
    rw [norm_mul, hgn]
    calc ‖γ‖ * ‖b i‖ ≤ t * r * ‖b i‖ := by gcongr
      _ = t * (‖b i‖ * r) := by ring
      _ ≤ 1 := h2
  choose β hβ using fun i => (norm_le_one_iff_exists_algebraMap (K := K) (p := p)).1 (hcb i)
  choose ω hω using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hw1 i)

  set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C)
  have hφ : ∀ e : 𝒪K♭, algebraMap K♭ C♭ (algebraMap 𝒪K♭ K♭ e) = algebraMap 𝒪C♭ C♭ (φ e) :=
    fun e => tiltMap_algebraMap _ _ e
  have hφmem : ∀ e : 𝒪K♭, φ e ∈ integerTilt K C p N := fun e => by
    rw [mem_integerTilt, ← hφ]; exact N.algebraMap_mem _
  have hωmem : ∀ i, ω i ∈ integerTilt K C p N := fun i => by
    rw [mem_integerTilt, hω]; exact hwN i

  have hid : φ γ * a = ∑ i, φ (β i) * ω i := by
    apply IsFractionRing.injective 𝒪C♭ C♭
    rw [map_mul, ← hφ, map_sum]
    simp only [map_mul, ← hφ, hω, hβ]
    rw [← hx, hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, hg]
    ring
  obtain ⟨z'', hz'', hsum⟩ := exists_untilt_sum_eq (N := N) Finset.univ
    (fun i => (⟨φ (β i) * ω i, mul_mem (hφmem _) (hωmem i)⟩ : integerTilt K C p N))
  refine ⟨∑ i, ((PreTilt.untilt (β i) : normInteger K) : K) • tiltSharp C p (w i),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
    z'' + PreTilt.untilt (φ γ) * z', add_mem hz'' (mul_mem (untilt_mem_untiltInteger (hφmem γ)) hz'),
    ?_⟩
  have hsum' := congrArg (fun q : normInteger C => (q : C)) hsum
  simp only at hsum'
  have hγa : ((PreTilt.untilt (φ γ * a) : normInteger C) : C) =
      algebraMap K C ((PreTilt.untilt γ : normInteger K) : K) *
        ((PreTilt.untilt a : normInteger C) : C) := by
    rw [map_mul, Subring.coe_mul, coe_untilt_preTiltMap]
  rw [hid] at hγa
  have hterm : ∀ i, ((PreTilt.untilt (φ (β i) * ω i) : normInteger C) : C) =
      ((PreTilt.untilt (β i) : normInteger K) : K) • tiltSharp C p (w i) := by
    intro i
    rw [map_mul, Subring.coe_mul, coe_untilt_preTiltMap, Algebra.smul_def, ← hω,
      tiltSharp_algebraMap]
  rw [Subring.coe_add, Subring.coe_mul, mul_add, ← hγa, hsum']
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, AddSubmonoidClass.coe_finsetSum,
    hterm]
  rw [show ((PreTilt.untilt (φ γ) : normInteger C) : C) =
    algebraMap K C ((PreTilt.untilt γ : normInteger K) : K) from coe_untilt_preTiltMap _ _ γ]
  ring
theorem coe_mem_span_of_mem_untiltInteger (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    {ι : Type*} [Fintype ι] {w : ι → C♭} (hwN : ∀ i, w i ∈ N) (hw1 : ∀ i, ‖w i‖ ≤ 1)
    (hspan : ∀ x ∈ N, ∃ b : ι → K♭, x = ∑ i, b i • w i) {t r : ℝ} (ht : 0 < t)
    (hwr : ∀ i, r < ‖w i‖) (htr : t * r ≤ 1)
    (horth : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hp : ‖(p : K)‖ < t * r) {z : normInteger C} (hz : z ∈ untiltInteger K C p N) :
    (z : C) ∈ Submodule.span K (Set.range fun i => tiltSharp C p (w i)) := by
  classical
  have := IsPerfectoidField.completeSpace (K := K) p
  set V := Submodule.span K (Set.range fun i => tiltSharp C p (w i)) with hVdef

  have htr0 : 0 < t * r := (norm_nonneg _).trans_lt hp
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioc (K := K♭) p
    (lt_max_of_lt_right (half_pos htr0)) (max_lt hp (half_lt_self htr0))
  obtain ⟨γ, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 (hc2.trans htr)
  rw [norm_algebraMap_preTilt] at hc1 hc2
  have hpγ : ‖(p : K)‖ < ‖γ‖ := (le_max_left _ _).trans_lt hc1
  set e : K := ((PreTilt.untilt γ : normInteger K) : K) with he
  have hen : ‖e‖ = ‖γ‖ := (preTilt_norm_def γ).symm
  have he0 : e ≠ 0 := by
    intro h; rw [h, norm_zero] at hen; linarith [norm_nonneg (p : K)]
  set πK : K := (p : K) / e
  have hπ : ‖πK‖ < 1 := by
    rw [norm_div, hen, div_lt_one ((norm_nonneg _).trans_lt hpγ)]; exact hpγ
  set π : C := algebraMap K C πK

  have step : ∀ y : normInteger C, y ∈ untiltInteger K C p N →
      ∃ v ∈ V, ∃ y' ∈ untiltInteger K C p N, (y : C) = v + π * y' := by
    intro y hy
    obtain ⟨v, hv, y', hy', hyv⟩ := exists_mul_eq_add_p_mul N hwN hw1 hspan ht hwr horth hc2 hy
    refine ⟨e⁻¹ • v, V.smul_mem _ hv, y', hy', ?_⟩
    have hae : algebraMap K C e ≠ 0 := (map_ne_zero _).2 he0
    rw [Algebra.smul_def, map_inv₀]
    simp only [π, πK, map_div₀, map_natCast]
    field_simp
    rw [← he] at hyv
    linear_combination hyv

  have iter : ∀ k : ℕ, ∃ v ∈ V, ∃ y' ∈ untiltInteger K C p N, (z : C) = v + π ^ k * y' := by
    intro k
    induction k with
    | zero => exact ⟨0, V.zero_mem, z, hz, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, y, hy, hzv⟩ := ih
      obtain ⟨v', hv', y', hy', hyv⟩ := step y hy
      refine ⟨v + πK ^ k • v', V.add_mem hv (V.smul_mem _ hv'), y', hy', ?_⟩
      rw [hzv, hyv, Algebra.smul_def, map_pow]
      ring
  choose v hv y hy hzv using iter
  have hVc : IsClosed (V : Set C) := by
    have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
    exact V.closed_of_finiteDimensional
  have hlim : Filter.Tendsto v Filter.atTop (nhds (z : C)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ)
    have : v k - (z : C) = -(π ^ k * y k) := by rw [hzv k]; ring
    rw [this, norm_neg, norm_mul, norm_pow, norm_algebraMap']
    calc ‖πK‖ ^ k * ‖((y k : normInteger C) : C)‖ ≤ ‖πK‖ ^ k * 1 := by
          gcongr; exact mem_normInteger.1 (y k).2
      _ = _ := mul_one _
  exact hVc.mem_of_tendsto hlim (Filter.Eventually.of_forall hv)
theorem untiltField_le_of_subset (N : IntermediateField K♭ C♭) (V : Submodule K C)
    [FiniteDimensional K V] (hV : ∀ z ∈ untiltInteger K C p N, (z : C) ∈ V) :
    ∀ y ∈ untiltField K C p N, y ∈ V := by
  classical
  set S : Set C := (↑) '' (untiltInteger K C p N : Set (normInteger C))
  let T : Submonoid C :=
    { carrier := S
      one_mem' := ⟨1, (untiltInteger K C p N).one_mem, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, (untiltInteger K C p N).mul_mem ha hb, rfl⟩ }
  have hA : Subalgebra.toSubmodule (Algebra.adjoin K S) ≤ V := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    have : x ∈ T := (Submonoid.closure_le (S := T)).2 le_rfl hx
    obtain ⟨z, hz, rfl⟩ := this
    exact hV z hz
  have : FiniteDimensional K (Algebra.adjoin K S) :=
    Submodule.finiteDimensional_of_le hA
  have halg : ∀ x ∈ S, IsAlgebraic K x := by
    intro x hx
    have hint : IsIntegral K (⟨x, Algebra.subset_adjoin hx⟩ : Algebra.adjoin K S) :=
      Algebra.IsIntegral.isIntegral _
    exact (hint.map (Algebra.adjoin K S).val).isAlgebraic
  intro y hy
  have hy' : y ∈ (IntermediateField.adjoin K S).toSubalgebra := hy
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg] at hy'
  exact hA hy'
theorem exists_untiltField_basis (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    ∃ (w : Fin (Module.finrank K♭ N) → C♭) (t r ρ : ℝ), 0 < t ∧ t < 1 ∧ 0 < r ∧ r < 1 ∧
      0 < ρ ∧ ρ < 1 ∧ ‖(p : K)‖ ≤ t * r * ρ ∧ (∀ i, w i ∈ N) ∧ (∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖) ∧
      (∀ x ∈ N, ∃ b : Fin (Module.finrank K♭ N) → K♭, x = ∑ i, b i • w i) ∧
      (∀ (c : Fin (Module.finrank K♭ N) → K♭) (i : Fin (Module.finrank K♭ N)),
        t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      (∀ (l : Fin (Module.finrank K♭ N) → K) (i : Fin (Module.finrank K♭ N)),
        t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖) ∧
      LinearIndependent K (fun i => tiltSharp C p (w i)) ∧
      (∀ y ∈ untiltField K C p N,
        y ∈ Submodule.span K (Set.range fun i => tiltSharp C p (w i))) := by
  classical
  set n := Module.finrank K♭ N
  set B := Module.finBasis K♭ N
  have hv : LinearIndependent K♭ (fun i => (B i : C♭)) :=
    B.linearIndependent.map' (IntermediateField.val N).toLinearMap
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  obtain ⟨w, t, r, ρ, ht0, ht1, hr0, hr1, hρ0, hρ1, hp, hli, hspanv, horth, hnorm, hest⟩ :=
    exists_tiltSharp_family (K := K) (C := C) hv
  have hwN : ∀ i, w i ∈ N := fun i => by
    have h := hspanv i
    have hle : Submodule.span K♭ (Set.range fun i => (B i : C♭)) ≤
        Subalgebra.toSubmodule N.toSubalgebra :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (B j).2)
    exact hle h

  let w' : Fin n → N := fun i => ⟨w i, hwN i⟩
  have hli' : LinearIndependent K♭ w' :=
    LinearIndependent.of_comp (IntermediateField.val N).toLinearMap hli
  have htop := hli'.span_eq_top_of_card_eq_finrank' (by simp [n])
  have hspan : ∀ x ∈ N, ∃ b : Fin n → K♭, x = ∑ i, b i • w i := by
    intro x hx
    have hmem : (⟨x, hx⟩ : N) ∈ Submodule.span K♭ (Set.range w') := by rw [htop]; trivial
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun K♭).1 hmem
    refine ⟨b, ?_⟩
    have := congrArg (fun u : N => (u : C♭)) hb
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, w'] at this
    exact this.symm
  have hptr : ‖(p : K)‖ < t * r := by
    calc ‖(p : K)‖ ≤ t * r * ρ := hp
      _ < t * r * 1 := by gcongr
      _ = t * r := mul_one _
  have htr : t * r ≤ 1 := by nlinarith
  have hsub : ∀ y ∈ untiltField K C p N,
      y ∈ Submodule.span K (Set.range fun i => tiltSharp C p (w i)) := by
    have : FiniteDimensional K (Submodule.span K (Set.range fun i => tiltSharp C p (w i))) :=
      FiniteDimensional.span_of_finite K (Set.finite_range _)
    exact untiltField_le_of_subset N _ fun z hz =>
      coe_mem_span_of_mem_untiltInteger N hwN (fun i => (hnorm i).1) hspan ht0
        (fun i => (hnorm i).2) htr horth hptr hz
  exact ⟨w, t, r, ρ, ht0, ht1, hr0, hr1, hρ0, hρ1, hp, hwN, hnorm, hspan, horth, hest,
    linearIndependent_tiltSharp horth (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0 hρ0
      hρ1 hp, hsub⟩
instance finiteDimensional_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    FiniteDimensional K (untiltField K C p N) := by
  obtain ⟨w, t, r, ρ, -, -, -, -, -, -, -, hwN, -, -, -, -, hli, hsub⟩ :=
    exists_untiltField_basis (K := K) (C := C) (p := p) N
  set V := Submodule.span K (Set.range fun i => tiltSharp C p (w i))
  have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
  let f : untiltField K C p N →ₗ[K] V :=
    { toFun := fun y => ⟨y, hsub y y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg Subtype.val h :)
end GroundTheory.PAdicHodge


