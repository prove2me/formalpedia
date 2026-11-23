-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:09.42227+00:00
-- url     : https://prove2.me/theorems/90a27492-8f27-49fa-8d19-945dbf30ea2f
-- title:
--   First Raising Mem Equivariant
-- statement:
--   Definitions and structural lemmas for First Raising Mem Equivariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstRaisingMemEquivariant.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_cc_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)
namespace GlobalTheory
namespace GaussCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {ζ : E}
omit [NumberField E] [IsCMField E] in
theorem sq_eq (hζ : IsPrimitiveRoot ζ 4) : ζ * ζ = -1 := by
  have h : IsPrimitiveRoot (ζ ^ 2) 2 := hζ.pow (by norm_num) (by norm_num : 4 = 2 * 2)
  rw [← sq]; exact h.eq_neg_one_of_two_right
omit [NumberField E] [IsCMField E] in
theorem emb_eq (hζ : IsPrimitiveRoot ζ 4) (τ : E →+* ℂ) : τ ζ = Complex.I ∨ τ ζ = -Complex.I := by
  have h : τ ζ * τ ζ = Complex.I * Complex.I := by
    rw [← map_mul, sq_eq hζ, Complex.I_mul_I]; simp
  exact mul_self_eq_mul_self_iff.mp h
theorem cc_root (hζ : IsPrimitiveRoot ζ 4) : cc ζ = -ζ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [emb_cc, map_neg]
  rcases emb_eq hζ τ with h | h <;> simp [h]
theorem cc_add (x y : E) : cc (x + y) = cc x + cc y := map_add _ x y
theorem cc_intCast (n : ℤ) : cc (n : E) = n := map_intCast _ n
theorem cc_half_root (hζ : IsPrimitiveRoot ζ 4) : cc (ζ / 2) = -(ζ / 2) := by
  have h : cc (ζ / 2) = cc ζ / 2 := by
    unfold cc; rw [map_div₀, map_ofNat]
  rw [h, cc_root hζ]; ring
theorem trace_root (hζ : IsPrimitiveRoot ζ 4) : Algebra.trace ℚ E ζ = 0 := by
  have h := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) ζ
  have h2 : ((IsCMField.complexConj E).restrictScalars ℚ) ζ = -ζ := cc_root hζ
  rw [h2, map_neg] at h
  linarith
section Coords
variable [IsCyclotomicExtension {4} ℚ E]
omit [IsCMField E] in
theorem finrank_eq : Module.finrank ℚ E = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) E (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide
omit [IsCMField E] in

theorem exists_coords (hζ : IsPrimitiveRoot ζ 4) (a : 𝓞 E) :
    ∃ m n : ℤ, (a : E) = m + n * ζ := by
  have hmem : a ∈ Algebra.adjoin ℤ {hζ.integralPowerBasis.gen} := by
    rw [hζ.integralPowerBasis.adjoin_gen_eq_top]; trivial
  rw [hζ.integralPowerBasis_gen] at hmem
  have hs := sq_eq hζ
  induction hmem using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨0, 1, by simp only [Int.cast_zero, Int.cast_one, zero_add, one_mul]; rfl⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, h1⟩ := hx
    obtain ⟨c, d, h2⟩ := hy
    change algebraMap (𝓞 E) E x = _ at h1
    change algebraMap (𝓞 E) E y = _ at h2
    refine ⟨a + c, b + d, ?_⟩
    change algebraMap (𝓞 E) E (x + y) = _
    rw [map_add, h1, h2]
    push_cast
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, h1⟩ := hx
    obtain ⟨c, d, h2⟩ := hy
    change algebraMap (𝓞 E) E x = _ at h1
    change algebraMap (𝓞 E) E y = _ at h2
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    change algebraMap (𝓞 E) E (x * y) = _
    rw [map_mul, h1, h2]
    push_cast
    linear_combination (b * d : E) * hs
theorem trace_form (hζ : IsPrimitiveRoot ζ 4) (a b c d : ℤ) :
    Algebra.trace ℚ E (-(ζ / 2) * (((a : E) + b * ζ) * cc ((c : E) + d * ζ))) =
      ((b * c - a * d : ℤ) : ℚ) := by
  have hs := sq_eq hζ
  have h : -(ζ / 2) * (((a : E) + b * ζ) * cc ((c : E) + d * ζ)) =
      algebraMap ℚ E (((b * c - a * d : ℤ) : ℚ) / 2) +
        (-(((a * c + b * d : ℤ) : ℚ) / 2)) • ζ := by
    rw [cc_add, cc_mul, cc_intCast, cc_intCast, cc_root hζ, Algebra.smul_def]
    simp only [map_div₀, map_intCast, map_neg, map_ofNat]
    push_cast
    linear_combination (-(b * c - a * d : E) / 2 + b * d * ζ / 2) * hs
  rw [h, map_add, map_smul, trace_root hζ, Algebra.trace_algebraMap, finrank_eq]
  simp only [smul_zero, add_zero, nsmul_eq_mul]
  push_cast
  ring
end Coords
def intLat (E : Type) [Field E] : Submodule (𝓞 E) (Fin 1 → E) :=
  Submodule.span (𝓞 E) {(e1 : Fin 1 → E)}
omit [NumberField E] [IsCMField E] in
theorem mem_intLat (x : Fin 1 → E) : x ∈ intLat E ↔ ∃ a : 𝓞 E, (a : E) = x 0 := by
  rw [intLat, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp [e1, Algebra.smul_def]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    funext i
    fin_cases i
    simp [e1, Algebra.smul_def, ha]
omit [NumberField E] [IsCMField E] in
theorem mem_intLat_iff (x : Fin 1 → E) : x ∈ intLat E ↔ IsIntegral ℤ (x 0) := by
  rw [mem_intLat]
  constructor
  · rintro ⟨a, ha⟩; exact ha ▸ a.isIntegral_coe
  · intro h; exact ⟨⟨x 0, h⟩, rfl⟩
omit [NumberField E] [IsCMField E] in
theorem first_raising_mem_equivariant : (e1 : Fin 1 → E) ∈ intLat E := Submodule.subset_span (Set.mem_singleton _)
theorem herm_int {x y : Fin 1 → E} (hx : x ∈ intLat E) (hy : y ∈ intLat E) :
    IsIntegral ℤ (herm (1 : Matrix (Fin 1) (Fin 1) E) x y) := by
  rw [herm_one]
  exact ((mem_intLat_iff x).mp hx).mul (isIntegral_cc ((mem_intLat_iff y).mp hy))
theorem eq_zero_of_iso {ξ : Fin 1 → E} (h : herm (1 : Matrix (Fin 1) (Fin 1) E) ξ ξ = 0) :
    ξ = 0 := by
  rw [herm_one] at h
  funext i
  fin_cases i
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact cc_eq_zero h
omit [NumberField E] [IsCMField E] in
theorem mulVec_firstBasisVector (γ : Matrix (Fin 1) (Fin 1) E) : Matrix.mulVec γ e1 0 = γ 0 0 := by
  simp [Matrix.mulVec, dotProduct, e1]
theorem norm_entry {γ : GL (Fin 1) E} (hγ : IsUStab 1 (intLat E) γ) (φ : E →+* ℂ) :
    ‖φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0)‖ = 1 := by
  have h1 := hγ.1 e1 e1
  rw [herm_one, herm_one, mulVec_firstBasisVector] at h1
  simp only [e1, cc_one, mul_one] at h1
  have h2 := congrArg φ h1
  rw [map_mul, emb_cc, map_one, Complex.mul_conj] at h2
  have h3 : ‖φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h2
  nlinarith [norm_nonneg (φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0))]
theorem eq_one_of_cong {γ : GL (Fin 1) E} (hγ : IsUStab 1 (intLat E) γ)
    (h : ∀ x ∈ intLat E, ∃ y ∈ intLat E,
      Matrix.mulVec (γ : Matrix (Fin 1) (Fin 1) E) x - x = ((3 : ℕ) : E) • y) : γ = 1 := by
  obtain ⟨y, hy, hyy⟩ := h e1 first_raising_mem_equivariant
  obtain ⟨a, ha⟩ := (mem_intLat y).mp hy
  have h0 := congrFun hyy 0
  simp only [Pi.sub_apply, mulVec_firstBasisVector, Pi.smul_apply, smul_eq_mul, ← ha] at h0
  have he : (e1 : Fin 1 → E) 0 = 1 := rfl
  rw [he] at h0
  have ha0 : a = 0 := by
    by_contra hne
    obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hne
    have h1 := norm_entry hγ σ
    have h2 := congrArg (fun z => ‖σ z‖) h0
    simp only [map_sub, map_mul, map_natCast, map_one, norm_mul, Complex.norm_natCast] at h2
    have h3 := norm_sub_le (σ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0)) 1
    rw [h2, h1, norm_one] at h3
    change 1 ≤ ‖σ (a : E)‖ at hσ
    push_cast at h3
    linarith
  rw [ha0] at h0
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simpa [sub_eq_zero] using h0
open Classical in

noncomputable def data (hζ : IsPrimitiveRoot ζ 4) : Data E 1 where
  Ψ := Finset.univ.filter fun τ : E →+* ℂ => 0 < (τ ζ).im
  cmType := by
    intro τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ComplexEmbedding.conjugate_coe_eq,
      Complex.conj_im, not_lt, neg_nonpos]
    rcases emb_eq hζ τ with h | h <;> norm_num [h]
  Gm := 1
  Gm_herm := by
    intro a b
    fin_cases a; fin_cases b
    simp [cc_one]
  Gm_det := by simp
  p0 := 1
  p0_le := le_rfl
  signature := by
    intro τ
    refine ⟨1, by simp, ?_⟩
    ext a b
    fin_cases a; fin_cases b
    simp [gram, hermC, col, sgn]
  Λ := intLat E
  Λ_fg := Submodule.fg_span_singleton _
  Λ_span := by
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • (e1 : Fin 1 → E) := by
      funext i; fin_cases i; simp [e1]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span first_raising_mem_equivariant)
  den := 1
  den_ne := one_ne_zero
  Λ_int := by
    intro x hx y hy
    rw [show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
    exact herm_int hx hy
  Γ := ⊥
  Γ_stab := by
    intro γ hγ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    simp [IsUStab]
  Γ_index := by
    refine ⟨(stab_finite (E := E)).toFinset, ?_⟩
    intro γ hγ
    refine ⟨γ, ?_, by simp⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, fun φ => (norm_entry hγ φ).le⟩
    have h := (mem_intLat_iff _).mp ((hγ.2 e1).mp first_raising_mem_equivariant)
    rwa [mulVec_firstBasisVector] at h
  Γ_free := by
    intro γ hγ _ _ _ _ _
    exact (Subgroup.mem_bot.mp hγ)
  χ := fun _ _ => 1
  χ_mul := by intros; simp
  χ_add := by intros; simp
  χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
  ξ0 := ζ / 2
  ξ0_im := cc_half_root hζ
  ξ0_ne := div_ne_zero (hζ.ne_zero (by norm_num)) two_ne_zero
  κ0 := -ζ
  κ0_xi := Or.inr (by ring)
  κ0_sign := by
    rintro ⟨τ, hτ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    simpa using hτ
  m := 1
  m_pos := one_pos
  transv := by
    intro ξ _ hiso s _ _
    rw [eq_zero_of_iso hiso]
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    ext a b
    fin_cases a; fin_cases b
    simp [transvMat]
noncomputable def dataX [IsCyclotomicExtension {4} ℚ E] (hζ : IsPrimitiveRoot ζ 4) :
    DataX E 1 where
  toData := data hζ
  k0 := 1
  minWeight_pos := one_pos
  k0_le := one_le_two
  ξ0_abs := by
    intro τ
    change ‖τ.1 (ζ / 2)‖ = 1 / 2
    rw [map_div₀, map_ofNat, norm_div]
    rcases emb_eq hζ τ.1 with h | h <;> simp [h]
  EF_int := by
    intro x hx y hy
    obtain ⟨u, hu⟩ := (mem_intLat x).mp hx
    obtain ⟨w, hw⟩ := (mem_intLat y).mp hy
    obtain ⟨a, b, hab⟩ := exists_coords hζ u
    obtain ⟨c, d, hcd⟩ := exists_coords hζ w
    refine ⟨b * c - a * d, ?_⟩
    change Algebra.trace ℚ E (-(ζ / 2) * herm 1 x y) = _
    rw [herm_one, ← hu, ← hw, hab, hcd, trace_form hζ]
  EF_perf := by
    intro (φ : intLat E →+ ℤ)
    have hz : IsIntegral ℤ ζ := hζ.isIntegral (by norm_num)
    let u : intLat E := ⟨e1, first_raising_mem_equivariant⟩
    let w : intLat E := ⟨fun _ => ζ, (mem_intLat_iff _).mpr hz⟩
    refine ⟨fun _ => ((-φ w : ℤ) : E) + (φ u : ℤ) * ζ, (mem_intLat_iff _).mpr ?_, ?_⟩
    · exact (isIntegral_intCast _).add ((isIntegral_intCast _).mul hz)
    · intro (y : intLat E)
      obtain ⟨v, hv⟩ := (mem_intLat y.1).mp y.2
      obtain ⟨c, d, hcd⟩ := exists_coords hζ v
      have hy : y = c • u + d • w := by
        apply Subtype.ext
        funext i
        fin_cases i
        change y.1 0 = c • (1 : E) + d • ζ
        rw [← hv, hcd]; simp
      have hφ : φ y = c * φ u + d * φ w := by
        rw [hy]
        exact (map_add φ _ _).trans (by rw [map_zsmul, map_zsmul]; simp)
      change ((φ y : ℤ) : ℚ) = Algebra.trace ℚ E (-(ζ / 2) * herm 1 _ y.1)
      rw [herm_one, ← hv, hcd, trace_form hζ, hφ]
      push_cast
      ring
  L' := intLat E
  L'_fg := Submodule.fg_span_singleton _
  L'_int := fun _ hx _ hy => herm_int hx hy
  L'_dual := by
    intro x hx
    have h := hx e1 first_raising_mem_equivariant
    change IsIntegral ℤ (herm 1 x e1) at h
    rw [herm_one] at h
    simp only [e1, cc_one, mul_one] at h
    exact (mem_intLat_iff x).mpr h
  NA := 1
  NC := 1
  NA_pos := one_pos
  NC_pos := one_pos
  NA_sub := by intro x hx; rw [Nat.cast_one, one_smul]; exact hx
  NC_sub := by intro x hx; rw [Nat.cast_one, one_smul]; exact hx
  g := 3
  g_pos := by norm_num
  cong := fun γ hγ h => Subgroup.mem_bot.mpr (eq_one_of_cong hγ h)
noncomputable def coordProd {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 1) : ℂ := ∏ τ, x τ 0 0
end GaussCusp
noncomputable def gaussCuspData : DataX E4 1 :=
  GaussCusp.dataX (IsCyclotomicExtension.zeta_spec 4 ℚ E4)
end GlobalTheory


