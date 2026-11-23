-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:17.812963+00:00
-- url     : https://prove2.me/theorems/5643c84c-a162-4e54-88c8-638857f60281
-- title:
--   Is Integral Cc
-- statement:
--   Definitions and structural lemmas for Is Integral Cc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsIntegralCc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
lemma cc_cc (x : E) : cc (cc x) = x := by
  simp [cc]
lemma cc_sub (x y : E) : cc (x - y) = cc x - cc y := by
  simp [cc]
lemma cc_one : cc (1 : E) = 1 := by
  simp [cc]
lemma cc_zero : cc (0 : E) = 0 := by
  simp [cc]
lemma emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by
  rw [cc]
  exact IsCMField.complexEmbedding_complexConj E τ x
lemma cc_eq_zero {x : E} (h : cc x = 0) : x = 0 := by
  have := congrArg cc h
  rwa [cc_cc, cc_zero] at this
lemma isIntegral_cc {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) := by
  have := hx.map (IsCMField.complexConj E).toAlgHom.toRatAlgHom
  exact this
lemma exists_imag : ∃ κ : E, cc κ = -κ ∧ κ ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x : E, cc x ≠ x := by
    by_contra hne
    push_neg at hne
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    apply InfinitePlace.isComplex_iff.mp (IsTotallyComplex.isComplex w)
    refine RingHom.ext fun y => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, ← emb_cc, hne y]
  refine ⟨x - cc x, ?_, ?_⟩
  · rw [cc_sub, cc_cc, neg_sub]
  · exact sub_ne_zero.mpr (Ne.symm hx)
lemma im_ne_zero {κ : E} (hκ : cc κ = -κ) (h0 : κ ≠ 0) (τ : E →+* ℂ) : (τ κ).im ≠ 0 := by
  intro him
  have h1 : conj (τ κ) = -(τ κ) := by rw [← emb_cc, hκ, map_neg]
  have h2 : conj (τ κ) = τ κ := Complex.conj_eq_iff_im.mpr him
  have h3 : τ κ = 0 := by
    have h4 : τ κ = -(τ κ) := h2.symm.trans h1
    linear_combination (1 / 2 : ℂ) * h4
  exact h0 ((map_eq_zero_iff τ τ.injective).mp h3)
def e1 : Fin 1 → E := fun _ => 1
lemma herm_one (x y : Fin 1 → E) : herm (1 : Matrix (Fin 1) (Fin 1) E) x y = x 0 * cc (y 0) := by
  simp [herm]
lemma stab_finite :
    {γ : GL (Fin 1) E | IsIntegral ℤ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0) ∧
      ∀ φ : E →+* ℂ, ‖φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0)‖ ≤ 1}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ (1 : ℝ)
  refine (hfin.preimage (f := fun γ : GL (Fin 1) E => (γ : Matrix (Fin 1) (Fin 1) E) 0 0) ?_).subset ?_
  · intro γ₁ _ γ₂ _ h
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    exact h
  · intro γ hγ
    exact hγ
noncomputable def inhab : Data E 1 := by
  classical
  let κ : E := (exists_imag (E := E)).choose
  have hκ : cc κ = -κ := (exists_imag (E := E)).choose_spec.1
  have hκ0 : κ ≠ 0 := (exists_imag (E := E)).choose_spec.2
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {(e1 : Fin 1 → E)}
  have memΛ : ∀ x, x ∈ Λ ↔ ∃ a : 𝓞 E, (a : E) = x 0 := by
    intro x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by simp [e1, Algebra.smul_def]⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      funext i
      fin_cases i
      simp [e1, Algebra.smul_def, ha]
  have hfin := stab_finite (E := E)
  exact
  { Ψ := Finset.univ.filter fun τ : E →+* ℂ => 0 < (τ κ).im
    cmType := by
      intro τ
      have h1 := im_ne_zero hκ hκ0 τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_im, not_lt, neg_nonpos]
      constructor
      · intro h; exact h.le
      · intro h; exact lt_of_le_of_ne h (Ne.symm h1)
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
      simp [gram, hermC, col, sgn, Matrix.one_apply]
    Λ := Λ
    Λ_fg := Submodule.fg_span_singleton _
    Λ_span := by
      rw [eq_top_iff]
      intro x _
      have hx : x = x 0 • (e1 : Fin 1 → E) := by
        funext i; fin_cases i; simp [e1]
      rw [hx]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Submodule.subset_span (Set.mem_singleton _)
    den := 1
    den_ne := one_ne_zero
    Λ_int := by
      intro x hx y hy
      obtain ⟨a, ha⟩ := (memΛ x).mp hx
      obtain ⟨b, hb⟩ := (memΛ y).mp hy
      rw [herm_one, ← ha, ← hb]
      rw [show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
      exact a.isIntegral_coe.mul (isIntegral_cc b.isIntegral_coe)
    Γ := ⊥
    Γ_stab := by
      intro γ hγ
      rw [Subgroup.mem_bot] at hγ
      subst hγ
      simp [IsUStab]
    Γ_index := by
      refine ⟨hfin.toFinset, ?_⟩
      intro γ hγ
      refine ⟨γ, ?_, by simp⟩
      rw [Set.Finite.mem_toFinset]
      obtain ⟨hh, hl⟩ := hγ
      have hmem : Matrix.mulVec (γ : Matrix (Fin 1) (Fin 1) E) e1 ∈ Λ :=
        (hl e1).mp (Submodule.subset_span (Set.mem_singleton _))
      have hv : Matrix.mulVec (γ : Matrix (Fin 1) (Fin 1) E) e1 0 = (γ : Matrix (Fin 1) (Fin 1) E) 0 0 := by
        simp [Matrix.mulVec, dotProduct, e1]
      obtain ⟨a, ha⟩ := (memΛ _).mp hmem
      rw [hv] at ha
      refine ⟨ha ▸ a.isIntegral_coe, ?_⟩
      intro φ
      have h1 := hh e1 e1
      rw [herm_one, herm_one, hv] at h1
      simp only [e1, cc_one, mul_one] at h1
      have h2 := congrArg φ h1
      rw [map_mul, emb_cc, map_one, Complex.mul_conj] at h2
      have h3 : ‖φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0)‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h2
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0))]
    Γ_free := by
      intro γ hγ _ _ _ _ _
      exact (Subgroup.mem_bot.mp hγ)
    χ := fun _ _ => 1
    χ_mul := by intros; simp
    χ_add := by intros; simp
    χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
    ξ0 := κ
    ξ0_im := hκ
    ξ0_ne := hκ0
    κ0 := -(2 * κ)
    κ0_xi := Or.inr rfl
    κ0_sign := by
      rintro ⟨τ, hτ⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
      simp only [map_neg, map_mul, map_ofNat, Complex.neg_im, Complex.mul_im]
      norm_num
      exact hτ
    m := 1
    m_pos := one_pos
    transv := by
      intro ξ _ hiso s _ _
      rw [herm_one] at hiso
      have hξ : ξ 0 = 0 := by
        rcases mul_eq_zero.mp hiso with h | h
        · exact h
        · exact cc_eq_zero h
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      fin_cases a; fin_cases b
      simp [transvMat, hξ] }
end ReciprocityTheory.ChartRestriction.G.FD


