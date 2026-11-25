-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:38.690808+00:00
-- url     : https://prove2.me/theorems/6387247a-8d06-4447-bf85-ade39b46fac7
-- title:
--   Eq Zero Of Herm One
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Herm One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EqZeroOfHermOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
namespace GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem herm_one_two (x y : Fin 2 → E) :
    herm (1 : Matrix (Fin 2) (Fin 2) E) x y = x 0 * cc (y 0) + x 1 * cc (y 1) := by
  simp [herm, Fin.sum_univ_two, Matrix.one_apply]
theorem emb_herm_one (φ : E →+* ℂ) (x : Fin 2 → E) :
    φ (herm (1 : Matrix (Fin 2) (Fin 2) E) x x) = ((‖φ (x 0)‖ ^ 2 + ‖φ (x 1)‖ ^ 2 : ℝ) : ℂ) := by
  rw [herm_one_two, map_add, map_mul, map_mul, emb_cc, emb_cc, Complex.mul_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring
theorem eq_zero_of_herm_one (x : Fin 2 → E) (h : herm (1 : Matrix (Fin 2) (Fin 2) E) x x = 0) :
    x = 0 := by
  obtain ⟨φ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have h1 := emb_herm_one φ x
  rw [h, map_zero] at h1
  have h2 : ‖φ (x 0)‖ ^ 2 + ‖φ (x 1)‖ ^ 2 = 0 := by exact_mod_cast h1.symm
  have hsq0 := sq_nonneg ‖φ (x 0)‖
  have hsq1 := sq_nonneg ‖φ (x 1)‖
  have hx0 : x 0 = 0 := by
    have h3 : ‖φ (x 0)‖ ^ 2 = 0 := by linarith
    simpa using h3
  have hx1 : x 1 = 0 := by
    have h3 : ‖φ (x 1)‖ ^ 2 = 0 := by linarith
    simpa using h3
  funext i
  fin_cases i <;> simp [hx0, hx1]
omit [IsCMField E] in
theorem bounded_finite :
    {γ : GL (Fin 2) E | ∀ a b, IsIntegral ℤ ((γ : Matrix (Fin 2) (Fin 2) E) a b) ∧
      ∀ φ : E →+* ℂ, ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) a b)‖ ≤ 1}.Finite := by
  have hS := NumberField.Embeddings.finite_of_norm_le E ℂ 1
  have hpi : (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 1}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hS
  refine Set.Finite.subset
    (Set.Finite.preimage (f := fun (γ : GL (Fin 2) E) (a b : Fin 2) => (γ : Matrix (Fin 2) (Fin 2) E) a b)
      (fun γ _ δ _ hγδ => Units.ext (Matrix.ext fun a b => congrFun (congrFun hγδ a) b)) hpi) ?_
  intro γ hγ
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  intro a b
  exact ⟨(hγ a b).1, (hγ a b).2⟩
def intLat (E : Type) [Field E] : Submodule (𝓞 E) (Fin 2 → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
omit [NumberField E] [IsCMField E] in
theorem mem_intLat (x : Fin 2 → E) : x ∈ intLat E ↔ ∀ a, IsIntegral ℤ (x a) := by
  simp only [intLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y
omit [NumberField E] [IsCMField E] in
theorem single_mem_intLat (b : Fin 2) : (Pi.single b 1 : Fin 2 → E) ∈ intLat E := by
  rw [mem_intLat]
  intro a
  by_cases hab : a = b
  · subst hab
    simp [isIntegral_one]
  · simp [hab, isIntegral_zero]
noncomputable def defData (E : Type) [Field E] [NumberField E] [IsCMField E] : Data E 2 where
  Ψ := (inhab (E := E)).Ψ
  cmType := (inhab (E := E)).cmType
  Gm := 1
  Gm_herm := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [cc_one, cc_zero]
  Gm_det := by simp
  p0 := 2
  p0_le := le_rfl
  signature := by
    intro τ
    refine ⟨1, by simp, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, sgn, Matrix.one_apply]
  Λ := intLat E
  Λ_fg := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  Λ_span := by
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → E) + x 1 • (Pi.single 1 1 : Fin 2 → E) := by
      funext i; fin_cases i <;> simp
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_intLat 0)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_intLat 1)))
  den := 1
  den_ne := one_ne_zero
  Λ_int := by
    intro x hx y hy
    rw [mem_intLat] at hx hy
    rw [herm_one_two, show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
    exact ((hx 0).mul (isIntegral_cc (hy 0))).add ((hx 1).mul (isIntegral_cc (hy 1)))
  Γ := ⊥
  Γ_stab := by
    intro γ hγ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    simp [IsUStab]
  Γ_index := by
    refine ⟨(bounded_finite (E := E)).toFinset, ?_⟩
    intro γ hγ
    refine ⟨γ, ?_, by simp⟩
    rw [Set.Finite.mem_toFinset]
    obtain ⟨hh, hl⟩ := hγ
    intro a b
    have hmem := (mem_intLat _).mp ((hl _).mp (single_mem_intLat b))
    have hv : ∀ c, Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) E) (Pi.single b 1) c =
        (γ : Matrix (Fin 2) (Fin 2) E) c b := by
      intro c; simp
    refine ⟨hv a ▸ hmem a, fun φ => ?_⟩
    have h1 := congrArg φ (hh (Pi.single b 1) (Pi.single b 1))
    rw [emb_herm_one, emb_herm_one, hv, hv] at h1
    have h2 : ‖φ ((Pi.single b 1 : Fin 2 → E) 0)‖ ^ 2 + ‖φ ((Pi.single b 1 : Fin 2 → E) 1)‖ ^ 2 = 1 := by
      fin_cases b <;> simp
    rw [h2] at h1
    have h3 : ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) 0 b)‖ ^ 2 +
      ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) 1 b)‖ ^ 2 = 1 := by exact_mod_cast h1
    have h4 : ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) a b)‖ ^ 2 ≤ 1 := by
      fin_cases a
      · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) 1 b)‖]
      · simp only [Fin.mk_one]; nlinarith [sq_nonneg ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) 0 b)‖]
    nlinarith [norm_nonneg (φ ((γ : Matrix (Fin 2) (Fin 2) E) a b))]
  Γ_free := fun γ hγ _ _ _ _ _ => Subgroup.mem_bot.mp hγ
  χ := fun _ _ => 1
  χ_mul := by intros; simp
  χ_add := by intros; simp
  χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
  ξ0 := (inhab (E := E)).ξ0
  ξ0_im := (inhab (E := E)).ξ0_im
  ξ0_ne := (inhab (E := E)).ξ0_ne
  κ0 := (inhab (E := E)).κ0
  κ0_xi := (inhab (E := E)).κ0_xi
  κ0_sign := (inhab (E := E)).κ0_sign
  m := 1
  m_pos := one_pos
  transv := by
    intro ξ _ hiso s _ _
    have hξ := eq_zero_of_herm_one ξ hiso
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    ext a b
    simp [transvMat, hξ, Matrix.one_apply]
end GlobalTheory.TwoLines


