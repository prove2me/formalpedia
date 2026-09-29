-- Prove2me | solution 1 for AutomorphicForm.archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e8ffaa20-3b2d-5416-b2eb-e14367b7fb04

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicVolume MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.TranslateSpanOccurrence"

open scoped Classical ENNReal NNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCuspRealizationAt finiteAdelicGL2Subgroup lsXiMemberAt_iff CarrierPins productionPinsOf AdelicGL2 centralScalar IsLsXiFunction HeckeEigensystem not_ae_zero_restrict_of_continuous_of_mem_interior SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre"
p2m_open "AutomorphicForm"

namespace DetFloor

variable {F : Type} [Field F] [NumberField F]

local instance instMS : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
local instance instBS : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
local instance instHaar : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

abbrev μH (F : Type) [Field F] [NumberField F] : Measure (AdelicGL2 (𝓞 F) F) :=
  AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F

def sqm (φ : AdelicGL2 (𝓞 F) F → ℂ) (A : Set (AdelicGL2 (𝓞 F) F)) : ℝ≥0∞ :=
  ∫⁻ g in A, ((‖φ g‖₊ : ℝ≥0∞) ^ 2) ∂(μH F)

theorem measurable_sq_nnnorm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) :
    Measurable fun g => ((‖φ g‖₊ : ℝ≥0∞) ^ 2) :=
  (hφ.measurable.nnnorm.coe_nnreal_ennreal).pow_const 2

theorem sqm_mono (φ : AdelicGL2 (𝓞 F) F → ℂ) {A B : Set (AdelicGL2 (𝓞 F) F)} (h : A ⊆ B) : sqm φ A ≤ sqm φ B :=
  lintegral_mono_set h

theorem archComponent_centralScalar_archCentralUnit (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) (i j : Fin 2) :
    ((archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a))) :
        GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = if i = j then ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v else 0 := by
  simp only [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h; rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]; rfl

def centralEntry (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) : v.Completion :=
  ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v

theorem centralEntry_self (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) : centralEntry v₀ v₀ a = a :=
  archCentralUnit_fst_self v₀ a

theorem centralEntry_of_ne {v₀ v : InfinitePlace F} (a : (v₀.Completion)ˣ) (h : v ≠ v₀) : centralEntry v₀ v a = 1 :=
  archCentralUnit_fst_of_ne v₀ a h

theorem centralEntry_ne_zero (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) : centralEntry v₀ v a ≠ 0 :=
  archCentralUnit_fst_ne_zero v₀ a v

theorem localHeight_cS_mul (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)))
      = localHeight (archComponent F v (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  have h := archComponent_centralScalar_archCentralUnit v₀ v a
  exact localHeight_scalar_entries_mul (centralEntry_ne_zero v₀ v a)
    (by rw [h, if_pos rfl]; rfl) (by rw [h, if_neg (by decide)]) (by rw [h, if_neg (by decide)])
    (by rw [h, if_pos rfl]; rfl) _

theorem xWindowSq_cS_mul (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    xWindowSq (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)))
      = xWindowSq (archComponent F v (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  have h := archComponent_centralScalar_archCentralUnit v₀ v a
  exact xWindowSq_scalar_entries_mul (centralEntry_ne_zero v₀ v a)
    (by rw [h, if_pos rfl]; rfl) (by rw [h, if_neg (by decide)]) (by rw [h, if_neg (by decide)])
    (by rw [h, if_pos rfl]; rfl) _

theorem archDetNorm_cS_mul (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)
      = ‖centralEntry v₀ v a‖ * ‖centralEntry v₀ v a‖ * archDetNorm v g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  have h := archComponent_centralScalar_archCentralUnit v₀ v a
  rw [Matrix.det_fin_two, h, h, h, h]
  simp [norm_mul, centralEntry]

theorem archDetNorm_cS_mul_self (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v₀ (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)
      = ‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖ * archDetNorm v₀ g := by
  rw [archDetNorm_cS_mul, centralEntry_self]

theorem archDetNorm_cS_mul_of_ne {v₀ v : InfinitePlace F} (h : v ≠ v₀) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g) = archDetNorm v g := by
  rw [archDetNorm_cS_mul, centralEntry_of_ne a h, norm_one, one_mul, one_mul]

theorem cS_pow_facts (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) (n : ℕ) (g : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F ((archCentralUnit F v₀ a) ^ n) * g) = glFin (𝓞 F) F g ∧
    (∀ v, localHeight (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F ((archCentralUnit F v₀ a) ^ n) * g)))
        = localHeight (archComponent F v (glArch (𝓞 F) F g))) ∧
    (∀ v, xWindowSq (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F ((archCentralUnit F v₀ a) ^ n) * g)))
        = xWindowSq (archComponent F v (glArch (𝓞 F) F g))) ∧
    archDetNorm v₀ (centralScalar (𝓞 F) F ((archCentralUnit F v₀ a) ^ n) * g)
        = (‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖) ^ n * archDetNorm v₀ g ∧
    (∀ v, v ≠ v₀ → archDetNorm v (centralScalar (𝓞 F) F ((archCentralUnit F v₀ a) ^ n) * g) = archDetNorm v g) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    have hsplit : centralScalar (𝓞 F) F ((archCentralUnit F v₀ a) ^ (n + 1)) * g
        = centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * (centralScalar (𝓞 F) F ((archCentralUnit F v₀ a) ^ n) * g) := by
      rw [pow_succ', map_mul, mul_assoc]
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih g
    refine ⟨?_, fun v => ?_, fun v => ?_, ?_, fun v hv => ?_⟩
    · rw [hsplit, map_mul, glFin_centralScalar_archCentralUnit, one_mul, h1]
    · rw [hsplit, localHeight_cS_mul, h2]
    · rw [hsplit, xWindowSq_cS_mul, h3]
    · rw [hsplit, archDetNorm_cS_mul_self, h4, pow_succ]; ring
    · rw [hsplit, archDetNorm_cS_mul_of_ne hv, h5 v hv]

omit [NumberField F] in
theorem norm_ratCast_completion (v : InfinitePlace F) (q : ℚ) : ‖((q : v.Completion))‖ = |(q : ℝ)| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
    map_ratCast, Complex.norm_ratCast]

omit [NumberField F] in

theorem exists_unit_norm_mul_norm_eq (v : InfinitePlace F) {q : ℚ} (hq : 0 < q) :
    ∃ a : (v.Completion)ˣ, ‖(a : v.Completion)‖ * ‖(a : v.Completion)‖ = (q : ℝ) ^ 2 := by
  have hn : ‖((q : v.Completion))‖ = (q : ℝ) := by
    rw [norm_ratCast_completion, abs_of_pos (by exact_mod_cast hq)]
  have h0 : (q : v.Completion) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact (ne_of_gt (by exact_mod_cast hq : (0 : ℝ) < q)) hn.symm
  exact ⟨Units.mk0 _ h0, by rw [Units.val_mk0, hn, sq]⟩

theorem exists_rat_sq_mem_Icc {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ q : ℚ, 0 < q ∧ a ≤ (q : ℝ) ^ 2 ∧ (q : ℝ) ^ 2 ≤ b := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Real.sqrt_lt_sqrt ha.le hab)
  have hqpos : (0 : ℝ) < q := (Real.sqrt_pos.mpr ha).trans hq1
  refine ⟨q, by exact_mod_cast hqpos, ?_, ?_⟩
  · calc a = Real.sqrt a ^ 2 := (Real.sq_sqrt ha.le).symm
      _ ≤ (q : ℝ) ^ 2 := by gcongr
  · calc (q : ℝ) ^ 2 ≤ Real.sqrt b ^ 2 := by gcongr
      _ = b := Real.sq_sqrt (ha.le.trans hab.le)

theorem exists_rat_sq_mem_Ico {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ q : ℚ, 0 < q ∧ a ≤ (q : ℝ) ^ 2 ∧ (q : ℝ) ^ 2 < b := by
  obtain ⟨q, hq, h1, h2⟩ := exists_rat_sq_mem_Icc ha (show a < (a + b) / 2 by linarith)
  exact ⟨q, hq, h1, by linarith⟩

theorem exists_central_adjust (g : AdelicGL2 (𝓞 F) F) {e₁ e₂ : ℝ} (he₁ : 0 < e₁) (he : e₁ < e₂)
    (P : Finset (InfinitePlace F)) :
    ∃ z : (AdeleRing (𝓞 F) F)ˣ,
      glFin (𝓞 F) F (centralScalar (𝓞 F) F z) = 1 ∧
      (∀ v, localHeight (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F z * g)))
          = localHeight (archComponent F v (glArch (𝓞 F) F g))) ∧
      (∀ v, xWindowSq (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F z * g)))
          = xWindowSq (archComponent F v (glArch (𝓞 F) F g))) ∧
      (∀ v ∈ P, archDetNorm v (centralScalar (𝓞 F) F z * g) ∈ Set.Icc e₁ e₂) ∧
      (∀ v ∉ P, archDetNorm v (centralScalar (𝓞 F) F z * g) = archDetNorm v g) := by
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨1, by rw [map_one, map_one], fun v => by rw [map_one, one_mul],
      fun v => by rw [map_one, one_mul], fun v hv => (Finset.notMem_empty v hv).elim,
      fun v _ => by rw [map_one, one_mul]⟩
  | insert v₀ P hv₀ ih =>
    obtain ⟨z, hzfin, hzh, hzx, hzP, hznP⟩ := ih
    set g' := centralScalar (𝓞 F) F z * g with hg'
    have hr : 0 < archDetNorm v₀ g' := archDetNorm_pos v₀ g'
    obtain ⟨q, hq, hq1, hq2⟩ := exists_rat_sq_mem_Icc (div_pos he₁ hr) ((div_lt_div_iff_of_pos_right hr).mpr he)
    obtain ⟨a, ha⟩ := exists_unit_norm_mul_norm_eq v₀ hq
    have hcs : centralScalar (𝓞 F) F (archCentralUnit F v₀ a * z) * g
        = centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g' := by
      rw [map_mul, mul_assoc]
    refine ⟨archCentralUnit F v₀ a * z, ?_, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, map_mul, glFin_centralScalar_archCentralUnit, one_mul, hzfin]
    · intro v; rw [hcs, localHeight_cS_mul, hg', hzh]
    · intro v; rw [hcs, xWindowSq_cS_mul, hg', hzx]
    · intro v hv
      rw [hcs]
      rcases Finset.mem_insert.mp hv with rfl | hv
      · rw [archDetNorm_cS_mul_self, ha]
        exact ⟨(div_le_iff₀ hr).mp hq1, (le_div_iff₀ hr).mp hq2⟩
      · have hne : v ≠ v₀ := fun h => hv₀ (h ▸ hv)
        rw [archDetNorm_cS_mul_of_ne hne]
        exact hzP v hv
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [hcs, archDetNorm_cS_mul_of_ne hv.1]
      exact hznP v hv.2

theorem coversModCentre_raise {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    {e₁ : ℝ} (he₁ : 0 < e₁) (he : e₁ < d₂) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u e₁ d₂) := by
  intro g
  obtain ⟨γ, z, hmem⟩ := hcov g
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨x, hx, s, hs, hsx⟩ := hmem
  obtain ⟨hfin, hh, hxw, -⟩ := mem_centreCutSiegelSet_iff.mp hs
  obtain ⟨z', hz'fin, hz'h, hz'x, hz'P, -⟩ := exists_central_adjust s he₁ he Finset.univ
  refine ⟨γ, z * z', ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨x, hx, centralScalar (𝓞 F) F z' * s, ?_, ?_⟩
  · rw [mem_centreCutSiegelSet_iff]
    refine ⟨?_, fun v => ?_, fun v => ?_, fun v => hz'P v (Finset.mem_univ v)⟩
    · rw [map_mul, hz'fin, one_mul]; exact hfin
    · rw [hz'h]; exact hh v
    · rw [hz'x]; exact hxw v
  · rw [map_mul, ← mul_assoc, ← hsx, mul_centralScalar_comm z' (s * x), mul_assoc]

section Realizations

variable (F)

abbrev pinsOf (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

variable {F}

theorem memLp_of_realization {D : Set (AdelicGL2 (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F (pinsOf F D) Φ) : MemLp R.toFun 2 ((μH F).restrict D) :=
  ((lsXiMemberAt_iff (𝓞 F) F (μH F) ⊤ R.centralChar D R.toFun).mp R.smoothCusp.1.1).2

theorem isLsXi_of_realization {D : Set (AdelicGL2 (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F (pinsOf F D) Φ) : IsLsXiFunction (𝓞 F) F ⊤ R.centralChar R.toFun :=
  ((lsXiMemberAt_iff (𝓞 F) F (μH F) ⊤ R.centralChar D R.toFun).mp R.smoothCusp.1.1).1

def transport {D₁ D₂ : Set (AdelicGL2 (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F (pinsOf F D₁) Φ) (hL2 : MemLp R.toFun 2 ((μH F).restrict D₂)) :
    SmoothCuspRealizationAt F (pinsOf F D₂) Φ where
  toFun := R.toFun
  exists_ne_zero := R.exists_ne_zero
  centralChar := R.centralChar
  smoothCusp :=
    ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (μH F) ⊤ R.centralChar D₂ R.toFun).mpr ⟨isLsXi_of_realization R, hL2⟩,
      R.smoothCusp.1.2⟩, R.smoothCusp.2⟩
  level_invariant := R.level_invariant
  exceptionalSet := R.exceptionalSet
  hecke_eigen := R.hecke_eigen
  central_eigen := R.central_eigen

@[scoped simp] theorem transport_toFun {D₁ D₂ : Set (AdelicGL2 (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F (pinsOf F D₁) Φ) (hL2 : MemLp R.toFun 2 ((μH F).restrict D₂)) :
    (transport R hL2).toFun = R.toFun := rfl

@[scoped simp] theorem transport_centralChar {D₁ D₂ : Set (AdelicGL2 (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F (pinsOf F D₁) Φ) (hL2 : MemLp R.toFun 2 ((μH F).restrict D₂)) :
    (transport R hL2).centralChar = R.centralChar := rfl

private def _root_.AutomorphicForm.DetFloor.restrict {D₁ D₂ : Set (AdelicGL2 (𝓞 F) F)} (h : D₂ ⊆ D₁) {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F (pinsOf F D₁) Φ) : SmoothCuspRealizationAt F (pinsOf F D₂) Φ :=
  transport R ((memLp_of_realization R).mono_measure (Measure.restrict_mono h le_rfl))

p2m_export "AutomorphicForm.DetFloor" "restrict"
end Realizations

theorem sqm_lt_top_of_memLp {φ : AdelicGL2 (𝓞 F) F → ℂ} {A : Set (AdelicGL2 (𝓞 F) F)}
    (h : MemLp φ 2 ((μH F).restrict A)) : sqm φ A < ⊤ := by
  have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by simp) h.2
  have hto : (2 : ℝ≥0∞).toReal = 2 := by simp
  unfold sqm
  convert h2 using 2 with g
  funext g
  rw [hto, ENNReal.rpow_two, enorm_eq_nnnorm]

theorem memLp_of_sqm_lt_top {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) {A : Set (AdelicGL2 (𝓞 F) F)}
    (h : sqm φ A < ⊤) : MemLp φ 2 ((μH F).restrict A) := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)]
  have hto : (2 : ℝ≥0∞).toReal = 2 := by simp
  unfold sqm at h
  convert h using 2 with g
  funext g
  rw [hto, ENNReal.rpow_two, enorm_eq_nnnorm]

theorem image_mul_left_eq_preimage (z : (AdeleRing (𝓞 F) F)ˣ) (A : Set (AdelicGL2 (𝓞 F) F)) :
    (fun g => centralScalar (𝓞 F) F z * g) '' A = (fun g => centralScalar (𝓞 F) F z⁻¹ * g) ⁻¹' A := by
  ext g
  simp only [Set.mem_image, Set.mem_preimage, map_inv]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rwa [inv_mul_cancel_left]
  · intro h
    exact ⟨_, h, by rw [mul_inv_cancel_left]⟩

theorem measurableSet_image_mul_left (z : (AdeleRing (𝓞 F) F)ˣ) {A : Set (AdelicGL2 (𝓞 F) F)}
    (hA : MeasurableSet A) : MeasurableSet ((fun g => centralScalar (𝓞 F) F z * g) '' A) := by
  rw [image_mul_left_eq_preimage]
  exact measurable_const_mul _ hA

theorem sqm_image_mul_left {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ) (z : (AdeleRing (𝓞 F) F)ˣ)
    {A : Set (AdelicGL2 (𝓞 F) F)} (hA : MeasurableSet A) :
    sqm φ ((fun g => centralScalar (𝓞 F) F z * g) '' A)
      = ((‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2) * sqm φ A := by
  unfold sqm
  rw [image_mul_left_eq_preimage]
  have hmp := measurePreserving_mul_left (μH F) (centralScalar (𝓞 F) F z⁻¹)
  have hmeas : Measurable fun b => ((‖φ (centralScalar (𝓞 F) F z * b)‖₊ : ℝ≥0∞) ^ 2) :=
    ((hcont.comp (continuous_const.mul continuous_id)).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have key := hmp.setLIntegral_comp_preimage hA hmeas
  simp only [map_inv, mul_inv_cancel_left] at key
  rw [map_inv, key]
  have hlaw : ∀ b, ((‖φ (centralScalar (𝓞 F) F z * b)‖₊ : ℝ≥0∞) ^ 2)
      = ((‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2) * ((‖φ b‖₊ : ℝ≥0∞) ^ 2) := by
    intro b
    have := hφ.central_transform ⟨z, Subgroup.mem_top z⟩ b
    rw [this, nnnorm_mul, ENNReal.coe_mul, mul_pow]
  simp_rw [hlaw]
  rw [lintegral_const_mul _ (measurable_sq_nnnorm hcont)]

section Shells

variable (c u d₁ d₁' d₂ : ℝ)

def AQ (Q : Finset (InfinitePlace F)) : Set (AdelicGL2 (𝓞 F) F) :=
  centreCutSiegelSet F c u d₁ d₂ ∩ {g | ∀ w, w ∉ Q → d₁' ≤ archDetNorm w g}

variable {c u d₁ d₁' d₂}

theorem measurableSet_AQ (Q : Finset (InfinitePlace F)) : MeasurableSet (AQ c u d₁ d₁' d₂ Q) := by
  refine (measurableSet_centreCutSiegelSet c u d₁ d₂).inter ?_
  have : {g : AdelicGL2 (𝓞 F) F | ∀ w, w ∉ Q → d₁' ≤ archDetNorm w g}
      = ⋂ w, ⋂ (_ : w ∉ Q), {g | d₁' ≤ archDetNorm w g} := by
    ext g; simp
  rw [this]
  exact MeasurableSet.iInter fun w => MeasurableSet.iInter fun _ =>
    (isClosed_le continuous_const (continuous_archDetNorm w)).measurableSet

theorem AQ_empty_subset :
    AQ c u d₁ d₁' d₂ (∅ : Finset (InfinitePlace F)) ⊆ centreCutSiegelSet F c u d₁' d₂ := by
  rintro g ⟨hg, hdet⟩
  obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.mp hg
  exact mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ⟨hdet w (Finset.notMem_empty w), (h4 w).2⟩⟩

theorem subset_AQ_univ :
    centreCutSiegelSet F c u d₁ d₂ ⊆ AQ c u d₁ d₁' d₂ (Finset.univ : Finset (InfinitePlace F)) :=
  fun _ hg => ⟨hg, fun w hw => (hw (Finset.mem_univ w)).elim⟩

theorem measurableSet_translate {A : Set (AdelicGL2 (𝓞 F) F)} (hA : MeasurableSet A) (x : AdelicGL2 (𝓞 F) F) :
    MeasurableSet ((· * x) '' A) := by
  have himg : (· * x) '' A = (· * x⁻¹) ⁻¹' A := by ext g; simp [Set.mem_preimage]
  rw [himg]
  exact measurable_mul_const x⁻¹ hA

theorem shell_cover {v : InfinitePlace F} {Q : Finset (InfinitePlace F)}
    (hd₁' : 0 < d₁') (hd' : d₁' < d₂) (hle : d₁ ≤ d₁')
    (a : (v.Completion)ˣ) {ρ' : ℝ} (ha : ‖(a : v.Completion)‖ * ‖(a : v.Completion)‖ = ρ')
    (hρ'1 : ρ' < 1) (hρ'2 : d₁' ≤ ρ' * d₂)
    (x : AdelicGL2 (𝓞 F) F) {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ (· * x) '' AQ c u d₁ d₁' d₂ (insert v Q)) :
    ∃ n : ℕ, d₁ ≤ ρ' ^ n * d₂ ∧
      g ∈ (fun y => centralScalar (𝓞 F) F ((archCentralUnit F v a) ^ n) * y) '' ((· * x) '' AQ c u d₁ d₁' d₂ Q) := by
  have hd₂ : 0 < d₂ := hd₁'.trans hd'
  have hρ'0 : 0 < ρ' := (pos_iff_pos_of_mul_pos (hd₁'.trans_le hρ'2)).mpr hd₂
  obtain ⟨h, hh, rfl⟩ := hg
  obtain ⟨hS, hdet⟩ := hh
  obtain ⟨hfin, hht, hxw, hd⟩ := mem_centreCutSiegelSet_iff.mp hS
  set r := archDetNorm v h with hr
  have hrpos : 0 < r := archDetNorm_pos v h
  have hr2 : r ≤ d₂ := (hd v).2
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one (div_pos hrpos hd₂) ((div_le_one hd₂).mpr hr2) hρ'0 hρ'1

  set zn := (archCentralUnit F v a) ^ n with hzn
  set h' := (centralScalar (𝓞 F) F zn)⁻¹ * h with hh'
  have hhh' : h = centralScalar (𝓞 F) F zn * h' := by rw [hh', mul_inv_cancel_left]
  obtain ⟨f1, f2, f3, f4, f5⟩ := cS_pow_facts v a n h'
  rw [← hhh'] at f1 f2 f3 f4 f5
  rw [ha] at f4
  have hρn : 0 < ρ' ^ n := pow_pos hρ'0 n

  have hr' : archDetNorm v h' = r / ρ' ^ n := by
    rw [eq_div_iff hρn.ne', mul_comm, ← f4]
  have h1v : ρ' * d₂ < r / ρ' ^ n := by
    rw [lt_div_iff₀ hρn]
    have := (lt_div_iff₀ hd₂).mp hn1
    calc ρ' * d₂ * ρ' ^ n = ρ' ^ (n + 1) * d₂ := by ring
      _ < r := this
  have h2v : r / ρ' ^ n ≤ d₂ := by
    rw [div_le_iff₀ hρn]
    calc r ≤ ρ' ^ n * d₂ := by simpa using (div_le_iff₀ hd₂).mp hn2
      _ = d₂ * ρ' ^ n := by ring
  have hbound : d₁ ≤ ρ' ^ n * d₂ := (hd v).1.trans (by simpa [hr] using (div_le_iff₀ hd₂).mp hn2)
  have hmemS : h' ∈ centreCutSiegelSet F c u d₁ d₂ := by
    rw [mem_centreCutSiegelSet_iff]
    refine ⟨by rw [← f1]; exact hfin, fun w => by rw [← f2 w]; exact hht w, fun w => by rw [← f3 w]; exact hxw w,
      fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      rw [hr']
      exact ⟨hle.trans (hρ'2.trans h1v.le), h2v⟩
    · rw [← f5 w hw]; exact hd w
  have hextra : ∀ w, w ∉ Q → d₁' ≤ archDetNorm w h' := by
    intro w hwQ
    by_cases hw : w = v
    · subst hw
      rw [hr']
      exact hρ'2.trans h1v.le
    · rw [← f5 w hw]
      exact hdet w (by simp [hw, hwQ])
  refine ⟨n, hbound, h' * x, ⟨h', ⟨hmemS, hextra⟩, rfl⟩, ?_⟩
  show centralScalar (𝓞 F) F zn * (h' * x) = h * x
  rw [← mul_assoc, ← hhh']

end Shells

section Mass

variable {c u d₁ d₁' d₂ : ℝ}

theorem archDetNorm_mul (v : InfinitePlace F) (g h : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (g * h) = archDetNorm v g * archDetNorm v h := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

theorem sqm_image_pow {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ) (z : (AdeleRing (𝓞 F) F)ˣ) (m : ℕ)
    {A : Set (AdelicGL2 (𝓞 F) F)} (hA : MeasurableSet A) :
    sqm φ ((fun g => centralScalar (𝓞 F) F (z ^ m) * g) '' A)
      = (((‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2) ^ m) * sqm φ A := by
  rw [sqm_image_mul_left hφ hcont (z ^ m) hA]
  congr 1
  have : (⟨z ^ m, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) = ⟨z, Subgroup.mem_top z⟩ ^ m := rfl
  rw [this, map_pow, Units.val_pow_eq_pow_val, nnnorm_pow, ENNReal.coe_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem finite_step (hd₁' : 0 < d₁') (hd' : d₁' < d₂) (hle : d₁ ≤ d₁')
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ) (hcont : Continuous ψ)
    (v : InfinitePlace F) (Q : Finset (InfinitePlace F))
    (a : (v.Completion)ˣ) {ρ' : ℝ} (ha : ‖(a : v.Completion)‖ * ‖(a : v.Completion)‖ = ρ')
    (hρ'1 : ρ' < 1) (hρ'2 : d₁' ≤ ρ' * d₂)
    (hq : d₁ ≤ 0 → ((‖((ξ ⟨archCentralUnit F v a, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2) < 1)
    (x : AdelicGL2 (𝓞 F) F) (hfin : sqm ψ ((· * x) '' AQ c u d₁ d₁' d₂ Q) < ⊤) :
    sqm ψ ((· * x) '' AQ c u d₁ d₁' d₂ (insert v Q)) < ⊤ := by
  have hd₂ : 0 < d₂ := hd₁'.trans hd'
  have hρ'0 : 0 < ρ' := (pos_iff_pos_of_mul_pos (hd₁'.trans_le hρ'2)).mpr hd₂
  set z := archCentralUnit F v a with hz
  set r : ℝ≥0∞ := ((‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2) with hr
  have hAx : MeasurableSet ((· * x) '' AQ c u d₁ d₁' d₂ Q) := measurableSet_translate (measurableSet_AQ Q) x
  set B : ℕ → Set (AdelicGL2 (𝓞 F) F) :=
    fun m => (fun y => centralScalar (𝓞 F) F (z ^ m) * y) '' ((· * x) '' AQ c u d₁ d₁' d₂ Q) with hB
  have hBmass : ∀ m, sqm ψ (B m) = r ^ m * sqm ψ ((· * x) '' AQ c u d₁ d₁' d₂ Q) := fun m =>
    sqm_image_pow hψ hcont z m hAx
  have hr_top : r < ⊤ := ENNReal.pow_lt_top ENNReal.coe_lt_top
  by_cases hd₁0 : d₁ ≤ 0
  ·
    have hcover : (· * x) '' AQ c u d₁ d₁' d₂ (insert v Q) ⊆ ⋃ m, B m := by
      intro g hg
      obtain ⟨n, -, hn⟩ := shell_cover hd₁' hd' hle a ha hρ'1 hρ'2 x hg
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    calc sqm ψ ((· * x) '' AQ c u d₁ d₁' d₂ (insert v Q))
        ≤ sqm ψ (⋃ m, B m) := sqm_mono ψ hcover
      _ ≤ ∑' m, sqm ψ (B m) := lintegral_iUnion_le B _
      _ = ∑' m, r ^ m * sqm ψ ((· * x) '' AQ c u d₁ d₁' d₂ Q) := by simp_rw [hBmass]
      _ = (∑' m, r ^ m) * sqm ψ ((· * x) '' AQ c u d₁ d₁' d₂ Q) := ENNReal.tsum_mul_right
      _ < ⊤ := ENNReal.mul_lt_top ?_ hfin
    rw [ENNReal.tsum_geometric, ENNReal.inv_lt_top, tsub_pos_iff_lt]
    exact hq hd₁0
  ·
    push Not at hd₁0
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (div_pos hd₁0 hd₂) hρ'1
    have hcover : (· * x) '' AQ c u d₁ d₁' d₂ (insert v Q) ⊆ ⋃ m : Fin M, B m := by
      intro g hg
      obtain ⟨n, hnb, hn⟩ := shell_cover hd₁' hd' hle a ha hρ'1 hρ'2 x hg
      have hnM : n < M := by
        by_contra hcon
        push Not at hcon
        have h1 : ρ' ^ n ≤ ρ' ^ M := pow_le_pow_of_le_one hρ'0.le hρ'1.le hcon
        have h2 : ρ' ^ n * d₂ < d₁ :=
          calc ρ' ^ n * d₂ ≤ ρ' ^ M * d₂ := by gcongr
            _ < d₁ / d₂ * d₂ := by gcongr
            _ = d₁ := div_mul_cancel₀ _ hd₂.ne'
        linarith
      exact Set.mem_iUnion.mpr ⟨⟨n, hnM⟩, hn⟩
    calc sqm ψ ((· * x) '' AQ c u d₁ d₁' d₂ (insert v Q))
        ≤ sqm ψ (⋃ m : Fin M, B m) := sqm_mono ψ hcover
      _ ≤ ∑' m : Fin M, sqm ψ (B m) := lintegral_iUnion_le _ _
      _ = ∑ m : Fin M, sqm ψ (B m) := tsum_fintype _
      _ < ⊤ := ENNReal.sum_lt_top.mpr fun m _ => by
          rw [hBmass]; exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hr_top) hfin

theorem ratio_lt_one (hle : d₁ ≤ d₁') (hd₁0 : d₁ ≤ 0)
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ)
    (v : InfinitePlace F) (a : (v.Completion)ˣ) {ρ' : ℝ}
    (ha : ‖(a : v.Completion)‖ * ‖(a : v.Completion)‖ = ρ') (hρ'0 : 0 < ρ') (hρ'1 : ρ' < 1)
    (hρ'3 : ρ' ^ 2 * d₂ < d₁') (hd₂ : 0 < d₂)
    (x₀ : AdelicGL2 (𝓞 F) F)
    (hfin : sqm φ ((· * x₀) '' centreCutSiegelSet F c u d₁ d₂) < ⊤)
    (hpos : 0 < sqm φ ((· * x₀) '' centreCutSiegelSet F c u d₁' d₂)) :
    ((‖((ξ ⟨archCentralUnit F v a, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2) < 1 := by
  set z := archCentralUnit F v a with hz
  set r : ℝ≥0∞ := ((‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2) with hr
  set Y := (· * x₀) '' centreCutSiegelSet F c u d₁' d₂ with hY
  have hYm : MeasurableSet Y := measurableSet_translate (measurableSet_centreCutSiegelSet c u d₁' d₂) x₀
  set B : ℕ → Set (AdelicGL2 (𝓞 F) F) := fun m => (fun y => centralScalar (𝓞 F) F (z ^ (2 * m)) * y) '' Y with hB
  have hBm : ∀ m, MeasurableSet (B m) := fun m => measurableSet_image_mul_left _ hYm
  have hBmass : ∀ m, sqm φ (B m) = (r ^ 2) ^ m * sqm φ Y := fun m => by
    rw [hB]; dsimp only; rw [sqm_image_pow hφ hcont z (2 * m) hYm, pow_mul]

  have hκ : 0 < archDetNorm v x₀ := archDetNorm_pos v x₀
  have hBdet : ∀ m, ∀ g ∈ B m,
      ρ' ^ (2 * m) * d₁' * archDetNorm v x₀ ≤ archDetNorm v g ∧
        archDetNorm v g ≤ ρ' ^ (2 * m) * d₂ * archDetNorm v x₀ := by
    rintro m g ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨-, -, -, f4, -⟩ := cS_pow_facts v a (2 * m) s
    rw [ha] at f4
    dsimp only
    rw [← mul_assoc, archDetNorm_mul, f4]
    have h := (mem_centreCutSiegelSet_iff.mp hs).2.2.2 v
    have hp : 0 ≤ ρ' ^ (2 * m) := pow_nonneg hρ'0.le _
    constructor
    · have := mul_le_mul_of_nonneg_left h.1 hp
      exact mul_le_mul_of_nonneg_right this hκ.le
    · have := mul_le_mul_of_nonneg_left h.2 hp
      exact mul_le_mul_of_nonneg_right this hκ.le

  have hBsub : ∀ m, B m ⊆ (· * x₀) '' centreCutSiegelSet F c u d₁ d₂ := by
    rintro m g ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨f1, f2, f3, f4, f5⟩ := cS_pow_facts v a (2 * m) s
    rw [ha] at f4
    obtain ⟨hfin', hh, hxw, hd⟩ := mem_centreCutSiegelSet_iff.mp hs
    refine ⟨centralScalar (𝓞 F) F (z ^ (2 * m)) * s, ?_, by simp only [mul_assoc]⟩
    rw [mem_centreCutSiegelSet_iff]
    refine ⟨by rw [f1]; exact hfin', fun w => by rw [f2]; exact hh w, fun w => by rw [f3]; exact hxw w, fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      rw [f4]
      have hp : 0 ≤ ρ' ^ (2 * m) := pow_nonneg hρ'0.le _
      have hp1 : ρ' ^ (2 * m) ≤ 1 := pow_le_one₀ hρ'0.le hρ'1.le
      constructor
      · exact hd₁0.trans (mul_nonneg hp (archDetNorm_pos w s).le)
      · calc ρ' ^ (2 * m) * archDetNorm w s ≤ 1 * d₂ :=
            mul_le_mul hp1 (hd w).2 (archDetNorm_pos w s).le zero_le_one
          _ = d₂ := one_mul _
    · rw [f5 w hw]
      exact ⟨hle.trans (hd w).1, (hd w).2⟩

  have hstep : ∀ m : ℕ, ρ' ^ (2 * (m + 1)) * d₂ < ρ' ^ (2 * m) * d₁' := fun m => by
    have : ρ' ^ (2 * (m + 1)) * d₂ = ρ' ^ (2 * m) * (ρ' ^ 2 * d₂) := by ring
    rw [this]
    exact mul_lt_mul_of_pos_left hρ'3 (pow_pos hρ'0 _)
  have hlt : ∀ {m m' : ℕ}, m < m' → ρ' ^ (2 * m') * d₂ < ρ' ^ (2 * m) * d₁' := by
    intro m m' hmm'
    have h1 : ρ' ^ (2 * m') ≤ ρ' ^ (2 * (m + 1)) :=
      pow_le_pow_of_le_one hρ'0.le hρ'1.le (by omega)
    calc ρ' ^ (2 * m') * d₂ ≤ ρ' ^ (2 * (m + 1)) * d₂ := mul_le_mul_of_nonneg_right h1 hd₂.le
      _ < ρ' ^ (2 * m) * d₁' := hstep m
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro m m' hne
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    obtain ⟨l1, u1⟩ := hBdet m g hg
    obtain ⟨l2, u2⟩ := hBdet m' g hg'
    rcases lt_or_gt_of_ne hne with h | h
    · have := hlt h
      have : ρ' ^ (2 * m') * d₂ * archDetNorm v x₀ < ρ' ^ (2 * m) * d₁' * archDetNorm v x₀ :=
        mul_lt_mul_of_pos_right this hκ
      linarith
    · have := hlt h
      have : ρ' ^ (2 * m) * d₂ * archDetNorm v x₀ < ρ' ^ (2 * m') * d₁' * archDetNorm v x₀ :=
        mul_lt_mul_of_pos_right this hκ
      linarith

  have hsum : (∑' m, (r ^ 2) ^ m) * sqm φ Y < ⊤ := by
    calc (∑' m, (r ^ 2) ^ m) * sqm φ Y = ∑' m, (r ^ 2) ^ m * sqm φ Y := ENNReal.tsum_mul_right.symm
      _ = ∑' m, sqm φ (B m) := by simp_rw [hBmass]
      _ = sqm φ (⋃ m, B m) := (lintegral_iUnion hBm hdisj _).symm
      _ ≤ sqm φ ((· * x₀) '' centreCutSiegelSet F c u d₁ d₂) := sqm_mono φ (Set.iUnion_subset hBsub)
      _ < ⊤ := hfin
  have htsum : (∑' m, (r ^ 2) ^ m) < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.mp hsum with h | h | h
    · exact h.1
    · exfalso
      rw [ENNReal.tsum_geometric] at h
      exact (ENNReal.inv_ne_zero.mpr (ENNReal.sub_ne_top ENNReal.one_ne_top)) h
    · exact absurd h hpos.ne'
  rw [ENNReal.tsum_geometric, ENNReal.inv_lt_top, tsub_pos_iff_lt] at htsum
  by_contra hcon
  push Not at hcon
  exact absurd htsum (not_lt.mpr (one_le_pow₀ hcon))

end Mass

section Main

variable {c u d₁ d₁' d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}

theorem subset_biUnion_translate (A : ℝ → ℝ → Set (AdelicGL2 (𝓞 F) F)) {a b : ℝ} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ T) : (· * x) '' A a b ⊆ ⋃ y ∈ T, (· * y) '' A a b := by
  intro g hg
  simp only [Set.mem_iUnion]
  exact ⟨x, hx, hg⟩

theorem exists_pos_translate (hd' : d₁' < d₂)
    (hcov' : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂))
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0) :
    ∃ x₀ ∈ T, 0 < sqm φ ((· * x₀) '' centreCutSiegelSet F c u d₁' d₂) := by
  obtain ⟨g₁, hg₁⟩ := hne
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds g₁
  obtain ⟨N, hN⟩ :=
    AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
      F c u d₁' d₂ T hd' hcov' ξ hK
  have hK' : sqm φ K ≤ ENNReal.ofReal N * sqm φ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) :=
    hN φ hφ hcont
  have hposK : 0 < sqm φ K := by
    rw [pos_iff_ne_zero]
    intro h0
    have hae := (lintegral_eq_zero_iff (measurable_sq_nnnorm hcont)).mp h0
    apply not_ae_zero_restrict_of_continuous_of_mem_interior (μ := μH F) hcont hg₁ (mem_interior_iff_mem_nhds.mpr hKn)
    filter_upwards [hae] with g hg
    have h2 : ((‖φ g‖₊ : ℝ≥0∞) ^ 2) = 0 := hg
    simpa [pow_eq_zero_iff, ENNReal.coe_eq_zero, nnnorm_eq_zero] using h2
  have hD' : sqm φ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hK'
    exact hposK.ne' (le_zero_iff.mp hK')
  have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
      ⊆ ⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁' d₂ := by
    intro g hg
    simp only [Set.mem_iUnion] at hg ⊢
    obtain ⟨x, hx, h⟩ := hg
    exact ⟨⟨x, hx⟩, h⟩
  have hle' : sqm φ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
      ≤ ∑ x : T, sqm φ ((· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁' d₂) :=
    (sqm_mono φ hsub).trans ((lintegral_iUnion_le _ _).trans_eq (tsum_fintype _))
  have hsum : ∑ x : T, sqm φ ((· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁' d₂) ≠ 0 := by
    intro h
    rw [h] at hle'
    exact hD' (le_zero_iff.mp hle')
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨x, x.2, pos_iff_ne_zero.mpr hx⟩

end Main

end DetFloor
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre.AutomorphicForm.DetFloor"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre.AutomorphicForm.DetFloor P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre.AutomorphicForm.DetFloor P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre.AutomorphicForm"

open AutomorphicForm.DetFloor in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₁' d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hd' : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) Θ P ↔
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ P := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hd₂ : 0 < d₂ := hd₁'.trans hd'
  have hSS : centreCutSiegelSet F c u d₁' d₂ ⊆ centreCutSiegelSet F c u d₁ d₂ := fun g hg => by
    obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.mp hg
    exact mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ⟨hle.trans (h4 w).1, (h4 w).2⟩⟩
  have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
      ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ :=
    Set.iUnion₂_mono fun x _ => Set.image_mono hSS
  constructor
  · rintro ⟨Θ'', h'', R, hR, hP⟩
    obtain ⟨Θ', h', R₀, hR₀, -⟩ := hΘ
    have hψL := isLsXi_of_realization R
    have hψ2 := memLp_of_realization R

    have hchar : R₀.centralChar = R.centralChar :=
      AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite F _ Θ' Θ''
        (agrees_trans h' (agrees_symm h'')) (restrict hsub R₀) hR₀ R hR
    have hφL : IsLsXiFunction (𝓞 F) F ⊤ R.centralChar R₀.toFun := hchar ▸ isLsXi_of_realization R₀

    have hρ : 0 < d₁' / d₂ := div_pos hd₁' hd₂
    have hρ1 : d₁' / d₂ < 1 := (div_lt_one hd₂).mpr hd'
    have hρsqrt : d₁' / d₂ < Real.sqrt (d₁' / d₂) := by
      rw [Real.lt_sqrt hρ.le]
      nlinarith
    obtain ⟨q, hq, hq1, hq2⟩ := exists_rat_sq_mem_Ico hρ hρsqrt
    have hρ'0 : 0 < (q : ℝ) ^ 2 := by positivity
    have hρ'1 : (q : ℝ) ^ 2 < 1 := by
      refine hq2.trans_le ?_
      rw [Real.sqrt_le_one]
      exact hρ1.le
    have hρ'2 : d₁' ≤ (q : ℝ) ^ 2 * d₂ := (div_le_iff₀ hd₂).mp hq1
    have hρ'3 : ((q : ℝ) ^ 2) ^ 2 * d₂ < d₁' := by
      have : ((q : ℝ) ^ 2) ^ 2 < d₁' / d₂ :=
        calc ((q : ℝ) ^ 2) ^ 2 < (Real.sqrt (d₁' / d₂)) ^ 2 := by gcongr
          _ = d₁' / d₂ := Real.sq_sqrt hρ.le
      exact (lt_div_iff₀ hd₂).mp this
    have hcov' := coversModCentre_raise hcov hd₁' hd'

    have key : ∀ x ∈ T, ∀ Q : Finset (InfinitePlace F),
        sqm R.toFun ((· * x) '' AQ c u d₁ d₁' d₂ Q) < ⊤ := by
      intro x hx Q
      induction Q using Finset.induction_on with
      | empty =>
        refine lt_of_le_of_lt (sqm_mono _ (Set.image_mono AQ_empty_subset)) ?_
        exact lt_of_le_of_lt (sqm_mono _ (subset_biUnion_translate (fun a b => centreCutSiegelSet F c u a b) hx))
          (sqm_lt_top_of_memLp hψ2)
      | insert v Q hv ih =>
        obtain ⟨a, ha⟩ := exists_unit_norm_mul_norm_eq v hq
        refine finite_step hd₁' hd' hle hψL hR v Q a ha hρ'1 hρ'2 (fun hd₁0 => ?_) x ih
        obtain ⟨x₀, hx₀, hpos⟩ := exists_pos_translate hd' hcov' hφL hR₀ R₀.exists_ne_zero
        refine ratio_lt_one hle hd₁0 hφL hR₀ v a ha hρ'0 hρ'1 hρ'3 hd₂ x₀ ?_ hpos
        exact lt_of_le_of_lt (sqm_mono _ (subset_biUnion_translate (fun a b => centreCutSiegelSet F c u a b) hx₀))
          (sqm_lt_top_of_memLp (memLp_of_realization R₀))
    have hD : sqm R.toFun (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
      have hsub' : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          ⊆ ⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' AQ c u d₁ d₁' d₂ Finset.univ := by
        intro g hg
        simp only [Set.mem_iUnion, Set.mem_image] at hg ⊢
        obtain ⟨x, hx, s, hs, rfl⟩ := hg
        exact ⟨⟨x, hx⟩, s, subset_AQ_univ hs, rfl⟩
      calc sqm R.toFun (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          ≤ sqm R.toFun (⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' AQ c u d₁ d₁' d₂ Finset.univ) := sqm_mono _ hsub'
        _ ≤ ∑' x : T, sqm R.toFun ((· * (x : AdelicGL2 (𝓞 F) F)) '' AQ c u d₁ d₁' d₂ Finset.univ) :=
          lintegral_iUnion_le _ _
        _ = ∑ x : T, sqm R.toFun ((· * (x : AdelicGL2 (𝓞 F) F)) '' AQ c u d₁ d₁' d₂ Finset.univ) := tsum_fintype _
        _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ => key x x.2 _
    exact ⟨Θ'', h'', transport R (memLp_of_sqm_lt_top hR hD), hR, hP⟩
  · rintro ⟨Θ', h', R, hR, hP⟩
    exact ⟨Θ', h', restrict hsub R, hR, hP⟩

end S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre (solution)
