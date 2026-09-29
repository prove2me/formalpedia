-- Prove2me | solution 1 for AutomorphicForm.exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2281d774-f127-57a3-a748-5f69412e31e2

import Mathlib
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology FLT.SmoothVectors
open scoped NNReal

noncomputable section

namespace WITNESS

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

theorem gl_ext {g h : AdelicGL2 (𝓞 F) F} (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ v, finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = finComponent (𝓞 F) F v (glFin (𝓞 F) F h)) :
    g = h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) h₁) i) j
    rwa [glArch_apply, glArch_apply] at this
  · refine RestrictedProduct.ext _ _ fun v => ?_
    have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (v.adicCompletion F) => (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) (h₂ v)) i) j
    rwa [finComponent_apply, finComponent_apply, glFin_apply, glFin_apply] at this

theorem continuous_finComponent_glFin (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => finComponent (𝓞 F) F v (glFin (𝓞 F) F g) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun g : AdelicGL2 (𝓞 F) F => (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) v
    exact (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp
      ((Units.continuous_val.matrix_elem i j)))
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun g : AdelicGL2 (𝓞 F) F => ((((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) v
    exact (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp
      ((Units.continuous_coe_inv.matrix_elem i j)))

def Cpt : Set (AdelicGL2 (𝓞 F) F) :=
  (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) ∩ (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))

theorem isCompact_Cpt : IsCompact (Cpt F) :=
  (isCompact_adelicMaximalCompact F).inter_right (isClosed_finiteAdelicGL2Subgroup F)

theorem mem_Cpt {k : AdelicGL2 (𝓞 F) F} (h1 : glArch (𝓞 F) F k = 1) (h2 : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F) :
    k ∈ Cpt F := by
  refine ⟨⟨h2, fun w => ?_⟩, h1⟩
  rw [h1, map_one]; exact isRowIsometry_one

theorem exists_finset_fixing (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (hsm : IsKfSmooth F φ₀) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ k : AdelicGL2 (𝓞 F) F,
      glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ v ∈ S₂, finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = 1) → ∀ g, φ₀ (g * k) = φ₀ g := by

  have hopen : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ₀ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := hsm
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hopen
  have h1V : (1 : AdelicGL2 (𝓞 F) F) ∈ V := by
    have : (1 : finiteAdelicGL2Subgroup F) ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]; exact Subgroup.one_mem _
    exact this

  set t : Finset (HeightOneSpectrum (𝓞 F)) → Set (AdelicGL2 (𝓞 F) F) :=
    fun S => {k | ∀ v ∈ S, finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = 1} with ht
  have htc : ∀ S, IsClosed (t S) := by
    intro S
    have : t S = ⋂ v ∈ S, (fun k => finComponent (𝓞 F) F v (glFin (𝓞 F) F k)) ⁻¹' {1} := by
      ext k; simp [ht]
    rw [this]
    exact isClosed_biInter fun v _ => isClosed_singleton.preimage (continuous_finComponent_glFin F v)
  have hdir : Directed (· ⊇ ·) t := by
    intro S S'
    refine ⟨S ∪ S', fun k hk v hv => hk v (Finset.mem_union_left _ hv), fun k hk v hv => hk v (Finset.mem_union_right _ hv)⟩
  have hst : (Cpt F ∩ Vᶜ) ∩ ⋂ S, t S = ∅ := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hk hall
    apply hk.2
    have : k = 1 := by
      refine gl_ext F (by rw [map_one]; exact hk.1.2) fun v => ?_
      rw [map_one, map_one]
      exact hall {v} v (Finset.mem_singleton_self v)
    rw [this]; exact h1V
  obtain ⟨S₂, hS₂⟩ := ((isCompact_Cpt F).inter_right hV.isClosed_compl).elim_directed_family_closed t htc hst hdir
  refine ⟨S₂, fun k hk1 hk2 hk3 g => ?_⟩
  have hkC : k ∈ Cpt F := mem_Cpt F hk1 hk2
  have hkV : k ∈ V := by
    by_contra hnot
    have : k ∈ (Cpt F ∩ Vᶜ) ∩ t S₂ := ⟨⟨hkC, hnot⟩, hk3⟩
    rw [hS₂] at this; exact this
  have hstab : (⟨k, hk1⟩ : finiteAdelicGL2Subgroup F) ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ₀ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) := by
    have : (⟨k, hk1⟩ : finiteAdelicGL2Subgroup F) ∈ Subtype.val ⁻¹' V := hkV
    rw [hVeq] at this; exact this
  rw [MulAction.mem_stabilizer_iff] at hstab
  have := congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ => RightTranslationFn.toFun f g) hstab
  exact this

variable (S₂ : Finset (HeightOneSpectrum (𝓞 F)))

theorem compl_le : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((↑S₂ : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  Filter.le_principal_iff.mpr S₂.finite_toSet.compl_mem_cofinite

def secP (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓟 ((↑S₂ : Set (HeightOneSpectrum (𝓞 F)))ᶜ)) :=
  ⟨fun v => if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F), by
    rw [Filter.eventually_principal]
    intro v hv
    rw [Set.mem_compl_iff, Finset.mem_coe] at hv
    simp only [dif_neg hv]
    exact zero_mem _⟩

def sec (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (compl_le F S₂) (secP F S₂ b)

theorem sec_apply_of_mem (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S₂) :
    sec F S₂ b v = b ⟨v, hv⟩ := by
  change (if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F)) = _
  rw [dif_pos hv]

theorem continuous_sec : Continuous (sec F S₂) := by
  refine (RestrictedProduct.continuous_inclusion (compl_le F S₂)).comp ?_
  rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
  intro v
  change Continuous fun b : (∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) => (if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F))
  by_cases hv : v ∈ S₂
  · simp only [dif_pos hv]; exact continuous_apply _
  · simp only [dif_neg hv]; exact continuous_const

theorem sec_apply_of_not_mem (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S₂) :
    sec F S₂ b v = 0 := by
  change (if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F)) = _
  rw [dif_neg hv]

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def evFin (v : HeightOneSpectrum (𝓞 F)) : AdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  (finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)

theorem evFin_apply (v : HeightOneSpectrum (𝓞 F)) (a : AdeleRing (𝓞 F) F) : evFin F v a = a.2 v := rfl

theorem matrix_ext {M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)}
    (h₁ : (adeleArch (𝓞 F) F).mapMatrix M = (adeleArch (𝓞 F) F).mapMatrix N)
    (h₂ : ∀ v, (evFin F v).mapMatrix M = (evFin F v).mapMatrix N) : M = N := by
  ext i j
  apply Prod.ext
  · exact congrFun (congrFun h₁ i) j
  · refine RestrictedProduct.ext _ _ fun v => ?_
    exact congrFun (congrFun (h₂ v) i) j

def awayMat (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
      (⟨fun v => if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else (M i j).2 v, by
        filter_upwards [(M i j).2.2] with v hv
        split_ifs
        · rw [Matrix.one_apply]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        · exact hv⟩ : FiniteAdeleRing (𝓞 F) F))

theorem evArch_awayMat (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :
    (adeleArch (𝓞 F) F).mapMatrix (awayMat F S M) = 1 := by
  ext i j; rfl

theorem evFin_awayMat (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)) :
    (evFin F v).mapMatrix (awayMat F S M) = if v ∈ S then 1 else (evFin F v).mapMatrix M := by
  split_ifs with hv
  · ext i j : 1
    show (if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else (M i j).2 v) = _
    rw [if_pos hv]
  · ext i j : 1
    show (if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else (M i j).2 v) = _
    rw [if_neg hv]
    rfl

def awayMatHom : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) →* Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) where
  toFun := awayMat F S
  map_one' := matrix_ext F (by rw [evArch_awayMat, map_one]) fun v => by
    rw [evFin_awayMat]; split_ifs <;> simp [map_one]
  map_mul' M N := matrix_ext F (by rw [evArch_awayMat, map_mul, evArch_awayMat, evArch_awayMat, one_mul]) fun v => by
    simp only [evFin_awayMat, map_mul]
    split_ifs <;> simp

def awayPart : AdelicGL2 (𝓞 F) F →* AdelicGL2 (𝓞 F) F := Units.map (awayMatHom F S)

theorem coe_awayPart (g : AdelicGL2 (𝓞 F) F) :
    ((awayPart F S g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = awayMat F S g := rfl

theorem glArch_awayPart (g : AdelicGL2 (𝓞 F) F) : glArch (𝓞 F) F (awayPart F S g) = 1 := by
  refine Units.ext ?_
  change (adeleArch (𝓞 F) F).mapMatrix (awayMat F S g) = 1
  exact evArch_awayMat F S g

theorem coe_finComponent_glFin (g : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      (evFin F v).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := rfl

theorem finComponent_awayPart (g : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (awayPart F S g)) =
      if v ∈ S then 1 else finComponent (𝓞 F) F v (glFin (𝓞 F) F g) := by
  split_ifs with hv
  · refine Units.ext ?_
    rw [coe_finComponent_glFin, coe_awayPart, evFin_awayMat, if_pos hv]; rfl
  · refine Units.ext ?_
    rw [coe_finComponent_glFin, coe_awayPart, evFin_awayMat, if_neg hv, coe_finComponent_glFin]

theorem glFin_awayPart_mem {h : AdelicGL2 (𝓞 F) F}
    (hint : ∀ v ∉ S, ∀ i j, ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F ∧
      (((h⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F) :
    glFin (𝓞 F) F (awayPart F S h) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    rw [glFin_apply, coe_awayPart]
    change (if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) ∈ _
    split_ifs with hv
    · rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
    · exact (hint v hv i j).1
  · intro i j v
    rw [← map_inv, ← map_inv, glFin_apply, coe_awayPart]
    change (if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else (((h⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) ∈ _
    split_ifs with hv
    · rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
    · exact (hint v hv i j).2

theorem coe_adelicWeyl :
    ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] := by
  rw [adelicWeyl]
  ext i j
  change algebraMap F (AdeleRing (𝓞 F) F) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem adelicWeyl_inv : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

theorem unipotentGL2_inv (x : AdeleRing (𝓞 F) F) : (unipotentGL2 x : AdelicGL2 (𝓞 F) F)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem mul_apply_fst (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) (w : InfinitePlace F) :
    ((M * N) i j).1 w = ∑ k : Fin 2, (M i k).1 w * (N k j).1 w := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

theorem mul_apply_snd (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) :
    ((M * N) i j).2 v = ∑ k : Fin 2, (M i k).2 v * (N k j).2 v := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

theorem mem_borel_of_unit (g : AdelicGL2 (𝓞 F) F) (c : (AdeleRing (𝓞 F) F)ˣ)
    (hc : (c : AdeleRing (𝓞 F) F) = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) :
    g * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (↑c⁻¹ * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1))⁻¹ ∈
      adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff, mul_inv_rev, inv_inv, unipotentGL2_inv, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, coe_adelicWeyl, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hc, ← mul_assoc, Units.mul_inv, one_mul]
  ring

theorem continuous_unipotentGL2 :
    Continuous (fun y : AdeleRing (𝓞 F) F => (unipotentGL2 y : AdelicGL2 (𝓞 F) F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · have : ∀ y : AdeleRing (𝓞 F) F, (↑((unipotentGL2 y : AdelicGL2 (𝓞 F) F)⁻¹) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, -y; 0, 1] := fun y => rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem entry10_mul_lower (g : AdelicGL2 (𝓞 F) F) (y : AdeleRing (𝓞 F) F) :
    ((g * (adelicWeyl (𝓞 F) F * unipotentGL2 y * adelicWeyl (𝓞 F) F) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 + (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 * y := by
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_adelicWeyl, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_ne_zero_mem_arch (w : InfinitePlace F) {t : Set w.Completion} (ht : IsOpen t) (h0 : (0 : w.Completion) ∈ t) :
    ∃ x ∈ t, x ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ht 0 h0

  have hmem : ((r / 2 : ℝ) : ℂ) ∈ Set.range (InfinitePlace.Completion.extensionEmbedding w) := by
    rcases w.isReal_or_isComplex with hw | hw
    · obtain ⟨x, hx⟩ := (InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hw).2 (r / 2)
      exact ⟨x, by rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x, hx]⟩
    · exact (InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw) _
  obtain ⟨x, hx⟩ := hmem
  have hnorm : ‖x‖ = r / 2 := by
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
    rw [← h, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine ⟨x, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, hnorm]; linarith
  · rw [← norm_ne_zero_iff, hnorm]; positivity

theorem exists_ne_zero_mem_fin (v : HeightOneSpectrum (𝓞 F)) {t : Set (v.adicCompletion F)} (ht : IsOpen t)
    (h0 : (0 : v.adicCompletion F) ∈ t) : ∃ x ∈ t, x ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ht 0 h0
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer F v
  have hvπ : Valued.v ((π : F) : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  have hπ0 : ((π : F) : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hvπ
    exact WithZero.zero_ne_coe hvπ
  have hπ1 : ‖((π : F) : v.adicCompletion F)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hvπ, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
    norm_num
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hπ1
  refine ⟨((π : F) : v.adicCompletion F) ^ n, hball ?_, pow_ne_zero _ hπ0⟩
  rw [Metric.mem_ball, dist_zero_right, norm_pow]; exact hn

theorem main (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
    (hφc : Continuous φ) (hφf : IsKfSmooth F φ) (hne : ∃ g, φ g ≠ 0) :
    ∃ x : AdeleRing (𝓞 F) F, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ≠ 0 := by
  by_contra hall
  push_neg at hall

  have hvan : ∀ (g : AdelicGL2 (𝓞 F) F) (c : (AdeleRing (𝓞 F) F)ˣ),
      (c : AdeleRing (𝓞 F) F) = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 → φ g = 0 := by
    intro g c hc
    set x := (↑c⁻¹ * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) with hx
    have hb := mem_borel_of_unit F g c hc
    have e : g = (g * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)⁻¹) * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) := by
      rw [inv_mul_cancel_right]
    rw [e, hφ _ hb, hall x, mul_zero]
  obtain ⟨g₀, hg₀⟩ := hne

  have hT : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ ij : Fin 2 × Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ij.1 ij.2).2 v ∈ v.adicCompletionIntegers F ∧
      (((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ij.1 ij.2).2 v ∈ v.adicCompletionIntegers F := by
    rw [Filter.eventually_all]
    intro ij
    exact (((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ij.1 ij.2).2.2).and
      ((((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ij.1 ij.2).2.2)
  rw [Filter.eventually_cofinite] at hT
  set T : Finset (HeightOneSpectrum (𝓞 F)) := hT.toFinset with hTdef
  have hgood : ∀ v ∉ T, ∀ i j, ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F ∧
      (((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv i j
    rw [hTdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
    exact hv (i, j)

  obtain ⟨S₂, hS₂⟩ := exists_finset_fixing F φ hφf
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₂ ∪ T with hSdef
  set h : AdelicGL2 (𝓞 F) F := g₀⁻¹ * adelicWeyl (𝓞 F) F with hhdef
  have hWint : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      (((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro v i j
    rw [coe_adelicWeyl]
    fin_cases i <;> fin_cases j
    · exact zero_mem _
    · exact one_mem _
    · exact one_mem _
    · exact zero_mem _
  have hhint : ∀ v ∉ S, ∀ i j, ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F ∧
      (((h⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv i j
    have hvT : v ∉ T := fun h' => hv (Finset.mem_union_right _ h')
    constructor
    · rw [hhdef, Matrix.GeneralLinearGroup.coe_mul, mul_apply_snd, Fin.sum_univ_two]
      exact add_mem (mul_mem (hgood v hvT _ _).2 (hWint v _ _)) (mul_mem (hgood v hvT _ _).2 (hWint v _ _))
    · rw [hhdef, mul_inv_rev, adelicWeyl_inv, inv_inv, Matrix.GeneralLinearGroup.coe_mul, mul_apply_snd, Fin.sum_univ_two]
      exact add_mem (mul_mem (hWint v _ _) (hgood v hvT _ _).1) (mul_mem (hWint v _ _) (hgood v hvT _ _).1)
  set m := awayPart F S h with hmdef
  set g₁ := g₀ * m with hg₁def
  have hφg₁ : φ g₁ = φ g₀ :=
    hS₂ m (glArch_awayPart F S h) (glFin_awayPart_mem F S hhint)
      (fun v hv => by rw [hmdef, finComponent_awayPart, if_pos (Finset.mem_union_left _ hv)]) g₀

  set a : AdeleRing (𝓞 F) F := (g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 with hadef
  set d : AdeleRing (𝓞 F) F := (g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 with hddef
  have hoff : ∀ v ∉ S, a.2 v = 1 ∧ d.2 v = 0 := by
    intro v hv
    have hfc : finComponent (𝓞 F) F v (glFin (𝓞 F) F g₁) = finComponent (𝓞 F) F v (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F)) := by
      rw [hg₁def, map_mul, map_mul, hmdef, finComponent_awayPart, if_neg hv, hhdef, map_mul, map_mul, map_inv, map_inv,
        mul_inv_cancel_left]
    have e10 := congrArg (fun M : GL (Fin 2) (v.adicCompletion F) => (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) hfc
    have e11 := congrArg (fun M : GL (Fin 2) (v.adicCompletion F) => (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) hfc
    simp only [finComponent_apply, glFin_apply, coe_adelicWeyl] at e10 e11
    exact ⟨by rw [hadef, e10]; rfl, by rw [hddef, e11]; rfl⟩
  have hrow_fin : ∀ v, ¬ (a.2 v = 0 ∧ d.2 v = 0) := by
    intro v ⟨ha, hd⟩
    have hdet := (Matrix.isUnits_det_units (finComponent (𝓞 F) F v (glFin (𝓞 F) F g₁))).ne_zero
    rw [Matrix.det_fin_two] at hdet
    simp only [finComponent_apply, glFin_apply] at hdet
    apply hdet
    rw [show ((g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 v = 0 from ha,
      show ((g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v = 0 from hd]
    ring
  have hrow_arch : ∀ w, ¬ (a.1 w = 0 ∧ d.1 w = 0) := by
    intro w ⟨ha, hd⟩
    have hdet := (Matrix.isUnits_det_units (archComponent F w (glArch (𝓞 F) F g₁))).ne_zero
    rw [Matrix.det_fin_two] at hdet
    simp only [archComponent_apply, glArch_apply] at hdet
    apply hdet
    rw [show ((g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).1 w = 0 from ha,
      show ((g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w = 0 from hd]
    ring

  set gy : AdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F :=
    fun y => g₁ * (adelicWeyl (𝓞 F) F * unipotentGL2 y * adelicWeyl (𝓞 F) F) with hgydef
  have hgyc : Continuous gy :=
    continuous_const.mul ((continuous_const.mul (continuous_unipotentGL2 F)).mul continuous_const)
  have hWW : adelicWeyl (𝓞 F) F * adelicWeyl (𝓞 F) F = 1 := mul_eq_one_iff_eq_inv.mpr (adelicWeyl_inv F).symm
  have hgy0 : gy 0 = g₁ := by simp only [hgydef, unipotentGL2_zero, mul_one, hWW]
  set V : Set (AdeleRing (𝓞 F) F) := {y | φ (gy y) ≠ 0} with hVdef
  have hVo : IsOpen V := isOpen_compl_singleton.preimage (hφc.comp hgyc)
  have h0V : (0 : AdeleRing (𝓞 F) F) ∈ V := by
    change φ (gy 0) ≠ 0; rw [hgy0, hφg₁]; exact hg₀

  set e : InfiniteAdeleRing F × (∀ v : S, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) → AdeleRing (𝓞 F) F :=
    fun p => (p.1, sec F S p.2) with hedef
  have hec : Continuous e := continuous_fst.prodMk ((continuous_sec F S).comp continuous_snd)
  have hsec0 : sec F S 0 = 0 := by
    refine RestrictedProduct.ext _ _ fun v => ?_
    by_cases hv : v ∈ S
    · exact sec_apply_of_mem F S 0 hv
    · exact sec_apply_of_not_mem F S 0 hv
  have he0 : e (0, 0) = 0 := by
    change ((0 : InfiniteAdeleRing F), sec F S 0) = 0
    rw [hsec0]; rfl
  have hO : IsOpen (e ⁻¹' V) := hVo.preimage hec
  have h0O : ((0 : InfiniteAdeleRing F), (0 : ∀ v : S, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) ∈ e ⁻¹' V := by
    change e (0, 0) ∈ V; rw [he0]; exact h0V
  obtain ⟨u₁, u₂, hu₁, hu₂, h0u₁, h0u₂, hsub⟩ := isOpen_prod_iff.mp hO 0 0 h0O
  obtain ⟨t₁, ht₁, ht₁sub⟩ := isOpen_pi_iff'.mp hu₁ 0 h0u₁
  obtain ⟨t₂, ht₂, ht₂sub⟩ := isOpen_pi_iff'.mp hu₂ 0 h0u₂

  have hch₁ : ∀ w : InfinitePlace F, ∃ q : w.Completion, q ∈ t₁ w ∧ a.1 w + d.1 w * q ≠ 0 := by
    intro w
    by_cases ha : a.1 w = 0
    · have hd : d.1 w ≠ 0 := fun hd => hrow_arch w ⟨ha, hd⟩
      obtain ⟨q, hq, hq0⟩ := exists_ne_zero_mem_arch F w (ht₁ w).1 (by simpa using (ht₁ w).2)
      exact ⟨q, hq, by rw [ha, zero_add]; exact mul_ne_zero hd hq0⟩
    · exact ⟨0, by simpa using (ht₁ w).2, by rwa [mul_zero, add_zero]⟩
  have hch₂ : ∀ v : S, ∃ q : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F, q ∈ t₂ v ∧ a.2 v + d.2 v * q ≠ 0 := by
    intro v
    by_cases ha : a.2 v = 0
    · have hd : d.2 v ≠ 0 := fun hd => hrow_fin v ⟨ha, hd⟩
      obtain ⟨q, hq, hq0⟩ := exists_ne_zero_mem_fin F v (ht₂ v).1 (by simpa using (ht₂ v).2)
      exact ⟨q, hq, by rw [ha, zero_add]; exact mul_ne_zero hd hq0⟩
    · exact ⟨0, by simpa using (ht₂ v).2, by rwa [mul_zero, add_zero]⟩
  choose p₁ hp₁ hp₁' using hch₁
  choose p₂ hp₂ hp₂' using hch₂
  set y : AdeleRing (𝓞 F) F := e (p₁, p₂) with hydef
  have hyV : y ∈ V := by
    have : (p₁, p₂) ∈ u₁ ×ˢ u₂ :=
      ⟨ht₁sub (Set.mem_univ_pi.mpr fun w => hp₁ w), ht₂sub (Set.mem_univ_pi.mpr fun v => hp₂ v)⟩
    exact hsub this

  set z : AdeleRing (𝓞 F) F := a + d * y with hzdef
  have hz1 : ∀ w, z.1 w ≠ 0 := fun w => by
    change a.1 w + d.1 w * p₁ w ≠ 0; exact hp₁' w
  have hz2S : ∀ v : HeightOneSpectrum (𝓞 F), ∀ hv : v ∈ S, z.2 v = a.2 v + d.2 v * p₂ ⟨v, hv⟩ := fun v hv => by
    change a.2 v + d.2 v * (sec F S p₂) v = _; rw [sec_apply_of_mem F S _ hv]
  have hz2off : ∀ v ∉ S, z.2 v = 1 := fun v hv => by
    change a.2 v + d.2 v * (sec F S p₂) v = 1
    rw [(hoff v hv).1, (hoff v hv).2, zero_mul, add_zero]
  have hz2 : ∀ v, z.2 v ≠ 0 := fun v => by
    by_cases hv : v ∈ S
    · rw [hz2S v hv]; exact hp₂' ⟨v, hv⟩
    · rw [hz2off v hv]; exact one_ne_zero
  set zinv : AdeleRing (𝓞 F) F := (fun w => (z.1 w)⁻¹, (⟨fun v => (z.2 v)⁻¹,
      Filter.eventually_of_mem S.finite_toSet.compl_mem_cofinite fun v hv => by
        rw [Set.mem_compl_iff, Finset.mem_coe] at hv
        show (z.2 v)⁻¹ ∈ v.adicCompletionIntegers F
        rw [hz2off v hv, inv_one]; exact one_mem _⟩ : FiniteAdeleRing (𝓞 F) F)) with hzinv
  have hzz : z * zinv = 1 := by
    refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
    · exact mul_inv_cancel₀ (hz1 w)
    · exact mul_inv_cancel₀ (hz2 v)
  set c : (AdeleRing (𝓞 F) F)ˣ := ⟨z, zinv, hzz, by rw [mul_comm]; exact hzz⟩ with hcdef
  have hc : (c : AdeleRing (𝓞 F) F) = ((gy y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 := by
    change z = _
    rw [hzdef, hgydef]; dsimp only
    rw [entry10_mul_lower]
  exact hyV (hvan (gy y) c hc)

end WITNESS

end

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (_hφc : Continuous φ) (_hφf : IsKfSmooth F φ) (_hne : ∃ g, φ g ≠ 0),
    ∃ x : AdeleRing (𝓞 F) F, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ≠ 0 := by
  intro α hα s φ hφ hφc hφf hne
  exact WITNESS.main F α hα s φ hφ hφc hφf hne

end S_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth
end P2MW
export P2MW.S_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth (solution)
