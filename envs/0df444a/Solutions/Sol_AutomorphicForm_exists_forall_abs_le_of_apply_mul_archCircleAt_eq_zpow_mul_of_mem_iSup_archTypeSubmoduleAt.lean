-- Prove2me | solution 1 for AutomorphicForm.exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8e024cb8-d1d5-5b84-8c25-8cbf8d135e48

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open NumberField.InfinitePlace.Completion

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace Kw1C

variable (F : Type) [Field F] [NumberField F]

theorem adelicArchGLInclAt_coe_apply (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (archMatrixUpdate F w k.val i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) := by
  rfl

theorem continuous_archMatrixUpdate_entry (w : InfinitePlace F) (i j : Fin 2) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) w.Completion => archMatrixUpdate F w m i j := by
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp_rw [archMatrixUpdate_apply_self]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp_rw [archMatrixUpdate_apply_of_ne F _ _ i j hv]
    exact continuous_const

theorem continuous_coe_adelicArchGLInclAt (w : InfinitePlace F) :
    Continuous fun k : GL (Fin 2) w.Completion =>
      ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  refine continuous_matrix fun i j => ?_
  simp_rw [adelicArchGLInclAt_coe_apply]
  exact ((continuous_archMatrixUpdate_entry F w i j).comp Units.continuous_val).prodMk continuous_const

theorem continuous_adelicArchGLInclAt (w : InfinitePlace F) : Continuous (adelicArchGLInclAt F w) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_coe_adelicArchGLInclAt F w, ?_⟩
  have : (fun k : GL (Fin 2) w.Completion => ((adelicArchGLInclAt F w k)⁻¹ : AdelicGL2 (𝓞 F) F).val) =
      (fun k => ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ∘
        fun k => k⁻¹ := by
    funext k; simp [map_inv]
  rw [this]
  exact (continuous_coe_adelicArchGLInclAt F w).comp continuous_inv

theorem continuous_rowIsometryInclAt₀ (w : InfinitePlace F) : Continuous (rowIsometryInclAt₀ F w) :=
  (continuous_adelicArchGLInclAt F w).comp continuous_subtype_val

theorem injective_rowIsometryInclAt₀ (w : InfinitePlace F) : Function.Injective (rowIsometryInclAt₀ F w) := by
  intro k k' h
  apply Subtype.ext
  have h1 : archComponent F w (glArch (𝓞 F) F (rowIsometryInclAt₀ F w k)) =
      archComponent F w (glArch (𝓞 F) F (rowIsometryInclAt₀ F w k')) := by rw [h]
  have e : ∀ k : rowIsometrySubgroup₀ w.Completion,
      archComponent F w (glArch (𝓞 F) F (rowIsometryInclAt₀ F w k)) = (k : GL (Fin 2) w.Completion) := fun k => by
    show archComponent F w (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w (k : GL (Fin 2) w.Completion)))) = _
    rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_self]
  rwa [e, e] at h1

variable {F}

section CircleElt

variable {w : InfinitePlace F} (hw : w.IsComplex)

theorem circleGL2_mem (ζ : ℂˣ) (hζ : ‖(ζ : ℂ)‖ = 1) : circleGL2 ζ ∈ rowIsometrySubgroup₀ ℂ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  have hζi : ‖((ζ⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hζ, inv_one]
  have hdet : ((circleGL2 ζ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    show (!![(ζ : ℂ), 0; 0, ((ζ⁻¹ : ℂˣ) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).det = 1
    rw [Matrix.det_fin_two_of]
    simp
  refine ⟨hdet, ?_, fun x y => ?_⟩
  · rw [hdet, norm_one]
  · show ‖x * (ζ : ℂ) + y * 0‖ ^ 2 + ‖x * 0 + y * ((ζ⁻¹ : ℂˣ) : ℂ)‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [mul_zero, mul_zero, add_zero, zero_add, norm_mul, norm_mul, hζ, hζi, mul_one, mul_one]

theorem norm_ringEquivComplexOfIsComplex (x : w.Completion) : ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem norm_symm_ringEquivComplexOfIsComplex (y : ℂ) : ‖(ringEquivComplexOfIsComplex hw).symm y‖ = ‖y‖ := by
  have := norm_ringEquivComplexOfIsComplex hw ((ringEquivComplexOfIsComplex hw).symm y)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

abbrev cU (ζ : Circle) : ℂˣ := Units.mk0 (ζ : ℂ) (Circle.coe_ne_zero ζ)

theorem norm_cU (ζ : Circle) : ‖((cU ζ : ℂˣ) : ℂ)‖ = 1 := Circle.norm_coe ζ

def kC (ζ : Circle) : rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivComplexOfIsComplex hw).symm (norm_symm_ringEquivComplexOfIsComplex hw)
    ⟨circleGL2 (cU ζ), circleGL2_mem (cU ζ) (norm_cU ζ)⟩

theorem archCircleAt_eq (ζ : Circle) : archCircleAt hw (cU ζ) = rowIsometryInclAt₀ F w (kC hw ζ) := rfl

theorem apply_mul_kC {m : ℤ} {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : HasCircleWeightAt hw m f) (ζ : Circle)
    (g : AdelicGL2 (𝓞 F) F) : f (g * rowIsometryInclAt₀ F w (kC hw ζ)) = (ζ : ℂ) ^ m * f g := by
  rw [← archCircleAt_eq]
  exact hf (cU ζ) (norm_cU ζ) g

def χ (m : ℤ) : Circle →* ℂ where
  toFun ζ := (ζ : ℂ) ^ m
  map_one' := by simp
  map_mul' a b := by rw [Circle.coe_mul, mul_zpow]

theorem χ_apply (m : ℤ) (ζ : Circle) : χ m ζ = (ζ : ℂ) ^ m := rfl

theorem exp_I_ne_one : Complex.exp Complex.I ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have him := congrArg Complex.im hn
  simp only [Complex.I_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero,
    add_zero, mul_one, zero_add] at him
  have hpos : (0 : ℝ) < (n : ℝ) := by nlinarith [Real.pi_pos]
  have hn1 : (1 : ℤ) ≤ n := by have := Int.cast_pos.1 hpos; omega
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  nlinarith [Real.pi_gt_three]

theorem χ_injective : Function.Injective (χ : ℤ → Circle →* ℂ) := by
  intro m m' h
  by_contra hne
  have hd : ((m - m' : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  set θ : ℝ := ((m - m' : ℤ) : ℝ)⁻¹ with hθ
  have h1 := congrArg (fun c : Circle →* ℂ => c (Circle.exp θ)) h
  simp only [χ_apply, Circle.coe_exp] at h1

  have h2 : Complex.exp (θ * Complex.I) ^ (m - m') = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  rw [← Complex.exp_int_mul] at h2
  have h3 : ((m - m' : ℤ) : ℂ) * ((θ : ℝ) * Complex.I) = Complex.I := by
    have : ((m - m' : ℤ) : ℝ) * θ = 1 := mul_inv_cancel₀ hd
    have h4 : (((m - m' : ℤ) : ℝ) : ℂ) * ((θ : ℝ) : ℂ) = 1 := by exact_mod_cast this
    push_cast at h4 ⊢
    linear_combination Complex.I * h4
  rw [h3] at h2
  exact exp_I_ne_one h2

end CircleElt

section Window

variable {w : InfinitePlace F} (hw : w.IsComplex)

theorem mulVec_family_eq_sum {r n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin r → Fin n → ℂ) :
    (fun j => A.mulVec (u j)) = ∑ ab : Fin n × Fin n, A ab.1 ab.2 • (fun j a' => if a' = ab.1 then u j ab.2 else 0) := by
  funext j a'
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter, show (Finset.univ.filter fun ab : Fin n × Fin n => a' = ab.1) =
    (Finset.univ : Finset (Fin n)).map ⟨fun b => (a', b), fun b b' h => by simpa using h⟩ from ?_]
  · rw [Finset.sum_map]
    rfl
  · ext ⟨a, b⟩
    simp [eq_comm]

theorem exists_finset_weights (m₀ : ℕ) (ρs : Fin m₀ → ArchRepAt F w) :
    ∃ Λ : Finset ℤ, ∀ f : AdelicGL2 (𝓞 F) F → ℂ, Continuous f → f ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
      ∀ (x₀ : AdelicGL2 (𝓞 F) F) (m : ℤ),
        (∀ ζ : ℂˣ, ‖(ζ : ℂ)‖ = 1 → f (x₀ * archCircleAt hw ζ) = (ζ : ℂ) ^ m * f x₀) → f x₀ ≠ 0 → m ∈ Λ := by
  classical
  haveI : CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
    isCompact_iff_compactSpace.1 (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  obtain ⟨n, ρc, hρc, H⟩ :=
    AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
      (K := rowIsometrySubgroup₀ w.Completion) (fun i : Fin m₀ => (ρs i).ρ)
  obtain ⟨-, H3⟩ := H (AdelicGL2 (𝓞 F) F) (rowIsometryInclAt₀ F w) (injective_rowIsometryInclAt₀ F w)

  set MC : Submodule ℂ (Circle → ℂ) :=
    Submodule.span ℂ (Set.range fun ab : Fin n × Fin n => fun ζ : Circle => ρc (kC hw ζ) ab.1 ab.2) with hMC
  haveI : FiniteDimensional ℂ MC := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  set Λs : Set ℤ := {m | ((χ m : Circle →* ℂ) : Circle → ℂ) ∈ MC} with hΛs
  have hfin : Λs.Finite := by
    let v : Λs → MC := fun m => ⟨(χ m.1 : Circle → ℂ), m.2⟩
    have hv : LinearIndependent ℂ v := by
      apply LinearIndependent.of_comp MC.subtype
      show LinearIndependent ℂ ((fun c : Circle →* ℂ => (c : Circle → ℂ)) ∘ fun m : Λs => χ m.1)
      exact (linearIndependent_monoidHom Circle ℂ).comp _ (χ_injective.comp Subtype.val_injective)
    haveI : Finite Λs := hv.finite_of_isNoetherian
    exact Set.toFinite Λs
  refine ⟨hfin.toFinset, fun f hfc hf x₀ m hm hx₀ => ?_⟩
  rw [Set.Finite.mem_toFinset]
  show ((χ m : Circle →* ℂ) : Circle → ℂ) ∈ MC

  obtain ⟨r, T, hT, hrange⟩ := H3 f hf (fun y => hfc.comp (continuous_const.mul (continuous_rowIsometryInclAt₀ F w)))
  have hfT : f ∈ LinearMap.range T := by
    rw [hrange]
    refine Submodule.subset_span ⟨1, ?_⟩
    funext y
    show f (y * rowIsometryInclAt₀ F w 1) = f y
    rw [map_one, mul_one]
  obtain ⟨u₀, hu₀⟩ := hfT

  have key : ∀ ζ : Circle, (ζ : ℂ) ^ m * f x₀ =
      ∑ ab : Fin n × Fin n, ρc (kC hw ζ) ab.1 ab.2 * T (fun j a' => if a' = ab.1 then u₀ j ab.2 else 0) x₀ := by
    intro ζ
    have hm' : f (x₀ * rowIsometryInclAt₀ F w (kC hw ζ)) = (ζ : ℂ) ^ m * f x₀ := hm (cU ζ) (norm_cU ζ)
    rw [← hm', ← hu₀]
    have e := congrFun (hT (kC hw ζ) u₀) x₀
    rw [← e, mulVec_family_eq_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  have hmem : (fun ζ : Circle => (ζ : ℂ) ^ m * f x₀) ∈ MC := by
    have : (fun ζ : Circle => (ζ : ℂ) ^ m * f x₀) =
        ∑ ab : Fin n × Fin n, T (fun j a' => if a' = ab.1 then u₀ j ab.2 else 0) x₀ •
          (fun ζ : Circle => ρc (kC hw ζ) ab.1 ab.2) := by
      funext ζ
      rw [key ζ, Finset.sum_apply]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun ab _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ab, rfl⟩)
  have : ((χ m : Circle →* ℂ) : Circle → ℂ) = (f x₀)⁻¹ • fun ζ : Circle => (ζ : ℂ) ^ m * f x₀ := by
    funext ζ
    rw [Pi.smul_apply, smul_eq_mul, χ_apply, mul_comm ((ζ : ℂ) ^ m) (f x₀), ← mul_assoc, inv_mul_cancel₀ hx₀, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

end Window

end Kw1C

open Kw1C in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (tys : ArchTypeFamily K) :
    ∃ n₀ : ℕ,
      ∀ (w : InfinitePlace K) (hw : w.IsComplex) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous f → f ∈ (⨆ i : Fin (tys.card w), archTypeSubmoduleAt K w (tys.rep w i)) →
        ∀ (x₀ : AdelicGL2 (𝓞 K) K) (m : ℤ),
          (∀ ζ : ℂˣ, ‖(ζ : ℂ)‖ = 1 → f (x₀ * archCircleAt hw ζ) = (ζ : ℂ) ^ m * f x₀) →
          f x₀ ≠ 0 → |m| ≤ (n₀ : ℤ) := by
  classical

  have hΛ : ∀ w : InfinitePlace K, ∃ Λ : Finset ℤ, ∀ (hw : w.IsComplex) (f : AdelicGL2 (𝓞 K) K → ℂ),
      Continuous f → f ∈ (⨆ i : Fin (tys.card w), archTypeSubmoduleAt K w (tys.rep w i)) →
      ∀ (x₀ : AdelicGL2 (𝓞 K) K) (m : ℤ),
        (∀ ζ : ℂˣ, ‖(ζ : ℂ)‖ = 1 → f (x₀ * archCircleAt hw ζ) = (ζ : ℂ) ^ m * f x₀) → f x₀ ≠ 0 → m ∈ Λ := by
    intro w
    by_cases hw : w.IsComplex
    · obtain ⟨Λ, hΛ⟩ := exists_finset_weights (F := K) hw (tys.card w) (tys.rep w)
      exact ⟨Λ, fun hw' f hfc hf x₀ m hm hx => hΛ f hfc hf x₀ m hm hx⟩
    · exact ⟨∅, fun hw' => absurd hw' hw⟩
  choose Λ hΛ using hΛ
  refine ⟨Finset.univ.sup fun w => (Λ w).sup fun m => m.natAbs, ?_⟩
  intro w hw f hfc hf x₀ m hm hx
  have hmem : m ∈ Λ w := hΛ w hw f hfc hf x₀ m hm hx
  have h1 : m.natAbs ≤ (Λ w).sup fun m => m.natAbs := Finset.le_sup (f := fun m : ℤ => m.natAbs) hmem
  have h2 : ((Λ w).sup fun m => m.natAbs) ≤ Finset.univ.sup fun w => (Λ w).sup fun m => m.natAbs :=
    Finset.le_sup (f := fun w => (Λ w).sup fun m : ℤ => m.natAbs) (Finset.mem_univ w)
  have h3 : (m.natAbs : ℤ) ≤ ((Finset.univ.sup fun w => (Λ w).sup fun m => m.natAbs : ℕ) : ℤ) := by
    exact_mod_cast h1.trans h2
  rwa [Int.natCast_natAbs] at h3

end
end S_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt (solution)
