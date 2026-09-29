-- Prove2me | solution 1 for AutomorphicForm.hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ea6b878b-3340-5d55-a2df-fef10e29ca6b

import Mathlib
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear

set_option autoImplicit false

noncomputable section

namespace UnipDeriv

set_option linter.unusedSectionVars false

open scoped Classical
open NumberField NumberField.AdelicLevel AutomorphicForm MeasureTheory Set Filter Topology

variable (K : Type) [Field K] [NumberField K]

abbrev MS := mixedEmbedding.mixedSpace K
abbrev eA := InfiniteAdeleRing.ringEquiv_mixedSpace K
abbrev Ent := Fin 2 → Fin 2 → MS K

def nA (s : MS K) : AdelicGL2 (𝓞 K) K := unipotentGL2 (R := AdeleRing (𝓞 K) K) ((eA K).symm s, 0)

theorem nA_add (s r : MS K) : nA K (s + r) = nA K s * nA K r := by
  rw [nA, nA, nA, ← unipotentGL2_add]
  congr 1
  refine Prod.ext ?_ ?_
  · show (eA K).symm (s + r) = (eA K).symm s + (eA K).symm r; rw [map_add]
  · show (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) = 0 + 0; rw [add_zero]

theorem nA_zero : nA K 0 = 1 := by
  rw [nA]
  have : (((eA K).symm 0, (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K) = 0 := by
    refine Prod.ext ?_ ?_
    · show (eA K).symm 0 = 0; rw [map_zero]
    · rfl
  rw [this]
  exact unipotentGL2_zero

theorem nA_inv (s : MS K) : (nA K s)⁻¹ = nA K (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← nA_add, add_neg_cancel, nA_zero])

theorem glFin_nA (s : MS K) : glFin (𝓞 K) K (nA K s) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [glFin_apply]
  show ((!![(1 : AdeleRing (𝓞 K) K), ((eA K).symm s, 0); 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
  fin_cases i <;> fin_cases j <;> rfl

theorem glArch_nA (s : MS K) : glArch (𝓞 K) K (nA K s) = unipotentGL2 ((eA K).symm s) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [glArch_apply]
  show ((!![(1 : AdeleRing (𝓞 K) K), ((eA K).symm s, 0); 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 =
    (!![(1 : InfiniteAdeleRing K), (eA K).symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
  fin_cases i <;> fin_cases j <;> rfl

theorem continuous_eA : Continuous (eA K) := by
  have h : ((eA K) : InfiniteAdeleRing K → MS K)
      = fun x => (fun (w : {w : InfinitePlace K // w.IsReal}) =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (x w.1),
        fun (w : {w : InfinitePlace K // w.IsComplex}) =>
          InfinitePlace.Completion.extensionEmbedding w.1 (x w.1)) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  rw [h]
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp (continuous_apply w.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp (continuous_apply w.1)

theorem continuous_eA_symm : Continuous (eA K).symm := by
  refine continuous_pi fun w => ?_
  by_cases hw : w.IsReal
  · have h : ∀ z : MS K, (eA K).symm z w = (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm (z.1 ⟨w, hw⟩) := by
      intro z
      have hy : eA K ((eA K).symm z) = z := RingEquiv.apply_symm_apply _ _
      have h1 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((eA K).symm z w) = z.1 ⟨w, hw⟩ := by
        have := congrArg (fun p : MS K => p.1 ⟨w, hw⟩) hy
        simpa [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] using this
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact h1
    rw [show (fun z : MS K => (eA K).symm z w) = _ from funext h]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have h : ∀ z : MS K, (eA K).symm z w = (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw').symm (z.2 ⟨w, hw'⟩) := by
      intro z
      have hy : eA K ((eA K).symm z) = z := RingEquiv.apply_symm_apply _ _
      have h1 : InfinitePlace.Completion.extensionEmbedding w ((eA K).symm z w) = z.2 ⟨w, hw'⟩ := by
        have := congrArg (fun p : MS K => p.2 ⟨w, hw'⟩) hy
        simpa [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] using this
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw').injective
      rw [IsometryEquiv.apply_symm_apply]
      exact h1
    rw [show (fun z : MS K => (eA K).symm z w) = _ from funext h]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw').symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

theorem continuous_unipotentGL2 {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (unipotentGL2 (R := R)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ unipotentGL2 (R := R)) = fun x => !![(1 : R), x; 0, 1] := by funext x; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun x => ((unipotentGL2 (R := R) x)⁻¹ : GL (Fin 2) R).val) = fun x => !![(1 : R), -x; 0, 1] := by funext x; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_nA : Continuous (nA K) :=
  continuous_unipotentGL2.comp ((continuous_eA_symm K).prodMk continuous_const)

theorem continuous_archEntries : Continuous (archEntries K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_eA K).comp ((continuous_id.matrix_elem i j).comp Units.continuous_val)

def N (v : MS K) (m : Ent K) : Ent K := fun i j => if i = 0 then v * m 1 j else 0

theorem N_add_smul (a b : ℝ) (v w : MS K) (m : Ent K) : N K (a • v + b • w) m = a • N K v m + b • N K w m := by
  funext i j
  simp only [N, Pi.add_apply, Pi.smul_apply]
  split_ifs
  · rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  · rw [smul_zero, smul_zero, add_zero]

theorem N_smul (a : ℝ) (v : MS K) (m : Ent K) : N K (a • v) m = a • N K v m := by
  have := N_add_smul K a 0 v 0 m
  simpa using this

theorem N_neg (v : MS K) (m : Ent K) : N K (-v) m = -N K v m := by
  have := N_smul K (-1) v m
  simpa using this

def NL (v : MS K) : Ent K →L[ℝ] Ent K :=
  LinearMap.toContinuousLinearMap
    { toFun := N K v
      map_add' := fun m m' => by funext i j; simp only [N, Pi.add_apply]; split_ifs <;> simp [mul_add]
      map_smul' := fun c m => by funext i j; simp only [N, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

theorem NL_apply (v : MS K) (m : Ent K) : NL K v m = N K v m := rfl

theorem archEntries_unipotent_mul (s : MS K) (z : GL (Fin 2) (InfiniteAdeleRing K)) :
    archEntries K (unipotentGL2 ((eA K).symm s) * z) = archEntries K z + N K s (archEntries K z) := by
  funext i j
  simp only [archEntries_apply, Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply, N]
  dsimp only [eA]
  set e : InfiniteAdeleRing K ≃+* MS K := InfiniteAdeleRing.ringEquiv_mixedSpace K with he
  clear_value e
  have h00 : (!![(1 : InfiniteAdeleRing K), e.symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 = 1 := rfl
  have h01 : (!![(1 : InfiniteAdeleRing K), e.symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = e.symm s := rfl
  have h10 : (!![(1 : InfiniteAdeleRing K), e.symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 := rfl
  have h11 : (!![(1 : InfiniteAdeleRing K), e.symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 = 1 := rfl
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, map_add, map_mul, ↓reduceIte]
    rw [h00, h01, map_one, one_mul, RingEquiv.apply_symm_apply]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, add_zero]
    rw [h10, h11, zero_mul, one_mul, zero_add]

section Curve

variable {K}
variable {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
  {Φ : Ent K → ℂ} {f : AdelicGL2 (𝓞 K) K → ℂ}

abbrev E (y : AdelicGL2 (𝓞 K) K) : Ent K := archEntries K (glArch (𝓞 K) K y)

def Lf (Φ : Ent K → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ) (v : MS K) (t : ℝ)
    (y : AdelicGL2 (𝓞 K) K) : ℂ :=
  (fderiv ℝ Φ (E y - t • N K v (E y))) (-N K v (E y)) * ff (glFin (𝓞 K) K y)

theorem curve_eq (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hf : ∀ g, f g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (v : MS K) (y : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    f (nA K (-(t • v)) * y) = Φ (E y - t • N K v (E y)) * ff (glFin (𝓞 K) K y) := by
  rw [hf, map_mul, map_mul, glFin_nA, one_mul, glArch_nA, hfa, archEntries_unipotent_mul, N_neg, N_smul, sub_eq_add_neg]

theorem hasDerivAt_curve (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hf : ∀ g, f g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (v : MS K) (y : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (nA K (-(s • v)) * y)) (Lf Φ ff v t y) t := by
  have hfun : (fun s : ℝ => f (nA K (-(s • v)) * y)) = fun s => Φ (E y - s • N K v (E y)) * ff (glFin (𝓞 K) K y) :=
    funext fun s => curve_eq hfa hf v y s
  rw [hfun, Lf]
  have hinner : HasDerivAt (fun s : ℝ => E y - s • N K v (E y)) (-N K v (E y)) t := by
    have := ((hasDerivAt_id t).smul_const (N K v (E y))).const_sub (E y)
    simpa using this
  have hdiff : DifferentiableAt ℝ Φ (E y - t • N K v (E y)) :=
    (hΦ.differentiable (by simp)).differentiableAt
  exact (hdiff.hasFDerivAt.comp_hasDerivAt t hinner).mul_const _

theorem deriv_curve (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hf : ∀ g, f g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (v : MS K) (y : AdelicGL2 (𝓞 K) K) :
    deriv (fun s : ℝ => f (nA K (-(s • v)) * y)) 0 = Lf Φ ff v 0 y :=
  (hasDerivAt_curve hΦ hfa hf v y 0).deriv

def Φv (Φ : Ent K → ℂ) (v : MS K) (m : Ent K) : ℂ := (fderiv ℝ Φ m) (-N K v m)

theorem Lf_zero (v : MS K) (y : AdelicGL2 (𝓞 K) K) :
    Lf Φ ff v 0 y = Φv Φ v (archEntries K (glArch (𝓞 K) K y)) * ff (glFin (𝓞 K) K y) := by
  simp only [Lf, Φv, zero_smul, sub_zero]

theorem contDiff_Φv (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : MS K) : ContDiff ℝ (⊤ : ℕ∞) (Φv Φ v) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Φ) := (contDiff_infty_iff_fderiv.1 hΦ).2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun m : Ent K => -N K v m := (NL K v).contDiff.neg
  exact h1.clm_apply h2

theorem Φv_eq_zero (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z)) (v : MS K)
    {z : GL (Fin 2) (InfiniteAdeleRing K)} (hz : z ∉ tsupport fa) : Φv Φ v (archEntries K z) = 0 := by

  have hcurve : HasDerivAt (fun s : ℝ => fa (unipotentGL2 ((eA K).symm (-(s • v))) * z)) (Φv Φ v (archEntries K z)) 0 := by
    have hfun : (fun s : ℝ => fa (unipotentGL2 ((eA K).symm (-(s • v))) * z)) =
        fun s => Φ (archEntries K z - s • N K v (archEntries K z)) := by
      funext s
      rw [hfa, archEntries_unipotent_mul, N_neg, N_smul, sub_eq_add_neg]
    rw [hfun, Φv]
    have hinner : HasDerivAt (fun s : ℝ => archEntries K z - s • N K v (archEntries K z)) (-N K v (archEntries K z)) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const (N K v (archEntries K z))).const_sub (archEntries K z)
      simpa using this
    have hdiff : DifferentiableAt ℝ Φ (archEntries K z - (0 : ℝ) • N K v (archEntries K z)) :=
      (hΦ.differentiable (by simp)).differentiableAt
    have := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinner
    simp at this ⊢
    exact this
  have hcont : Continuous fun s : ℝ => unipotentGL2 ((eA K).symm (-(s • v))) * z :=
    (continuous_unipotentGL2.comp ((continuous_eA_symm K).comp (continuous_id.smul continuous_const).neg)).mul
      continuous_const
  have h0 : unipotentGL2 ((eA K).symm (-((0 : ℝ) • v))) * z = z := by
    rw [zero_smul, neg_zero, map_zero, unipotentGL2_zero, one_mul]
  have hev : (fun s : ℝ => fa (unipotentGL2 ((eA K).symm (-(s • v))) * z)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have hmem : (tsupport fa)ᶜ ∈ 𝓝 (unipotentGL2 ((eA K).symm (-((0 : ℝ) • v))) * z) := by
      rw [h0]; exact (isClosed_tsupport fa).isOpen_compl.mem_nhds hz
    filter_upwards [hcont.continuousAt.preimage_mem_nhds hmem] with s hs
    exact image_eq_zero_of_notMem_tsupport hs
  have hzero : HasDerivAt (fun s : ℝ => fa (unipotentGL2 ((eA K).symm (-(s • v))) * z)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hev
  exact hcurve.unique hzero

theorem hasCompactSupport_Φv (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hsupp : HasCompactSupport fa) (v : MS K) : HasCompactSupport fun z => Φv Φ v (archEntries K z) := by
  refine hsupp.mono' fun z hz => ?_
  by_contra hzt
  exact hz (Φv_eq_zero hΦ hfa v hzt)

end Curve

theorem continuous_Lf {Φ : Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsLocallyConstant ff) (v : MS K) :
    Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => Lf Φ ff v p.1 p.2 := by
  have hE : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => E p.2 :=
    (continuous_archEntries K).comp ((continuous_glArch (𝓞 K) K).comp continuous_snd)
  have hN : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => N K v (E p.2) := (NL K v).continuous.comp hE
  have hpt : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => E p.2 - p.1 • N K v (E p.2) :=
    hE.sub (continuous_fst.smul hN)
  have hD : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => fderiv ℝ Φ (E p.2 - p.1 • N K v (E p.2)) :=
    (hΦ.continuous_fderiv (by simp)).comp hpt
  have hff' : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => ff (glFin (𝓞 K) K p.2) :=
    hff.continuous.comp ((continuous_glFin (𝓞 K) K).comp continuous_snd)
  unfold Lf
  exact (hD.clm_apply hN.neg).mul hff'

theorem main (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {Φ : Ent K → ℂ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z)) (hff : IsLocallyConstant ff)
    (hf : ∀ g, f g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    (hfc : Continuous f) (hfs : HasCompactSupport f) (v : MS K) (g : AdelicGL2 (𝓞 K) K) :
    HasDerivAt (fun t : ℝ => rightConv K φ f (g * nA K (t • v))) (rightConv K φ (Lf Φ ff v 0) g) 0 := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  have ha : ∀ t : ℝ, rightConv K φ f (g * nA K (t • v)) = ∫ y, φ (g * y) * f (nA K (-(t • v)) * y) ∂μ := by
    intro t
    rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, nA_inv, rightConv_apply]

  set F : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t y => φ (g * y) * f (nA K (-(t • v)) * y) with hF
  set F' : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t y => φ (g * y) * Lf Φ ff v t y with hF'
  have hderiv : ∀ (y : AdelicGL2 (𝓞 K) K) (t : ℝ), HasDerivAt (fun s => F s y) (F' t y) t := fun y t =>
    (hasDerivAt_curve hΦ hfa hf v y t).const_mul _

  set C : Set (AdelicGL2 (𝓞 K) K) := (fun p : ℝ × AdelicGL2 (𝓞 K) K => nA K (p.1 • v) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport f) with hC
  have hCcpt : IsCompact C :=
    ((isCompact_closedBall (0 : ℝ) 1).prod hfs).image
      (((continuous_nA K).comp (continuous_fst.smul continuous_const)).mul continuous_snd)
  have hout : ∀ y, y ∉ C → ∀ t ∈ Metric.ball (0 : ℝ) 1, F' t y = 0 := by
    intro y hy t ht

    have hoff : ∀ s ∈ Metric.ball (0 : ℝ) 1, f (nA K (-(s • v)) * y) = 0 := by
      intro s hs
      by_contra hne
      apply hy
      refine ⟨(s, nA K (-(s • v)) * y), ⟨Metric.ball_subset_closedBall hs, subset_tsupport _ hne⟩, ?_⟩
      show nA K (s • v) * (nA K (-(s • v)) * y) = y
      rw [← mul_assoc, ← nA_add, add_neg_cancel, nA_zero, one_mul]
    have hev : (fun s : ℝ => f (nA K (-(s • v)) * y)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
      exact hoff s hs
    have hz : HasDerivAt (fun s : ℝ => f (nA K (-(s • v)) * y)) 0 t :=
      (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hev
    have := (hasDerivAt_curve hΦ hfa hf v y t).unique hz
    show φ (g * y) * Lf Φ ff v t y = 0
    rw [this, mul_zero]

  have hF'cont : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => F' p.1 p.2 :=
    ((hcont.comp (continuous_const.mul continuous_snd))).mul (continuous_Lf K hΦ hff v)
  obtain ⟨Mb, hMb⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hCcpt).exists_bound_of_continuousOn hF'cont.continuousOn
  have hCm : MeasurableSet C := hCcpt.isClosed.measurableSet
  have hbound_int : Integrable (fun y => if y ∈ C then Mb else 0) μ :=
    (integrableOn_const (C := Mb) hCcpt.measure_lt_top.ne).integrable_indicator hCm
  have h_bound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t y‖ ≤ if y ∈ C then Mb else 0 := by
    refine Eventually.of_forall fun y t ht => ?_
    by_cases hy : y ∈ C
    · rw [if_pos hy]; exact hMb (t, y) ⟨Metric.ball_subset_closedBall ht, hy⟩
    · rw [if_neg hy, hout y hy t ht, norm_zero]

  have hFt : ∀ t : ℝ, Continuous (F t) := fun t =>
    (hcont.comp (continuous_const.mul continuous_id)).mul (hfc.comp (continuous_const.mul continuous_id))
  have hint0 : Integrable (F 0) μ := by
    have hsupp : HasCompactSupport (F 0) := by
      have h1 : HasCompactSupport fun y : AdelicGL2 (𝓞 K) K => f (nA K (-((0 : ℝ) • v)) * y) := by
        rw [zero_smul, neg_zero, nA_zero]; simpa using hfs
      exact h1.mul_left
    exact (hFt 0).integrable_of_hasCompactSupport hsupp
  have hF'0m : AEStronglyMeasurable (F' 0) μ :=
    (hF'cont.comp ((continuous_const : Continuous fun _ : AdelicGL2 (𝓞 K) K => (0 : ℝ)).prodMk continuous_id)).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (s := Metric.ball (0 : ℝ) 1) (bound := fun y => if y ∈ C then Mb else 0) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t => (hFt t).aestronglyMeasurable) hint0 hF'0m h_bound hbound_int
    (Eventually.of_forall fun y t _ => hderiv y t)

  have hfun : (fun t : ℝ => rightConv K φ f (g * nA K (t • v))) = fun t => ∫ y, F t y ∂μ := funext ha
  have hval : (∫ y, F' 0 y ∂μ) = rightConv K φ (Lf Φ ff v 0) g := by rw [rightConv_apply]
  rw [hfun, ← hval]
  exact key.2

end UnipDeriv

end

open NumberField AutomorphicForm

open UnipDeriv in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    (∀ (v : mixedEmbedding.mixedSpace K) (g : AdelicGL2 (𝓞 K) K),
        HasDerivAt (fun t : ℝ => rightConv K φ f (g * unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)))
          (rightConv K φ (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0) g) 0) ∧
    (∀ v : mixedEmbedding.mixedSpace K,
        IsFactorizableTestFn K (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0)) ∧
    (∀ (a b : ℝ) (v w : mixedEmbedding.mixedSpace K) (y : AdelicGL2 (𝓞 K) K),
        deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • (a • v + b • w))), 0) * y)) 0 =
          a * deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0 +
            b * deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • w)), 0) * y)) 0) := by
  classical
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, ⟨hff, hffs⟩, hfeq⟩ := hf

  have hL : ∀ (v : mixedEmbedding.mixedSpace K) (y : AdelicGL2 (𝓞 K) K),
      deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0 = Lf Φ ff v 0 y :=
    fun v y => deriv_curve hΦ hfa hfeq v y
  refine ⟨fun v g => ?_, fun v => ?_, fun a b v w y => ?_⟩
  · have h := main K φ hcont f hΦ hfa hff hfeq hfc hfs v g
    have hfun : (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0) = Lf Φ ff v 0 := funext (hL v)
    rw [hfun]
    exact h
  · refine ⟨fun z => Φv Φ v (archEntries K z), ff, ⟨⟨Φv Φ v, contDiff_Φv hΦ v, fun _ => rfl⟩,
      hasCompactSupport_Φv hΦ hfa hsupp v⟩, ⟨hff, hffs⟩, fun y => ?_⟩
    beta_reduce
    rw [hL v y, Lf_zero]
  · rw [hL, hL, hL, Lf_zero, Lf_zero, Lf_zero]
    simp only [Φv, N_add_smul, neg_add, map_add, map_neg, map_smul, Complex.real_smul]
    ring

end S_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
end P2MW
export P2MW.S_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear (solution)
