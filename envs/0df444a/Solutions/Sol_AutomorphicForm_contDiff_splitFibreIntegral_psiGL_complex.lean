-- Prove2me | solution 1 for AutomorphicForm.contDiff_splitFibreIntegral_psiGL_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7627e289-5371-535d-acaa-7ee1d8932692

import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 800000

open MeasureTheory AutomorphicForm AutomorphicForm.SplitPlace Metric Topology Filter Set TopologicalSpace

open scoped TensorProduct TensorProduct.RightActions ContDiff

noncomputable section

namespace P2mSplitFibreSmoothComplex

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.isTopologicalRing_tensor

section Parametric

variable {T : Type} [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]
  {μ : Measure T} [IsFiniteMeasureOnCompacts μ] {S : Set T} (hS : IsCompact S)
  {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  {c : T → M} (hc : Continuous c)

def dP {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : M × P → E) :
    M × P → (P →L[ℝ] E) :=
  fun q => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inr ℝ M P)

theorem contDiff_dP {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : M × P → E}
    (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (dP Ψ) :=
  (contDiff_infty_iff_fderiv.mp hΨ).2.clm_comp contDiff_const

theorem hasFDerivAt_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : M × P → E}
    (hΨ : ContDiff ℝ ∞ Ψ) (m : M) (p : P) :
    HasFDerivAt (fun p => Ψ (m, p)) (dP Ψ (m, p)) p :=
  ((hΨ.differentiable (by simp)) (m, p)).hasFDerivAt.comp p (hasFDerivAt_prodMk_right m p)

include hS hc in
theorem integrableOn_comp {E : Type} [NormedAddCommGroup E] {Ψ : M × P → E}
    (hΨ : Continuous Ψ) (p : P) : IntegrableOn (fun t => Ψ (c t, p)) S μ :=
  ContinuousOn.integrableOn_compact hS (hΨ.comp (hc.prodMk continuous_const)).continuousOn

include hS hc in

theorem exists_bound {E : Type} [NormedAddCommGroup E] {Φ : M × P → E} (hΦ : Continuous Φ) (p₀ : P) :
    ∃ C : ℝ, ∀ t ∈ S, ∀ p ∈ closedBall p₀ 1, ‖Φ (c t, p)‖ ≤ C := by
  have hK : IsCompact (S ×ˢ closedBall p₀ (1 : ℝ)) := hS.prod (isCompact_closedBall _ _)
  have hcont : Continuous fun z : T × P => Φ (c z.1, z.2) :=
    hΦ.comp ((hc.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨C, fun t ht p hp => hC (t, p) ⟨ht, hp⟩⟩

include hS hc in

theorem hasFDerivAt_setIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Ψ : M × P → E} (hΨ : ContDiff ℝ ∞ Ψ) (p₀ : P) :
    HasFDerivAt (fun p => ∫ t in S, Ψ (c t, p) ∂μ) (∫ t in S, dP Ψ (c t, p₀) ∂μ) p₀ := by
  obtain ⟨C, hC⟩ := exists_bound hS hc (contDiff_dP hΨ).continuous p₀
  have hSm : MeasurableSet S := hS.measurableSet
  haveI : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hS.measure_lt_top⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ.restrict S)
    (F := fun p t => Ψ (c t, p)) (F' := fun p t => dP Ψ (c t, p)) (bound := fun _ => C)
    (ball_mem_nhds p₀ one_pos)
    (Eventually.of_forall fun p =>
      (integrableOn_comp hS hc hΨ.continuous p).integrable.aestronglyMeasurable)
    (integrableOn_comp hS hc hΨ.continuous p₀).integrable
    ((integrableOn_comp hS hc (contDiff_dP hΨ).continuous p₀).integrable.aestronglyMeasurable)
    ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun t ht p hp =>
      hC t ht p (ball_subset_closedBall hp)))
    (integrable_const C)
    (Eventually.of_forall fun t p _ => hasFDerivAt_slice hΨ (c t) p)

include hS hc in

theorem contDiff_setIntegral_nat (n : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ψ : M × P → E} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ n (fun p => ∫ t in S, Ψ (c t, p) ∂μ) := by
  induction n generalizing E with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p => (hasFDerivAt_setIntegral hS hc hΨ p).continuousAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨fun p => ∫ t in S, dP Ψ (c t, p) ∂μ, ih (contDiff_dP hΨ),
      fun p => hasFDerivAt_setIntegral hS hc hΨ p⟩

include hS hc in

theorem contDiff_setIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Ψ : M × P → E} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (fun p => ∫ t in S, Ψ (c t, p) ∂μ) :=
  contDiff_infty.mpr fun n => contDiff_setIntegral_nat hS hc n hΨ

end Parametric

section GLTopology

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem borelSpace_GL : BorelSpace (GL (Fin 2) R) := ⟨rfl⟩

theorem t2Space_GL [T2Space R] : T2Space (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology R] :
    SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space R] [LocallyCompactSpace R] :
    LocallyCompactSpace (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → R))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end GLTopology

attribute [local instance] borelSpace_GL t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL

section Coords

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A) (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def matPsi :
    Matrix (Fin 2) (Fin 2) (L ⊗[K] A) ≃ₜ* (Fin (Module.finrank K L) → Matrix (Fin 2) (Fin 2) A) :=
  { ((psiEquiv A σ ι hdeg hσ).toRingEquiv.mapMatrix.trans
      (Matrix.piRingEquiv (β := fun _ : Fin (Module.finrank K L) => A) (n := Fin 2))).toMulEquiv with
    continuous_toFun := by
      refine continuous_pi fun i => continuous_pi fun p => continuous_pi fun q => ?_
      exact (continuous_apply i).comp ((continuous_psi A σ ι).comp
        ((continuous_apply q).comp (continuous_apply p)))
    continuous_invFun := by
      refine continuous_pi fun p => continuous_pi fun q => ?_
      refine (continuous_psiEquiv_symm A σ ι hdeg hσ).comp ?_
      exact continuous_pi fun i => (continuous_apply q).comp ((continuous_apply p).comp (continuous_apply i)) }

def psiGLₜ : GL (Fin 2) (L ⊗[K] A) ≃ₜ* (Fin (Module.finrank K L) → GL (Fin 2) A) :=
  (Units.mapContinuousMulEquiv (matPsi A σ ι hdeg hσ)).trans ContinuousMulEquiv.piUnits

theorem psiGLₜ_apply (g : GL (Fin 2) (L ⊗[K] A)) : psiGLₜ A σ ι hdeg hσ g = psiGL A σ ι hdeg hσ g := by
  funext i; ext p q; rfl

def reindexₜ : (Fin (Module.finrank K L) → GL (Fin 2) A) ≃ₜ* (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
  { reindex K L (GL (Fin 2) A) with
    continuous_toFun := continuous_pi fun j => continuous_apply _
    continuous_invFun := continuous_pi fun i => continuous_apply _ }

def coordsₜ : GL (Fin 2) (L ⊗[K] A) ≃ₜ* (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
  (psiGLₜ A σ ι hdeg hσ).trans (reindexₜ A)

theorem coordsₜ_apply (g : GL (Fin 2) (L ⊗[K] A)) : coordsₜ A σ ι hdeg hσ g = coords A σ ι hdeg hσ g := by
  funext j
  change reindex K L (GL (Fin 2) A) (psiGLₜ A σ ι hdeg hσ g) j = _
  rw [psiGLₜ_apply]
  rfl

theorem coordsₜ_eq : ((coordsₜ A σ ι hdeg hσ) : GL (Fin 2) (L ⊗[K] A) → _) = coords A σ ι hdeg hσ :=
  funext (coordsₜ_apply A σ ι hdeg hσ)

theorem continuous_coords : Continuous (coords A σ ι hdeg hσ) := by
  rw [← coordsₜ_eq]; exact (coordsₜ A σ ι hdeg hσ).continuous

theorem coordsₜ_symm_eq :
    ((coordsₜ A σ ι hdeg hσ).symm : _ → GL (Fin 2) (L ⊗[K] A)) = (coords A σ ι hdeg hσ).symm := by
  funext t
  apply (coords A σ ι hdeg hσ).injective
  rw [MulEquiv.apply_symm_apply, ← coordsₜ_apply, ContinuousMulEquiv.apply_symm_apply]

theorem continuous_coords_symm : Continuous (coords A σ ι hdeg hσ).symm := by
  rw [← coordsₜ_symm_eq]; exact (coordsₜ A σ ι hdeg hσ).symm.continuous

def coordsHomeo : GL (Fin 2) (L ⊗[K] A) ≃ₜ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
  { (coords A σ ι hdeg hσ).toEquiv with
    continuous_toFun := continuous_coords A σ ι hdeg hσ
    continuous_invFun := continuous_coords_symm A σ ι hdeg hσ }

theorem psiGL_coords_symm (s : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A)
    (k : Fin (Module.finrank K L)) :
    psiGL A σ ι hdeg hσ ((coords A σ ι hdeg hσ).symm s) k = s (Fin.cast (finrank_eq_succ K L) k) := by
  change psiGL A σ ι hdeg hσ ((psiGL A σ ι hdeg hσ).symm ((reindex K L (GL (Fin 2) A)).symm s)) k = _
  rw [MulEquiv.apply_symm_apply, reindex_symm_apply]

end Coords

section Aux

def snocHomeo (G : Type) [TopologicalSpace G] (n : ℕ) : (Fin n → G) × G ≃ₜ (Fin (n + 1) → G) where
  toFun z := Fin.snoc z.1 z.2
  invFun x := (Fin.init x, x (Fin.last n))
  left_inv z := by
    obtain ⟨g, k⟩ := z
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv x := Fin.snoc_init_self x
  continuous_toFun := Continuous.finSnoc (A := fun _ : Fin (n + 1) => G) continuous_fst continuous_snd
  continuous_invFun := (continuous_pi fun i => continuous_apply _).prodMk (continuous_apply _)

theorem continuous_listProd {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (n : ℕ) :
    Continuous fun g : Fin n → G => SplitPlace.listProd g := by
  have h : (fun g : Fin n → G => SplitPlace.listProd g) =
      fun g => ((List.finRange n).map fun i => g i).prod := by
    funext g; simp [SplitPlace.listProd, List.ofFn_eq_map]
  rw [h]
  exact continuous_list_prod _ fun i _ => continuous_apply i

variable (A : Type) [NormedField A] [NormedAlgebra ℝ A]

abbrev EE : Type := Fin 2 → Fin 2 → A

def ent (g : GL (Fin 2) A) : EE A := fun i j => (g : Matrix (Fin 2) (Fin 2) A) i j

def mmul (X Y : EE A) : EE A := fun i j => ∑ k, X i k * Y k j

theorem contDiff_mmul : ContDiff ℝ ∞ (fun z : EE A × EE A => mmul A z.1 z.2) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  refine ContDiff.sum fun k _ => ?_
  have h1 : ContDiff ℝ ∞ fun z : EE A × EE A => z.1 i k :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_fst i) k
  have h2 : ContDiff ℝ ∞ fun z : EE A × EE A => z.2 k j :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_snd k) j
  exact h1.mul h2

theorem ent_mul (a b : GL (Fin 2) A) : ent A (a * b) = mmul A (ent A a) (ent A b) := by
  funext i j
  simp only [ent, mmul, Units.val_mul, Matrix.mul_apply]

theorem continuous_ent : Continuous (ent A) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact Continuous.matrix_elem Units.continuous_val i j

end Aux

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
  (A : Type) [NormedField A] [NormedAlgebra ℝ A] [ProperSpace A] [Algebra K A] (ι : L →ₐ[K] A)
  (μA : Measure (GL (Fin 2) A)) (hμA : IsFiniteMeasureOnCompacts μA)
  (φ : GL (Fin 2) (L ⊗[K] A) → ℂ)
  (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → A) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL A σ ι hdeg hσ g k : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j)) ∧
      HasCompactSupport φ)

include hμA hφ in
theorem main :
    (∃ F : (Fin 2 → Fin 2 → A) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, splitFibreIntegral K L hdeg σ hσ A ι μA φ g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) A) i j)) ∧
    HasCompactSupport (splitFibreIntegral K L hdeg σ hσ A ι μA φ) := by
  haveI : IsFiniteMeasureOnCompacts μA := hμA
  haveI : IsLocallyFiniteMeasure μA := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite μA := sigmaFinite_of_locallyFinite
  obtain ⟨⟨Φ, hΦ, hφΦ⟩, hφc⟩ := hφ
  let G : Type := GL (Fin 2) A
  let T : Type := Fin (Module.finrank K L - 1) → GL (Fin 2) A
  let μT : Measure T := Measure.pi fun _ => μA
  haveI : IsFiniteMeasureOnCompacts μT := Measure.pi.isFiniteMeasureOnCompacts _

  let F : T → GL (Fin 2) A → ℂ := fun t k => φ ((coords A σ ι hdeg hσ).symm (Fin.snoc t k))
  let M : Type := Fin (Module.finrank K L - 1) → EE A
  let c : T → M := fun t k' => ent A (t k')
  have hc : Continuous c := continuous_pi fun k' => (continuous_ent A).comp (continuous_apply k')
  let Ψ : M × EE A → ℂ := fun z =>
    Φ (fun k => Fin.snoc (α := fun _ : Fin ((Module.finrank K L - 1) + 1) => EE A) z.1 z.2 (Fin.cast (finrank_eq_succ K L) k))
  have hΨ : ContDiff ℝ ∞ Ψ := by
    refine hΦ.comp (contDiff_pi.2 fun k => ?_)
    generalize Fin.cast (finrank_eq_succ K L) k = j
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact contDiff_snd
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact contDiff_pi.1 contDiff_fst i
  have hF : ∀ t g, F t g = Ψ (c t, ent A g) := by
    intro t g
    simp only [F, Ψ, hφΦ]
    congr 1
    funext k
    rw [psiGL_coords_symm]
    generalize Fin.cast (finrank_eq_succ K L) k = j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; rfl
    | cast i => simp only [Fin.snoc_castSucc]; rfl

  let e₀ : T × G ≃ₜ GL (Fin 2) (L ⊗[K] A) :=
    (snocHomeo (GL (Fin 2) A) (Module.finrank K L - 1)).trans (coordsHomeo A σ ι hdeg hσ).symm
  have he₀ : (φ ∘ e₀ : T × G → ℂ) = Function.uncurry F := by
    funext z
    obtain ⟨g, k⟩ := z
    rfl
  have hFc : HasCompactSupport (Function.uncurry F) := he₀ ▸ hφc.comp_homeomorph e₀

  let p : T → G := fun t => (SplitPlace.listProd t)⁻¹
  have hp : Continuous p := (continuous_listProd _).inv
  have hfun : ∀ h, splitFibreIntegral K L hdeg σ hσ A ι μA φ h = ∫ t, F t (p t * h) ∂μT := fun h => rfl

  set C₁ : Set T := Prod.fst '' tsupport (Function.uncurry F) with hC₁_def
  have hC₁ : IsCompact C₁ := hFc.image continuous_fst
  have hzero : ∀ {t : T}, t ∉ C₁ → ∀ g, F t g = 0 := by
    intro t ht g
    by_contra h
    exact ht ⟨(t, g), subset_tsupport _ (by simpa [Function.mem_support] using h), rfl⟩
  refine ⟨?_, ?_⟩
  ·
    let c' : T → M × EE A := fun t => (c t, ent A (p t))
    have hc' : Continuous c' := hc.prodMk ((continuous_ent A).comp hp)
    let Ψ' : (M × EE A) × EE A → ℂ := fun z => Ψ (z.1.1, mmul A z.1.2 z.2)
    have hΨ' : ContDiff ℝ ∞ Ψ' := by
      have hm := contDiff_mmul A
      have h1 : ContDiff ℝ ∞ fun z : (M × EE A) × EE A => mmul A z.1.2 z.2 :=
        hm.comp (contDiff_fst.snd.prodMk contDiff_snd)
      exact hΨ.comp (contDiff_fst.fst.prodMk h1)
    refine ⟨fun X => ∫ t in C₁, Ψ' (c' t, X) ∂μT, contDiff_setIntegral hC₁ hc' hΨ', fun h => ?_⟩
    rw [hfun, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C₁) (fun t ht => hzero ht _)]
    refine setIntegral_congr_fun hC₁.measurableSet fun t _ => ?_
    simp only [hF, Ψ', c']
    rfl
  ·
    set C₃ : Set G := (fun z : T × G => (p z.1)⁻¹ * z.2) '' tsupport (Function.uncurry F) with hC₃_def
    have hC₃ : IsCompact C₃ := hFc.image ((hp.comp continuous_fst).inv.mul continuous_snd)
    refine HasCompactSupport.intro hC₃ fun h hh => ?_
    have hz : ∀ t, F t (p t * h) = 0 := by
      intro t
      by_contra hne
      refine hh ⟨(t, p t * h), subset_tsupport _ ?_, ?_⟩
      · simpa [Function.mem_support] using hne
      · exact inv_mul_cancel_left (p t) h
    rw [hfun]
    simp [hz]

end Main

end P2mSplitFibreSmoothComplex

end

open MeasureTheory AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
    (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
    (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℂ σ ι hdeg hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
      HasCompactSupport φ) :
    (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, splitFibreIntegral K L hdeg σ hσ ℂ ι μA φ g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
    HasCompactSupport (splitFibreIntegral K L hdeg σ hσ ℂ ι μA φ) := by
  letI : MeasurableSpace (GL (Fin 2) ℂ) := glBorelOf ℂ
  haveI : Measure.IsHaarMeasure μA := hμA
  exact P2mSplitFibreSmoothComplex.main K L hdeg σ hσ ℂ ι μA inferInstance φ hφ

end S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex
end P2MW
export P2MW.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex (solution)
